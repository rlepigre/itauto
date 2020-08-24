(* Nelson-Oppen Scheme *)

open Constr
open Names
open Lazy

let debug = false

let constr_of_string str =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref str))

let eq_refl = lazy (constr_of_string "core.eq.refl")
let eq = lazy (constr_of_string "core.eq.type")

(** [unsafe_to_constr c] returns a [Constr.t] without considering an evar_map.
    This is useful for calling Constr.hash *)
let unsafe_to_constr = EConstr.Unsafe.to_constr

module HConstr = struct
  module M = Map.Make (struct
    type t = EConstr.t

    let compare c c' = Constr.compare (unsafe_to_constr c) (unsafe_to_constr c')
  end)

  include M
end

let decompose_app env evd e =
  try
    match EConstr.kind evd e with
    | App (c, a) -> (c, a)
    | _ -> (EConstr.whd_evar evd e, [||])
  with _ -> failwith "decompose_app"

type purify =
  (* [Pure] term of type ty such that any substerm is of type ty *)
  | Pure
  (* [Impure] may be of any type but does not contain pure subterms (except variables) *)
  | Impure

type spec_env =
  { map : (Names.Id.t * purify) HConstr.t
  ; term_name : Names.Id.t
  ; fresh : Nameops.Subscript.t
  ; remember : (Names.Id.t * Nameops.Subscript.t * EConstr.t * EConstr.t) list
  }

let register_constr env evd {map; term_name; fresh; remember} c p =
  if debug then
    Feedback.msg_debug
      Pp.(str "register_constr " ++ Printer.pr_econstr_env env evd c);
  let tname = Nameops.add_subscript term_name fresh in
  let ty = Retyping.get_type_of env evd c in
  ( EConstr.mkVar tname
  , { map = HConstr.add c (tname, p) map
    ; term_name
    ; fresh = Nameops.Subscript.succ fresh
    ; remember = (term_name, fresh, ty, c) :: remember } )

let fresh_subscript env =
  let ctx = (Environ.named_context_val env).Environ.env_named_map in
  Nameops.Subscript.succ
    (Names.Id.Map.fold
       (fun id _ s ->
         let _, s' = Nameops.get_subscript id in
         let cmp = Nameops.Subscript.compare s s' in
         if cmp = 0 then s else if cmp < 0 then s' else s)
       ctx Nameops.Subscript.zero)

let init_env tname s =
  {map = HConstr.empty; term_name = tname; fresh = s; remember = []}

let has_typ env evd ty t =
  EConstr.eq_constr evd ty (Retyping.get_type_of env evd t)

let is_pure = function Pure -> true | _ -> false
let pp_purity = function Pure -> Pp.str "Pure" | Impure -> Pp.str "Impure"

let pp_econstr_purity env evd (c, p) =
  Pp.(Printer.pr_econstr_env env evd c ++ str ":" ++ pp_purity p)

let rec remember_term env evd senv t =
  let isVar c = try EConstr.isVar evd c with _ -> true in
  let name k (c, p) senv =
    if k = p then
      try (EConstr.mkVar (fst (HConstr.find c senv.map)), senv)
      with Not_found ->
        let c, senv = register_constr env evd senv c p in
        (c, senv)
    else (c, senv)
  in
  let names k l senv =
    List.fold_right
      (fun (c, p) (l, senv) ->
        let c', senv = name k (c, p) senv in
        (c' :: l, senv))
      l ([], senv)
  in
  try
    let id, p = HConstr.find t senv.map in
    ((EConstr.mkVar id, p), senv)
  with Not_found -> (
    let c, a = decompose_app env evd t in
    let c, a, p =
      match Zify_plugin.Zify.declared_term env evd c a with
      | c, a -> (c, a, Pure)
      | exception Not_found ->
        if isVar c && a = [||] then (c, a, Pure) else (c, a, Impure)
    in
    let a, senv =
      Array.fold_right
        (fun e (l, senv) ->
          let r, senv = remember_term env evd senv e in
          (r :: l, senv))
        a ([], senv)
    in
    match p with
    | Pure ->
      let a, senv = names Impure a senv in
      ((EConstr.mkApp (c, Array.of_list a), Pure), senv)
    | Impure ->
      let a, senv = names Pure a senv in
      ((EConstr.mkApp (c, Array.of_list a), Impure), senv) )

(** [eq_proof typ source target] returns (target = target : source = target) *)
let eq_proof typ source target =
  EConstr.mkCast
    ( EConstr.mkApp (force eq_refl, [|typ; target|])
    , DEFAULTcast
    , EConstr.mkApp (force eq, [|typ; source; target|]) )

let show_goal =
  Proofview.Goal.enter (fun gl ->
      Feedback.msg_debug
        Pp.(str " Current  goal " ++ Printer.pr_goal (Proofview.Goal.print gl));
      Tacticals.New.tclIDTAC)

let remember_tac id h (s, ty, t) =
  let tn = Nameops.add_subscript id s in
  let hn = Nameops.add_subscript h s in
  Proofview.Goal.enter (fun gl ->
      let env = Tacmach.New.pf_env gl in
      let evd = Tacmach.New.project gl in
      if debug then
        Feedback.msg_debug
          Pp.(
            str "remember "
            ++ Printer.pr_econstr_env env evd t
            ++ str " as " ++ Names.Id.print tn);
      Tactics.letin_tac
        (Some (false, CAst.make (Namegen.IntroFresh hn)))
        (Names.Name tn) t None
        {Locus.onhyps = None; Locus.concl_occs = Locus.AllOccurrences})

let collect_shared gl =
  let terms =
    Tacmach.New.pf_concl gl :: List.map snd (Tacmach.New.pf_hyps_types gl)
  in
  let env = Tacmach.New.pf_env gl in
  let evd = Tacmach.New.project gl in
  let s = fresh_subscript env in
  let pr = Names.Id.of_string "pr" in
  let senv =
    List.fold_left
      (fun acc t -> snd (remember_term env evd acc t))
      (init_env pr s) terms
  in
  (senv.fresh, List.rev senv.remember)

let purify l =
  Proofview.Goal.enter (fun gl ->
      let env = Tacmach.New.pf_env gl in
      let evd = Tacmach.New.project gl in
      if debug then
        Feedback.msg_debug
          Pp.(
            str "purify "
            ++ Pp.pr_enum
                 (fun (_, _, _, t) -> Printer.pr_econstr_env env evd t)
                 l);
      let hpr = Names.Id.of_string "hpr" in
      Tacticals.New.tclMAP
        (fun (tn, s, ty, t) -> remember_tac tn hpr (s, ty, t))
        l)

let fresh_id id gl =
  Tactics.fresh_id_in_env Id.Set.empty id (Proofview.Goal.env gl)

let prove_equation s c1 ty c2 tac =
  Proofview.Goal.enter (fun gl ->
      let id = Nameops.add_subscript (Names.Id.of_string "__eq") s in
      Tactics.assert_by (Names.Name id)
        (EConstr.mkApp (Lazy.force eq, [|ty; c1; c2|]))
        tac)

let rec all_pairs eq_typ l =
  match l with
  | [] -> []
  | (e, ty) :: l ->
    List.fold_left
      (fun acc (e', ty') -> if eq_typ ty ty' then (e, ty, e') :: acc else acc)
      (all_pairs eq_typ l) l

let or_prover tac1 tac2 = Tacticals.New.tclSOLVE [tac1; tac2]

let idtac_constr msg l =
  Proofview.Goal.enter (fun gl ->
      let env = Tacmach.New.pf_env gl in
      let evd = Tacmach.New.project gl in
      if debug then
        Feedback.msg_debug
          Pp.(str msg ++ pr_enum (Printer.pr_econstr_env env evd) l);
      Tacticals.New.tclIDTAC)

open Proofview.Notations

let rec solve_with select by (tacl : (unit Proofview.tactic * int) list) =
  match tacl with
  | [] -> Tacticals.New.tclFAIL 0 (Pp.str "Cannot prove using any prover")
  | (tac, i) :: tacl ->
    if select i then
      Proofview.tclOR
        (by tac >>= fun () -> Proofview.tclUNIT i)
        (fun _ -> solve_with select by tacl)
    else solve_with select by tacl

let utactic tac = tac >>= fun _ -> Tacticals.New.tclIDTAC

let no_tacs tacl =
  let rec prove_one_equation s acc ll =
    match ll with
    | [] -> Tacticals.New.tclFAIL 0 (Pp.str "Cannot prove any equation")
    | (e1, ty, e2) :: ll ->
      Proofview.tclOR
        ( solve_with (fun _ -> true) (prove_equation s e1 ty e2) tacl
        >>= fun i -> Proofview.tclUNIT (i, List.rev_append acc ll) )
        (fun _ -> prove_one_equation s ((e1, ty, e2) :: acc) ll)
  in
  let rec no_tac s ll =
    prove_one_equation s [] ll
    >>= fun (i, ll') ->
    Proofview.tclOR
      (solve_with (fun i' -> i <> i') (fun x -> x) tacl)
      (fun e -> no_tac (Nameops.Subscript.succ s) ll')
  in
  Tacticals.New.tclTHEN
    (Tacticals.New.tclREPEAT Tactics.intro)
    (Proofview.Goal.enter (fun gl ->
         let s, l = collect_shared gl in
         let evd = Tacmach.New.project gl in
         let ll =
           all_pairs (EConstr.eq_constr evd)
             (List.map
                (fun (x, s, ty, _) ->
                  (EConstr.mkVar (Nameops.add_subscript x s), ty))
                l)
         in
         Tacticals.New.tclTHENLIST [purify l; utactic (no_tac s ll)]))

let solve_with_any tacl = utactic (solve_with (fun _ -> true) (fun x -> x) tacl)

let no_tac tac1 tac2 =
  let tacs = List.mapi (fun i t -> (t, i)) [tac1; tac2] in
  Proofview.tclOR (solve_with_any tacs) (fun _ -> no_tacs tacs)

let purify_tac =
  Proofview.Goal.enter (fun gl ->
      let s, l = collect_shared gl in
      purify l)
