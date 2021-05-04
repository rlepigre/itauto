(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
(* Nelson-Oppen Scheme *)

open Constr
open Names
open Lazy

(* From zify.ml *)
let arrow =
  let name x =
    Context.make_annot (Name.mk_name (Names.Id.of_string x)) Sorts.Relevant
  in
  EConstr.mkLambda
    ( name "x"
    , EConstr.mkProp
    , EConstr.mkLambda
        ( name "y"
        , EConstr.mkProp
        , EConstr.mkProd
            ( Context.make_annot Names.Anonymous Sorts.Relevant
            , EConstr.mkRel 2
            , EConstr.mkRel 2 ) ) )
let is_prop env sigma term =
  let sort = Retyping.get_sort_of env sigma term in
  Sorts.is_prop sort


let is_arrow env evd a p1 p2 =
  is_prop env evd p1
  && is_prop
       (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (a, p1)) env)
       evd p2
  && (a.Context.binder_name = Names.Anonymous || EConstr.Vars.noccurn evd 1 p2)


let decompose_app env evd e =
  match EConstr.kind evd e with
  | Prod (a, p1, p2) when is_arrow env evd a p1 p2 -> (arrow, [|p1; p2|])
  | App (c, a) -> (c, a)
  | _ -> (EConstr.whd_evar evd e, [||])

(* end zify.ml *)

let debug = false

let constr_of_string str =
    EConstr.of_constr
    (UnivGen.constr_of_monomorphic_global
       (Coqlib.lib_ref str))

let coq_TheorySig  = lazy (constr_of_string "No.TheorySig")
let coq_TheoryType = lazy (constr_of_string "No.TheoryType")
let coq_ZarithThy  = lazy (constr_of_string "No.ZarithThy")

let theory = Summary.ref ~name:"no_thy" coq_ZarithThy


let eq_refl = lazy (constr_of_string "core.eq.refl")
let eq = lazy (constr_of_string "core.eq.type")

let isVar evd c = try EConstr.isVar evd c with _ -> true


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


type classify_term =
  (* [Arith] is only built from opertors known to zify *)
  | Arith
  (* [NonArith] any other term without any [Arith] subterms (except variables) *)
  | NonArith

type var = {name : Names.Id.t; sub : Nameops.Subscript.t ; typ : EConstr.t}
type 'a texpr = {expr : 'a; kpure : classify_term; typ : EConstr.t}

type spec_env =
  { map : Names.Id.t texpr HConstr.t
  ; term_name : Names.Id.t
  ; fresh : Nameops.Subscript.t
  ; remember : (var * EConstr.t option) list }

let pp_var {name; sub;typ} =
  Names.Id.print (Nameops.add_subscript name sub)


let register_constr env evd {map; term_name; fresh; remember} c p =
  if debug then
    Feedback.msg_debug
      Pp.(str "register_constr " ++ Printer.pr_econstr_env env evd c);
  let tname = Nameops.add_subscript term_name fresh in

  match EConstr.kind evd c with
  | Var id -> let typ = Retyping.get_type_of env evd c in
              (c , {map = map ;
                    term_name = term_name;
                    fresh = fresh;
                    remember = ({name = id ; sub = Nameops.Subscript.zero ; typ = typ} , None) :: remember})
  | _ -> 
     let ty = Retyping.get_type_of env evd c
     in
     ( EConstr.mkVar tname
     , { map =
           HConstr.add (EConstr.mkVar tname)
                   {expr = tname; kpure = p; typ = ty}
                   (HConstr.add c {expr = tname; kpure = p; typ = ty} map)
       ; term_name
       ; fresh = Nameops.Subscript.succ fresh
       ; remember = ({name = term_name; sub = fresh; typ = ty}, Some c) :: remember
     } )

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

let is_arith = function Arith -> true | _ -> false
let pp_purity = function Arith -> Pp.str "Arith" | NonArith -> Pp.str "NonArith"

let pp_econstr_purity env evd (c, p) =
  Pp.(Printer.pr_econstr_env env evd c ++ str ":" ++ pp_purity p)

let is_op env evd thy c =
  let typ = Retyping.get_type_of env evd c in
  let op = EConstr.mkApp (Lazy.force coq_TheorySig,[| thy ; typ; c|]) in
  try 
    ignore (Typeclasses.resolve_one_typeclass env evd op) ; true
  with Not_found -> false

let is_arity_op env evd thy c a n =
  let len = Array.length a in
  if len > n
  then
    let op = EConstr.mkApp(c, Array.sub a 0 (len - n)) in
    if is_op env evd thy op
    then (op, Array.sub a (len - n) n)
    else raise Not_found
  else raise Not_found


let declared_term thy env evd c a =
  if is_op env evd thy c
  then (c,a)
  else
    match is_arity_op env evd thy c a 2 with
    | res -> res
    | exception Not_found -> is_arity_op env evd thy c a 1
         

let is_declared_type thy env evd  typS = 
  let typ = EConstr.mkApp(Lazy.force coq_TheoryType,[|thy;typS|]) in
  try 
    ignore (Typeclasses.resolve_one_typeclass env evd typ); true
  with Not_found -> false
  

let rec remember_term thy env evd senv t =
  let name k (c, p) senv =
    if k = p then
      try (EConstr.mkVar (HConstr.find c senv.map).expr, senv)
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
    (* The term is already known *)
    let {expr = id; kpure = p; typ = _} = HConstr.find t senv.map in
    ((EConstr.mkVar id, p), senv)
  with Not_found -> (
    let c, a = decompose_app env evd t in
    let c, a, p =
      match declared_term thy env evd c a with
      | c, a -> (c, a, Arith)
      | exception Not_found ->
         if isVar evd c && a = [||] && is_declared_type thy env evd  (Retyping.get_type_of env evd c)
         then (c, a, Arith) else (c, a, NonArith)
    in
    let a, senv =
      Array.fold_right
        (fun e (l, senv) ->
          let r, senv = remember_term thy env evd  senv e in
          (r :: l, senv))
        a ([], senv)
    in
    match p with
    | Arith ->
      let a, senv = names NonArith a senv in
      ((EConstr.mkApp (c, Array.of_list a), Arith), senv)
    | NonArith ->
      let a, senv = names Arith a senv in
      ((EConstr.mkApp (c, Array.of_list a), NonArith), senv) )

let rec remember_prop thy env evd senv t =
  match EConstr.kind evd t with
  | Prod(a,p1,p2) when is_arrow env evd a p1 p2 ->
     let senv = remember_prop thy env evd senv p1 in
     remember_prop thy env evd senv p2
  |  _  ->
      snd (remember_term thy env evd senv t)
  

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

let collect_shared thy gl =
  let terms =
    Tacmach.New.pf_concl gl :: List.map snd (Tacmach.New.pf_hyps_types gl)
  in
  let env = Tacmach.New.pf_env gl in
  let evd = Tacmach.New.project gl in
  let s = fresh_subscript env in
  let pr = Names.Id.of_string "pr" in
  let senv =
    List.fold_left
      (fun acc t ->  (remember_prop thy env evd acc t))
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
                 (fun (v, t) ->
                   match t with
                   | None -> pp_var v
                   | Some t -> pp_var v ++ str " = " ++Printer.pr_econstr_env env evd t)
                 l);
      let hpr = Names.Id.of_string "hpr" in
      Tacticals.New.tclMAP
        (fun ({name; sub; typ}, t) ->
          match t with
          | None -> Tacticals.New.tclIDTAC
          | Some t -> remember_tac name hpr (sub, typ, t))
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

let pr_all_pairs env evd  l =
  Feedback.msg_debug Pp.(pr_enum (fun (x,_,y) -> Printer.pr_econstr_env env evd x ++ str" = " ++ Printer.pr_econstr_env env evd y) l)


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

let no_tacs thy tacl =
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
         let s, l = collect_shared thy gl in
         let evd = Tacmach.New.project gl in
         let env = Tacmach.New.pf_env gl in
         let vars = (List.map
                (fun ({name; sub; typ}, _) ->
                  (EConstr.mkVar (Nameops.add_subscript name sub), typ))
                l) in
         let ll =
           all_pairs (EConstr.eq_constr evd) vars in
         if debug
         then
           (Feedback.msg_debug Pp.(pr_enum (Printer.pr_econstr_env env evd) (List.map fst vars));
            pr_all_pairs env  evd ll);
         Tacticals.New.tclTHENLIST [purify l; utactic (no_tac s ll)]))

let solve_with_any tacl = utactic (solve_with (fun _ -> true) (fun x -> x) tacl)

let no_tac thy tac1 tac2 =
  let thy  = EConstr.of_constr
               (UnivGen.constr_of_monomorphic_global thy) in
  let tacs = List.mapi (fun i t -> (t, i)) [tac1; tac2] in
  Proofview.tclOR (solve_with_any tacs) (fun _ -> no_tacs thy tacs)

let purify_tac thy =
  let thy  = EConstr.of_constr
               (UnivGen.constr_of_monomorphic_global thy) in
  Proofview.Goal.enter (fun gl ->
      let s, l = collect_shared thy gl in
      purify l)
