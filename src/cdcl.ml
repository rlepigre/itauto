open Names
open Constr
module P = ProverPatch

let constr_of_gref r =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global r)

let constr_of_ref str = constr_of_gref (Coqlib.lib_ref str)
let coq_True = lazy (Coqlib.lib_ref "core.True.type")
let coq_False = lazy (Coqlib.lib_ref "core.False.type")
let coq_and = lazy (Coqlib.lib_ref "core.and.type")
let coq_or = lazy (Coqlib.lib_ref "core.or.type")

(*let coq_iff = lazy (Coqlib.lib_ref "core.iff.type") *)

(* Formula terms *)
let coq_Formula = lazy (constr_of_ref "cdcl.Formula.type")
let coq_TT = lazy (constr_of_ref "cdcl.Formula.TT")
let coq_FF = lazy (constr_of_ref "cdcl.Formula.FF")
let coq_AT = lazy (constr_of_ref "cdcl.Formula.AT")
let coq_OP = lazy (constr_of_ref "cdcl.Formula.OP")
let coq_AND = lazy (constr_of_ref "cdcl.op.AND")
let coq_OR = lazy (constr_of_ref "cdcl.op.OR")
let coq_IMPL = lazy (constr_of_ref "cdcl.op.IMPL")
let coq_hc = lazy (constr_of_ref "cdcl.HCons.mk")
let coq_true = lazy (constr_of_ref "core.bool.true")
let coq_false = lazy (constr_of_ref "core.bool.false")
let coq_int = lazy (constr_of_ref "num.int63.type")

(* Evaluation *)
let coq_eval_is_dec = lazy (constr_of_ref "cdcl.eval_is_dec")
let coq_dProp = lazy (constr_of_ref "cdcl.dProp")
let coq_DecP1 = lazy (constr_of_ref "cdcl.DecP1")
let coq_DecP2 = lazy (constr_of_ref "cdcl.DecP2")
let coq_decP1 = lazy (constr_of_ref "cdcl.decP1")
let coq_decP2 = lazy (constr_of_ref "cdcl.decP2")
let coq_mkAtom = lazy (constr_of_ref "cdcl.mkAtom")
let coq_mkDecAtom = lazy (constr_of_ref "cdcl.mkDecAtom")
let coq_eval_prop = lazy (constr_of_ref "cdcl.eval_prop")
let coq_eval_hformula = lazy (constr_of_ref "cdcl.eval_hformula")
let coq_empty = lazy (constr_of_ref "cdcl.IntMap.empty")
let coq_add = lazy (constr_of_ref "cdcl.IntMap.add")

let is_prop env sigma term =
  let sort = Retyping.get_sort_of env sigma term in
  Sorts.is_prop sort

module IMap = Map.Make (Int)

module Env = struct
  module OMap = Map.Make (struct
    type t = P.op * Uint63.t * Uint63.t

    let compare : t -> t -> int = Pervasives.compare
  end)

  module AMap = Map.Make (Int)

  type dec = NotDec | IsDec of EConstr.t (* Proof of p \/ ~ p *)

  let is_dec = function NotDec -> false | IsDec _ -> true

  type t =
    { fresh : int
    ; vars : (EConstr.t * (int * dec)) list (* hcons value for atoms *)
    ; amap : (EConstr.t * dec) AMap.t (* same as vars + is_dec*)
    ; hmap : int OMap.t
    ; sigma : Evd.evar_map }

  let get_constr_of_atom ep a =
    ProverPatch.(
      match a.HCons.elt with
      | AT i -> (fst (AMap.find (Uint63.hash i) ep.amap), Uint63.hash i)
      | _ -> raise Not_found)

  let empty sigma =
    { fresh = 2
    ; (* 0,1 are reserved for false and true *)
      vars = []
    ; amap = AMap.empty
    ; hmap = OMap.empty
    ; sigma }

  (** [eq_constr gl x y] returns an updated [gl] if x and y can be unified *)
  let eq_constr (env, sigma) x y =
    match EConstr.eq_constr_universes_proj env sigma x y with
    | Some csts -> (
      let csts =
        UnivProblem.to_constraints ~force_weak:false (Evd.universes sigma) csts
      in
      match Evd.add_constraints sigma csts with
      | evd -> Some sigma
      | exception Univ.UniverseInconsistency _ -> None )
    | None -> None

  let is_dec_constr env evd t =
    match EConstr.kind evd t with
    | App (c, a) -> (
      let len = Array.length a in
      if len = 1 then
        (* Unary predicate *)
        let ty = Retyping.get_type_of env evd a.(0) in
        let tc = EConstr.mkApp (Lazy.force coq_DecP1, [|ty; c|]) in
        try
          let _evd, dec = Typeclasses.resolve_one_typeclass env evd tc in
          IsDec (EConstr.mkApp (Lazy.force coq_decP1, [|ty; c; dec; a.(1)|]))
        with Not_found -> NotDec
      else
        let c, v1, v2 =
          if len = 2 then (c, a.(0), a.(1))
          else
            ( EConstr.mkApp (c, Array.sub a 0 (Array.length a - 2))
            , a.(len - 2)
            , a.(len - 1) )
        in
        let ty1 = Retyping.get_type_of env evd v1 in
        let ty2 = Retyping.get_type_of env evd v2 in
        let tc = EConstr.mkApp (Lazy.force coq_DecP2, [|ty1; ty2; c|]) in
        try
          let _evd, dec = Typeclasses.resolve_one_typeclass env evd tc in
          IsDec
            (EConstr.mkApp (Lazy.force coq_decP2, [|ty1; ty2; c; dec; v1; v2|]))
        with Not_found -> NotDec )
    | _ -> NotDec

  let hcons_atom genv env v =
    let rec find sigma v vars =
      match vars with
      | [] -> raise Not_found
      | (e, i) :: vars -> (
        match eq_constr (genv, sigma) e v with
        | Some sigma' -> (sigma', i)
        | None -> find sigma v vars )
    in
    try
      let sigma', i = find env.sigma v env.vars in
      ({env with sigma = sigma'}, i)
    with Not_found ->
      let dec = is_dec_constr genv env.sigma v in
      let f = env.fresh in
      ( { env with
          vars = (v, (f, dec)) :: env.vars
        ; amap = AMap.add f (v, dec) env.amap
        ; fresh = f + 1 }
      , (f, dec) )

  let hcons_op env op f1 f2 =
    try (env, OMap.find (op, f1, f2) env.hmap)
    with Not_found ->
      ( { env with
          hmap = OMap.add (op, f1, f2) env.fresh env.hmap
        ; fresh = env.fresh + 1 }
      , env.fresh )

  let map_of_env env =
    let add = Lazy.force coq_add in
    let ty = Lazy.force coq_dProp in
    let mk_atom = Lazy.force coq_mkAtom in
    let mk_dec_atom = Lazy.force coq_mkDecAtom in
    let mk_atom (p, d) =
      match d with
      | NotDec -> EConstr.mkApp (mk_atom, [|p|])
      | IsDec prf -> EConstr.mkApp (mk_dec_atom, [|p; prf|])
    in
    let add i e m =
      EConstr.mkApp (add, [|ty; EConstr.mkInt (Uint63.of_int i); mk_atom e; m|])
    in
    let rec map_of_list l =
      match l with
      | [] -> EConstr.mkApp (Lazy.force coq_empty, [|ty|])
      | (e, (i, d)) :: l -> add i (e, d) (map_of_list l)
    in
    map_of_list env.vars
end

let hcons i b f = P.HCons.{id = Uint63.of_int i; is_dec = b; elt = f}

let reify_formula genv env (f : EConstr.t) =
  let evd = env.Env.sigma in
  let tt = hcons 1 true P.TT in
  let ff = hcons 0 true P.FF in
  let mkop o f1 f2 = P.OP (o, f1, f2) in
  let eq_ind r i = GlobRef.equal r (GlobRef.IndRef i) in
  let is_true = eq_ind (Lazy.force coq_True) in
  let is_false = eq_ind (Lazy.force coq_False) in
  let is_and = eq_ind (Lazy.force coq_and) in
  let is_or = eq_ind (Lazy.force coq_or) in
  let var env f =
    let env', (i, dec) = Env.hcons_atom genv env f in
    (hcons i (Env.is_dec dec) (P.AT (Uint63.of_int i)), env')
  in
  let get_binop t =
    match EConstr.kind evd t with
    | Ind (i, _) ->
      if is_and i then P.AND else if is_or i then P.OR else raise Not_found
    | _ -> raise Not_found
  in
  let rec reify_formula env f =
    match EConstr.kind evd f with
    | Ind (i, _) ->
      if is_true i then (tt, env)
      else if is_false i then (ff, env)
      else var env f
    | App (h, [|f1; f2|]) -> (
      try
        let op = get_binop h in
        let f1, env = reify_formula env f1 in
        let f2, env = reify_formula env f2 in
        let env, i = Env.hcons_op env op f1.P.HCons.id f2.P.HCons.id in
        (hcons i (f1.P.HCons.is_dec && f2.P.HCons.is_dec) (mkop op f1 f2), env)
      with Not_found -> var env f )
    | Prod (t, f1, f2)
      when t.Context.binder_name = Anonymous || EConstr.Vars.noccurn evd 1 f2 ->
      let f1, env = reify_formula env f1 in
      let f2, env = reify_formula env f2 in
      let env, i = Env.hcons_op env P.IMPL f1.P.HCons.id f2.P.HCons.id in
      (hcons i (f1.P.HCons.is_dec && f2.P.HCons.is_dec) (mkop P.IMPL f1 f2), env)
    | _ -> var env f
  in
  reify_formula env f

let rec reify_hyps genv env (hyps : (Names.Id.t * EConstr.types) list) =
  match hyps with
  | [] -> ([], env)
  | (id, t) :: l ->
    let lhyps, env = reify_hyps genv env l in
    if is_prop genv env.Env.sigma t then
      let hf, env = reify_formula genv env t in
      ((id, hf) :: lhyps, env)
    else (lhyps, env)

let reify_goal genv env hyps concl =
  let hyps, env = reify_hyps genv env hyps in
  let hf, env = reify_formula genv env concl in
  (hyps, hf, env)

let make_formula env hyps hconcl =
  let rec make env hyps hconcl =
    match hyps with
    | [] -> (hconcl, env)
    | (_, hf1) :: hyps ->
      let hf2, env = make env hyps hconcl in
      let env, i = Env.hcons_op env P.IMPL hf1.P.HCons.id hf2.P.HCons.id in
      let is_dec = hf1.P.HCons.is_dec && hf2.P.HCons.is_dec in
      (hcons i is_dec (P.OP (P.IMPL, hf1, hf2)), env)
  in
  make env hyps hconcl

let constr_of_bool = function
  | true -> Lazy.force coq_true
  | false -> Lazy.force coq_false

let hc typ i b v =
  EConstr.mkApp
    (Lazy.force coq_hc, [|typ; EConstr.mkInt i; constr_of_bool b; v|])

let constr_of_op = function
  | P.AND -> Lazy.force coq_AND
  | P.OR -> Lazy.force coq_OR
  | P.IMPL -> Lazy.force coq_IMPL

let mkop typ o f1 f2 =
  EConstr.mkApp (Lazy.force coq_OP, [|typ; constr_of_op o; f1; f2|])

let constr_of_hcons typ constr_of_elt f =
  EConstr.mkApp
    ( Lazy.force coq_hc
    , [| typ
       ; EConstr.mkInt f.P.HCons.id
       ; constr_of_bool f.P.HCons.is_dec
       ; constr_of_elt f.P.HCons.elt |] )

(*let constr_of_formula typ f =
  let tt = EConstr.mkApp (Lazy.force coq_TT, [|typ|]) in
  let ff = EConstr.mkApp (Lazy.force coq_FF, [|typ|]) in
  let ftyp = EConstr.mkApp (Lazy.force coq_Formula, [|typ|]) in
  let at i = EConstr.mkApp (Lazy.force coq_AT, [|typ; EConstr.mkInt i|]) in
  let mk_op = Lazy.force coq_OP in
  let mkop o f1 f2 = EConstr.mkApp (mk_op, [|typ; constr_of_op o; f1; f2|]) in
  P.(
    let rec constr_of_op_formula f =
      match f with
      | TT -> tt
      | FF -> ff
      | AT i -> at i
      | OP (o, f1, f2) ->
        mkop o
          (constr_of_hcons ftyp constr_of_op_formula f1)
          (constr_of_hcons ftyp constr_of_op_formula f2)
    in
    constr_of_hcons ftyp constr_of_op_formula f)
 *)

let constr_of_formula f =
  let tt = Lazy.force coq_TT in
  let ff = Lazy.force coq_FF in
  let ftyp = Lazy.force coq_Formula in
  let at i = EConstr.mkApp (Lazy.force coq_AT, [|EConstr.mkInt i|]) in
  let mk_op = Lazy.force coq_OP in
  let mkop o f1 f2 = EConstr.mkApp (mk_op, [|constr_of_op o; f1; f2|]) in
  P.(
    let rec constr_of_op_formula f =
      match f with
      | TT -> tt
      | FF -> ff
      | AT i -> at i
      | OP (o, f1, f2) ->
        mkop o
          (constr_of_hcons ftyp constr_of_op_formula f1)
          (constr_of_hcons ftyp constr_of_op_formula f2)
    in
    constr_of_hcons ftyp constr_of_op_formula f)

let nat_of_int i =
  if i < 0 then P.O
  else
    let rec nat_of_int i = if i = 0 then P.O else P.S (nat_of_int (i - 1)) in
    nat_of_int i

module Theory = struct
  open ProverPatch
  open Micromega_plugin
  module Mc = Micromega

  let rec parse_clause (genv, sigma) ep env l =
    match l with
    | [] -> (Mc.FF Mc.IsProp, env)
    | a :: l -> (
      let f, env = parse_clause (genv, sigma) ep env l in
      try
        let form = form_of_literal a in
        let eform, i = Env.get_constr_of_atom ep form in
        let at, env =
          Coq_micromega.parse_zarith Mc.IsProp env eform (genv, sigma)
        in
        let at = Mc.A (Mc.IsProp, at, i) in
        match a with
        | POS _ -> (Mc.OR (Mc.IsProp, at, f), env)
        | NEG _ -> (Mc.IMPL (Mc.IsProp, at, None, f), env)
      with Not_found | Coq_micromega.ParseError | Failure _ -> (f, env) )

  open Coq_micromega
  open Certificate

  let iset_of_list l =
    List.fold_left (fun acc i -> Mutils.ISet.add i acc) Mutils.ISet.empty l

  let map_of_list l =
    let rec map_of_list m i l =
      match l with
      | [] -> m
      | (_, id) :: l -> map_of_list (IMap.add i id m) (i + 1) l
    in
    map_of_list IMap.empty 0 l

  let find_deps_of_prf p prf l =
    let m = map_of_list l in
    let hyps = p.hyps prf in
    Mutils.ISet.fold
      (fun i acc -> Mutils.ISet.add (IMap.find i m) acc)
      hyps Mutils.ISet.empty

  let find_unsat_clause p clid =
    let cl = List.map fst clid in
    match p.prover (p.get_option (), cl) with
    | Model _ -> None
    | Unknown -> None
    | Prf prf -> Some (find_deps_of_prf p prf clid)

  let rec find_unsat_core p s l =
    match l with
    | [] -> Some s
    | cl :: l -> (
      match find_unsat_clause p cl with
      | None -> None
      | Some s' -> find_unsat_core p (Mutils.ISet.union s s') l )

  let select_atom is lit =
    let id = Uint63.hash (form_of_literal lit).HCons.id in
    Mutils.ISet.mem id is

  let thy_prover cc p (genv, sigma) ep hm l =
    let env = Coq_micromega.Env.empty (genv, sigma) in
    let cl, _ = parse_clause (genv, sigma) ep env l in
    let cnf_ff, cnf_ff_tags = Mc.cnfZ Mc.IsProp cl in
    match find_unsat_core p (iset_of_list cnf_ff_tags) cnf_ff with
    | None ->
      Printf.fprintf stdout "Thy ⊬ %a\n" P.output_literal_list l;
      None
    | Some is ->
      let c = List.filter (select_atom is) l in
      Printf.fprintf stdout "Thy ⊢ %a\n" P.output_literal_list c;
      cc := c :: !cc;
      Some (hm, c)
end

let run_prover cc (genv, sigma) ep f =
  let is_dec i =
    try
      let c, d = Env.AMap.find (Uint63.hash i) ep.Env.amap in
      Env.is_dec d
    with Not_found -> false
  in
  let m = P.hcons_form f in
  P.prover_formula is_dec
    (Theory.thy_prover cc Micromega_plugin.Coq_micromega.linear_Z (genv, sigma)
       ep)
    true m (nat_of_int 200) f

let constr_of_literal_list ep mkFF mkOr mkImpl l =
  P.(
    let rec constr_of_literal_list l =
      match l with
      | [] -> mkFF
      | x :: l ->
        (match x with POS a -> mkOr | NEG a -> mkImpl)
          (fst (Env.get_constr_of_atom ep (P.form_of_literal x)))
          (constr_of_literal_list l)
    in
    constr_of_literal_list l)

let fresh_id id gl =
  Tactics.fresh_id_in_env Id.Set.empty id (Proofview.Goal.env gl)

(* let clear_all_no_check =
  Proofview.Goal.enter (fun gl ->
      let concl = Tacmach.New.pf_concl gl in
      let env =
        Environ.reset_with_named_context Environ.empty_named_context_val
          (Tacmach.New.pf_env gl)
      in
      Refine.refine ~typecheck:false (fun sigma ->
          Evarutil.new_evar env sigma ~principal:true concl))
 *)

let assert_conflicts ep l tac gl =
  let mkFF = constr_of_gref (Lazy.force coq_False) in
  let mkOr x y = EConstr.mkApp (constr_of_gref (Lazy.force coq_or), [|x; y|]) in
  let mkImpl x y = EConstr.mkArrow x Sorts.Irrelevant y in
  let mk_goal c = constr_of_literal_list ep mkFF mkOr mkImpl c in
  let rec assert_conflicts n l =
    match l with
    | [] -> Tacticals.New.tclIDTAC
    | c :: l ->
      let id = fresh_id (Names.Id.of_string ("__arith" ^ string_of_int n)) gl in
      Tacticals.New.tclTHEN
        (Tactics.assert_by (Names.Name id) (mk_goal c)
           (Tacticals.New.tclTHEN (Tactics.keep []) tac))
        (assert_conflicts (n + 1) l)
  in
  assert_conflicts 0 l

(** [assert_conflicts_clauses tac] runs the sat prover in ml 
    and asserts conflict_clauses *)
let assert_conflicts_clauses tac =
  Proofview.Goal.enter (fun gl ->
      Coqlib.check_required_library ["Cdcl"; "Formula"];
      let sigma = Tacmach.New.project gl in
      let genv = Tacmach.New.pf_env gl in
      let concl = Tacmach.New.pf_concl gl in
      let hyps = Tacmach.New.pf_hyps_types gl in
      let hyps, concl, env = reify_goal genv (Env.empty sigma) hyps concl in
      let form, env = make_formula env (List.rev hyps) concl in
      let cc = ref [] in
      match run_prover cc (genv, sigma) env form with
      | P.HasProof _ -> assert_conflicts env !cc tac gl
      | _ -> Tacticals.New.tclFAIL 0 (Pp.str "Not a tautology"))

let change_goal =
  Proofview.Goal.enter (fun gl ->
      Coqlib.check_required_library ["Cdcl"; "Formula"];
      let sigma = Tacmach.New.project gl in
      let genv = Tacmach.New.pf_env gl in
      let concl = Tacmach.New.pf_concl gl in
      let hyps = Tacmach.New.pf_hyps_types gl in
      let hyps, concl, env = reify_goal genv (Env.empty sigma) hyps concl in
      let form, env = make_formula env (List.rev hyps) concl in
      let cform = constr_of_formula form in
      let m = Env.map_of_env env in
      Tacticals.New.tclTHEN
        (Tactics.generalize
           (List.rev_map (fun x -> EConstr.mkVar (fst x)) hyps))
        (Tactics.change_concl
           (EConstr.mkApp
              ( Lazy.force coq_eval_hformula
              , [|EConstr.mkApp (Lazy.force coq_eval_prop, [|m|]); cform|] ))))

let cdcl tac = Tacticals.New.tclTHEN (assert_conflicts_clauses tac) change_goal
