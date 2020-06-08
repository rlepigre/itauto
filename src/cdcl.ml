open Names
open Constr

let constr_of_ref str =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref str))

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
let coq_eval_prop = lazy (constr_of_ref "cdcl.eval_prop")
let coq_eval_hformula = lazy (constr_of_ref "cdcl.eval_hformula")
let coq_empty = lazy (constr_of_ref "cdcl.IntMap.empty")
let coq_add = lazy (constr_of_ref "cdcl.IntMap.add")

let is_prop env sigma term =
  let sort = Retyping.get_sort_of env sigma term in
  Sorts.is_prop sort

type op = AND | OR | IMPL

module Env = struct
  type gl = {env : Environ.env; sigma : Evd.evar_map}

  module Map = Map.Make (struct
    type t = op * int * int

    let compare : t -> t -> int = Pervasives.compare
  end)

  type t =
    { fresh : int
    ; vars : (EConstr.t * int) list (* hcons value for atoms *)
    ; hmap : int Map.t
    ; gl : gl }

  let empty gl =
    { fresh = 2
    ; (* 0,1 are reserved for false and true *)
      vars = []
    ; hmap = Map.empty
    ; gl }

  (** [eq_constr gl x y] returns an updated [gl] if x and y can be unified *)
  let eq_constr gl x y =
    let evd = gl.sigma in
    match EConstr.eq_constr_universes_proj gl.env evd x y with
    | Some csts -> (
      let csts =
        UnivProblem.to_constraints ~force_weak:false (Evd.universes evd) csts
      in
      match Evd.add_constraints evd csts with
      | evd -> Some {gl with sigma = evd}
      | exception Univ.UniverseInconsistency _ -> None )
    | None -> None

  let hcons_atom env v =
    let rec find gl v vars =
      match vars with
      | [] -> raise Not_found
      | (e, i) :: vars -> (
        match eq_constr gl e v with
        | Some gl' -> (gl', i)
        | None -> find gl v vars )
    in
    try
      let gl', i = find env.gl v env.vars in
      ({env with gl = gl'}, i)
    with Not_found ->
      let f = env.fresh in
      ({env with vars = (v, f) :: env.vars; fresh = f + 1}, f)

  let hcons_op env op f1 f2 =
    try (env, Map.find (op, f1, f2) env.hmap)
    with Not_found ->
      ( { env with
          hmap = Map.add (op, f1, f2) env.fresh env.hmap
        ; fresh = env.fresh + 1 }
      , env.fresh )

  let map_of_env env =
    let add i e m =
      EConstr.mkApp
        ( Lazy.force coq_add
        , [|EConstr.mkProp; EConstr.mkInt (Uint63.of_int i); e; m|] )
    in
    let rec map_of_list l =
      match l with
      | [] -> EConstr.mkApp (Lazy.force coq_empty, [|EConstr.mkProp|])
      | (e, i) :: l -> add i e (map_of_list l)
    in
    map_of_list env.vars
end

let constr_of_bool = function
  | true -> Lazy.force coq_true
  | false -> Lazy.force coq_false

let hc typ i b v =
  EConstr.mkApp
    ( Lazy.force coq_hc
    , [|typ; EConstr.mkInt (Uint63.of_int i); constr_of_bool b; v|] )

let constr_of_op = function
  | AND -> Lazy.force coq_AND
  | OR -> Lazy.force coq_OR
  | IMPL -> Lazy.force coq_IMPL

type hc_formula = {hc : int; is_dec : bool; form : EConstr.t}

let mkop typ o f1 f2 =
  EConstr.mkApp (Lazy.force coq_OP, [|typ; constr_of_op o; f1; f2|])

let reify_formula typ env f =
  let evd = env.Env.gl.Env.sigma in
  let ftyp = EConstr.mkApp (Lazy.force coq_Formula, [|typ|]) in
  let tt = hc ftyp 1 true (EConstr.mkApp (Lazy.force coq_TT, [|typ|])) in
  let ff = hc ftyp 0 true (EConstr.mkApp (Lazy.force coq_FF, [|typ|])) in
  let at i f =
    hc ftyp i false
      (EConstr.mkApp
         (Lazy.force coq_AT, [|typ; EConstr.mkInt (Uint63.of_int i)|]))
  in
  let mk_op = Lazy.force coq_OP in
  let mkop o f1 f2 = EConstr.mkApp (mk_op, [|typ; constr_of_op o; f1; f2|]) in
  let eq_ind r i = GlobRef.equal r (GlobRef.IndRef i) in
  let is_true = eq_ind (Lazy.force coq_True) in
  let is_false = eq_ind (Lazy.force coq_False) in
  let is_and = eq_ind (Lazy.force coq_and) in
  let is_or = eq_ind (Lazy.force coq_or) in
  let var env f =
    let env', i = Env.hcons_atom env f in
    ({hc = i; is_dec = false; form = at i f}, env')
  in
  let get_binop t =
    match EConstr.kind evd t with
    | Ind (i, _) ->
      if is_and i then AND else if is_or i then OR else raise Not_found
    | _ -> raise Not_found
  in
  let rec reify_formula env f =
    match EConstr.kind evd f with
    | Ind (i, _) ->
      if is_true i then ({hc = 1; is_dec = true; form = tt}, env)
      else if is_false i then ({hc = 0; is_dec = true; form = ff}, env)
      else var env f
    | App (h, [|f1; f2|]) -> (
      try
        let op = get_binop h in
        let {hc = i1; is_dec = b1; form = f1}, env = reify_formula env f1 in
        let {hc = i2; is_dec = b2; form = f2}, env = reify_formula env f2 in
        let env, i = Env.hcons_op env op i1 i2 in
        ( { hc = i
          ; is_dec = b1 && b2
          ; form = hc ftyp i (b1 && b2) (mkop op f1 f2) }
        , env )
      with Not_found -> var env f )
    | Prod (t, f1, f2)
      when t.Context.binder_name = Anonymous || EConstr.Vars.noccurn evd 1 f2 ->
      let {hc = i1; is_dec = b1; form = f1}, env = reify_formula env f1 in
      let {hc = i2; is_dec = b2; form = f2}, env = reify_formula env f2 in
      let env, i = Env.hcons_op env IMPL i1 i2 in
      ( { hc = i
        ; is_dec = b1 && b2
        ; form = hc ftyp i (b1 && b2) (mkop IMPL f1 f2) }
      , env )
    | _ -> var env f
  in
  reify_formula env f

let rec reify_hyps env (hyps : (Names.Id.t * EConstr.types) list) =
  match hyps with
  | [] -> ([], env)
  | (id, t) :: l ->
    let lhyps, env = reify_hyps env l in
    if is_prop env.Env.gl.Env.env env.Env.gl.Env.sigma t then
      let hf, env = reify_formula (Lazy.force coq_int) env t in
      ((id, hf) :: lhyps, env)
    else (lhyps, env)

let reify_goal env hyps concl =
  let hyps, env = reify_hyps env hyps in
  let hf, env = reify_formula (Lazy.force coq_int) env concl in
  (hyps, hf, env)

let make_formula env hyps hconcl =
  let typ = Lazy.force coq_int in
  let ftyp = EConstr.mkApp (Lazy.force coq_Formula, [|typ|]) in
  let rec make env hyps hconcl =
    match hyps with
    | [] -> (hconcl, env)
    | (_, hf1) :: hyps ->
      let hf2, env = make env hyps hconcl in
      let env, i = Env.hcons_op env IMPL hf1.hc hf2.hc in
      let is_dec = hf1.is_dec && hf2.is_dec in
      ( { hc = i
        ; is_dec
        ; form = hc ftyp i is_dec (mkop typ IMPL hf1.form hf2.form) }
      , env )
  in
  make env hyps hconcl

let change_goal =
  Proofview.Goal.enter (fun gl ->
      Coqlib.check_required_library ["Cdcl"; "Formula"];
      let sigma = Tacmach.New.project gl in
      let concl = Tacmach.New.pf_concl gl in
      let hyps = Tacmach.New.pf_hyps_types gl in
      let gl0 = {Env.env = Tacmach.New.pf_env gl; sigma} in
      let typ = Lazy.force coq_int in
      let hyps, concl, env = reify_goal (Env.empty gl0) hyps concl in
      let form, env = make_formula env (List.rev hyps) concl in
      (* Feedback.msg_debug
         Pp.(
           str "formula: "
           ++ Printer.pr_econstr_env (Tacmach.New.pf_env gl) sigma form.form); *)
      let m = Env.map_of_env env in
      Feedback.msg_debug
        Pp.(
          str "map: " ++ Printer.pr_econstr_env (Tacmach.New.pf_env gl) sigma m);
      Tacticals.New.tclTHEN
        (Tactics.generalize
           (List.rev_map (fun x -> EConstr.mkVar (fst x)) hyps))
        (Tactics.change_concl
           (EConstr.mkApp
              ( Lazy.force coq_eval_hformula
              , [| typ
                 ; EConstr.mkApp (Lazy.force coq_eval_prop, [|m|])
                 ; form.form |] ))))
