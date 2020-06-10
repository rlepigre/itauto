open Names
open Constr
module P = Prover
open Ppprover

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

module Env = struct
  type gl = {env : Environ.env; sigma : Evd.evar_map}

  module Map = Map.Make (struct
    type t = P.op * Uint63.t * Uint63.t

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

let hcons i b f = P.HCons.{id = Uint63.of_int i; is_dec = b; elt = f}

let reify_formula env (f : EConstr.t) =
  let evd = env.Env.gl.Env.sigma in
  let tt = hcons 1 true P.TT in
  let ff = hcons 0 true P.FF in
  let mkop o f1 f2 = P.OP (o, f1, f2) in
  let eq_ind r i = GlobRef.equal r (GlobRef.IndRef i) in
  let is_true = eq_ind (Lazy.force coq_True) in
  let is_false = eq_ind (Lazy.force coq_False) in
  let is_and = eq_ind (Lazy.force coq_and) in
  let is_or = eq_ind (Lazy.force coq_or) in
  let var env f =
    let env', i = Env.hcons_atom env f in
    (hcons i false (P.AT (Uint63.of_int i)), env')
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

let rec reify_hyps env (hyps : (Names.Id.t * EConstr.types) list) =
  match hyps with
  | [] -> ([], env)
  | (id, t) :: l ->
    let lhyps, env = reify_hyps env l in
    if is_prop env.Env.gl.Env.env env.Env.gl.Env.sigma t then
      let hf, env = reify_formula env t in
      ((id, hf) :: lhyps, env)
    else (lhyps, env)

let reify_goal env hyps concl =
  let hyps, env = reify_hyps env hyps in
  let hf, env = reify_formula env concl in
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

let constr_of_formula typ f =
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

let nat_of_int i =
  if i < 0 then P.O
  else
    let rec nat_of_int i = if i = 0 then P.O else P.S (nat_of_int (i - 1)) in
    nat_of_int i

let length_of_literal = function P.POS p -> 2 | P.NEG p -> 3

let rec length_of_clause = function
  | P.EMPTY -> 1
  | P.ARROW (r, cl) -> 6 + length_of_clause cl
  | P.DIS (p, cl) -> length_of_literal p + 4 + length_of_clause cl

let length_of_list len l = List.fold_left (fun n p -> len p + n + 1) 0 l

let output_concl o = function
  | None -> output_string o "\\bot"
  | Some f -> output_hform o f

let output_sequent o ((u, l), c) concl =
  List.iter (fun l -> Printf.fprintf o "%a;" output_lit l) u;
  List.iter (fun l -> Printf.fprintf o "%a;" output_lit l) l;
  List.iter (fun cl -> Printf.fprintf o "%a;" output_clause cl) c;
  output_string o "\\vdash";
  output_concl o concl

let length_of_sequent ((u, l), c) concl =
  length_of_list length_of_literal u
  + length_of_list length_of_literal l
  + length_of_list length_of_clause c
  + 2

let output_sequent m o a =
  let s = P.show_state m a.P.ante in
  output_sequent o s a.P.csq

let rec output_ptree m o t =
  match t with
  | P.Leaf0 b ->
    if b then Printf.fprintf o "\\prftree{}{%s}" (if b then "OK" else "KO")
  | P.Deriv (a, l) ->
    if l = [] then output_sequent m o a
    else
      Printf.fprintf o "\\prftree %a {%a}" (output_ptree_list m) l
        (output_sequent m) a

and output_ptree_list m o l =
  match l with
  | [] -> ()
  | e :: l ->
    Printf.fprintf o "{%a} %a" (output_ptree m) e (output_ptree_list m) l

let run_prover f =
  let m = P.hcons_form f in
  match P.prover_formula Uint63.equal (fun _ -> false) m (nat_of_int 10) f with
  | P.HasProof _ -> true
  | P.HasModel r ->
    (*    ignore (output_ptree m stdout r);*)
    false
  | P.Timeout r ->
    (*ignore (output_ptree m stdout r);*)
    false
  | P.Done _ -> false

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
      ignore (run_prover form);
      let cform = constr_of_formula typ form in
      let m = Env.map_of_env env in
      Tacticals.New.tclTHEN
        (Tactics.generalize
           (List.rev_map (fun x -> EConstr.mkVar (fst x)) hyps))
        (Tactics.change_concl
           (EConstr.mkApp
              ( Lazy.force coq_eval_hformula
              , [|typ; EConstr.mkApp (Lazy.force coq_eval_prop, [|m|]); cform|]
              ))))
