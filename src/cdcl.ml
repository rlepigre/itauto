open Names
open Constr
module P = ProverPatch

let pr_constr env evd e = Printer.pr_econstr_env env evd e

let constr_of_gref r =
  EConstr.of_constr (UnivGen.constr_of_monomorphic_global r)

let constr_of_ref str = constr_of_gref (Coqlib.lib_ref str)
let coq_True = lazy (Coqlib.lib_ref "core.True.type")
let coq_False = lazy (Coqlib.lib_ref "core.False.type")
let coq_and = lazy (Coqlib.lib_ref "core.and.type")
let coq_or = lazy (Coqlib.lib_ref "core.or.type")
let coq_true = lazy (Coqlib.lib_ref "core.bool.true")
let coq_false = lazy (Coqlib.lib_ref "core.bool.false")
let coq_orb = lazy (Coqlib.lib_ref "core.bool.orb")
let coq_andb = lazy (Coqlib.lib_ref "core.bool.andb")
let coq_implb = lazy (Coqlib.lib_ref "core.bool.implb")
let coq_Is_true = lazy (Coqlib.lib_ref "cdcl.Is_true")
let coq_None = lazy (constr_of_ref "core.option.None")
let coq_Some = lazy (constr_of_ref "core.option.Some")
let coq_iff_refl = lazy (constr_of_ref "cdcl.iff_refl")
let coq_nnpp = lazy (constr_of_ref "core.nnpp.type")

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
let coq_int = lazy (constr_of_ref "num.int63.type")

(* Boolean formula terms *)
let coq_IsBool = lazy (constr_of_ref "cdcl.kind.IsBool")
let coq_IsProp = lazy (constr_of_ref "cdcl.kind.IsProp")
let coq_BFormula = lazy (constr_of_ref "cdcl.BFormula.type")
let coq_BTT = lazy (constr_of_ref "cdcl.BFormula.BTT")
let coq_BFF = lazy (constr_of_ref "cdcl.BFormula.BFF")
let coq_BAT = lazy (constr_of_ref "cdcl.BFormula.BAT")
let coq_BOP = lazy (constr_of_ref "cdcl.BFormula.BOP")
let coq_BIT = lazy (constr_of_ref "cdcl.BFormula.BIT")

(* Evaluation *)
let coq_eval_is_dec = lazy (constr_of_ref "cdcl.eval_is_dec")
let coq_atomT = lazy (constr_of_ref "cdcl.atomT.type")
let coq_mkAtom = lazy (constr_of_ref "cdcl.mkAtom")
let coq_mkAtomDec = lazy (constr_of_ref "cdcl.mkAtomDec")
let coq_TBool = lazy (constr_of_ref "cdcl.atomT.TBool")
let coq_DecP1 = lazy (constr_of_ref "cdcl.DecP1")
let coq_decP1 = lazy (constr_of_ref "cdcl.decP1")
let coq_DecP2 = lazy (constr_of_ref "cdcl.DecP2")
let coq_decP2 = lazy (constr_of_ref "cdcl.decP2")
let coq_Rbool1 = lazy (constr_of_ref "cdcl.Rbool1.type")
let coq_p1 = lazy (constr_of_ref "cdcl.Rbool1.p1")
let coq_p1_prf = lazy (constr_of_ref "cdcl.Rbool1.p1_prf")
let coq_Rbool2 = lazy (constr_of_ref "cdcl.Rbool2.type")
let coq_p2 = lazy (constr_of_ref "cdcl.Rbool2.p2")
let coq_p2_prf = lazy (constr_of_ref "cdcl.Rbool2.p2_prf")
let coq_RProp1 = lazy (constr_of_ref "cdcl.RProp1.type")
let coq_b1 = lazy (constr_of_ref "cdcl.RProp1.b1")
let coq_b1_prf = lazy (constr_of_ref "cdcl.RProp1.b1_prf")
let coq_RProp2 = lazy (constr_of_ref "cdcl.RProp2.type")
let coq_b2 = lazy (constr_of_ref "cdcl.RProp2.b2")
let coq_b2_prf = lazy (constr_of_ref "cdcl.RProp2.b2_prf")
let coq_eval_prop = lazy (constr_of_ref "cdcl.eval_prop")
let coq_eval_hformula = lazy (constr_of_ref "cdcl.eval_hformula")
let coq_eval_hbformula = lazy (constr_of_ref "cdcl.eval_hbformula")
let coq_empty = lazy (constr_of_ref "cdcl.IntMap.empty")
let coq_add = lazy (constr_of_ref "cdcl.IntMap.add")

let is_prop env sigma term =
  let sort = Retyping.get_sort_of env sigma term in
  Sorts.is_prop sort

let constr_of_option typ constr_of_val = function
  | None -> EConstr.mkApp (Lazy.force coq_None, [|typ|])
  | Some v -> EConstr.mkApp (Lazy.force coq_Some, [|typ; constr_of_val v|])

module IMap = Map.Make (Int)

module Env = struct
  module OMap = Map.Make (struct
    type t = P.op * Uint63.t * Uint63.t

    let compare : t -> t -> int = Pervasives.compare
  end)

  module AMap = Map.Make (Int)

  type atom_spec =
    | AtomProp of EConstr.t * EConstr.t option (* NBool *)
    | AtomBool of EConstr.t * EConstr.t * EConstr.t

  (* TBool *)

  type t =
    { fresh : int
    ; vars : (atom_spec * int) list (* hcons value for atoms *)
    ; amap : atom_spec AMap.t (* same as vars + is_dec*)
    ; hmap : int OMap.t
    ; sigma : Evd.evar_map }

  let get_proposition_of_atom_spec = function
    | AtomProp (p, _) -> p
    | AtomBool (_, p, _) -> p

  let get_constr_of_atom ep a =
    ProverPatch.(
      match a.HCons.elt with
      | AT i ->
        ( get_proposition_of_atom_spec (AMap.find (Uint63.hash i) ep.amap)
        , Uint63.hash i )
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
          Some (EConstr.mkApp (Lazy.force coq_decP1, [|ty; c; dec; a.(0)|]))
        with Not_found -> None
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
          Some
            (EConstr.mkApp (Lazy.force coq_decP2, [|ty1; ty2; c; dec; v1; v2|]))
        with Not_found -> None )
    | _ -> None

  let default_bool t =
    let is_true =
      EConstr.mkApp (constr_of_gref (Lazy.force coq_Is_true), [|t|])
    in
    AtomBool (t, is_true, EConstr.mkApp (Lazy.force coq_iff_refl, [|is_true|]))

  let make_atom_of_bool env evd t =
    match EConstr.kind evd t with
    | App (c, a) -> (
      let len = Array.length a in
      if len = 1 then
        (* Unary predicate *)
        let ty = Retyping.get_type_of env evd a.(0) in
        let tc = EConstr.mkApp (Lazy.force coq_Rbool1, [|ty; c|]) in
        try
          let _evd, refl = Typeclasses.resolve_one_typeclass env evd tc in
          let p1 = EConstr.mkApp (Lazy.force coq_p1, [|ty; c; refl; a.(0)|]) in
          let p1_prf =
            EConstr.mkApp (Lazy.force coq_p1_prf, [|ty; c; refl; a.(0)|])
          in
          AtomBool (t, p1, p1_prf)
        with Not_found -> default_bool t
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
        let tc = EConstr.mkApp (Lazy.force coq_Rbool2, [|ty1; ty2; c|]) in
        try
          let _evd, refl = Typeclasses.resolve_one_typeclass env evd tc in
          let p2 =
            EConstr.mkApp (Lazy.force coq_p2, [|ty1; ty2; c; refl; v1; v2|])
          in
          let p2_prf =
            EConstr.mkApp (Lazy.force coq_p2_prf, [|ty1; ty2; c; refl; v1; v2|])
          in
          AtomBool (t, p2, p2_prf)
        with Not_found -> default_bool t )
    | _ -> default_bool t

  let default_prop env evd t = AtomProp (t, is_dec_constr env evd t)

  let make_atom_of_prop env evd t =
    match EConstr.kind evd t with
    | App (c, a) -> (
      let len = Array.length a in
      if len = 1 then
        (* Unary predicate *)
        let ty = Retyping.get_type_of env evd a.(0) in
        let tc = EConstr.mkApp (Lazy.force coq_RProp1, [|ty; c|]) in
        try
          let _evd, refl = Typeclasses.resolve_one_typeclass env evd tc in
          let b1 = EConstr.mkApp (Lazy.force coq_b1, [|ty; c; refl; a.(0)|]) in
          let b1_prf =
            EConstr.mkApp (Lazy.force coq_b1_prf, [|ty; c; refl; a.(0)|])
          in
          AtomBool (b1, t, b1_prf)
        with Not_found -> default_prop env evd t
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
        let tc = EConstr.mkApp (Lazy.force coq_RProp2, [|ty1; ty2; c|]) in
        try
          let _evd, refl = Typeclasses.resolve_one_typeclass env evd tc in
          let p2 =
            EConstr.mkApp (Lazy.force coq_p2, [|ty1; ty2; c; refl; v1; v2|])
          in
          let p2_prf =
            EConstr.mkApp (Lazy.force coq_p2_prf, [|ty1; ty2; c; refl; v1; v2|])
          in
          AtomBool (t, p2, p2_prf)
        with Not_found -> default_prop env evd t )
    | _ -> default_prop env evd t

  let eq_constr_atom_spec (genv, sigma) k a v =
    match k with
    | P.IsProp -> eq_constr (genv, sigma) (get_proposition_of_atom_spec a) v
    | P.IsBool -> (
      match a with
      | AtomProp _ -> None
      | AtomBool (b, _, _) -> eq_constr (genv, sigma) b v )

  let hcons_atom genv env k v =
    let rec find sigma v vars =
      match vars with
      | [] -> raise Not_found
      | (e, i) :: vars -> (
        match eq_constr_atom_spec (genv, sigma) k e v with
        | Some sigma' -> (sigma', (e, i))
        | None -> find sigma v vars )
    in
    try
      let sigma', i = find env.sigma v env.vars in
      ({env with sigma = sigma'}, i)
    with Not_found ->
      let f = env.fresh in
      let atom =
        match k with
        | P.IsProp -> make_atom_of_prop genv env.sigma v
        | P.IsBool -> make_atom_of_bool genv env.sigma v
      in
      ( { env with
          vars = (atom, f) :: env.vars
        ; amap = AMap.add f atom env.amap
        ; fresh = f + 1 }
      , (atom, f) )

  let is_dec = function AtomProp (_, None) -> false | _ -> true
  let has_bool = function AtomBool _ -> true | _ -> false

  let hcons_op env op f1 f2 =
    try (env, OMap.find (op, f1, f2) env.hmap)
    with Not_found ->
      ( { env with
          hmap = OMap.add (op, f1, f2) env.fresh env.hmap
        ; fresh = env.fresh + 1 }
      , env.fresh )

  let map_of_env env =
    let add = Lazy.force coq_add in
    let ty = Lazy.force coq_atomT in
    let mk_atom a =
      match a with
      | AtomProp (p, None) -> EConstr.mkApp (Lazy.force coq_mkAtom, [|p|])
      | AtomProp (p, Some prf) ->
        EConstr.mkApp (Lazy.force coq_mkAtomDec, [|p; prf|])
      | AtomBool (b, p, prf) ->
        EConstr.mkApp (Lazy.force coq_TBool, [|b; p; prf|])
    in
    let add i e m =
      EConstr.mkApp (add, [|ty; EConstr.mkInt (Uint63.of_int i); mk_atom e; m|])
    in
    let rec map_of_list l =
      match l with
      | [] -> EConstr.mkApp (Lazy.force coq_empty, [|ty|])
      | (e, i) :: l -> add i e (map_of_list l)
    in
    map_of_list env.vars
end

let hcons i b f = P.HCons.{id = Uint63.of_int i; is_dec = b; elt = f}

let reify_formula genv env k (f : EConstr.t) =
  let evd = env.Env.sigma in
  let tt k = hcons 1 true (P.BForm.BTT k) in
  let ff k = hcons 0 true (P.BForm.BFF k) in
  let mkop k o f1 f2 = P.BForm.BOP (k, o, f1, f2) in
  let eq_ind r i = GlobRef.equal r (GlobRef.IndRef i) in
  let eq_constructor r c = GlobRef.equal r (GlobRef.ConstructRef c) in
  let eq_const r c = GlobRef.equal r (GlobRef.ConstRef c) in
  let is_True = eq_ind (Lazy.force coq_True) in
  let is_False = eq_ind (Lazy.force coq_False) in
  let is_and = eq_ind (Lazy.force coq_and) in
  let is_or = eq_ind (Lazy.force coq_or) in
  let is_andb = eq_const (Lazy.force coq_andb) in
  let is_orb = eq_const (Lazy.force coq_orb) in
  let is_implb = eq_const (Lazy.force coq_implb) in
  let is_is_True = eq_const (Lazy.force coq_Is_true) in
  let is_true = eq_constructor (Lazy.force coq_true) in
  let is_false = eq_constructor (Lazy.force coq_false) in
  let var env k f =
    let env', (atom, i) = Env.hcons_atom genv env k f in
    (hcons i (Env.is_dec atom) (P.BForm.BAT (k, Uint63.of_int i)), env')
  in
  let get_binop k t =
    match k with
    | P.IsProp -> (
      match EConstr.kind evd t with
      | Ind (i, _) ->
        if is_and i then P.AND else if is_or i then P.OR else raise Not_found
      | _ -> raise Not_found )
    | P.IsBool -> (
      match EConstr.kind evd t with
      | Const (c, _) ->
        if is_andb c then P.AND
        else if is_orb c then P.OR
        else if is_implb c then P.IMPL
        else raise Not_found
      | _ -> raise Not_found )
  in
  let rec reify_formula env k f =
    match EConstr.kind evd f with
    | Ind (i, _) -> (
      match k with
      | P.IsProp ->
        if is_True i then (tt k, env)
        else if is_False i then (ff k, env)
        else var env k f
      | P.IsBool -> var env k f )
    | Construct (c, _) ->
      if is_true c then (tt P.IsBool, env)
      else if is_false c then (ff P.IsBool, env)
      else var env k f
    | App (h, [|f1; f2|]) -> (
      try
        let op = get_binop k h in
        let f1, env = reify_formula env k f1 in
        let f2, env = reify_formula env k f2 in
        let env, i = Env.hcons_op env op f1.P.HCons.id f2.P.HCons.id in
        (hcons i (f1.P.HCons.is_dec && f2.P.HCons.is_dec) (mkop k op f1 f2), env)
      with Not_found -> var env k f )
    | Prod (t, f1, f2)
      when t.Context.binder_name = Anonymous || EConstr.Vars.noccurn evd 1 f2 ->
      let f1, env = reify_formula env P.IsProp f1 in
      let f2, env = reify_formula env P.IsProp f2 in
      let env, i = Env.hcons_op env P.IMPL f1.P.HCons.id f2.P.HCons.id in
      ( hcons i
          (f1.P.HCons.is_dec && f2.P.HCons.is_dec)
          (mkop P.IsProp P.IMPL f1 f2)
      , env )
    | App (h, [|f1|]) -> (
      match k with
      | P.IsBool -> var env k f
      | P.IsProp -> (
        match EConstr.kind evd h with
        | Const (c, _) ->
          if is_is_True c then
            let f1, env = reify_formula env P.IsBool f1 in
            ( hcons (Uint63.hash f1.P.HCons.id) true (P.BForm.BIT f1.P.HCons.elt)
            , env )
          else var env k f
        | _ -> var env k f ) )
    | _ -> var env k f
  in
  reify_formula env k f

let rec reify_hyps genv env (hyps : (Names.Id.t * EConstr.types) list) =
  match hyps with
  | [] -> ([], env)
  | (id, t) :: l ->
    let lhyps, env = reify_hyps genv env l in
    if is_prop genv env.Env.sigma t then
      let hf, env = reify_formula genv env P.IsProp t in
      ((id, hf) :: lhyps, env)
    else (lhyps, env)

let reify_goal genv env hyps concl =
  let hyps, env = reify_hyps genv env hyps in
  let hf, env = reify_formula genv env P.IsProp concl in
  (hyps, hf, env)

let make_formula env hyps hconcl =
  let rec make env hyps hconcl =
    match hyps with
    | [] -> (hconcl, env)
    | (_, hf1) :: hyps ->
      let hf2, env = make env hyps hconcl in
      let env, i = Env.hcons_op env P.IMPL hf1.P.HCons.id hf2.P.HCons.id in
      let is_dec = hf1.P.HCons.is_dec && hf2.P.HCons.is_dec in
      (hcons i is_dec (P.BForm.BOP (P.IsProp, P.IMPL, hf1, hf2)), env)
  in
  make env hyps hconcl

let constr_of_bool = function
  | true -> constr_of_gref (Lazy.force coq_true)
  | false -> constr_of_gref (Lazy.force coq_false)

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

let constr_of_kind = function
  | P.IsProp -> Lazy.force coq_IsProp
  | P.IsBool -> Lazy.force coq_IsBool

let constr_of_bformula f =
  let tt k = EConstr.mkApp (Lazy.force coq_BTT, [|constr_of_kind k|]) in
  let ff k = EConstr.mkApp (Lazy.force coq_BFF, [|constr_of_kind k|]) in
  let ftyp k = EConstr.mkApp (Lazy.force coq_BFormula, [|constr_of_kind k|]) in
  let at k i =
    EConstr.mkApp (Lazy.force coq_BAT, [|constr_of_kind k; EConstr.mkInt i|])
  in
  let mk_op = Lazy.force coq_BOP in
  let mkop k o f1 f2 =
    EConstr.mkApp (mk_op, [|constr_of_kind k; constr_of_op o; f1; f2|])
  in
  P.BForm.(
    let rec constr_of_op_formula f =
      match f with
      | BTT k -> tt k
      | BFF k -> ff k
      | BAT (k, i) -> at k i
      | BOP (k, o, f1, f2) ->
        mkop k o
          (constr_of_hcons (ftyp k) constr_of_op_formula f1)
          (constr_of_hcons (ftyp k) constr_of_op_formula f2)
      | BIT f -> EConstr.mkApp (Lazy.force coq_BIT, [|constr_of_op_formula f|])
    in
    constr_of_hcons (ftyp P.IsProp) constr_of_op_formula f)

let nat_of_int i =
  if i < 0 then P.O
  else
    let rec nat_of_int i = if i = 0 then P.O else P.S (nat_of_int (i - 1)) in
    nat_of_int i

module Theory = struct
  open ProverPatch

  let split_clause l =
    let rec split_acc ln lp l =
      match l with
      | [] -> (ln, lp)
      | at :: l -> (
        match at with
        | NEG _ -> split_acc (at :: ln) lp l
        | POS _ -> split_acc ln (at :: lp) l )
    in
    split_acc [] [] l

  let id_of_literal a =
    Names.Id.of_string_soft
      ("cid__" ^ string_of_int (Uint63.hash (id_of_literal a)))

  let rec constr_of_clause ep cl =
    match cl with
    | [] -> constr_of_gref (Lazy.force coq_False)
    | a :: l -> (
      let c = constr_of_clause ep l in
      let at = fst (Env.get_constr_of_atom ep (form_of_literal a)) in
      match a with
      | NEG _ -> EConstr.mkProd (Context.nameR (id_of_literal a), at, c)
      | POS _ -> (
        match l with
        | [] -> at
        | _ -> EConstr.mkApp (constr_of_gref (Lazy.force coq_or), [|at; c|]) ) )

  let name_of_binder c =
    match Context.binder_name c with
    | Name.Anonymous -> raise Not_found
    | Name.Name id -> id

  let rec intros_proof evd binders c =
    match EConstr.kind evd c with
    | Lambda (c, _, t) -> intros_proof evd (name_of_binder c :: binders) t
    | _ -> (binders, c)

  module ISet = Set.Make (Int)

  let hyps_of_rels s l =
    let rec select i l =
      match l with
      | [] -> []
      | e :: l ->
        if ISet.mem i s then e :: select (i + 1) l else select (i + 1) l
    in
    select 1 l

  let deps_of_proof evd c =
    let rec deps d s c =
      match EConstr.kind evd c with
      | Rel i ->
        let i' = i - d in
        if i' <= 0 then s else ISet.add i' s
      | App (c, i) -> Array.fold_left (fun s t -> deps d s t) (deps d s c) i
      | Const _ | Construct _ | Var _ | Sort _ | Ind _ -> s
      | Lambda (x, t, e) -> deps (d + 1) (deps d s t) e
      | Prod (x, t, e) -> deps (d + 1) (deps d s t) e
      | LetIn (x, e1, t1, e2) -> deps (d + 1) (deps d (deps d s e1) t1) e2
      | Cast (c, _, t) -> deps d (deps d s c) t
      | Int _ | Float _ -> s
      | _ ->
        Feedback.msg_debug
          Pp.(str "deps_of_proof : " ++ pr_constr (Global.env ()) evd c);
        failwith "deps of proof"
    in
    let binders, prf = intros_proof evd [] c in
    hyps_of_rels (deps 0 ISet.empty prf) binders

  let rec concl_of_clause cl =
    match cl with
    | [] -> []
    | at :: l -> ( match at with NEG _ -> concl_of_clause l | POS _ -> cl )

  let rec get_used_hyps l' cl =
    match l' with
    | [] -> concl_of_clause cl
    | e :: l' -> (
      match cl with
      | [] -> failwith "get_used_hyps"
      | at :: cl ->
        if Names.Id.equal e (id_of_literal at) then at :: get_used_hyps l' cl
        else get_used_hyps (e :: l') cl )

  type 'a core = UnsatCore of P.literal list | NoCore of 'a

  let find_unsat_core ep cl tac env sigma =
    let gl = constr_of_clause ep cl in
    let e, pv = Proofview.init sigma [(env, gl)] in
    try
      let _, pv, _, _ =
        Proofview.apply
          ~name:(Names.Id.of_string "unsat_core")
          ~poly:false env
          (Tacticals.New.tclTHEN (Tactics.keep [])
             (Tacticals.New.tclCOMPLETE tac))
          pv
      in
      match Proofview.partial_proof e pv with
      | [prf] ->
        let l = List.rev (deps_of_proof sigma prf) in
        UnsatCore (get_used_hyps l cl)
      | _ -> failwith "Multiple proof terms"
    with e when CErrors.noncritical e -> NoCore (CErrors.print e, gl)

  let find_unsat_core ep cl tac env sigma =
    let ln, lp = split_clause cl in
    let rec all_cores c =
      match c with
      | [] -> NoCore []
      | c1 :: c -> (
        match find_unsat_core ep (ln @ [c1]) tac env sigma with
        | UnsatCore s -> UnsatCore s
        | NoCore r -> (
          match all_cores c with
          | UnsatCore s -> UnsatCore s
          | NoCore r' -> NoCore (r :: r') ) )
    in
    match find_unsat_core ep lp tac env sigma with
    | NoCore _ -> all_cores lp
    | UnsatCore s -> UnsatCore s

  let pp_no_core env sigma l =
    Pp.(
      pr_enum
        (fun (fail, gl) -> fail ++ str " for " ++ pr_constr env sigma gl)
        l)

  let thy_prover tac cc p (genv, sigma) ep hm l =
    match find_unsat_core ep l tac genv sigma with
    | NoCore r -> CErrors.user_err (pp_no_core genv sigma r)
    | UnsatCore core ->
      Printf.fprintf stdout "Thy ⊢ %a\n" P.output_literal_list core;
      cc := core :: !cc;
      Some (hm, core)
end

let run_prover tac cc (genv, sigma) ep f =
  let is_dec i =
    try
      let d = Env.AMap.find (Uint63.hash i) ep.Env.amap in
      Env.is_dec d
    with Not_found -> false
  in
  let m = P.hcons_form f in
  P.prover_formula is_dec
    (Theory.thy_prover tac cc Micromega_plugin.Coq_micromega.linear_Z
       (genv, sigma) ep)
    true m (nat_of_int 200) f

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
  let mk_goal c = Theory.constr_of_clause ep c in
  let rec assert_conflicts n l =
    match l with
    | [] -> Tacticals.New.tclIDTAC
    | c :: l ->
      let id = fresh_id (Names.Id.of_string ("__cc" ^ string_of_int n)) gl in
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
      let bform, env = make_formula env (List.rev hyps) concl in
      let has_bool i =
        try
          let d = Env.AMap.find (Uint63.hash i) env.Env.amap in
          Env.has_bool d
        with Not_found -> false
      in
      let form = P.BForm.to_hformula has_bool bform in
      let cc = ref [] in
      match run_prover tac cc (genv, sigma) env form with
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
      let cform = constr_of_bformula form in
      let m = Env.map_of_env env in
      let change =
        EConstr.mkApp
          ( Lazy.force coq_eval_hbformula
          , [|EConstr.mkApp (Lazy.force coq_eval_prop, [|m|]); cform|] )
      in
      Tacticals.New.tclOR
        (Tacticals.New.tclTHEN
           (Tactics.generalize
              (List.rev_map (fun x -> EConstr.mkVar (fst x)) hyps))
           (Tactics.change_concl change))
        (Tacticals.New.tclFAIL 0 (pr_constr genv sigma change)))

let is_loaded_library d =
  let make_dir l = DirPath.make (List.rev_map Id.of_string l) in
  let dir = make_dir d in
  try
    let (_ : Declarations.module_body) =
      Global.lookup_module (ModPath.MPfile dir)
    in
    true
  with Not_found -> false

let nnpp =
  Proofview.Goal.enter (fun gl ->
      if is_loaded_library ["Coq"; "Logic"; "Classical_Prop"] then
        Tactics.apply (Lazy.force coq_nnpp)
      else Tacticals.New.tclIDTAC)

let cdcl tac = Tacticals.New.tclTHEN (assert_conflicts_clauses tac) change_goal
