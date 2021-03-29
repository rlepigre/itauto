(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)

open Names
open Constr
module P = ProverPatch

let show_theory_time =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~key:["Itauto"; "Theory"; "Time"]
    ~value:false

let thy_time = ref 0.

let debug = Goptions.declare_bool_option_and_ref ~depr:false
    ~key:["Itauto"; "Debug"]
    ~value:false

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

let coq_bool = lazy (constr_of_ref "core.bool.type")


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
let coq_BForm = lazy (constr_of_ref "cdcl.BForm.type")
let coq_HBForm = lazy (constr_of_ref "cdcl.HBForm.type")
let coq_BTT = lazy (constr_of_ref "cdcl.BForm.BTT")
let coq_BFF = lazy (constr_of_ref "cdcl.BForm.BFF")
let coq_BAT = lazy (constr_of_ref "cdcl.BForm.BAT")
let coq_BOP = lazy (constr_of_ref "cdcl.BForm.BOP")
let coq_BIT = lazy (constr_of_ref "cdcl.BForm.BIT")

(* PTrie *)
let coq_ptrie = lazy (constr_of_ref "PTrie.ptrie.type")
let coq_Empty = lazy (constr_of_ref "PTrie.ptrie.Empty")
let coq_Leaf = lazy (constr_of_ref "PTrie.ptrie.Leaf")
let coq_Branch = lazy (constr_of_ref "PTrie.ptrie.Branch")

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
let coq_NegBinRel = lazy (constr_of_ref "cdcl.NegBinRel.type")
let coq_neg_bin_rel_clause = lazy (constr_of_ref "cdcl.neg_bin_rel_clause")
let coq_neg_bin_rel_correct = lazy (constr_of_ref "cdcl.neg_bin_rel_correct")

let whd = Reductionops.clos_whd_flags CClosure.all

let get_projection env evd c =
  match EConstr.kind evd c with
  | Const(c,u) ->
     let body = Environ.constant_value_in env (c,EConstr.Unsafe.to_instance u) in
     begin
       match Constr.kind  body with
       | App(c,a) -> fun i -> EConstr.of_constr a.(i)
       | _        -> failwith "get_projection: expecting an application"
     end
  | _ -> failwith "get_projection: expecting a Constant"
  


let is_prop env sigma term =
  let sort = Retyping.get_sort_of env sigma term in
  Sorts.is_prop sort

let constr_of_option typ constr_of_val = function
  | None -> EConstr.mkApp (Lazy.force coq_None, [|typ|])
  | Some v -> EConstr.mkApp (Lazy.force coq_Some, [|typ; constr_of_val v|])

let constr_of_ptrie constr_of_typ constr_of_val t =
  let empty = Lazy.force coq_Empty in
  let leaf  = Lazy.force coq_Leaf in
  let branch = Lazy.force coq_Branch in
  let int63   = Lazy.force coq_int in

  let rec constr_of_ptrie = function
    | P.PTrie.Empty -> EConstr.mkApp(empty,[|int63; constr_of_typ|])
    | P.PTrie.Leaf(k,v) -> EConstr.mkApp(leaf,[| int63;constr_of_typ; EConstr.mkInt k;constr_of_val v|])
    | P.PTrie.Branch(k1,k2,l,r) -> EConstr.mkApp(branch,[| int63;constr_of_typ; EConstr.mkInt k1; EConstr.mkInt k2;
                                                           constr_of_ptrie l;constr_of_ptrie r|])
  in
  constr_of_ptrie t
       
module IMap = Map.Make (Int)

module Env = struct
  module OMap = Map.Make (struct
    type t = (P.op * Uint63.t * Uint63.t)

    let compare : t -> t -> int = Stdlib.compare
  end)

  module AMap = Map.Make (Int)

  type atom_spec =
    | AtomProp of EConstr.t * EConstr.t option (* NBool *)
    (* TBool *)
    | AtomBool of
        { constr_bool : EConstr.t
        ; constr_prop : EConstr.t
        ; constr_iff : EConstr.t }

  
  
  let pp_atom_spec env evd = function
    | AtomProp(e,_) -> Pp.(str "AtomProp " ++ Printer.pr_econstr_env env evd e)
    | AtomBool{constr_bool;constr_prop} -> Pp.(str "AtomBool " ++ Printer.pr_econstr_env env evd constr_bool ++ str"," ++ Printer.pr_econstr_env env evd constr_prop)


  let check_atom env evd = function
    | AtomProp (p,_) ->
       if is_prop env evd p then ()
       else  Feedback.msg_debug
           Pp.(
             str "check_atom is well typed "
             ++ Printer.pr_econstr_env env evd p)
    | AtomBool {constr_bool; constr_prop; constr_iff} ->
      (let ty = Retyping.get_type_of env evd constr_bool in
       if EConstr.eq_constr evd ty (constr_of_ref "core.bool.type") then ()
       else
         Feedback.msg_debug
           Pp.(
             str "check_atom_constr_bool "
             ++ Printer.pr_econstr_env env evd constr_bool
             ++ str " : "
             ++ Printer.pr_econstr_env env evd ty));
      if is_prop env evd constr_prop then ()
      else
        Feedback.msg_debug
          Pp.(
            str "check_atom_constr_prop "
            ++ Printer.pr_econstr_env env evd constr_prop)

  let check_atom env evd res = check_atom env evd res; res

  type t =
    { fresh : int
    ; vars : (atom_spec * int) list (* hcons value for atoms *)
    ; amap : atom_spec AMap.t (* same as vars + is_dec*)
    ; hmap : int OMap.t
    ; sigma : Evd.evar_map }

  let get_proposition_of_atom_spec = function
    | AtomProp (p, _) -> p
    | AtomBool {constr_prop} -> constr_prop

  let get_constr_of_atom ep a =
    ProverPatch.(
      match a.HCons.elt with
      | LAT i ->
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
          Some
            (whd env evd
               (EConstr.mkApp (Lazy.force coq_decP1, [|ty; c; dec; a.(0)|])))
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
            (whd env evd
               (EConstr.mkApp
                  (Lazy.force coq_decP2, [|ty1; ty2; c; dec; v1; v2|])))
        with Not_found -> None )
    | _ -> None

  let default_bool env evd t =
    let is_true =
      EConstr.mkApp (constr_of_gref (Lazy.force coq_Is_true), [|t|])
    in
    check_atom env evd
      (AtomBool
         { constr_bool = t
         ; constr_prop = is_true
         ; constr_iff = EConstr.mkApp (Lazy.force coq_iff_refl, [|is_true|]) })

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
          let p1 =
            whd env evd
              (EConstr.mkApp (Lazy.force coq_p1, [|ty; c; refl; a.(0)|]))
          in
          let p1_prf =
            whd env evd
              (EConstr.mkApp (Lazy.force coq_p1_prf, [|ty; c; refl; a.(0)|]))
          in
          check_atom env evd
            (AtomBool {constr_bool = t; constr_prop = p1; constr_iff = p1_prf})
        with Not_found -> default_bool env evd t
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
          let proj = get_projection env evd refl in 
          let p2 = EConstr.mkApp (proj 3,[|v1;v2|]) in
          let p2_prf = EConstr.mkApp (proj 4,[|v1;v2|])
          in
          check_atom env evd
            (AtomBool {constr_bool = t; constr_prop = p2; constr_iff = p2_prf})
        with Not_found -> default_bool env evd t )
    | _ -> default_bool env evd t

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
          let b1 =
            whd env evd
              (EConstr.mkApp (Lazy.force coq_b1, [|ty; c; refl; a.(0)|]))
          in
          let b1_prf =
            whd env evd
              (EConstr.mkApp (Lazy.force coq_b1_prf, [|ty; c; refl; a.(0)|]))
          in
          check_atom env evd
            (AtomBool {constr_bool = b1; constr_prop = t; constr_iff = b1_prf})
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
          let proj = get_projection env evd refl in 
          let p2 = EConstr.mkApp (proj 3,[|v1;v2|])
    (* whd  env evd
              (EConstr.mkApp (Lazy.force coq_p2, [|ty1; ty2; c; refl; v1; v2|])) *)
          in
          let p2_prf = EConstr.mkApp (proj 4,[|v1;v2|])
    (* whd  env evd
              (EConstr.mkApp
                 (Lazy.force coq_p2_prf, [|ty1; ty2; c; refl; v1; v2|])) *)
          in
          check_atom env evd
            (AtomBool {constr_bool = p2; constr_prop = t; constr_iff = p2_prf})
        with Not_found -> default_prop env evd t )
    | _ -> default_prop env evd t

  let eq_constr_atom_spec (genv, sigma) k a v =
    match k with
    | P.IsProp -> eq_constr (genv, sigma) (get_proposition_of_atom_spec a) v
    | P.IsBool -> (
      match a with
      | AtomProp _ -> None
      | AtomBool {constr_bool = b} -> eq_constr (genv, sigma) b v )

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

  let hcons_atom genv env k v1 = 
    let res = hcons_atom genv env k v1 in
    if debug () then
      Feedback.msg_debug Pp.(str "hons_atom " ++
                               Printer.pr_econstr_env genv env.sigma v1 ++ str"->" ++
                               pp_atom_spec genv env.sigma (fst (snd res))) ;
    res

  
  let is_dec = function AtomProp (_, None) -> false | _ -> true
  let has_bool = function AtomBool _ -> true | _ -> false

  let hcons_op env op f1 f2 =
    try (env, OMap.find (op, f1, f2) env.hmap)
    with Not_found ->
      ( { env with
          hmap = OMap.add (op, f1, f2) env.fresh env.hmap
        ; fresh = env.fresh + 1 }
      , env.fresh )

  let ptrie_of_env env = 
    List.fold_left (fun m (e,i) -> 
        P.PTrie.set' P.kInt (Uint63.of_int i) e m) P.PTrie.empty env.vars

  let constr_of_atom a =
      match a with
      | AtomProp (p, None) -> EConstr.mkApp (Lazy.force coq_mkAtom, [|p|])
      | AtomProp (p, Some prf) ->
        EConstr.mkApp (Lazy.force coq_mkAtomDec, [|p; prf|])
      | AtomBool {constr_bool = b; constr_prop = p; constr_iff = prf} ->
        EConstr.mkApp (Lazy.force coq_TBool, [|b; p; prf|])


  (* [all_literals] returns the list of all literals as a clause.
     NB: is_dec is not correctly set. *)
  let all_literals env =
    List.map (fun (_,i) ->
        let i' = Uint63.of_int i in 
        P.NEG ({P.HCons.id = i'; P.HCons.is_dec = false; P.HCons.elt =  (P.LAT i')})) env.vars

end

let hcons i b f = P.HCons.{id = Uint63.of_int i; is_dec = b; elt = f}

let reify_formula genv env k (f : EConstr.t) =
  let evd = env.Env.sigma in
  let tt k = hcons 1 true (P.BTT k) in
  let ff k = hcons 0 true (P.BFF k) in
  let mkop k o f1 f2 = P.BOP (k, o, f1, f2) in
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
    (hcons i (Env.is_dec atom) (P.BAT (k, Uint63.of_int i)), env')
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
         when is_prop genv evd f1 &&
                (t.Context.binder_name = Anonymous || EConstr.Vars.noccurn evd 1 f2) ->
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
            (hcons (Uint63.hash f1.P.HCons.id) true (P.BIT f1.P.HCons.elt), env)
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
      (hcons i is_dec (P.BOP (P.IsProp, P.IMPL, hf1, hf2)), env)
  in
  make env hyps hconcl

(** [clause_of_formula f] returns a list of literals if the formula [f] is in clausal form.
    NB: the verification is partial.
 *)
let rec clause_of_formula f =
  let P.HCons.{id; is_dec; elt} = f in
  let mkf () = hcons (Uint63.hash id) is_dec (P.LAT id) in
  match elt with
  | P.BAT (k, _) -> [P.POS (mkf ())]
  | P.BOP (k, P.IMPL, f1, f2) -> (
    match clause_of_formula f1 with
    | [P.POS f] -> P.NEG f :: clause_of_formula f2
    | _ -> failwith "clause_of_formula: not a clause" )
  | P.BOP (k, P.OR, f1, f2) -> (
    match clause_of_formula f1 with
    | [P.POS f] -> P.POS f :: clause_of_formula f2
    | _ -> failwith "clause_of_formula: not a clause" )
  | _ -> failwith "clause_of_formula: not a clause"

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

(*let constr_of_formula f =
  (* let tt = Lazy.force coq_TT in
     let ff = Lazy.force coq_FF in *)
  let ftyp = Lazy.force coq_Formula in
  let at i = EConstr.mkApp (Lazy.force coq_AT, [|EConstr.mkInt i|]) in
  let mk_op = Lazy.force coq_OP in
  let mkop o f1 f2 = EConstr.mkApp (mk_op, [|constr_of_op o; f1; f2|]) in
  P.(
    let rec constr_of_op_formula f =
      match f with
      (* | TT -> tt
         | FF -> ff *)
      | LAT i -> at i
      | LOP (o, l) ->
        mkop o
          (constr_of_hcons ftyp constr_of_op_formula f1)
          (constr_of_hcons ftyp constr_of_op_formula f2)
    in
    constr_of_hcons ftyp constr_of_op_formula f)
 *)
let constr_of_kind = function
  | P.IsProp -> Lazy.force coq_IsProp
  | P.IsBool -> Lazy.force coq_IsBool

let constr_of_bformula f =
  let tt k = EConstr.mkApp (Lazy.force coq_BTT, [|constr_of_kind k|]) in
  let ff k = EConstr.mkApp (Lazy.force coq_BFF, [|constr_of_kind k|]) in
  let ftyp k = EConstr.mkApp (Lazy.force coq_BForm, [|constr_of_kind k|]) in
  let at k i =
    EConstr.mkApp (Lazy.force coq_BAT, [|constr_of_kind k; EConstr.mkInt i|])
  in
  let mk_op = Lazy.force coq_BOP in
  let mkop k o f1 f2 =
    EConstr.mkApp (mk_op, [|constr_of_kind k; constr_of_op o; f1; f2|])
  in
  P.(
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

  let lit_is_dec a = (P.form_of_literal a).HCons.is_dec

  let not_constr c =
    EConstr.mkProd (Context.anonR, c, constr_of_gref (Lazy.force coq_False))

  let pp_literal env sigma ep a =
    let c, i = Env.get_constr_of_atom ep (form_of_literal a) in
    Pp.(
      (match a with NEG _ -> str "¬" | POS _ -> str "")
      ++ Printer.pr_econstr_env env sigma c
      ++ str "@" ++ int i)

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

  let rec constr_of_clause_dec ep cl =
    match cl with
    | [] -> constr_of_gref (Lazy.force coq_False)
    | a :: l -> (
      match a with
      | NEG _ ->
        let at = fst (Env.get_constr_of_atom ep (form_of_literal a)) in
        EConstr.mkProd
          (Context.nameR (id_of_literal a), at, constr_of_clause_dec ep l)
      | POS _ ->
        if List.for_all lit_is_dec cl then constr_of_clause_dec_pos ep cl
        else constr_of_clause ep cl )

  and constr_of_clause_dec_pos ep cl =
    match cl with
    | [] -> constr_of_gref (Lazy.force coq_False)
    | a :: l -> (
      match a with
      | NEG _ -> failwith "A positive literal is expected"
      | POS _ ->
        let at = fst (Env.get_constr_of_atom ep (form_of_literal a)) in
        EConstr.mkProd
          ( Context.nameR (id_of_literal a)
          , not_constr at
          , constr_of_clause_dec_pos ep l ) )

  let name_of_binder c =
    match Context.binder_name c with
    | Name.Anonymous -> raise Not_found
    | Name.Name id -> id

  let rec intros_proof evd cl binders c =
    match EConstr.kind evd c with
    | Lambda (b, t, e) ->
       let n = name_of_binder b in
       if List.exists (Names.Id.equal n) cl
       then intros_proof evd cl ((n, t) :: binders) e
       else (binders,c)
    | _ -> (binders, c)

  module ISet = Set.Make (Int)
  module IMap = Map.Make (Int)

  let hyps_of_rels s l =
    let rec select i l =
      match l with
      | [] -> []
      | e :: l ->
        if ISet.mem i s then e :: select (i + 1) l else select (i + 1) l
    in
    select 1 l

  let deps_of_proof evd cl c =
    let rec deps_rec depth (acc : ISet.t) (c : Constr.constr) =
      match Constr.kind c with
      | Constr.Rel i ->
        let i' = i - depth in
        if i' <= 0 then acc else ISet.add i' acc
      | _ -> fold_constr_with_binders succ deps_rec depth acc c
    in
    let deps c = deps_rec 0 ISet.empty c in
    let cl = List.map id_of_literal cl in
    let binders, prf = intros_proof evd cl [] c in
    ( binders
    , hyps_of_rels
        (deps (EConstr.to_constr ~abort_on_undefined_evars:false evd prf))
        binders
    , prf )

  let remap_proof m evd c =
    let rec remap evd d c =
      match EConstr.kind evd c with
      | Rel i ->
        let i' = i - d in
        if i' <= 0 then EConstr.mkRel i else EConstr.mkRel (IMap.find i' m + d)
      | _ -> EConstr.map_with_binders evd succ (remap evd) d c
    in
    remap evd 0 c

  let remap_binders l' l =
    let rec remap i j m l' l =
      match l' with
      | [] -> m
      | (id, _) :: ll' -> (
        match l with
        | (id', _) :: ll ->
          if Names.Id.equal id id' then
            remap (i + 1) (j + 1) (IMap.add j i m) ll' ll
          else remap i (j + 1) m l' ll
        | [] -> failwith "remap_binders not a sublist" )
    in
    remap 1 1 IMap.empty l' l

  let rec concl_of_clause cl =
    match cl with
    | [] -> []
    | at :: l -> ( match at with NEG _ -> concl_of_clause l | POS _ -> cl )

  let rec concl_of_clause_dec cl =
    match cl with
    | [] -> []
    | at :: l -> (
      match at with
      | NEG _ -> concl_of_clause_dec l
      | POS _ -> if List.for_all lit_is_dec cl then [] else cl )

  (* TODO l' may contain more than literals (goal with quantifiers? *)
  let rec get_used_hyps l' cl =
    match l' with
    | [] -> concl_of_clause_dec cl
    | (e, t) :: l' -> (
      match cl with
      | [] -> []
      | at :: cl ->
        if Names.Id.equal e (id_of_literal at) then at :: get_used_hyps l' cl
        else get_used_hyps ((e, t) :: l') cl )

(*  let get_used_hyps l' cl =
    Printf.printf "get_used_hyps:\n";
    List.iter (fun (i,_) -> Printf.printf "%s " (Names.Id.to_string i)) l';
    Printf.printf "\n";
    List.iter (fun i -> Printf.printf "%s " (Names.Id.to_string (id_of_literal i))) cl; flush stdout ;
    get_used_hyps l' cl
 *)  
    
  
  type 'a core = UnsatCore of (P.literal list * EConstr.t) | NoCore of 'a

  let rec mkLambdas l t =
    match l with
    | [] -> t
    | (x, u) :: l -> EConstr.mkLambda (Context.nameR x, u, mkLambdas l t)

  let reduce_proof sigma cl prf =
    let binders, used_binders, prf' = deps_of_proof sigma cl prf in
    let rused = List.rev used_binders in
    let core = get_used_hyps rused cl in
    let prf_core =
      remap_proof (remap_binders used_binders binders) sigma prf'
    in
    (core, mkLambdas rused prf_core)

  (** [dirty_intros] introduces the negative atoms of the clauses in the context.
      We assume that there is no name conflict. *)

  let dirty_intros cids =
    Tacticals.New.tclTHEN 
      (Tacticals.New.tclMAP Tactics.introduction cids)
      (Tacticals.New.tclREPEAT Tactics.intro)



  let find_unsat_core ep cl tac env sigma =
    let gl = constr_of_clause_dec !ep cl in
    let cids = List.fold_right (fun x acc ->
                   if P.is_positive_literal x then acc
                   else id_of_literal x::acc) cl [] in
    let e, pv = Proofview.init !sigma [(env, gl)] in
    try
      if debug () then
        Feedback.msg_debug
          Pp.(str "Goal " ++ Printer.pr_econstr_env env !sigma gl);
      let _, pv, _, _ =
        Proofview.apply
          ~name:(Names.Id.of_string "unsat_core")
          ~poly:false env
          (Tacticals.New.tclTHENLIST
             [ dirty_intros cids
             ; Tacticals.New.tclCOMPLETE tac ])
          pv
      in
      match Proofview.partial_proof e pv with
      | [prf] ->
        sigma := Proofview.return pv;
        let core, prf = reduce_proof !sigma cl prf in
        if debug () then begin
          Feedback.msg_debug
            Pp.(
              str "Literals"
              ++ prlist_with_sep
                   (fun () -> str ";")
                   (pp_literal env !sigma !ep)
                   cl);
          Feedback.msg_debug
            Pp.(
              str "Core "
              ++ Printer.pr_econstr_env env !sigma (constr_of_clause !ep core))
        end;
        UnsatCore (core, prf)
      | _ -> failwith "Multiple proof terms"
    with e when CErrors.noncritical e ->
      if debug () then
        Feedback.msg_debug
          Pp.(str "find_unsat_core (non-critical): " ++ CErrors.print e);
      NoCore (CErrors.print e, gl)

  let find_unsat_core ep cl tac env sigma =
    let t1 = System.get_time () in
    let res = find_unsat_core ep cl tac env sigma in
    let t2 = System.get_time () in
    if show_theory_time () then
      thy_time := !thy_time +. System.time_difference t1 t2;
    res

  let cons_core c f a =
    match c with
    | UnsatCore c -> UnsatCore c
    | NoCore e -> (
      match f a with UnsatCore c -> UnsatCore c | NoCore l -> NoCore (e :: l) )

  let cons_core_end c f a =
    match c with
    | UnsatCore c -> UnsatCore c
    | NoCore l -> (
      match f a with UnsatCore c -> UnsatCore c | NoCore e -> NoCore (e :: l) )

  let core_list c = match c with UnsatCore _ -> c | NoCore c -> NoCore [c]

  let find_unsat_core ep cl tac env sigma =
    let ln, lp = split_clause cl in
    let rec all_cores c =
      match c with
      | [] -> NoCore []
      | c1 :: c ->
        cons_core (find_unsat_core ep (ln @ [c1]) tac env sigma) all_cores c
    in
    match lp with
    | [] ->
      cons_core (find_unsat_core ep ln tac env sigma) (fun () -> NoCore []) ()
    | _ ->
      cons_core_end (all_cores lp)
        (fun () -> find_unsat_core ep cl tac env sigma)
        ()

  let pp_no_core env sigma l =
    Pp.(
      pr_enum
        (fun (fail, gl) -> fail ++ str " for " ++ pr_constr env sigma gl)
        l)

  let compare_atom a a' =
    match (a, a') with
    | NEG f, NEG f' | POS f, POS f' ->
      Int.compare (Uint63.hash f.HCons.id) (Uint63.hash f'.HCons.id)
    | NEG _, POS _ -> -1
    | POS _, NEG _ -> 1

  (** [subset_clause] assumes that both clauses are sorted *)
  let rec subset_clause cl1 cl2 =
    match (cl1, cl2) with
    | [], _ -> true
    | _, [] -> false
    | e1 :: cl1', e2 :: cl2' ->
      let cmp = compare_atom e1 e2 in
      if cmp < 0 then false
      else if cmp = 0 then subset_clause cl1' cl2'
      else subset_clause cl1 cl2'

  let rec search p l =
    match l with [] -> None | e :: l -> if p e then Some e else search p l

  type clause_type =
    | CC
    (* Conflict_clause *)
    | PC

  let search_atom a l =
    search
      (fun (x, _) ->
        match x with PC, [a'] -> compare_atom a a' = 0 | _ -> false)
      l

  let get_binrel evd t =
    try
      let c, a = EConstr.destApp evd t in
      let len = Array.length a in
      if len = 2 then Some (c, a.(0), a.(1))
      else if len < 2 then None
      else
        Some
          (EConstr.mkApp (c, Array.sub a 0 (len - 2)), a.(len - 2), a.(len - 1))
    with DestKO -> None

  (* Propagation clause *)

  let thy_prop_atom env sigma ep a =
    match a with
    | NEG _ -> None (* We do not do theory propagation for negative atoms *)
    | POS f -> (
      match get_binrel !sigma (fst (Env.get_constr_of_atom !ep f)) with
      | None -> None
      | Some (c, a1, a2) -> (
        let t1 = Retyping.get_type_of env !sigma a1 in
        let t2 = Retyping.get_type_of env !sigma a2 in
        (* Get the instance *)
        let tc = EConstr.mkApp (Lazy.force coq_NegBinRel, [|t1; t2; c|]) in
        try
          let sigma', c' = Typeclasses.resolve_one_typeclass env !sigma tc in
          let rc = Reductionops.clos_whd_flags CClosure.delta env sigma' c' in
          match EConstr.kind sigma' rc with
          | App (c, a) ->
            sigma := sigma';
            let cl = a.(3) in
            let prf = a.(4) in
            let form, ep' =
              reify_formula env !ep P.IsProp
                (Reductionops.beta_applist sigma' (cl, [a1; a2]))
            in
            let prf = Reductionops.beta_applist sigma' (prf, [a1; a2]) in
            ep := ep';
            let l = clause_of_formula form in
            Some (l, prf)
          | _ -> None
        with Not_found -> None
        (* This is an error *) ) )

  let thy_prop_atoms cc (env, sigma) ep l =
    let rec prop l =
      match l with
      | [] -> None
      | a :: l -> (
        match search_atom a !cc with
        | Some _ -> prop l
        | None -> (
          match thy_prop_atom env sigma ep a with
          | None -> prop l
          | Some (l, prf) ->
            cc := ((PC, [a]), (l, prf)) :: !cc;
            Some l ) )
    in
    prop l

  let hcons_form hm f =
    let P.HCons.{id; is_dec; elt} = f in
    match elt with
    | P.LAT _ -> P.PTrie.set' kInt id (is_dec, elt) hm
    | _ -> failwith "hcons_form"

  let hcons_literals hm l =
    List.fold_left (fun m l -> hcons_form m (P.form_of_literal l)) hm l

  let thy_prover tac cc err (genv, sigma) ep hm l =
    let l = List.sort_uniq compare_atom l in
    match search (fun ((ck, x), _) -> ck = CC && subset_clause x l) !cc with
    | None -> (
      match thy_prop_atoms cc (genv, sigma) ep l with
      | Some l ->
        if debug () then
          Printf.fprintf stdout "Thy ⊢p %a\n" P.output_literal_list l;
        Some (hcons_literals hm l, l) (* We did not augment hm... *)
      | None -> (
        (* Really run the prover *)
        match find_unsat_core ep l tac genv sigma with
        | NoCore r -> err := r @ !err ; None
        | UnsatCore (core, prf) ->
          if debug () then
            Printf.fprintf stdout "Thy ⊢ %a\n" P.output_literal_list core;
          cc := ((CC, List.sort compare_atom core), (core, prf)) :: !cc;
          Some (hm, core) ) )
    | Some (core, prf) ->
      if debug () then
        Printf.fprintf stdout "Thy[Again] ⊢ %a\n" P.output_literal_list
          (snd core);
      Some (hm, snd core)
end

let get_env = Proofview.Goal.enter_one (fun gl ->
                   Proofview.tclUNIT (Tacmach.New.pf_env gl))

let dirty_clear ep (env, sigma) =
  let gl = Theory.constr_of_clause ep (Env.all_literals ep) in
  let (e,pv) = Proofview.init sigma [(env,gl)] in
  let env,_,_,_ =  Proofview.apply
                    ~name:(Names.Id.of_string "dirty_clear")
                    ~poly:false env
                    (Proofview.tclTHEN (Tactics.keep []) get_env)   pv in
  env


let run_prover tac cc err (genv, sigma) ep f =
  let is_dec i =
    try
      let d = Env.AMap.find (Uint63.hash i) !ep.Env.amap in
      Env.is_dec d
    with Not_found -> false
  in
  let m = P.hcons_form f in
  let genv = dirty_clear !ep (genv,!sigma) in
  thy_time := 0.;
  let res =
    P.prover_formula is_dec
      (Theory.thy_prover tac cc err (genv, sigma) ep)
      true m
      (nat_of_int (10 * !ep.Env.fresh))
      f
  in
  if show_theory_time () then
    Feedback.msg_debug Pp.(str "Theory running time " ++ real !thy_time);
  res

let fresh_id id gl =
  Tactics.fresh_id_in_env Id.Set.empty id (Proofview.Goal.env gl)

let fresh_ids n id env =
  let rec fresh n avoid acc =
    if n = 0 then acc
    else
      let id = Names.Id.of_string (id ^ string_of_int n) in
      let id = Tactics.fresh_id_in_env avoid id env in
      fresh (n - 1) (Id.Set.add id avoid) (id :: acc)
  in
  fresh n Id.Set.empty []

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

(* tclEVARS and tclRETYPE are borrowed from aactactics *)

let tclEVARS sigma gl =
  let open Evd in
  {it = [gl.it]; sigma}

let tclRETYPE c =
  let open Proofview.Notations in
  let open Proofview in
  tclEVARMAP
  >>= fun sigma ->
  Proofview.Goal.enter (fun goal ->
      let env = Proofview.Goal.env goal in
      let sigma, _ = Typing.type_of env sigma c in
      Unsafe.tclEVARS sigma)

let assert_conflicts  ids l gl =

(*   let l' = List.rev_map2 (fun n (c,prf) -> ( (Locus.NoOccurrences,EConstr.mkCast(prf,DEFAULTcast,c))   , Names.Name n)) ids l in
  Tactics.generalize_gen l'  *)

  let cc = List.rev_map2
             (fun id (c,prf) ->
               Tactics.assert_by (Names.Name id) c  (Tactics.exact_no_check prf)) ids l in
  Tacticals.New.tclTHEN
    (Tacticals.New.tclTHENLIST cc)
    (Tactics.revert ids) 

  



let rec output_list p o l =
  match l with
  | [] -> ()
  | [e] -> p o e
  | e :: l -> p o e; output_string o ";"; output_list p o l

let output_pset o s =
  ProverPatch.LitSet.fold
    (fun () k _ -> Printf.fprintf o "%i " (Uint63.hash k))
    s ()

let rec map_filter f l =
  match l with
  | [] -> []
  | e :: l -> (
    match f e with None -> map_filter f l | Some e' -> e' :: map_filter f l )

let rec needed_hyp f d =
  if P.LitSet.mem f.P.HCons.id d then true else needed_hyp_form f.P.HCons.elt d

and needed_hyp_form f d =
  match f with
  | P.BAT _ | P.BTT _ | P.BFF _ -> false
  | P.BOP (_, _, f1, f2) -> needed_hyp f1 d || needed_hyp f2 d
  | P.BIT f -> (
    match f with
    | P.BTT _ | P.BFF _ | P.BAT _ -> false
    | P.BOP (_, _, f1, f2) -> needed_hyp f1 d || needed_hyp f2 d
    | P.BIT f -> needed_hyp_form f d )

(** [assert_conflict_clauses tac] runs the sat prover in ml 
    and asserts conflict_clauses *)
let collect_conflict_clauses tac gl =
  let sigma = Tacmach.New.project gl in
  let genv = Tacmach.New.pf_env gl in
  let concl = Tacmach.New.pf_concl gl in
  let hyps = Tacmach.New.pf_hyps_types gl in
  let hyps, concl, env = reify_goal genv (Env.empty sigma) hyps concl in
  if debug () then
    begin
      Printf.printf "Hypotheses:\n";
      output_list
      (fun o (h, f) ->
        Printf.fprintf o "%s : %a\n" (Names.Id.to_string h)
          ProverPatch.output_hbformula f)
      stdout hyps;
      Printf.printf "Conclusion %a:\n" ProverPatch.output_hbformula concl
    end;
  let bform, env = make_formula env (List.rev hyps) concl in
  let has_bool i =
    try
      let d = Env.AMap.find (Uint63.hash i) env.Env.amap in
      Env.has_bool d
    with Not_found -> false
  in
  let form1 = (P.BForm.to_hformula has_bool bform) in
  let form = P.hlform form1 in
  if debug () then (
    Printf.printf "\nBFormula : %a\n" P.output_hbformula bform;
    Printf.printf "\nFormula1 : %a\n" P.dbg_output_hform form1;
    Printf.printf "\nFormula : %a\n" P.dbg_output_hform form;
    flush stdout );
  let cc = ref [] in
  let err = ref [] in
  let sigma = ref sigma in
  let env = ref env in
  let save_deps = !P.deps in
  P.deps := P.LitSet.empty ; (* In case of recursive call *)
  match run_prover tac cc err (genv, sigma) env form with
  | P.Success ((hm, _cc), d) ->
    let cc =
      List.map
        (fun ((k, _), (c, prf)) ->
          ( ( if k = Theory.CC then Theory.constr_of_clause_dec
            else Theory.constr_of_clause )
              !env c
          , prf ))
        !cc
    in
    let d = P.LitSet.union d !P.deps in
    let hyps' =
      map_filter (fun (h, f) -> if needed_hyp f d then Some h else None) hyps
    in
    if debug () then (
      Printf.printf "Deps %a\n" output_pset d;
      Printf.printf "Hyps %a\n"
        (output_list (fun o h -> output_string o (Names.Id.to_string h)))
        hyps' );
    P.deps := save_deps;
    Some (!sigma, cc, hyps')
  | _ -> P.deps := save_deps; 
     match !err with
     | [] -> CErrors.user_err Pp.(str "Not a tautology")
     | l  -> CErrors.user_err (Theory.pp_no_core genv !sigma l)


let assert_conflict_clauses tac =
  Proofview.Goal.enter (fun gl ->
      Coqlib.check_required_library ["Cdcl"; "Formula"];
      match collect_conflict_clauses tac gl with
      | None -> Tacticals.New.tclFAIL 0 (Pp.str "Not a tautology")
      | Some (sigma, cc, d) ->
        let ids = fresh_ids (List.length cc) "__cc" (Proofview.Goal.env gl) in
        Tacticals.New.tclTHENLIST
          [
            Proofview.Unsafe.tclEVARS sigma ; 
            (* Generalize the used hypotheses *)
            Tactics.generalize (List.rev_map EConstr.mkVar d);
            (* Assert the conflict clauses *)
            assert_conflicts  ids cc gl;
            Tactics.keep []
    ])




let generalize_prop =
  Proofview.Goal.enter (fun gl ->
      let sigma = Tacmach.New.project gl in
      let genv = Tacmach.New.pf_env gl in
      let hyps = Tacmach.New.pf_hyps_types gl in
      let hyps = List.filter (fun (_, t) -> is_prop genv sigma t) hyps in
      Tactics.generalize (List.map (fun x -> EConstr.mkVar (fst x)) hyps))

let feedback msg =
  Proofview.Goal.enter (fun gl ->
      Feedback.msg_debug msg; Tacticals.New.tclIDTAC)

let generalize l =
  let l = List.map (fun c -> ((Locus.AllOccurrences, c), Anonymous)) l in
  Tactics.generalize_gen l

(*let generalize_env env =
  let prop_of_atom (a, _) =
    Env.(
      match a with
      | AtomProp (p, o) -> ( match o with None -> [p] | Some prf -> [p; prf] )
      | AtomBool {constr_bool; constr_prop; constr_iff} ->
        [constr_prop; constr_bool; constr_iff])
  in
  let gen_list l =
    let n = List.length l in
    Tacticals.New.tclTRY
      (Tacticals.New.tclTHEN (generalize l)
         (Tacticals.New.tclDO n Tactics.intro))
  in
  let gen_tac tac a = Tacticals.New.tclTHEN tac (gen_list (prop_of_atom a)) in
  List.fold_left gen_tac Tacticals.New.tclIDTAC env.Env.vars
 *)

let change_goal =
  Proofview.Goal.enter (fun gl ->
      Coqlib.check_required_library ["Cdcl"; "Formula"];
      let sigma = Tacmach.New.project gl in
      let genv = Tacmach.New.pf_env gl in
      let concl = Tacmach.New.pf_concl gl in
      let hyps, concl, env = reify_goal genv (Env.empty sigma) [] concl in
      let form, env = make_formula env (List.rev hyps) concl in

      if debug () then (
        flush stdout;
        Feedback.msg_debug Pp.(str "Running prover with conflict clauses");
        let has_bool i =
          try
            let d = Env.AMap.find (Uint63.hash i) env.Env.amap in
            Env.has_bool d
          with Not_found -> false
        in
        match
          run_prover Tacticals.New.tclIDTAC (ref []) (ref [])
            (genv, ref sigma)
            (ref env)
            (P.hlform (P.BForm.to_hformula has_bool form))
        with
        | P.Progress _ -> Feedback.msg_debug Pp.(str "Prover Progress")
        | P.Fail f -> Feedback.msg_debug Pp.(str "Prover Failure" ++ str (P.string_of_failure f))
        | P.Success _ -> Feedback.msg_debug Pp.(str "Prover success") );

      let cform = constr_of_bformula form in
      let m = Env.ptrie_of_env env in
(*      let mbool = P.PTrie.map1' Env.has_bool m in
      let mdec  = P.PTrie.map1' Env.is_dec m in *)
      let f = env.Env.fresh in
      let n = fresh_id (Names.Id.of_string "__n") gl in
      let form_name = fresh_id (Names.Id.of_string "__f") gl in
      let m_name = fresh_id (Names.Id.of_string "__m") gl in
(*      let mb_name = fresh_id (Names.Id.of_string "__mb") gl in 
      let md_name = fresh_id (Names.Id.of_string "__md") gl in *)

      let m_typ = EConstr.mkApp(Lazy.force coq_ptrie,[| Lazy.force coq_int; Lazy.force coq_atomT|]) in
      (*      let mbool_typ = EConstr.mkApp(Lazy.force coq_ptrie,[| Lazy.force coq_int; Lazy.force coq_bool|]) in*)

      let change =
        EConstr.mkLetIn
          ( Context.nameR n
          , EConstr.mkInt (Uint63.of_int (10 * f))
          , Lazy.force coq_int,
(*          EConstr.mkLetIn
            (Context.nameR mb_name, constr_of_ptrie (Lazy.force coq_bool) constr_of_bool mbool, mbool_typ,
             EConstr.mkLetIn
               (Context.nameR md_name, constr_of_ptrie (Lazy.force coq_bool) constr_of_bool mdec, mbool_typ, *)
                EConstr.mkLetIn (
                 Context.nameR m_name, constr_of_ptrie (Lazy.force coq_atomT) Env.constr_of_atom  m, m_typ,
                 EConstr.mkLetIn
                   (Context.nameR form_name, cform, Lazy.force coq_HBForm,
                     EConstr.mkApp
                       ( Lazy.force coq_eval_hbformula
                       , [|EConstr.mkApp (Lazy.force coq_eval_prop, [|EConstr.mkRel 2 |]); EConstr.mkRel 1|] ) )))
      in
      if debug () then
        Feedback.msg_debug
          Pp.(str "change " ++ Printer.pr_econstr_env genv sigma change);
      Tacticals.New.tclTHENLIST [Tactics.change_concl change(*; generalize_env env*)])

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
