(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
open Prover

(** val empty_state *)

let lift_printer (p : out_channel -> 'a -> unit) o v = p o (Annot.elt v)
let string_op = function AND -> "∧" | OR -> "∨" | IMPL -> "→"
let string_lop = function LAND -> "∧" | LOR -> "∨"
let op_of_lop = function LAND -> AND | LOR -> OR

let rec output_op_list op o l =
  match l with
  | [] ->
    if op = AND || op = IMPL then output_string o "⊤"
    else output_string o "⊥"
  | [f] -> output_formula o f.HCons.elt
  | f1 :: l ->
    Printf.fprintf o "%a %s %a" output_formula f1.HCons.elt (string_op op)
      (output_op_list op) l

and output_formula o = function
  | LFF   -> output_string o "⊥"
  | LAT i -> Printf.fprintf o "p%i" (Uint63.hash i)
  | LOP (op, l) -> Printf.fprintf o "(%a)" (output_op_list (op_of_lop op)) l
  | LIMPL (l, r) ->
    Printf.fprintf o "(%a → %a)" (output_op_list IMPL) l output_formula
      r.HCons.elt


let rec dbg_output_op_list o l =
  match l with
  | [] -> ()
  | [f] -> dbg_output_formula o f.HCons.elt
  | f1 :: l ->
    Printf.fprintf o "%a ; %a" dbg_output_formula  f1.HCons.elt
      (dbg_output_op_list) l

and dbg_output_formula o = function
  | LFF  -> output_string o "⊥"
  | LAT i -> Printf.fprintf o "p%i" (Uint63.hash i)
  | LOP (op, l) -> Printf.fprintf o "[%s %a]" (string_lop op) (dbg_output_op_list ) l
  | LIMPL (l, r) ->
    Printf.fprintf o "(%s [%a] %a)" (string_op IMPL)(dbg_output_op_list ) l  dbg_output_formula
      r.HCons.elt



let rec output_bformula o = function
  | BTT _ -> output_string o "⊤"
  | BFF _ -> output_string o "⊥"
  | BAT (_, i) -> Printf.fprintf o "p%i" (Uint63.hash i)
  | BOP (_, op, f1, f2) ->
    Printf.fprintf o "(%a.(%i) %s %a.(%i))" output_bformula f1.HCons.elt
      (Uint63.hash f1.HCons.id) (string_op op) output_bformula f2.HCons.elt
      (Uint63.hash f2.HCons.id)
  | BIT _ -> ()

let output_hbformula o f =
  Printf.fprintf o "%a.(%i)" output_bformula f.HCons.elt
    (Uint63.hash f.HCons.id)

let output_lit o = function
  | POS p -> Printf.fprintf o "[%a]" output_formula p.HCons.elt
  | NEG p -> Printf.fprintf o "~[%a]" output_formula p.HCons.elt

let output_hform o f = Printf.fprintf o "%a" output_formula f.HCons.elt

let dbg_output_hform o f = Printf.fprintf o "%a" dbg_output_formula f.HCons.elt


let output_oform o f =
  match f with None -> output_string o "⊥" | Some f -> output_hform o f

let rec output_literal_list o l =
  match l with
  | [] -> output_string o "⊥"
  | [POS p] -> Printf.fprintf o "[%a]" output_formula p.HCons.elt
  | POS p :: l ->
    Printf.fprintf o "[%a] ∨ %a" output_formula p.HCons.elt
      output_literal_list l
  | NEG p :: l ->
    Printf.fprintf o "[%a] → %a" output_formula p.HCons.elt
      output_literal_list l

let output_watched_clause o l =
  output_literal_list o (l.watch1 :: l.watch2 :: l.unwatched)

let rec unprovable l =
  match l with
  | [] -> false
  | NEG f :: l -> f.HCons.elt = LOP (LOR, []) || unprovable l
  | POS f :: l -> false

let output_useful_watched_clause o l =
  let l = l.watch1 :: l.watch2 :: l.unwatched in
  if unprovable l then () else output_literal_list o l

let output_clause o = function
  | EMPTY -> output_string o "⊥"
  | TRUE -> output_string o "⊤"
  | UNIT r -> output_lit o r
  | CLAUSE l -> output_watched_clause o l

let rec output_list out o l =
  match l with
  | [] -> ()
  | [e] -> out o e
  | e :: l -> out o e; output_string o ";"; output_list out o l

let output_map out o m =
  IntMap.fold' (fun _ i cl -> Printf.fprintf o "%a;" out (Annot.elt cl)) m ()

let output_clauses o m =
  IntMap.fold'
    (fun _ i (m1, m2) ->
      output_map output_useful_watched_clause o m1;
      output_map output_useful_watched_clause o m2)
    m ()

let output_units hm o m =
  let out_elt i b =
    match IntMap.get' kInt i hm with
    | None -> failwith "Unknow literal"
    | Some (b', f) ->
      let hf = HCons.{id = i; is_dec = b'; elt = f} in
      Printf.fprintf o "%i:%a;" (Uint63.hash i) output_lit
        (if Annot.elt b then POS hf else NEG hf)
  in
  IntMap.fold' (fun _ i b -> out_elt i b) m ()

let output_wneg hm o m =
  let out_elt i b =
    match IntMap.get' kInt i hm with
    | None -> failwith "Unknow literal"
    | Some (b', f) ->
      let hf = HCons.{id = i; is_dec = b'; elt = f} in
      Printf.fprintf o "%i:%a;" (Uint63.hash i) output_hform hf
  in
  IntMap.fold' (fun _ i b -> out_elt i b) m ()

let output_state o st =
  Printf.fprintf o "Arrows : %a\n" (output_list output_lit) st.arrows;
  Printf.fprintf o "WNEG : %a\n" (output_wneg st.hconsmap) st.wneg;
  Printf.fprintf o "Lit : %a\n"
    (output_list (lift_printer output_lit))
    st.unit_stack;
  Printf.fprintf o "Units : %a\n" (output_units st.hconsmap) st.units;
  Printf.fprintf o "Clauses : %a\n" output_clauses st.clauses

let output_plit o hm p =
  LitSet.fold
    (fun () k b ->
      match IntMap.get' kInt k hm with
      | None -> failwith "Unknow literal"
      | Some (b', f) -> (
        match b with
        | None -> Printf.fprintf o "Err : %a" output_bformula f
        | Some b -> Printf.fprintf o "Err : %b %a" b output_bformula f ))
    p ()

(**  *)

(** *)

(*
let cnf pol is_classic cp cm ar acc f hf =
  let x, cl = cnf pol is_classic cp cm ar acc f hf in
  let s = if pol then "+" else "-" in
  Printf.printf "cnf%s %a ⊢ %a\n" s output_formula f
    (output_list output_watched_clause)
    cl;
  (x, cl)
 *)
(** *)

(*let reduce lit cl =
  let res = reduce lit cl in
  ( match res with
  | None -> Printf.printf "reduce : %a -> ∅\n" output_literal_list cl
  | Some r ->
    Printf.printf "reduce : %a -> %a\n" output_literal_list cl
      output_literal_list r );
  res
 *)
(** *)
(*
let cnf_hyps b hs st =
  Printf.printf "cnf_hyps: %a\n" (output_list output_lit) hs;
  cnf_hyps b hs st
 *)
(** *)

(** *)
(*
let intro_state st f hf =
  match intro_state st f hf with
  | Success _ as r ->
    Printf.printf "intro state ⊢ ⊥ \n";
    r
  | Progress (st', g) ->
    Printf.printf "intro state ⊢\n%a\n" output_state st';
    Progress (st', g)
  | Fail _ as f ->
    Printf.printf "intro state ⊢ failure\n";
    f
 *)
(** *)
(*let unit_propagation n st concl =
  let res = unit_propagation n st concl in
  ( match res with
  | Success _ -> Printf.printf "OK"
  | Fail _ -> Printf.printf "KO"
  | Progress st -> Printf.printf "unit_propagation ⊢\n%a\n" output_state st );
  res
 *)
(** *)

(*let select_clause b l acc k cl =
  let res = select_clause b l acc k cl in
  ( match (acc, res) with
  | _, Some l ->
    Printf.printf "select_clause %a -> %a\n" output_watched_clause cl
      output_literal_list l
  | _, _ -> Printf.printf "select_clause %a -> ∅ \n" output_watched_clause cl
  );
  res
 *)
(** *)
(*
let find_split lit is_bot cl =
  let res = find_split lit is_bot cl in
  ( match res with
  | None -> Printf.printf "find_split  -> ∅\n"
  | Some l -> Printf.printf "find_split  -> %a\n" (output_list output_lit) l.Annot.elt );
  res
 *)
(** *)
(*
let progress_arrow l st  =
  let res = find_lit (POS (form_of_literal l)) (st.units) in
  (match res with
  | None -> Printf.printf "find_lit %a -> None\n" output_lit l ;
  | Some b -> Printf.printf "find_lit %a -> Some %b \n" output_lit l (Annot.elt b ));
  let res = progress_arrow l st  in
  Printf.printf "progress_arrow %a -> %b\n" output_lit l res;
  res
 *)

(** *)
(*
let find_arrows st l =
  let res = find_arrows st l in
  Printf.printf "find_arrows %a -> %a\n" (output_list output_lit) l
    (output_list output_lit) res;
  res
 *)
(** *)
(*
let forall_dis prover st g l =
  let prover = fun st g ->
    Printf.printf "(Starting prover %a\n" output_lit (List.hd st.unit_stack).Annot.elt;
    let res = prover st g in
    Printf.printf ")"; flush stdout; res  in
  Printf.printf "( Case analysing %a\n" (output_list output_lit) l ;
  let res = forall_dis prover st g l in
  Printf.printf ")"; flush stdout;
  res
 *)

(** *)
(*
let prover_intro p st g =
  let res = prover_intro p st g in
  ( match res with
  | Success _ -> Printf.fprintf stdout "prover ⊢ %a\n" output_oform g
  | _ -> Printf.fprintf stdout "prover ⊬ %a\n" output_oform g );
  flush stdout; res
 *)
