open Prover

(** val empty_state *)

let string_op = function AND -> "∧" | OR -> "∨" | IMPL -> "→"

let rec output_formula o = function
  | TT -> output_string o "⊤"
  | FF -> output_string o "⊥"
  | AT i -> Printf.fprintf o "p%i" (Uint63.hash i)
  | OP (op, f1, f2) ->
    Printf.fprintf o "(%a %s %a)" output_formula f1.HCons.elt (string_op op)
      output_formula f2.HCons.elt

let output_lit o = function
  | POS p -> Printf.fprintf o "[%a]" output_formula p.HCons.elt
  | NEG p -> Printf.fprintf o "~[%a]" output_formula p.HCons.elt

let output_hform o f = Printf.fprintf o "%a" output_formula f.HCons.elt

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
  | NEG f :: l -> f.HCons.elt = FF || unprovable l
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
  IntMap.fold' (fun _ i cl -> Printf.fprintf o "%a;" out cl) m ()

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
        (if b then POS hf else NEG hf)
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
  Printf.fprintf o "Lit : %a\n" (output_list output_lit) st.unit_stack;
  Printf.fprintf o "Units : %a\n" (output_units st.hconsmap) st.units;
  Printf.fprintf o "Clauses : %a\n" output_clauses st.clauses

(**  *)

(** *)

(*let cnf pol is_classic cp cm ar acc f hf =
  let x, cl = cnf pol is_classic cp cm ar acc f hf in
  Printf.printf "cnf %a ⊢ %a\n" output_formula f
    (output_list output_useful_watched_clause)
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

(*let cnf_hyps b hs st =
  Printf.printf "cnf_hyps: %a\n" output_literal_list hs;
  cnf_hyps b hs st
 *)
(** *)

(*let intro_state st f hf =
  match intro_state st f hf with
  | None ->
    Printf.printf "intro state ⊢ ⊥ \n";
    None
  | Some (st', g) ->
    Printf.printf "intro state ⊢\n%a\n" output_state st';
    Some (st', g)
 *)
(** *)

(*let unit_propagation n st concl =
  let res = unit_propagation n st concl in
  ( match res with
  | Success -> Printf.printf "OK"
  | OutOfFuel -> Printf.printf "KO"
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
(*let find_split lit is_bot cl =
  let res = find_split lit is_bot cl in
  ( match res with
  | None -> Printf.printf "find_split  -> ∅\n"
  | Some l -> Printf.printf "find_split  -> %a\n" (output_list output_lit) l );
  res
 *)
(** *)
(*let find_arrows st l =
  let res = find_arrows st l in
  Printf.printf "find_arrows %a -> %a\n" (output_list output_lit) l
    (output_list output_lit) res;
  res
 *)
(** *)
(*
let prover_intro p st g =
  let res = prover_intro p st g in
  ( match res with
  | HasProof _ -> Printf.fprintf stdout "prover ⊢ %a\n" output_oform g
  | _ -> Printf.fprintf stdout "prover ⊬ %a\n" output_oform g );
  flush stdout; res
 *)
