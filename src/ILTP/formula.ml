type kind = Axiom | Conjecture
type op = And | Or | Impl | Iff
type bformula = False | Var of string | Op of op * bformula * bformula
type formula = {name : string; kind : kind; bform : bformula}

let string_of_kind = function Axiom -> "Variable" | Conjecture -> "Lemma"

let is_non_theorem =
  let split = Str.regexp " \\|\n" in
  fun s ->
    let l = Str.split split s in
    List.mem "Non-Theorem" l

let string_of_op = function
  | And -> "/\\"
  | Or -> "\\/"
  | Impl -> "->"
  | Iff -> "<->"

let rec output_bformula o = function
  | Var s -> output_string o s
  | False -> output_string o "False"
  | Op (op, f1, f2) ->
    Printf.fprintf o "%a %s %a" output_sformula f1 (string_of_op op)
      output_sformula f2

and output_sformula o = function
  | Var s -> output_string o s
  | f -> Printf.fprintf o "(%a)" output_bformula f

module StrSet = Set.Make (String)

let rec vars_of_bformula = function
  | False -> StrSet.empty
  | Var s -> StrSet.singleton s
  | Op (o, f1, f2) -> StrSet.union (vars_of_bformula f1) (vars_of_bformula f2)

let output_vars o s =
  if StrSet.is_empty s then ()
  else StrSet.iter (fun s -> Printf.fprintf o "Variable %s: Prop.\n" s) s

let output_formula o f =
  Printf.fprintf o "%s %s: %a." (string_of_kind f.kind) f.name output_bformula
    f.bform

let output_file o (b, l) =
  let vars =
    List.fold_left
      (fun acc f -> StrSet.union (vars_of_bformula f.bform) acc)
      StrSet.empty l
  in
  Printf.fprintf o "Section S.\n";
  output_vars o vars;
  Printf.fprintf o "\n";
  List.iter (fun f -> Printf.fprintf o "%a\n" output_formula f) l;
  if b then output_string o "Proof. tauto. Qed.\n"
  else output_string o "Proof. Fail intuition fail. Abort.\n";
  Printf.fprintf o "End S.\n"
