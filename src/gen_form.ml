type op = AND | OR | IMPL
type form = TT | FF | AT of int | OP of op * form * form

let rec gen_atoms i = if i = 0 then [] else AT i :: gen_atoms (i - 1)

let forall_pairs f l =
  let rec forall_pairs acc l1 =
    match l1 with
    | [] -> acc
    | e :: l1' ->
      forall_pairs (List.fold_left (fun acc v -> f e v @ acc) acc l) l1'
  in
  forall_pairs [] l

let rec gen_form j i =
  match i with
  | 0 -> TT :: FF :: gen_atoms j
  | _ ->
    let f1 = gen_form j (i - 1) in
    let f x y = [OP (AND, x, y); OP (OR, x, y); OP (IMPL, x, y)] in
    forall_pairs f f1

let pp_forall o i =
  let rec forall o i =
    if i = 0 then ()
    else (
      Printf.fprintf o "(p%i:Prop)" i;
      forall o (i - 1) )
  in
  Printf.printf "forall %a," forall i

let pp_op o = function
  | AND -> output_string o "/\\"
  | OR -> output_string o "\\/"
  | IMPL -> output_string o "->"

let rec pp_form o f =
  match f with
  | TT -> output_string o "True"
  | FF -> output_string o "False"
  | AT i -> Printf.fprintf o "p%i" i
  | OP (op, f1, f2) ->
    Printf.fprintf o "(%a %a %a)" pp_form f1 pp_op op pp_form f2

let lemma = ref 0
let nb_atoms = ref 0
let depth = ref 0

let pp_goal o f =
  incr lemma;
  Printf.fprintf o "\nLemma test%i : %a %a.\nProof. tauto. Qed.\n" !lemma
    pp_forall !nb_atoms pp_form f

let args =
  [ ("-atom", Arg.Set_int nb_atoms, "number of atoms")
  ; ("-depth", Arg.Set_int depth, "depth of formula") ]

let _ =
  Arg.parse args (fun _ -> ()) "";
  let l = gen_form !nb_atoms !depth in
  List.iter (fun x -> pp_goal stdout x) l
