(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
type elt = Comment of string | Code of string
type document = elt list

type patch_elt =
  | Before of string * string list (* [Before fct c] inserts code c before the type declaration  of function fct *)
  | After of string * string

(* [After fct c] inserts the code c after the code of function *)

let output_elt o = function
  | Comment str -> Printf.fprintf o "(**[yes]%s **)\n" str
  | Code str -> Printf.fprintf o "%s\n" str

let output_list out o l = List.iter (out o) l
let output_document o l = output_list output_elt o l

let output_patch_elt o = function
  | Before (s, l) ->
    Printf.fprintf o "Before declaration of %s, insert <%a>" s
      (output_list output_string)
      l
  | After (s, _) -> Printf.fprintf o "After code of %s, insert <%s>" s s

let output_patch = output_list output_patch_elt
let split = Str.regexp "[ \n\r\t]+"

let get_name_of_decl_function str =
  match Str.split split str with "val" :: n :: _ -> Some n | _ -> None

let get_name_of_function str =
  match Str.split split str with
  | "let" :: "rec" :: s :: _ -> Some s
  | "let" :: s :: _ -> Some s
  | _ -> None

let get_decl_of_function str =
  match Str.split split str with "val" :: s :: _ -> Some s | _ -> None

let rec get_code l =
  match l with
  | [] -> ([], [])
  | Code str :: l ->
    let l1, l2 = get_code l in
    (str :: l1, l2)
  | Comment _ :: _ -> ([], l)

let rec gen_patch_file l =
  match l with
  | [] -> []
  | Comment s :: rst -> (
    match get_decl_of_function s with
    | None ->
      (*Printf.printf "Warning: cannot parse comment %s\n" s;*)
      gen_patch_file rst
    | Some d ->
      (* before d *)
      let c, r = get_code rst in
      Before (d, c) :: gen_patch_file r )
  | Code s :: rst -> (
    match get_name_of_function s with
    | Some n -> After (n, s) :: gen_patch_file rst
    | None ->
      (*Printf.printf "Warning: ignoring %s" s;*)
      gen_patch_file rst )

let rec split_at_comment d l =
  match l with
  | [] -> failwith (Printf.sprintf "Cannot find comment for %s" d)
  | Comment s :: l -> (
    match get_decl_of_function s with
    | None ->
      (*Printf.printf "Warning: cannot parse declaration %s\n" s;*)
      let l1, c, l2 = split_at_comment d l in
      (Comment s :: l1, c, l2)
    | Some v ->
      if d = v then ([], Comment s, l)
      else
        let l1, c, l2 = split_at_comment d l in
        (Comment s :: l1, c, l2) )
  | Code s :: l ->
    let l1, c, l2 = split_at_comment d l in
    (Code s :: l1, c, l2)

let rec apply_patch p f =
  match p with
  | [] -> f
  | Before (d, code) :: p ->
    let l1, c, l2 = split_at_comment d f in
    l1 @ List.map (fun x -> Code x) code @ (c :: apply_patch p l2)
  | After (d, code) :: p -> (
    let l1, c, l2 = split_at_comment d f in
    match l2 with
    | e :: rst -> l1 @ (c :: e :: Code code :: apply_patch p rst)
    | [] -> l1 @ (c :: l2) )
