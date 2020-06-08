let file = ref ""
let dir = ref ""
let ext = ref ""

let process_file str =
  try
    let ifile = open_in str in
    let vfile = open_out (Filename.chop_extension str ^ ".v") in
    let lexbuf = Lexing.from_channel ifile in
    let b, l = Parser.file Lexer.token lexbuf in
    List.iter (fun f -> Printf.fprintf vfile "%a\n" Formula.output_formula f) l;
    if b then output_string vfile "Proof. tauto. Qed.\n"
    else output_string vfile "Proof. Fail intuition fail. Abort.\n";
    close_out_noerr vfile;
    close_in_noerr ifile
  with
  | Failure s -> raise (failwith (Printf.sprintf "%s : %s" str s))
  | Parsing.Parse_error ->
    raise (failwith (Printf.sprintf "%s : Parse_error" str))

let rec process_dir ext dname =
  Array.iter
    (fun s ->
      let fn = Filename.concat dname s in
      if Sys.is_directory fn then process_dir ext fn
      else if Filename.check_suffix fn ext then process_file fn)
    (Sys.readdir dname)

let args =
  [ ("-ifile", Arg.Set_string file, "File to parse")
  ; ("-idir", Arg.Set_string dir, "Directory to analyse")
  ; ("-ext", Arg.Set_string ext, "File extension") ]

let _ =
  Arg.parse args (fun s -> ()) "";
  if !file <> "" then process_file !file
  else if !dir <> "" && !ext <> "" then process_dir !ext !dir
