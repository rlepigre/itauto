let file = ref ""
let dir = ref ""
let ext = ref ""
let header = ref ""
let map_char c = match c with '+' -> '_' | '.' -> '_' | c -> c
let normalise_str str = String.map map_char str

let process_file hd str =
  try
    let ifile = open_in str in
    let vfile = open_out (normalise_str (Filename.chop_extension str) ^ ".v") in
    let lexbuf = Lexing.from_channel ifile in
    let b, l = Parser.file Lexer.token lexbuf in
    Printf.fprintf vfile "%s\n" hd;
    Formula.output_file vfile (b, l);
    close_out_noerr vfile;
    close_in_noerr ifile
  with
  | Failure s -> raise (failwith (Printf.sprintf "%s : %s" str s))
  | Parsing.Parse_error ->
    raise (failwith (Printf.sprintf "%s : Parse_error" str))

let rec process_dir hd ext dname =
  Array.iter
    (fun s ->
      let fn = Filename.concat dname s in
      if Sys.is_directory fn then process_dir hd ext fn
      else if Filename.check_suffix fn ext then process_file hd fn)
    (Sys.readdir dname)

let args =
  [ ("-ifile", Arg.Set_string file, "File to parse")
  ; ("-idir", Arg.Set_string dir, "Directory to analyse")
  ; ("-ext", Arg.Set_string ext, "File extension")
  ; ("-header", Arg.Set_string header, "Header string to insert") ]

let _ =
  Arg.parse args (fun s -> ()) "";
  if !file <> "" then process_file !header !file
  else if !dir <> "" && !ext <> "" then process_dir !header !ext !dir
