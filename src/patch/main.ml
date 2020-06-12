let pfile = ref ""
let ifile = ref ""

let process_file pfile ifile =
  let ifile = open_in ifile in
  let lexbuf = Lexing.from_channel ifile in
  let ifile = Parser.document Lexer.locate_comment lexbuf in
  let pfile = open_in pfile in
  let lexbuf = Lexing.from_channel pfile in
  let pfile = Parser.document Lexer.locate_comment lexbuf in
  let pfile = Patch.gen_patch_file pfile in
  (*  Printf.printf "Patch File\n%a" Patch.output_patch pfile;*)
  let tfile = Patch.apply_patch pfile ifile in
  Patch.output_document stdout tfile

let args =
  [ ("-pfile", Arg.Set_string pfile, "Patch file")
  ; ("-ifile", Arg.Set_string ifile, "File to parse") ]

let _ =
  Arg.parse args (fun s -> ()) "";
  if !ifile <> "" && !pfile <> "" then process_file !pfile !ifile
