{
open Parser
}

let incomment = ([^'*']|('*'[^')']))*
let notcomment  = [^ '(' '*' ')']
let notlrcomment = ('('[^'*']) | ('*'[^')''*']) 

rule locate_comment  = parse
            | "(*"'*'* { LCOMMENT }
	    | '*'*"*)" { RCOMMENT }
	    | (('('[^'*'])')'? | ('*'+[^')' '*']) | ([^'*']')') |[^'(' '*' ')'])+
{ TEXT (Lexing.lexeme lexbuf) } 
	    | eof   { EOF }	       
	    |  _    {failwith (Printf.sprintf "Unknown character %s at position %i" (Lexing.lexeme lexbuf)
	       (Lexing.lexeme_start lexbuf))}

