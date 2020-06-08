{
open Parser
}

let letter = ['a'-'z' 'A'-'Z']
let digit  = ['0' - '9']
let ident = letter(letter|digit|'_')*
let comment = '%'[^'\n']*'\n' 
              
  rule token  = parse
            | "fof" { FOF }
            | "axiom" {AXIOM}
            | "conjecture" {CONJECTURE}
            | comment {COMMENT (Lexing.lexeme lexbuf) }
            | [' ' '\n' '\t'] { token lexbuf }
            |  "."  { DOT }
            | "("   { LPAREN  }
            | ")"   { RPAREN }
            | "|"   { OR  }
            | "&"   { AND }
            | "=>"  { IMPL }
            | "<=>"  { IFF }
	    | "~"    { NOT }
	    | ","   {COMMA}
	    | ident { IDENT (Lexing.lexeme lexbuf) }
            | eof   { EOF }
	    |  _    {failwith (Printf.sprintf "Unknown character %s at position %i" (Lexing.lexeme lexbuf)
	       (Lexing.lexeme_start lexbuf))}
