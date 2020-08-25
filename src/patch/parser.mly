%{
(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
 open Patch
%}

%token LCOMMENT RCOMMENT EOF
%token <string> TEXT
%token <string> CODE
%token <string> COMMENT
%start document
%type <Patch.document > document
%%

document : elements EOF { $1 };

elements :
  | {[]}
  | element elements {$1 :: $2}
;

element : LCOMMENT TEXT RCOMMENT { Comment $2 }
  | TEXT { Code $1 }
  ; 

