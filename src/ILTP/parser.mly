%{
 open Formula

%}

%token FOF AXIOM CONJECTURE
%token EOF DOT COMMA LPAREN RPAREN OR AND IMPL IFF NOT
%token <string> IDENT
%token <string> COMMENT
%start file
%type <bool * (Formula.formula list) > file
%left IFF
%left IMPL
%left OR
%left AND
%nonassoc NOT
%%

comments :
  |  { false }
  | COMMENT comments { Formula.is_non_theorem $1 || $2 }
  ;

file : comments formulae comments EOF { not $1,$2 }
;

formulae :
| formula {[$1] }
| formula formulae { $1::$2 }
;

kind : AXIOM { Axiom }
  |  CONJECTURE {Conjecture}
; 

formula : FOF LPAREN IDENT COMMA kind COMMA bformula RPAREN DOT  { {name = $3;kind = $5;bform = $7 } }
;

bformula : IDENT  { Var $1 }
  | LPAREN bformula RPAREN { $2 }
  | bformula AND bformula  { Op(And,$1,$3) }
  | bformula OR bformula  { Op(Or,$1,$3) }
  | bformula IMPL bformula  { Op(Impl,$1,$3) }
  | bformula IFF bformula  { Op(Iff,$1,$3) }
  | NOT bformula          { Op(Impl,$2,False) }
;

