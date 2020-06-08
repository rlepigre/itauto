gen_test : lexer.mll parser.mly formula.ml main.ml
	ocamlbuild main.native  -yaccflag -v -libs str
	mv main.native gen_test
