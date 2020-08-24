mlpatch : lexer.mll parser.mly patch.ml main.ml
	ocamlbuild main.native  -yaccflag -v -libs str
	mv main.native mlpatch

clean :
	ocamlbuild -clean
