COQLIB = /home/fbesson/.opam/coq-fajb/lib/coq/kernel

all : CoqMakefile
	make -f CoqMakefile

src/prover.ml : theories/Formula.vo theories/Formula.v
	cd theories ; coqc  Prover.v

src/prover.cmx : src/prover.ml
	rm -f src/prover.mli
	ocamlopt -rectypes -c src/prover.ml -bin-annot -I $(COQLIB)


src/proverPatch.ml : src/prover.cmx src/ppprover.ml
	./src/patch/mlpatch -ifile src/prover.ml -pfile src/ppprover.ml > src/proverPatch.in
	ocamlformat src/proverPatch.in > src/proverPatch.ml

prover :  src/proverPatch.ml 

install :
	make -f CoqMakefile install

clean :
	make -f CoqMakefile clean

CoqMakefile : _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

