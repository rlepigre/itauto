all : CoqMakefile
	make -f CoqMakefile

prover :theories/Formula.v
	find . -name prover.cmi -exec rm {} \;
	find . -name prover.mli -exec rm {} \;

install :
	make -f CoqMakefile install

clean :
	make -f CoqMakefile clean

CoqMakefile : _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

