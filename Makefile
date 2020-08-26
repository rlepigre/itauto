# For debugging purposes, it is desirable to patch the Coq extracted code
# This is done by calling `make prover` once the Coq code is extracted

.PHONY: clean cleanaux coq

all : src/proverPatch.ml
	rm src/cdcl.ml.d
	rm src/cdcl_plugin.mlpack.d
	make -f CoqMakefile 

coq :
	make -f CoqMakefile theories/Prover.vo

theories/Prover.vo src/prover.ml : CoqMakefile coq




src/patch/mlpatch :
	cd src/patch ; make 

HASOCAMLFORMAT := $(shell command -v ocamlformat 2> /dev/null)

src/proverPatch.in : src/prover.ml src/ppprover.ml src/patch/mlpatch
	./src/patch/mlpatch -ifile src/prover.ml -pfile src/ppprover.ml > src/proverPatch.in

src/proverPatch.ml : src/proverPatch.in
ifdef $(HASOCAMLFORMAT)
	ocamlformat src/proverPatch.in > src/proverPatch.ml
else
	cp src/proverPatch.in src/proverPatch.ml
endif

install :
	make -f CoqMakefile install

uninstall:
	make -f CoqMakefile uninstall

cleanaux : 
	rm -f src/prover.*  src/proverPatch.ml src/patch/mlpatch

clean : cleanaux
	make -f CoqMakefile clean


CoqMakefile : _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

