# For debugging purposes, it is desirable to patch the Coq extracted code
# This is done by calling `make prover` once the Coq code is extracted

.PHONY: clean cleanaux coq test cleantest

all : src/proverPatch.ml
	rm src/cdcl.ml.d
	rm src/cdcl_plugin.mlpack.d
	make -f CoqMakefile 

coq : CoqMakefile
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


TESTSUITE = arith.v no_test.v refl_bool.v
ISSUES    = issue_0.v issue_2.v issue_3.v issue_5.v issue_6.v issue_8.v issue_9.v issue_10.v \
	issue_12.v

ALLTESTV = $(addprefix test-suite/,$(TESTSUITE)) $(addprefix issues/,$(ISSUES))
ALLTESTVO = $(ALLTESTV:.v=.vo)

-include CoqMakefile.conf

ifneq (,$(COQBIN))
# add an ending /
COQBIN:=$(COQBIN)/
endif

COQC ?= "$(COQBIN)coqc"

%.vo : %.v
	$(COQC) $(COQMF_COQLIBS_NOML) $<

test : $(ALLTESTVO)

cleantest :
	rm -f $(ALLTESTVO)
