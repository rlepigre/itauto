# For debugging purposes, it is desirable to patch the Coq extracted code
# This is done by calling `make prover` once the Coq code is extracted

.PHONY: clean cleanaux coq test cleantest benchmark

-include CoqMakefile.conf

ifneq (,$(COQBIN))
# add an ending /
COQBIN:=$(COQBIN)/
endif


all : src/proverPatch.ml
	rm -f src/cdcl.ml.d
	rm -f src/cdcl_plugin.mlpack.d
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

UINT := $(shell coqc -config | grep COQLIB | cut -f2 -d'=')/kernel




src/prover.cmx : src/prover.ml
	ocamlc -annot -I $(UINT) -rectypes -c src/prover.mli
	ocamlc -annot -I $(UINT) -I src -rectypes -c src/prover.ml

install :
	make -f CoqMakefile install

uninstall:
	make -f CoqMakefile uninstall

cleanaux : 
	rm -f src/prover.*  src/proverPatch.ml src/patch/mlpatch

clean : cleanaux
	make -f CoqMakefile clean
	rm CoqMakefile.conf


CoqMakefile CoqMakefile.conf : _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile


TESTSUITE = arith.v no_test.v refl_bool.v
ISSUES    = issue_0.v issue_2.v issue_3.v issue_5.v issue_6.v issue_8.v issue_9.v issue_10.v \
	issue_11.v issue_12.v issue_13.v issue_14.v issue_15.v issue_16.v issue_19.v issue_20.v issue_21.v \
	issue_22.v issue_23.v issue_cc.v

ALLTESTV = $(addprefix test-suite/,$(TESTSUITE)) $(addprefix issues/,$(ISSUES))
ALLTESTVO = $(ALLTESTV:.v=.vo)

BENCH = pigeon_hole.v
ALLBENCHV = $(addprefix benchmark/,$(BENCH))
ALLBENCHVO = $(ALLBENCHV:.v=.vo)

COQC ?= "$(COQBIN)coqc"

%.vo : %.v
	$(COQC) $(COQMF_COQLIBS_NOML) $<

test : $(ALLTESTVO)

benchmark : $(ALLBENCHVO)

cleantest :
	rm -f $(ALLTESTVO)



