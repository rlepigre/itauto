# For debugging purposes, it is desirable to patch the Coq extracted code
# This is done by calling `make prover` once the Coq code is extracted

.PHONY: clean cleanaux coq test cleantest benchmark paper

-include CoqMakefile.conf

ifneq (,$(COQBIN))
# add an ending /
COQBIN:=$(COQBIN)/
endif


all : theories/Itauto.vo theories/NOlia.vo theories/NOlra.vo

theories/Prover.vo src/prover.ml : CoqMakefile 
	$(MAKE) -f CoqMakefile theories/Prover.vo COQBIN=$(COQBIN) 

theories/Itauto.vo : theories/Itauto.v theories/Prover.vo src/cdcl_plugin.cmxs  CoqMakefile_ml
	$(MAKE) -f CoqMakefile_ml theories/Itauto.vo COQBIN=$(COQBIN)

theories/NOlia.vo : theories/NOlia.v theories/Itauto.vo src/cdcl_plugin.cmxs  CoqMakefile_ml
	$(MAKE) -f CoqMakefile_ml theories/NOlia.vo COQBIN=$(COQBIN) 

theories/NOlra.vo : theories/NOlra.v theories/Itauto.vo src/cdcl_plugin.cmxs  CoqMakefile_ml
	$(MAKE) -f CoqMakefile_ml theories/NOlra.vo COQBIN=$(COQBIN) 


src/cdcl_plugin.cmxs CoqMakefile_ml CoqMakefile_ml.conf : src/proverPatch.ml src/no.ml
	$(COQBIN)coq_makefile -f _CoqProject_ml -o CoqMakefile_ml
	$(MAKE) -f CoqMakefile_ml src/cdcl_plugin.cmxs COQBIN=$(COQBIN) 

CoqMakefile CoqMakefile.conf : _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

src/patch/mlpatch :
	cd src/patch ; $(MAKE)

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
	$(MAKE) -f CoqMakefile install
	$(MAKE) -f CoqMakefile_ml install

uninstall:
	$(MAKE) -f CoqMakefile uninstall

cleanaux : 
	rm -f src/prover.*  src/proverPatch.ml src/patch/mlpatch

clean : cleanaux
	$(MAKE) -f CoqMakefile clean
	$(MAKE) -f CoqMakefile_ml clean
	rm -f CoqMakefile.conf CoqMakefile CoqMakefile_ml CoqMakefile_ml.conf




TESTSUITE = arith.v  refl_bool.v no_test_lia.v no_test_lra.v
ISSUES    = issue_2.v issue_3.v issue_5.v issue_6.v issue_8.v issue_9.v issue_10.v \
	issue_11.v issue_12.v issue_13.v issue_14.v issue_15.v issue_16.v issue_19.v issue_20.v issue_21.v \
	issue_22.v issue_23.v issue_cc.v

ALLTESTV = $(addprefix test-suite/,$(TESTSUITE)) $(addprefix issues/,$(ISSUES))
ALLTESTVO = $(ALLTESTV:.v=.vo)

BENCH = pigeon_hole.v
ALLBENCHV = $(addprefix benchmark/,$(BENCH))
ALLBENCHVO = $(ALLBENCHV:.v=.vo)

COQC ?= $(COQBIN)coqc

%.vo : %.v
	$(COQC) $(COQMF_COQLIBS_NOML) $<

test : $(ALLTESTVO)

benchmark : $(ALLBENCHVO)

cleantest :
	rm -f $(ALLTESTVO)


