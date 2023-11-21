# For debugging purposes, it is desirable to patch the Coq extracted code
# This is done by calling `make prover` once the Coq code is extracted

.PHONY: clean cleanaux coq test cleantest benchmark paper

.NOTPARALLEL:

-include CoqMakefile.conf

ifneq (,$(COQBIN))
# add an ending /
COQBIN:=$(COQBIN)/
endif

VFILES := Lit.v Clause.v CnfSolver.v Formula.v Syntax.v KeyInt.v  Lib.v PatriciaR.v  Prover.v  ReifClasses.v  Tac.v 
VFILESTHY := $(addprefix theories/,$(VFILES))
ALLVFILES := Itauto.v  NOlia.v Itauto.v Ctauto.v $(VFILES)
ALLVFILESTHY := $(addprefix theories/,$(ALLVFILES))

all : CoqMakefile CoqMakefile_ml src/patch/mlpatch.exe $(ALLVFILESTHY) 
	$(MAKE) -f CoqMakefile_ml  COQBIN=$(COQBIN) 


src/prover.ml :  CoqMakefile $(VFILESTHY)
	$(MAKE) -f CoqMakefile theories/CnfSolver.vo COQBIN=$(COQBIN) 
	$(MAKE) -f CoqMakefile theories/Prover.vo COQBIN=$(COQBIN) 

src/patch/mlpatch.exe :
	$(MAKE) -C src/patch

HASOCAMLFORMAT := $(shell command -v ocamlformat 2> /dev/null)

src/proverPatch.in : src/prover.ml src/ppprover.ml src/patch/mlpatch.exe
	./src/patch/mlpatch.exe -ifile src/prover.ml -pfile src/ppprover.ml > src/proverPatch.in

src/proverPatch.ml : src/proverPatch.in
ifdef $(HASOCAMLFORMAT)
	ocamlformat src/proverPatch.in > src/proverPatch.ml
else
	cp src/proverPatch.in src/proverPatch.ml
endif


.merlin : CoqMakefile_ml
	$(MAKE) -f CoqMakefile_ml .merlin

src/cdcl_plugin.cmxs  : CoqMakefile_ml src/cdcl.ml
	$(MAKE) -f CoqMakefile_ml src/cdcl_plugin.cmxs COQBIN=$(COQBIN) 

CoqMakefile_ml CoqMakefile_ml.conf : src/proverPatch.ml
	$(COQBIN)coq_makefile -f _CoqProject_ml -o CoqMakefile_ml

CoqMakefile CoqMakefile.conf : _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile



UINT := $(shell $(COQBIN)coqc -config | grep COQCORELIB | cut -f2 -d'=')/kernel

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
	$(MAKE) -C src/patch clean
	rm -f CoqMakefile.conf CoqMakefile CoqMakefile_ml CoqMakefile_ml.conf




TESTSUITE = arith.v  refl_bool.v no_test_lia.v no_test_lra.v btauto.v comp.v
ISSUES    =  cnf.v issue_2.v issue_3.v issue_5.v issue_6.v issue_8.v issue_9.v issue_10.v \
	issue_11.v issue_12.v issue_13.v issue_14.v issue_15.v issue_16.v issue_19.v issue_20.v issue_21.v \
	issue_22.v issue_23.v issue_cc.v issue_25.v issue_28.v

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


