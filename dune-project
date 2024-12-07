(lang dune 3.15)
(using coq 0.8)
(name coq-itauto)

(generate_opam_files)

(maintainers "Frédéric Besson <frederic.besson@inria.fr>")
(authors "Frédéric Besson <frederic.besson@inria.fr>")
(homepage "https://gitlab.inria.fr/fbesson/itauto")
(source (uri "git+https://gitlab.inria.fr/fbesson/itauto.git"))
(bug_reports "https://gitlab.inria.fr/fbesson/itauto/-/issues")
(license MIT)

(package
 (name coq-itauto)
 (synopsis "Reflexive SAT solver with Nelson-Oppen support, parameterised by a leaf tactic inside Coq")
 (description "itauto is a reflexive intuitionistic SAT solver parameterised by a theory module. \
When run inside Coq, the theory module wraps an arbitrary Coq tactic, e.g., the lia \
solver for linear arithmetic or the congruence solver for uninterpreted function symbols \
and constructors. Using a black-box Nelson-Oppen scheme for combination of theories, \
itauto also provides an SMT-like tactic for propositional reasoning modulo the solvers for \
both arithmetic and function symbols.")
 (depends
  (ocaml (>= "4.9~"))
  (coq (= "dev"))
  (coq-mathcomp-zify :with-test))
 (tags
  ("category:Miscellaneous/Coq Extensions"
   "category:Computer Science/Decision Procedures and Certified Algorithms/Decision procedures"
   "keyword:integers"
   "keyword:SAT"
   "keyword:SMT"
   "keyword:Nelson-Oppen"
   "keyword:automation"
   "logpath:Cdcl")))
