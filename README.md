# itauto : a micro intuitionistic SMT for the Coq proof assistant

## Contexte and Motivation

The Coq proof assistant features several decision procedures for various logic fragments.
For instance, we have:

- `tauto` for propositional logic 
- `btauto` for boolean logic 
- `congruence` for uninterpreted function symbols (and constructors)
- `lia` for linear integer arithmetic 

However, there is currently no satisfactory scheme for combining the
above.  The traditional way to combine `tauto` with `congruence` is to
invoke `intuition congruence`. This approach is not satistactory
because it is neither complete nor efficient.  

### Example of incompleteness

Consider the following goal:

```coq
Goal forall {A: Type} (x y z: A) (p: Prop), x = y -> y = z -> (x = z -> p) -> p.
Proof.
intros.
Fail intuition congruence.
Abort.
```
`intuition` is unable to make any propositional progress and
therefore calls `congruence` which is unable to solve the goal. 
A successful strategy would be to ask `congruence` to prove `x = z`; perform *modus ponens* and conclude.

### Example of (non-)efficiency

Consider a smiliar goal where the conclusion is of the form `A /\ A`.

```coq
Goal forall {A: Type} (x y z: A), x = y -> y = z -> x = z /\ x = z.
Proof.
intros.
intuition congruence.
Qed.
```

In this case, `congruence` is called twice. A better strategy would be to reuse the proof of `x=z`.
In other words, reuse learned theory clauses along the propositional proof search.

## Installation

The development uses a fork of coq https://github.com/fajb/coq/tree/for_itauto

Clone the current repository:

`git clone https://gitlab.inria.fr/fbesson/itauto.git`

and move to the `itauto` directory.

### Using opam

`opam pin add coq https://github.com/fajb/coq.git#for_itauto`

`opam install .`

### Manual install

Once de dependancies are build:

- `coq` from `https://github.com/fajb/coq.git#for_itauto`
- `ocamlbuild` https://ocaml.org/learn/tutorials/

In the `itauto` top directory, `make; make install` builds and installs the plugin.

## Usage

A few relevant tests are found in the `test-suite` directory.

`Require Import Cdcl.Itauto` defines the `itauto` tactic.  

`itauto tac` calls `tac` when no propositional progress is possible.

The `smt` tactic is `itauto` using as theory solver a combination à la Nelson-Oppen of `congruence` and `lia`.

## Limitations

This is still an early prototype. Do not hesitate to report bugs by [email](mailto:frederic.besson@inria.fr) 
or fill an issue https://gitlab.inria.fr/fbesson/itauto/-/issues .

Know limitations:

- Proofs may depend on unused section variables (see https://gitlab.inria.fr/fbesson/itauto/-/issues/3 ). 
  A workaround is to instruct `itauto` to finish the proof using `tauto`. This may put some pressure on `tauto`.

`Ltac itauto_use_tauto ::= constr:(true).` (false by default)


## Internals

### A hybrid reflective intuitionitic SMT core

In Coq, we have a reflexive intuitionistic SAT solver parametrised by a
theory module.  The theory module takes an input a clause of the form
$`p_1 \to \dots \to p_n \to q_1 \lor \dots \lor q_n`$
and returns and unsat core that
is used by the SAT solver for the rest of the proof.

In Ocaml, the SAT solver is run and the theory module wraps an arbitrary
Coq tactic. The unsat core being obtained by analysing the proof-term.

Once the SAT solver has succeeded. All the unsat cores are asserted in
the original goal. Eventually, the reflexive SAT solver is rerun  in Coq
using an empty theory.

### Nelson-Oppen combination

We also have a naive Nelson-Oppen scheme allowing to combine `congruence` and `lia`.

### Design of the sat solver

The SAT solver is intuitionistic but follows the structure of a
classic DPLL SAT solver with a few modifications to account for the
specificities of intuitionistic logic.  

- The input formula is first hash-consed and thus each sub-formula is
identified by a unique primitive integer.

- The input formula is transformed using a definitional cnf
and we obtain a set of clauses of the following form $` p_1 \to \dots
\to p_n \to q_1 \lor \dots \lor q_n `$ 

After this pre-processing, the SAT solver iterates unit-propgation and
case-splits.

- unit propagation is implemented using a variation of head tail pointers.

- When unit propatation is done, the solver branches over a clause of
the form $` q_1 \lor \dots \q_n `$ 

- When there is no disjunction to branch over, the solver searches for
a literal bound to a formula of the form $`f \to g `$ and tried to
prove $`g`$ assuming $`f`$.  

- When no propositional progress is possible, a clause is built and
sent to the theory prover. If a conflict clause is generated, the SAT
solver continues.

### Future work

- **Backjumping** requires to track dependencies of used decisions.

- **Conflict Driven Clause Learning** requires a finer tracking of dependencies to detect the set of input clauses responsible for a conflict.

