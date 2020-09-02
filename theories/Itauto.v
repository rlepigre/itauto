(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)

Require Import Cdcl.Formula.
Require Export Cdcl.ReifClasses Cdcl.ZArithDec.
Require Import Lia.

Require Import List.
Require Import Int63.


Notation "'TTT'" := (HCons.mk _ _ TT).
Notation "'FFF'" := (HCons.mk _ _ FF).
Notation "A _/\_ B" := (HCons.mk _ _ (OP AND A B)) (at level 80).
Notation "A _\/_ B" := (HCons.mk _ _ (OP OR A B)) (at level 80).
Notation "A  -->  B" := (HCons.mk _ _ (OP IMPL A B)) (at level 80).
Notation "'AT' x" := (HCons.mk _ _ (AT x)) (at level 80).

Declare ML Module "cdcl_plugin".
Require Import Cdcl.Formula.


Ltac gen_conflicts tac :=
  intros; unfold not in *; unfold iff in *;
  (* Apply ~ ~ p -> p if Classical is loaded *)
  cdcl_nnpp; unfold not;
  (* Generate conflict clauses *)
  (cdcl_conflicts tac).

Ltac run_solver :=
  (* Generalize all the propositions
     (in reverse order to avoid problems with dependent hypotheses *)
  cdcl_generalize ;
  (* Reify the conclusion *)
  cdcl_change;
  let n := fresh in
  (intro n ;
  (* Apply soundness proof and compute *)
  apply (hcons_bprover_correct (KeyInt.nat_of_int n)); (* todo compute n *)
  vm_compute; reflexivity).

Ltac itauto_use_tauto := constr:(false).

Ltac itauton tac  :=
  gen_conflicts tac ;
  lazymatch itauto_use_tauto with
  | true => tauto
  | false => run_solver
  end.


Ltac itauto tac := itauton tac.

Ltac smt :=
  let tac := no congruence lia in
  (* zify of div mod generate propositional formulae *)
  Zify.zify ; itauton tac.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_post_hook ::= idtac. (* ZifyBool sets some nasty Ltac *)
