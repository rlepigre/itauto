(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)

Require Import Cdcl.Formula.
Require Export Cdcl.ReifClasses.
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

Ltac itauton tac n :=
  intros; unfold not in *; unfold iff in *;
  cdcl_nnpp; unfold not;
  (cdcl_conflicts tac);
  cdcl_change;
  apply (hcons_bprover_correct n);
  vm_compute; reflexivity.

Ltac itauto := itauton idtac 100%nat.
Tactic Notation "itauto" := itauto.
Tactic Notation "itauto" tactic(tac) := itauton tac 100%nat.

Ltac smt :=
  let tac := no congruence lia in
  (* zify of div mod generate propositional formulae *)
  Zify.zify ; itauton tac 100%nat.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_post_hook ::= idtac. (* ZifyBool sets some nasty Ltac *)
