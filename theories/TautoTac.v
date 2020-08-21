Require Import Cdcl.Formula.
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

Ltac tauton tac n :=
  intros; unfold not in *; unfold iff in *;
  cdcl_nnpp; unfold not;
  (cdcl_conflicts tac);
  cdcl_change;
  apply (hcons_bprover_correct n);
  vm_compute; reflexivity.

Ltac tauto := tauton idtac 100%nat.
Tactic Notation "tauto" := tauto.
Tactic Notation "tauto" tactic(tac) := tauton tac 100%nat.

Ltac smt :=
  let tac := no congruence lia in
  tauton tac 100%nat.
