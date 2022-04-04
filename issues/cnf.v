Require Import Cdcl.Itauto.


Lemma eq_iff : forall (A B: Prop) , A = B -> A <-> B.
Proof.
  intros. rewrite H. tauto.
Qed.


Ltac remember_iff t v :=
  let H := fresh "Riff" in
  remember t as v eqn:H;
  apply eq_iff in H.

Lemma elim_and : forall (A B C : Prop),
    (A <-> B /\ C ) <-> (A -> B) /\ (A -> C) /\ (B -> C -> A).
Proof.
  tauto.
Qed.

Lemma elim_or : forall (A B C : Prop),
    (A <-> B \/ C ) <-> ((A -> B \/ C) /\ (B -> A) /\ (C -> A)).
Proof.
  tauto.
Qed.

Definition block (A: Prop) := A.

Lemma block_eq : forall (x: Prop), block x = x.
Proof.
  reflexivity.
Qed.
Opaque block.

Lemma elim_impl : forall (A B C : Prop),
    (A <-> (B ->  C) ) <-> ((block (B -> C) -> A) /\(A -> B -> C)).
Proof.
  tauto.
Qed.

Lemma elim_iff : forall (A B C : Prop),
    (A <-> (B <-> C)) <-> ((A -> B -> C) /\ (A ->C -> B) /\ (block (B -> C) -> block (C -> B) -> A)).
Proof.
  split ; intros.
  tauto.
  tauto.
Qed.

Ltac cnf :=
  repeat
    match goal with
    | H : _ <->  (_ /\ _) |- _ =>
        rewrite elim_and in H;
        let c1 := fresh "A1" in
        let c2 := fresh "A2" in
        let c3 := fresh "A3" in
        destruct H as (c1 & c2 & c3)
    | H : _ <->  (_ \/ _) |- _ =>
        rewrite elim_or in H;
        let c1 := fresh "O1" in
        let c2 := fresh "O2" in
        let c3 := fresh "O3" in
        destruct H as (c1 & c2 & c3)
    | H : _ <->  (_ ->  _) |- _ =>
        rewrite elim_impl in H;
        let c1 := fresh "I1" in
        let c2 := fresh "I2" in
        destruct H as (c1 & c2)
    | H : _ <->  (_ <->  _) |- _ =>
        rewrite elim_iff in H;
        let c1 := fresh "F1" in
        let c2 := fresh "F2" in
        let c3 := fresh "F3" in
        destruct H as (c1 & c2 & c3)

    end.

Ltac mp :=
  repeat match goal with
  | H : ?A , H2 : ?A -> ?B |- _ => specialize (H2 H)
  end.

Ltac prove_block :=
  match goal with
  | H : block ?A -> _ |- _ =>
      let n := fresh "PB" in
      assert (n:A) by
      (rewrite block_eq in *;
       itauto congruence); rewrite block_eq in H
  end.

Ltac dest_and :=
  repeat match goal with
  | H : ?A /\ ?B |- _ => destruct H
  end.
