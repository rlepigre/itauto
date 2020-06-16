Require Import Cdcl.Patricia.
Require Import ZArith Lia ZifyClasses.
Require  Int63 Cdcl.ZifyInt.
Require Import Bool.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Section S.
  Import Int63.
  Definition zero := 0%int63.
  Definition one  := 1%int63.
End S.

Module KInt.

  Definition t := Int63.int.
  Definition zero : t := zero.
  Definition land : t -> t -> t := Int63.land.
  Definition lxor: t -> t -> t := Int63.lxor.
  Definition lopp: t -> t := Int63.opp.
  Definition ltb: t -> t -> bool := Int63.ltb.

  Definition int_of_nat (n:nat) := Int63.of_Z (Z.of_nat n).


  Program Instance Op_int_of_nat : UnOp int_of_nat :=
  {| TUOp := (fun x => (x mod 9223372036854775808%Z)%Z); TUOpInj := _ |}.
  Proof.
  Next Obligation.
    apply Int63.of_Z_spec.
  Defined.
  Add UnOp Op_int_of_nat.

  Definition eqb  := Int63.eqb.

  Definition testbit (i:t) (n:nat) :=
    Int63.bit i (int_of_nat n).

  Definition interp (i:t) := (Int63.sub i one).

  Definition is_mask (m: t) (n: nat) := forall p, testbit m p = true <-> n = p.

  Lemma zero_spec: forall n, testbit zero n = false.
  Proof.
    intros. unfold testbit,zero.
    apply Int63.bit_0.
  Qed.


  Lemma eqb_spec : forall k1 k2, eqb k1 k2 = true <-> k1 = k2.
  Proof.
    unfold eqb.
    split ; intros.
    apply Int63.eqb_correct; auto.
    apply Int63.eqb_complete; auto.
  Qed.

  Lemma testbit_spec: forall k1 k2, (forall n, testbit k1 n = testbit k2 n) -> k1 = k2.
  Proof.
    intros.
    unfold testbit in *.
    apply Int63.bit_ext;auto ; intros.
    specialize (H (Z.to_nat (Int63.to_Z n))).
    assert ( int_of_nat (Z.to_nat (Int63.to_Z (n)))  = n) by lia.
    congruence.
  Qed.
    
  Lemma interp_spec: forall m n, is_mask m n -> forall p, testbit (interp m) p = true <-> (p < n)%nat.
  Proof.
    unfold is_mask,testbit,interp.
    intros.
  Admitted.


  Lemma land_spec: forall n k1 k2, testbit (land k1 k2) n = testbit k1 n && testbit k2 n.
  Proof. intros. apply Int63.land_spec. Qed.


  Lemma lxor_spec: forall n k1 k2, testbit (lxor k1 k2) n = xorb (testbit k1 n) (testbit k2 n).
  Proof. intros. apply Int63.lxor_spec. Qed.

  Import Int63.

  Lemma lopp_spec_low: forall k m, (forall p, (p < m)%nat -> testbit k p = false) -> testbit k m = true -> forall p, (p < m)%nat -> testbit (lopp k) p = false.
  Proof.
    intros.
    unfold lopp.
  Admitted.

  Lemma lopp_spec_eq: forall k m, (forall p, (p < m)%nat -> testbit k p = false) -> testbit k m = true -> testbit (lopp k) m = true.
  Proof.
  Admitted.

  Lemma lopp_spec_high: forall k m, (forall p, (p < m)%nat -> testbit k p = false) -> testbit k m = true -> forall p, (p > m)%nat -> testbit (lopp k) p = negb (testbit k p).
  Proof.
  Admitted.

  Lemma ltb_spec: forall m1 n1 m2 n2, is_mask m1 n1 -> is_mask m2 n2 -> (ltb m1 m2 = true <-> (n1 < n2)%nat).
  Proof.
  Admitted.

  Lemma LPO_pos : forall x, exists p, Pos.testbit x p = true.
  Proof.
    induction x.
    - simpl. exists 0%N. reflexivity.
    - simpl. destruct IHx.
      exists (x0+1)%N.
      destruct (x0+1)%N eqn:EQ.
      lia.
      assert (Pos.pred_N p = x0).
      lia.
      congruence.
    - simpl. exists 0%N.
      reflexivity.
  Qed.

  Lemma LPO : forall (k:t), k <> zero -> exists p, testbit k p = true.
  Proof.
  Admitted.

End KInt.


Module PTrie := PTrie(KInt).
