Require Import Bool Arith Cdcl.ReifClasses.

Lemma is_true_le : forall a b, a <= b <-> Is_true (a <=? b).
Proof.
  intros.
  rewrite <- Nat.leb_le.
  unfold Is_true.
  destruct (a <=? b); intuition congruence.
Qed.

Instance leb_le : Reflect.Rbool2 leb := Reflect.mkrbool2 _ _ leb le is_true_le.
Instance le_leb : Reflect.RProp2 le := Reflect.mkrProp2 _ _ le leb is_true_le.

Require Import Cdcl.Itauto.
Require Import Int63.

Lemma map : forall a b, Is_true (a <=? b) -> a <= b.
Proof.
  intros a b.
  itauto idtac.
Qed.
