Require Import Lia Cdcl.Itauto.

Lemma foo1: forall (a: nat), a + a = a * 2.
Proof.
  Zify.zify; itauto (xlia zchecker).
Qed.
