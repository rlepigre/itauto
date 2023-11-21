Require Import Cdcl.Itauto.

Open Scope bool_scope.

Require Import Btauto.

Lemma test_neg_involutive b :  negb (negb b) = b.
Proof.
  itauto. Qed.

Lemma test_orb a b : (if a || b then negb (negb b && negb a) else negb a && negb b) = true.
Proof.
  itauto. Qed.

Lemma test_xorb a : xorb a a = false.
Proof. itauto. Qed.

