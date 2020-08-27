Require Import Lia.
Require Import Cdcl.Itauto.



Lemma foo1: forall (a: nat), a + a = a * 2.
Proof.
  Zify.zify.
  xlia zchecker.
Qed.

Lemma foo2: forall (a: nat), a + a = a * 2.
Proof.
  Zify.zify.
  Fail itauto (xlia zchecker).  (* xlia not found ? *)
Abort.

Ltac lia2 := xlia zchecker.

Lemma foo2: forall (a: nat), a + a = a * 2.
Proof.
  Zify.zify.
  itauto lia2.  (* works *)
Abort.
