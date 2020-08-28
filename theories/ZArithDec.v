(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)

(** Teach itauto that comparisons over Z are decidable *)
Require Import Cdcl.ReifClasses.
Require Import ZArith Lia.
Open Scope Z_scope.

Lemma dec_le : forall x y, x <= y \/ ~ x <= y.
Proof.
  lia.
Qed.

Lemma dec_lt : forall x y, x < y \/ ~ x < y.
Proof.
  lia.
Qed.

Lemma dec_ge : forall x y, x >= y \/ ~ x >= y.
Proof.
  lia.
Qed.

Lemma dec_gt : forall x y, x > y \/ ~ x > y.
Proof.
  lia.
Qed.

Lemma dec_eq : forall (x y:Z), x = y \/ ~ x = y.
Proof.
  lia.
Qed.

Instance DecLe : DecP2 Z.le := dec_le.
Instance DecLt : DecP2 Z.lt := dec_lt.
Instance DecGt : DecP2 Z.gt := dec_gt.
Instance DecEq : DecP2 (@eq Z) := dec_eq.
