From Coq Require Import  ZArith Zify ZifyClasses ZifyBool ZifyInst Lia.

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.zify Require Import zify.


Require Import Cdcl.NOlia.

Local Open Scope Z_scope.

(* arith on Z *)
Lemma foo_Z (x : Z) : 1 + x = x + 1.
Proof. lia. Qed.

(* eq + arith on Z *)
Lemma foo_f (f : Z -> Z) (x : Z) : f (1 + x) = f (x + 1).
Proof. smt. Qed.

Import Order.Theory.
Import GRing.Theory.

Local Open Scope ring_scope.

(* arith on int, thx to mczify's instances *)
Lemma foo_int (x : int) : 1 + x = x + 1.
Proof. lia. Qed.

Lemma foo_f_int (f : int -> int) (x : int) : f (1 + x) = f (x + 1).
Proof.
  smt.
Qed.
