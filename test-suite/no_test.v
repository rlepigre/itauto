Require Import ZArith List Lia.
Declare ML Module "cdcl_plugin".

Require Import Cdcl.Formula.
Require Import Cdcl.Itauto.

Goal forall x, 1 + x :: nil = x + 1 :: nil.
Proof.
  intros.
  no congruence lia.
Qed.

Close Scope  Z_scope.

Goal forall (P: nat-> Prop) x, (P (1 + x) -> P (x + 1)).
Proof.
  intros.
  smt.
Qed.


Goal forall x, 1 + x = x + 1.
Proof.
  intros.
  smt.
Qed.



Goal forall x y (P:nat -> Prop) (p:Prop),
    (x :: nil = y + 1 :: nil -> P (x - y) -> P 1).
Proof.
  intros.
  no congruence lia.
Qed.

Goal forall x y (P:nat -> Prop) (p:Prop),
    x::nil = y + 1 :: nil ->
    P (x-y) ->
    P 1.
Proof.
  intros.
  no  congruence lia.
Qed.

Section test.
   Variable f : nat -> nat.

   Goal forall m n, f (m + n) = f (n + m).
   Proof.
     intros.
     no congruence lia.
   Qed.

   Goal forall m n, 2 * f (m + n) = (f (n + m)) * 2.
   Proof.
     intros. no congruence lia.
   Qed.

   Goal forall m n, n = m -> 2 * f n = f m * 2.
   Proof.
     intros.
     purify.
     no congruence lia.
   Qed.
End test.

Axiom f : nat -> nat.
Goal forall m n, 2 * f (m + n) = f (m + n) + f (n + m).
Proof.
  intros.
  no congruence lia.
Qed.
