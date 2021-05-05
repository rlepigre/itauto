Require Import ZArith List Lia ZifyClasses.
Declare ML Module "cdcl_plugin".
Require Import Cdcl.NOlia.

Goal forall x, 1 + x :: nil = x + 1 :: nil.
Proof.
  intros.
  smt.
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
  smt.
Qed.


Section test.
   Variable f : nat -> nat.

   Goal forall m n, f (m + n) = f (n + m).
   Proof.
     intros.
     smt.
   Qed.

   Goal forall m n, 2 * f (m + n) = (f (n + m)) * 2.
   Proof.
     intros.
     smt.
   Qed.

   Goal forall m n, n = m -> 2 * f n = f m * 2.
   Proof.
     intros.
     smt.
   Qed.
End test.

Axiom f : nat -> nat.
Goal forall m n, 2 * f (m + n) = f (m + n) + f (n + m).
Proof.
  intros.
  smt.
Qed.

Require Import Classical.

Open Scope Z_scope.
Goal forall (h g: Z -> Z) (a d x y: Z),
    g x = g y ->
    0 < d ->
    a < h (g y) ->
    a < h (g x) + d.
Proof.
  intros.
  smt.
Qed.
