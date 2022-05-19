Require Import ZArith List Lra ZifyClasses.
Require Import ZArith.
Require Import Cdcl.NOlra.
Require Import Reals.
Open Scope R_scope.

Goal forall (x:R), 1 + x :: nil = x + 1 :: nil.
Proof.
  intros.
  smt.
Qed.

Close Scope  Z_scope.

Goal forall (P: R-> Prop) x, (P (1 + x) -> P (x + 1)).
Proof.
  intros.
  smt.
Qed.


Goal forall x, 1 + x = x + 1.
Proof.
  intros.
  smt.
Qed.



Goal forall x y (P:R -> Prop) (p:Prop),
    (x :: nil = y + 1 :: nil -> P (x - y) -> P 1).
Proof.
  intros.
  smt.
Qed.


Section test.
   Variable f : R -> R.

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

Axiom f : R  -> R.
Goal forall m n, 2 * f (m + n) = f (m + n) + f (n + m).
Proof.
  intros.
  smt.
Qed.

Require Import Classical.

Goal forall (h g: R -> R) (a d x y: R),
    g x = g y ->
    0 < d ->
    a < h (g y) ->
    a < h (g x) + d.
Proof.
  intros.
  smt.
Qed.

(* Reviewer 1 Coq Workshop 2021 (worst-case) *)

Goal forall f x0 x1 x2 x3 x4,
    f (x0 + 0)%R    = 0%R ->
    f (x1 + f x0)%R = 0%R ->
    f (x2 + f x1)%R = 0%R ->
    f (x3 + f x2)%R = 0%R ->
    f (x4 + f x3)%R = 0%R ->
    f x4 = 0%R.
Proof.
Time intros; smt.
Qed.
