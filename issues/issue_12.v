Require Import Lia ZArith.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Variable F : nat -> Prop.

Fixpoint orn (n : nat) := match n with
                          | O => F 0
                          | S m => F n \/ orn m
                          end.

Axiom Fbad : forall n, F n -> False.

Ltac appFBad := intros;lazymatch goal with
                | H : F ?n |- _ => exfalso ; apply (Fbad n H)
                end.

Goal forall (P:Prop), orn 50 -> P.
Proof.
  simpl.
  Time itauto appFBad.
Qed.

Goal orn 50 -> False.
Proof.
  simpl.
  Time itauto appFBad.
Qed.

Goal
  4 = 3 \/
  5 = 3 \/
  6 = 3 \/
  7 = 3 \/
  8 = 3 \/
  9 = 3 \/
  10 = 3 \/
  11 = 3 \/
  12 = 3 \/
  13 = 3 \/
  14 = 3 \/
  15 = 3 \/
  16 = 3 \/
  17 = 3 \/
  18 = 3 \/
  19 = 3 \/
  20 = 3 \/
  21 = 3 \/
  22 = 3 \/
  23 = 3 \/
  24 = 3 \/
  25 = 3 \/
  26 = 3 \/
  27 = 3 \/
  28 = 3 \/
  29 = 3 \/
  30 = 3 \/
  31 = 3 \/
  False ->
  False.
Proof.
  intros.
  (* lia. succeeds immediately *)
  Time itauto lia.
Qed.
