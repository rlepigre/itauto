Require Import Lia ZArith.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Unset Lia Cache.
Set Itauto Theory Time.

Ltac lia_core := xlia zchecker.

Ltac enhanced_lia := Zify.zify; itauto lia_core.

Goal forall (right left : Z) (length_xs v : nat) (x2 x1 : Z) (length_x : nat),
  (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
  (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
  length_x = v ->
  (x2 - x1) mod 2 ^ 64 <> 0 ->
  0 <= 8 * Z.of_nat length_x < 2 ^ 64 ->
  (x1 + (8 * Z.of_nat length_x) mod 2 ^ 64 / 2 ^ 4 * 2 ^ 3 - x1) mod 2 ^ 64 <
  8 * Z.of_nat length_x.
Proof.
  intros.
  Z.div_mod_to_equations.
(*  Time lia. (* 16.583 secs *) *)
  (*  Time itauto lia. (* Theory running time 16.979, Finished transaction in 34.413 secs *)*)
  Time enhanced_lia. (* Theory running time 19.474, Finished transaction in 41.531 secs *)
Qed.
