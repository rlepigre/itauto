Require Import Lia ZArith.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Unset Lia Cache.
Set Itauto Theory Time.

Ltac timing_lia := time "lia" lia.

Ltac timing_lia_core := time "lia_core" xlia zchecker.

(* to compare to not using itauto *)
(*Ltac better_lia :=
  time "old_lia" (
    Z.div_mod_to_equations;
    lia
  ).
*)

Ltac better_lia :=
  time "better_lia" (
    Z.div_mod_to_equations;
    Zify.zify;
    time "itauto" itauto lia
  ).


Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 ((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 <
 8 mod 2 ^ 64 * Z.of_nat length_x.
Proof.
  intros. better_lia. (* 0.351 secs *)
Qed.


Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64)
 mod (8 mod 2 ^ 64) = 0.
Proof.
  intros. better_lia. (* 0.288 secs *)
Qed.

Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 (x2 -
  ((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 + 8 mod 2 ^ 64) mod 2 ^ 64)
 mod 2 ^ 64 =
 8 *
 Z.of_nat
   (length_x -
    S
      (Z.to_nat
         (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 /
          (8 mod 2 ^ 64)))).
Proof.
  intros. better_lia. (* 5.838 secs *)
Qed.


Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 (length_x -
  S
    (Z.to_nat
       (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 /
        (8 mod 2 ^ 64))) < v)%nat.
Proof.
  intros. better_lia. (* 0.767 secs *)
Qed.

Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 ((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 <
 8 mod 2 ^ 64 * Z.of_nat length_x.
Proof.
  intros. better_lia. (* 0.358 secs *)
Qed.

Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64)
 mod (8 mod 2 ^ 64) = 0.
Proof.
  intros. better_lia. (* 0.3 secs *)
Qed.

Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 ((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 =
 8 *
 Z.of_nat
   (Init.Nat.min
      (Z.to_nat
         (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 /
          (8 mod 2 ^ 64))) length_x).
Proof.
  intros. better_lia. (* 0.809 secs *)
Qed.

Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 (Init.Nat.min
    (Z.to_nat
       (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 /
        (8 mod 2 ^ 64))) length_x < v)%nat.
Proof.
  intros. better_lia. (* 0.778 secs *)
Qed.

Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 ((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 <
 8 mod 2 ^ 64 * Z.of_nat length_x.
Proof.
  intros. better_lia. (* 0.354 secs *)
Qed.

Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64)
 mod (8 mod 2 ^ 64) = 0.
Proof.
  intros. better_lia. (* 0.298 secs *)
Qed.

Goal forall (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x2 x1 : Z) (length_x : nat),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat length_x ->
 length_x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 Z.to_nat
   (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 /
    (8 mod 2 ^ 64)) =
 Z.to_nat
   (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 /
    (8 mod 2 ^ 64)).
Proof.
  intros. better_lia. (* 0.14 secs *)
Qed.

Goal forall (word : Type) (right left : Z) (length_xs : nat),
 (right - left) mod 2 ^ 64 = 8 * Z.of_nat length_xs ->
 forall (v : nat) (x : list word) (x2 x1 : Z),
 (x2 - x1) mod 2 ^ 64 = 8 * Z.of_nat (Datatypes.length x) ->
 Datatypes.length x = v ->
 (x2 - x1) mod 2 ^ 64 <> 0 ->
 forall (x3 : Z) (z2w : word -> Z) (w2z : Z -> word) (f : list word -> word),
 z2w
   (if
     z2w
       (f
          (List.skipn
             (Z.to_nat
                (((x1 + Z.shiftl (Z.shiftr ((x2 - x1) mod 2 ^ 64) 4 mod 2 ^ 64) 3 mod 2 ^ 64) mod 2 ^ 64 - x1)
                 mod 2 ^ 64 / (8 mod 2 ^ 64))) x)) <? x3
    then w2z 1
    else w2z 0) <> 0 ->
 (x2 -
  ((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 + 8 mod 2 ^ 64) mod 2 ^ 64)
 mod 2 ^ 64 =
 8 *
 Z.of_nat
   (Datatypes.length x -
    S
      (Z.to_nat
         (((x1 + (((x2 - x1) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - x1) mod 2 ^ 64 /
          (8 mod 2 ^ 64)))).
Proof.
  intros.
  better_lia.  (* 57.007 secs *)
  (* Note: this one illustrates why calling zify twice (once in before calling itauto
     to expose the propositional structure to itauto, and a second time before the
     leaf-lia to do more preprocessing) can be beneficial:
     If we replace timing_lia by timing_lia_core in better_lia, this example will run
     slower, maybe even forever. *)
Qed.

Goal forall (w4 w5 : Z) (len1 : nat),
 (w4 - w5) mod 2 ^ 64 = 8 * Z.of_nat len1 ->
 forall (v : nat) (w2 w3 : Z) (len0 : nat),
 (w2 - w3) mod 2 ^ 64 = 8 * Z.of_nat len0 ->
 len0 = v ->
 (w2 - w3) mod 2 ^ 64 <> 0 ->
 forall w0 w1 : Z,
 (if w0 <? w1 then 1 mod 2 ^ 64 else 0 mod 2 ^ 64) <> 0 ->
 (w2 -
  ((w3 + (((w2 - w3) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 + 8 mod 2 ^ 64) mod 2 ^ 64)
 mod 2 ^ 64 =
 8 *
 Z.of_nat
   (len0 -
    S
      (Z.to_nat
         (((w3 + (((w2 - w3) mod 2 ^ 64 / 2 ^ 4) mod 2 ^ 64 * 2 ^ 3) mod 2 ^ 64) mod 2 ^ 64 - w3) mod 2 ^ 64 /
          (8 mod 2 ^ 64)))).
Proof.
  intros. better_lia. (* 3.826 secs *)
Qed.
