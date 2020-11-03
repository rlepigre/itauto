Require Import Cdcl.Itauto.
Require Import pigeon_hole.

Goal pigeon_hole true 1 0 -> False.
Proof.
  simpl_pigeon.
  Time  vitautog.
  Time Qed.

Goal pigeon_hole true 2 1 -> False.
Proof.
  simpl_pigeon.
  Time  vitautog.
Time Qed.

Goal pigeon_hole true 3 2 -> False.
Proof.
  simpl_pigeon.
Time  vitautog.
Time Qed.

Goal pigeon_hole true 4 3 -> False.
Proof.
  simpl_pigeon.
Time  vitautog.
Time Qed.

Goal pigeon_hole false 5 4 -> False.
Proof.
  simpl_pigeon.
Time  vitautog.
Time Qed.

Goal pigeon_hole true 6 5 -> False.
Proof.
  simpl_pigeon.
Time  vitautog.
Time Qed.

Goal pigeon_hole true 7 6 -> False.
Proof.
  simpl_pigeon.
Time  vitautog.
Time Qed.

Goal pigeon_hole true 8 7 -> False.
Proof.
  simpl_pigeon.
Time  vitautog.
Time Qed.

Goal pigeon_hole true 9 8 -> False.
Proof.
  simpl_pigeon.
Time  vitautog.
Time Qed.

(* Using P i k -> P j k -> False *)

(* pigeon 1 *)
(*Finished transaction in 0.021 secs (0.013u,0.005s) (successful) *)
(*Finished transaction in 0.008 secs (0.005u,0.002s) (successful) *)

(* pigeon 2 *)
(* Finished transaction in 0.044 secs (0.023u,0.021s) (successful) *)
(* Finished transaction in 0.027 secs (0.018u,0.009s) (successful) *)

(* pigeon 3 *)
(* Finished transaction in 0.136 secs (0.1u,0.034s) (successful) *)
(* Finished transaction in 0.012 secs (0.012u,0.s) (successful) *)

(* pigeon 4 *)
(* Finished transaction in 0.137 secs (0.136u,0.s) (successful) *)
(* Finished transaction in 0.062 secs (0.061u,0.s) (successful) *)

(* pigeon 5 *)
(* Finished transaction in 0.365 secs (0.362u,0.001s) (successful) *)
(* Finished transaction in 0.144 secs (0.143u,0.s) (successful) *)

(* pigeon 6 *)
(* Finished transaction in 1.141 secs (1.134u,0.002s) (successful) *)
(* Finished transaction in 0.601 secs (0.595u,0.s) (successful) *)

(* pigeon 7 *)
(* Finished transaction in 5.607 secs (5.574u,0.009s) (successful) *)
(* Finished transaction in 4.579 secs (4.555u,0.003s) (successful) *)

(* pigeon 8 *)
(* Finished transaction in 44.294 secs (44.15u,0.015s) (successful) *)
(* Finished transaction in 41.726 secs (41.638u,0.004s) (successful) *)

(* pigeon 9 *)
(* Finished transaction in 437.165 secs (436.209u,0.09s) (successful) *)
(* Finished transaction in 438.732 secs (437.6u,0.048s) (successful) *)

(* Using ~ P i k \/ ~ P j k  - here, bad performance -- this is the same for rtauto *)
