Require Import Rtauto.
Require Import pigeon_hole.

Goal pigeon_hole 1 0 -> False.
Proof.
  unfold pigeon_hole. cbn.
  Time  rtauto.
Time Qed.

Goal pigeon_hole 2 1 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  rtauto.
Time Qed.

Goal pigeon_hole 3 2 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  rtauto.
Time Qed.

Goal pigeon_hole 4 3 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  timeout 1000 rtauto.
Time Qed.

Goal pigeon_hole 5 4 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  timeout 1000 rtauto.
Time Qed.

Goal pigeon_hole 6 5 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  timeout 1000 rtauto.
Time Qed.

Goal pigeon_hole 7 6 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  timeout 1000 rtauto.
Time Qed.

Goal pigeon_hole 8 7 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  timeout 1000 rtauto.
Time Qed. (* Qed blows up *)

Goal pigeon_hole 9 8 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  timeout 1000 rtauto.
Time Qed.

(* pigeon 1 *)

(* pigeon 2 *)

(* pigeon 3 *)

(* pigeon 4 *)

(* pigeon 5 *)

(* pigeon 6 *)

(* pigeon 7 *)

(* pigeon 8 *)

(* pigeon 9 *)
