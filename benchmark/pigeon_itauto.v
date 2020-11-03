Require Import Cdcl.Itauto.
Require Import pigeon_hole.

Goal pigeon_hole 1 0 -> False.
Proof.
  unfold pigeon_hole. cbn.
  Time  vitauto.
Time Qed.

Goal pigeon_hole 2 1 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  vitauto.
Time Qed.

Goal pigeon_hole 3 2 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  vitauto.
Time Qed.

Goal pigeon_hole 4 3 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  vitauto.
Time Qed.

Goal pigeon_hole 5 4 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  vitauto.
Time Qed.

Goal pigeon_hole 6 5 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  vitauto.
Time Qed.

Goal pigeon_hole 7 6 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  vitauto.
Time Qed.

Goal pigeon_hole 8 7 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  vitauto.
Time Qed.

Goal pigeon_hole 9 8 -> False.
Proof.
  unfold pigeon_hole. cbn.
Time  vitauto.
Time Qed.
