Require Import Lia ZArith.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Unset Lia Cache.
Set Itauto Theory Time.

Ltac timing_lia := idtac "starting a lia call..."; time "lia" lia.

Goal forall instrMemSizeLg memSizeLg stack_size_in_bytes
            instrMemSizeBytes : Z,
 3 <= instrMemSizeLg <= 30 ->
 2 + instrMemSizeLg < memSizeLg <= 16 ->
 forall BPW : Z,
 stack_size_in_bytes mod BPW = 0 ->
 0 <= stack_size_in_bytes <= 2 ^ memSizeLg - instrMemSizeBytes ->
 forall (L2 : nat) (width : Z) (wordrep : Type)
   (w2z : wordrep -> Z) (z2w : Z -> wordrep),
 w2z (z2w 0) + Z.of_nat L2 <= w2z (z2w instrMemSizeBytes) ->
 0 <= Z.of_nat L2 ->
 Z.of_nat L2 <= instrMemSizeBytes ->
 instrMemSizeBytes <= 2 ^ memSizeLg - stack_size_in_bytes ->
 2 ^ memSizeLg - stack_size_in_bytes <= 2 ^ memSizeLg ->
 2 ^ memSizeLg < 2 ^ width ->
 instrMemSizeBytes = 2 ^ (2 + instrMemSizeLg) ->
 forall (z9 : Z) (L1 : nat),
 Z.of_nat L1 = z9 ->
 0 <= Z.of_nat L1 ->
 forall z2 : Z,
 0 < instrMemSizeBytes /\ z2 = instrMemSizeBytes \/
 instrMemSizeBytes <= 0 /\ z2 = 0 ->
 forall z3 : Z,
 0 < z2 - Z.of_nat L2 /\ z3 = z2 - Z.of_nat L2 \/
 z2 - Z.of_nat L2 <= 0 /\ z3 = 0 ->
 forall z4 : Z,
 0 < Z.of_nat L1 - Z.of_nat L2 /\ z4 = Z.of_nat L1 - Z.of_nat L2 \/
 Z.of_nat L1 - Z.of_nat L2 <= 0 /\ z4 = 0 ->
 forall z5 : Z,
 0 < z4 - z3 /\ z5 = z4 - z3 \/ z4 - z3 <= 0 /\ z5 = 0 ->
 forall z6 : Z,
 0 < 2 ^ memSizeLg - instrMemSizeBytes - stack_size_in_bytes /\
 z6 = 2 ^ memSizeLg - instrMemSizeBytes - stack_size_in_bytes \/
 2 ^ memSizeLg - instrMemSizeBytes - stack_size_in_bytes <= 0 /\
 z6 = 0 ->
 forall z7 : Z,
 z6 < z5 /\ z7 = z6 \/ z5 <= z6 /\ z7 = z5 ->
 forall z8 : Z,
 z3 < z4 /\ z8 = z3 \/ z4 <= z3 /\ z8 = z4 ->
 0 < 2 ^ memSizeLg /\ z9 = 2 ^ memSizeLg \/
 2 ^ memSizeLg <= 0 /\ z9 = 0 ->
 Z.of_nat L2 + z8 + z7 = 2 ^ memSizeLg - stack_size_in_bytes.
Proof.
  intros.
  (* Time lia. (* 0.565 secs *) *)
  Time itauto lia. (* From 155s to 3s *)
Qed.
