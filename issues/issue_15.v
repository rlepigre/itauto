Require Import Lia ZArith List.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Unset Lia Cache.

Set Itauto Theory Time.

Ltac timing_lia := time "lia" lia.

Goal forall (word : Type) (w2z : word -> Z) (argnames retnames : list Z) (rem_framewords : Z)
    (program_base : word) (pos pos0 : Z)
    (unused_scratch old_argvals old_retvals old_ras ToSplit old_modvarvals : list word)
    (z55 z54 z53 z52 z50 z51 z49 sw : Z) (mv : list Z) (bpw : Z),
  pos0 mod 4 = 0 ->
  pos mod 4 = 0 ->
  w2z program_base mod 4 = 0 ->
  0 <= rem_framewords ->
  bpw = 4 \/ bpw = 8 ->
  0 <= sw ->
  Z.of_nat (length old_modvarvals) = Z.of_nat (length mv) ->
  Z.of_nat (length ToSplit) = z55 ->
  Z.of_nat (length old_ras) = 1 ->
  Z.of_nat (length (ToSplit ++ old_modvarvals)) = z54 ->
  Z.of_nat (length old_retvals) = Z.of_nat (length retnames) ->
  Z.of_nat (length ((ToSplit ++ old_modvarvals) ++ old_ras)) = z53 ->
  Z.of_nat (length old_argvals) = Z.of_nat (length argnames) ->
  Z.of_nat (length (((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals)) = z52 ->
  Z.of_nat (length unused_scratch) = z50 ->
  Z.of_nat (length ((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals)) =
  z51 ->
  rem_framewords +
  (sw + (Z.of_nat (length argnames) + Z.of_nat (length retnames) + 1 + Z.of_nat (length mv))) <=
  Z.of_nat
    (length
       (((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals) ++
        unused_scratch)) ->
  0 <= Z.of_nat (length argnames) ->
  0 <= Z.of_nat (length old_argvals) ->
  0 <= Z.of_nat (length old_retvals) ->
  0 <=
  Z.of_nat
    (length
       (((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals) ++
        unused_scratch)) ->
  0 <= Z.of_nat (length mv) ->
  0 <= Z.of_nat (length ((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals)) ->
  0 <= Z.of_nat (length ((ToSplit ++ old_modvarvals) ++ old_ras)) ->
  0 <= Z.of_nat (length (ToSplit ++ old_modvarvals)) ->
  0 <= Z.of_nat (length ToSplit) ->
  0 <= Z.of_nat (length unused_scratch) ->
  0 <= Z.of_nat (length retnames) ->
  0 <= Z.of_nat (length old_ras) ->
  0 <= Z.of_nat (length old_modvarvals) ->
  0 <= Z.of_nat (length (((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals)) ->
  0 < sw /\ z49 = sw \/ sw <= 0 /\ z49 = 0 ->
  0 < rem_framewords /\ z50 = rem_framewords \/ rem_framewords <= 0 /\ z50 = 0 ->
  0 <
  Z.of_nat
    (length
       (((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals) ++
        unused_scratch)) - z50 /\
  z51 =
  Z.of_nat
    (length
       (((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals) ++
        unused_scratch)) - z50 \/
  Z.of_nat
    (length
       (((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals) ++
        unused_scratch)) - z50 <= 0 /\ z51 = 0 ->
  0 <
  Z.of_nat (length ((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals)) -
  Z.of_nat (length argnames) /\
  z52 =
  Z.of_nat (length ((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals)) -
  Z.of_nat (length argnames) \/
  Z.of_nat (length ((((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals) ++ old_argvals)) -
  Z.of_nat (length argnames) <= 0 /\ z52 = 0 ->
  0 <
  Z.of_nat (length (((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals)) -
  Z.of_nat (length retnames) /\
  z53 =
  Z.of_nat (length (((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals)) -
  Z.of_nat (length retnames) \/
  Z.of_nat (length (((ToSplit ++ old_modvarvals) ++ old_ras) ++ old_retvals)) -
  Z.of_nat (length retnames) <= 0 /\ z53 = 0 ->
  0 < Z.of_nat (length ((ToSplit ++ old_modvarvals) ++ old_ras)) - 1 /\
  z54 = Z.of_nat (length ((ToSplit ++ old_modvarvals) ++ old_ras)) - 1 \/
  Z.of_nat (length ((ToSplit ++ old_modvarvals) ++ old_ras)) - 1 <= 0 /\ z54 = 0 ->
  0 < Z.of_nat (length (ToSplit ++ old_modvarvals)) - Z.of_nat (length mv) /\
  z55 = Z.of_nat (length (ToSplit ++ old_modvarvals)) - Z.of_nat (length mv) \/
  Z.of_nat (length (ToSplit ++ old_modvarvals)) - Z.of_nat (length mv) <= 0 /\ z55 = 0 ->
  z49 <= Z.of_nat (length ToSplit).
Proof.
  intros.
  (*timing_lia. (* 1.603 secs, and about the same in the full bedrock2 context *) *)
  Time itauto timing_lia. (* Same timing for itauto *)
 (* 3.647 secs/Theory running time 0.417,
    and 7.21 secs/Theory running time 1.004 in the full bedrock2 context *)
Qed.
