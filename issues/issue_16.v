Require Import Lia ZArith List.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Unset Lia Cache.
Set Itauto Theory Time.

Ltac mp :=  repeat match goal with
         | H :?A , H1 : ?A -> ?B |- _ => specialize (H1 H)
         end.

Ltac sub :=  repeat match goal with
                    | H :?A -> False , H1 : ?A -> ?B |- _ => clear H1
                    end.


Goal  forall (word : Type) (left right : word) (xs : list word)
    (r8 : Z) (v : nat) (x : list word) (x1 x2 : word)
    (r7 q r r6 q0 r0 r2 : Z) (w2z : word -> Z)
    (width q1 r1 q2 r3 q3 r4 r5 q4 q5 q6 q7 q8 : Z),
    r8 = 8 * Z.of_nat (Datatypes.length xs) ->
  r7 = 8 * Z.of_nat (Datatypes.length x) ->
  Datatypes.length x = v ->
  r7 <> 0 ->
  (2 ^ r6 <> 0 -> r7 = 2 ^ r6 * q + r) ->
  (0 < 2 ^ r6 -> 0 <= r < 2 ^ r6) ->
  (2 ^ r6 < 0 -> 2 ^ r6 < r <= 0) ->
  (2 ^ r6 = 0 -> q = 0) ->
  (2 ^ r6 = 0 -> r = 0) ->
  (2 ^ width <> 0 -> r2 - w2z x1 = 2 ^ width * q0 + r0) ->
  (0 < 2 ^ width -> 0 <= r0 < 2 ^ width) ->
  (2 ^ width < 0 -> 2 ^ width < r0 <= 0) ->
  (2 ^ width = 0 -> q0 = 0) ->
  (2 ^ width = 0 -> r0 = 0) ->
  (2 ^ width <> 0 -> 8 = 2 ^ width * q1 + r1) ->
  (0 < 2 ^ width -> 0 <= r1 < 2 ^ width) ->
  (2 ^ width < 0 -> 2 ^ width < r1 <= 0) ->
  (2 ^ width = 0 -> q1 = 0) ->
  (2 ^ width = 0 -> r1 = 0) ->
  (2 ^ width <> 0 -> w2z x1 + r3 = 2 ^ width * q2 + r2) ->
  (0 < 2 ^ width -> 0 <= r2 < 2 ^ width) ->
  (2 ^ width < 0 -> 2 ^ width < r2 <= 0) ->
  (2 ^ width = 0 -> q2 = 0) ->
  (2 ^ width = 0 -> r2 = 0) ->
  (2 ^ width <> 0 -> r4 * 2 ^ r5 = 2 ^ width * q3 + r3) ->
  (0 < 2 ^ width -> 0 <= r3 < 2 ^ width) ->
  (2 ^ width < 0 -> 2 ^ width < r3 <= 0) ->
  (2 ^ width = 0 -> q3 = 0) ->
  (2 ^ width = 0 -> r3 = 0) ->
  (2 ^ width <> 0 -> q = 2 ^ width * q4 + r4) ->
  (0 < 2 ^ width -> 0 <= r4 < 2 ^ width) ->
  (2 ^ width < 0 -> 2 ^ width < r4 <= 0) ->
  (2 ^ width = 0 -> q4 = 0) ->
  (2 ^ width = 0 -> r4 = 0) ->
  (2 ^ width <> 0 -> 3 = 2 ^ width * q5 + r5) ->
  (0 < 2 ^ width -> 0 <= r5 < 2 ^ width) ->
  (2 ^ width < 0 -> 2 ^ width < r5 <= 0) ->
  (2 ^ width = 0 -> q5 = 0) ->
  (2 ^ width = 0 -> r5 = 0) ->
  (2 ^ width <> 0 -> 4 = 2 ^ width * q6 + r6) ->
  (0 < 2 ^ width -> 0 <= r6 < 2 ^ width) ->
  (2 ^ width < 0 -> 2 ^ width < r6 <= 0) ->
  (2 ^ width = 0 -> q6 = 0) ->
  (2 ^ width = 0 -> r6 = 0) ->
  (2 ^ width <> 0 -> w2z x2 - w2z x1 = 2 ^ width * q7 + r7) ->
  (0 < 2 ^ width -> 0 <= r7 < 2 ^ width) ->
  (2 ^ width < 0 -> 2 ^ width < r7 <= 0) ->
  (2 ^ width = 0 -> q7 = 0) ->
  (2 ^ width = 0 -> r7 = 0) ->
  (2 ^ width <> 0 -> w2z right - w2z left = 2 ^ width * q8 + r8) ->
  (0 < 2 ^ width -> 0 <= r8 < 2 ^ width) ->
  (2 ^ width < 0 -> 2 ^ width < r8 <= 0) ->
  (2 ^ width = 0 -> q8 = 0) ->
  (2 ^ width = 0 -> r8 = 0) ->
  r0 < r1 * Z.of_nat (Datatypes.length x).
Proof.
  intros.
  Time Fail itauto lia.
  (* Manual decomposition *)
  assert (CASE : 2 ^ width < 0 \/ 2^width = 0 \/ 0 < 2^width) by lia.
  destruct CASE as [C1 | [C1 | C1]].
  - assert (NZ : 2 ^ width <> 0) by (clear - C1 ; lia).
    mp.
    unfold not in NZ.
    sub.
    lia.
  - mp.
    assert (0 < 2 ^ width -> False) by (clear - C1; lia).
    assert (2 ^ width <> 0 -> False) by (clear - C1; lia).
    assert (0 < 2 ^ width  -> False) by (clear - C1; lia).
    assert (2 ^ width < 0 -> False) by (clear - C1; lia).
    sub.
    lia.
  -
    assert (2 ^ width = 0 -> False) by (clear - C1; lia).
    assert (2 ^ width <> 0) by (clear - C1; lia).
    assert (2 ^ width < 0 -> False) by (clear - C1; lia).
    mp.  sub.
    Fail lia.
Abort.
