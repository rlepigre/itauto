Require Import Cdcl.Itauto.
Require Import ZArith Lia List.
Require Import Cdcl.Itauto.
Open Scope Z_scope.


Goal forall (W : Type) (left right : W) (xs : list W) (w2z : W -> Z)
            (v : nat) (x : list W) (x1 x2 : W) (q1 z5 q q0 z6 r r0 r1 : Z),
    (w2z right - w2z left) mod 2 ^ 64 = 8 * Z.of_nat (length xs) ->
    (w2z x2 - w2z x1) mod 2 ^ 64 = 8 * Z.of_nat (length x) ->
    (w2z x2 - w2z x1) mod 2 ^ 64 <> 0 ->
    Z.of_nat (length x) = Z.of_nat v ->
    0 <= Z.of_nat (length xs) ->
    0 <= Z.of_nat (length x) ->
    0 <= Z.of_nat v ->
    0 < q0 /\ z5 = q0 \/ q0 <= 0 /\ z5 = 0 ->
    z5 < Z.of_nat (length x) /\ z6 = z5 \/
    Z.of_nat (length x) <= z5 /\ z6 = Z.of_nat (length x) ->
    (2 ^ 4 <> 0 -> (w2z x2 - w2z x1) mod 2 ^ 64 = 2 ^ 4 * q + r) ->
    (0 < 2 ^ 4 -> 0 <= r < 2 ^ 4) ->
    (2 ^ 4 < 0 -> 2 ^ 4 < r <= 0) ->
    (8 <> 0 -> (w2z x1 + q * 2 ^ 3 - w2z x1) mod 2 ^ 64 = 8 * q0 + r0) ->
    (0 < 8 -> 0 <= r0 < 8) ->
    (8 < 0 -> 8 < r0 <= 0) ->
    (8 mod 2 ^ 64 <> 0 ->
     ((w2z x1 +
       Z.shiftl
         (Z.shiftr ((w2z x2 - w2z x1) mod 2 ^ 64) (4 mod 2 ^ 64) mod 2 ^ 64)
         (3 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64 - w2z x1) mod 2 ^ 64 = 8 mod 2 ^ 64 * q1 + r1) ->
    (0 < 8 mod 2 ^ 64 -> 0 <= r1 < 8 mod 2 ^ 64) ->
    (8 mod 2 ^ 64 < 0 -> 8 mod 2 ^ 64 < r1 <= 0) ->
    (w2z x1 + q * 2 ^ 3 - w2z x1) mod 2 ^ 64 = 8 * z6.
Proof.
  intros.
  Fail Time itauto lia. (* Fast... *)
Abort.
