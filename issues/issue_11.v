Require Import Lia ZArith.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Axiom width: Z.

Goal forall (W : Type) (left right : W) (Lxs : nat) (w2z : W -> Z)
    (v : nat) (x1 x2 : W),
  forall (Lx : nat) (q1 z5 q q0 z6 r r0 r1 : Z),
  (w2z right - w2z left) mod 2 ^ width = 8 * Z.of_nat Lxs ->
  (w2z x2 - w2z x1) mod 2 ^ width = 8 * Z.of_nat Lx ->
  (w2z x2 - w2z x1) mod 2 ^ width <> 0 ->
  0 <= 8 * Z.of_nat Lx < 2 ^ width ->
  Z.of_nat Lx = Z.of_nat v ->
  0 <= Z.of_nat Lxs ->
  0 <= Z.of_nat Lx ->
  0 <= Z.of_nat v ->
  0 < q0 /\ z5 = q0 \/ q0 <= 0 /\ z5 = 0 ->
  0 < Z.of_nat Lx - (z5 + 1) /\ z6 = Z.of_nat Lx - (z5 + 1) \/
  Z.of_nat Lx - (z5 + 1) <= 0 /\ z6 = 0 ->
  (2 ^ 4 <> 0 -> (w2z x2 - w2z x1) mod 2 ^ width = 2 ^ 4 * q + r) ->
  (0 < 2 ^ 4 -> 0 <= r < 2 ^ 4) ->
  (2 ^ 4 < 0 -> 2 ^ 4 < r <= 0) ->
  (8 <> 0 -> w2z x1 + q * 2 ^ 3 - w2z x1 = 8 * q0 + r0) ->
  (0 < 8 -> 0 <= r0 < 8) ->
  (8 < 0 -> 8 < r0 <= 0) ->
  (8 mod 2 ^ width <> 0 ->
   ((w2z x1 +
     Z.shiftl
       (Z.shiftr ((w2z x2 - w2z x1) mod 2 ^ width) (4 mod 2 ^ width)
        mod 2 ^ width) (3 mod 2 ^ width) mod 2 ^ width) mod
    2 ^ width - w2z x1) mod 2 ^ width = 8 mod 2 ^ width * q1 + r1) ->
  (0 < 8 mod 2 ^ width -> 0 <= r1 < 8 mod 2 ^ width) ->
  (8 mod 2 ^ width < 0 -> 8 mod 2 ^ width < r1 <= 0) ->
  -8 * q + 8 * Z.of_nat Lx - 8 = 8 * z6.
Proof.
  intros.
  (* lia. succeeds *)
  Time itauto lia. (* still slow... *)
Qed.
