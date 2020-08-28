Require Import Lia ZArith.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Axiom width: Z.

Goal forall (W : Type) (left right : W) (Lxs : nat) (w2z : W -> Z)
            (v : nat) (x1 x2 : W) (Lx : nat) (q r : Z),
    (w2z right - w2z left) mod 2 ^ width = 8 * Z.of_nat Lxs ->
    (w2z x2 - w2z x1) mod 2 ^ width = 8 * Z.of_nat Lx ->
    (w2z x2 - w2z x1) mod 2 ^ width <> 0 ->
    0 <= 8 * Z.of_nat Lx < 2 ^ width ->
    Z.of_nat Lx = Z.of_nat v ->
    0 <= Z.of_nat Lxs ->
    0 <= Z.of_nat Lx ->
    0 <= Z.of_nat v ->
    (2 ^ 4 <> 0 -> 8 * Z.of_nat Lx = 2 ^ 4 * q + r) ->
    (0 < 2 ^ 4 -> 0 <= r < 2 ^ 4) ->
    (2 ^ 4 < 0 -> 2 ^ 4 < r <= 0) ->
    8 * q < 8 * Z.of_nat Lx.
Proof.
  intros.
  (* lia. (* succeeds *) *)
  itauto lia. (* fails with 4 "Cannot find witness" errors *)
Qed.
