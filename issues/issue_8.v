Require Import Lia ZArith.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Definition Register := Z.

Goal forall (x: Register) (n : x <> 0),
    Z.eq_dec x 0 = right n ->
    (0 <? x) = false \/ (x <? 32) = false ->
    0 < x < 32 \/ x = 0 ->
    False.
Proof.
  intros.
  unfold Register in n, H.
  itauto lia.
Qed.
