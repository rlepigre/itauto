Require Import Lia ZArith.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Goal forall (x : Z) (n : x <> 0),
    Z.eq_dec x 0 = right n ->
    (0 <? x) = false \/ (x <? 32) = false ->
    0 < x < 32 \/ x = 0 ->
    False.
Proof.
  intros.
  itauto lia. (* Error: Not convertible. *)
Qed.
