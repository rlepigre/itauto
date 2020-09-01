Require Import Lia ZArith.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Unset Lia Cache.

Axiom width: Z.
Axiom word: Type.
Axiom w2z : word -> Z.
Axiom z2w : Z -> word.

(* With evar *)
Goal forall (left right : word) (xs : list word) (Lxs : nat)
    (v : nat) (x : list word) (x1 x2 x3 : word)
    (Lx : nat) (q0 q r r0 : Z),
  (w2z right - w2z left) mod 2 ^ width = 8 * Z.of_nat Lxs ->
  (w2z x2 - w2z x1) mod 2 ^ width = 8 * Z.of_nat Lx ->
  (w2z x2 - w2z x1) mod 2 ^ width <> 0 ->
  (forall default, w2z
    (if w2z (List.hd default (List.skipn (Z.to_nat q0) x)) <? w2z x3
     then z2w 1
     else z2w 0) <> 0) ->
  0 <= 8 * Z.of_nat Lx < 2 ^ width ->
  Z.of_nat Lx = Z.of_nat v ->
  0 <= Z.of_nat Lxs ->
  0 <= Z.of_nat Lx ->
  0 <= Z.of_nat v ->
  (2 ^ 4 <> 0 -> (w2z x2 - w2z x1) mod 2 ^ width = 2 ^ 4 * q + r) ->
  (0 < 2 ^ 4 -> 0 <= r < 2 ^ 4) ->
  (2 ^ 4 < 0 -> 2 ^ 4 < r <= 0) ->
  (8 mod 2 ^ width <> 0 ->
   ((w2z x1 +
     Z.shiftl
       (Z.shiftr ((w2z x2 - w2z x1) mod 2 ^ width) (4 mod 2 ^ width)
        mod 2 ^ width) (3 mod 2 ^ width) mod 2 ^ width) mod
    2 ^ width - w2z x1) mod 2 ^ width = 8 mod 2 ^ width * q0 + r0) ->
  (0 < 8 mod 2 ^ width -> 0 <= r0 < 8 mod 2 ^ width) ->
  (8 mod 2 ^ width < 0 -> 8 mod 2 ^ width < r0 <= 0) ->
  0 <= -8 * q + 8 * Z.of_nat Lx - 8 < 2 ^ width.
Proof.
  intros.
  evar (default: word).
  specialize (H2 default).
  subst default.
Time  itauto lia.
  Unshelve.
  exact x1.
Time Qed.

(* without evar *)
Goal forall (left right : word) (xs : list word) (Lxs : nat)
    (v : nat) (x : list word) (x1 x2 x3 : word)
    (Lx : nat) (q0 q r r0 : Z),
  (w2z right - w2z left) mod 2 ^ width = 8 * Z.of_nat Lxs ->
  (w2z x2 - w2z x1) mod 2 ^ width = 8 * Z.of_nat Lx ->
  (w2z x2 - w2z x1) mod 2 ^ width <> 0 ->
  (forall default, w2z
    (if w2z (List.hd default (List.skipn (Z.to_nat q0) x)) <? w2z x3
     then z2w 1
     else z2w 0) <> 0) ->
  0 <= 8 * Z.of_nat Lx < 2 ^ width ->
  Z.of_nat Lx = Z.of_nat v ->
  0 <= Z.of_nat Lxs ->
  0 <= Z.of_nat Lx ->
  0 <= Z.of_nat v ->
  (2 ^ 4 <> 0 -> (w2z x2 - w2z x1) mod 2 ^ width = 2 ^ 4 * q + r) ->
  (0 < 2 ^ 4 -> 0 <= r < 2 ^ 4) ->
  (2 ^ 4 < 0 -> 2 ^ 4 < r <= 0) ->
  (8 mod 2 ^ width <> 0 ->
   ((w2z x1 +
     Z.shiftl
       (Z.shiftr ((w2z x2 - w2z x1) mod 2 ^ width) (4 mod 2 ^ width)
        mod 2 ^ width) (3 mod 2 ^ width) mod 2 ^ width) mod
    2 ^ width - w2z x1) mod 2 ^ width = 8 mod 2 ^ width * q0 + r0) ->
  (0 < 8 mod 2 ^ width -> 0 <= r0 < 8 mod 2 ^ width) ->
  (8 mod 2 ^ width < 0 -> 8 mod 2 ^ width < r0 <= 0) ->
  0 <= -8 * q + 8 * Z.of_nat Lx - 8 < 2 ^ width.
Proof.
  intros.
  Time  itauto lia.
Time Qed.
