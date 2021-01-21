Require Import Cdcl.Itauto.

Goal forall (P P0 P1 P2 P3 P4 P5 : Prop),
    P5 ->
    (P4 -> False) ->
    P3 ->
    (P2 -> P3 -> P5 -> P1) ->
    (P1 -> P0) ->
    (P3 -> P) -> (P0 -> P1) -> (P0 -> (P2 \/ P /\ P1)) /\ ((P2 \/ P /\ P1) -> P0).
Proof.
  intros.
  itauto idtac.
Qed.
