Require Import Cdcl.Itauto.
Require Import List.

Goal forall (P P0 P1: Prop),
  (P1 -> P0) ->
  (P0 -> P1) ->
  ((P0 \/ P -> False) -> (P1 -> False) /\ (P -> False)) /\
  ((P1 -> False) /\ (P -> False) -> P0 \/ P -> False).
Proof.
  intros.
  itauto idtac.
Qed.

Goal forall P0 P1 (D:Prop),
    (((P0 \/ P1 -> False) -> (P1 -> False) /\ (P0 -> False)) -> D) ->
  D.
Proof.
  intros P0 P1 D.
  itauto idtac.
Qed.

Goal forall P0 P1 (D:Prop),
    (((P0 \/ P1 -> False) -> (P1 -> False) /\ (P0 -> False)) -> D) ->
  D.
Proof.
  intros P0 P1 D.
  itauto idtac.
Qed.
