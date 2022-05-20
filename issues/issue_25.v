Require Import Cdcl.Itauto.
Require Import List.

Goal forall A a a0 (r l l' : list A), (In a l' <-> In a l /\ ~ In a r) ->
~ (~ In a0 r) ->
In a l' <-> (a = a0 \/ In a l) /\ ~ In a r.
Proof.
Fail itauto auto.
(* Slow: Time itauto congruence. *)
  Time itauto congruence.
Time Qed.
