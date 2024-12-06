From Cdcl Require Import Lia.
Goal forall (A B C D:Prop),
    ((A -> C) -> B) ->
    (A -> D) -> (D -> C) ->
    B.
Proof.
  Fail lia.
  Set Itauto Use Implication Clauses.
  lia.
Qed.
