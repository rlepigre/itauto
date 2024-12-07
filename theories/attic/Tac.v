Ltac mp :=  repeat match goal with
         | H :?A , H1 : ?A -> ?B |- _ => specialize (H1 H)
         end.

Ltac sub :=  repeat match goal with
                    | H :?A -> False , H1 : ?A -> ?B |- _ => clear H1
                    end.
