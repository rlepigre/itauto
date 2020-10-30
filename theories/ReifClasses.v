(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Bool.

Class DecP1 {A : Type} (P : A -> Prop) :=
  decP1 : forall x, P x \/ ~ P x.

Class DecP2 {A B: Type} (P : A -> B -> Prop) :=
  decP2 : forall x y, P x y \/ ~ P x y.

Module Reflect.

  Class Rbool1 {A:Type} (P : A -> bool) :=
    mkrbool1 {
        p1 : A -> Prop;
        p1_prf : forall x, p1 x <-> Is_true (P x)
      }.

  Class Rbool2 {A B: Type} (P : A -> B -> bool) :=
    mkrbool2 {
        p2 : A -> B -> Prop;
        p2_prf : forall x y, p2 x y <-> Is_true (P x y)
      }.

  (* Reverse mapping *)

  Class RProp1 {A:Type} (P : A -> Prop) :=
    mkrProp1 {
       b1 : A -> bool;
       b1_prf : forall x, P x <-> Is_true (b1 x)
      }.

  Class RProp2 {A B: Type} (P : A -> B -> Prop) :=
    mkrProp2 {
        b2 : A -> B -> bool;
        b2_prf : forall x y, P x y <-> Is_true (b2 x y)
      }.

End Reflect.

Module TheoryPropagation.
 (* The following type-classes allow to generate clauses based on the
    shape of a literal.  They are used by the prover to perform some
    theory propagation.
  *)


  (** [NegBinRel R] is used for literals of the form [~ R x y].
      When it is matched, the solver generates the clause [mk_clause x y].
      For this to work, [mk_clause x y] needs to be a clause i.e.
      a proposition of the form x1 -> ... -> xn -> y1 \/ ... \/  yn.
      see ZArithDec for a way to eliminate (~ @eq Z x y)
 *)

  Class NegBinRel {A B: Type} (R : A -> B -> Prop) :=
    mkNegBinProp
      {
        neg_bin_rel_clause : forall (x:A) (y:B), Prop;
        neg_bin_rel_correct : forall x y, neg_bin_rel_clause x y
      }.

End TheoryPropagation.
