(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)

(** Teach itauto that comparisons over Z are decidable *)
Require Import Cdcl.ReifClasses.
Require Import Bool ZArith Lia.
Open Scope Z_scope.

Lemma dec_le : forall x y, x <= y \/ ~ x <= y.
Proof.
  lia.
Qed.

Lemma dec_lt : forall x y, x < y \/ ~ x < y.
Proof.
  lia.
Qed.

Lemma dec_ge : forall x y, x >= y \/ ~ x >= y.
Proof.
  lia.
Qed.

Lemma dec_gt : forall x y, x > y \/ ~ x > y.
Proof.
  lia.
Qed.

Lemma dec_eq : forall (x y:Z), x = y \/ ~ x = y.
Proof.
  lia.
Qed.

Lemma decb_le : forall (x y:Z), x <= y <-> Is_true (Z.leb x y).
Proof.
  intros. unfold Is_true.
  destruct (x <=? y) eqn:EQ. lia. lia.
Qed.

Lemma decb_ge : forall (x y:Z), x >= y <-> Is_true (Z.geb x y).
Proof.
  intros. unfold Is_true.
  destruct (x >=? y) eqn:EQ. lia. lia.
Qed.



#[export] Instance DecLe : DecP2 Z.le := dec_le.
#[export] Instance DecLt : DecP2 Z.lt := dec_lt.
#[export] Instance DecGt : DecP2 Z.gt := dec_gt.
#[export] Instance DecGe : DecP2 Z.ge := dec_ge.
#[export] Instance DecEq : DecP2 (@eq Z) := dec_eq.

(** To eliminate literals of the form ~ x = y,
    we generate the clause x < y \/ x = y \/ y < x.
 *)

#[export] Instance negeqZ : TheoryPropagation.NegBinRel (@eq Z) :=
  {
  neg_bin_rel_clause := fun x y => x < y \/ x = y \/ y < x;
  neg_bin_rel_correct := Z.lt_trichotomy
  }.

(** TODO
Instance DecRLeb : Reflect.RProp2 Z.le := Reflect.mkrProp2 _ _ Z.le Z.leb decb_le.
Instance DecLeb : Reflect.Rbool2 Z.leb := Reflect.mkrbool2 _ _ Z.leb Z.le  decb_le.
Instance DecRGeb : Reflect.RProp2 Z.ge := Reflect.mkrProp2 _ _ Z.ge Z.geb decb_ge.
Instance DecGeb : Reflect.Rbool2 Z.geb := Reflect.mkrbool2 _ _ Z.geb Z.ge  decb_ge.
*)
