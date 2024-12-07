Require Import ZArith.
Require Import Int63.
Require Import ZifyBool.
Import ZifyClasses.

Lemma to_Z_bounded : forall x, (0 <= to_Z x < 9223372036854775808)%Z.
Proof. apply to_Z_bounded. Qed.

Instance Inj_int_Z : InjTyp int Z :=
  mkinj _ _ to_Z (fun x => 0 <= x < 9223372036854775808)%Z to_Z_bounded.
Add Zify  InjTyp Inj_int_Z.

Program Instance Op_max_int : CstOp max_int :=
  { TCst := 9223372036854775807 ; TCstInj := _}.
Add Zify CstOp Op_max_int.

Program Instance Op_one : CstOp 1%int63 :=
  { TCst := 1%Z ; TCstInj := _}.
Add Zify CstOp Op_one.


Program Instance Op_ltb : BinOp ltb :=
  {| TBOp := Z.ltb; TBOpInj := _ |}.
Proof.
  Next Obligation.
    generalize (ltb_spec n m).
    rewrite <- Z.ltb_lt.
    destruct ((φ (n)%int63 <? φ (m)%int63)%Z);
    destruct (n < m)%int63; intuition.
  Qed.
Add Zify BinOp Op_ltb.

Program Instance Op_leb : BinOp leb :=
  {| TBOp := Z.leb; TBOpInj := _ |}.
Proof.
  Next Obligation.
    generalize (leb_spec n m).
    rewrite <- Z.leb_le.
    destruct ((φ (n)%int63 <=? φ (m)%int63)%Z);
    destruct (n <= m)%int63; intuition.
  Qed.
Add Zify BinOp Op_leb.


Program Instance Op_eqb : BinOp eqb :=
  {| TBOp := Z.eqb; TBOpInj := _ |}.
Proof.
  Next Obligation.
    generalize (eqb_spec n m).
    symmetry.
    destruct (n == m)%int63 ; intuition.
    rewrite Z.eqb_eq.  subst ; reflexivity.
    rewrite Z.eqb_neq. intro.
    apply to_Z_inj in H.
    intuition congruence.
  Qed.
Add Zify BinOp Op_eqb.

Program Instance Op_eq : BinRel (@eq int) :=
  {| TR := @eq Z; TRInj := _ |}.
Proof.
  Next Obligation.
    split.
    congruence.
    apply to_Z_inj.
  Qed.
Add Zify BinRel Op_eq.

Program Instance Op_add : BinOp add :=
  {| TBOp := fun x y => (x + y) mod 9223372036854775808%Z; TBOpInj := add_spec |}%Z.
Add Zify BinOp Op_add.

Program Instance Op_sub : BinOp sub :=
  {| TBOp := fun x y => (x - y) mod 9223372036854775808%Z; TBOpInj := sub_spec |}%Z.
Add Zify BinOp Op_sub.

Program Instance Op_of_Z : UnOp of_Z :=
  {| TUOp := fun x => x mod 9223372036854775808%Z; TUOpInj := of_Z_spec |}%Z.
Add Zify UnOp Op_of_Z.

Program Instance Op_to_Z : UnOp to_Z :=
  {| TUOp := fun x => x ; TUOpInj := _ |}%Z.
Add Zify UnOp Op_to_Z.
