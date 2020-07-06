Require Import ZArith Lia Int63.
Require Import ZifyClasses.

Ltac inv H := inversion H ; clear H ; try subst.
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Lemma to_Z_bounded : forall x, (0 <= to_Z x < 9223372036854775808%Z)%Z.
Proof.
  apply to_Z_bounded.
Qed.

Instance InjInt : InjTyp int Z :=
  {| inj := to_Z ; pred := fun x => (0 <= x < 9223372036854775808%Z)%Z;
     cstr := to_Z_bounded |}.
Add InjTyp InjInt.

Program Instance InjEq : BinRel (@eq int) :=
  {| TR := @eq Z |}.
Next Obligation.
  split ; intro.
  - congruence.
  - apply to_Z_inj; auto.
Defined.
Add BinRel InjEq.

Definition lt : int -> int -> Prop := fun x y => compare x y = Lt.

Program Instance InjLt : BinRel lt :=
  {| TR := Z.lt |}.
Next Obligation.
  unfold lt.
  rewrite compare_spec.
  unfold Z.lt. tauto.
Defined.
Add BinRel InjLt.

Program Instance InjAdd : BinOp add :=
  {| TBOp := fun x y => Zmod (Z.add x y)  9223372036854775808%Z |}.
Next Obligation.
  apply add_spec.
Defined.
Add BinOp InjAdd.


Program Instance InjSub : BinOp sub :=
  {| TBOp := fun x y => Zmod (Z.sub x y)  9223372036854775808%Z |}.
Next Obligation.
  apply sub_spec.
Defined.
Add BinOp InjSub.



Program Instance Injto_Z : UnOp to_Z :=
  {| TUOp := fun x => x |}.
Add UnOp Injto_Z.


Program Instance InjMax_int : CstOp max_int%int63 :=
  {| TCst := 9223372036854775807%Z |}.
Add CstOp InjMax_int.


Program Instance InjO : CstOp 0%int63 :=
  {| TCst := 0%Z |}.
Add CstOp InjO.

Program Instance Inj1 : CstOp 1%int63 :=
  {| TCst := 1%Z |}.
Add CstOp Inj1.
