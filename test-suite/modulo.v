Require Import Coq.micromega.Zify.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
From Cdcl Require Import Lia.

#[local] Open Scope Z_scope.

Lemma mod_lt (a b : Z) : True -> 0 < b -> 0 <= a mod b < b.
Proof. now simpl; intros ??; apply Z.mod_pos_bound. Qed.

#[global] Instance sat_mod_lt : ZifyClasses.Saturate BinIntDef.Z.modulo :=
  {|
    ZifyClasses.PArg1 := fun a => True;
    ZifyClasses.PArg2 := fun b => 0 < b;
    ZifyClasses.PRes := fun a b ab => 0 <= ab < b;
    ZifyClasses.SatOk := mod_lt
  |}.
Add Zify Saturate sat_mod_lt.

Lemma mod_le (a b : Z) : 0 <= a -> 0 < b -> a mod b <= a.
Proof.
  now simpl; intros Ha Hb; apply Zmod_le.
Qed.

#[global] Instance sat_mod_le : ZifyClasses.Saturate BinIntDef.Z.modulo :=
  {|
    ZifyClasses.PArg1 := fun a => 0 <= a;
    ZifyClasses.PArg2 := fun b => 0 < b;
    ZifyClasses.PRes := fun a b ab => ab <= a;
    ZifyClasses.SatOk := mod_le
  |}.
Add Zify Saturate sat_mod_le.

Module ZifyUint63.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End ZifyUint63.

Goal forall a b m : Z, 0 <= a - b < m -> a mod m = b mod m -> (a mod m - b mod m) mod m <> 0 -> a = b.
Proof.
  lia.
Qed.
