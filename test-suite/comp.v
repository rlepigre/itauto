Require Import ZArith Lia ZifyClasses.
Require Import Cdcl.Itauto.

#[global]
Instance Inj_comparison : InjTyp comparison comparison :=
  mkinj _ _ (fun x => x) (fun x =>  True ) (fun _ => I).
Add Zify InjTyp Inj_comparison.

#[global]
Program Instance Op_compare : BinOp BinNat.N.compare  :=
  { TBOp := Z.compare ; TBOpInj := _ }.
Next Obligation.
  rewrite N2Z.inj_compare. reflexivity.
Defined.
Add Zify BinOp Op_compare.

#[global]
 Instance Op_eq_comp : BinRel (@eq comparison)  :=
  { TR := @eq comparison; TRInj := (fun x y => iff_refl _ ) }.
Add Zify BinRel Op_eq_comp.

Print comparison.

#[global]
Program Instance Zcompare_Spec : BinOpSpec Z.compare :=
  { BPred n m r := ((r = Lt <-> n < m) /\
                   (r = Eq <-> n = m) /\
                     (r = Gt <-> n > m))%Z ; BSpec := _ }.
Next Obligation.
  rewrite Z.compare_nge_iff.
  rewrite Z.compare_eq_iff.
  rewrite Z.compare_nle_iff.
  lia.
Defined.
Add Zify BinOpSpec Zcompare_Spec.

(*
Goal forall n1 n2 n3,
  ( n2 <  n3 ->
    n1 <  n2 ->
   ( n1 <  n3 -> False) -> False) ->
  (n1 <  n2) ->  n1 <  n3.
Proof.
  intros n1 n2 n3.
  vitautog.
*)

Ltac lia_congr := lia ||congruence.

Lemma binnat_lt_trans : forall n1 n2 n3,
    BinNat.N.compare n1 n2 = Lt ->
    BinNat.N.compare n2 n3 = Lt ->
    BinNat.N.compare n1 n3 = Lt.
Proof.
  intros n1 n2 n3.
  zify.
  itauto lia_congr.
Qed.
