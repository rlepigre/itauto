(* Copyright 2023 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Bool ZifyBool ZArith ZifyUint63 Uint63 Lia List.
Require Import Morphisms.
Require Import Cdcl.Lib Cdcl.Syntax.

(* Here, we consider [HFormula] as tokens. *)


  Section HEQB.
    Variable eqb : LForm -> LForm -> bool.

    Definition xhformula_eqb (f1 f2: HFormula) :=
      HCons.eq_hc f1 f2 && eqb f1.(HCons.elt) f2.(HCons.elt).
  End HEQB.

  Fixpoint formula_eqb (f1 f2 : LForm) {struct f1}: bool :=
    match f1 , f2 with
    | LAT i , LAT j => Uint63.eqb i j
    | LOP o1 l1, LOP o2 l2 => lop_eqb o1 o2 && forall2b (xhformula_eqb formula_eqb) l1 l2
    | LIMPL l1 r1, LIMPL l2 r2 => forall2b (xhformula_eqb formula_eqb) l1 l2 && xhformula_eqb formula_eqb r1 r2
    | _ , _ => false
    end.

  Definition hformula_eqb (x y: HFormula) := xhformula_eqb formula_eqb x y.

  Fixpoint formula_eqb_true (f1 f2: LForm) : formula_eqb f1 f2 = true -> f1 = f2.
  Proof.
    assert (REC : forall f1 f2, xhformula_eqb formula_eqb f1 f2 = true -> f1 = f2).
    {
      unfold xhformula_eqb.
      intros.
      destruct f0,f3 ; simpl in *.
      unfold HCons.eq_hc in H.
      simpl in *. rewrite! andb_true_iff in H.
      destruct H. destruct H.
      f_equal;auto. lia. rewrite eqb_true_iff in H1; auto.
    }
    assert (ALL : forall l1 l2,
               forall2b (xhformula_eqb formula_eqb) l1 l2 = true ->
               l1 = l2).
    {
      intros.
      apply forall2b_Forall2 in H.
      revert l2 H.
      induction l1.
      - intros. inv H. reflexivity.
      - intros.
        inv H. apply IHl1 in H4.
        apply REC in H2.
        congruence.
    }
    destruct f1 ; simpl; destruct f2; simpl; try congruence.
    - intros. f_equal. lia.
    - intros.
      rewrite andb_true_iff in *.
      destruct H.
      apply lop_eqb_true in H.
      f_equal. auto. apply ALL; auto.
    - intros.
      rewrite andb_true_iff in *.
      destruct H.
      f_equal ;auto.
  Qed.

  Fixpoint formula_eqb_refl (f1: LForm) : formula_eqb f1 f1 = true.
  Proof.
    assert (REC : forall f1, xhformula_eqb formula_eqb f1 f1 = true).
    {
      unfold xhformula_eqb.
      intros.
      destruct f0 ; simpl in *.
      unfold HCons.eq_hc.
      simpl. rewrite! andb_true_iff.
      split_and. lia.
      apply eqb_reflx.
      apply formula_eqb_refl.
    }
    assert (ALL : forall l1,
               forall2b (xhformula_eqb formula_eqb) l1 l1 = true).
    {
      intros.
      induction l1.
      - reflexivity.
      -  simpl.
         rewrite REC. rewrite IHl1.
         reflexivity.
    }
    destruct f1 ; simpl; try congruence.
    - lia.
    - rewrite andb_true_iff.
      split_and.
      apply lop_eqb_refl.
      apply ALL;auto.
    - intros.
      rewrite andb_true_iff in *.
      split;
      auto.
  Qed.



  Definition hformula_eqb_true (f1 f2: HFormula) : hformula_eqb f1 f2 = true -> f1 = f2.
  Proof.
    unfold hformula_eqb.
    {
      unfold xhformula_eqb.
      intros.
      destruct f1,f2 ; simpl in *.
      unfold HCons.eq_hc in H.
      simpl in *. rewrite! andb_true_iff in H.
      destruct H. destruct H.
      f_equal;auto. lia. rewrite eqb_true_iff in H1; auto.
      apply formula_eqb_true; auto.
    }
  Qed.


  Lemma hformula_eqb_refl (f1: HFormula) : hformula_eqb f1 f1 = true.
  Proof.
    unfold hformula_eqb.
    destruct f1 ; simpl in *.
    unfold xhformula_eqb.
    unfold HCons.eq_hc. simpl.
    rewrite! andb_true_iff.
    split_and. lia.
    apply eqb_reflx.
    apply formula_eqb_refl.
  Qed.

  Lemma hformula_eq_dec (f1 f2: HFormula) : {f1 = f2} + {f1 <> f2}.
  Proof.
    destruct (hformula_eqb f1 f2) eqn:HF.
    apply hformula_eqb_true in HF.
    left ; auto.
    right. intro. subst. rewrite hformula_eqb_refl in HF.  discriminate.
  Qed.

Definition t := literal.

Definition pol (x:t) :=
  match x with
  | POS _ => true
  | NEG _ => false
  end.

Definition isPOS (x:t) :=
  pol x = true.


Definition var (x:t) :=
  match x with
  | POS p => p
  | NEG p => p
  end.

Definition neg (x:t) :=
  match x with
  | POS x => NEG x
  | NEG x => POS x
  end.


Definition beval_lit (env : HFormula -> bool) (l:t) :=
  if pol l then env (var l) else
    negb (env (var l)).

Definition eval_lit (env: HFormula -> Prop) (l:t) (X:Prop)  :=
  if pol l then env (var l) \/ X
  else env (var l) -> X.

Lemma beval_lit_neg : forall env l,
    beval_lit env l = negb (beval_lit env (neg l)).
Proof.
  unfold beval_lit.
  destruct l; simpl; auto.
  rewrite negb_involutive. reflexivity.
Qed.


Add Parametric Morphism (env:HFormula -> Prop) (l:t) : (eval_lit env l) with signature iff ==> iff as eval_lit_morph.
Proof.
  unfold eval_lit.
  intros.
  destruct (pol l). tauto.
  tauto.
Qed.

Definition get_pol (p:HFormula) (l : Lit.t) : option bool :=
  if hformula_eqb p (var l) then Some (pol l) else None.


Definition eq_dec (l1 l2:t) : {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
  apply hformula_eq_dec.
  apply hformula_eq_dec.
Qed.


Definition make (b:bool) (v:HFormula) :=
  if b then POS v else NEG v.

Lemma var_make : forall b v, var (make b v) = v.
Proof.
  unfold make. destruct b;reflexivity.
Qed.

Lemma decomp : forall l,
    l = (if pol l then POS (var l) else NEG (var l)).
Proof.
  destruct l; reflexivity.
Qed.

Lemma get_pol_inv : forall p l b,
    get_pol p l = Some b -> l = make b p.
Proof.
  unfold get_pol.
  intros.
  destruct (hformula_eqb p (var l)) eqn:E.
  inv H.
  apply hformula_eqb_true in E.
  subst.
  apply decomp.
  discriminate.
Qed.

Lemma get_pol_None : forall p l,
    get_pol p l = None -> var l <> p.
Proof.
  unfold get_pol.
  intros.
  destruct (hformula_eqb p (var l)) eqn:E.
  discriminate.
  intro. subst.
  rewrite hformula_eqb_refl in E. discriminate.
Qed.

Lemma eval_lit_negb_make : forall env b p,
    beval_lit env (make b p) = negb (beval_lit env (make (negb b) p)).
Proof.
  unfold beval_lit. unfold make.
  destruct b; simpl;auto.
  intros. rewrite negb_involutive. reflexivity.
Qed.

Lemma make_var : forall b a,
    make b (var a) <> a -> make (negb b) (var a) = a.
Proof.
  unfold make.
  destruct b,a; simpl; congruence.
Qed.


