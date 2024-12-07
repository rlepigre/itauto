(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)

Require Import Cdcl.Base.Formula.
Require Export Cdcl.Base.ReifClasses Cdcl.ZArithDec.
From Coq Require Import Lia.

Require Import List.
Require Import Uint63.

Declare ML Module "coq-itauto.plugin".
Require Import Cdcl.Base.Formula.
Require Import Bool.

Lemma Is_true_iff_eq_true : forall b, Is_true b <-> b = true.
Proof.
  split ; intro.
  - apply Is_true_eq_true; assumption.
  - apply Is_true_eq_left; assumption.
Qed.

Lemma xorb_def : forall x y,
    xorb x y = (x || y) && negb (Bool.eqb x y).
Proof.
  destruct x,y; reflexivity.
Qed.

Ltac rewrite_Is_true :=
  match goal with
  | H : context[Is_true ?X] |- _ => rewrite (Is_true_iff_eq_true X) in H
  | |- context[Is_true ?X]   => rewrite (Is_true_iff_eq_true X)
  end.

Ltac gen_conflicts tac :=
  intros; unfold not in *;
  repeat rewrite xorb_def in *;
  repeat rewrite_Is_true;
  unfold is_true;
  (* Apply ~ ~ p -> p if Classical is loaded *)
  cdcl_nnpp; unfold not;
  (* Generate conflict clauses *)
  (cdcl_conflicts tac).

Ltac vitautog :=
  (* Reify the conclusion *)
  cdcl_change;
  let ua := fresh "ua" in
  let n := fresh "n" in
  let mb := fresh "mb" in
  let md := fresh "md" in
  let m := fresh "m" in
  let f := fresh "f" in
  (intros ua n mb md m f;
  (* Apply soundness proof and compute *)
   apply (hcons_tauto_prover_correct m md mb ua (KeyInt.nat_of_int n));
   [reflexivity | reflexivity | vm_compute; reflexivity]).



(** [nitautog] same as [vitauto] but uses native_compute *)
Ltac nitautog :=
(* Reify the conclusion *)
  cdcl_change;
  let ua := fresh "ua" in
  let n := fresh "n" in
  let mb := fresh "mb" in
  let md := fresh "md" in
  let m := fresh "m" in
  let f := fresh "f" in
  (intros ua n mb md m f;
  (* Apply soundness proof and compute *)
   apply (hcons_tauto_prover_correct m md mb ua (KeyInt.nat_of_int n));
   [reflexivity | reflexivity | native_compute; reflexivity]).

Ltac citautog :=
(* Reify the conclusion *)
  cdcl_change;
  let ua := fresh "ua" in
  let n := fresh "n" in
  let mb := fresh "mb" in
  let md := fresh "md" in
  let m := fresh "m" in
  let f := fresh "f" in
  (intros n mb md m f;
  (* Apply soundness proof and compute *)
   apply (hcons_tauto_prover_correct m md mb ua (KeyInt.nat_of_int n));
   [reflexivity | reflexivity | compute; reflexivity]).

(** [vitauto] is a standalone version reifying all the hypotheses *)
Ltac vitauto :=
  cdcl_generalize ;
  vitautog.

Tactic Notation "itauto" tactic(tac) :=
  gen_conflicts tac ;
  vitautog.

Tactic Notation "itauto" :=
  itauto auto.


Ltac itautor tac := let t := solve[tac | itauto tac] in itauto t.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_post_hook ::= idtac. (* ZifyBool sets some nasty Ltac *)

(* Nelson Oppen Support *)
Class TheorySig (Tid:Type) {T:Type} (Op: T) : Prop.

Class TheoryType (Tid:Type) (T:Type) : Prop.

Register TheorySig as No.TheorySig.
Register TheoryType as No.TheoryType.

(* Convenient for benchmarking against existing tactics *)
Module Redef.

  (* old tauto and intuition *)
  Ltac otauto := tauto.
  Tactic Notation "ointuition" tactic(t) := intuition t.

  (* Emulate intuition and tauto *)
  Ltac nneg :=
    match goal with
    | H1 : (?T1 -> False) |- False => apply H1 ; assumption
    end.

  Ltac tauto_solve :=
    solve[reflexivity| assumption | nneg].

  Ltac tautor :=
    let t := solve [tauto_solve|itauto tauto_solve] in
    itauto t.

  Ltac tauto := itauto tauto_solve.

  Tactic Notation "intuition" tactic(t) :=
    itauto t.

  Ltac intuitionr t :=
    let tac := solve[t |itauto t] in
    itauto tac.


End Redef.

Module Bench.

  Lemma double : forall (P:Prop), P -> P -> P.
  Proof.
    auto.
  Qed.

  Ltac apply_double :=
    match goal with
    | |- ?G => apply (double G)
    end.

  Ltac tac_or_tac t1 t2 :=
    solve [apply_double ; [solve [ time "T1" t1] | solve [time "T2" t2]]].

End Bench.

