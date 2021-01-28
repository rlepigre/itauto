(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)

Require Import Cdcl.Formula.
Require Export Cdcl.ReifClasses Cdcl.ZArithDec.
Require Import Lia.

Require Import List.
Require Import Int63.

Declare ML Module "cdcl_plugin".
Require Import Cdcl.Formula.

Ltac gen_conflicts tac :=
  intros; unfold not in *; unfold iff in *;
  (* Apply ~ ~ p -> p if Classical is loaded *)
  cdcl_nnpp; unfold not;
  (* Generate conflict clauses *)
  (cdcl_conflicts tac).

(** [vitautog] reifies the CONCLUSION of the goal and computes using vm_compute *)
Ltac vitautog :=
  (* Reify the conclusion *)
  cdcl_change;
  let n := fresh in
  (intro n ;
  (* Apply soundness proof and compute *)
  apply (hcons_bprover_correct (KeyInt.nat_of_int n));
  vm_compute; reflexivity).

(** [nitautog] same as [vitauto] but uses native_compute *)
Ltac nitautog :=
  cdcl_change;
  let n := fresh in
  (intro n ;
  (* Apply soundness proof and compute *)
  apply (hcons_bprover_correct (KeyInt.nat_of_int n));
  native_compute; reflexivity).

(** [vitauto] is a standalone version reifying all the hypotheses *)
Ltac vitauto :=
  cdcl_generalize ;
  vitautog.

Ltac itauto_use_tauto := constr:(false).

Ltac itauto tac  :=
  gen_conflicts tac ;
  clear;
  lazymatch itauto_use_tauto with
  | true => tauto
  | false => vitautog
  end.

Ltac itautor tac := let t := solve[tac | itauto tac] in itauto t.

Ltac smt :=
  let tac := no congruence lia in
  (* zify of div mod generate propositional formulae *)
  Zify.zify ; itauto tac.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_post_hook ::= idtac. (* ZifyBool sets some nasty Ltac *)

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
