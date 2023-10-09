(* Copyright 2023 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Bool ZifyBool ZArith ZifyUint63 Uint63 Lia.

(* Some basic tactics and results *)

Ltac inv H := inversion H ; try subst ; clear H.
Ltac split_and :=
  repeat
    match goal with
    | |- ?A /\ ?B => split ; split_and
    end.

Lemma and_first : forall A B : Prop,
    A -> (A -> B) -> A /\ B.
Proof.  tauto. Qed.

Ltac split_and_first :=
  match goal with
  | |- _ /\ _ => apply and_first ; [| intro ; split_and_first]
  | |- _ => idtac
  end.

Ltac destruct_in_goal eqn :=
  match goal with
  | |- context[match ?X with
               | _ => _
               end] => destruct X eqn: eqn
  end.

Ltac destruct_in_hyp H eqn :=
  match type of H with
  | context[match ?X with
                | _ => _
            end]  => destruct X eqn: eqn
  end.

(** Comparison of uint63 *)

Lemma compare_refl : forall i, (i ?= i)%uint63 = Eq.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  replace (i <? i)%uint63 with false by lia.
  replace (i =? i)%uint63 with true by lia.
  reflexivity.
Qed.

Lemma compare_Eq : forall x y, (x ?= y)%uint63 = Eq <-> (x =? y = true)%uint63.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  destruct (x <?y)%uint63 eqn:LT; try congruence.
  intuition (congruence || lia).
  destruct (x =?y)%uint63 ;   intuition (congruence || lia).
Qed.

Lemma compare_Lt : forall x y, (x ?= y)%uint63 = Lt <-> (x <? y = true)%uint63.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  destruct (x <?y)%uint63 eqn:LT; try congruence.
  intuition (congruence || lia).
  destruct (x =?y)%uint63 ;   intuition (congruence || lia).
Qed.

Lemma compare_Gt : forall x y, (x ?= y)%uint63 = Gt <-> (y <? x = true)%uint63.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  destruct (x <?y)%uint63 eqn:LT; try congruence.
  intuition (congruence || lia).
  destruct (x =?y)%uint63 eqn:EQ;   intuition (congruence || lia).
Qed.

Ltac elim_compare :=
  match goal with
  | H : (?X ?= ?Y)%uint63 = Eq |- _ => rewrite compare_Eq in H
  | H : (?X ?= ?Y)%uint63 = Lt |- _ => rewrite compare_Lt in H
  | H : (?X ?= ?Y)%uint63 = Gt |- _ => rewrite compare_Gt in H
  | |-  (?X ?= ?Y)%uint63 = Eq  => rewrite compare_Eq
  | |-  (?X ?= ?Y)%uint63 = Lt  => rewrite compare_Lt
  | |-  (?X ?= ?Y)%uint63 = Gt  => rewrite compare_Gt
  end.

Lemma lift_if : forall (P: bool -> Prop), forall x, (x =  true -> P true) /\ (x = false -> P false)  -> P x.
Proof.
  destruct x ; tauto.
Qed.

Ltac lift_if :=
  match goal with
  | |- context[if ?x then _ else _ ] => pattern x ; apply lift_if
  end.

Ltac elim_match_comparison :=
  match goal with
  | |- context[match ?X with
       | Eq => _
       | Lt => _
       | Gt => _
       end] => let F := fresh in destruct X eqn:F
  | H: context[match ?X with
       | Eq => _
       | Lt => _
       | Gt => _
       end] |- _ => let F := fresh in destruct X eqn:F
  end.
