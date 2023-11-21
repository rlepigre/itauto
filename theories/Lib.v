(* Copyright 2023 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Bool ZifyBool ZArith ZifyUint63 Uint63 Lia List.

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

(** lists *)
Section FORALL2.
  Context {A B:Type}.
  Variable F : A -> B -> bool.

  Fixpoint forall2b  (l1 : list A) (l2 : list B) : bool :=
    match l1 , l2 with
    | nil , nil => true
    | e1::l1', e2::l2' => F e1 e2 && forall2b l1' l2'
    | _      , _       => false
    end.
End FORALL2.

Lemma forall2b_Forall2 : forall {A B: Type} (F : A -> B -> bool) l1 l2,
    forall2b F l1 l2 = true <-> Forall2 (fun x y => F x y = true) l1 l2.
Proof.
  induction l1 ; simpl.
  - destruct l2.
    split ; auto.
    intuition try congruence.
    inv H.
  - destruct l2.
    split ; try discriminate.
    intros. inv H.
    rewrite andb_true_iff.
    rewrite IHl1.
    intuition. inv H ; auto.
    inv H ;auto.
Qed.


Lemma Forall_rew : forall {T: Type} [P: T -> Prop] (l : list T),
    Forall P l <-> match l with
                   | nil => True
                   | e::l => P e /\ Forall P l
                   end.
Proof.
  destruct l.
  - split ; auto.
  - split ; intro.
    inv H. tauto.
    destruct H. constructor ; auto.
Qed.

(** [sublist] *)


Inductive sublist {A: Type}: list A -> list A -> Prop :=
| SUB_NIL : forall l, sublist nil l
| SUB_CONS : forall l1 l2 a, sublist l1 l2 -> sublist l1 (a::l2)
| SUB_CONS2: forall l1 l2 a, sublist l1 l2 -> sublist (a::l1) (a::l2).

Lemma sublist_refl : forall {A: Type} (l: list A),
    sublist l l.
Proof.
  induction l.
  - constructor.
  - apply SUB_CONS2. auto.
Qed.

Lemma sublist_forall : forall {A: Type} (P : A -> Prop) l1 l2,
    Forall P l2 ->
    sublist l1 l2 ->
    Forall P l1.
Proof.
  intros.
  induction H0.
  constructor.
  inv H.
  tauto.
  inv H.
  constructor; auto.
Qed.

(* A naive Ltac [btauto] *)

Ltac collect_boolean_vars E :=
  match E with
  | ?E1 || ?E2 => collect_bin E1 E2
  | ?E1 && ?E2 => let e1 := collect_boolean_vars E1 in
                  let e2 := collect_boolean_vars E2 in
                  eval simpl in (e1 ++ e2)
  |   _        => constr:(E::nil)
  end
    with collect_bin E1 E2 :=
    let e1 := collect_boolean_vars E1 in
    let e2 := collect_boolean_vars E2 in
    eval simpl in (e1 ++ e2).



Ltac simplify_bool :=
  repeat match goal with
  | |- context[?X && false] => rewrite (andb_false_r X)
  | |- context[?X && true] => rewrite (andb_true_r X)
  | |- context[?X || false] => rewrite (orb_false_r X)
  | |- context[?X || true] => rewrite (orb_true_r X)
  | |- context[negb true] =>  change (negb true) with false
  | |- context[negb false] =>  change (negb false) with true
  end.

Ltac destruct_boolean L :=
  match goal with
  | |- true = false => gfail 0 "Not a tautolofy"
  | |- false = true => gfail 0 "Not a tautolofy"
  | |- _            =>
      try reflexivity ;
      lazymatch L with
      | nil => reflexivity
      | cons ?V ?L =>
          match goal with
          | |- context[V] => destruct V ; simplify_bool ; destruct_boolean L
          | |-   _        => destruct_boolean L
          end
      end
  end.


Ltac btauto :=
  match goal with
  | |- @eq bool ?E1 ?E2 =>
      let vars := collect_bin E1 E2  in
      destruct_boolean vars
  end.

  Lemma bool_and : forall (b: bool) (P: bool -> Prop),
      (b = true -> P true) /\
      (b = false -> P false) -> P b.
  Proof.
    intros.
    destruct b;
    tauto.
  Qed.

  Ltac elim_if :=
    match goal with
    | |- context[match ?e with
                 | true => _
                 | false => _
                 end] => apply (bool_and e)
    end.
