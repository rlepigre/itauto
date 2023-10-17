(* Copyright 2023 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Bool ZifyBool ZArith ZifyUint63 Uint63 Lia List.
Require Import Cdcl.Lib Cdcl.Syntax Cdcl.Lit.

(* A clause is a list of literals.
   Section EvalList provides some results for manipulating lists *)

Section EvalList.
  Context {A: Type}.
  Variable eval : A -> Prop.

  Fixpoint eval_and_list  (l : list A) :=
    match l with
    | nil => True
    | e :: nil => eval e
    | e1 ::l   => eval e1 /\ eval_and_list l
    end.

  Fixpoint eval_and_list'  (l : list A) :=
    match l with
    | nil => True
    | e1 ::l   => eval e1 /\ eval_and_list' l
    end.

  Lemma eval_and_list_eq : forall l,
      eval_and_list l <-> eval_and_list' l.
  Proof.
    induction l ; simpl.
    - tauto.
    - destruct l.
      + simpl; tauto.
      + tauto.
  Qed.

  Fixpoint eval_or_list  (l : list A) :=
    match l with
    | nil => False
    | e :: nil => eval e
    | e1 ::l   => eval e1 \/ eval_or_list  l
    end.

  Fixpoint eval_or_list'  (l : list A) :=
    match l with
    | nil => False
    | e1 ::l   => eval e1 \/ eval_or_list'  l
    end.


  Lemma eval_or_list_eq : forall l,
      eval_or_list l <-> eval_or_list' l.
  Proof.
    induction l ; simpl.
    - tauto.
    - destruct l.
      + simpl; tauto.
      + tauto.
  Qed.

  Definition eval_op_list (o:lop) (l : list A) :=
    match o with
    | LAND => eval_and_list  l
    | LOR  => eval_or_list  l
    end.

  Fixpoint eval_impl_list (l : list A) (r: Prop) :=
    match l with
    | nil => r
    | e::l => eval e -> eval_impl_list l r
    end.

  Lemma eval_and_list_dec :
    forall l,
      Forall (fun x  => eval x \/ ~ eval x) l ->
      eval_and_list  l \/  ~ eval_and_list l.
  Proof.
    intros. induction H.
    - simpl. tauto.
    - simpl.
      destruct l. tauto.
      tauto.
  Qed.

  Lemma eval_or_list_dec :
    forall l,
      Forall (fun x  => eval x \/ ~ eval x) l ->
      eval_or_list  l \/  ~ eval_or_list l.
  Proof.
    intros. induction H.
    - simpl. tauto.
    - simpl.
      destruct l. tauto. tauto.
  Qed.

  Lemma eval_op_list_dec :
    forall o l,
      Forall (fun x  => eval x \/ ~ eval x) l ->
      eval_op_list o l \/  ~ eval_op_list o l.
  Proof.
    destruct o.
    apply eval_and_list_dec.
    apply eval_or_list_dec.
  Qed.

  Lemma eval_impl_list_dec :
    forall l r,
      Forall (fun x  => eval x \/ ~ eval x) l ->
      r \/ ~ r ->
      eval_impl_list l r \/  ~ eval_impl_list l r.
  Proof.
    intros l r H.
    induction H.
    - simpl. tauto.
    - simpl.
      intros.
      tauto.
  Qed.

  Lemma eval_and_list'_Forall : forall l, eval_and_list' l <-> Forall eval l.
  Proof.
    induction l.
    - simpl.
      rewrite Forall_rew. tauto.
    - simpl.
      rewrite Forall_rew. tauto.
  Qed.

  Lemma eval_or_list'_Exists : forall l, eval_or_list' l <-> Exists eval l.
  Proof.
    induction l.
    - simpl.
      intuition. inversion H.
    - simpl.
      rewrite IHl ; intuition.
      inv H1; tauto.
  Qed.


  Lemma eval_and_list_impl :
    forall l l',
      (forall x, In x l -> exists y, In y l' /\ (eval x <-> eval y)) ->
      eval_and_list  l' -> eval_and_list  l.
  Proof.
    intros.
    rewrite! eval_and_list_eq in *.
    revert l' H H0.
    induction l; simpl.
    - intuition.
    - intros.
      split.
      destruct (H a (or_introl eq_refl)).
      destruct H1. rewrite H2.
      clear H2.
      revert x H1.
      rewrite <- Forall_forall.
      apply eval_and_list'_Forall in H0 ; auto.
      eapply IHl ; eauto.
  Qed.

  Lemma eval_or_list_impl :
    forall l l',
      (forall x, In x l' -> exists y, In y l /\ (eval x <-> eval y)) ->
      eval_or_list  l' -> eval_or_list  l.
  Proof.
    intros.
    rewrite! eval_or_list_eq in *.
    revert l H H0.
    induction l'; simpl.
    - tauto.
    - intros.
      destruct H0.
      destruct (H a (or_introl eq_refl)).
      destruct H1.
      rewrite H2 in H0.
      rewrite eval_or_list'_Exists.
      rewrite Exists_exists.
      exists x ; tauto.
      eapply IHl' ; eauto.
  Qed.

  Lemma eval_and_list_app : forall l1 l2,
      eval_and_list' (l1 ++ l2) <->  (eval_and_list' l1 /\ eval_and_list' l2).
  Proof.
    induction l1; simpl.
    - tauto.
    - intros. rewrite IHl1. tauto.
  Qed.

  Lemma eval_or_list_app : forall l1 l2,
      eval_or_list' (l1 ++ l2) <->  (eval_or_list' l1 \/ eval_or_list' l2).
  Proof.
    induction l1; simpl.
    - tauto.
    - intros. rewrite IHl1. tauto.
  Qed.

  Lemma eval_and_list_rev_append : forall l1 l2,
      eval_and_list' (rev_append l1 l2) <-> (eval_and_list' l1 /\ eval_and_list' l2).
  Proof.
    induction l1 ; simpl.
    - tauto.
    - intros.
      rewrite IHl1. simpl.
      tauto.
  Qed.

  Lemma eval_or_list_rev_append : forall l1 l2,
      eval_or_list' (rev_append l1 l2) <-> (eval_or_list' l1 \/ eval_or_list' l2).
  Proof.
    induction l1 ; simpl.
    - tauto.
    - intros.
      rewrite IHl1. simpl.
      tauto.
  Qed.

  Definition eval_lop (o: lop) :=
    match o with
    | LAND => and
    | LOR  => or
    end.

  Lemma eval_op_list_app : forall o l1 l2,
      eval_op_list o (l1++l2) <->  eval_lop o (eval_op_list o l1) (eval_op_list o l2).
  Proof.
    destruct o; simpl;intros.
    - rewrite! eval_and_list_eq.
      rewrite eval_and_list_app.
      tauto.
    - rewrite! eval_or_list_eq.
      rewrite eval_or_list_app.
      tauto.
  Qed.

  Lemma eval_op_list_rev_append : forall o l1 l2,
      eval_op_list o (rev_append l1 l2) <->  eval_lop o (eval_op_list o l1) (eval_op_list o l2).
  Proof.
    destruct o; simpl;intros.
    - rewrite! eval_and_list_eq.
      rewrite eval_and_list_rev_append.
      tauto.
    - rewrite! eval_or_list_eq.
      rewrite eval_or_list_rev_append.
      tauto.
  Qed.

  Lemma eval_op_list_cons : forall o e l,
      eval_op_list o (e::l) <->  eval_lop o (eval e) (eval_op_list o l).
  Proof.
    destruct o; unfold eval_op_list; intros.
    - rewrite! eval_and_list_eq.
      simpl ; tauto.
    - rewrite! eval_or_list_eq.
      simpl ; tauto.
  Qed.

  Lemma eval_impl_list_eq : forall l (r:Prop),
      (eval_and_list l -> r)
      <-> eval_impl_list l r.
  Proof.
    intros.
    rewrite eval_and_list_eq.
    induction l; simpl.
    - tauto.
    - tauto.
  Qed.

  Lemma eval_impl_list_iff : forall l r l' r',
      (eval_and_list l <-> eval_and_list l') ->
      (r <->  r') ->
      eval_impl_list l r <-> eval_impl_list l' r'.
  Proof.
    intros.
    rewrite <- ! eval_impl_list_eq.
    rewrite! eval_and_list_eq in *.
    tauto.
  Qed.

  Lemma eval_and_list_rev : forall l,
      eval_and_list'  (rev l) <-> eval_and_list'  l.
  Proof.
    induction l; simpl.
    - tauto.
    - rewrite eval_and_list_app.
      simpl. tauto.
  Qed.

  Lemma eval_or_list_rev : forall l,
      eval_or_list'  (rev l) <-> eval_or_list'  l.
  Proof.
    induction l; simpl.
    - tauto.
    - rewrite eval_or_list_app.
      simpl. tauto.
  Qed.


End EvalList.

Definition clause := list Lit.t.

Definition wf (l : clause) :=
  exists l1 l2, l=(List.map NEG l1) ++ (List.map POS l2).

Fixpoint eval_clause (env : HFormula -> Prop) (cl : clause) :=
  match cl with
  | nil => False
  | e::cl' => eval_lit env e (eval_clause env cl')
  end.

Fixpoint beval_clause (env : HFormula -> bool) (cl : clause) :=
  match cl with
  | nil => false
  | e::cl' => beval_lit env e || beval_clause env cl'
  end.

Definition cnf := list clause.

Definition penv (env : HFormula -> bool) := fun x => is_true (env x).

Definition beval_cnf (env :HFormula -> bool) (l: cnf) :=
  List.fold_right (fun e acc => beval_clause env e && acc) true l.

Definition eval_cnf (env :HFormula -> Prop) (l: cnf) :=
  List.fold_right (fun e acc => eval_clause env e /\ acc) True l.


Lemma beval_clause_app : forall env l1 l2,
    beval_clause env (l1 ++ l2) = (beval_clause env l1 || beval_clause env l2).
Proof.
  induction l1; simpl.
  - reflexivity.
  - intros.
    rewrite IHl1.
    btauto.
Qed.

Lemma beval_cnf_app : forall env l1 l2,
    beval_cnf env (l1 ++ l2) = (beval_cnf env l1 && beval_cnf env l2).
Proof.
  induction l1; simpl.
  - tauto.
  - intros.
    rewrite IHl1.
    btauto.
Qed.

Lemma eval_cnf_app : forall env l1 l2,
    eval_cnf env (l1 ++ l2) <-> (eval_cnf env l1 /\ eval_cnf env l2).
Proof.
  induction l1; simpl.
  - tauto.
  - intros.
    rewrite IHl1.
    tauto.
Qed.
