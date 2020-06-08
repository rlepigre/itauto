Lemma double_neg : forall (A: Prop), (A \/ ~ A) -> ~~ A -> A.
Proof.
  tauto.
Qed.

Ltac double_neg :=
  apply double_neg;[tauto|].

Lemma deduce_neg_and : forall (A B: Prop), ~ (A /\ B) -> (A -> B -> False).
Proof.
  tauto.
Qed.

Ltac deduce_neg_and H :=
  match type of H with
  | ~ (?A /\ ?B) => generalize (deduce_neg_and A B H)
  end.

Lemma case_arrow : forall (A B: Prop),
    (~A \/ B -> False) -> ((A -> B) -> False).
Proof.
  tauto.
Qed.

Ltac case_arrow H :=
  match type of H with
  | ?A -> ?B => revert H ; apply (case_arrow A B); intro
  end.

Lemma deduce_neg_arrow : forall (A B: Prop), ~ (A -> B) -> ~ B.
Proof.
  tauto.
Qed.

Ltac deduce_neg_arrow H :=
  match type of H with
  | ~ (?A -> ?B) => generalize (deduce_neg_arrow A B H)
  end.

Lemma intro_cnf_and : forall (A B: Prop), A -> B -> A /\ B.
Proof.
  intros. split ; auto.
Qed.

Ltac intro_cnf :=
  match goal with
  | |- ?A /\ ?B => generalize (intro_cnf_and A B); generalize (A /\ B); do 2 intro
  end.

Lemma unfold_cnf_or : forall (A B: Prop), (A \/ B -> A \/ B).
Proof.
  tauto.
Qed.

Ltac unfold_cnf_or H :=
  match type of H with
  | ?A \/ ?B => specialize (unfold_cnf_or A B) ; revert H;
                generalize (A \/ B) at 1 2
  end.

Lemma unfold_cnf_and : forall (A B: Prop), ((A /\ B) -> A) /\ ((A /\ B) -> B).
Proof.
  tauto.
Qed.

Ltac unfold_cnf H :=
  match type of H with
  | ?A \/ ?B => specialize (unfold_cnf_or A B) ; revert H;
                generalize (A \/ B) at 1 2
  | ?A /\ ?B => specialize (unfold_cnf_and A B) ; revert H;
                generalize (A /\ B) ;
                let P1 := fresh in
                let P2 := fresh in
                let P3 := fresh in
                intros P1 P2 P3 ; destruct P3
  end.

Require Import Cdcl.Formula.


Ltac step :=
  match goal with
  | |- match  ?X with true => _ | false => _ end = _  =>
    let f := fresh in
    set (f := X) ; compute in f ; unfold f  ;clear f
  | |- context[set_literal ?A ?B ?C] =>
    let f := fresh in
    set (f := set_literal A B C) ; compute in f ; unfold f  ;clear f
  | |- match  ?X with HasProof _ _ => _ | _ => _ end = _  =>
    let f := fresh in
    set (f := X) ; compute in f ; unfold f  ;clear f
  | |- match  ?X with Some _ => _ | _ => _ end = _  =>
    let f := fresh in
    set (f := X) ; compute in f ; unfold f  ;clear f
  | |- match  ?X with (A,B)  => _ end = _  =>
    let f := fresh in
    set (f := X) ; compute in f ; unfold f  ;clear f
  | |- hcons_prover _ _ _ _ = _ => unfold hcons_prover
  | |- prover_formula _ _ _ _ _ = _ => unfold prover_formula
  | |- prover _ _ _  = _ => rewrite prover_rew
  | |- context[find_arrows ?A ?B] =>
    let f := fresh in
    set (f := find_arrows A B) ; compute in f ; unfold f  ;clear f
  | |- prover_arrows ?A ?B ?C ?D = _ =>
    rewrite prover_arrows_rew
  | |- (let f := form_of_literal ?A in _) = _  =>
    let form := fresh in
    set (form := form_of_literal A) ; compute in form ; unfold form  ;clear form
  end.

Ltac run_prover :=
  match goal with
    | |- context [prover ?A ?B ?C] =>
    let f := fresh in
    set (f := prover A B C) ; compute in f ; unfold f  ;clear f
  end.

Ltac select_prover :=
  match goal with
  | |- context[prover ?A ?B ?C] =>
    assert (exists prf, prover A B C = prf)
  end.

Ltac select_unit :=
  match goal with
     |- context[unit_propagation ?A ?B ?C] =>
     assert (exists prf, unit_propagation A B C = prf)
  end.

Require Import List.
Require Import Int63.

Definition show_units (h:hmap) (u : IntMap.t bool) : list (@literal int) :=
  IntMap.fold (fun i v (acc:list literal) => match IntMap.find i h with
                              | None => acc
                              | Some (b,f) => (literal_of_bool v (HCons.mk i b f)) :: acc
                              end) u nil.

Definition show_clauses (cl : @map_clauses int) :=
  IntMap.fold (fun i '(l1,l2) acc => (l1++l2)++acc) cl nil.

Definition show_state (h:hmap) (st: @state int) :=
  (show_units h (units st), unit_stack st , show_clauses (clauses st)).

Ltac show_state :=
  match goal with
  | M : hmap |- context[prover _ _ ?S] =>
    let f := fresh in
    set (f := show_state M S) ; compute in f
  | M : hmap |- context[unit_propagation _  ?S _] =>
    let f := fresh in
    set (f := show_state M S) ; compute in f
  | M : hmap |- context[mkstate ?A ?B ?C ?D ?E] =>
    let f := fresh in
    set (f := show_state M (mkstate A B C D E)) ; compute in f


  end.

Ltac getM :=
  match goal with
  | |-context[wfb ?M] =>
    let m := fresh "M" in
    set (m:=M)
  end.



Notation "'TTT'" := (HCons.mk _ _ TT).
Notation "'FFF'" := (HCons.mk _ _ FF).
Notation "A _/\_ B" := (HCons.mk _ _ (OP AND A B)) (at level 80).
Notation "A _\/_ B" := (HCons.mk _ _ (OP OR A B)) (at level 80).
Notation "A  -->  B" := (HCons.mk _ _ (OP IMPL A B)) (at level 80).
Notation "'AT' x" := (HCons.mk _ _ (AT x)) (at level 80).
