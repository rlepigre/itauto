Require Import ZArith.
Require Import List Bool Lia.
Require Import Morphisms.
Require Import Cdcl.Base.Syntax Cdcl.Base.Lib Cdcl.Base.Lit Cdcl.Base.Clause.

Import Lit.

Fixpoint cons_lit (l:Lit.t) (cl:clause) :=
  match cl with
  | nil => l::nil
  | l1::cl' => if pol l1 || negb (pol l) then l::cl
               else l1 ::(cons_lit l cl')
  end.

Lemma cons_lit_POS_true : forall l cl,
    pol l = true ->
    cons_lit l (map POS cl) = POS (var l) :: map POS cl.
Proof.
  induction cl.
  - simpl. intros. destruct l; simpl ; auto. discriminate.
  - intros. simpl.  destruct l; simpl ; auto. discriminate.
Qed.

Lemma cons_lit_POS_false : forall l cl,
    pol l = false ->
    cons_lit l cl = l :: cl.
Proof.
  induction cl;simpl.
  - reflexivity.
  - intros.
    rewrite H. rewrite orb_comm. simpl.
    reflexivity.
Qed.

Lemma wf_sublist :
  forall cl cl'
           (SUB:sublist cl' cl)
           (WF: wf cl),
      wf cl'.
  Proof.
    unfold wf.
    intros.
    destruct WF as (n & p & EQ).
    revert n p EQ.
    induction SUB;intros.
    - exists nil. exists nil. reflexivity.
    - destruct n.
      destruct p.
      + discriminate.
      + inv EQ.
        destruct (IHSUB nil p eq_refl) as (n1& n2 & EQ).
        subst.
        exists n1. exists n2.
        reflexivity.
      + inv EQ.
        destruct (IHSUB _ _ eq_refl) as (n1& n2 & EQ).
        subst.
        exists n1. exists n2.
        reflexivity.
    - destruct n.
      destruct p.
      + discriminate.
      + inv EQ.
        destruct (IHSUB nil p eq_refl) as (n1& n2 & EQ).
        subst.
        destruct n1.
        * simpl. exists nil,(h::n2). reflexivity.
        * simpl in SUB.
          apply (sublist_forall Lit.isPOS) in SUB.
          inv SUB. discriminate.
          rewrite Forall_map.
          rewrite Forall_forall.
          intros. reflexivity.
      + inv EQ.
        destruct (IHSUB _ _ eq_refl) as (n1& n2 & EQ).
        subst.
        exists (h::n1).
        exists n2.
        reflexivity.
  Qed.



Lemma wf_cons_lit : forall l cl,
    wf cl -> wf (cons_lit l cl).
Proof.
  unfold wf.
  intros.
  destruct H as (l1 & l2 & EQ).
  subst.
  revert l2.
  induction l1.
  - simpl. intros.
    destruct (pol l) eqn:POL.
    exists nil,(var l::l2).
    rewrite cons_lit_POS_true by auto.
    reflexivity.
    exists (var l::nil),l2.
    simpl.
    rewrite cons_lit_POS_false by auto.
    destruct l ; try discriminate ; reflexivity.
  - intros.
    simpl.
    destruct (pol l) eqn:PL; simpl.
    destruct (IHl1 l2) as (l1' & l2' & EQ).
    rewrite EQ.
    exists (a::l1'), l2'.
    reflexivity.
    exists (var l ::a ::l1), l2.
    destruct l; try discriminate. reflexivity.
Qed.



Inductive has_cardinal {A: Type}: list A -> nat -> Prop :=
| Card0 : has_cardinal nil 0
| CardS : forall n l x, has_cardinal l n ->
                        ~ In x l ->
                        has_cardinal (x::l) (S n).

Lemma has_cardinal_no_dup : forall {A: Type} (l:list A),
    NoDup l ->
    has_cardinal l (length l).
Proof.
  intros.
  induction H.
  - simpl. constructor.
  - simpl.
    constructor;auto.
Qed.

Definition vars_of_clause (cl:clause) := List.map Lit.var cl.

Definition vars_of_cnf (cls : cnf) := List.fold_right (fun e acc => vars_of_clause e ++ acc) nil cls.

Lemma nodup_nil : forall {A: Type} (dec : forall (x y:A), {x = y} + {x <> y}) l,
                         nodup dec l = nil -> l = nil.
Proof.
  induction l.
  - reflexivity.
  - simpl. destruct (in_dec dec a l).
    intro. apply IHl in H. subst. simpl in i. tauto.
    discriminate.
Qed.

Lemma vars_of_clause_nil : forall l, vars_of_clause l = nil -> l = nil.
Proof.
  unfold vars_of_clause.
  apply map_eq_nil.
Qed.

Lemma vars_of_cnf_nil : forall cls,
    vars_of_cnf cls = nil ->
    cls = List.map (fun _ => nil) cls.
Proof.
  induction cls.
  - simpl. reflexivity.
  - simpl. intros.
    apply app_eq_nil in H.
    destruct H as [H1 H2].
    apply vars_of_clause_nil in H1.
    apply IHcls in H2.
    subst a. rewrite <- H2. reflexivity.
Qed.

Definition is_clause_of (p:HFormula) (cl: list Lit.t) :=
  forall l, In l cl -> var l = p.

Lemma vars_of_cnf_uniq : forall p cls,
  (forall x , In x (vars_of_cnf cls) -> x = p) ->
  forall cl : clause, In cl cls -> is_clause_of p cl.
Proof.
  induction cls.
  - intros. simpl in H0. tauto.
  - intros.
    simpl in H0. simpl in H. destruct H0 ; subst.
    assert ((forall x, In x (vars_of_clause cl) -> x = p)).
    { intros. apply H. rewrite in_app_iff. tauto. }
    clear H IHcls.
    unfold is_clause_of.
    intros. unfold vars_of_clause in H0. apply H0.
    rewrite in_map_iff. exists l; simpl;auto.
    eapply IHcls;eauto.
    intros.
    apply H. rewrite in_app_iff. tauto.
Qed.

Definition boeval (env : HFormula -> bool) (o: option HFormula) :=
  match o with
  | None => false
  | Some i => env i
  end.

Definition oeval (env: HFormula -> Prop) (o: option HFormula) :=
  match o with
  | None => False
  | Some i => env i
  end.


Fixpoint map_filter {A B: Type} (F: A -> option B ) (l: list A) : list B :=
  match l with
  | nil => nil
  | e::l => match F e with
            | None => map_filter F l
            | Some e' => e' :: map_filter F l
            end
  end.


Module Elim.

  Fixpoint get_polarity_rec (p:HFormula)  (l :  clause) :=
    match l with
    | nil => None
    | li :: l => match Lit.get_pol p li with
                 | None =>
                     match get_polarity_rec p  l with
                     | None => None
                     | Some (b,l) => Some (b,li::l)
                     end
                 | Some b   => Some (b,l)
                 end
    end.

  Fixpoint normalise (cl: clause): option clause :=
    match cl with
    | nil => Some nil
    | l::cl' => match normalise cl' with
                | None => None
                | Some cl' => match get_polarity_rec (Lit.var l) cl'  with
                              | None => Some (l::cl')
                              | Some(b,_) => if Lit.eq_dec (Lit.make (negb b) (Lit.var l)) l
                                             then None else Some cl'
                              end
                end
    end.

  Fixpoint split_clause (l1: clause) : clause * clause :=
    match  l1 with
    | nil => (nil,nil)
    | POS p::l => (nil,l1)
    | NEG p::l => let (ln,lp):= split_clause l in
                  (NEG p::ln,lp)
    end.


  Definition merge_clause (cl1 cl2 : clause) : clause :=
    let (cln1,clp1) := split_clause cl1 in
    let (cln2,clp2) := split_clause cl2 in
    cln1 ++ cln2 ++ clp1 ++ clp2.


Fixpoint resolve_all (l1:cnf) (l2:cnf) :=
  match l1 with
  | nil => nil
  | cl::l1 => map_filter normalise (List.map (merge_clause cl) l2) ++ (resolve_all l1 l2)
  end.



Fixpoint split_polarity (p: HFormula) (l: cnf) : cnf * cnf * cnf:=
  match l with
  | nil => (nil,nil,nil)
  | cl::l => let '(lp,ln,lo) := split_polarity p l in
             match normalise cl with
             | None => split_polarity p l
             | Some cl' =>
                 match get_polarity_rec p cl' with
                 | None => (lp,ln,cl'::lo)
                 | Some(b,cl') => (if b then cl'::lp else lp ,if b then ln else cl'::ln,lo)
                 end
             end
  end.


Definition elim (p:HFormula) (l: cnf) :=
  let '(lp,ln,lo) := split_polarity p l in
  resolve_all lp ln ++ lo.


(*  Definition eval_oclause (env: positive -> Prop) (cl:option clause) :=
    match cl with
    | None => True
    | Some cl => eval_clause env cl
    end.
*)


End Elim.


Definition is_var_of_clause (v:HFormula) (cl: clause) :=
  exists l, In l cl /\ var l = v.

Definition is_var_of_cnf (v:HFormula) (cls: cnf) :=
  exists cl, In cl cls /\ is_var_of_clause v cl.

Lemma is_var_of_cnf_cons : forall v c cls,
    is_var_of_cnf v (c :: cls) <-> (is_var_of_clause v c \/ is_var_of_cnf v cls).
Proof.
  unfold is_var_of_cnf at 1.
  intros. simpl. firstorder congruence.
Qed.

Lemma is_var_of_cnf_nil : forall v,
    is_var_of_cnf v nil <-> False.
Proof.
  unfold is_var_of_cnf at 1.
  intros. simpl. firstorder congruence.
Qed.

Lemma is_var_of_cnf_app : forall v cl1 cl2,
    is_var_of_cnf v (cl1 ++cl2) <-> (is_var_of_cnf v cl1 \/ is_var_of_cnf v cl2).
Proof.
  induction cl1.
  - intros.
    simpl.
    rewrite is_var_of_cnf_nil.
    tauto.
  -intros.
   simpl.
   rewrite !is_var_of_cnf_cons.
   rewrite IHcl1.
   tauto.
Qed.




Lemma is_var_of_clause_cons : forall v l cl,
    is_var_of_clause v (l::cl) <->
      var l = v \/ is_var_of_clause v cl.
Proof.
  unfold is_var_of_clause.
  simpl. firstorder congruence.
Qed.

Lemma is_var_of_clause_nil : forall v,
    is_var_of_clause v nil <-> False.
Proof.
  unfold is_var_of_clause.
  simpl. firstorder congruence.
Qed.

Lemma is_var_of_clause_app : forall v cl1 cl2,
    is_var_of_clause v (cl1++cl2) <->
      is_var_of_clause v cl1 \/ is_var_of_clause v cl2.
Proof.
  induction cl1;simpl;intros.
  - rewrite is_var_of_clause_nil.
  tauto.
  - rewrite! is_var_of_clause_cons.
    rewrite! IHcl1.
    tauto.
Qed.





Lemma vars_of_clause_ok : forall p cl,
    is_var_of_clause p cl <-> In p (vars_of_clause cl).
Proof.
  induction cl.
  - rewrite is_var_of_clause_nil.
    simpl. tauto.
  - rewrite is_var_of_clause_cons.
    simpl.
    rewrite IHcl.
    tauto.
Qed.

Lemma vars_of_cnf_ok : forall cls v,
    is_var_of_cnf v cls <-> In v (vars_of_cnf cls).
Proof.
  unfold is_var_of_cnf, vars_of_cnf,vars_of_clause.
  induction cls;simpl;intros.
  - split; firstorder.
  - rewrite in_app_iff.
    rewrite <- IHcls.
    rewrite in_map_iff.
    firstorder congruence.
Qed.

Lemma is_var_of_cnf_False : forall cls,
    (forall v , is_var_of_cnf v cls -> False) ->
    forall cl, In cl cls -> cl = nil.
Proof.
  intros.
  induction cls.
  - simpl. firstorder.
  - simpl in H0.
    destruct H0; subst.
    destruct cl;auto.
    exfalso.
    apply (H (var t)).
    rewrite is_var_of_cnf_cons.
    left. rewrite is_var_of_clause_cons.
    tauto.
    eapply IHcls; auto.
    intros.
    apply (H v).
    rewrite is_var_of_cnf_cons. tauto.
Qed.

Definition match_option (p:HFormula) (o:option HFormula) :=
  match o with
  | None => False
  | Some q => p = q
  end.

Lemma match_option_dec : forall p o,
    match_option p o \/ ~ match_option p o.
Proof.
  destruct o; simpl.
  destruct (hformula_eq_dec p h);tauto.
  tauto.
Qed.

Lemma beval_clauses_Nil : forall p,
    (forall env : HFormula -> bool,
        beval_cnf env nil = true -> env p = true) -> False.
Proof.
  intros.
  simpl in H.
  specialize (H (fun _ => false) eq_refl).
  discriminate.
Qed.


Lemma beval_clause_one_var : forall p cl,
  (forall v, is_var_of_clause v cl -> p = v) ->
  beval_clause (fun _ => false) cl = false ->
  (forall l, In l cl -> l = POS p).
Proof.
  intros.
  induction cl.
  - simpl in *.
    tauto.
  - simpl in *.
    rewrite orb_false_iff in *.
    destruct H0 ; subst.
    intros.
    destruct H1 ; subst.
     +
    assert (p = (var l)).
    {
      apply H.  unfold is_var_of_clause.
      simpl. exists l. intuition congruence.
    }
    subst.
    destruct l ; simpl in *; auto.
    unfold beval_lit in *.
    simpl in *. discriminate.
     +
       eapply IHcl; eauto.
       intros.
       apply H.
       rewrite is_var_of_clause_cons.
       tauto.
Qed.

Lemma beval_clauses_one_var : forall p cls,
  (forall env : HFormula -> bool,
    beval_cnf env cls = true -> env p = true) ->
  (forall v , is_var_of_cnf v cls -> p = v) ->
  exists cl, In cl cls /\ forall l, In l cl -> l = POS p.
Proof.
  intros.
  specialize (H (fun _ => false)).
  induction cls.
  - simpl in *.
    intuition congruence.
  - simpl in *.
    destruct (beval_clause (fun _  => false) a) eqn:B.
    simpl in H.
    apply IHcls in H.
    destruct H as (cl & IN & ALLPOS).
    exists cl.
    tauto.
    { intros. apply H0.
      rewrite is_var_of_cnf_cons. tauto.
    }
    simpl in H.
    clear H.
    assert (IVC : forall v, is_var_of_clause v a -> p = v).
    { intros. apply H0. rewrite is_var_of_cnf_cons. tauto. }
    specialize (beval_clause_one_var p _ IVC B).
    intros.
    exists a. tauto.
Qed.

Lemma eval_clause_POS : forall env p cl,
  (forall l : t, In l cl -> l = POS p) ->
  eval_clause env cl ->
  env p.
Proof.
  induction cl; simpl.
  - tauto.
  - intros.
    unfold eval_lit in H0.
    rewrite (H _ (or_introl eq_refl)) in *.
    simpl in H0.
    destruct H0;auto.
Qed.

Lemma eval_clauses_all_pos :
  forall env p cl cls
         (INC : In cl cls)
         (ALLP : forall l : t, In l cl -> l = POS p),
    eval_cnf env cls -> env p.
Proof.
  induction cls.
  - simpl. tauto.
  - intros.
    simpl in H. destruct H.
    destruct INC. subst.
    eapply eval_clause_POS in ALLP; eauto.
    eapply IHcls; eauto.
Qed.

Lemma eval_clause_cons_lit_POS : forall env l cl,
    Forall (fun l : t => pol l = true) cl ->
    eval_lit env l (eval_clause env cl) <-> eval_clause env (cons_lit l cl).
Proof.
  intros. induction H.
  - simpl. tauto.
  - simpl. rewrite H. simpl.
    tauto.
Qed.

Lemma eval_clause_cons_lit_NEG : forall env l cl,
    pol l = false ->
    eval_lit env l (eval_clause env cl) <-> eval_clause env (cons_lit l cl).
Proof.
  intros. induction cl; simpl.
  - simpl. tauto.
  - rewrite H. simpl. rewrite orb_comm. simpl.
    tauto.
Qed.



Lemma beval_clause_cons_lit : forall env l cl,
    beval_clause env (cons_lit l cl) = (beval_lit env l || beval_clause env cl).
Proof.
  induction cl; simpl.
  - reflexivity.
  - destruct (pol a || (negb (pol l))).
    simpl. btauto.
    simpl. rewrite IHcl. btauto.
Qed.

Lemma get_polarity_spec :
  forall env p cl,
         match Elim.get_polarity_rec p cl with
         | None => ~ is_var_of_clause  p  cl
         | Some (b,cl') =>
             beval_clause env cl = beval_clause env (cons_lit (Lit.make b p) cl')
         end.
Proof.
  induction cl.
  - simpl. rewrite is_var_of_clause_nil. tauto.
  - intros.
    simpl.
    destruct (Lit.get_pol p a) eqn:GP.
    apply Lit.get_pol_inv in GP.
    subst.
    + rewrite beval_clause_cons_lit.
      reflexivity.
    + destruct (Elim.get_polarity_rec p cl).
      destruct p0.
      rewrite beval_clause_cons_lit in *.
      rewrite IHcl.
      simpl.
      rewrite orb_comm.
      rewrite <- orb_assoc.
      f_equal.
      rewrite orb_comm.
      reflexivity.
      * rewrite is_var_of_clause_cons.
        apply Lit.get_pol_None in GP.
        intro. intuition congruence.
Qed.

Definition beval_option {A: Type} (eA: A -> bool) (v: option A) :=
  match v with
  | None => true
  | Some v => eA v
  end.

Definition eval_option {A: Type} (eA: A -> Prop) (v: option A) :=
  match v with
  | None => True
  | Some v => eA v
  end.


Lemma beval_normalise : forall env cl,
    beval_clause env cl = beval_option (beval_clause env) (Elim.normalise cl).
Proof.
  induction cl.
  - simpl. reflexivity.
  - simpl.
    destruct (Elim.normalise cl) eqn:N.
    simpl in *.
    rewrite IHcl.
    generalize (get_polarity_spec env (var a) c).
    destruct (Elim.get_polarity_rec (Lit.var a) c) eqn:GP.
    destruct p.
    destruct (Lit.eq_dec (Lit.make (negb b) (Lit.var a)) a).
    +
      rewrite beval_clause_cons_lit.
      simpl.
      intro E.
      rewrite E.
      rewrite <- e at 1.
      rewrite orb_assoc.
      rewrite eval_lit_negb_make.
      rewrite negb_involutive.
      rewrite orb_negb_l. reflexivity.
    + intros.
      simpl.
      rewrite H.
      rewrite beval_clause_cons_lit.
      simpl.
      apply make_var in n.
      rewrite negb_involutive in n.
      rewrite n.
      btauto.
    + simpl.
      auto.
    + simpl in *.
      rewrite IHcl.
      btauto.
Qed.

Lemma beval_cnf_cons_lit : forall env l lp,
    beval_cnf env (map (cons_lit l) lp) = (Lit.beval_lit env l || (beval_cnf env lp)).
Proof.
  induction lp;simpl.
  - btauto.
  - rewrite IHlp.
    rewrite beval_clause_cons_lit.
    btauto.
Qed.


Lemma split_polarity_eval : forall env p l lp ln lo,
    Elim.split_polarity p l = (lp,ln,lo) ->
    beval_cnf env l = (beval_cnf env lo) && (beval_cnf env (List.map (cons_lit (POS p)) lp))
                      && (beval_cnf env (List.map (cons_lit (NEG p)) ln)).
Proof.
  induction l.
  - simpl; intros.
    inv H.
    simpl. reflexivity.
  -  intros.
     simpl in H.
     simpl.
     destruct (Elim.split_polarity p l) as [[lp' ln'] lo'] eqn:E.
     rewrite (IHl lp' ln' lo') by auto.
     rewrite (beval_normalise env a).
     destruct (Elim.normalise a); simpl.
     +
       generalize (get_polarity_spec env p c).
       destruct (Elim.get_polarity_rec p c).
       destruct p0 as [b cl'].
       inv H.
       intros.
       rewrite H.
       rewrite !beval_cnf_cons_lit. simpl.
       rewrite beval_clause_cons_lit.
       destruct b ; simpl.
       btauto.
       btauto.
       inv H.
       intros.
       simpl.
       btauto.
     +  inv H. btauto.
Qed.

Lemma beval_cnf_normalise : forall env cl,
    beval_cnf env (map_filter Elim.normalise cl) =  beval_cnf env cl.
Proof.
  induction cl.
  - simpl. tauto.
  - simpl.
    specialize (beval_normalise env a).
    destruct (Elim.normalise a).
    simpl. intro. rewrite <- H. rewrite IHcl. reflexivity.
    simpl. intros. rewrite H. simpl. auto.
Qed.

Lemma beval_split_clause : forall env cl1 n1 p1,
    Elim.split_clause cl1 = (n1, p1) ->
    beval_clause env cl1 = beval_clause env(n1 ++ p1).
Proof.
  induction cl1.
  - simpl. intros. inv H.
    reflexivity.
  - intros. simpl in H.
    destruct a. inv H.
    simpl. reflexivity.
    destruct (Elim.split_clause cl1) as (ln2,lp2) eqn:SC.
    inv H.
    simpl. erewrite IHcl1; eauto.
Qed.

Lemma beval_merge_clause : forall env cl1 cl2,
    beval_clause env (Elim.merge_clause cl1 cl2) = (beval_clause env cl1 || beval_clause env cl2).
Proof.
  unfold Elim.merge_clause.
  intros.
  destruct (Elim.split_clause cl1) as (cln1,clp1) eqn:SC1.
  destruct (Elim.split_clause cl2) as (cln2,clp2) eqn:SC2.
  rewrite! beval_clause_app.
  eapply beval_split_clause in SC1;eauto.
  eapply beval_split_clause in SC2;eauto.
  rewrite SC1. rewrite SC2.
  rewrite! beval_clause_app.
  btauto.
Qed.


Lemma beval_cnf_merge_clause : forall env clp ln,
    beval_cnf env (map (Elim.merge_clause clp) ln) = beval_clause env clp || beval_cnf env ln.
Proof.
  induction ln.
  - simpl. rewrite orb_comm. reflexivity.
  - simpl.
    rewrite IHln.
    rewrite beval_merge_clause.
    btauto.
Qed.

Lemma beval_cnf_Forall : forall env cls,
    beval_cnf env cls = true <->
    Forall (fun x : clause => beval_clause env x = true) cls.
Proof.
  induction cls.
  - simpl; split; auto.
  - simpl. rewrite andb_true_iff.
    rewrite IHcls.
    intuition. inv H1; auto.
    inv H1; auto.
Qed.


Lemma resolve_all_eval : forall env lp ln,
        beval_cnf  env (Elim.resolve_all lp ln)= true ->
        forall clp cln, In clp lp -> In cln ln -> beval_clause env clp = true \/ beval_clause env cln = true.
Proof.
  induction lp;simpl.
  - tauto.
  - intros.
    rewrite beval_cnf_app in H.
    rewrite andb_true_iff in H.
    destruct  H as [E1 E2].
    destruct H0 ; subst.
    rewrite beval_cnf_normalise in E1.
    rewrite beval_cnf_merge_clause in E1.
    rewrite orb_true_iff in E1.
    destruct E1 ; auto.
    right.
    revert cln H1.
    rewrite <- Forall_forall.
    apply beval_cnf_Forall;auto.
    eapply IHlp;eauto.
Qed.

Lemma NoDup_no_var :
  forall p c
         (ND : NoDup (vars_of_clause c)) b c',
    Elim.get_polarity_rec p c = Some (b, c') ->
    is_var_of_clause p c' ->
    False.
Proof.
  induction c.
  - intros. simpl in H. discriminate.
  - intros. simpl in ND.
    inv ND.
    simpl in H.
    destruct (get_pol p a) eqn:POL.
    + inv H.
    apply get_pol_inv in POL.
    subst.
    rewrite Lit.var_make in H3.
    rewrite <- vars_of_clause_ok in H3.
    tauto.
    +  apply get_pol_None in POL.
       destruct (Elim.get_polarity_rec p c) eqn:GP; try discriminate.
       destruct p0. inv H.
       rewrite is_var_of_clause_cons in H0.
       destruct H0; try tauto.
       eapply IHc;eauto.
Qed.

Lemma normalise_NoDup : forall a c,
    Elim.normalise a = Some c ->
    NoDup (vars_of_clause c).
Proof.
  induction a.
  - simpl. intros. inv H. constructor.
  - simpl. intros.
    destruct (Elim.normalise a0) eqn:N.
    destruct (Elim.get_polarity_rec (var a) c0) eqn:GP.
    destruct p. destruct (eq_dec (make (negb b) (var a)) a).
    +  discriminate.
    + inv H.
      apply IHa; auto.
    +inv H.
     simpl.
     constructor.
     generalize (get_polarity_spec (fun _ => true) (var a) c0).
     rewrite GP.
     rewrite vars_of_clause_ok. auto.
     apply IHa;auto.
    +  discriminate.
Qed.

Lemma split_polarity_vars :
  forall p l lp ln lo,
    Elim.split_polarity p l = (lp,ln,lo) ->
    ~ is_var_of_cnf p lp /\ ~ is_var_of_cnf p ln /\ ~ is_var_of_cnf p lo.
Proof.
  induction l ;simpl.
  - intros. inv H.
    rewrite is_var_of_cnf_nil.
    tauto.
  - intros.
    destruct (Elim.split_polarity p l) as [[lp' ln'] lo'] eqn:SP.
    destruct (Elim.normalise a) eqn:NORM.
    specialize (IHl _ _ _  eq_refl).
    destruct (Elim.get_polarity_rec p c) eqn:P.
    destruct p0. inv H.
    assert (~ is_var_of_clause p l0).
    { intro.
      eapply NoDup_no_var in P; auto.
      eapply normalise_NoDup in NORM    ; eauto.
    }
    destruct b; rewrite is_var_of_cnf_cons.
    tauto. tauto.
    inv H.
    rewrite is_var_of_cnf_cons.
    specialize (get_polarity_spec (fun _ => true) p c).
    rewrite P.
    tauto.
    inv H. eapply IHl;eauto.
Qed.

Definition set_env {A: Type}(env: HFormula -> A) (x': HFormula) (v: A) :=
  fun x => if hformula_eq_dec x x' then v else env x.

Lemma set_env_same : forall {A:Type} env p (v:A),
    set_env env p v p = v.
Proof.
  unfold set_env.
  intros. destruct (hformula_eq_dec p p);try congruence.
Qed.

Lemma beval_lit_no_var : forall p b env l,
    var l <> p ->
    beval_lit (set_env env p b) l = beval_lit env l.
Proof.
  unfold beval_lit.
  intros.
  unfold set_env.
  destruct (hformula_eq_dec (var l) p); try congruence.
Qed.

Lemma beval_clause_no_var : forall p b env cl,
    ~ is_var_of_clause p cl ->
    beval_clause (set_env env p b) cl = beval_clause env cl.
Proof.
  induction cl;simpl.
  - reflexivity.
  - rewrite is_var_of_clause_cons.
    intros.
    rewrite IHcl by tauto.
    rewrite beval_lit_no_var by tauto.
    reflexivity.
Qed.

Lemma beval_no_var : forall p l b env,
    ~ is_var_of_cnf p  l ->
    beval_cnf (set_env env p b) l = beval_cnf env l.
Proof.
  intros.
  induction l.
  - simpl. reflexivity.
  - simpl.
    rewrite is_var_of_cnf_cons in H.
    rewrite IHl by tauto.
    f_equal.
    apply beval_clause_no_var.
    tauto.
Qed.

Lemma beval_cnf_exists : forall env cls,
    (beval_cnf env cls = true -> False) ->
    exists cl, In cl cls /\ beval_clause env cl = false.
Proof.
  induction cls;simpl.
  - tauto.
  - intros.
    rewrite andb_true_iff in H.
    destruct (beval_clause env a) eqn:EC.
    specialize (fun E => H (conj eq_refl E)).
    apply IHcls in H.
    destruct H as (c & T1 & T2).
    exists c. tauto.
    exists a. tauto.
Qed.


Lemma elim_complete :
  forall p l
         (EV :forall env , beval_cnf env l = true -> False)
         env
         (EL : beval_cnf env  (Elim.elim p l) = true), False.
    Proof.
      unfold Elim.elim.
      intros.
      destruct (Elim.split_polarity p l) as [[lp ln] lo] eqn:SP.
      rewrite beval_cnf_app in EL.
      assert (EV' : forall env, beval_cnf env lo && beval_cnf env (map (cons_lit (POS p)) lp) && beval_cnf env (map (cons_lit (NEG p)) ln) = true -> False).
      {
        intros.
        apply (EV env0).
        rewrite (split_polarity_eval env0 p l lp ln lo) by auto.
        tauto.
      }
      clear EV.
      rewrite andb_true_iff in EL.
      destruct EL as (EL1 & EL2).
      apply split_polarity_vars in SP ; auto.
      generalize (EV' (set_env env p true)).
      generalize (EV' (set_env env p false)).
      clear EV'.
      rewrite! beval_cnf_cons_lit.
      unfold beval_lit; simpl.
      rewrite! set_env_same. simpl.
      rewrite! andb_true_r.
      rewrite! beval_no_var by tauto.
      rewrite EL2.
      simpl.
      intros.
      apply beval_cnf_exists in H.
      apply beval_cnf_exists in H0.
      destruct H as (cl1 & IN1 & E1).
      destruct H0 as (cl2 & IN2 & E2).
      eapply resolve_all_eval in EL1;eauto.
      intuition congruence.
    Qed.

    Definition clause_of_opt (o:option HFormula) :=
      match o with
      | None => nil
      | Some i => (NEG i :: nil) ::nil
      end.

    Lemma eval_clause_of_opt : forall env l,
        beval_cnf env (clause_of_opt l) = negb (boeval env l).
    Proof.
      destruct l;simpl.
      unfold beval_lit. simpl.
      btauto.
      reflexivity.
    Qed.

    Lemma neg_concl : forall cls l,
      (forall env, beval_cnf env cls = true -> boeval env l = true)
      <->
        (forall env, beval_cnf env (clause_of_opt l ++ cls) = true -> False).
    Proof.
      split;intros.
      rewrite beval_cnf_app in *.
      rewrite andb_true_iff in H0.
      destruct H0.
      apply H in H1.
      rewrite eval_clause_of_opt in H0.
      rewrite H1 in H0. discriminate.
      specialize (H env).
      rewrite beval_cnf_app in H.
      rewrite eval_clause_of_opt in H.
      destruct (boeval env l); auto.
    Qed.

    Lemma get_polarity_spec_var : forall p c,
        Elim.get_polarity_rec p c <> None ->
        is_var_of_clause p c.
    Proof.
      induction c ; simpl.
      - rewrite is_var_of_clause_nil.
        tauto.
      - destruct (get_pol p a) eqn: POL.
        rewrite is_var_of_clause_cons.
        intros.
        apply get_pol_inv in POL.
        subst.
        rewrite var_make. tauto.
        destruct (Elim.get_polarity_rec p c); try congruence.
        destruct p0.
        intros.
        apply get_pol_None in POL.
        rewrite is_var_of_clause_cons.
        intuition congruence.
    Qed.

    Lemma get_polarity_spec_not_var : forall p c,
        ~ is_var_of_clause p c ->
        Elim.get_polarity_rec p c = None.
    Proof.
      intros.
      destruct (Elim.get_polarity_rec p c) eqn:G;auto.
      exfalso.
      assert (Elim.get_polarity_rec p c <> None) by congruence.
      apply get_polarity_spec_var in H0.
      tauto.
    Qed.


    Lemma normalise_vars : forall p c c',
        Elim.normalise c = Some c' ->
        is_var_of_clause p c <-> is_var_of_clause p c'.
    Proof.
      induction c;simpl.
      - intros. inv H.
        tauto.
      - intros.
        destruct (Elim.normalise c) eqn: N; try discriminate.
        destruct (Elim.get_polarity_rec (var a) c0) eqn: G.
        destruct p0.
        destruct (eq_dec (make (negb b) (var a)) a); try discriminate.
        inv H. rewrite is_var_of_clause_cons.
        apply make_var in n.
        rewrite negb_involutive in n.
        rewrite IHc by auto.
        assert (G' : Elim.get_polarity_rec (var a) c' <> None) by congruence.
        apply get_polarity_spec_var  in G'.
        intuition congruence.
        inv H.
        rewrite! is_var_of_clause_cons.
        rewrite IHc by auto.
        tauto.
    Qed.


    Lemma split_polarity_no_vars : forall p cl1 cl2 lp ln lo,
        ~ is_var_of_cnf p cl1 ->
          Elim.split_polarity p cl2 = (lp,ln,lo) ->
          Elim.split_polarity p (cl1 ++ cl2) = (lp, ln, map_filter Elim.normalise cl1++lo).
    Proof.
      induction cl1.
      - simpl. auto.
      - simpl.
        intros.
        apply IHcl1 in H0.
        rewrite H0.
        destruct (Elim.normalise a) eqn:N.
        apply normalise_vars with (p:=p) in N.
        rewrite is_var_of_cnf_cons in H.
        rewrite get_polarity_spec_not_var by tauto.
        reflexivity.
        reflexivity.
        rewrite is_var_of_cnf_cons in H.
        tauto.
    Qed.

    
Lemma elim_no_vars : forall env p cl1 cl2,
    ~ is_var_of_cnf p cl1 ->
    beval_cnf env (Elim.elim p (cl1 ++ cl2)) =     beval_cnf env (cl1 ++ Elim.elim p cl2).
  Proof.
    unfold Elim.elim.
    intros.
    destruct (Elim.split_polarity p (cl1 ++ cl2)) as ((lp,ln),lo) eqn: S1.
    destruct (Elim.split_polarity p cl2) as ((lp1,ln1),lo1) eqn: S2.
    rewrite! beval_cnf_app.
    apply split_polarity_no_vars with (cl1:=cl1) in S2; auto.
    rewrite S1 in S2. inv S2.
    rewrite beval_cnf_app.
    rewrite beval_cnf_normalise.
    btauto.
  Qed.


(*Lemma split_polarity_vars :
  forall p l lp ln lo,
    Elim.split_polarity p l = (lp,ln,lo) ->
    (is_var_of_cnf v lp -> is_var_of_cnf v l) /\

Proof.
  induction l ;simpl.
  - intros. inv H.
    rewrite is_var_of_cnf_nil.
    tauto.
  - intros.
    destruct (Elim.split_polarity p l) as [[lp' ln'] lo'] eqn:SP.
    destruct (Elim.normalise a) eqn:NORM.
    specialize (IHl _ _ _  eq_refl).
    destruct (Elim.get_polarity_rec p c) eqn:P.
    destruct p0. inv H.
    assert (~ is_var_of_clause p l0).
    { intro.
      eapply NoDup_no_var in P; auto.
      eapply normalise_NoDup in NORM    ; eauto.
    }
    destruct b; rewrite is_var_of_cnf_cons.
    tauto. tauto.
    inv H.
    rewrite is_var_of_cnf_cons.
    specialize (get_polarity_spec (fun _ => true) p c).
    rewrite P.
    tauto.
    inv H. eapply IHl;eauto.
Qed.
*)
  Lemma is_var_of_cnf_normalise : forall v l,
      is_var_of_cnf v (map_filter Elim.normalise l) ->
      is_var_of_cnf v l.
  Proof.
    induction l; simpl;auto.
    destruct (Elim.normalise a) eqn: N.
    - rewrite !is_var_of_cnf_cons.
      apply normalise_vars with (p:=v) in N.
      tauto.
    - rewrite is_var_of_cnf_cons.
      tauto.
  Qed.

  Lemma is_var_of_clause_split : forall v cl cln1 clp1,
      Elim.split_clause cl = (cln1, clp1) ->
      is_var_of_clause v cl <-> is_var_of_clause  v (cln1 ++clp1).
  Proof.
    induction cl;simpl;intros.
    - inv H. simpl. tauto.
    - destruct a.
      inv H.
      simpl.
      rewrite! is_var_of_clause_cons.
      tauto.
      destruct (Elim.split_clause cl) as (cln2,clp2) eqn:SC1.
      inv H.
      rewrite! is_var_of_clause_app.
      rewrite! is_var_of_clause_cons.
      rewrite IHcl by reflexivity.
      rewrite is_var_of_clause_app.
      tauto.
  Qed.



  Lemma is_var_of_clause_merge : forall v cl1 cl2,
  is_var_of_clause v (Elim.merge_clause cl1 cl2) <->
    is_var_of_clause v (cl1 ++ cl2).
  Proof.
    unfold Elim.merge_clause.
    intros.
    destruct (Elim.split_clause cl1) as (cln1,clp1) eqn:SC1.
    destruct (Elim.split_clause cl2) as (cln2,clp2) eqn:SC2.
    rewrite! is_var_of_clause_app.
    apply is_var_of_clause_split with (v:=v) in SC1.
    apply is_var_of_clause_split with (v:=v) in SC2.
    rewrite is_var_of_clause_app in *.
    tauto.
  Qed.

  Lemma is_var_of_cnf_merge : forall v a l2,
      is_var_of_cnf v (map (Elim.merge_clause a) l2) ->
      is_var_of_clause v a \/ is_var_of_cnf v l2.
  Proof.
    induction l2.
    - simpl. rewrite is_var_of_cnf_nil.
      tauto.
    - simpl. rewrite! is_var_of_cnf_cons.
      rewrite! is_var_of_clause_merge.
      rewrite! is_var_of_clause_app.
      tauto.
  Qed.

  Lemma is_var_of_cnf_resolve : forall v l1 l2,
      is_var_of_cnf v (Elim.resolve_all l1 l2) ->
        is_var_of_cnf v (l1++ l2).
  Proof.
    induction l1;simpl.
    - intros. rewrite is_var_of_cnf_nil in H. tauto.
    - intros.
      rewrite is_var_of_cnf_app in H.
      destruct H.
      + rewrite is_var_of_cnf_cons.
        rewrite or_comm.
        rewrite is_var_of_cnf_app.
        rewrite or_assoc.
        right.
        apply is_var_of_cnf_normalise in H.
        apply is_var_of_cnf_merge in H.
        tauto.
      + apply IHl1 in H.
        rewrite is_var_of_cnf_cons.
        tauto.
  Qed.

  Lemma get_polarity_rec_vars_res : forall v v' c b l,
      Elim.get_polarity_rec v' c = Some (b, l) ->
      is_var_of_clause v l -> is_var_of_clause v c.
  Proof.
    induction c.
    - simpl. discriminate.
    - simpl. intros.
      destruct (get_pol v' a) eqn:POL.
      inv H.
      rewrite is_var_of_clause_cons. tauto.
      destruct (Elim.get_polarity_rec v' c) eqn: P.
      destruct p. inv H.
      rewrite is_var_of_clause_cons in *.
      intuition.
      specialize (IHc _ _ eq_refl).
      tauto.
      discriminate.
  Qed.


 Lemma split_polarity_vars_spec : forall v' v cls lp ln lo,
      Elim.split_polarity v' cls = (lp, ln, lo) ->
      is_var_of_cnf v (lp++ln++lo) ->
      is_var_of_cnf v cls /\ v <> v'.
 Proof.
   split.
   - revert lp ln lo H H0.
   induction cls.
   + simpl. intros. inv H.
     rewrite is_var_of_cnf_nil in H0.
     tauto.
   + intros.
     simpl in H.
     destruct (Elim.split_polarity v' cls) as ((lp',ln'),lo').
     specialize (IHcls _ _ _ eq_refl).
     destruct (Elim.normalise a) eqn:N.
     apply normalise_vars with (p:= v) in N.
     destruct (Elim.get_polarity_rec v' c) eqn:GP.
     destruct p. inv H.
     rewrite! is_var_of_cnf_app in H0.
     rewrite is_var_of_cnf_cons.
     specialize (get_polarity_rec_vars_res v _ _ _ _ GP).
     rewrite! is_var_of_cnf_app in *.
     destruct b; rewrite !is_var_of_cnf_cons in *.
     tauto. tauto.
     inv H.
     rewrite is_var_of_cnf_cons.
     rewrite! is_var_of_cnf_app in *.
     rewrite is_var_of_cnf_cons in *.
     tauto.
     rewrite is_var_of_cnf_cons.
     rewrite! is_var_of_cnf_app in *.
     inv H.
     tauto.
   - apply split_polarity_vars in H.
     rewrite! is_var_of_cnf_app in H0.
     intuition congruence.
 Qed.


   
  Lemma is_var_of_cnf_elim : forall v v' cls,
      is_var_of_cnf v (Elim.elim v' cls) -> (is_var_of_cnf v cls /\ v <> v').
  Proof.
    unfold Elim.elim.
    intros.
    destruct (Elim.split_polarity v' cls) as ((lp,ln),lo) eqn:E.
    apply split_polarity_vars_spec with (v:=v)    in E;auto.
    rewrite is_var_of_cnf_app in H.
    rewrite! is_var_of_cnf_app.
    intuition.
    apply is_var_of_cnf_resolve in H0.
    rewrite! is_var_of_cnf_app in H0.
    tauto.
  Qed.

  Lemma wf_cons : forall l cl,
      wf (l :: cl) -> if pol l then Forall (fun l => pol l = true) cl else wf cl.
  Proof.
    intros.
    unfold wf in H.
    destruct H as (l1 & l2 & EQ); subst.
    destruct l1. simpl in EQ.
    destruct l; simpl;auto.
    destruct l2. inv EQ.
    inv EQ.
    rewrite Forall_map.
    rewrite Forall_forall.
    reflexivity.
    destruct l2 ; discriminate.
    inv EQ.
    simpl.
    exists l1,l2;auto.
  Qed.

  Lemma wf_tl : forall l cl,
      wf (l :: cl) -> wf cl.
  Proof.
    unfold wf. intros.
    destruct H as (l1 & l2 & EQ); subst.
    destruct l1. simpl in EQ. destruct l2; try discriminate.
    inv EQ. exists nil,l2. reflexivity.
    inv EQ.
    exists l1,l2. reflexivity.
  Qed.

  Lemma get_polarity_rec_all_pos : forall p cl,
      Forall (fun l : t => pol l = true) cl ->
      forall b cl',
      Elim.get_polarity_rec p cl = Some (b, cl') ->
      b = true /\ Forall (fun l : t => pol l = true) cl'.
  Proof.
    intros p cl ALL.
    induction ALL.
    - simpl. discriminate.
    - intros.
      simpl in H0.
      destruct (get_pol p x) eqn:GP.
      + inv H0. apply get_pol_inv in GP.
      subst.
      destruct b; try discriminate.
      tauto.
      + destruct (Elim.get_polarity_rec p l) eqn:GP'; try discriminate.
        destruct p0. inv H0.
        specialize (IHALL _ _ eq_refl).
        intuition.
  Qed.



  
 Lemma get_polarity_ispec :
  forall env p cl
    (WF : wf cl),
    match Elim.get_polarity_rec p cl with
         | None => ~ is_var_of_clause  p  cl
         | Some (b,cl') =>
             eval_clause env cl <-> eval_clause env (cons_lit (Lit.make b p) cl')
         end.
Proof.
  induction cl.
  - simpl. rewrite is_var_of_clause_nil. tauto.
  - intros.
    simpl.
    destruct (Lit.get_pol p a) eqn:GP.
    apply Lit.get_pol_inv in GP.
    subst.
    +
      apply wf_cons in WF.
      destruct (pol (make b p)) eqn:POL.
      rewrite eval_clause_cons_lit_POS by auto.
      tauto.
      rewrite eval_clause_cons_lit_NEG by auto.
      tauto.
    + destruct (Elim.get_polarity_rec p cl) eqn:GP'.
      destruct p0 as (b,cl').
      simpl.
      assert (WFT := wf_tl a cl WF).
      apply wf_cons in WF.
      destruct (pol a) eqn:PA.
      * simpl.
        rewrite IHcl by auto.
        apply get_polarity_rec_all_pos in GP';auto.
        destruct GP';subst.
        rewrite <- !eval_clause_cons_lit_POS; auto.
        simpl. destruct a ; try discriminate.
        unfold eval_lit ; simpl. tauto.
      * simpl.
        rewrite IHcl by auto.
        destruct b; simpl.
        unfold make. tauto.
        rewrite! cons_lit_POS_false by reflexivity.
        simpl.
        destruct a; try discriminate. unfold eval_lit.
        simpl. tauto.
      * apply wf_tl in WF.
        apply get_pol_None in GP.
        rewrite is_var_of_clause_cons.
        intuition congruence.
Qed.


Lemma sublist_normalise :
  forall  cl cl',
          Elim.normalise cl = Some cl' ->
          sublist cl' cl.
Proof.
  induction cl.
  - simpl. intros. inv H; auto. constructor.
  - simpl; intros.
    destruct (Elim.normalise cl) eqn:N.
    + simpl in *.
    intros.
    destruct (Elim.get_polarity_rec (var a) c) eqn:POL.
    * destruct p.
      destruct (eq_dec (make (negb b) (var a)) a); try discriminate.
      inv H.
      specialize (IHcl _ eq_refl).
      apply SUB_CONS;auto.
    * inv H.
      apply SUB_CONS2; auto.
    + discriminate.
Qed.

Lemma wf_normalise :
  forall  cl cl',
    wf cl ->
    Elim.normalise cl = Some cl' ->
    wf cl'.
Proof.
  intros.
  apply sublist_normalise in H0.
  eapply wf_sublist; eauto.
Qed.

(*Lemma cons_lit_neg : forall env l a,
    eval_lit env a (eval_clause env (cons_lit (neg a) l)).
Proof.
  induction l.
  - simpl. destruct a; unfold eval_lit; simpl. tauto.
*)

Lemma wf_cons_sublist : forall a cl c,
    wf (a :: cl) ->
    sublist c cl ->
    wf (a :: c).
Proof.
  intros.
  apply wf_cons in H.
  destruct (pol a) eqn:PA.
  - unfold wf.
  exists nil, (map var (a::c)).
  simpl.
  f_equal.
  destruct a; try discriminate;auto.
  rewrite map_map.
  apply sublist_forall with (P:= Lit.isPOS) in H0; auto.
  induction H0 ; simpl. reflexivity.
  destruct x ; try discriminate.
  f_equal. auto.
  - apply wf_sublist in H0;auto.
    unfold wf in H0.
    destruct H0 as (l1&l2& EQ).
    subst.
    destruct a; try discriminate.
    exists (f::l1),l2.
    reflexivity.
Qed.

Lemma get_polarity_rec_sublist : forall p cl b cl',
    Elim.get_polarity_rec p cl = Some(b,cl') ->
    sublist cl' cl /\ In (make b p) cl.
Proof.
  induction cl.
  - simpl. discriminate.
  - simpl. intros.
    destruct (get_pol p a) eqn:GP.
    inv H.
    apply get_pol_inv in GP.
    split ; intuition.
    constructor.
    apply sublist_refl.
    destruct (Elim.get_polarity_rec p cl) eqn: GP'.
    destruct p0.
    inv H. apply get_pol_None in GP.
    specialize (IHcl _ _ eq_refl).
    intuition.
    apply SUB_CONS2. auto.
    discriminate.
Qed.

Lemma eval_clause_cons_lit_tauto : forall (env: HFormula -> Prop) p l,
    env p -> eval_clause env (cons_lit (POS p) l).
Proof.
  induction l;simpl.
  - unfold eval_lit. simpl. tauto.
  - rewrite orb_false_r.
    destruct (pol a). simpl. unfold eval_lit. simpl.
    destruct (pol a). tauto.
    tauto.  simpl.
    intros.
    destruct a; unfold eval_lit; simpl.
    tauto. tauto.
Qed.

Lemma cons_lit_twice : forall env a l,
  eval_lit env a (eval_clause env (cons_lit a l)) <-> eval_clause env (cons_lit a l).
Proof.
  induction l; simpl.
  -  unfold eval_lit. destruct a; simpl. tauto.
     tauto.
  - destruct a0; simpl.
    unfold eval_lit.
    destruct a; simpl.
    tauto.
    tauto.
    destruct (pol a) eqn:A; simpl.
    unfold eval_lit. rewrite A. simpl.
    destruct a; try discriminate.
    simpl.
    unfold eval_lit in IHl. simpl in *.
    tauto.
    unfold eval_lit.
    simpl. rewrite A.
    tauto.
Qed.

Lemma eval_normalise :
  forall env cl
         (WF : wf cl),
    eval_clause env cl <-> eval_option (eval_clause env) (Elim.normalise cl).
Proof.
  intros.
  induction cl.
  - simpl. tauto.
  - simpl.
    destruct (Elim.normalise cl) eqn:N.
    +
      assert (SL : sublist c cl).
      {
        apply sublist_normalise in N; auto.
      }
      simpl in *. intros.
      assert (WFTL := wf_tl _ _ WF).
      specialize (IHcl WFTL).
      apply wf_normalise in N; auto.
      generalize (get_polarity_ispec env (var a) c N).
      destruct (Elim.get_polarity_rec (var a) c) eqn:POL.
      * destruct p.
        destruct (eq_dec (make (negb b) (var a)) a); simpl;auto.
        intros.
        split ; auto.
        intros.
        rewrite IHcl.
        rewrite H.
        assert (make b (var a) = Lit.neg a).
        { rewrite <- e. destruct b; simpl;auto. }
        rewrite H1.
        assert (POL':= POL).
        apply get_polarity_rec_sublist in POL.
        destruct POL as (POL & IN).
        rewrite H1 in IN.
        assert (WFC : wf (a::c)).
        {           eapply wf_cons_sublist;eauto. }
        assert (WFL : wf (a::l)).
        {
          eapply wf_cons_sublist;eauto.
        }
        apply wf_cons in WFC.
        destruct (pol a) eqn:PA.
        destruct a ; try discriminate.
        rewrite Forall_forall in WFC.
        apply WFC in IN. discriminate.
        destruct a; try discriminate.
        simpl. unfold eval_lit ; simpl.
        apply eval_clause_cons_lit_tauto.
        intros.
        apply make_var in n.
        rewrite negb_involutive in n.
        rewrite n in *.
        rewrite IHcl.
        rewrite H.
        apply cons_lit_twice.
      * simpl.
        intros.
        rewrite IHcl.
        tauto.
    + simpl in *.
      apply wf_tl in WF.
      rewrite IHcl by auto.
      unfold eval_lit. destruct (pol a).
      tauto.
      tauto.
Qed.

Lemma split_polarity_ieval:
  forall (env : HFormula -> Prop) (p : HFormula) (l lp ln lo : cnf)
           (WF : Forall wf l)
    ,
  Elim.split_polarity p l = (lp, ln, lo) ->
  eval_cnf env l ->
    (eval_cnf env lo /\ eval_cnf env (map (cons_lit (POS p)) lp) /\
       eval_cnf env (map (cons_lit (NEG p)) ln)).
  Proof.
  induction l.
  - simpl; intros.
    inv H.
    simpl. tauto.
  -  intros.
     simpl in H.
     simpl.
     destruct (Elim.split_polarity p l) as [[lp' ln'] lo'] eqn:E.
     inv WF.
     specialize (IHl lp' ln' lo' H4 eq_refl).
     simpl in H0.
     rewrite eval_normalise in H0;auto.
     destruct (Elim.normalise a) eqn:N; simpl.
     +
       apply wf_normalise in N; auto.
       generalize (get_polarity_ispec env p c N).
       destruct (Elim.get_polarity_rec p c).
       *
       destruct p0 as [b cl'].
       inv H.
       intros.
       simpl in H0.
       destruct b;
       simpl;
       intuition.
       * inv H.
         simpl in *.
         intuition.
     +  inv H. tauto.
  Qed.

  Lemma wf_split_polarity:
    forall  (p : HFormula) (l lp ln lo : cnf)
           (WF : Forall wf l)
    ,
      Elim.split_polarity p l = (lp, ln, lo) ->
      Forall wf lp /\ Forall wf ln /\ Forall wf lo.
  Proof.
    induction l.
    - simpl; intros.
      inv H.
      simpl. tauto.
    -  intros.
       simpl in H.
       destruct (Elim.split_polarity p l) as [[lp' ln'] lo'] eqn:E.
       inv WF.
       specialize (IHl lp' ln' lo' H3 eq_refl).
       destruct (Elim.normalise a) eqn:N; simpl.
       +
         apply wf_normalise in N; auto.
         destruct (Elim.get_polarity_rec p c) eqn:GP.
         *
           destruct p0 as [b cl'].
           apply get_polarity_rec_sublist in GP.
           destruct GP.
           apply wf_sublist in H0;auto.
           destruct b; inv H; intuition.
         * inv H. intuition.
       + inv H;intuition.
Qed.

Lemma split_clause_wf : forall l1 l2,
    Elim.split_clause (map NEG l1 ++ map POS l2) = (map NEG l1 , map POS l2).
Proof.
  induction l1;simpl.
  -  destruct l2 ; reflexivity.
  -  intros. rewrite IHl1. reflexivity.
Qed.

Lemma wf_merge_clause :
  forall c1 c2,
    wf c1 -> wf c2 ->
    wf (Elim.merge_clause c1 c2).
Proof.
  intros.
  unfold wf in *.
  destruct H as (l1 & l2 & EQ).
  destruct H0 as (l1' & l2' & EQ').
  subst.
  exists (l1 ++ l1') ,(l2 ++ l2').
  unfold Elim.merge_clause.
  rewrite! split_clause_wf.
  rewrite! map_app.
  rewrite <- !app_assoc.
  reflexivity.
Qed.

Lemma cons_lit_POS_wf : forall v l1 l2,
    (cons_lit (POS v) (map NEG l1 ++ map POS l2)) =
      map NEG l1 ++ (map POS (v::l2)).
Proof.
  induction l1;simpl.
  - destruct l2 ; reflexivity.
  - intros.
    f_equal.
    rewrite IHl1. reflexivity.
Qed.

Lemma cons_lit_NEG_wf : forall v l1 l2,
    (cons_lit (NEG v) (map NEG l1 ++ map POS l2)) =
      map NEG (v::l1) ++ (map POS l2).
Proof.
  destruct l1;simpl;auto.
  destruct l2;simpl;auto.
Qed.

Definition eval_or {A: Type} (F : A -> Prop) (l : list A) :=
  List.fold_right (fun e acc => F e \/ acc) False l.

Definition eval_and {A: Type} (F : A -> Prop) (l : list A) :=
  List.fold_right (fun e acc => F e /\ acc) True l.

Lemma eval_or_app : forall {A: Type} (F: A-> Prop) l1 l2,
    eval_or F (l1++l2) <-> (eval_or F l1 \/ eval_or F l2).
Proof.
  induction l1;simpl.
  - tauto.
  - intros. rewrite IHl1. tauto.
Qed.


Lemma eval_clause_or : forall env l,
    eval_clause env (map POS l) <-> eval_or env l.
Proof.
  induction l;simpl.
  - tauto.
  - rewrite IHl. unfold eval_lit. simpl. tauto.
Qed.

Lemma eval_clause_wf : forall env l1 l2,
    eval_clause env (map NEG l1 ++ l2) <-> (eval_and env l1 -> eval_clause env l2).
Proof.
  induction l1.
  - simpl.
    intros. tauto.
  - simpl. intros.
    rewrite IHl1.
    unfold eval_lit. simpl. tauto.
Qed.

Lemma merge_clause_correct : forall env v cl cl',
    wf cl -> wf cl' ->
    eval_clause env (cons_lit (POS v) cl) ->
    eval_clause env (cons_lit (NEG v) cl') ->
    eval_clause env (Elim.merge_clause cl cl').
Proof.
  intros.
  unfold wf in *.
  destruct H as (l1 & l2 & EQ).
  destruct H0 as (l1' & l2' & EQ').
  subst.
  unfold Elim.merge_clause.
  rewrite! split_clause_wf.
  rewrite cons_lit_NEG_wf in H2.
  rewrite cons_lit_POS_wf in H1.
  simpl in H2.
  repeat rewrite eval_clause_wf  in *.
  unfold eval_lit in H2. simpl in H2.
  intros.
  rewrite <- map_app.
  rewrite eval_clause_or.
  rewrite eval_or_app.
  rewrite eval_clause_or in *.
  simpl in H1. unfold eval_lit in H1. simpl in H1.
  tauto.
Qed.


Lemma elim_correct : forall env v cls
                              (WF: Forall wf cls),
      eval_cnf env cls ->
      eval_cnf env (Elim.elim v cls).
  Proof.
    unfold Elim.elim.
    intros.
    destruct (Elim.split_polarity v cls) as ((lp,ln),lo) eqn:SP.
    assert (SP':=SP).
    apply split_polarity_ieval with (env:=env) in SP;auto.
    destruct SP as (SP1 & SP2 & SP3).
    apply wf_split_polarity in SP'; auto.
    rewrite eval_cnf_app.
    split ;auto.
    destruct SP' as [WF1 [WF2 WF3]].
    revert ln SP3 WF2.
    induction lp.
    - simpl. auto.
    - simpl.
      intros.
      simpl in SP2.
      rewrite eval_cnf_app.
      intuition.
      clear H2.
      clear H1.
      induction ln.
      + simpl. auto.
      + simpl.
        simpl in SP3.
        assert (wf (Elim.merge_clause a a0)).
        {
          inv WF1. inv WF2.
          apply wf_merge_clause;auto.
        }
        generalize (eval_normalise env _ H1).
        destruct (Elim.normalise (Elim.merge_clause a a0)).
        simpl.
        intros. split.
        rewrite <- H2.
        eapply merge_clause_correct;eauto.
        inv WF1;auto.
        inv WF2;auto.
        tauto.
        apply IHln.
        tauto.
        inv WF2;auto.
        simpl.
        intros. apply IHln;auto.
        tauto. inv WF2;auto.
      +  apply H2;auto.
         inv WF1;auto.
Qed.

  Lemma wf_resolve_all : forall lp ln
                                (WF1 : Forall wf lp)
                                (WF2 : Forall wf ln)
    ,

    Forall wf (Elim.resolve_all lp ln).
Proof.
  induction lp.
  - simpl. constructor.
  - simpl. intros.
    rewrite Forall_app. split; auto.
    assert (Forall wf (map (Elim.merge_clause a) ln)).
    inv WF1.
    induction ln.
    constructor.
    simpl.
    constructor.
    apply wf_merge_clause;auto. inv WF2;auto.
    apply IHln. inv WF2;auto.
    induction  ((map (Elim.merge_clause a) ln)).
    + simpl. constructor.
    + simpl.  inv H.
      destruct (Elim.normalise a0) eqn:N.
      constructor.
      eapply wf_normalise;eauto.
      apply IHl;auto. apply IHl;auto.
    + apply IHlp;auto.
      inv WF1;auto.
Qed.


Lemma wf_elim : forall x cls,
    Forall wf cls ->
    Forall wf (Elim.elim x cls).
Proof.
  unfold Elim.elim.
  intros.
  destruct (Elim.split_polarity x cls) as ((lp,ln),lo) eqn:SP.
  apply wf_split_polarity  in SP; auto.
  rewrite Forall_app.
  split ; try tauto.
  apply wf_resolve_all;tauto.
Qed.


  Lemma eval_clause_classic :
  forall cls i (WF: Forall wf cls),
    (forall env, beval_cnf env cls = true -> boeval env i = true) ->
    (forall env, eval_cnf env cls  -> oeval env i).
Proof.
  intros.
  set (L := vars_of_cnf cls).
  assert (ND := NoDup_nodup hformula_eq_dec L).
  apply has_cardinal_no_dup in ND.
  assert (Lspec :
           forall v, is_var_of_cnf v cls -> In v (nodup hformula_eq_dec L)).
  {
    intros.
    rewrite nodup_In.
    apply vars_of_cnf_ok; auto.
  }
  revert ND H0.
  generalize (length (nodup hformula_eq_dec L)) as n.
  intro.
  unfold L in *.
  clear L. revert Lspec.
  generalize ((nodup hformula_eq_dec (vars_of_cnf cls))) as vars.
  revert cls WF H.
  induction n.
  - intros.
    inv ND.
    simpl in Lspec.
    assert (LspecFalse := is_var_of_cnf_False cls Lspec).
    destruct cls.
    + simpl in H0.
      specialize (H (fun x => false) eq_refl).
      destruct i; simpl in *;discriminate.
    + simpl in H0.
      destruct H0.
      assert (c = nil).
      apply LspecFalse. simpl; tauto.
      subst.
      simpl in H0. tauto.
  - intros.
    inv ND.
    destruct (match_option_dec x i).
    + destruct i ; simpl in *; try tauto.
      subst.
      destruct l.
      * assert (IN : forall v, is_var_of_cnf v cls -> h = v).
      {
        intros.
        apply Lspec in H1. simpl in H1.
        tauto.
      }
      eapply beval_clauses_one_var in H.
      destruct H as (cl & INC & ALLP).
      eapply eval_clauses_all_pos ; eauto.
      intros.
      apply Lspec in H1. simpl in H1. tauto.
      *
        set (E := Elim.elim  h0 cls).
        eapply IHn with (cls:= E) (vars:= (h::l)); auto.
        apply wf_elim;auto.
        {
          rewrite neg_concl with (l:= Some h) in H.
          rewrite neg_concl with (l:= Some h).
          intros.
          apply elim_complete with (env:=env0) (p:= h0) in H.
          tauto.
          rewrite elim_no_vars.
          auto.
          simpl. rewrite is_var_of_cnf_cons.
          rewrite is_var_of_cnf_nil.
          rewrite is_var_of_clause_cons.
          rewrite is_var_of_clause_nil.
          simpl. simpl in H4. intuition congruence.
        }
        {
          intros.
          apply is_var_of_cnf_elim in H1.
          destruct H1.
          apply Lspec in H1.
          simpl in *. intuition congruence.
        }
        { inv H2. constructor;auto. simpl in H4. tauto. }
        { apply elim_correct; auto. }
    +   set (E := Elim.elim x cls).
        eapply IHn with (cls:= E) (vars:= l); auto.
        apply wf_elim;auto.
        {
          intros.
          rewrite neg_concl with (l:= i) in H.
          destruct (boeval env0 i) eqn:EI;auto.
          exfalso.
          apply elim_complete with (env:=env0) (p:= x) in H; auto.
          rewrite elim_no_vars.
          rewrite beval_cnf_app.
          unfold E in H3. rewrite H3.
          rewrite eval_clause_of_opt.
          rewrite EI. reflexivity.
          destruct i; simpl in *.
          rewrite is_var_of_cnf_cons.
          rewrite is_var_of_clause_cons.
          rewrite is_var_of_cnf_nil.
          rewrite is_var_of_clause_nil.
          simpl.  intuition congruence.
          rewrite is_var_of_cnf_nil. tauto.
        }
        {
          intros.
          apply is_var_of_cnf_elim in H3.
          destruct H3.
          apply Lspec in H3.
          simpl in *. intuition congruence.
        }
        { apply elim_correct; auto.
        }
Qed.
