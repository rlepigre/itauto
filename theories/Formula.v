Require Import Cdcl.PatriciaInt.
Require Import Bool ZifyBool Cdcl.ZifyInt ZArith Int63 Lia List.
Import ZifyClasses.

Ltac inv H := inversion H ; try subst ; clear H.
Ltac split_and :=
  repeat
    match goal with
    | |- ?A /\ ?B => split ; split_and
    end.

Lemma and_first : forall A B : Prop,
    A -> (A -> B) -> A /\ B.
Proof.
  tauto.
Qed.

Ltac split_and_first :=
  match goal with
  | |- _ /\ _ => apply and_first ; [| intro ; split_and_first]
  | |- _ => idtac
  end.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Lemma compare_refl : forall i, (i ?= i)%int63 = Eq.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  replace (i < i)%int63 with false by lia.
  replace (i == i)%int63 with true by lia.
  reflexivity.
Qed.

Lemma compare_Eq : forall x y, (x ?= y)%int63 = Eq <-> (x == y = true)%int63.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  destruct (x <y)%int63 eqn:LT; try congruence.
  intuition (congruence || lia).
  destruct (x ==y)%int63 ;   intuition (congruence || lia).
Qed.

Lemma compare_Lt : forall x y, (x ?= y)%int63 = Lt <-> (x < y = true)%int63.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  destruct (x <y)%int63 eqn:LT; try congruence.
  intuition (congruence || lia).
  destruct (x ==y)%int63 ;   intuition (congruence || lia).
Qed.

Lemma compare_Gt : forall x y, (x ?= y)%int63 = Gt <-> (y < x = true)%int63.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  destruct (x <y)%int63 eqn:LT; try congruence.
  intuition (congruence || lia).
  destruct (x ==y)%int63 eqn:EQ;   intuition (congruence || lia).
Qed.

Ltac elim_compare :=
  match goal with
  | H : (?X ?= ?Y)%int63 = Eq |- _ => rewrite compare_Eq in H
  | H : (?X ?= ?Y)%int63 = Lt |- _ => rewrite compare_Lt in H
  | H : (?X ?= ?Y)%int63 = Gt |- _ => rewrite compare_Gt in H
  | |-  (?X ?= ?Y)%int63 = Eq  => rewrite compare_Eq
  | |-  (?X ?= ?Y)%int63 = Lt  => rewrite compare_Lt
  | |-  (?X ?= ?Y)%int63 = Gt  => rewrite compare_Gt
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



Module HCons.
  Section S.
    Variable A: Type.

    Record t : Type :=
      mk {
          id : int;
          is_dec: bool;
          elt: A
        }.


    Lemma dest_eq : forall f,
        mk (id f) (is_dec f) (elt f) = f.
    Proof.
      destruct f ; reflexivity.
    Qed.


  End S.
End HCons.
Import HCons.

Arguments HCons.mk {A} id is_dec elt.
Arguments HCons.elt {A} .
Arguments HCons.id {A} .
Arguments HCons.is_dec {A} .

(*Module OrdInt <: OrderedType.OrderedType.
    Definition t := int.
    Definition eq : t -> t -> Prop := fun x y => Int63.eqb x y = true.
    Definition lt : t -> t -> Prop := fun x y => Int63.ltb x y = true.
    Lemma eq_refl : forall x : t, eq x x.
    Proof.
      intros; unfold eq.
      lia.
    Qed.

    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    Proof.
      unfold eq; intros.
      lia.
    Qed.

    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof.
      unfold eq; intros.
      lia.
    Qed.

    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt. intros.
      lia.
    Qed.

    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof.
      unfold lt,eq. intros.
      lia.
    Qed.

    Lemma compare : forall x y : t, OrderedType.Compare lt eq x y.
    Proof.
      intros.
      destruct (ltb x y) eqn:LTB.
      apply OrderedType.LT ; auto.
      destruct (eqb x y) eqn:EQB.
      apply OrderedType.EQ ; auto.
      apply OrderedType.GT.
      {
        unfold lt.
        lia.
      }
    Defined.

    Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    Proof.
      unfold eq.
      intros.
      destruct (x ==y)%int63.
      left ; auto.
      right. congruence.
    Defined.

End OrdInt.
 *)

Module IntMap  := PatriciaInt.PTrie.

Inductive op :=
| AND | OR | IMPL.

Section S.
  Context {A: Type}.

  Inductive Formula  : Type :=
  | TT  : Formula
  | FF  : Formula
  | AT  : A -> Formula
  | OP  : op -> HCons.t Formula -> HCons.t Formula -> Formula.



  Definition HFormula : Type := HCons.t Formula.

  Section FormInd.

  Fixpoint depth (f:Formula) : nat :=
    match f with
    | TT | FF | AT _ => O
    | OP _ f1 f2 => S (max (depth (HCons.elt f1)) (depth (HCons.elt f2)))
    end.


    Variable P : Formula -> Prop.

    Variable PTT: P TT.
    Variable PFF: P FF.
    Variable PA : forall a, P (AT a).
    Variable Pop : forall f1 f2, P f1.(elt) -> P f2.(elt) -> forall o, P (OP o f1 f2).

    Lemma form_ind : forall f, P f.
    Proof.
      intro f.
      remember (depth f) as n.
      revert f Heqn.
      induction n using Wf_nat.lt_wf_ind.
      destruct n.
      - destruct f ; simpl; auto; discriminate.
      - destruct f; simpl ; try discriminate.
        intros. apply Pop.
        apply (H (depth (elt t0))) ; eauto.
        lia.
        apply (H (depth (elt t1))) ; eauto.
        lia.
    Qed.

  End FormInd.

  Fixpoint aformula (f: Formula) : Formula :=
    match f with
    | TT => TT
    | FF => FF
    | AT a => AT a
    | OP o f1 f2 => OP o (HCons.mk 0%int63 f1.(is_dec) (aformula f1.(elt)))
                       (HCons.mk 0%int63 f2.(is_dec) (aformula f2.(elt)))
    end.

  Open Scope int63.

  Variable atom_eqb : A -> A -> bool.

  Definition op_eqb (o o': op) : bool :=
    match o , o' with
    | AND , AND => true
    | OR  , OR  => true
    | IMPL , IMPL => true
    | _ , _ => false
    end.

  Lemma op_eqb_true : forall o o',
      op_eqb o o' = true -> o = o'.
  Proof.
    destruct o,o' ; simpl ; intuition congruence.
  Qed.

  Definition hmap := @IntMap.t (bool*Formula)%type.



  Section S.

    Variable AT_is_dec : A -> bool.

  Fixpoint chkHc (m: hmap) (f:Formula) (i:int) (b:bool) : bool :=
    match f with
    | FF => (i == 0) && Bool.eqb b true
    | TT => (i == 1) && Bool.eqb b true
    | AT a => match IntMap.get' i m with
             | Some(b',AT a') => atom_eqb a a' && Bool.eqb b (AT_is_dec a) && Bool.eqb b b'
             |  _   => false
             end
    | OP o f1 f2 => chkHc m f1.(elt) f1.(id) f1.(is_dec)
                    && chkHc m f2.(elt) f2.(id) f2.(is_dec) &&
                    match IntMap.get' i m with
                    | Some (b',OP o' f1' f2') =>
                      op_eqb o o' &&
                      (f1.(id) == f1'.(id)) &&
                      (f2.(id) == f2'.(id)) && Bool.eqb b (f1.(is_dec) && f2.(is_dec)) && Bool.eqb b b'
                    | _ => false
                    end
    end.




    Inductive has_form (m:hmap) : HFormula -> Prop :=
    | wf_FF : forall i b, IntMap.get' i m = Some (b,FF) -> has_form m (HCons.mk i b FF)
    | wf_TT : forall i b, IntMap.get' i m = Some (b,TT) -> has_form m (HCons.mk i b TT)
    | wf_AT  : forall a i b, IntMap.get' i m = Some (b,AT a) -> AT_is_dec a = b ->
                             has_form m (HCons.mk i b (AT a))
    | wf_OP : forall o f1 f2 f1' f2' i b,
      has_form m f1 -> has_form m f2 ->
      IntMap.get' i m = Some (b,OP o f1' f2') ->
      f1.(id) = f1'.(id) ->  f2.(id) = f2'.(id)  ->
      b = f1.(is_dec) && f2.(is_dec) ->
      has_form m (HCons.mk i b (OP o f1 f2)).

  Variable atom_eqb_true :
    forall a a', atom_eqb  a a' = true -> a=a'.

  Definition  hFF := HCons.mk 0 true FF.
  Definition  hTT := HCons.mk 1 true TT.

  Record wf (m: IntMap.t (bool * Formula)) : Prop :=
    {
    wf_false : IntMap.get' 0 m = Some (true,FF);
    wf_true : IntMap.get' 1 m = Some (true,TT);
    }.

  Lemma chkHc_has_form : forall m f i b
      (WF: wf m),
      chkHc m f i b = true -> has_form m (HCons.mk i b f).
  Proof.
    intros m f i.
    revert i.
    induction f using form_ind.
    - simpl.
      intros.
      rewrite andb_true_iff in H.
      rewrite eqb_true_iff in H.
      destruct H.
      assert (i = 1) by lia. subst.
      constructor.
      apply wf_true;auto.
    - simpl.
      intros.
      rewrite andb_true_iff in H.
      rewrite eqb_true_iff in H.
      destruct H.
      intros.
      assert (i = 0) by lia. subst.
      constructor.
      apply wf_false;auto.
    - simpl.
      intros.
      destruct (IntMap.get'  i m) eqn:EQ; try congruence.
      destruct p as (b',f).
      destruct f ; try congruence.
      rewrite! andb_true_iff in H.
      rewrite! eqb_true_iff in H.
      destruct H as ((H1, H2),H3).
      subst.
      apply atom_eqb_true in H1. subst.
      econstructor ; eauto.
    - simpl ; intros.
      repeat rewrite andb_true_iff in H.
      destruct H as ((Hf1 & Hf2) & FIND).
      apply IHf in Hf1; auto.
      apply IHf0 in Hf2;auto.
      destruct (IntMap.get'  i m)eqn:FIND2; try congruence.
      destruct p as (b',f).
      destruct f ; try congruence.
      repeat rewrite andb_true_iff in FIND.
      rewrite! eqb_true_iff in FIND.
      destruct FIND as ((((OPEQ,ID1),ID2),B1),B2).
      subst.
      apply op_eqb_true in OPEQ.
      subst.
      rewrite HCons.dest_eq in Hf1.
      rewrite HCons.dest_eq in Hf2.
      econstructor ; eauto.
      lia.
      lia.
  Qed.

  Lemma has_form_eq :
    forall m f1 f2
           (HASF1: has_form m f1)
           (HASF2: has_form m f2)
           (EQ   : f1.(id) = f2.(id)),
      f1 =  f2.
  Proof.
    intros m f1.
    destruct f1 as (i,b,f1).
    revert i b.
    induction f1 using form_ind.
    - intros.
      simpl in EQ.
      subst.
      inv HASF1.
      inv HASF2; simpl in * ; congruence.
    - intros.
      simpl in EQ.
      subst.
      inv HASF1.
      inv HASF2; simpl in * ; congruence.
    - simpl. intros.
      subst.
      inv HASF1.
      inv HASF2; simpl in * ; congruence.
    - simpl in *.
      intros.
      inv HASF1.
      destruct f1 as (i1,b1,f1).
      destruct f2 as (i2,b2, f2).
      simpl in *.
      inv HASF2; simpl in * ; try congruence.
      assert (o = o0) by congruence.
      subst.
      rewrite H6 in H1.
      inv H1.
      symmetry in H2.
      symmetry in H3.
      apply IHf1 with (2:= H) in H4; auto.
      apply IHf0 with (2:= H0) in H5; auto.
      subst. simpl.
      f_equal.
  Qed.

  Variable eval_atom : A -> Prop.


  Definition eval_op (o: op) (f1 f2 : Prop) : Prop :=
    match o with
    | AND => f1 /\ f2
    | OR  => f1 \/ f2
    | IMP => f1 -> f2
    end.

  Fixpoint eval_formula (f: Formula) : Prop :=
    match f with
    | TT => True
    | FF => False
    | AT a => eval_atom a
    | OP o f1 f2 => eval_op o (eval_formula f1.(elt)) (eval_formula f2.(elt))
    end.

  Variable AT_is_dec_correct : forall a,
      AT_is_dec a = true -> eval_atom a \/ ~ eval_atom a.

  Lemma eval_formula_dec : forall m f,
      has_form m f ->
      is_dec f = true ->
      eval_formula f.(elt) \/ ~ eval_formula f.(elt).
  Proof.
    intros m f IND.
    induction IND; simpl.
    - tauto.
    - tauto.
    - intros;  subst. auto.
    - intros.
      subst.
      rewrite andb_true_iff in H3.
      destruct H3.
      apply IHIND1 in H2.
      apply IHIND2 in H3.
      destruct o ; simpl ; tauto.
  Qed.


  Inductive literal : Type :=
  | POS (f:HFormula)
  | NEG (f:HFormula).

  Record watched_clause : Type :=
    {
    watch1 : literal;
    watch2 : literal;
    unwatched : list literal
    }.

  Inductive clause :=
  | EMPTY
  | TRUE
  | UNIT (l:literal)
  | CLAUSE (wc:watched_clause).

    Definition has_literal (m : hmap) (l : literal) :=
    match l with
    | POS f => has_form m f
    | NEG f => has_form m f
    end.

      Definition has_watched_clause (m : hmap) (cl:watched_clause) :=
    Forall (has_literal m) (watch1 cl :: watch2 cl :: unwatched cl).

  Definition has_clause (m:hmap) (cl:clause) :=
    match cl with
    | EMPTY => True
    | TRUE  => True
    | UNIT l => has_literal m l
    | CLAUSE cl => has_watched_clause m cl
    end.

  Definition eval_literal (l:literal) :=
    match l with
    | POS l => eval_formula l.(elt)
    | NEG l => eval_formula l.(elt) -> False
    end.

  Definition eval_literal_rec (l:literal) (P:Prop) :=
    match l with
    | POS l => eval_formula l.(elt) \/ P
    | NEG l => eval_formula l.(elt) -> P
    end.

  Fixpoint eval_literal_list (ls: list literal) :=
    match ls with
    | nil => False
    | l::ls => eval_literal_rec l (eval_literal_list ls)
    end.

  Definition eval_watched_clause (cl: watched_clause) :=
    eval_literal_list (watch1 cl :: watch2 cl :: (unwatched cl)).


  Definition eval_clause  (cl:clause) :=
    match cl with
    | EMPTY => False
    | TRUE  => True
    | UNIT l => eval_literal l
    | CLAUSE cl => eval_watched_clause cl
    end.


  Definition watch_map_elt := (IntMap.t watched_clause * IntMap.t watched_clause )%type.

  Definition watch_map := IntMap.t watch_map_elt.

  Definition empty_watch_map  := IntMap.empty watch_map_elt.


  Record state : Type :=
    mkstate {
        fresh_clause_id : int;
        hconsmap : hmap;
        (* Formulae of the form a -> b need a special processing *)
        arrows : list literal;
        (* Formulae which cnf has been already unfold *)
        defs : IntMap.t unit * IntMap.t unit ;
        units : IntMap.t bool;
        unit_stack : list literal;
        (* unit_list is a stack of unit clauses to be processed *)
        clauses : watch_map
       (* An entry clause(v) returns the set of clauses starting by v.
        *);
      }.

  Definition empty_state m :=
    {|
    fresh_clause_id := 0;
    hconsmap := m;
    arrows := nil;
    defs := (IntMap.empty unit , IntMap.empty unit);
    units := IntMap.empty bool;
    unit_stack := nil;
    clauses := empty_watch_map
    |}.


  Definition find_clauses (v:int) (cls : watch_map) :=
    match IntMap.get' v cls with
    | None => (IntMap.empty watched_clause,IntMap.empty watched_clause)
    | Some r => r
    end.

    Definition form_of_literal (l: literal) : HFormula :=
    match l with
    | POS f => f
    | NEG f => f
    end.

  Definition id_of_literal (l:literal) : int :=
    (form_of_literal l).(id).


  Definition is_positive_literal (l:literal) : bool :=
    match l with
    | POS _ => true
    | NEG _ => false
    end.

  Definition add_clause (l:literal) (clause_id: int) (cl: watched_clause) (cls : watch_map) :=
    let lid := id_of_literal l in
    let (ln,lp) := find_clauses (id_of_literal l) cls in
    if is_positive_literal l
    then IntMap.set' lid (ln,IntMap.set' clause_id cl lp) cls
    else IntMap.set' lid (IntMap.set' clause_id cl ln,lp) cls
  .


  Definition is_impl (o: op) : bool :=
    match o with
    | IMPL => true
    | _    => false
    end.


  Definition is_arrow (f:Formula) : bool :=
    match f with
    | OP IMPL f1 f2 => true
    | _             => false
    end.

  Definition is_arrow_lit (l: literal) : bool :=
    match l with
    | POS f | NEG f => is_arrow f.(elt)
    end.


  Definition insert_unit (l:literal) (st:state) : state :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs   := defs st;
    arrows :=  arrows st;
    units := units st;
    unit_stack := l:: unit_stack st;
    clauses := clauses st
    |}.

  Definition insert_lit_clause (l:literal) (clause_id: int) (cl: watched_clause) (st : state) : state :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs   := defs st;
    arrows := arrows st ;
    units := units st;
    unit_stack := unit_stack st;
    clauses := add_clause l clause_id cl (clauses st)
    |}.




  Definition is_cons (id: int) (l : IntMap.t unit) :=
    match IntMap.get' id l with
    | Some _ => true
    | _ => false
    end.

  Definition set_cons (id:int) (l: IntMap.t unit) := IntMap.set' id tt l.

  Lemma Forall_rew : forall {T: Type} (P: T -> Prop) (l : list T),
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

  Definition literal_of_bool (b:bool) (f:HFormula) :=
    if b then POS f else NEG f.

  (** Plaisted & Greenbaum cnf
      cnf+ f generate clauses to build f from sub-formulae (ways to deduce f)
      cnf- f generate clauses to deduce sub-formulae from f
   *)
  Definition cnf_plus_and (f1:HFormula) (f2:HFormula) (f:HFormula) (rst: list watched_clause) :=
    {|
    watch1 := NEG f1 ;
    watch2 := NEG f2 ;
    unwatched := POS f :: nil|} :: rst.

  Definition  cnf_plus_or (f1 f2: HFormula) (f: HFormula) (rst: list watched_clause) :=
    {|
    watch1 := NEG f1 ;
    watch2 := POS f;
    unwatched := nil
    |} ::
    {|
    watch1 := NEG f2 ;
    watch2 := POS f;
    unwatched := nil
    |} :: rst.

  (* This one is incomplete
     - should take into account the conclusion! *)
  Definition cnf_plus_impl (is_classic: bool) (f1 f2: HFormula) (f: HFormula) (rst: list watched_clause) :=
    if is_classic
    then
      {| watch1 := POS f1 ;
         watch2 := POS f;
         unwatched := nil
      |} :: {| watch1 := NEG f2;
               watch2 := POS f;
               unwatched:= nil
            |} :: rst
    else
    {|
    watch1 := NEG f2;
    watch2 := POS f;
    unwatched := nil
    |} :: rst.

  Definition cnf_minus_and (f1:HFormula) (f2:HFormula) (f:HFormula) (rst: list watched_clause) :=
    {|
    watch1 := NEG f ;
    watch2 := POS f1 ;
    unwatched := nil|} ::
    {|
    watch1 := NEG f ;
    watch2 := POS f2 ;
    unwatched := nil|} :: rst.

  Definition cnf_minus_or (f1:HFormula) (f2:HFormula) (f:HFormula) (rst: list watched_clause) :=
    {|
    watch1 := NEG f ;
    watch2 := POS f1 ;
    unwatched := POS f2::nil|} :: rst.

  Definition cnf_minus_impl (f1:HFormula) (f2:HFormula) (f:HFormula) (rst: list watched_clause) :=
    {| watch1 := NEG f;
       watch2 := NEG f1;
       unwatched := POS f2::nil
    |}::rst.

  Definition cnf_of_op_plus (is_classic: bool) (o:op) :=
    match o with
    | AND => cnf_plus_and
    | OR  => cnf_plus_or
    | IMPL => cnf_plus_impl is_classic
    end.

  Definition cnf_of_op_minus (is_classic: bool) (o:op) :=
    match o with
    | AND => cnf_minus_and
    | OR  => cnf_minus_or
    | IMPL => cnf_minus_impl
    end.

  Definition polarity_of_op_1 (o: op) (b:bool):=
    match o with
    | AND => b
    | OR  => b
    | IMPL => negb b
    end.

  Fixpoint cnf (pol:bool) (is_classic: bool) (cp cm: IntMap.t unit)
           (ar:list literal) (acc : list watched_clause)   (f: Formula) (hf: HFormula) :
    IntMap.t unit * IntMap.t unit * list literal * list watched_clause
    :=
    let h := hf.(id) in
    if is_cons h (if pol then cp else cm) then (cp,cm,ar,acc)
    else
      match f with
      | FF | TT | AT _ => (cp,cm,ar,acc)
      | OP op f1 f2 =>
        let acc := (if pol then cnf_of_op_plus else cnf_of_op_minus) is_classic op f1 f2 hf acc in
        let cp  := if pol then set_cons h cp else cp in
        let cm  := if pol then cm else set_cons h cm in
        let ar  := if is_impl op && negb is_classic && pol then POS hf::ar else ar in
        let '(cp,cm,ar,acc) := cnf (polarity_of_op_1 op pol) is_classic cp cm ar acc f1.(elt) f1 in
        cnf pol is_classic cp cm ar acc f2.(elt) f2
      end.

  Definition eval_hformula (f: HFormula) := eval_formula f.(elt).


  Definition eval_ohformula (o : option HFormula) : Prop :=
    match o with
    | None => False
    | Some f => eval_hformula f
    end.

  Definition is_classic (concl: option HFormula) :=
    match concl with
    | None => true
    | _    => false
    end.

  Lemma cnf_of_op_plus_correct :
        forall acc g o f1 f2 hf
               (EQ : hf.(elt) = OP o f1 f2)
               (ACC : (Forall eval_watched_clause acc -> eval_ohformula g)
                      -> eval_ohformula g),
               (Forall eval_watched_clause (cnf_of_op_plus (is_classic g) o f1 f2 hf acc) ->  eval_ohformula g) -> eval_ohformula g.
      Proof.
        destruct o ; simpl.
        - intros. apply ACC.
          intro. apply H.
          unfold cnf_plus_and.
          repeat constructor; auto.
          rewrite EQ. simpl. split ; assumption.
        - intros. apply ACC.
          intro. apply H.
          unfold cnf_plus_or.
          repeat constructor; auto.
          rewrite EQ. simpl. left ; auto.
          rewrite EQ. simpl. right ; auto.
        - destruct g ; simpl.
          + intros. apply ACC.
          intro. apply H.
          unfold cnf_plus_impl.
          repeat constructor; auto.
          rewrite EQ. simpl. intro ; assumption.
          +
            intros.
            rewrite Forall_rew in H.
            rewrite Forall_rew in H.
            unfold eval_watched_clause at 1 2 in H.
            simpl in H.
            rewrite EQ in H.
            simpl in H. tauto.
      Qed.

      Lemma cnf_of_op_minus_correct :
        forall acc g o f1 f2 hf
               (EQ : hf.(elt) = OP o f1 f2)
               (ACC : (Forall eval_watched_clause acc -> eval_ohformula g)
                      -> eval_ohformula g),
               (Forall eval_watched_clause (cnf_of_op_minus (is_classic g) o f1 f2 hf acc) ->  eval_ohformula g) -> eval_ohformula g.
      Proof.
        intros.
        apply ACC.
        intros. apply H.
        clear ACC H.
        destruct o ; simpl.
        -
          repeat constructor; auto.
          rewrite EQ in H. simpl in H. destruct H ; assumption.
          rewrite EQ in H. simpl in H. destruct H ; assumption.
        - unfold cnf_minus_or.
          constructor. unfold eval_watched_clause. simpl.
          rewrite EQ. simpl. tauto.
          auto.
        - unfold cnf_minus_impl.
          constructor; auto.
          unfold eval_watched_clause. simpl.
          rewrite EQ. simpl. tauto.
      Qed.


      Lemma cnf_correct :
        forall f pol g cp cm ar acc hf
               (EQ: hf.(elt) = f)
               (ACC1 : (Forall eval_watched_clause acc -> eval_ohformula g)
                       -> eval_ohformula g)
               (CNF  : Forall eval_watched_clause
                              (snd (cnf pol (is_classic g) cp cm ar acc f hf)) ->
                       eval_ohformula g),
          eval_ohformula g.
  Proof.
    induction f using form_ind.
    - simpl; intros.
      destruct (is_cons (id hf) (if pol then cp else cm)); simpl in CNF; tauto.
    - simpl; intros.
      destruct (is_cons (id hf) (if pol then cp else cm)); simpl in CNF; tauto.
    - simpl; intros.
      destruct (is_cons (id hf) (if pol then cp else cm)); simpl in CNF; tauto.
    - simpl; intros.
      destruct (is_cons (id hf) (if pol then cp else cm)).
      + simpl in CNF ; tauto.
      +
        revert CNF.
        generalize (if pol then set_cons (id hf) cp else cp) as cp'.
        generalize (if pol then cm else set_cons (id hf) cm) as cm'.
        set (acc':= ((if pol then cnf_of_op_plus else cnf_of_op_minus)
               (is_classic g) o f1 f2 hf acc)).
        set (ar' := (if
              is_impl o && negb (is_classic g) &&
               pol
             then POS hf :: ar
             else ar)).
        intros cm' cp'.
        destruct (cnf
                    (polarity_of_op_1 o pol)
                    (is_classic g) cp' cm' ar' acc' (elt f1) f1) as
            (((cp1,cm1),ar1),acc1) eqn:EQPf1.
        apply IHf0; auto.
        change acc1 with (snd (cp1,cm1,ar1,acc1)).
        rewrite <- EQPf1.
        apply IHf; auto.
        unfold acc'.
        destruct pol.
        apply cnf_of_op_plus_correct; auto.
        apply cnf_of_op_minus_correct; auto.
  Qed.

  Definition insert_defs (m : IntMap.t unit * IntMap.t unit) (ar : list literal) (st : state ) :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs := m;
    arrows := ar;
    units  := units st;
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.

  Definition reset_arrows (ar : list literal) (st: state) :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs := defs st;
    arrows := ar;
    units  := units st;
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.


  Definition neg_bool (o : option bool) : option bool :=
    match o with
    | None => None
    | Some b => Some (negb b)
    end.

  Definition find_lit (l: literal) (lit: IntMap.t bool) : option bool :=
    match l with
    | POS l => IntMap.get' l.(id) lit
    | NEG l => neg_bool (IntMap.get' l.(id) lit)
    end.

  Definition find_lit' (l: literal) (lit : IntMap.t bool)  : option bool :=
    (if is_positive_literal l then (fun x => x) else neg_bool)
      (IntMap.get' (id_of_literal l) lit).

  Lemma find_lit_eq : forall l lit,
      find_lit l lit = find_lit' l lit.
  Proof.
    unfold find_lit,find_lit'.
    destruct l ; simpl.
    - reflexivity.
    - reflexivity.
  Qed.

  Fixpoint make_watched (lit: IntMap.t bool) (w:literal)  (cl : list literal) :=
    match cl with
    | nil => UNIT w
    | e::l => match find_lit e lit with
              | None => CLAUSE {| watch1 := w ; watch2 := e ; unwatched := l |}
              | Some true => TRUE
              | Some false => make_watched lit w l
              end
    end.

  Fixpoint reduce (lit: IntMap.t bool) (cl : list literal) :=
    match cl with
    | nil => Some nil
    | e::cl => match find_lit e lit with
              | None => match reduce lit cl with
                        | None => None
                        | Some l' => Some (e::l')
                        end
              | Some true => None
              | Some false => reduce lit cl
              end
    end.

  
  (** Either one or the other watched literal is set (not both) *)
  Definition shorten_clause (lit : IntMap.t bool) (cl : watched_clause) :=
    match find_lit (watch1 cl) lit with
    | None => match find_lit (watch2 cl) lit with
              | None => (* Should not happen *) CLAUSE cl
              | Some true  => TRUE
              | Some false => make_watched lit (watch1 cl) (unwatched cl)
              end
    | Some true => TRUE
    | Some false => make_watched lit (watch2 cl) (unwatched cl)
    end.

  Definition add_watched_clause  (st : state) (id: int) (cl: watched_clause) : state :=
    let w1 := watch1 cl in
    let w2 := watch2 cl in
    let mcl := clauses st in
    let mcl := add_clause w1 id cl mcl in
    let mcl := add_clause w2 id cl mcl in
    {|
      fresh_clause_id := fresh_clause_id st;
      hconsmap := hconsmap st;
      arrows := arrows st;
      defs   := defs st ;
      units  := units st;
      unit_stack := unit_stack st;
      clauses := mcl
    |}.

  Definition get_fresh_clause_id (st:state) : int * state :=
    let res := fresh_clause_id st in
    (res,{|
       fresh_clause_id := res + 1;
       hconsmap := hconsmap st;
       arrows := arrows st;
      defs := defs st;
      units := units st;
      unit_stack :=unit_stack st;
      clauses := clauses st
    |}).

  Definition insert_normalised_clause (id: int) (cl:clause) (st: state)  : option state :=
    match  cl with
    | EMPTY => None
    | UNIT l => Some (insert_unit l st)
    | TRUE   => Some st
    | CLAUSE cl =>Some (add_watched_clause st id cl)
    end.

  Definition insert_watched_clause (id: int) (cl: watched_clause) (st: state)  : option state :=
    insert_normalised_clause id (shorten_clause (units st) cl) st .

  Definition insert_fresh_watched_clause (cl:watched_clause) (st: state) :=
    let (fr,st') := get_fresh_clause_id st in
    insert_watched_clause fr cl st'.


  Definition insert_clause (id: int) (cl:clause) (st: state)  : option state :=
    match cl with
    | EMPTY => None
    | UNIT l => Some (insert_unit l st)
    | CLAUSE cl => insert_watched_clause id  cl st
    | TRUE => Some st
    end.

  Definition insert_fresh_clause (cl:clause) (st: state) :=
    let (fr,st') := get_fresh_clause_id st in
    insert_clause fr cl st'.


  Fixpoint fold_update {A: Type} (F : A -> state -> option state) (l: list A) (st:state)  : option state :=
    match l with
    | nil => Some st
    | e::l => match F e st with
              | None => None
              | Some st' => fold_update F  l st'
              end
    end.

  Fixpoint app_list (l: list (state -> option state)) (st: state) :=
    match l with
    | nil => Some st
    | f1::fl => match f1 st with
                | None => None
                | Some st' => app_list fl st'
                end
    end.

  Fixpoint intro_impl (acc: list literal) (f: Formula) (hf: HFormula) :=
    match f with
    | TT => (acc, Some hf)
    | FF => (acc, None)
    | AT a => if hf.(is_dec) then  ((NEG hf) :: acc , None)
              else  (acc , Some hf)
    | OP o f1 f2 => if is_impl o then intro_impl (POS f1::acc) f2.(elt) f2
                    else if hf.(is_dec) then (NEG hf::acc, None)
                         else (acc, Some hf)
    end.

  Definition cnf_of_literal (l:literal) := cnf  (negb (is_positive_literal l)).

  Definition augment_cnf (is_classic: bool) (h: literal) (st: state) :=
      let f := form_of_literal h in
      let '(cp,cm,ar,acc) := (cnf_of_literal h) is_classic (fst (defs st)) (snd (defs st)) (arrows st) nil f.(elt) f in
      fold_update insert_fresh_watched_clause  acc (insert_defs (cp,cm) ar  st).

  Definition augment_hyp (is_classic: bool) (h: literal) (st:state) :=
    augment_cnf is_classic h (insert_unit h st).

  Definition cnf_hyps (is_classic: bool) (l: list literal) (st: state) :=
    fold_update (augment_hyp is_classic) l st.



  Definition intro_state (st:state) (f: Formula) (hf: HFormula) :=
    let (hs,c) := intro_impl nil f hf in
    match cnf_hyps (is_classic c) hs st with
    | None => None
    | Some st =>
      match c with
      | None => Some(st,None)
      | Some g => match augment_cnf false (NEG g) st with
                  | None => None
                  | Some st' => Some(st',Some g)
                  end
      end
    end.


  Lemma neg_bool_some : forall o b,
      neg_bool o = Some b ->
      o = Some (negb b).
  Proof.
    destruct o ; simpl ; try congruence.
    intros. inv H.
    rewrite negb_involutive. reflexivity.
  Qed.




  Definition remove_clauses (l:literal) (st: state) : state :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs   := defs st;
    arrows := arrows st;
    units := units st;
    unit_stack := unit_stack st;
    clauses := IntMap.remove' (id_of_literal l) (clauses st)
    |}.


  Definition add_literal (l:literal) (lit : IntMap.t bool) :=
    IntMap.set' (id_of_literal l) (is_positive_literal l) lit.


  Definition is_neg_arrow (l:literal) : bool :=
    match l with
    | POS _ => false
    | NEG f => is_arrow f.(elt)
    end.



  Definition insert_literal (l:literal) (st: state) : state :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs := defs st;
    arrows := if is_neg_arrow l then (l::arrows st) else arrows st;
    units := add_literal l (units st);
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.


 Definition is_FF (g: Formula) : bool :=
    match g with
    | FF => true
    | _  => false
    end.

  Definition is_TT (g: Formula) : bool :=
    match g with
    | TT => true
    | _  => false
    end.



  Definition is_hFF (g: HFormula) :=
    (g.(id) == 0) && Bool.eqb g.(is_dec) true && is_FF g.(elt).


  Definition is_unsat (lit: IntMap.t bool) (l:literal) : bool  :=
    match l with
    | POS l => if is_hFF l then true
               else
                 match IntMap.get' l.(id) lit with
                 | Some false => true
                 |  _         => false
                 end
    | NEG l => match IntMap.get' l.(id) lit with
               | Some true => true
               | _         => false
               end
    end.

  Definition is_goal (goal : HFormula) (l:literal) : bool :=
    match l with
    | POS f => f.(id) == goal.(id)
    | NEG _ => false
    end.

  Definition success (goal: option HFormula) (lit: IntMap.t bool) (l:literal) :=
    match goal with
    | None => is_unsat lit l
    | Some g => if is_goal g l
                then true else is_unsat lit l
    end.


  Definition set_unit_stack (l : list literal) (st : state) :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs := defs st;
    arrows := arrows st ;
    units := units st;
    unit_stack := l;
    clauses := clauses st |}.

  Definition add_arrow (l: literal) (st:state) :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs := defs st;
    arrows := l:: arrows st ;
    units := units st;
    unit_stack := unit_stack st;
    clauses := clauses st |}.


  Definition extract_unit (st:state) :=
    match unit_stack st with
    | nil => None
    | e::us => Some(e , set_unit_stack us st)
    end.

  Inductive ptree (A:Type) :=
  | Leaf  (b:bool)
  | Deriv (sq : A) (l: list (ptree A)).

  Arguments Leaf {A}.
  Arguments Deriv {A}.

  Inductive status (A:Type):=
  | HasProof (p: A)
  | HasModel (f: A)
  | Timeout (p:  A)
  | Done    (st: state).

  Arguments HasProof {A}.
  Arguments HasModel {A}.
  Arguments Timeout {A}.
  Arguments Done {A}.

  Inductive result :=
  | OutOfFuel
  | Success
  | Progress (st : state).

  Definition remove_watched_id (l:literal) (id:int) (cl: watch_map) :=
    let lid := id_of_literal l in
    let (ln,lp) := find_clauses lid cl in
    if is_positive_literal l
    then IntMap.set' lid (ln, IntMap.remove' id lp) cl
    else IntMap.set' lid (IntMap.remove' id ln,lp) cl.

  Definition remove_watched_clause (id:int) (cl:watched_clause) (st: state) :=
    let cls := remove_watched_id (watch2 cl) id (remove_watched_id (watch1 cl) id (clauses st)) in
    {|
      fresh_clause_id := fresh_clause_id st;
      hconsmap := hconsmap st;
      arrows := arrows st;
      defs := defs st;
      units := units st;
      unit_stack := unit_stack st;
      clauses := cls
    |}.


  Definition update_watched_clause (st:option state) (id : int) (cl: watched_clause)  : option state :=
    match st with
    | None => None
    | Some st => insert_watched_clause id cl (remove_watched_clause id cl st)
    end.

  Definition shorten_clauses (cl : IntMap.t watched_clause) (st:state) :=
    IntMap.fold' update_watched_clause cl (Some st).

  
  Fixpoint unit_propagation (n:nat) (st: state) (concl: option HFormula) : result :=
    match n with
    | O => OutOfFuel
    | S n =>
      match extract_unit st with
      | None => Progress st
      | Some(l,st) =>
        if success concl (units st) l
        then Success
        else
          let st := insert_literal l st in
          let (ln,lp) := find_clauses (id_of_literal l) (clauses st) in
          let lc := match l with
                    | POS _ => ln
                    | NEG _ => lp end in
          match shorten_clauses lc st with
          | None => Success
          | Some st => unit_propagation n st concl
          end
      end
    end.

  Lemma unit_propagation_rew : forall (n:nat) (st: state) (concl: option HFormula),
      unit_propagation n st concl =
    match n with
    | O => OutOfFuel
    | S n =>
      match extract_unit st with
      | None => Progress st
      | Some(l,st) =>
        if success concl (units st) l
        then Success
        else
          let st := insert_literal l st in
          let (ln,lp) := find_clauses (id_of_literal l) (clauses st) in
          let lc := match l with
                    | POS _ => ln
                    | NEG _ => lp end in
          match shorten_clauses lc st with
          | None => Success
          | Some st => unit_propagation n st concl
          end
      end
    end.
  Proof. destruct n ; reflexivity. Qed.


  Definition eval_units (m : hmap) (u : IntMap.t bool) :=
    forall b f,
      IntMap.get' (f.(id)) u = Some b ->
      has_form m f ->
      eval_literal (literal_of_bool b f).

  Definition eval_stack (lst : list literal) : Prop :=
    List.Forall eval_literal lst.

  Definition IntMapForall {A:Type} (P: A -> Prop) (m: IntMap.t A) :=
    forall k r, IntMap.get' k m = Some r -> P r.

  Definition IntMapForall2 {A: Type} (P: A -> Prop) (m: IntMap.t A* IntMap.t A) :=
    IntMapForall P (fst m) /\ IntMapForall P (snd m).

  Lemma empty_o : forall {T:Type} k,
      IntMap.get' k (IntMap.empty T) = None.
  Proof.
    reflexivity.
  Qed.

  Lemma IntMapForallEmpty : forall {A: Type} {P: A -> Prop},
      IntMapForall P (IntMap.empty A).
  Proof.
    unfold IntMapForall.
    intros.
    rewrite empty_o in H.
    congruence.
  Qed.

  Definition wf_map  {A: Type} (m : IntMap.t A) := PTrie.wf None m.

  Lemma grspec : forall {A:Type} i j (m: IntMap.t A)
                          (WF: wf_map m),
      IntMap.get' i (IntMap.remove' j m) =
      if eqs i j then None else IntMap.get' i m.
  Proof.
    intros.
    destruct (eqs i j).
    - subst. eapply  IntMap.grs'; eauto.
    - eapply IntMap.gro'; eauto.
  Qed.

  Theorem gsspec:
    forall (A: Type) (i j: int) (x: A) (m: IntMap.t A)
           (WF : wf_map m),
      IntMap.get' i (IntMap.set' j x m) = if eqs i j then Some x else IntMap.get' i m.
  Proof.
    intros; destruct (eqs i j).
    - subst i; eapply IntMap.gss'; eauto.
    - eapply IntMap.gso'; eauto.
  Qed.



  Lemma IntMapForallRemove : forall {A:Type} (P: A -> Prop) m x
                                    (WF: wf_map m),
      IntMapForall P m ->
      IntMapForall P (IntMap.remove' x m).
  Proof.
    intros.
    repeat intro.
    rewrite grspec in H0; auto.
    destruct (eqs k x); try discriminate.
    eapply H  ;eauto.
  Qed.


  Lemma IntMapForallAdd : forall {A:Type} (P: A -> Prop) m i v
                                 (WF: wf_map m),
      IntMapForall P m ->
      P v ->
      IntMapForall P (IntMap.set' i v m).
  Proof.
    unfold IntMapForall.
    repeat intro.
    rewrite gsspec in H1;auto.
    destruct (eqs k i); auto.
    inv H1. auto.
    eapply H ; eauto.
  Qed.

  Lemma wf_map_add : forall  {A: Type} x v (cls : IntMap.t A)
                             (WF : wf_map cls),
      wf_map (IntMap.set' x v cls).
  Proof.
    intros.
    eapply IntMap.wf_set'; eauto.
    constructor.
  Qed.

  Hint Resolve wf_map_add.

  Definition eval_clauses  (h : watch_map) :=
    IntMapForall (IntMapForall2 eval_watched_clause) h.

  Definition order_map ( m m' : IntMap.t Formula) : Prop :=
    forall i f, IntMap.get' i m = Some f -> IntMap.get' i m' = Some f.

  Definition order_dom {A B:Type} (m : IntMap.t A) (m': IntMap.t B) : Prop :=
    forall i, IntMap.get' i m <> None -> IntMap.get' i m' <> None.

  Definition has_clauses (m : hmap) (cl : watch_map) :=
    IntMapForall (IntMapForall2 (has_watched_clause m)) cl.

  Definition wf_watch_map (m : watch_map) :=
    IntMapForall (fun x => wf_map (fst x) /\ wf_map (snd x)) m.

  Record wf_state (m:hmap) (st : state) : Prop :=
    {
    wf_arrows  : List.Forall (has_literal m) (arrows st) ;
    wf_units : order_dom (units st) m;
    wf_stack : List.Forall (has_literal  m) (unit_stack st);
    wf_clauses : has_clauses  m (clauses st);
    wf_units_m : wf_map (units st);
    wf_clauses_m1 :  wf_map (clauses st);
    wf_clauses_m2 : wf_watch_map (clauses st)
    }.

  Definition wf_csqo (m:hmap) (o:option HFormula) :=
    match o with
    | None => True
    | Some f => has_form m f
    end.



  Record eval_state (m: hmap) (st: state) : Prop :=
    {
    ev_units : eval_units m (units st) ;
    ev_stack : eval_stack (unit_stack st) ;
    ev_clauses :  eval_clauses (clauses st)
    }.


  Definition has_oform (m: hmap) (o : option HFormula) : Prop :=
    match o with
    | None => True
    | Some f => has_form m f
    end.


  Lemma get_unit_eval_state :
    forall m st l st',
      eval_state m st ->
      extract_unit st = Some (l,st') ->
      eval_literal l /\ eval_state m st'.
  Proof.
    unfold extract_unit.
    intros.
    destruct (unit_stack st) eqn:EQ; try congruence.
    inv H0.
    destruct H.
    rewrite EQ in ev_stack0.
    unfold eval_stack in ev_stack0.
    inv ev_stack0.
    split ; auto.
    constructor; simpl ; auto.
  Qed.

  Lemma has_form_find_lit :
    forall m f lit
           (HL : has_form m f)
           (EU : eval_units m lit),
      match IntMap.get' (id f) lit with
      | None => True
      | Some b => eval_literal (literal_of_bool b f)
      end.
  Proof.
    intros.
    unfold eval_units in EU.
    destruct (IntMap.get'  (id f) lit) eqn:EQ; auto.
  Qed.

  Lemma is_hFF_true : forall g, is_hFF g = true -> g = hFF.
  Proof.
    unfold is_hFF.
    destruct g ; simpl.
    intros. unfold hFF.
    repeat rewrite andb_true_iff in H.
    destruct H as ((H1 & H2) & H3).
    rewrite eqb_true_iff in H2.
    subst.
    assert (id0 = 0) by lia.
    destruct elt0 ; simpl in H3 ; try congruence.
  Qed.


  Lemma is_unsat_correct :
    forall m lit l
           (HL : has_literal m l)
           (EL : eval_literal l)
           (EU : eval_units m lit)
           (US : is_unsat lit l = true),
      False.
  Proof.
    unfold is_unsat.
    destruct l.
    - simpl.
      intros.
      destruct (is_hFF f) eqn:FF.
      apply is_hFF_true in FF. subst.
      simpl in EL ; auto.
      generalize (has_form_find_lit _ _ _ HL EU).
      destruct (IntMap.get' (id f) lit); auto.
      destruct b ; try congruence.
      congruence.
    - simpl; intros.
      generalize (has_form_find_lit _ _ _ HL EU).
      destruct (IntMap.get' (id f) lit); auto.
      destruct b ; try congruence.
      simpl. auto.
      congruence.
  Qed.

  Lemma success_correct :
    forall m g u l
           (HASG : has_oform m g)
           (WFL  : has_literal m l)
           (WFU  : order_dom u m)
           (SUC  : success g u l = true)
           (EU   : eval_units m u)
           (EL   : eval_literal l),
      eval_ohformula g.
  Proof.
    intros.
    unfold success in *.
    destruct g; simpl.
    destruct (is_goal h l) eqn:G.
    - simpl in HASG.
      destruct l ; simpl in G ; try discriminate.
      assert (G' : id f = id h) by lia.
      apply has_form_eq with (m:=m) in G';auto.
      subst; auto.
    - exfalso ; eapply is_unsat_correct ; eauto.
    - exfalso ; eapply is_unsat_correct ; eauto.
  Qed.

  Lemma get_unit_wf : forall m st l st',
      wf_state m st ->
      extract_unit st = Some (l, st') ->
      wf_state m st' /\ has_literal m l.
  Proof.
    intros.
    unfold extract_unit in H0.
    destruct H.
    destruct (unit_stack st) eqn:EQ; try discriminate.
    inv H0.
    inv wf_stack0.
    split ; try constructor ; auto.
  Qed.

  Lemma wf_insert_unit :
    forall m l st
           (WF : wf_state m st)
           (WFL: has_literal m l),
      wf_state m (insert_unit l st).
  Proof.
    unfold insert_unit.
    intros.
    destruct WF ; constructor ; simpl ; auto.
  Qed.

  Lemma eval_insert_unit :
    forall m l st
           (WF : wf_state m st)
           (ES : eval_state m st)
           (EL : eval_literal l),
      eval_state m (insert_unit l st).
  Proof.
    unfold insert_unit.
    intros.
    destruct ES ; constructor ; simpl ; auto.
    constructor;auto.
  Qed.

  Lemma wf_remove_clauses :
    forall m l st
           (WF : wf_state m st),
      wf_state m (remove_clauses l st).
  Proof.
    intros.
    destruct WF ; constructor ; simpl ; auto.
    unfold has_clauses in *.
    apply IntMapForallRemove; auto.
    apply IntMap.wf_remove'; auto.
    unfold wf_watch_map in *.
    unfold IntMapForall in *.
    intros.
    rewrite grspec in H; auto.
    destruct (eqs k (id_of_literal l)); try congruence.
    eauto.
  Qed.

  Lemma eval_remove_clauses :
    forall m l st
           (WF : wf_state m st)
           (ES : eval_state m st),
      eval_state m (remove_clauses l st).
  Proof.
    intros.
    destruct ES ; constructor ; simpl ; auto.
    unfold eval_clauses in * ; intros.
    apply IntMapForallRemove;auto.
    destruct WF ; auto.
  Qed.

  Lemma eval_find_clauses :
    forall i cl ln lp
           (EC : eval_clauses  cl)
           (FD : find_clauses i cl = (ln, lp)),
      IntMapForall eval_watched_clause ln /\
      IntMapForall eval_watched_clause lp.
  Proof.
    unfold eval_clauses, find_clauses.
    intros.
    destruct (IntMap.get'  i cl) eqn:EQ.
    -  destruct w. inv FD.
       apply EC in EQ; auto.
    - inv FD.
      split ; apply IntMapForallEmpty.
  Qed.

  Definition neg_literal (l: literal) :=
    match l with
    | POS h => NEG h
    | NEG h => POS h
    end.

    Lemma literal_eq : forall l,
      literal_of_bool (is_positive_literal l) (form_of_literal l) = l.
  Proof.
    destruct l ; simpl ; auto.
  Qed.

  Lemma has_form_of_literal : forall m l,
      has_literal m l ->
      has_form m (form_of_literal l).
  Proof.
    destruct l ; simpl in *; auto.
  Qed.

  Lemma eval_units_find_lit :
    forall m h u b
           (EV : eval_units m u)
           (HAS : has_literal m h)
           (FD : find_lit h u = Some b),
      (if b then eval_literal h else
         eval_literal (neg_literal h)).
  Proof.
    unfold eval_units ; intros.
    rewrite find_lit_eq in FD.
    unfold find_lit' in FD.
    assert (FL := has_form_of_literal m h HAS).
    destruct (is_positive_literal h) eqn:POS.
    - apply EV in FD ; auto.
      destruct b ; simpl in * ; auto.
      destruct h ; simpl in * ; try congruence.
      destruct h ; simpl in * ; try congruence.
    - apply neg_bool_some in FD.
      apply EV in FD ; auto.
      destruct b ; simpl in * ; auto.
      destruct h ; simpl in * ; try congruence.
      destruct h ; simpl in * ; try congruence.
  Qed.

  Lemma eval_neg_literal : forall h,
      eval_literal (neg_literal h) -> ~ eval_literal h.
  Proof.
    destruct h ; simpl ; auto.
  Qed.



  Lemma has_clause_make_watched :
    forall m u w cl
           (HASL : has_literal m w)
           (HASL : Forall (has_literal m) cl),
           has_clause m (make_watched u w cl).
  Proof.
    induction cl; simpl.
    - auto.
    - intros.
      inv HASL0.
      destruct (find_lit a u).
      destruct b ; auto.
      simpl ; auto.
      simpl. unfold has_watched_clause ; auto.
  Qed.

  Lemma wf_shorten_clause :
    forall m u cl
           (WFC : has_watched_clause m cl),
      has_clause m (shorten_clause u cl).
  Proof.
    intros.
    unfold shorten_clause.
    unfold has_watched_clause in WFC.
    inv WFC. inv H2.
    destruct (find_lit (watch1 cl) u).
    - destruct b ; simpl ; auto.
      apply has_clause_make_watched; auto.
    -  destruct (find_lit (watch2 cl) u).
       destruct b ; simpl ; auto.
       apply has_clause_make_watched; auto.
       simpl.
       unfold has_watched_clause.
       repeat constructor ; auto.
  Qed.

  Definition ohold {A: Type} (P: A -> Prop) (o : option A) :=
    match o with
    | None => True
    | Some v => P v
    end.

  Lemma wf_reduce :
    forall m u cl
           (WFC : Forall (has_literal m) cl),
      ohold (Forall (has_literal m)) (reduce u cl).
  Proof.
    intros.
    induction WFC ; simpl.
    -  constructor.
    - destruct (find_lit x  u) eqn:FIND.
      destruct b ; simpl ; auto.
      destruct (reduce u l).
      simpl in *. constructor ; auto.
      simpl ; auto.
  Qed.


  Lemma eval_neg_literal_rec : forall l p,
      eval_literal_rec l p ->
      eval_literal (neg_literal l) -> p.
  Proof.
    destruct l ; simpl.
    tauto.
    tauto.
  Qed.

  Lemma eval_literal_rec_swap : forall w w' p,
      eval_literal_rec w (eval_literal_rec w' p) ->
      eval_literal (neg_literal w') ->
      (eval_literal_rec w p).
  Proof.
    destruct w,w' ; simpl; try tauto.
  Qed.




    Lemma eval_make_watched :
    forall m u cl w
           (EV : eval_units m u)
           (HL : Forall (has_literal m) cl)
           (EC : eval_literal_rec w (eval_literal_list cl)),
      eval_clause (make_watched u w cl).
  Proof.
    induction cl; simpl.
    - destruct w ; simpl; tauto.
    - intros.
      destruct (find_lit a u) eqn:FD.
      + inv HL.
        apply eval_units_find_lit with (m:=m) in FD; auto.
        destruct b; simpl ; auto.
        apply IHcl; auto.
        apply eval_literal_rec_swap in EC ; auto.
      + simpl.
        unfold eval_watched_clause.
        simpl.
        auto.
  Qed.

  Lemma shorten_clause_correct :
    forall m u
           (EV : eval_units m u)
           cl
           (WFC : has_watched_clause m cl)
           (EC : eval_watched_clause cl),
      eval_clause (shorten_clause u cl).
  Proof.
    unfold shorten_clause;intros.
    assert (HW1 : has_literal m (watch1 cl)).
    { inv WFC. auto. }
    assert (HW2 : has_literal m (watch2 cl)).
    { inv WFC. inv H2; auto. }
    assert (HUW : Forall (has_literal m) (unwatched cl)).
    { inv WFC. inv H2; auto. }
    destruct (find_lit (watch1 cl) u) eqn:FD1.
    destruct b ; simpl ; auto.
    apply eval_units_find_lit with (m:=m) in FD1; auto.
    - unfold eval_watched_clause in EC.
      simpl in EC.
      apply eval_neg_literal_rec in EC; auto.
      apply  eval_make_watched with (m:=m); auto.
    - destruct (find_lit (watch2 cl) u) eqn:FD2; simpl; auto.
      destruct b ; simpl ; auto.
      apply eval_units_find_lit with (m:=m) in FD2; auto.
      apply  eval_make_watched with (m:=m); auto.
      unfold eval_watched_clause in EC.
      simpl in EC.
      apply eval_literal_rec_swap in EC; auto.
  Qed.

  Lemma eval_reduce :
    forall m u
           (EV : eval_units m u)
           cl
           (WFC : Forall (has_literal m) cl)
           (EC : eval_literal_list cl),
      ohold eval_literal_list (reduce u cl).
  Proof.
    intros. induction WFC.
    - simpl in *. auto.
    - simpl in *.
      destruct (find_lit x u) eqn:EQ.
      apply eval_units_find_lit with (m:=m) in EQ; auto.
      destruct b ; simpl ; auto.
      apply eval_neg_literal_rec in EC; auto.
      destruct (reduce u l); simpl in * ; auto.
      destruct x ; simpl in *.
      + tauto.
      + tauto.
  Qed.

  Lemma wf_map_empty : forall {A: Type},
      wf_map (IntMap.empty A).
  Proof.
    unfold wf_map.
    intros. constructor.
  Qed.

  Lemma wf_find_clauses2 :
    forall i cls ln lp
           (WF   : wf_watch_map cls)
           (FD : find_clauses i cls = (ln, lp)),
      wf_map ln /\ wf_map lp.
  Proof.
    intros.
    unfold find_clauses in FD.
    destruct (IntMap.get' i cls) eqn:EQ.
    - subst.
      apply WF in EQ; auto.
    - inv FD.
      split;
      apply wf_map_empty.
  Qed.

  Lemma wf_find_clauses :
    forall m i cls ln lp
           (WF   : wf_watch_map cls)
           (WFCL : has_clauses m cls)
           (FD : find_clauses i cls = (ln, lp)),
      IntMapForall2 (has_watched_clause m) (ln,lp) /\
      wf_map ln /\ wf_map lp.
  Proof.
    intros.
    split.
    - unfold has_clauses in WFCL.
      unfold IntMapForall in WFCL.
      unfold find_clauses in FD.
      destruct (IntMap.get' i cls) eqn:EQ.
      subst.
      apply WFCL in EQ; auto.
      inv FD.
      split; apply IntMapForallEmpty.
    - apply wf_find_clauses2 in FD;auto.
  Qed.

  Lemma has_form_find : forall m f,
      has_form m f -> IntMap.get' f.(id) m <> None.
  Proof.
    intros. inv H; simpl;  congruence.
  Qed.


  Lemma wf_map_add_clause :
    forall l id cl cls
           (WF: wf_map cls),
      wf_map (add_clause l id cl cls).
  Proof.
    unfold add_clause.
    intros.
    destruct (find_clauses (id_of_literal l) cls).
    destruct (is_positive_literal l); auto.
  Qed.

  Hint Resolve wf_map_add_clause.

  Lemma wf_watch_map_add_clause :
    forall l id cl cls
           (WFM: wf_map cls)
           (WF: wf_watch_map cls),
      wf_watch_map (add_clause l id cl cls).
  Proof.
    intros.
    unfold wf_watch_map in *.
    unfold IntMapForall in *; intros.
    unfold add_clause in H.
    destruct (find_clauses (id_of_literal l) cls) eqn:EQ.
    apply wf_find_clauses2 in EQ; auto.
    destruct EQ as(WF1 & WF2).
    destruct (is_positive_literal l);
      rewrite gsspec in H ; auto;
        destruct (eqs k (id_of_literal l)); eauto.
    - inv H; simpl ; split ; auto.
    - inv H; simpl ; split ; auto.
  Qed.


  Lemma wf_add_clause :
    forall m l i wc cls
           (WF: wf_map cls)
           (WFW : wf_watch_map cls)
           (WF : has_clauses m cls)
           (WCL : has_watched_clause m wc),
      has_clauses m (add_clause l i wc cls).
  Proof.
    unfold add_clause. intros.
    destruct(find_clauses (id_of_literal l) cls) as (ln,lp) eqn:EQ.
    apply wf_find_clauses with (m:=m) in EQ;auto.
    destruct EQ as ((WF11 & WF12) & WF2 & WF3).
    destruct (is_positive_literal l).
    unfold has_clauses.
    apply IntMapForallAdd; auto.
    split  ; simpl ; auto.
    apply IntMapForallAdd; simpl in * ; auto.
    apply IntMapForallAdd; auto.
    split  ; simpl ; auto.
    apply IntMapForallAdd; auto.
  Qed.

  Lemma eval_add_clause :
    forall l i wc cls
           (WFM : wf_map cls)
           (WF: wf_watch_map cls)
           (EC: eval_clauses cls)
           (EW: eval_watched_clause wc),
      eval_clauses (add_clause l i wc cls).
  Proof.
    unfold add_clause. intros.
    destruct (find_clauses (id_of_literal l) cls) as (ln, lp) eqn:EQ.
    assert (EQ':= EQ).
    apply eval_find_clauses  in EQ; auto.
    destruct EQ as (LN & LP).
    apply wf_find_clauses2  in EQ'; auto.
    destruct EQ' as (WLN & WLP).
    destruct (is_positive_literal l) ;
      apply IntMapForallAdd; auto.
    split; simpl; auto.
    apply IntMapForallAdd;auto.
    split; simpl; auto.
    apply IntMapForallAdd;auto.
  Qed.



  Lemma wf_insert_lit_clause :
    forall m l id cl st
           (WFS : wf_state m st)
           (WFL : has_literal m l)
           (WFC : has_watched_clause m cl),
           wf_state m (insert_lit_clause l id cl st).
  Proof.
    intros.
    destruct WFS ; destruct st ; simpl in *.
    constructor ; simpl ; auto.
    - apply wf_add_clause; auto.
    - apply wf_watch_map_add_clause; auto.
  Qed.

  Lemma eval_insert_lit_clause :
    forall m u id cl st
           (WF : wf_state m st)
           (ES : eval_state m st)
           (ECL : eval_watched_clause cl),
      eval_state m (insert_lit_clause u id cl st).
  Proof.
    unfold insert_lit_clause.
    intros. destruct st ; destruct ES ; destruct WF ; constructor ; simpl in *; auto.
    apply eval_add_clause;auto.
  Qed.

  Lemma Forall_Forall : forall {T:Type} (P Q:T -> Prop) l,
      (forall x, P x -> Q x) ->
      List.Forall P l -> List.Forall Q l.
  Proof.
    intros.
    induction H0. constructor.
    constructor ; auto.
  Qed.



  Lemma eval_add_literal :
    forall m l u
           (WF : wf_map u)
           (EU : eval_units m u)
           (EL :eval_literal l)
           (HL : has_literal m l),
      eval_units m (add_literal l u).
  Proof.
    intros.
    unfold add_literal.
    repeat intro.
    rewrite gsspec  in H ; auto.
    destruct (eqs (id f) (id_of_literal l) ).
    + inv H.
      assert (form_of_literal l =  f).
      { eapply has_form_eq ; eauto.
        apply has_form_of_literal; auto.
      }
      rewrite <- H.
      rewrite literal_eq. auto.
    + eapply EU ; eauto.
  Qed.

  Lemma wf_map_add_literal :
    forall l u
           (WF : wf_map u),
      wf_map (add_literal l u).
  Proof.
    unfold add_literal.
    intros.
    apply wf_map_add; auto.
  Qed.

  Hint Resolve wf_map_add_literal.

  Lemma wf_insert_literal : forall m l st
           (WF : wf_state m st)
           (HF : has_literal m l),
      wf_state m (insert_literal l st).
  Proof.
    unfold insert_literal.
    intros.
    destruct WF ; constructor ; simpl ; auto.
    {
      destruct (is_neg_arrow l). constructor ; auto.
      auto.
    }
    - unfold add_literal.
      unfold order_dom ; intros.
      rewrite gsspec  in H;auto.
      destruct (eqs i (id_of_literal l) ).
      replace i with (id_of_literal l) by lia.
      eapply has_form_find.
      apply has_form_of_literal; auto.
      apply wf_units0; auto.
  Qed.

  Lemma eval_insert_literal : forall m l st
           (WF : wf_state m st)
           (HF : has_literal m l)
           (EV : eval_state m st)
           (EL : eval_literal l),
      eval_state m (insert_literal l st) /\ wf_state m (insert_literal l st).
  Proof.
    split.
    -
      unfold insert_literal.
      destruct EV ; constructor ; simpl; auto.
      eapply eval_add_literal ; eauto.
      destruct WF ; auto.
    -  apply wf_insert_literal ; auto.
  Qed.



  Definition wf_state_option (m: hmap) (st: option state) :=
    match st with
    | None => True
    | Some st => wf_state m st
    end.


  Definition eval_option (m: hmap) (st: option state) :=
    match st with
    | None => False
    | Some st => eval_state m st
    end.

  Lemma fold_update_correct :
    forall {A: Type} (F: A -> state -> option state)
           (P: option state -> Prop) l
           (FOK : forall x st, In x l -> P (Some st) -> P (F x st))
           st
           (Acc : P (Some st)),
           P (fold_update F  l st).
  Proof.
    induction l; simpl.
    - auto.
    - intros.
      generalize (FOK _ _ (or_introl eq_refl) Acc).
      destruct (F a st) ; auto.
  Qed.


  Lemma eval_fold_update :
    forall {A: Type} (EVAL : A -> Prop) (WP : hmap -> A -> Prop) m F l
           (FO :
              Forall (fun cl => forall st,wf_state m st ->
                            eval_state m st ->WP  m cl ->
                            wf_state_option m (F cl st) /\ eval_option m (F cl st)) l)
           st
           (WF : wf_state m st)
           (ES : eval_state m st)
           (ALL : Forall (WP m) l)
           (CLS : Forall EVAL l),
      eval_option m
                        (fold_update F  l st).
  Proof.
    induction l ; simpl; auto.
    intros. inv CLS. inv ALL.
    inv FO.
    specialize (H5 _  WF ES).
    destruct (H5 H3).
    destruct (F a st) ; simpl in * ; auto.
  Qed.

  Lemma wf_fold_watched_update :
    forall m F l
           (FO :
              Forall (fun cl => forall st,wf_state m st ->
                                          has_watched_clause m cl ->
                            wf_state_option m (F cl st)) l)
           st
           (WF : wf_state m st)
           (ALL : Forall (has_watched_clause m) l),
      wf_state_option m
                        (fold_update F  l st).
  Proof.
    induction l ; simpl; auto.
    intros. inv ALL.
    inv FO.
    specialize (H3 _  WF).
    destruct (F a st) ; simpl in * ; auto.
  Qed.

  Lemma wf_add_watched_clause :
  forall m i wc st
         (WFC: has_watched_clause m wc)
         (WFS: wf_state m st),
  wf_state m (add_watched_clause st i wc).
  Proof.
    unfold add_watched_clause.
    intros.
    destruct WFS ; constructor ; auto.
    simpl.
    apply wf_add_clause; auto.
    apply wf_watch_map_add_clause;auto.
    apply wf_add_clause; auto.
    simpl.
    apply wf_map_add_clause ;auto.
    simpl.
    apply wf_watch_map_add_clause ;auto.
    apply wf_watch_map_add_clause ;auto.
  Qed.

  Lemma eval_add_watched_clause :
  forall m i wc st
         (WF : wf_state m st)
         (ES : eval_state m st)
         (EC : eval_watched_clause wc),
    eval_state m (add_watched_clause st i wc).
  Proof.
    unfold add_watched_clause. intros.
    destruct ES ; destruct WF ; constructor ; auto.
    simpl.
    apply eval_add_clause;auto.
    apply wf_watch_map_add_clause;auto.
    apply eval_add_clause;auto.
  Qed.

  Lemma wf_insert_normalised_clause :
    forall i m cl st
           (HCL : has_clause m cl)
           (WF : wf_state m st),
  wf_state_option m (insert_normalised_clause i cl st).
  Proof.
    unfold insert_normalised_clause.
    destruct cl ; simpl ; auto.
    intros. apply wf_insert_unit;auto.
    intros. apply wf_add_watched_clause; auto.
  Qed.

  Lemma eval_insert_normalised_clause :
    forall i m cl st
           (HCL : has_clause m cl)
           (WF : wf_state m st)
           (ES : eval_state m st)
           (EC : eval_clause cl),
  eval_option m (insert_normalised_clause i cl st).
  Proof.
    unfold insert_normalised_clause.
    destruct cl ; simpl ; auto.
    - intros; apply eval_insert_unit;auto.
    - intros.
      apply eval_add_watched_clause; auto.
  Qed.

  Lemma wf_insert_clause :
        forall m i cl st
               (HCL : has_clause m cl)
               (WF  : wf_state m st),
          wf_state_option m (insert_clause i cl st).
  Proof.
    unfold insert_clause.
    destruct cl ; simpl.
    - tauto.
    - tauto.
    - intros; apply wf_insert_unit; auto.
    - intros.
      unfold insert_watched_clause.
      apply wf_insert_normalised_clause; auto.
      apply wf_shorten_clause; auto.
  Qed.


  Lemma eval_insert_clause :
        forall m i cl st
               (HCL : has_clause m cl)
               (WF  : wf_state m st)
               (ES : eval_state m st)
               (EC : eval_clause cl),
          eval_option m (insert_clause i cl st).
  Proof.
    unfold insert_clause.
    destruct cl ; simpl.
    - tauto.
    - tauto.
    - intros.
      apply eval_insert_unit; auto.
    - intros.
      unfold insert_watched_clause.
      apply eval_insert_normalised_clause; auto.
      apply wf_shorten_clause; auto.
      apply shorten_clause_correct with (m:=m); auto.
      destruct ES ; auto.
  Qed.

  Lemma wf_get_fresh_clause : forall m st,
      wf_state m st ->
      wf_state m (snd (get_fresh_clause_id st)).
  Proof.
    intros. destruct H ; constructor ; simpl;auto.
  Qed.

  Lemma eval_get_fresh_clause : forall m st,
      eval_state m st ->
      eval_state m (snd (get_fresh_clause_id st)).
  Proof.
    intros. destruct H ; constructor ; simpl;auto.
  Qed.

  Lemma wf_insert_fresh_clause :
  forall m (cl : clause) (st : state)
         (WFCL : has_clause m cl)
         (WFST : wf_state m st),
  wf_state_option m (insert_fresh_clause cl st).
  Proof.
    unfold insert_fresh_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    change s with (snd (i,s)).
    rewrite <- EQ.
    apply wf_insert_clause ; auto.
    apply wf_get_fresh_clause ; auto.
  Qed.


  Lemma eval_insert_fresh_clause :
  forall m (cl : clause) (st : state)
         (WFCL : has_clause m cl)
         (WFST : wf_state m st)
         (EC   : eval_clause cl)
         (ES   : eval_state m st),
  eval_option m (insert_fresh_clause cl st).
  Proof.
    unfold insert_fresh_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    change s with (snd (i,s)).
    rewrite <- EQ.
    apply eval_insert_clause ; auto.
    apply wf_get_fresh_clause ; auto.
    apply eval_get_fresh_clause;auto.
  Qed.


  Lemma fold_up : forall {A Acc: Type} (P: A -> Prop) (Q: Acc -> Prop)
                                    (UP : Acc -> int -> A -> Acc)
                                    (UPOK :  forall i cl st , Q st ->  P cl  -> Q (UP st i cl))
    (cl: IntMap.t A)
    (st: Acc)
    (WF: wf_map cl)
    (CL : IntMapForall P cl)
    (ES : Q st),
    Q (IntMap.fold' UP cl st).
Proof.
  intros.
  rewrite PTrie.fold_elements'.
  assert (ALL : forall x, In x (IntMap.elements' cl nil) -> P (snd x)).
  {
    intros.
    unfold IntMapForall in CL.
    apply CL with (k:=fst x).
    destruct x.
    apply IntMap.in_elements' with (opt:= None) in H; auto.
    simpl in *. tauto.
  }
  revert st ES ALL.
  induction ((IntMap.elements'  cl nil)).
  - simpl.
    auto.
  - simpl; intros.
    apply IHl ; auto.
Qed.

Lemma wf_remove_watched_id :
  forall m l i cls
         (WF  : wf_map cls)
         (WFW : wf_watch_map cls)
         (WF : has_clauses m cls),
  has_clauses m (remove_watched_id l i cls).
Proof.
  unfold remove_watched_id.
  intros.
  destruct (find_clauses (id_of_literal l) cls) eqn:EQ.
  unfold has_clauses.
  apply wf_find_clauses with (m:=m) in EQ; auto.
  destruct EQ ; simpl  in * ; auto.
  destruct H ; simpl in *.
  destruct (is_positive_literal l); apply IntMapForallAdd;auto.
  split ; simpl; auto.
  apply IntMapForallRemove;tauto.
  split ; simpl; auto.
  apply IntMapForallRemove;tauto.
Qed.

Lemma wf_map_remove_watched_id :
  forall l i cls
         (WF: wf_map cls)
         (WFW : wf_watch_map cls),
    wf_map (remove_watched_id l i cls).
Proof.
  unfold remove_watched_id.
  intros.
  destruct (find_clauses (id_of_literal l) cls) eqn:FD.
  apply wf_find_clauses2 in FD; auto.
  destruct (is_positive_literal l);
    apply wf_map_add; auto.
Qed.

Lemma wf_watch_map_set :
  forall i t1 t2 cls
         (WF: wf_map cls)
         (WF1: wf_map t1)
         (WF2: wf_map t2)
         (WFW: wf_watch_map  cls)
  ,
  wf_watch_map (IntMap.set' i (t1,t2) cls).
Proof.
  unfold wf_watch_map.
  intros. repeat intro.
  rewrite gsspec in H; auto.
  destruct (eqs k i).
  inv H ; simpl ; auto.
  apply WFW in H.
  auto.
Qed.


Lemma wf_watch_map_remove_watched_id :
  forall l i cls
         (WFM: wf_map cls)
         (WF: wf_watch_map cls)
  ,
    wf_watch_map (remove_watched_id l i cls).
Proof.
  unfold remove_watched_id.
  intros.
  destruct (find_clauses (id_of_literal l) cls) eqn:FD.
  apply wf_find_clauses2 in FD; auto.
  destruct FD.
  destruct (is_positive_literal l).
  apply wf_watch_map_set  ; auto.
  apply IntMap.wf_remove';auto.
  apply wf_watch_map_set  ; auto.
  apply IntMap.wf_remove';auto.
Qed.

    Lemma wf_remove_watched_clause :
  forall m i s cl
         (WF : wf_state m s)
         (HAS : has_watched_clause m cl),
  wf_state m (remove_watched_clause i cl s).
Proof.
  unfold remove_watched_clause.
  intros. destruct WF ; constructor ; simpl ; auto.
  apply wf_remove_watched_id ; auto.
  apply wf_map_remove_watched_id;auto.
  apply wf_watch_map_remove_watched_id  ; auto.
  apply wf_remove_watched_id ; auto.
  apply wf_map_remove_watched_id;auto.
  apply wf_map_remove_watched_id;auto.
  apply wf_watch_map_remove_watched_id  ; auto.
  apply wf_watch_map_remove_watched_id  ; auto.
  apply wf_map_remove_watched_id;auto.
  apply wf_watch_map_remove_watched_id  ; auto.
Qed.

Lemma wf_update_watched_clause : forall m i cl st,
    wf_state_option m st ->
    has_watched_clause m cl ->
    wf_state_option m (update_watched_clause  st i cl).
Proof.
  intros. unfold update_watched_clause.
  destruct st ; simpl in * ; auto.
  unfold insert_watched_clause.
  apply wf_insert_normalised_clause; auto.
  apply wf_shorten_clause; auto.
  apply wf_remove_watched_clause;auto.
Qed.

Lemma wf_shorten_clauses :
  forall m l st
         (WFM: wf_map l)
         (ALL: IntMapForall (has_watched_clause m) l)
         (WF: wf_state m st),
        wf_state_option m (shorten_clauses l st).
Proof.
  unfold shorten_clauses.
  intros.
  change (wf_state_option m (Some st)) in WF.
  revert ALL WF .
  apply fold_up; auto.
  intros.
  apply wf_update_watched_clause; auto.
Qed.


Lemma wf_unit_propagation :
    forall n m g st
           (WF  : wf_state m st)
           (WFG : has_oform m  g),
           match unit_propagation n st g with
           | Success => True
           | OutOfFuel => True
           | Progress st' => wf_state m st'
           end.
  Proof.
    induction n.
    - simpl. tauto.
    - cbn. intros.
      destruct (extract_unit st) eqn:EQ ;[|auto].
      destruct p as (l,st').
      assert (EQ':= EQ).
      apply get_unit_wf with (m:=m) in EQ.
      destruct EQ as (WFST' & WFL).
      destruct (success g (units st') l) eqn:SUC.
      +
        auto.
      +
        destruct (find_clauses (id_of_literal l) (clauses st')) as (ln,lp) eqn:FD.
        set (L := match l with
                          | POS _ => ln
                          | NEG _ => lp
                          end) in *.
        assert (WFLL: IntMapForall (has_watched_clause m) L /\ wf_map L).
        {
          apply wf_find_clauses with (m:=m) in FD; auto.
          destruct FD as ((FD1 & FD2) & (WF1 & WF2)).
          destruct l ; tauto.
          destruct WFST' ; auto.
          destruct WFST' ; auto.
        }
        destruct WFLL as (WFL1 & WFL2).
        assert (wf_state_option m (shorten_clauses L (insert_literal l st'))).
        { apply wf_shorten_clauses ; auto.
          apply wf_insert_literal; auto.
        }
        destruct (shorten_clauses L  (insert_literal l st'))eqn:RES ; try tauto.
        apply IHn; auto.
      +  auto.
  Qed.

  Lemma IntMapForallAnd : forall {A: Type} (P1 P2: A -> Prop) l,
      IntMapForall P1 l -> IntMapForall P2 l ->
      IntMapForall (fun x => P1 x /\ P2 x) l.
  Proof.
    repeat intro.
    unfold IntMapForall in *.
    split ; eauto.
  Qed.

  Lemma eval_remove_watched_id :
    forall l i cls cl
           (WF: wf_map cls)
           (WFW: wf_watch_map cls)
           (EC : eval_clauses cls)
           (EW : eval_watched_clause cl),
  eval_clauses
    (remove_watched_id l i cls).
  Proof.
    unfold remove_watched_id.
    intros.
    destruct (find_clauses (id_of_literal l) cls) eqn:EQ.
    assert (EQ':= EQ).
    apply eval_find_clauses in EQ; auto.
    apply wf_find_clauses2 in EQ'; auto.
    unfold eval_clauses.
    destruct EQ.
    destruct (is_positive_literal l); apply IntMapForallAdd;auto.
    split; simpl ; auto.
    apply IntMapForallRemove;auto. tauto.
    split; simpl ; auto.
    apply IntMapForallRemove;auto. tauto.
  Qed.

  Lemma eval_remove_watched_clause :
    forall i m cl st
           (ES: eval_state m st)
           (WS: wf_state m st)
           (EW : eval_watched_clause cl),
      eval_state m (remove_watched_clause i cl st).
  Proof.
    unfold remove_watched_clause.
    intros. destruct ES ; destruct WS; constructor ; simpl ; auto.
    eapply eval_remove_watched_id;eauto.
    apply wf_map_remove_watched_id ; auto.
    apply wf_watch_map_remove_watched_id;auto.
    eapply eval_remove_watched_id;eauto.
  Qed.

  Lemma eval_shorten_clauses :
  forall m l st
         (WFL: wf_map l)
         (ALL: IntMapForall eval_watched_clause l)
         (ALL: IntMapForall (has_watched_clause m) l)
         (WF: wf_state m st /\ eval_state m st),
    wf_state_option m (shorten_clauses l st) /\ eval_option m (shorten_clauses l st).
Proof.
  unfold shorten_clauses.
  intros.
  apply fold_up with (P:= fun cl => eval_watched_clause  cl /\ has_watched_clause m cl);auto.
  - intros.
    destruct H; destruct H0.
    split.
    apply wf_update_watched_clause ; auto.
    unfold update_watched_clause.
    destruct st0 ; simpl in *; auto.
    unfold insert_watched_clause.
    apply eval_insert_normalised_clause; auto.
    apply wf_shorten_clause; auto.
    apply wf_remove_watched_clause;auto.
    apply eval_remove_watched_clause;auto.
    apply shorten_clause_correct with (m:=m) ;auto.
    destruct H1 ; auto.
  - apply IntMapForallAnd;auto.
Qed.


  Lemma unit_propagation_correct :
    forall n m g st
           (WF  : wf_state m st)
           (WFG : has_oform m  g)
           (EST  : eval_state m st),
           match unit_propagation n st g with
           | Success => True
           | OutOfFuel => False
           | Progress st' =>
                           (eval_state m st' -> eval_ohformula g)
           end ->  eval_ohformula g.
  Proof.
    induction n.
    - simpl. tauto.
    - cbn. intros.
      destruct (extract_unit st) eqn:EQ ;[|auto].
      destruct p as (l,st').
      assert (EQ':= EQ).
      apply get_unit_wf with (m:=m) in EQ.
      destruct EQ as (WFST' & WFL).
      apply get_unit_eval_state with (m:=m) in EQ'.
      destruct EQ' as (EL & EST').
      destruct (success g (units st') l) eqn:SUC.
      +
        destruct WFST', EST'.
        apply success_correct with (m:=m)  in SUC; auto.
      +
        destruct (find_clauses (id_of_literal l) (clauses st')) as (ln,lp) eqn:FD.
        set (L := match l with
                          | POS _ => ln
                          | NEG _ => lp
                          end) in *.
        assert (WFLL: IntMapForall (has_watched_clause m) L /\  wf_map L).
        {
          apply wf_find_clauses with (m:=m) in FD; auto.
          destruct FD as ((FD1 & FD2)& WF1 & WF2).
          destruct l ; tauto.
          destruct WFST';auto.
          destruct WFST';auto.
        }
        destruct WFLL as (WFL1 & WFL2).
        assert (EVALL : IntMapForall eval_watched_clause L).
        {
          apply eval_find_clauses
            in FD.
          destruct l ; unfold L ; simpl in *.
          tauto. tauto.
          destruct EST' ; auto.
        }
        assert (eval_option m (shorten_clauses L (insert_literal l st'))).
        { apply  eval_shorten_clauses; auto.
          split. apply wf_insert_literal; auto.
          apply eval_insert_literal ; auto.
        }
        assert (wf_state_option m (shorten_clauses L (insert_literal l st'))).
        { apply wf_shorten_clauses;auto.
          apply wf_insert_literal;auto.
        }
        destruct (shorten_clauses L (insert_literal l st'))
        eqn:RES ; try tauto.
        revert H.
        apply IHn; auto.
        simpl in *. tauto.
      +  auto.
      +  auto.
  Qed.


  Lemma eval_insert_defs : forall m m' a st,
      eval_state m st ->
      eval_state m (insert_defs m' a st).
  Proof.
    intros.
    destruct H.
    unfold insert_defs.
    constructor ; simpl ; auto.
  Qed.

  Lemma wf_insert_fresh_watched_clause :
    forall m cl st
           (ES : wf_state m st)
           (HS : has_watched_clause m cl),
           wf_state_option m (insert_fresh_watched_clause cl st).
  Proof.
    unfold insert_fresh_watched_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    change s with (snd (i,s)).
    rewrite <- EQ.
    unfold insert_watched_clause.
    apply wf_insert_normalised_clause;auto.
    apply wf_shorten_clause;auto.
    apply wf_get_fresh_clause;auto.
  Qed.

  Lemma eval_insert_fresh_watched_clause :
    forall m cl st
           (WF : wf_state m st)
           (ES : eval_state m st)
           (EC : eval_watched_clause  cl)
           (HS : has_watched_clause m cl)
    ,
      eval_option m (insert_fresh_watched_clause cl st).
  Proof.
    unfold insert_fresh_watched_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    change s with (snd (i,s)).
    rewrite <- EQ.
    unfold insert_watched_clause.
    apply eval_insert_normalised_clause;auto.
    apply wf_shorten_clause;auto.
    apply wf_get_fresh_clause;auto.
    apply eval_get_fresh_clause; auto.
    apply shorten_clause_correct with (m:=m); auto.
    destruct ES.
    destruct st ; simpl in * ; auto.
  Qed.

  Definition eval_unsat (m: hmap) (st: option state) :=
    match st with
    | None => False
    | Some st' => eval_state m st'
    end.



  Lemma eval_fold_update_correct :
    forall m  concl F
           (FOK : forall st cl, has_watched_clause m cl ->
                                eval_watched_clause cl ->
                                wf_state m st  ->eval_state m st ->
                                wf_state_option m (F cl st) /\
                                eval_unsat m (F cl st))
           acc st
           (WF: Forall (has_watched_clause m) acc)
           (EC: Forall eval_watched_clause acc)
           (WS: wf_state m st)
           (ES: eval_state m st),
      (eval_option m (fold_update F acc st) -> eval_formula concl) ->
      eval_formula concl.
  Proof.
    induction acc; simpl.
    - tauto.
    - intros. inv WF. inv EC.
      specialize (FOK _ _ H2 H4 WS ES).
      destruct (F a st) ; simpl in *; try tauto.
      destruct FOK.
      eapply IHacc with (st:=s); eauto.
  Qed.

  Lemma intro_impl_aux :
    forall m f hf acc l o
           (WF: has_form m hf)
           (EQ: hf.(elt) = f),
      intro_impl acc f hf = (l,o) ->
      (Forall eval_literal l -> eval_ohformula o) ->
      (Forall eval_literal acc -> eval_formula f).
  Proof.
    induction f using form_ind.
    - simpl; intros.
      inv H. auto.
    - simpl; intros.
      inv H. apply H0 ; auto.
    - simpl; intros.
      destruct (is_dec hf)eqn:D.
      + inv H.
        simpl in H0.
        rewrite Forall_rew in H0. simpl in H0.
        apply eval_formula_dec in WF ; auto.
        rewrite EQ in * ; simpl in *.
        tauto.
      + inv H.
        simpl in H0.
        unfold eval_hformula in H0.
        rewrite EQ in *; simpl in *; auto.
    - simpl.
      destruct (is_impl o) eqn:I.
      + destruct o ; simpl in I ; try discriminate.
        simpl.
        intros.
        revert H1.
        revert H0.
        inv EQ.
        intro.
        intro.
        assert (Forall eval_literal (POS f1 :: acc)).
        {
          constructor ; auto.
        }
        apply IHf0 in H ; auto.
        { destruct hf ; simpl in *.
          subst.
          inv WF ; auto.
        }
      + intros.
        destruct (is_dec hf)eqn:D.
        assert (WF':= WF).
        apply eval_formula_dec in WF ; auto.
        rewrite EQ in WF ; simpl in WF.
        inv H.
        rewrite Forall_rew in H0.
        simpl in H0. rewrite EQ in H0; simpl in H0.
        tauto.
        inv H. simpl in *.
        unfold eval_hformula in H0.
        rewrite EQ in H0.
        simpl in H0. tauto.
  Qed.


  Lemma intro_impl_correct :
    forall m f hf l o
           (WF: has_form m hf)
           (EQ: hf.(elt) = f),
      intro_impl nil f hf = (l,o) ->
      (Forall eval_literal l -> eval_ohformula o) ->
      eval_formula f.
  Proof.
    intros *.
    intros.
    apply intro_impl_aux with (m:=m) in H ; auto.
  Qed.

  Definition eval_oT {A:Type} (P: A -> Prop) (s : option A) :=
    match s with
    | None => True
    | Some v => P v
    end.


  Lemma cnf_of_literal_correct : forall g cp cm ar l,
      (Forall eval_watched_clause (snd (cnf_of_literal l (is_classic g) cp cm
                      ar nil (elt (form_of_literal l)) (form_of_literal l))) -> eval_ohformula g) ->
      eval_ohformula g.
  Proof.
    unfold cnf_of_literal.
    intros.
    apply cnf_correct in H ; auto.
  Qed.


  Lemma wf_intro_impl :
    forall m f acc hf l o
           (WF: has_form m hf)
           (ACC: Forall (has_literal m) acc)
           (EQ: hf.(elt) = f),
      intro_impl acc f hf = (l, o) ->
      Forall (has_literal m) l /\ has_oform m o.
  Proof.
    induction f using form_ind ; auto; intros.
    - simpl in *. inv H ; auto.
    - simpl in *. inv H ; auto.
      simpl ; tauto.
    - simpl in *.
      destruct (is_dec hf); inv H; auto.
      simpl ; split ; auto.
    - simpl in *.
      assert (HF: has_form m f1 /\ has_form m f2).
      {
        destruct hf ; simpl in *.
        subst. inv WF ; auto.
      }
      destruct HF.
      destruct (is_impl o).
      apply IHf0 in H ; auto.
      destruct (is_dec hf) ; inv H; auto.
      simpl. split ; constructor; auto.
  Qed.

  Lemma wf_cnf_of_op_plus :
    forall m b o f1 f2 hf acc
           (HF1: has_form m f1)
           (HF2: has_form m f2)
           (HF: has_form m hf)
           (HACC: Forall (has_watched_clause m) acc),
  Forall (has_watched_clause m) (cnf_of_op_plus b o f1 f2 hf acc).
  Proof.
    unfold cnf_of_op_plus.
    intros.
    destruct o ; auto.
    - repeat constructor ; auto.
    - repeat constructor ; auto.
    - unfold cnf_plus_impl.
      destruct b;
      repeat constructor ; auto.
  Qed.

  Lemma wf_cnf_of_op_minus :
    forall m b o f1 f2 hf acc
           (HF1: has_form m f1)
           (HF2: has_form m f2)
           (HF: has_form m hf)
           (HACC: Forall (has_watched_clause m) acc),
  Forall (has_watched_clause m) (cnf_of_op_minus b o f1 f2 hf acc).
  Proof.
    unfold cnf_of_op_plus.
    intros.
    destruct o ; auto.
    - repeat constructor ; auto.
    - repeat constructor ; auto.
    - repeat constructor ; auto.
  Qed.



  Lemma wf_cnf :
    forall m f b1 b2 cp cm ar acc  hf m' ar' w
      (HA : Forall (has_literal m) ar)
      (ACC: Forall (has_watched_clause m) acc)
      (HF : has_form m hf)
      (HFF: hf.(elt) = f)
      (EQ : cnf b1 b2 cp cm ar acc f hf = (m',ar',w)),
      Forall (has_literal m) ar' /\ Forall (has_watched_clause m) w.
  Proof.
    induction f using form_ind; simpl ; intros.
    - destruct (is_cons (id hf) (if b1 then cp else cm)).
      + inv EQ. split; auto.
      + inv EQ. split; auto.
    - destruct (is_cons (id hf) (if b1 then cp else cm)).
      + inv EQ. split; auto.
      + inv EQ. split; auto.
    - destruct (is_cons (id hf) (if b1 then cp else cm)).
      + inv EQ. split; auto.
      + inv EQ. split; auto.
    - destruct (is_cons (id hf) (if b1 then cp else cm)).
      + inv EQ. split; auto.
      + revert EQ.
        generalize ((if b1 then cm else set_cons (id hf) cm)) as cm'.
        generalize ((if b1 then set_cons (id hf) cp else cp)) as cp'.
        intros cp' cm'.
        set (acc':= ((if b1 then cnf_of_op_plus else cnf_of_op_minus) b2 o f1 f2 hf acc)).
        set (ar2 := (if
              is_impl o && negb b2 && b1
             then POS hf :: ar
             else ar)).

        destruct (cnf (polarity_of_op_1 o b1) b2 cp' cm' ar2 acc' (elt f1) f1)
                 as (((cp1,cm1),ar1),acc1) eqn:EQ.
        intros.
        assert (has_form m f1 /\ has_form m f2).
        { destruct hf ; simpl in HFF; subst.
          inv HF ; split; auto.
        } destruct H.
        apply IHf in EQ ; auto.
        destruct EQ.
        apply IHf0 in EQ0 ; auto.
        *  unfold ar2.
           destruct (is_impl o && negb b2 && b1);
             simpl ; auto.
        * unfold acc'.
        destruct b1.
        apply wf_cnf_of_op_plus;auto.
        apply wf_cnf_of_op_minus;auto.
  Qed.

  Lemma wf_cnf_of_literal :
    forall m l b cp cm ar acc f hf m' ar' w
           (HA : Forall (has_literal m) ar)
           (ACC: Forall (has_watched_clause m) acc)
           (HFF :elt hf = f)
           (HF : has_form m hf)
           (EQ : cnf_of_literal l b cp cm ar acc f hf = (m',ar',w)),
           Forall (has_literal m) ar' /\ Forall (has_watched_clause m) w.
  Proof.
    unfold cnf_of_literal.
    intros.
    apply wf_cnf with (m:=m) in EQ ; auto.
  Qed.


  Lemma wf_insert_defs : forall m m' ar st,
      wf_state m st ->
      Forall (has_literal m) ar ->
      wf_state m (insert_defs m' ar st).
  Proof.
    intros.
    unfold insert_defs.
    destruct H ; constructor ; simpl ; auto.
  Qed.


  Lemma wf_augment_cnf :
    forall m b l st
           (HL : has_literal m l)
           (WF : wf_state m st),
      wf_state_option m (augment_cnf b l st).
  Proof.
    unfold augment_cnf.
    intros.
    destruct (cnf_of_literal l b (fst (defs st)) (snd (defs st)) (arrows st) nil
        (elt (form_of_literal l)) (form_of_literal l)) as (((cp,cm),ar),acc) eqn:EQ.
    apply wf_cnf_of_literal with (m:=m) in EQ; auto.
    { apply fold_update_correct.
      simpl. intros.
      apply wf_insert_fresh_watched_clause; auto.
      revert x H.
      rewrite <- Forall_forall.
      tauto.
      simpl. apply wf_insert_defs;auto.
      tauto.
    }
    destruct WF; auto.
    apply has_form_of_literal; auto.
  Qed.

  Lemma wf_augment_hyp :
    forall m b l st
           (HL: has_literal m l)
           (WF: wf_state m st),
      wf_state_option m (augment_hyp b l st).
  Proof.
    unfold augment_hyp.
    intros.
    apply wf_augment_cnf; auto.
    apply wf_insert_unit ; auto.
  Qed.

  Lemma wf_cnf_hyps :
    forall b m l st
           (HL: Forall (has_literal m) l)
           (WF: wf_state m st),
      wf_state_option m (cnf_hyps b l st).
  Proof.
    unfold cnf_hyps.
    intros *. intro.
    apply fold_update_correct; simpl ; auto.
    intros.
    apply wf_augment_hyp; auto.
    revert x H. rewrite <- Forall_forall.
    auto.
  Qed.

  Lemma eval_augment_cnf :
    forall m o l st
           (HL : has_literal m l)
           (WF : wf_state m st),
      (eval_option m (augment_cnf (is_classic o) l st) -> eval_ohformula o) ->
      (eval_state m st -> eval_ohformula o).
  Proof.
    intros.
    unfold augment_cnf in H.
    destruct (cnf_of_literal l (is_classic o) (fst (defs st))
            (snd (defs st)) (arrows st) nil (elt (form_of_literal l))
            (form_of_literal l)) as (((cp',cm'),ar'),acc') eqn:EQ .
    assert (EQ':= EQ).
    apply wf_cnf_of_literal with (m:=m) in EQ' ; auto.

    change acc' with (snd (cp',cm',ar',acc')) in H.
    rewrite <- EQ in H.
    generalize (cnf_of_literal_correct o (fst (defs st))
                                       (snd (defs st)) (arrows st) l
                                       ).
    rewrite EQ in *. clear EQ.
    simpl in *.
    intros.
    apply H1. intro.
    apply H.
    apply eval_fold_update with (EVAL:=eval_watched_clause) (WP:=has_watched_clause); auto.
    {
      rewrite Forall_forall.
      intros.
      split.
      apply wf_insert_fresh_watched_clause; auto.
      apply eval_insert_fresh_watched_clause; auto.
      rewrite Forall_forall in H2 ; auto.
    }
    apply wf_insert_defs ; auto.
    tauto.
    apply eval_insert_defs ; auto.
    tauto.
    apply wf_arrows; auto.
    apply has_form_of_literal;auto.
  Qed.

  Lemma eval_augment_hyp :
    forall m o l st
           (HL : has_literal m l)
           (WF : wf_state m st),
      (eval_option m (augment_hyp (is_classic o) l st) -> eval_ohformula o) ->
      (eval_state m st -> eval_literal l -> eval_ohformula o).
  Proof.
    Proof.
      intros.
      apply eval_augment_cnf in H; auto.
      apply wf_insert_unit ; auto.
      apply eval_insert_unit;auto.
    Qed.

  Lemma eval_cnf_hyps : forall m o l st
                               (HL: Forall (has_literal m) l)
                               (WF: wf_state m st)
    ,
      (eval_option m (cnf_hyps (is_classic o) l st) -> eval_ohformula o) ->
       (eval_state m st -> Forall eval_literal l -> eval_ohformula o).
  Proof.
    unfold cnf_hyps.
    induction l ; simpl.
    - auto.
    - intros.
      inv H1. inv HL.
      specialize (eval_augment_hyp m o a st H3 WF).
      assert (WFA: wf_state_option m (augment_hyp (is_classic o) a st)).
      { apply wf_augment_hyp ; auto.  }
      destruct (augment_hyp (is_classic o) a st).
      + simpl in *.
      intros.
      specialize (IHl s H6).
      tauto.
      + simpl.
        tauto.
  Qed.


  Lemma intro_state_correct :
    forall m f st hf
           (EQ    : hf.(elt) = f)
           (WF    : has_form m hf)
           (WFST : wf_state m st)
           (EVAL  : eval_state m st),
           match intro_state st f hf with
           | None => True
           | Some (st',f') => eval_state m st' -> eval_ohformula f'
           end ->
      eval_formula f.
  Proof.
    unfold intro_state.
    intros.
    destruct (intro_impl nil f hf) eqn:I.
    assert (I':=I).
    apply wf_intro_impl with (m:=m) in I ; auto.
    generalize (intro_impl_correct m _ _ _ _ WF EQ I').
    intros.
    assert (WFC : wf_state_option  m (cnf_hyps (is_classic o) l st)).
    { apply wf_cnf_hyps ; auto. tauto. }
    specialize (eval_cnf_hyps m o l st).
    destruct (cnf_hyps (is_classic o) l st).
    - simpl.
      intros. destruct I as (HL & HH).
      destruct o.
      +
        generalize (eval_augment_cnf m (Some h) (NEG h) s HH WFC).
        simpl.
        destruct ((augment_cnf false (NEG h) s)).
        * simpl in *. intros.
          unfold eval_hformula in *.
          tauto.
        * simpl in *. tauto.
      + simpl in * ; tauto.
    - simpl in * ; tauto.
  Qed.

  Lemma intro_state_correct_Some :
    forall m f st hf st' f'
           (EQ    : hf.(elt) = f)
           (WF    : has_form m hf)
           (WFST : wf_state m st)
           (EVAL  : eval_state m st)
           (INTRO : intro_state st f hf = Some (st',f'))
           (STEP  : eval_state m st' -> eval_ohformula f'),
      eval_state m st -> eval_formula f.
  Proof.
    intros.
    generalize (intro_state_correct m f st hf EQ WF WFST).
    rewrite INTRO.
    tauto.
  Qed.

  Lemma intro_state_correct_None :
    forall m f st hf
           (EQ    : hf.(elt) = f)
           (WF    : has_form m hf)
           (WFST : wf_state m st)
           (INTRO : intro_state st f hf = None),
      eval_state m st -> eval_formula f.
  Proof.
    intros.
    generalize (intro_state_correct m f st hf EQ WF WFST).
    rewrite INTRO.
    tauto.
  Qed.



  Lemma has_form_hFF :
    forall m, wf m ->
              has_form m hFF.
  Proof.
    unfold hFF.
    intros.
    constructor.
    apply wf_false; auto.
  Qed.

  Lemma wf_intro_state :
    forall m f st hf st' f'
           (WFM   : wf m)
           (EQ: elt hf = f)
           (WF    : has_form m hf)
           (WFST : wf_state m st)
           (INTRO : intro_state st f hf = Some (st',f'))
    , wf_state m st' /\ has_oform m f'.
  Proof.
    unfold intro_state.
    intros.
    destruct (intro_impl nil f hf) eqn:WFI.
    apply wf_intro_impl with (m:=m) in WFI ; auto.
    destruct WFI.
    generalize (wf_cnf_hyps (is_classic o) m  l st).
    destruct (cnf_hyps (is_classic o) l st); try congruence.
    destruct o; try congruence.
    generalize (wf_augment_cnf m false (NEG h) s).
    destruct ((augment_cnf false (NEG h) s)); try congruence.
    inv INTRO. simpl. tauto.
    inv INTRO. simpl. tauto.
  Qed.

  Definition is_classic_lit  (l:literal) : bool :=
    match l with
    | POS _ => true
    | NEG f => f.(is_dec)
    end.

  Definition check_classic (l : list literal) :=
    List.forallb is_classic_lit l.

  Definition select_clause (is_bot: bool) (lit: IntMap.t bool) (acc: option (list literal)) (k:int) (cl : watched_clause) : option (list literal) :=
    match acc with
    | Some cl => Some cl
    | None  =>
      let res := reduce lit (watch1 cl :: watch2 cl :: unwatched cl) in
      match res with
      | None => None
      | Some l => if is_bot || check_classic l then Some l else None
      end
    end.

    Definition find_clause_in_map  (is_bot: bool) (lit: IntMap.t bool) (m : IntMap.t watched_clause)  :=
    IntMap.fold' (select_clause is_bot lit)  m None.

    Definition is_empty {A: Type} (m: IntMap.t A) :=
      match m with
      | IntMap.Leaf _ _ => true
      | _      => false
      end.


  Definition find_split_acc (lit : IntMap.t bool) (is_bot: bool) (acc: option (list literal))(k:int) (e: IntMap.t  watched_clause * IntMap.t watched_clause)
    :=
      match acc with
      | None => match find_clause_in_map is_bot lit (snd e) with
                | None => find_clause_in_map is_bot lit (fst e)
                | Some r => Some r
                end
      | Some r =>  Some r
      end.

  Definition find_split (lit : IntMap.t bool) (is_bot: bool) (cl:watch_map) : option (list literal) :=
    IntMap.fold' (find_split_acc lit is_bot) cl None.

  Definition progress_arrow (l:literal) (st:state): bool :=
    match  find_lit (POS (form_of_literal l)) (units st) with
     | None => true
     | Some true => false
     | Some false => true
    end.

  Fixpoint find_arrows (st: state) (l : list literal) :=
    match l with
    | nil => nil
    | f :: l => if progress_arrow f st
                then f::(find_arrows st l)
                else (find_arrows st l)
    end.


  Section P.

    Variable Prover : option HFormula -> state -> status (ptree unit).

    Fixpoint forall_dis (g : option HFormula) (st: state)  (cl: list literal) :
      status (list (ptree unit)) :=
      match cl with
      | nil => HasProof  (Leaf true :: nil)
      | f :: cl => match Prover g (insert_unit f st) with
                   | HasProof prf =>
                     match forall_dis g st cl with
                     | HasProof prf' =>
                       HasProof (prf :: prf')
                     | HasModel prf' => HasModel (prf::prf')
                     | Timeout prf'  => Timeout (prf::prf')
                     | Done st       => Done st
                     end
                   | HasModel prf => HasModel (prf::nil)
                   | Timeout prf  => Timeout (prf::nil)
                   | Done st      => Done st
                   end

      end.

    Lemma forall_dis_rew : forall (g : option HFormula) (st: state)  (cl: list literal),
        forall_dis g st cl =
        match cl with
      | nil => HasProof  (Leaf true :: nil)
      | f :: cl => match Prover g (insert_unit f st) with
                   | HasProof prf =>
                     match forall_dis g st cl with
                     | HasProof prf' =>
                       HasProof (prf :: prf')
                     | HasModel prf' => HasModel (prf::prf')
                     | Timeout prf'  => Timeout (prf::prf')
                     | Done st       => Done st
                     end
                   | HasModel prf => HasModel (prf::nil)
                   | Timeout prf  => Timeout (prf::nil)
                   | Done st      => Done st
                   end
        end.
    Proof. destruct cl ; reflexivity. Qed.


    Definition prover_intro (g:HFormula) (st: state) : bool :=
      match intro_state st g.(elt) g with
      | None => true
      | Some (st',g') =>
        match Prover g' st' with
        | HasProof prf => true
        | _            => false
        end
      end.

    Fixpoint prover_arrows (g : option HFormula) (st: state) (l : list literal) : status (list (ptree unit)) :=
      match l with
      | nil => HasModel (Leaf false ::nil)
      | e::l =>
        let f := form_of_literal e in
        if prover_intro f (reset_arrows l st)
        then  let st'' := insert_unit (POS f) st  in
            match Prover g st'' with
            | HasProof prf' => HasProof nil
            | HasModel prf' => HasModel nil
            | Timeout prf   => Timeout nil
            | Done st       => Done st
            end
        else prover_arrows g st l
      end.

    Lemma prover_arrows_rew : forall (g : option HFormula) (st: state) (l : list literal),
        prover_arrows g st l =
      match l with
      | nil => HasModel (Leaf false ::nil)
      | e::l =>
        let f := form_of_literal e in
        if prover_intro f (reset_arrows l st)
        then  let st'' := insert_unit (POS f) st in
            match Prover g st'' with
            | HasProof prf' => HasProof nil
            | HasModel prf' => HasModel nil
            | Timeout prf   => Timeout nil
            | Done st       => Done st
            end
        else prover_arrows g st l
      end.
    Proof. destruct l; reflexivity. Qed.

    Variable m: hmap.
    Variable wfm: wf m.

    Variable ProverCorrect :
      forall g st prf
             (WFS : wf_state m st)
             (HASF: has_oform m g)
             (ES  : eval_state m st)
             (PRF : Prover g st = HasProof prf),
        eval_ohformula g.

    Lemma eval_prover_intro : forall st f
             (WFM : wf m)
             (WFS : wf_state m st)
             (HASF: has_form m f)
             (PRF : prover_intro f st = true)
             (ES  : eval_state m st),
        eval_hformula f.
    Proof.
      intros.
      unfold prover_intro in PRF.
      destruct (intro_state st (elt f) f) eqn:EQ.
      - destruct p as (st',g').
        apply intro_state_correct_Some with (m:=m) in EQ; auto.
        apply wf_intro_state with (m:=m) in EQ; auto.
        intros. destruct (Prover g' st') eqn:P; try congruence.
        apply ProverCorrect  in P; tauto.
      - apply intro_state_correct_None with (m:=m) in EQ; auto.
    Qed.


  End P.

  Definition cons_proof (st:state) (g: option HFormula) (s : status (list (ptree unit)))  : status (ptree unit) :=
    match s with
    | HasProof l => HasProof (Deriv tt l)
    | HasModel l => HasModel (Deriv tt l)
    | Timeout  l => Timeout (Deriv tt l)
    | Done st    => Done st
    end.

  Fixpoint prover (n:nat)  (g : option HFormula) (st:state)  : status (ptree unit) :=
    match unit_propagation n st g with
    | Success => HasProof (Deriv tt nil)
    | Progress st' => match n with
                  | O => Timeout (Deriv tt nil)
                  | S n =>
                    match find_split (units st') (is_classic g) (clauses st') with
                    | None => cons_proof st' g (prover_arrows (prover n) g st' (find_arrows st' (arrows st')))
                    | Some cl => cons_proof st' g (forall_dis (prover n) g st' cl)
                    end
                  end
    | OutOfFuel =>  (cons_proof st g (Timeout nil))
    end.

  Lemma prover_rew : forall n g st,
      prover (n:nat)  (g : option HFormula) (st:state)  =
      match unit_propagation n st g with
      | Success => HasProof (Deriv tt nil)
      | Progress st' => match n with
                        | O => Timeout (Deriv tt nil)
                        | S n =>
                          match find_split (units st') (is_classic g) (clauses st') with
                          | None => cons_proof st' g (prover_arrows (prover n) g st' (find_arrows st' (arrows st')))
                          | Some cl => cons_proof st' g (forall_dis (prover n) g st' cl)
                          end
                        end
      | OutOfFuel =>  (cons_proof st g (Timeout nil))
      end.
  Proof.
    destruct n ; reflexivity.
  Qed.

  Fixpoint eval_or (l:list literal) :=
    match l with
    | nil => False
    | l::r => eval_literal l \/ eval_or r
    end.

  Lemma eval_literal_list_classic :
    forall m l
           (HF : Forall (has_literal m) l)
           (EV: eval_literal_list l)
           (C : check_classic l = true),
      eval_or l.
  Proof.
    induction l; simpl ; auto.
    intros.
    rewrite andb_true_iff in C.
    inv HF.
    destruct C. destruct a; simpl in *.
    - intuition.
    - apply eval_formula_dec in H1 ; auto.
      tauto.
  Qed.

  Lemma eval_literal_list_neg : forall l,
      (eval_or l -> False) ->
      eval_literal_list l -> False.
  Proof.
    induction l ; simpl.
    - tauto.
    - destruct a ; simpl; tauto.
  Qed.

  Lemma eval_find_clause_in_map :
    forall m g u ln
           (WF : wf_map ln)
           (EU : eval_units m u)
           (WL : IntMapForall (has_watched_clause m) ln)
           (EV : IntMapForall eval_watched_clause  ln)
           (EVAL : ohold eval_or (find_clause_in_map (is_classic g) u ln) -> eval_ohformula g),
      eval_ohformula g.
  Proof.
    unfold find_clause_in_map.
    intros.
    revert EVAL.
    set (P:= (fun x => (ohold eval_or x -> eval_ohformula g) ->
                     eval_ohformula g)).
    change (P (IntMap.fold'
        (fun (acc : option (list literal)) (_ : IntMap.elt) (cl : watched_clause) =>
         match acc with
         | Some cl0 => Some cl0
         | None =>
             match reduce u (watch1 cl :: watch2 cl :: unwatched cl) with
             | Some l => if is_classic g || check_classic l then Some l else None
             | None => None
             end
         end) ln None)).
    assert (P None) by (unfold P ; simpl; auto).
    revert H.
    generalize (IntMapForallAnd _ _ _ WL EV).
    apply fold_up.
    intros.
    destruct st ; auto.
    unfold has_watched_clause, eval_watched_clause in H0.
    destruct H0.
    apply eval_reduce with (m:=m) (u:=u)in H1; auto.
    apply wf_reduce with (u:=u) in H0.
    destruct ((reduce u (watch1 cl :: watch2 cl :: unwatched cl))).
    destruct  g; unfold is_classic.
    - unfold P.
      simpl in *.
      destruct (check_classic l) eqn:C; simpl ; auto.
      apply eval_literal_list_classic with (m:=m) in H1; auto.
    - unfold P ; simpl in *.
      intro. revert H1.
      apply eval_literal_list_neg;auto.
    - simpl in H1.
      unfold P ; destruct (is_classic g); simpl ; auto.
    - auto.
  Qed.

  Lemma wf_find_clause_in_map :
    forall m b u ln
           (WF : wf_map ln)
           (WL : IntMapForall (has_watched_clause m) ln),
      ohold (Forall (has_literal m)) (find_clause_in_map b u ln).
  Proof.
    unfold find_clause_in_map.
    intros.
    assert (ohold (Forall (has_literal m)) None) by (simpl; auto).
    revert H.
    revert WL.
    apply fold_up;auto.
    intros.
    unfold select_clause.
    destruct st ; auto.
    apply wf_reduce with (u:=u) in H0.
    destruct (reduce u (watch1 cl :: watch2 cl :: unwatched cl));
      simpl in * ; auto.
    destruct (b || check_classic l) ; simpl ; auto.
  Qed.

  Lemma eval_find_split :
    forall m g u cls
           (WFM: wf_map cls)
           (WFW: wf_watch_map cls)
           (EU : eval_units m u)
           (WF : has_clauses m cls)
           (EV : eval_clauses  cls)
           (EVAL : ohold eval_or (find_split u (is_classic g) cls) -> eval_ohformula g),
      eval_ohformula g.
  Proof.
    intros.
    unfold find_split in EVAL.
    revert EVAL.
    set (P:= (fun x => (ohold eval_or x -> eval_ohformula g) ->
                       eval_ohformula g)).
    change (P ((IntMap.fold' (find_split_acc u (is_classic g)) cls None))).
    assert (P None) by (unfold P ; simpl; auto).
    revert H.
    unfold has_clauses, eval_clauses,wf_watch_map in *.
    specialize (IntMapForallAnd _ _ _  WF EV).
    intro WF2.
    specialize (IntMapForallAnd _ _ _  WF2 WFW).
    clear WF2.
    apply fold_up;auto.
    intros.
    destruct H0 as ((HH1 & HH2) & WF1 & WF2).
    destruct HH1. destruct HH2.
    unfold find_split_acc.
    destruct st ; simpl ; auto.
    destruct (find_clause_in_map (is_classic g) u (snd cl)) eqn:FIND.
    unfold P. rewrite <- FIND.
    apply eval_find_clause_in_map with (m:=m); auto.
    unfold P.
    apply eval_find_clause_in_map with (m:=m); auto.
  Qed.

  Lemma wf_find_split :
    forall m g u cls
           (WFM: wf_map cls)
           (WFW: wf_watch_map cls)
           (WF : has_clauses m cls),
      ohold (Forall (has_literal m)) (find_split u (is_classic g) cls).
  Proof.
    intros.
    assert (ohold (Forall (has_literal m)) None) by (simpl; auto).
    revert H.
    specialize (IntMapForallAnd _ _ _  WF WFW).
    apply fold_up;auto.
    intros.
    unfold find_split_acc.
    destruct st ; simpl ; auto.
    destruct H0 as ((HH1 & HH2) & WF1 & WF2).
    destruct (find_clause_in_map (is_classic g) u (snd cl)) eqn:FIND.
    rewrite <- FIND.
    apply wf_find_clause_in_map with (m:=m); auto.
    apply wf_find_clause_in_map with (m:=m); auto.
  Qed.


  Lemma has_find_arrows :
    forall m st l
           (WF : Forall (has_literal m) l),
           Forall (has_literal m) (find_arrows st l).
  Proof.
    induction l ; simpl.
    - constructor.
    - intros.
      inv WF.
      destruct (progress_arrow a st); auto.
  Qed.

  Lemma cons_proof_inv : forall st g prf prf',
      cons_proof st g prf = HasProof prf' ->
      exists prf'', prf = HasProof prf''.
  Proof.
    destruct prf ; simpl ; try discriminate.
    intros.
    inv H.
    exists p. reflexivity.
  Qed.

  Lemma wf_reset_arrows :
    forall m l st,
           Forall (has_literal m) l ->
           wf_state m st ->
      wf_state m (reset_arrows l st).
  Proof.
    intros.
    destruct H0; constructor ; auto.
  Qed.

  Lemma eval_reset_arrows :
    forall m l st,
      eval_state m st ->
      eval_state m (reset_arrows l st).
  Proof.
    intros.
    destruct H; constructor ; auto.
  Qed.


  Lemma prover_correct :
    forall m n g st prf
           (WFm : wf m)
           (WF  : wf_state m st)
           (WFG : has_oform m g)
           (EV  :eval_state m st)
           (SUC : prover n g st  = HasProof prf),
      eval_ohformula g.
  Proof.
    induction n.
    - simpl ; auto.
      congruence.
    - intros. rewrite prover_rew in SUC.
      specialize (unit_propagation_correct (S n) _ _ _ WF WFG EV).
      specialize (wf_unit_propagation (S n) _ _ _ WF WFG).
      destruct (unit_propagation (S n) st g); try discriminate.
      + auto.
      + intros WFS0 ES.
        apply ES. clear ES ; intro ES.
        destruct (find_split (units st0) (is_classic g) (clauses st0)) eqn:FD ; try congruence.
        *
          assert (FDC : (ohold eval_or (find_split (units st0) (is_classic g) (clauses st0)) -> eval_ohformula g) ->
                  eval_ohformula g).
          {
            destruct ES, WFS0.
            apply eval_find_split with (m:=m); auto.
          }
          rewrite FD in FDC.
          simpl in FDC.
          assert (WFD : (ohold (Forall (has_literal m)) (find_split (units st0) (is_classic g) (clauses st0)))).
          {
            destruct ES, WFS0.
            apply wf_find_split with (m:=m); auto.
          }
          rewrite FD in WFD.
          simpl in WFD.
          clear FD.
          apply cons_proof_inv in SUC.
          destruct SUC as (prf'' & SUC).
          apply FDC. clear FDC.
          intro.
          revert prf'' st0 ES WFS0 SUC.
          { induction l; simpl.
          -  simpl in H. tauto.
          - intros.
            destruct (prover n g (insert_unit a st0)) eqn:C; try congruence.
            destruct (forall_dis (prover n) g st0 l) eqn:D; try congruence.
            inv SUC.
            +
              inv WFD.
              destruct H.
              revert C.
              apply IHn; auto.
              { apply wf_insert_unit ; auto. }
              { apply eval_insert_unit ; auto. }
              revert D.
              apply IHl ; auto.
          }
        *
        assert (Forall (has_literal m) (find_arrows st0 (arrows st0))).
        {
          apply has_find_arrows.
          destruct WFS0 ; auto.
        }
        apply cons_proof_inv in SUC.
        destruct SUC as (prf' & SUC).
        revert H SUC.
        revert ES WFS0.
        clear WF EV FD.
        {
          generalize (find_arrows st0 (arrows st0)) as l.
          intro. revert st0.
          induction l.
          - simpl. discriminate.
          - simpl.
            intros.
            destruct (prover_intro (prover n) (form_of_literal a) (reset_arrows l st0)) eqn:EQ; try congruence.
           +
             apply eval_prover_intro with (m:= m) in EQ; eauto.
             inv H.
             destruct ( prover n g (insert_unit (POS (form_of_literal a)) st0)) eqn:SUC' ; try congruence.
             generalize (wf_reset_arrows m l st0  H3 WFS0).
             intro.
             eapply IHn in SUC'; auto.
             apply wf_insert_unit; auto.
             simpl. apply has_form_of_literal; auto.
             apply eval_insert_unit; auto.
             apply wf_reset_arrows;auto.
             inv H ; auto.
             inv H. apply has_form_of_literal; auto.
             inv H ; auto.
             apply eval_reset_arrows; auto.
           +
              eapply IHl ; eauto.
              inv H ; auto.
        }
  Qed.


  Definition wf_entry (p : Formula -> bool) (v : option (bool * Formula)) :=
    match v with
    | None => false
    | Some(b,f) => p f && Bool.eqb b true
    end.


  Definition wfb (m:hmap) : bool :=
    (wf_entry is_FF (IntMap.get' 0 m))
    &&
    (wf_entry is_TT (IntMap.get' 1 m)).

  Lemma wfb_correct : forall m, wfb m = true -> wf m.
  Proof.
    intros.
    unfold wfb in H.
    rewrite andb_true_iff in H.
    destruct H.
    constructor ; intros.
    - unfold wf_entry in H.
      destruct (IntMap.get'  0 m) ; try congruence.
      destruct p.
      rewrite andb_true_iff in H.
      destruct H.
      rewrite Bool.eqb_true_iff in H1. subst.
      destruct f ; simpl in H ; try congruence.
    - unfold wf_entry in H0.
      destruct (IntMap.get'  1 m) ; try congruence.
      destruct p.
      rewrite andb_true_iff in H0.
      destruct H0.
      rewrite Bool.eqb_true_iff in H1. subst.
      destruct f ; simpl in H0 ; try congruence.
  Qed.

  Definition prover_formula (m: hmap) (n:nat) (f: HFormula)  :=
    if wfb m && chkHc m f.(elt) f.(id) f.(is_dec)
    then prover_intro (prover n) f (insert_unit (POS hTT) (empty_state m))
    else false.

  Lemma wf_empty : forall m,
      wf_state m (empty_state m).
  Proof.
    unfold empty_state.
    constructor ; simpl ; auto.
    - unfold order_dom.
      intros.
      rewrite empty_o in H.
      congruence.
    - repeat intro.
      unfold empty_watch_map in H.
      rewrite empty_o in H.
      congruence.
    - apply wf_map_empty; auto.
    - apply wf_map_empty; auto.
    - unfold empty_watch_map. unfold wf_watch_map.
      repeat intro.
      simpl in H. congruence.
  Qed.

  Lemma eval_empty : forall m, eval_state m (empty_state m).
  Proof.
    unfold empty_state.
    constructor ; simpl ; auto.
    - unfold eval_units.
      intros.
      rewrite empty_o in H.
      congruence.
    -  constructor.
    - repeat intro.
      unfold empty_watch_map in H.
      rewrite empty_o in H.
      congruence.
  Qed.

  Lemma prover_formula_correct : forall m n f ,
      prover_formula m n f = true ->
      eval_hformula f.
  Proof.
    unfold prover_formula.
    intros.
    destruct (wfb m && chkHc m (elt f) (id f) (is_dec f)) eqn:EQ ; try congruence.
    rewrite andb_true_iff in EQ.
    destruct EQ as (WFM & CHK).
    apply wfb_correct in WFM.
    apply chkHc_has_form in CHK; auto.
    apply eval_prover_intro with (m:=m) in H; auto.
    intros.
    eapply prover_correct; eauto.
    - apply wf_insert_unit;auto.
      apply wf_empty.
      simpl.
      constructor.
      apply wf_true ; auto.
    - destruct f; auto.
    -  apply eval_insert_unit.
       apply wf_empty.
       apply eval_empty.
       simpl. auto.
  Qed.


  Definition incr (i:int) :=
    if i == max_int then max_int else i + 1.

  Fixpoint hcons  (m : hmap) (f : Formula) : hmap :=
    match f with
    | TT  => m
    | FF =>  m
    | AT a => m
    | OP o f1 f2 => let m := hcons m f1.(elt) in
                    let m := hcons m f2.(elt) in
                    let m := IntMap.set' f1.(id) (f1.(is_dec), f1.(elt)) m in
                    IntMap.set' f2.(id) (f2.(is_dec), f2.(elt)) m
    end.

  Definition hmap_empty := IntMap.set' 0 (true, FF) (IntMap.set' 1 (true,TT) (IntMap.empty _)).

  Definition hcons_form (f : HFormula) : hmap :=
    IntMap.set' f.(id) (f.(is_dec),f.(elt)) (hcons hmap_empty f.(elt)).

  Definition hcons_prover (n:nat) (f:HFormula) :=
    let m := hcons_form f in
    prover_formula m n f.

  Lemma hcons_prover_correct : forall n f ,
      hcons_prover n f = true ->
      eval_hformula f.
  Proof.
    unfold hcons_prover.
    intros.
    apply prover_formula_correct in H.
    auto.
  Qed.

  End S.
End S.

Definition eval_prop (m: IntMap.t Prop) (i:int)  :=
  match IntMap.get' i m with
  | None => False
  | Some p => p
  end.

Register HCons.mk as cdcl.HCons.mk.
Register Formula as cdcl.Formula.type.
Register TT as cdcl.Formula.TT.
Register FF as cdcl.Formula.FF.
Register AT as cdcl.Formula.AT.
Register OP as cdcl.Formula.OP.
Register AND as cdcl.op.AND.
Register OR as cdcl.op.OR.
Register IMPL as cdcl.op.IMPL.
Register eval_hformula as cdcl.eval_hformula.
Register eval_formula as cdcl.eval_formula.
Register eval_prop as cdcl.eval_prop.

Register IntMap.empty as cdcl.IntMap.empty.
Register IntMap.set'   as cdcl.IntMap.add.


Lemma hcons_prover_int_correct : forall n f eval_atom,
    hcons_prover Int63.eqb (fun _ => false) n f  = true -> eval_hformula eval_atom f.
Proof.
  intros f prf eval_atom.
  eapply hcons_prover_correct; eauto.
  -  intros. apply Int63.eqb_correct ;auto.
  -  congruence.
Qed.

(* Definition show_units (h:hmap) (u : IntMap.t bool) : list (@literal int) :=
  IntMap.fold (fun i v (acc:list literal) => match IntMap.get' i h with
                              | None => acc
                              | Some (b,f) => (literal_of_bool v (HCons.mk i b f)) :: acc
                              end) u nil.

Definition show_clauses (cl : @map_clauses int) :=
  IntMap.fold (fun i '(l1,l2) acc => (l1++l2)++acc) cl nil.

Definition show_state (h:hmap) (st: @state int) :=
  (show_units h (units st), unit_stack st , show_clauses (clauses st)).
*)
