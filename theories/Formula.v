Require Import FSets.FMapAVL FSets.FMapFacts.
Require Import Bool ZifyBool ZArith Int63 Lia List.
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

Lemma to_Z_bounded : forall x, (0 <= to_Z x < 9223372036854775808)%Z.
Proof. apply to_Z_bounded. Qed.

Instance Inj_int_Z : InjTyp int Z :=
  mkinj _ _ to_Z (fun x => 0 <= x < 9223372036854775808)%Z to_Z_bounded.
Add  InjTyp Inj_int_Z.

Program Instance Op_max_int : CstOp max_int :=
  { TCst := 9223372036854775807 ; TCstInj := _}.
Add CstOp Op_max_int.

Program Instance Op_one : CstOp 1%int63 :=
  { TCst := 1%Z ; TCstInj := _}.
Add CstOp Op_one.


Program Instance Op_ltb : BinOp ltb :=
  {| TBOp := Z.ltb; TBOpInj := _ |}.
Proof.
  Next Obligation.
    generalize (ltb_spec n m).
    rewrite <- Z.ltb_lt.
    destruct ((φ (n)%int63 <? φ (m)%int63)%Z);
    destruct (n < m)%int63; intuition.
  Qed.
Add BinOp Op_ltb.

Program Instance Op_leb : BinOp leb :=
  {| TBOp := Z.leb; TBOpInj := _ |}.
Proof.
  Next Obligation.
    generalize (leb_spec n m).
    rewrite <- Z.leb_le.
    destruct ((φ (n)%int63 <=? φ (m)%int63)%Z);
    destruct (n <= m)%int63; intuition.
  Qed.
Add BinOp Op_leb.


Program Instance Op_eqb : BinOp eqb :=
  {| TBOp := Z.eqb; TBOpInj := _ |}.
Proof.
  Next Obligation.
    generalize (eqb_spec n m).
    symmetry.
    destruct (n == m)%int63 ; intuition.
    rewrite Z.eqb_eq.  subst ; reflexivity.
    rewrite Z.eqb_neq. intro.
    apply to_Z_inj in H.
    intuition congruence.
  Qed.
Add BinOp Op_eqb.

Program Instance Op_eq : BinRel (@eq int) :=
  {| TR := @eq Z; TRInj := _ |}.
Proof.
  Next Obligation.
    split.
    congruence.
    apply to_Z_inj.
  Qed.
Add BinRel Op_eq.

Program Instance Op_add : BinOp add :=
  {| TBOp := fun x y => (x + y) mod 9223372036854775808%Z; TBOpInj := add_spec |}%Z.
Add BinOp Op_add.


(*Module APPLIST.
  Section S.
    Variable (A: Type).

    Inductive t :=
      | NIL
      | CONS (e:A) (l:t)
      | APP  (t1: t) (t2:t).

    Definition app (l1 l2:t) : t :=
      match l1,l2 with
      | NIL , l => l
      | l   , NIL => l
      | CONS e EMPTY , l => CONS e l
      | APP l1 l2  , l   => APP l1 (APP l2 l)
      end.


    Fixpoint head (l:t) : option (A * t) :=
      match l with
      | NIL => None
      | CONS e l => Some (e,l)
      | APP t1 t2 => match head t1 with
                     | None => head t2
                     | Some(e,l) => Some(e, app l t2)
                     end
      end.

    Variable P : A -> Prop.

    Inductive Forall : t -> Prop :=
    | Forall_NIL  : Forall NIL
    | Forall_CONS : forall e l, P e -> Forall l -> Forall (CONS e l)
    | Forall_APP  : forall l1 l2, Forall l1 -> Forall l2 -> Forall (APP l1 l2).

  End S.

End APPLIST.

Arguments APPLIST.head {A}.
Arguments APPLIST.app {A}.
Arguments APPLIST.CONS {A}.
Arguments APPLIST.Forall {A}.

Import APPLIST.
*)
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

Module OrdInt <: OrderedType.OrderedType.
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

Module IntMap  := FMapAVL.Make(OrdInt).
Module IntMapF := FMapFacts.Properties(IntMap).

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

  Definition hmap := IntMap.t (bool*Formula).



  Section S.

    Variable AT_is_dec : A -> bool.

  Fixpoint chkHc (m: hmap) (f:Formula) (i:int) (b:bool) : bool :=
    match f with
    | FF => (i == 0) && Bool.eqb b true
    | TT => (i == 1) && Bool.eqb b true
    | AT a => match IntMap.find i m with
             | Some(b',AT a') => atom_eqb a a' && Bool.eqb b (AT_is_dec a) && Bool.eqb b b'
             |  _   => false
             end
    | OP o f1 f2 => chkHc m f1.(elt) f1.(id) f1.(is_dec)
                    && chkHc m f2.(elt) f2.(id) f2.(is_dec) &&
                    match IntMap.find i m with
                    | Some (b',OP o' f1' f2') =>
                      op_eqb o o' &&
                      (f1.(id) == f1'.(id)) &&
                      (f2.(id) == f2'.(id)) && Bool.eqb b (f1.(is_dec) && f2.(is_dec)) && Bool.eqb b b'
                    | _ => false
                    end
    end.


    Inductive has_form (m:hmap) : HFormula -> Prop :=
    | wf_FF : forall i b, IntMap.find i m = Some (b,FF) -> has_form m (HCons.mk i b FF)
    | wf_TT : forall i b, IntMap.find i m = Some (b,TT) -> has_form m (HCons.mk i b TT)
    | wf_AT  : forall a i b, IntMap.find i m = Some (b,AT a) -> AT_is_dec a = b ->
                             has_form m (HCons.mk i b (AT a))
    | wf_OP : forall o f1 f2 f1' f2' i b,
      has_form m f1 -> has_form m f2 ->
      IntMap.find i m = Some (b,OP o f1' f2') ->
      f1.(id) = f1'.(id) ->  f2.(id) = f2'.(id)  ->
      b = f1.(is_dec) && f2.(is_dec) ->
      has_form m (HCons.mk i b (OP o f1 f2)).

  Variable atom_eqb_true :
    forall a a', atom_eqb  a a' = true -> a=a'.

  Definition  hFF := HCons.mk 0 true FF.
  Definition  hTT := HCons.mk 1 true TT.

  Record wf (m: IntMap.t (bool * Formula)) : Prop :=
    {
    wf_false : IntMap.find 0 m = Some (true,FF);
    wf_true : IntMap.find 1 m = Some (true,TT);
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
      destruct (IntMap.find  i m) eqn:EQ; try congruence.
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
      destruct (IntMap.find  i m)eqn:FIND2; try congruence.
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

(** The classic representation of clauses is a list of positive and
    negative literals.  For inutitionistic logic, it is a formula of
    the form l1 -> ... -> ln -> l'1 \/ ... \/ l'm.

  A possible representation could be a pair of lists of literals.
  We use a more direct representation that is coupled with a well-formedness condition.
  The direct representation will allow to always consume clauses.
*)

  Inductive literal : Type :=
  | POS (f:HFormula)
  | NEG (f:HFormula).

  (* [clause] is not a very good data-structure. It would be better to  *)

  Inductive clause :=
  | EMPTY
  | ARROW (h: HFormula) (r: clause)
  | DIS   (h: literal) (r: clause).



  (** [wf_dis h1 \/ h2 \/ ... \/ hn ] *)
  Fixpoint wf_dis (cl : clause) :=
    match cl with
    | EMPTY => true
    | DIS h r => wf_dis r
    | _ => false
  end.

  Fixpoint wf_clause (cl: clause) :=
    match cl with
    | EMPTY => true
    | ARROW h r => wf_clause r
    | DIS h cl => wf_dis cl
    end.


  Definition get_unit (cl: clause) : option literal :=
    match cl with
    |ARROW h EMPTY => Some (NEG h)
    | DIS h EMPTY => Some  h
    | _ => None
    end.

  Definition map_clauses := IntMap.t (list clause * list clause).

  Inductive cnfkind :=
  | CnfCons (* a -> b -> a /\ b *)
  | CnfDes  (* a /\ b -> a , a /\ b -> b *)
  | CnfBoth.


  Record state : Type :=
    mkstate {
        (* Formulae of the form a -> b need a special processing *)
        arrows : list literal;
        (* Formulae which cnf has been already unfold *)
        defs : IntMap.t cnfkind ;
        units : IntMap.t bool;
        unit_stack : list literal;
        (* unit_list is a stack of unit clauses to be processed *)
        clauses : map_clauses
       (* An entry clause(v) returns the set of clauses starting by v.
        *);
      }.

  Definition empty_state :=
    {|
    arrows := nil;
    defs := IntMap.empty cnfkind;
    units := IntMap.empty bool;
    unit_stack := nil;
    clauses := IntMap.empty (list clause * list clause)
    |}.

  Definition find_clauses (v:int) (cls : IntMap.t (list clause * list clause)) :=
    match IntMap.find v cls with
    | None => (nil,nil)
    | Some r => r
    end.

  Definition id_of_literal (l:literal) : int :=
    match l with
    | POS l => l.(id)
    | NEG l => l.(id)
    end.

  Definition form_of_literal (l: literal) : HFormula :=
    match l with
    | POS f => f
    | NEG f => f
    end.

  Definition add_clause (l:literal) (cl: clause) (cls : IntMap.t (list clause * list clause)) :=
    let (ln,lp) := find_clauses (id_of_literal l) cls in
    match l with
    | POS v => IntMap.add v.(id) (ln,cl::lp) cls
    | NEG v => IntMap.add v.(id) (cl::ln,lp) cls
    end.

  Definition insert_unit (l:literal) (st:state) : state :=
    {|
    defs   := defs st;
    arrows := arrows st;
    units := units st;
    unit_stack := l:: unit_stack st;
    clauses := clauses st
    |}.

  Definition insert_lit_clause (l:literal) (cl: clause) (st : state) : state :=
    {|
    defs   := defs st;
    arrows := arrows st ;
    units := units st;
    unit_stack := unit_stack st;
    clauses := add_clause l cl (clauses st)
    |}.

  Definition insert_clause (st : state) (cl:clause)  : state :=
    match cl with
    | EMPTY => st (* Should not happen *)
    | ARROW h _ => insert_lit_clause (NEG h) cl st
    | DIS  l  _ => insert_lit_clause l cl st
    end.


  (** [cnf_build f] generate a list of clause to explain how to prove f *)

  Definition cnf_form_and (f1 f2: HFormula) (f: HFormula) (rst : list clause):=
    ARROW f1 (ARROW f2 (DIS (POS f) EMPTY)) :: rst.

  Definition  cnf_form_or (f1 f2: HFormula) (f: HFormula) (rst: list clause) :=
    (ARROW f1 (DIS (POS f) EMPTY))
      ::
      (ARROW f2 (DIS (POS f) EMPTY)) ::  rst.

  (* This one is incomplete *)
  Definition cnf_form_impl (f1 f2: HFormula) (f: HFormula) (rst: list clause) :=
    (ARROW f2 (DIS (POS f) (EMPTY)) :: rst).


  Definition is_cons (id: int) (l : IntMap.t cnfkind) :=
    match IntMap.find id l with
    | Some CnfCons | Some CnfBoth => true
    | _ => false
    end.

  Definition join (k1 k2 : cnfkind) :=
    match k1 , k2 with
    | CnfBoth , _ | _ , CnfBoth => CnfBoth
    | CnfCons , CnfDes | CnfDes , CnfCons => CnfBoth
    | CnfCons , CnfCons => CnfCons
    | CnfDes , CnfDes   => CnfDes
    end.

  Definition set_cons (id:int) (l: IntMap.t cnfkind) :=
    match IntMap.find id l with
    | None => IntMap.add id CnfCons l
    | Some x => IntMap.add id (join x CnfCons) l
    end.

  Fixpoint cnf_cons (l : IntMap.t cnfkind)
           (ar:list literal) (acc : list clause)  (f: Formula) (hf: HFormula) :=
    let h := hf.(id) in
    if is_cons h l then (l,ar,acc)
    else
      match f with
      | FF => (l,ar,acc) (* No way to prove false *)
      | TT => (l,ar,acc) (* We already have a proof of true *)
      | AT a => (l, ar, acc) (* We cannot do anything with atoms *)
      | OP op f1 f2 =>
        match op with
        | AND =>
          let '(l,ar,acc) := cnf_cons l ar acc f1.(elt) f1 in
          let '(l,ar,acc) := cnf_cons l ar acc f2.(elt) f2 in
          (set_cons h  l, ar,
           cnf_form_and f1 f2 hf acc)
        | OR =>
          let '(l,ar,acc) := cnf_cons l ar acc f1.(elt) f1 in
          let '(l,ar,acc) := cnf_cons l ar acc f2.(elt) f2 in
          (set_cons h  l, ar,
           cnf_form_or f1 f2 hf acc)
        | IMPL =>
          let '(l,ar,acc) := cnf_cons l ar acc f2.(elt) f2 in
          (set_cons h  l,POS hf::ar,
           cnf_form_impl f1 f2 hf acc )
        end
      end.

  (*
  Fixpoint cnf_build_classic (l : IntMap.t unit)
           (acc : list clause)  (f: Formula) (hf: HFormula) :=
    let h := hf.(id) in
    if IntMap.mem h l then (l,acc)
    else
      match f with
      | FF => (l,acc) (* No way to prove false *)
      | TT => (l,acc) (* We already have a proof of True *)
      | AT a => (IntMap.add h tt l, ar, acc)
      | OP op f1 f2 =>
        match op with
        | AND =>
          let '(l,ar,acc) := cnf_build l ar acc f1.(elt) f1 in
          let '(l,ar,acc) := cnf_build l ar acc f2.(elt) f2 in
          (IntMap.add h tt l, ar,
           cnf_form_and f1 f2 hf acc)
        | OR =>
          let '(l,ar,acc) := cnf_build l ar acc f1.(elt) f1 in
          let '(l,ar,acc) := cnf_build l ar acc f2.(elt) f2 in
          (IntMap.add h tt l, ar,
           cnf_form_or f1 f2 hf acc)
        | IMPL =>
          let '(l,ar,acc) := cnf_build l ar acc f2.(elt) f2 in
          (IntMap.add h tt l,POS hf::ar,
           cnf_form_impl f1 f2 hf acc )
        end
      end.
*)




  Definition dneg (st: state) (f : HFormula) : state :=
    {|
        defs := defs st;
        arrows := arrows st;
        units := units st;
        unit_stack := NEG f :: unit_stack st;
        clauses := clauses st
      |}.

  Definition insert_defs (m : IntMap.t cnfkind) (ar : list literal) (st : state ) :=
    {|
    defs := m;
    arrows := ar;
    units  := units st;
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.

  Definition is_impl (o: op) : bool :=
    match o with
    | IMPL => true
    | _    => false
    end.

  Definition add_unit_in_stack (u: literal)  (st: state) : state :=
    {|
    defs := defs st;
    arrows := arrows st;
    units := units st;
    unit_stack := u:: unit_stack st;
    clauses   := clauses st
    |}.


  Fixpoint intro_state (st:state) (f: Formula) (h: int) (b: bool) :=
    match f with
    | TT  => ( st, Some (HCons.mk h b TT))
    | FF  => (st, None)
    | AT a => (st, Some (HCons.mk h b (AT a))) (* could negate atom *)
    | OP o f1 f2 =>
      if is_impl o
      then
        intro_state (add_unit_in_stack (POS f1) st) f2.(elt) f2.(id) f2.(is_dec)
      else if b
               then (* apply double negation *)
                 (dneg st (HCons.mk h b f) , None)
               else (* unfold cnf *)
                 let '(m,ar,acc) := cnf_cons (defs st) (arrows st) nil f (HCons.mk h b f) in
                 let st := List.fold_left insert_clause acc st in
                 (insert_defs m ar st,Some (HCons.mk h b f))

    end.


  Inductive clause_kind :=
  | NULL (* This is an empty clause *)
  | UNIT (u:literal)
  | TAIL (u:literal) (cl:clause)
  | SUB
  .

  Definition is_empty (cl : clause) : bool :=
    match cl with
    | EMPTY => true
    | _     => false
    end.

  Definition classify_clause (cl : clause) : clause_kind :=
    match cl with
    | EMPTY => NULL
    | ARROW f r => if is_empty r then UNIT (NEG f) else
                     TAIL (NEG f) cl
    | DIS l r   => if is_empty r then UNIT l else
                     TAIL l cl
    end.

  Definition neg_bool (o : option bool) : option bool :=
    match o with
    | None => None
    | Some b => Some (negb b)
    end.

  Lemma neg_bool_some : forall o b,
      neg_bool o = Some b ->
      o = Some (negb b).
  Proof.
    destruct o ; simpl ; try congruence.
    intros. inv H.
    rewrite negb_involutive. reflexivity.
  Qed.


  Definition find_lit (l: literal) (lit : IntMap.t bool)  : option bool :=
    match l with
    | POS l => IntMap.find l.(id) lit
    | NEG l => neg_bool (IntMap.find l.(id) lit)
    end.

  Section SHORTEN.
    Variable Lit : IntMap.t bool.

    Variable REC : bool -> clause_kind.

    Definition shorten (cont: bool) (p: literal) (mk : clause -> clause) (c : clause):=
      match find_lit p Lit with
      | None => (* literal is not set *)
        if cont (* This is the first not set. Looking for 2d watch *)
        then match REC false with
             | NULL  => UNIT p
             | UNIT l =>  TAIL p (mk (DIS l EMPTY))
             | TAIL _ r => TAIL  p (mk r)
             | SUB      => SUB
             end
        else TAIL p c
      | Some true  => SUB
      | Some false => REC cont
      end.

  End SHORTEN.

  Fixpoint shorten_clause  (lit : IntMap.t bool)  (c: clause) (cont: bool) :=
    match c with
    | ARROW p r => shorten lit (shorten_clause lit r) cont (NEG p) (ARROW p) c
    | DIS p r =>   shorten lit (shorten_clause lit r) cont p      (DIS p) c
    | EMPTY => NULL
    end.


  Definition remove_clauses (l:literal) (st: state) : state :=
    {|
    defs   := defs st;
    arrows := arrows st;
    units := units st;
    unit_stack := unit_stack st;
    clauses := IntMap.remove (id_of_literal l) (clauses st)
    |}.


  Definition add_literal (l:literal) (lit : IntMap.t bool) :=
    match l with
    | POS l => IntMap.add l.(id) true lit
    | NEG l => IntMap.add l.(id) false lit
    end.

  Definition polarity_of_literal (l:literal) :=
    match l with
    | POS _ => true
    | NEG _ => false
    end.

  Definition add_literal' (l:literal) (lit: IntMap.t bool) :=
    IntMap.add (form_of_literal l).(id) (polarity_of_literal l) lit.

  Lemma add_literal_eq : forall l lit,
      add_literal l lit = add_literal' l lit.
  Proof.
    destruct l ; simpl ; auto.
  Qed.

  Definition is_arrow (f:Formula) : bool :=
    match f with
    | OP IMPL f1 f2 => true
    | _             => false
    end.


  Definition is_neg_arrow (l:literal) : bool :=
    match l with
    | POS _ => false
    | NEG f => is_arrow f.(elt)
    end.



  Definition insert_literal (l:literal) (st: state) : state :=
    {|
    defs := defs st;
    arrows := if is_neg_arrow l then (l::arrows st) else arrows st;
    units := add_literal l (units st);
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.

  Fixpoint shorten_clause_list (l:list clause) (st:state) : option state :=
    match l with
    | nil => Some st
    | e::l => match shorten_clause (units st) e true with
              | NULL => None
              | UNIT x => shorten_clause_list l (insert_unit x st)
              | TAIL x c => shorten_clause_list l (insert_lit_clause x c st)
              | SUB      => shorten_clause_list l st
              end
    end.

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
                 match IntMap.find l.(id) lit with
                 | Some false => true
                 |  _         => false
                 end
    | NEG l => match IntMap.find l.(id) lit with
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

  Inductive lit_csq :  Type :=
  | TRIVIAL
  | CLAUSES (cl : list clause_kind).

  Definition unit (l:literal) := DIS l EMPTY.

  Definition clause_of_literal (is_classic: bool) (l : literal) : list clause :=
    match l with
    | POS f =>
      match f.(elt) with
      | TT  | AT _ => nil
      | FF => nil (* the empty clause is detected earlier *)
      | OP AND f1 f2 => unit (POS f1)  :: unit (POS f2) :: nil
      | OP OR f1 f2  => (DIS (POS f1) (DIS (POS f2) EMPTY)) :: nil
      | OP IMPL f1 f2 => (ARROW f1 (DIS (POS f2) EMPTY)) :: nil
      end
    | NEG f => match f.(elt) with
               | TT           => nil
               | FF           => nil
               | AT a         => nil
               | OP AND f1 f2 => (ARROW f1 (ARROW f2 EMPTY)) :: nil
               | OP OR  f1 f2 =>  (DIS (NEG f1) EMPTY :: DIS (NEG f2) EMPTY :: nil)
               | OP IMPL f1 f2 =>
                     if is_classic then
                       unit (POS f1) :: unit (NEG f2) :: nil
                     else (* This is weaker - there are other ways to break arrows *)
                        (unit (NEG f2)  :: nil)
               end
    end.


  Definition set_unit_stack (l : list literal) (st : state) :=
    {|
    defs := defs st;
    arrows := arrows st ;
    units := units st;
    unit_stack := l;
    clauses := clauses st |}.

  Definition add_arrow (l: literal) (st:state) :=
    {|
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

  Definition insert_clause_kind (st: state) (cl:clause_kind) : option state :=
    match cl with
    | NULL => None
    | UNIT u => Some (add_unit_in_stack u st)
    | TAIL x cl => Some (insert_lit_clause x cl st)
    | SUB       => Some st (* Should not happen *)
    end.

  Definition insert_new_clause (st: state) (cl:clause) : option state :=
    insert_clause_kind st (shorten_clause  (units st) cl true).

  Fixpoint insert_new_clauses (st: state) (l : list clause) : option state :=
    match l with
    | nil => Some st
    | e::l => match insert_new_clause st e with
              | None => None
              | Some st' => insert_new_clauses st' l
              end
    end.


  Definition unfold_literal (is_classic: bool) (l:literal) (st: state) : option state :=
    insert_new_clauses st (clause_of_literal is_classic l).

  Definition set_literal (is_classic: bool) (l:literal) (st : state) : option state :=
    match unfold_literal is_classic l st with
    | None => None
    | Some st => Some (insert_literal l st)
    end.

  Record sequent :=
    mksq
      {
        ante : state;
        csq  : option HFormula
      }.

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


  Definition is_classic (concl: option HFormula) :=
    match concl with
    | None => true
    | _    => false
    end.

  (*    Definition cons_status (st:state) (concl: option HFormula) (res : status state) :=
      match res with
      | HasProof p => HasProof (Deriv (mksq st concl) (p::nil))
      | HasModel p => HasModel (Deriv (mksq st concl) (p::nil))
      | Error      => Error
      | Timeout st' => HasProof (Deriv (mksq st concl)
                                       (De
*)

  Inductive result :=
  | OutOfFuel
  | Success
  | Progress (st : state).


  
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
          match set_literal (is_classic concl) l st with
          | None => Success
          | Some st =>
            let (ln,lp) := find_clauses (id_of_literal l) (clauses st) in
            let lc := match l with
                      | POS _ => ln
                      | NEG _ => lp end in
            match shorten_clause_list lc (remove_clauses l st) with
            | None => Success
            | Some st => unit_propagation n st concl
            end
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
          match set_literal (is_classic concl) l st with
          | None => Success
          | Some st =>
            let (ln,lp) := find_clauses (id_of_literal l) (clauses st) in
            let lc := match l with
                      | POS _ => ln
                      | NEG _ => lp end in
            match shorten_clause_list lc (remove_clauses l st) with
            | None => Success
            | Some st => unit_propagation n st concl
            end
          end
      end
    end.
  Proof.
    destruct n ; reflexivity.
  Qed.

  Fixpoint eval_or (l:list HFormula) :=
    match l with
    | nil => False
    | e::l => eval_formula e.(elt) \/ eval_or l
    end.

  Fixpoint eval_and (l: list HFormula) :=
    match l with
    | nil => True
    | e::l => eval_formula e.(elt) /\ eval_and l
    end.

  Definition eval_literal (l:literal) :=
    match l with
    | POS l => eval_formula l.(elt)
    | NEG l => eval_formula l.(elt) -> False
    end.

  Fixpoint eval_clause (c: clause) :=
    match c with
    | EMPTY => False
    | ARROW f r => eval_formula f.(elt) -> (eval_clause r)
    | DIS f r   => eval_literal f \/ (eval_clause r)
    end.


  Definition literal_of_bool (b:bool) (f:HFormula) :=
    if b then POS f else NEG f.


  Definition eval_units (m : hmap) (u : IntMap.t bool) :=
    forall i d b f,
      IntMap.find i u = Some b ->
      has_form m (HCons.mk i d f) ->
      eval_literal (literal_of_bool b (HCons.mk i d f)).

  Definition eval_stack (lst : list literal) : Prop :=
    List.Forall eval_literal lst.


  Definition eval_clauses (m : hmap) (h : map_clauses) :=
    forall i ln lp,
                IntMap.find i h = Some (ln,lp) ->
                List.Forall eval_clause  ln
                /\
                List.Forall eval_clause lp.


  Definition order_map ( m m' : IntMap.t Formula) : Prop :=
    forall i f, IntMap.find i m = Some f -> IntMap.find i m' = Some f.

  Definition order_dom {A B:Type} (m : IntMap.t A) (m': IntMap.t B) : Prop :=
    forall i, IntMap.find i m <> None -> IntMap.find i m' <> None.

  Definition has_literal (m : hmap) (l : literal) :=
    match l with
    | POS f => has_form m f
    | NEG f => has_form m f
    end.

  Fixpoint has_clause (m : hmap) (cl:clause) :=
    match cl with
    | EMPTY  => True
    | ARROW h r  => has_form m h /\ has_clause m r
    | DIS l r    => has_literal m l /\ has_clause m r
    end.

  Definition has_clauses (m : hmap) (cl : map_clauses) :=
    forall i lp ln, IntMap.find i cl = Some (lp,ln) ->
                    List.Forall (has_clause m) lp  /\
                    List.Forall (has_clause m) ln.

  Record wf_state (m:hmap) (st : state) : Prop :=
    {
    wf_arrows  : List.Forall (has_literal m) (arrows st) ;
    wf_units : order_dom (units st) m;
    wf_stack : List.Forall (has_literal  m) (unit_stack st);
    wf_clauses : has_clauses  m (clauses st)
    }.

  Definition wf_csqo (m:hmap) (o:option HFormula) :=
    match o with
    | None => True
    | Some f => has_form m f
    end.


  Definition eval_hformula (f: HFormula) := eval_formula f.(elt).

  Record eval_state (m: hmap) (st: state) : Prop :=
    {
(*    ev_arrows : Forall eval_hformula (arrows st);*)
    ev_units : eval_units m (units st) ;
    ev_stack : eval_stack (unit_stack st) ;
    ev_clauses :  eval_clauses m (clauses st)
    }.

  Definition eval_ohformula (o : option HFormula) : Prop :=
    match o with
    | None => False
    | Some f => eval_hformula f
    end.

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
      match IntMap.find (id f) lit with
      | None => True
      | Some b => eval_literal (literal_of_bool b f)
      end.
  Proof.
    intros.
    unfold eval_units in EU.
    destruct (IntMap.find (elt:=bool) (id f) lit) eqn:EQ; auto.
    destruct f ; simpl in *.
    eapply EU in EQ ; eauto.
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
      destruct (IntMap.find (id f) lit); auto.
      destruct b ; try congruence.
      congruence.
    - simpl; intros.
      generalize (has_form_find_lit _ _ _ HL EU).
      destruct (IntMap.find (id f) lit); auto.
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

  Lemma eval_state_insert_unit :
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
    intros.
    rewrite IntMapF.F.remove_o in H.
    destruct (IntMap.E.eq_dec (id_of_literal l) i) eqn:EQ; try discriminate.
    apply wf_clauses0 with (i:=i); auto.
  Qed.

  Lemma eval_state_remove_clauses :
    forall m l st
           (ES : eval_state m st),
      eval_state m (remove_clauses l st).
  Proof.
    intros.
    destruct ES ; constructor ; simpl ; auto.
    unfold eval_clauses in * ; intros.
    rewrite IntMapF.F.remove_o in H.
    destruct (IntMap.E.eq_dec (id_of_literal l) i) eqn:EQ; try discriminate.
    apply ev_clauses0 with (i:= i); auto.
  Qed.

  Lemma eval_find_clauses :
    forall m   i cl ln lp
(*           (HASF: has_form m {| id := i; is_dec := b; elt := f |})*)
           (EC : eval_clauses m cl)
           (FD : find_clauses i cl = (ln, lp)),
      List.Forall eval_clause ln /\
      List.Forall eval_clause lp.
  Proof.
    unfold eval_clauses, find_clauses.
    intros.
    destruct (IntMap.find (elt:=list clause * list clause) i cl) eqn:EQ.
    -  destruct p. inv FD.
       apply EC in EQ; auto.
    - inv FD.
      split ; constructor.
  Qed.

  Definition neg_literal (l: literal) :=
    match l with
    | POS h => NEG h
    | NEG h => POS h
    end.

  Lemma eval_units_find_lit :
    forall m h u b
           (EV : eval_units m u)
           (HAS : has_literal m h)
           (FD : find_lit h u = Some b),
      (if b then eval_literal h else
         eval_literal (neg_literal h)).
  Proof.
    unfold eval_units ; intros.
    unfold find_lit in FD.
    destruct h.
    - apply EV with (d:= is_dec f) (f:=f.(elt)) in FD.
      destruct b ; simpl in * ; auto.
      simpl in HAS.
      destruct f ; auto.
    - apply neg_bool_some in FD.
      apply EV with (d:= is_dec f) (f:=f.(elt)) in FD.
      destruct b ; simpl in * ; auto.
      simpl in HAS.
      destruct f ; auto.
  Qed.

  Lemma eval_neg_literal : forall h,
      eval_literal (neg_literal h) -> ~ eval_literal h.
  Proof.
    destruct h ; simpl ; auto.
  Qed.

  Definition eval_clause_kind (cl : clause_kind) :=
    match cl with
    | NULL => False
    | UNIT u => eval_literal u
    | TAIL _ cl => eval_clause cl
    | SUB       => True
    end.

  Definition has_clause_kind (m:hmap) (cl: clause_kind) :=
    match cl with
    | NULL => True
    | UNIT u => has_literal m u
    | TAIL u cl => has_literal m u /\ has_clause m cl
    | SUB       => True
    end.

  Lemma wf_shorten_clause_aux :
    forall m cl u p
           (mkcl : clause -> clause)
           (HAS : forall cl, has_clause m cl -> has_clause m (mkcl cl))
           (IHcl : forall cont : bool,
               has_clause m cl -> has_clause_kind m (shorten_clause u cl cont)),
    forall cont : bool,
      has_literal m p /\ has_clause m cl ->
      has_clause_kind m
                      (shorten u (shorten_clause u cl) cont p mkcl (mkcl cl)).
  Proof.
    intros.
    destruct H.
    unfold shorten.
    destruct (find_lit p u).
    - destruct b ; simpl ; auto.
    - destruct cont.
      apply IHcl with (cont:= false) in H0.
      destruct (shorten_clause u cl false).
      +  simpl ; auto.
      + simpl. split ; auto.
        apply HAS. simpl. simpl in H0. tauto.
      + simpl in *. split ; auto.
        apply HAS. tauto.
      +  simpl ; auto.
      +   simpl. split ; auto.
  Qed.

  Lemma wf_shorten_clause :
    forall m u cl cont
           (WFC : has_clause m cl),
      has_clause_kind m (shorten_clause u cl cont).
  Proof.
    induction cl ; simpl.
    - auto.
    - intros.
      apply wf_shorten_clause_aux.
      + simpl. tauto.
      + auto.
      + simpl. tauto.
    - intros.
      apply wf_shorten_clause_aux.
      + simpl. tauto.
      + auto.
      + simpl. tauto.
  Qed.

  Lemma shorten_clause_correct_aux :
    forall m u mkcl h
           (MKMONO : forall cl1 cl2,
               (eval_clause cl1 -> eval_clause cl2) ->
               (eval_clause (mkcl cl1) -> eval_clause (mkcl cl2)))
           (MKLIT : eval_clause (mkcl EMPTY) -> eval_literal h)

           (cl   : clause)
           (MKEV1 : eval_clause (mkcl cl) ->
                    eval_literal (neg_literal h) ->
                    eval_clause cl)
           (EV : eval_units m u)
           (IHcl : forall cont, has_clause m cl ->
                                eval_clause cl -> eval_clause_kind (shorten_clause u cl cont))
           (WF : has_literal m h /\ has_clause m cl)
           (EVCL : eval_clause (mkcl cl))
           (cont : bool),
      eval_clause_kind (shorten u (shorten_clause u cl) cont h mkcl (mkcl cl)).
  Proof.
    unfold shorten; intros.
    destruct WF as (WF1 & WF2).
    - destruct (find_lit h u) eqn:FD.
      + destruct b ; simpl ; auto.
        apply IHcl; auto.
        apply eval_units_find_lit with (m:=m) in FD; auto.
      + destruct cont.
        specialize (IHcl false WF2).
        destruct (shorten_clause u cl false).
        * simpl in *.
          apply MKLIT.
          revert EVCL.
          apply MKMONO. simpl ; auto.
        * simpl in *.
          revert EVCL.
          apply MKMONO. simpl ; auto.
        * simpl in *.
          revert EVCL.
          apply MKMONO. simpl ; auto.
        * simpl. auto.
        * simpl; auto.
  Qed.

  Lemma shorten_clause_correct :
    forall m u
           (EV : eval_units m u)
           cl cont
           (WFC : has_clause m cl)
           (EC : eval_clause cl),
      eval_clause_kind (shorten_clause u cl cont).
  Proof.
    induction cl ; simpl.
    - auto.
    - intros. apply shorten_clause_correct_aux with (m:=m);  auto.
      + simpl. tauto.
    - intros. apply shorten_clause_correct_aux with (m:=m);  auto.
      + simpl. tauto.
      + simpl. tauto.
      + simpl. intros.
        destruct H ; auto.
        destruct h ; simpl in *. tauto. tauto.
  Qed.


  Lemma wf_find_clauses :
    forall m i cls ln lp
           (WFCL : has_clauses m cls)
           (FD : find_clauses i cls = (ln, lp)),
      (List.Forall (has_clause m) ln /\ List.Forall (has_clause m)  lp).
  Proof.
    unfold find_clauses.
    intros.
    destruct (IntMap.find i cls) eqn:EQ.
    subst.
    unfold has_clauses in WFCL.
    apply WFCL in EQ.
    tauto.
    inv FD.
    split ; constructor.
  Qed.

  Lemma has_form_find : forall m f,
      has_form m f -> IntMap.find f.(id) m <> None.
  Proof.
    intros. inv H; simpl;  congruence.
  Qed.


  Lemma wf_insert_lit_clause :
    forall m l cl st
           (WFS : wf_state m st)
           (WFL : has_literal m l)
           (WFC : has_clause m cl),
           wf_state m (insert_lit_clause l cl st).
  Proof.
    intros.
    destruct WFS ; destruct st ; simpl in *.
    unfold insert_clause.
    simpl. constructor ; simpl ; auto.
    unfold add_clause.
    destruct(find_clauses (id_of_literal l) clauses0) as (ln,lp) eqn:EQ.
    apply wf_find_clauses with (m:=m) in EQ;auto.
    destruct EQ.
    destruct l ;
    repeat intro.
    + rewrite IntMapF.F.add_o in H1.
    destruct (IntMap.E.eq_dec (id f) i).
    inv H1.
    split ; auto.
    apply wf_clauses0 in H1; auto.
    + rewrite IntMapF.F.add_o in H1.
    destruct (IntMap.E.eq_dec (id f) i).
    inv H1.
    split ; auto.
    apply wf_clauses0 in H1; auto.
  Qed.

  Lemma eval_state_insert_lit_clause :
    forall m u cl st
           (ES : eval_state m st)
           (ECL : eval_clause cl),
      eval_state m (insert_lit_clause u cl st).
  Proof.
    unfold insert_clause.
    intros. destruct st ; destruct ES ; constructor ; simpl in *; auto.
    unfold add_clause.
    destruct (find_clauses (id_of_literal u) clauses0) as (ln, lp) eqn:EQ.
    apply eval_find_clauses  with (m:=m) in EQ; auto.
    destruct u ; simpl in *.
    + repeat intro.
    rewrite IntMapF.F.add_o in H.
    destruct (IntMap.E.eq_dec (id f) i).
    inv H.
    destruct EQ. split ; auto.
    eapply ev_clauses0 ; eauto.
    +  repeat intro.
    rewrite IntMapF.F.add_o in H.
    destruct (IntMap.E.eq_dec (id f) i).
    inv H.
    destruct EQ.
    split ; auto.
    eapply ev_clauses0 ; eauto.
  Qed.

  Lemma wf_shorten_clause_list :
    forall m ln st
           (WFS : wf_state m st)
           (WF : List.Forall (has_clause m) ln),
      match shorten_clause_list ln st with
      | None => True
      | Some st' => wf_state m st'
      end.
  Proof.
    induction ln ; simpl.
    - auto.
    - intros.
      inv WF.
      specialize (wf_shorten_clause m (units st) _ true H1).
      destruct (shorten_clause (units st) a); auto.
      + intros. apply IHln; auto.
        apply wf_insert_unit  ; auto.
      + intros. apply IHln; auto.
        simpl in H. destruct H.
        apply wf_insert_lit_clause ; auto.
      + intros.
        apply IHln ; auto.
  Qed.

  Lemma shorten_clause_list_correct :
    forall m ln st
           (WFS : wf_state m st)
           (EV : eval_state m st)
           (WF : List.Forall (has_clause m) ln)
           (EC : List.Forall eval_clause ln)
    ,
      match shorten_clause_list ln st with
      | None => False
      | Some st' => eval_state m st'
      end.
  Proof.
    induction ln.
    - auto.
    - intros. cbn -[shorten_clause].
      simpl.
      inv EC.
      assert (EVU : eval_units m (units st)).
      {
        destruct EV ; auto.
      }
      inv WF.
      specialize (shorten_clause_correct _ _ EVU  _ true H3 H1).
      assert (WFA : has_clause_kind m (shorten_clause (units st) a true)).
      { apply wf_shorten_clause ; auto. }
      destruct (shorten_clause (units st) a); auto.
      + intros.
        apply IHln;auto.
        apply wf_insert_unit  ; auto.
        apply eval_state_insert_unit; auto.
      + simpl. intro.
        simpl in WFA. destruct WFA.
        apply IHln; auto.
        apply wf_insert_lit_clause ; auto.
        apply eval_state_insert_lit_clause; auto.
      + intros.
        apply IHln ; auto.
  Qed.



  Lemma Forall_Forall : forall {T:Type} (P Q:T -> Prop) l,
      (forall x, P x -> Q x) ->
      List.Forall P l -> List.Forall Q l.
  Proof.
    intros.
    induction H0. constructor.
    constructor ; auto.
  Qed.

  Lemma literal_eq : forall l,
      literal_of_bool (polarity_of_literal l) (form_of_literal l) = l.
  Proof.
    destruct l ; simpl ; auto.
  Qed.

  Lemma has_form_of_literal : forall m l,
      has_literal m l ->
      has_form m (form_of_literal l).
  Proof.
    destruct l ; simpl in *; auto.
  Qed.


  Lemma eval_add_literal :
    forall m l u
           (EU : eval_units m u)
           (EL :eval_literal l)
           (HL : has_literal m l),
      eval_units m (add_literal l u).
  Proof.
    intros.
    rewrite add_literal_eq.
    unfold add_literal'.
    repeat intro.
    rewrite IntMapF.F.add_o  in H.
    destruct (IntMap.E.eq_dec (id (form_of_literal l)) i).
    + inv H.
      assert (form_of_literal l =  {| id := i; is_dec := d; elt := f |}).
      { eapply has_form_eq ; eauto.
        apply has_form_of_literal; auto.
        simpl. lia.
      }
      rewrite <- H.
      rewrite literal_eq. auto.
    + eapply EU ; eauto.
  Qed.

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
    rewrite add_literal_eq.
    unfold order_dom, add_literal' ; intros.
    rewrite IntMapF.F.add_o  in H.
    destruct (IntMap.E.eq_dec (id (form_of_literal l)) i).
    replace i with (id (form_of_literal l)) by lia.
    eapply has_form_find.
    apply has_form_of_literal; auto.
    apply wf_units0; auto.
  Qed.

  Lemma insert_literal_correct : forall m l st
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
    -  apply wf_insert_literal ; auto.
  Qed.

  Lemma wf_add_unit_in_stack :
    forall m l st
           (HL : has_literal m l)
           (WF: wf_state m st),
      wf_state m (add_unit_in_stack l st).
  Proof.
    intros.
    destruct WF ; constructor ; simpl ; auto.
  Qed.

  Lemma eval_state_add_unit_in_stack :
    forall m l st
           (ES : eval_state m st)
           (EL : eval_literal l),
      eval_state m (add_unit_in_stack l st).
  Proof.
    intros.
    destruct ES ; constructor ; simpl; auto.
    constructor ; auto.
  Qed.




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

  Lemma clause_of_literal_correct :
    forall l  g
             (HYPS : Forall eval_clause (clause_of_literal (is_classic g) l) -> eval_ohformula g)
             (EL : eval_literal l) , eval_ohformula g.
  Proof.
    intros.
    unfold clause_of_literal in HYPS.
    destruct l ; simpl in HYPS.
    - simpl in EL.
      destruct (elt f) ; try congruence; simpl in *;
        repeat rewrite Forall_rew in HYPS; try tauto.
      destruct o;
      unfold unit in *; simpl in *;
      repeat rewrite Forall_rew in HYPS;
      simpl in *;  tauto.
    - simpl in EL.
      destruct (elt f) ; try congruence;
        subst; simpl in *;
        repeat rewrite Forall_rew in HYPS; try tauto.
      destruct o;
      simpl in *;
      repeat rewrite Forall_rew in HYPS;
      simpl in *;
      try tauto.
      destruct g ; simpl in *.
      { rewrite Forall_rew in HYPS. tauto. }
      {
        rewrite! Forall_rew in HYPS.
        simpl in HYPS.
        tauto.
      }
  Qed.

  Definition wf_state_option (m: hmap) (st: option state) :=
    match st with
    | None => True
    | Some st => wf_state m st
    end.

  Lemma wf_insert_clause_kind :
    forall m st cl
           (WL : has_clause_kind m cl)
           (WF : wf_state m st),
      wf_state_option m (insert_clause_kind st cl).
  Proof.
    unfold insert_clause_kind.
    destruct cl ; simpl ; auto.
    apply wf_add_unit_in_stack ; auto.
    intros.
    apply wf_insert_lit_clause ; auto.
    tauto. tauto.
  Qed.

  Definition eval_state_option (m: hmap) (st: option state) :=
    match st with
    | None => False
    | Some st => eval_state m st
    end.


  Lemma eval_state_insert_clause_kind : forall m st cl,
      eval_clause_kind cl ->
      eval_state m st  ->
      eval_state_option m (insert_clause_kind st cl).
  Proof.
    destruct cl ; simpl ; auto.
    - intros. apply eval_state_add_unit_in_stack ;auto.
    - intros. apply eval_state_insert_lit_clause ;auto.
  Qed.

  Lemma eval_insert_new_clause : forall m st a,
      eval_state m st ->
      eval_clause a   ->
      has_clause m a  ->
      eval_state_option m (insert_new_clause st a).
  Proof.
    unfold insert_new_clause.
    intros.
    apply eval_state_insert_clause_kind; auto.
    apply shorten_clause_correct with (m:=m); auto.
    destruct H ; auto.
  Qed.

  Lemma eval_state_insert_clause_kinds : forall m cl st,
      Forall (has_clause m) cl ->
      Forall eval_clause cl ->
      eval_state m st ->
      eval_state_option m (insert_new_clauses st cl).
  Proof.
    induction cl ; simpl ; auto.
    intros.
    inv H0. inv H.
    specialize (eval_insert_new_clause m st a H1 H4 H3).
    destruct (insert_new_clause st a)  ; simpl; auto.
  Qed.

  Lemma wf_clause_of_literal :
    forall m b l
           (HL : has_literal m l),
      Forall (has_clause m) (clause_of_literal b l).
  Proof.
    intros.
    destruct l ; simpl  ; try congruence.
    - simpl in HL. destruct f.
      simpl in *.
      destruct elt0; try constructor.
      destruct o ; inv HL ; repeat constructor ; simpl ; auto.
    - simpl in HL. destruct f.
      simpl in *.
      destruct elt0 ; repeat constructor ; auto.
      destruct o ; inv HL ; repeat constructor ; simpl ; auto.
      destruct b ; repeat constructor ; simpl; auto.
  Qed.


  Lemma unfold_literal_correct :
    forall m l st concl
           (WF : wf_state m st)
           (HF : has_literal m l)
           (EL : eval_literal l)
           (HYPS : eval_state_option m (unfold_literal (is_classic concl) l st) -> eval_ohformula concl)
           (ES : eval_state m st), eval_ohformula concl.
  Proof.
    unfold unfold_literal.
    intros.
    revert EL.
    apply clause_of_literal_correct.
    intros. apply HYPS.
    apply eval_state_insert_clause_kinds;auto.
    apply wf_clause_of_literal; auto.
  Qed.

  Lemma wf_insert_new_clause :
    forall m st cl
           (WFC : has_clause m cl)
           (WF: wf_state m st),
      wf_state_option m (insert_new_clause st cl).
  Proof.
    unfold insert_new_clause.
    intros.
    apply wf_insert_clause_kind; auto.
    apply wf_shorten_clause; auto.
  Qed.

  Lemma wf_unfold_literal :
    forall m b l st
           (HL : has_literal m l)
           (WF: wf_state m st),
      wf_state_option m (unfold_literal b l st).
  Proof.
    unfold unfold_literal.
    intros.
    apply  wf_clause_of_literal with (b:=b) in HL.
    revert  st WF.
    induction HL ; simpl ; auto.
    intros.
    specialize (wf_insert_new_clause m st x H WF).
    destruct (insert_new_clause st x); auto.
  Qed.

  Lemma set_literal_correct :
    forall m l st concl
           (WF : wf_state m st)
           (HF : has_literal m l)
           (EL : eval_literal l)
           (HYPS : eval_state_option m (set_literal (is_classic concl) l st) -> eval_ohformula concl)
           (ES : eval_state m st), eval_ohformula concl.
  Proof.
    unfold set_literal.
    intros.
    eapply unfold_literal_correct; eauto.
    specialize (wf_unfold_literal m (is_classic concl) l st HF WF).
    destruct (unfold_literal (is_classic concl) l st);
    simpl in *; auto.
    intros. apply HYPS.
    apply insert_literal_correct; auto.
  Qed.


  Lemma wf_set_literal :
    forall m b l st
           (WF : wf_state m st)
           (HF : has_literal m l),
      wf_state_option m (set_literal b l st).
  Proof.
    unfold set_literal.
    intros.
    specialize (wf_unfold_literal m b l st HF WF).
    destruct (unfold_literal b l st); auto.
    simpl ; auto.
    intros.
    apply wf_insert_literal ; auto.
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
    - cbn - [set_literal]. intros.
      destruct (extract_unit st) eqn:EQ ;[|auto].
      destruct p as (l,st').
      assert (EQ':= EQ).
      apply get_unit_wf with (m:=m) in EQ.
      destruct EQ as (WFST' & WFL).
      destruct (success g (units st') l) eqn:SUC.
      +
        auto.
      +
        destruct (set_literal (is_classic g) l st') as [st''|] eqn:SLIT .
        assert (WFST'' : wf_state m st'').
        {
          change (wf_state_option m (Some st'')).
          rewrite <- SLIT.
          apply wf_set_literal ; auto. }
        destruct (find_clauses (id_of_literal l) (clauses st'')) as (ln,lp) eqn:FD.
        assert (WFR : wf_state m (remove_clauses l st'')).
        {
          apply wf_remove_clauses.
          auto.
        }
        set (L := match l with
                          | POS _ => ln
                          | NEG _ => lp
                          end) in *.
        assert (WFLL: List.Forall (has_clause m) L).
        {
          apply wf_find_clauses with (m:=m) in FD; auto.
          destruct l ; tauto.
          apply wf_clauses ; auto.
        }
        specialize (wf_shorten_clause_list _ _ _ WFR WFLL).
        destruct (shorten_clause_list L (remove_clauses l st''))eqn:RES ; try tauto.
        intros WS.
        apply IHn; auto.
        auto.
      +  auto.
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
    - cbn - [set_literal]. intros.
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
        revert EST'.
        apply set_literal_correct with (l:=l) ; auto.
        intro EST''.
        set (st'' := set_literal (is_classic g) l st') in *.
        assert (WFST'' : wf_state_option m st'').
        { apply wf_set_literal ; auto. }
        clearbody st''.
        destruct st''  as [st''|] ; simpl in EST'' ; [|tauto].
        destruct (find_clauses (id_of_literal l) (clauses st'')) as (ln,lp) eqn:FD.
        assert (ESR : eval_state m (remove_clauses l st'')).
        { apply eval_state_remove_clauses ; auto. }
        assert (WFR : wf_state m (remove_clauses l st'')).
        {
          apply wf_remove_clauses.
          auto.
        }
        set (L := match l with
                          | POS _ => ln
                          | NEG _ => lp
                          end) in *.
        assert (WFLL: List.Forall (has_clause m) L).
        {
          apply wf_find_clauses with (m:=m) in FD; auto.
          destruct l ; tauto.
          apply wf_clauses ; auto.
        }
        assert (EVALL : List.Forall eval_clause L).
        {
          apply eval_find_clauses
            with (m:=m)  in FD.
          destruct l ; unfold L ; simpl in *.
          tauto. tauto.
          destruct EST'' ; auto.
        }
        specialize (shorten_clause_list_correct _ _ _ WFR ESR WFLL EVALL).
        specialize (wf_shorten_clause_list _ _ _ WFR WFLL).
        destruct (shorten_clause_list L (remove_clauses l st''))eqn:RES ; try tauto.
        intros WS ES.
        revert H.
        apply IHn; auto.
      +  auto.
      +  auto.
  Qed.


  Lemma cnf_form_and_correct : forall m f1 f2 hf acc,
      elt hf = OP AND f1 f2 ->
      has_form m f1 -> has_form m f2 ->
      has_form m hf ->
      Forall (has_clause m) acc ->
      Forall eval_clause acc ->
      Forall eval_clause (cnf_form_and f1 f2 hf acc)/\
      Forall (has_clause m) (cnf_form_and f1 f2 hf acc).
  Proof.
    unfold cnf_form_and.
    split ; constructor ; auto.
    -  simpl. rewrite H. simpl ; tauto.
    -  simpl. tauto.
  Qed.

  Lemma cnf_form_or_correct : forall m f1 f2 hf acc,
      elt hf = OP OR f1 f2 ->
      has_form m f1 -> has_form m f2 ->
      has_form m hf ->
      Forall (has_clause m) acc ->
      Forall eval_clause acc ->
      Forall eval_clause (cnf_form_or f1 f2 hf acc)/\
      Forall (has_clause m) (cnf_form_or f1 f2 hf acc).
  Proof.
    unfold cnf_form_or.
    split ; constructor ; auto.
    -  simpl. rewrite H. simpl ; tauto.
    -  constructor; auto.
       simpl. rewrite H. simpl ; tauto.
    - simpl. tauto.
    -  constructor ; simpl ; tauto.
  Qed.

  Lemma cnf_form_impl_correct : forall m f1 f2 hf acc,
      elt hf = OP IMPL f1 f2 ->
      has_form m f2 ->
      has_form m hf ->
      Forall (has_clause m) acc ->
      Forall eval_clause acc ->
      Forall eval_clause (cnf_form_impl f1 f2 hf acc)/\
      Forall (has_clause m) (cnf_form_impl f1 f2 hf acc).
  Proof.
    unfold cnf_form_impl.
    split ; constructor ; auto.
    -  simpl. rewrite H. simpl ; tauto.
    -  simpl. tauto.
  Qed.


  Lemma cnf_build_correct :
    forall m f d a acc  hf d' a' acc'
           (EC : Forall eval_clause acc)
           (WFC : Forall (has_clause m) acc)
           (WFA : Forall (has_literal m) a)
           (WF  : has_form m hf)
           (HF  : hf.(elt) = f)
           (EQ :  cnf_cons d a acc f hf = (d',a',acc')),
      (Forall eval_clause acc' /\ Forall (has_clause m) acc')
      /\
      Forall (has_literal m) a'.
  Proof.
    induction f using form_ind.
    - simpl. intros.
      destruct (is_cons (id hf) d).
      + inv EQ. tauto.
      + inv EQ.
        intuition.
    - simpl. intros.
      destruct (is_cons  (id hf) d).
      + inv EQ. tauto.
      + inv EQ.
        intuition.
    - simpl ; intros.
      destruct (is_cons (id hf) d).
      + inv EQ. tauto.
      + inv EQ. tauto.
    - intros.
      simpl in EQ.
      destruct (is_cons  (id hf) d); inv EQ ; [tauto|].
      destruct o.
      + destruct (cnf_cons d a acc (elt f1) f1) as ((l1&ar1)&acc1) eqn:EQ1.
        destruct (cnf_cons l1 ar1 acc1 (elt f2) f2) as ((l2&ar2)&acc2) eqn:EQ2.
        inv H0.
        assert (WF1 : has_form m f1 /\ has_form m f2).
        {
          destruct hf. simpl in *.
          subst. inv WF; auto.
        }
        destruct WF1 as (WF1 & WF2).
        apply IHf in EQ1 ; auto.
        apply IHf0 in EQ2 ; try tauto.
        split.
        apply cnf_form_and_correct ; try tauto.
        tauto.
      + destruct (cnf_cons d a acc (elt f1) f1) as ((l1&ar1)&acc1) eqn:EQ1.
        destruct (cnf_cons l1 ar1 acc1 (elt f2) f2) as ((l2&ar2)&acc2) eqn:EQ2.
        inv H0.
        assert (WF1 : has_form m f1 /\ has_form m f2).
        {
          destruct hf. simpl in *.
          subst. inv WF; auto.
        }
        destruct WF1 as (WF1 & WF2).
        apply IHf in EQ1 ; auto.
        apply IHf0 in EQ2 ; try tauto.
        split.
        apply cnf_form_or_correct ; try tauto.
        tauto.
      + destruct (cnf_cons d a acc (elt f2) f2) as ((l1&ar1)&acc1) eqn:EQ1.
        inv H0.
        assert (WF1 : has_form m f2).
        {
          destruct hf. simpl in *.
          subst. inv WF; auto.
        }
        apply IHf0 in EQ1 ; try tauto.
        split.
        apply cnf_form_impl_correct;try tauto.
        constructor ; tauto.
  Qed.


  Lemma eval_state_insert_clause :
    forall m st a,
      eval_clause a ->
      eval_state m st ->
      eval_state m (insert_clause st a).
  Proof.
    unfold insert_clause.
    destruct a.
    - auto.
    - intros.
      apply eval_state_insert_lit_clause; auto.
    - intros.
      apply eval_state_insert_lit_clause; auto.
  Qed.

  Lemma eval_state_insert_defs : forall m m' a st,
      eval_state m st ->
      eval_state m (insert_defs m' a st).
  Proof.
    intros.
    destruct H.
    unfold insert_defs.
    constructor ; simpl ; auto.
  Qed.


  Lemma intro_state_correct :
    forall m f st h b st' f'
           (WF    : has_form m (HCons.mk h b f))
           (WFST : wf_state m st)
           (INTRO : intro_state st f h b = (st',f'))
           (EVAL  : eval_state m st)
           (CONCL : eval_state m st' -> eval_ohformula f')
    , eval_formula f.
  Proof.
    induction f using form_ind.
    -  simpl ; auto.
    - intros. inv INTRO.
      simpl in *. tauto.
    - simpl; intros. inv INTRO.
      simpl in CONCL. tauto.
    - intros.
      destruct (is_impl o) eqn:ISIMPL.
      + destruct o ; simpl in ISIMPL ; try congruence.
        simpl in INTRO.
        simpl. intros.
        assert (HASF2 : has_form m f2).
        {
          inv WF. auto.
        }
        assert (HASF1 : has_form m f1).
        {
          inv WF. auto.
        }
        destruct f2; simpl in *.
        apply IHf0 in INTRO; auto.
        destruct WFST.
        constructor ; simpl ; auto.
        destruct EVAL ; constructor ; simpl ; auto.
        constructor ; auto.
      + unfold intro_state in INTRO.
        rewrite ISIMPL in INTRO.
        destruct b.
        * inv INTRO.
          simpl in CONCL.
          apply eval_formula_dec in WF; simpl ; auto.
          simpl in WF.
          destruct WF ; auto.
          exfalso.
          apply CONCL.
          destruct EVAL ;
            constructor; simpl;auto.
          constructor. simpl. tauto.
          auto.
        *
          destruct (cnf_cons (defs st) (arrows st) nil (OP o f1 f2)
                              {| id := h; is_dec := false; elt := OP o f1 f2 |})
                            as ((m',ar),acc) eqn:EQ.
          inv INTRO.
          apply CONCL.
          {
            apply cnf_build_correct with (m:= m) in EQ.
            -
            simpl in CONCL.
          assert (eval_state m (fold_left insert_clause acc st)).
          {
            revert EVAL.
            assert (EVALA : Forall eval_clause acc) by tauto.
            clear - EVALA.
            revert st.
            induction acc.
            - simpl. auto.
            - simpl.
              intros.
              inv EVALA.
              apply IHacc; auto.
              apply eval_state_insert_clause ; auto.
          }
          apply eval_state_insert_defs ; auto.
            -  constructor.
            -  constructor.
            -  destruct WFST ; auto.
            - auto.
            -  simpl ; auto.
          }
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

  Lemma wf_dneg : forall m f st,
      wf_state m st ->
      has_form m f ->
      wf_state m (dneg st f).
  Proof.
    unfold dneg.
    intros.
    destruct H ; constructor ; simpl ; auto.
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

  Lemma wf_intro_state :
    forall m f st h b st' f'
           (WFM   : wf m)
           (WF    : has_form m (HCons.mk h b f))
           (WFST : wf_state m st)
           (INTRO : intro_state st f h b = (st',f'))
    , wf_state m st' /\ has_oform m f'.
  Proof.
    induction f using form_ind.
    -  simpl ; intros.
       inv INTRO. split; auto.
    -  simpl; intros. inv INTRO.
       simpl.
       split ; auto.
    - simpl; intros. inv INTRO.
      split ; auto.
    - intros.
      destruct (is_impl o) eqn:ISIMPL.
      + destruct o ; simpl in ISIMPL ; try congruence.
        simpl in INTRO.
        assert (HASF2 : has_form m f2).
        {
          inv WF. auto.
        }
        assert (HASF1 : has_form m f1).
        {
          inv WF. auto.
        }
        destruct f2; simpl in *.
        apply IHf0 in INTRO; auto.
        apply wf_add_unit_in_stack ; auto.
      + unfold intro_state in INTRO.
        rewrite ISIMPL in INTRO.
        destruct b.
        * inv INTRO.
          split.
          now apply wf_dneg ; auto.
          now simpl ; auto.
        *
          destruct (cnf_cons (defs st) (arrows st) nil (OP o f1 f2)
                              {| id := h; is_dec := false; elt := OP o f1 f2 |})
                            as ((m',ar),acc) eqn:EQ.
          inv INTRO.
          split ; auto.
          apply cnf_build_correct with (m:= m) in EQ.
          destruct EQ as ((E1 & E2) &  E3).
          apply wf_insert_defs ; auto.
          revert st WFST.
          clear E1.
          induction acc ; simpl; auto.
          intros.
          eapply IHacc ; auto.
          inv E2 ; auto.
          unfold insert_clause.
          destruct a ; auto.
          apply wf_insert_lit_clause ; auto.
          inv E2. inv H1.  simpl ; auto.
          inv E2 ; auto.
          apply wf_insert_lit_clause ; auto.
          inv E2. inv H1.  simpl ; auto.
          inv E2 ; auto.
          constructor.
          constructor .
          destruct WFST ; auto.
          auto.
          simpl ; auto.
  Qed.


  Fixpoint split_of_cclause (cl: clause) : list literal :=
    match cl with
    | EMPTY => nil
    | ARROW l cl => (NEG l) :: split_of_cclause cl
    | DIS l cl   => l :: (split_of_cclause cl)
    end.

  Fixpoint split_of_iclause (cl : clause) : option (list literal) :=
    match cl with
    | EMPTY => Some nil
    | ARROW _ _ => None
    | DIS l cl  => match split_of_iclause cl with
                   | None => None
                   | Some cl => Some (l::cl)
                   end
    end.

  Definition split_of_clause (isbot: bool) (cl: clause) : option (list literal) :=
    if isbot then Some (split_of_cclause cl)
    else split_of_iclause cl.

  Definition is_sub (cl : clause_kind) :=
    match cl with
    | SUB => true
    | _   => false
    end.

  Definition clause_of_clause_kind (cl : clause_kind) :=
    match cl with
    | NULL => Some EMPTY
    | UNIT l => Some (DIS l EMPTY)
    | TAIL _ cl => Some cl
    | SUB       => None
    end.


  Fixpoint find_clause_kind (lit : IntMap.t bool) (l : list clause) :=
    match l with
    | nil => None
    | e::l => match clause_of_clause_kind (shorten_clause lit e true) with
              | None => find_clause_kind lit l
              | Some cl => Some cl
              end
    end.

  Definition find_split_acc (lit : IntMap.t bool) (is_bot: bool) (k:int) (e: list clause * list clause) (acc: option clause)
    :=
            match acc with
                   | None => match snd e with
                             | nil => if is_bot
                                      then find_clause_kind lit (fst e)
                                      else None
                             | l => find_clause_kind lit l
                             end
                   | Some r =>  Some r
            end.

  Definition find_split_clause (lit : IntMap.t bool) (is_bot: bool) (cl:map_clauses) : option clause :=
    IntMap.fold (find_split_acc lit is_bot) cl None.

  Definition find_split (lit : IntMap.t bool) (is_bot: bool) (cl: map_clauses) : option (list literal) :=
    match find_split_clause lit is_bot cl with
    | None => None
    | Some cl => split_of_clause is_bot cl
    end.

    Fixpoint find_arrows (st: state) (l : list literal) :=
      match l with
      | nil => nil
      | f :: l => if is_arrow (form_of_literal f).(elt)
                  then match  find_lit f (units st) with
                       | None => f::find_arrows st l
                       | Some _ => find_arrows st l
                       end
                  else find_arrows st l
      end.


  Section P.


    Variable Prover : option HFormula -> state -> status (ptree sequent).

    Fixpoint forall_dis (g : option HFormula) (st: state)  (cl: list literal) :
      status (list (ptree sequent)) :=
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

    Fixpoint prover_arrows (g : option HFormula) (st: state) (l : list literal) : status (list (ptree sequent)) :=
      match l with
      | nil => HasModel (Leaf false ::nil)
      | e::l =>
        let f := form_of_literal e in
        let (st',g') := intro_state st f.(elt) f.(id) f.(is_dec) in
        match Prover g' st' with
        | HasProof prf =>
          let st'' := add_unit_in_stack (POS f) st in
          match Prover g st'' with
          | HasProof prf' => HasProof nil
          | HasModel prf' => HasModel nil
          | Timeout prf   => Timeout nil
          | Done st       => Done st
          end
        | HasModel m => prover_arrows g st l
        | Timeout st' => Timeout (st'::nil)
        | Done st'    => Done st'
        end
      end.

    Lemma prover_arrows_rew : forall (g : option HFormula) (st: state) (l : list literal),
        prover_arrows g st l =
        match l with
      | nil => HasModel (Leaf false ::nil)
      | e::l =>
        let f := form_of_literal e in
        let (st',g') := intro_state st f.(elt) f.(id) f.(is_dec) in
        match Prover g' st' with
        | HasProof prf =>
          let st'' := add_unit_in_stack (POS f) st in
          match Prover g st'' with
          | HasProof prf' => HasProof nil
          | HasModel prf' => HasModel nil
          | Timeout prf   => Timeout nil
          | Done st       => Done st
          end
        | HasModel m => prover_arrows g st l
        | Timeout st' => Timeout (st'::nil)
        | Done st'    => Done st'
        end
      end.
    Proof.
      destruct l;reflexivity.
    Qed.

  End P.

  Definition cons_proof (st:state) (g: option HFormula) (s : status (list (ptree sequent)))  : status (ptree sequent) :=
    match s with
    | HasProof l => HasProof (Deriv (mksq st g) l)
    | HasModel l => HasModel (Deriv (mksq st g) l)
    | Timeout  l => Timeout (Deriv (mksq st g) l)
    | Done st    => Done st
    end.

  Fixpoint prover (n:nat)  (g : option HFormula) (st:state)  : status (ptree sequent) :=
    match unit_propagation n st g with
    | Success => HasProof (Deriv (mksq st g) nil)
    | Progress st' => match n with
                  | O => Timeout (Deriv (mksq st g) nil)
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
      | Success => HasProof (Deriv (mksq st g) nil)
      | Progress st' => match n with
                        | O => Timeout (Deriv (mksq st g) nil)
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

  Fixpoint eval_list (l:list literal) :=
    match l with
    | nil => False
    | l::r => eval_literal l \/ eval_list r
    end.

  Lemma eval_list_split_of_cclause : forall c,
       (eval_clause c -> False) <->
       (eval_list (split_of_cclause c) -> False).
  Proof.
    induction c ; simpl.
    - tauto.
    - tauto.
    - tauto.
  Qed.

  Lemma eval_clause_of_clause_kind :
    forall cl cl',
      eval_clause_kind cl ->
      clause_of_clause_kind cl = Some cl' ->
      eval_clause cl'.
  Proof.
    destruct cl; simpl.
    - tauto.
    - intros. inv H0.
      simpl. tauto.
    - intros. inv H0 ; auto.
    - discriminate.
  Qed.

  Lemma wf_clause_of_clause_kind :
    forall m cl cl',
      has_clause_kind m cl ->
      clause_of_clause_kind cl = Some cl' ->
      has_clause m cl'.
  Proof.
    destruct cl; simpl.
    - intros. inv H0.
      simpl ; auto.
    - intros. inv H0.
      simpl. tauto.
    - intros. inv H0 ; auto.
      tauto.
    - discriminate.
  Qed.


  Lemma find_clause_kind_correct :
    forall m u ln cl
           (FD : find_clause_kind u ln = Some cl)
           (EU : eval_units m u)
           (WL : Forall (has_clause m) ln)
           (EV : Forall eval_clause  ln),
      eval_clause cl.
  Proof.
    induction ln ; simpl.
    - discriminate.
    - intros.
      inv WL ; inv EV.
      destruct (clause_of_clause_kind (shorten_clause u a true)) eqn: FD';
        try discriminate.
      +
        inv FD.
        eapply eval_clause_of_clause_kind ; eauto.
        apply shorten_clause_correct with (m:=m); auto.
      +  eauto.
  Qed.

  Lemma wf_find_clause_kind :
    forall m u ln cl
           (FD : find_clause_kind u ln = Some cl)
           (WL : Forall (has_clause m) ln),
           has_clause m cl.
  Proof.
    induction ln ; simpl.
    - discriminate.
    - intros.
      inv WL.
      destruct (clause_of_clause_kind (shorten_clause u a true)) eqn: FD';
        try discriminate.
      +
        inv FD.
        eapply wf_clause_of_clause_kind ; eauto.
        apply wf_shorten_clause with (m:=m); auto.
      +  eauto.
  Qed.



  Lemma find_split_correct :
    forall m u cls b cl
           (FD : find_split_clause u b cls = Some cl)
           (EU : eval_units m u)
           (WF : has_clauses m cls)
           (EV : eval_clauses m cls),
      has_clause m cl /\ eval_clause cl .
  Proof.
    intros m u cls b.
    unfold  find_split_clause.
    rewrite IntMap.fold_1.
    set (F := (fun (a : option clause) (p : IntMap.key * (list clause * list clause)) =>
     find_split_acc u b (fst p) (snd p) a)).
    generalize (@IntMap.elements_2 _ cls).
    assert (ACC : match None with
                  | Some cl' => has_clause m cl' /\ eval_clause cl'
                  | None     => True
           end). auto.
    revert ACC.
    generalize (None (A:= clause)).
    generalize ((IntMap.elements (elt:=list clause * list clause) cls)).
    induction l.
    - simpl. intros.
      destruct o ; try congruence.
    - intros.
      simpl in FD.
      apply IHl in FD. auto.
      unfold F.
      unfold find_split_acc.
      destruct a as (i,(ln,lp)).
      assert (FIND : IntMap.MapsTo i (ln,lp) cls).
      {
        apply H.
        constructor.
        apply Equivalence_Reflexive.
      }
      apply IntMap.find_1 in FIND.
      assert (FIND' := FIND).
      apply EV in FIND.
      apply WF in FIND'.
      destruct FIND as (EVLN & EVLP).
      destruct FIND' as (WFLN & WFLP).
      destruct o.
      +  auto.
      + unfold snd,fst.
        destruct lp.
        destruct b.
        destruct (find_clause_kind u ln) eqn:FD' ; auto.
        split.
        eapply wf_find_clause_kind ; eauto.
        eapply find_clause_kind_correct ; eauto.
        auto.
        destruct (find_clause_kind u (c::lp)) eqn:FD' ; auto.
        inv EVLP ; inv WFLP; auto.
        split.
        eapply wf_find_clause_kind ; eauto.
        eapply find_clause_kind_correct ; eauto.
      +  intros.
         apply H.
         apply InA_cons_tl; auto.
      +   auto.
      + auto.
      + auto.
  Qed.

  Lemma  split_of_clause_correct : forall g c l
      (SP : split_of_clause (is_classic g) c = Some l),
      (eval_list l -> eval_ohformula g) -> (eval_clause c -> eval_ohformula g).
  Proof.
    unfold split_of_clause.
    destruct g; simpl ; intros.
    - apply H.
      clear H.
      revert l SP.
      induction c ; simpl in *.
      + intros. tauto.
      + congruence.
      + intros. destruct (split_of_iclause c) eqn:EQ.
        inv SP. simpl.
        destruct H0; try tauto.
        specialize (IHc H l0 eq_refl).
        tauto. congruence.
    - inv SP.
       induction c ; simpl in * ; try tauto.
  Qed.

  Lemma wf_split_of_clause : forall m b c l,
      has_clause m c ->
      split_of_clause b c = Some l ->
      Forall (has_literal m) l.
  Proof.
    unfold split_of_clause.
    destruct b.
    - intros.
      inv H0.
      induction c ; simpl in *.
      + constructor.
      + constructor ; tauto.
      +  constructor ; tauto.
    -
      induction c ; simpl; intros.
      + inv H0. constructor.
      + congruence.
      + destruct (split_of_iclause c) eqn:EQ ; try congruence.
        inv H0.
        specialize (IHc l0).
        constructor ; tauto.
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
      destruct (is_arrow (elt (form_of_literal a))); auto.
      destruct (find_lit a (units st));auto.
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
        unfold find_split in FD.
        destruct (find_split_clause (units st0) (is_classic g) (clauses st0)) eqn:FD1;try congruence.
        apply find_split_correct with (m:=m) in FD1.
        { destruct FD1 as (WFC & EC).
          revert EC.
          apply split_of_clause_correct with (l:=l); auto.
          assert (WFL := wf_split_of_clause _ _ _ _ WFC FD).
          {
            apply cons_proof_inv in SUC.
            destruct SUC as (prf'' & SUC).
            revert prf'' st0 ES WFS0 SUC.
            clear FD.
          induction l; simpl.
          - tauto.
          - intros.
            destruct (prover n g (insert_unit a st0)) eqn:C; try congruence.
            destruct (forall_dis (prover n) g st0 l) eqn:D; try congruence.
            inv SUC.
            destruct H.
            +
              assert (WSI : wf_state m (insert_unit a st0)).
              { apply wf_insert_unit ; auto. inv WFL ; auto. }
              assert (EVI : eval_state m (insert_unit a st0)).
              { apply eval_state_insert_unit ; auto. }
              specialize (IHn g _ p WFm WSI WFG EVI).
              rewrite C in IHn.
              auto.
            +
              eapply IHl ; eauto.
              inv WFL ; auto.
          }
        }
        destruct ES ; auto.
        destruct WFS0 ; auto.
        destruct ES ; auto.
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
            destruct (intro_state st0 (elt (form_of_literal a)) (id (form_of_literal a))
             (is_dec (form_of_literal a))) as (st',g') eqn:EQ .
            inv H.
            destruct (prover n g' st') eqn:P ; try discriminate.
            +
              destruct ( prover n g (add_unit_in_stack (POS (form_of_literal a)) st0)) eqn:SUC' ; try congruence.
              assert (WFST' : wf_state m st' /\ has_oform m g').
              {
                apply wf_intro_state with (m:= m) in EQ; auto.
                apply has_form_of_literal in H2.
                destruct (form_of_literal a) ; simpl ; auto.
              }
              destruct WFST' as (WFST' & WFG').
              assert (eval_state m st' -> eval_ohformula g').
              {
                intro. revert P.
                apply IHn ; auto.
              }
              assert (eval_formula (elt (form_of_literal a))).
              { apply intro_state_correct with (m:=m)(3:=EQ); eauto.
                apply has_form_of_literal in H2.
                destruct (form_of_literal a) ; simpl ; auto.
              }
              clear H.
              eapply IHn  in SUC' ; auto.
              apply wf_add_unit_in_stack;auto.
              destruct a ; simpl in * ; auto.
              apply eval_state_add_unit_in_stack;auto.
            +
              destruct (prover_arrows (prover n) g st0) eqn:S; try congruence.
              inv SUC.
              revert S.
              eapply IHl ; eauto.
        }
  Qed.

  Definition wf_entry (p : Formula -> bool) (v : option (bool * Formula)) :=
    match v with
    | None => false
    | Some(b,f) => p f && Bool.eqb b true
    end.


  Definition wfb (m:hmap) : bool :=
    (wf_entry is_FF (IntMap.find 0 m))
    &&
    (wf_entry is_TT (IntMap.find 1 m)).

  Lemma wfb_correct : forall m, wfb m = true -> wf m.
  Proof.
    intros.
    unfold wfb in H.
    rewrite andb_true_iff in H.
    destruct H.
    constructor ; intros.
    - unfold wf_entry in H.
      destruct (IntMap.find (elt:=bool * Formula) 0 m) ; try congruence.
      destruct p.
      rewrite andb_true_iff in H.
      destruct H.
      rewrite Bool.eqb_true_iff in H1. subst.
      destruct f ; simpl in H ; try congruence.
    - unfold wf_entry in H0.
      destruct (IntMap.find (elt:=bool * Formula) 1 m) ; try congruence.
      destruct p.
      rewrite andb_true_iff in H0.
      destruct H0.
      rewrite Bool.eqb_true_iff in H1. subst.
      destruct f ; simpl in H0 ; try congruence.
  Qed.


  Definition prover_formula (m: hmap) (n:nat) (f: HFormula)  :=
    if wfb m && chkHc m f.(elt) f.(id) f.(is_dec)
    then
      let (st,g) := intro_state (add_unit_in_stack (POS hTT) empty_state) f.(elt) f.(id) f.(is_dec) in
      prover n g st
    else HasModel (Leaf false).



  Lemma wf_empty : forall m,
      wf_state m empty_state.
  Proof.
    unfold empty_state.
    constructor ; simpl ; auto.
    - unfold order_dom.
      intros.
      rewrite IntMapF.F.empty_o in H.
      congruence.
    - repeat intro.
      rewrite IntMapF.F.empty_o in H.
      congruence.
  Qed.

  Lemma eval_state_empty : forall m, eval_state m empty_state.
  Proof.
    unfold empty_state.
    constructor ; simpl ; auto.
    - unfold eval_units.
      intros.
      rewrite IntMapF.F.empty_o in H.
      congruence.
    -  constructor.
    - repeat intro.
      rewrite IntMapF.F.empty_o in H.
      congruence.
  Qed.

  Lemma prover_formula_correct : forall m n f prf,
      prover_formula m n f = HasProof prf ->
      eval_hformula f.
  Proof.
    unfold prover_formula.
    intros.
    destruct (wfb m && chkHc m (elt f) (id f) (is_dec f)) eqn:EQ ; try congruence.
    rewrite andb_true_iff in EQ.
    destruct EQ as (WFM & CHK).
    apply wfb_correct in WFM.
    apply chkHc_has_form in CHK; auto.
    destruct (intro_state (add_unit_in_stack (POS hTT) empty_state) (elt f) (id f) (is_dec f)) eqn:I.
    assert (I':= I).
    assert (WFE : wf_state m empty_state). apply wf_empty.
    assert (EVE : eval_state m empty_state). apply eval_state_empty.
    apply wf_add_unit_in_stack with (l:= POS hTT) in WFE.
    apply eval_state_add_unit_in_stack with (l:= POS hTT) in EVE.
    apply wf_intro_state with (m:=m) in I; auto.
    apply intro_state_correct with (m:= m) in I' ; auto.
    destruct I as (WFS & F).
    intro.
    specialize (prover_correct m n _ _ prf  WFM WFS F H0).
    destruct (prover n o s) ; try congruence.
    simpl ; tauto.
    simpl. auto.
    constructor. apply wf_true;auto.
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
                    let m := IntMap.add f1.(id) (f1.(is_dec), f1.(elt)) m in
                    IntMap.add f2.(id) (f2.(is_dec), f2.(elt)) m
    end.

  Definition hmap_empty := IntMap.add 0 (true, FF) (IntMap.add 1 (true,TT) (IntMap.empty _)).

  Definition hcons_form (f : HFormula) : hmap :=
    IntMap.add f.(id) (f.(is_dec),f.(elt)) (hcons hmap_empty f.(elt)).

  Definition hcons_prover (n:nat) (f:HFormula) :=
    let m := hcons_form f in
    prover_formula m n f.

  Lemma hcons_prover_correct : forall n f prf,
      hcons_prover n f = HasProof prf ->
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
  match IntMap.find i m with
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
Register IntMap.add   as cdcl.IntMap.add.


Lemma hcons_prover_int_correct : forall f p eval_atom,
    hcons_prover Int63.eqb (fun _ => false) 20%nat f  = HasProof _ p -> eval_hformula eval_atom f.
Proof.
  intros f prf eval_atom.
  apply hcons_prover_correct; eauto.
  -  intros. apply Int63.eqb_correct ;auto.
  -  congruence.
Qed.

Definition show_units (h:hmap) (u : IntMap.t bool) : list (@literal int) :=
  IntMap.fold (fun i v (acc:list literal) => match IntMap.find i h with
                              | None => acc
                              | Some (b,f) => (literal_of_bool v (HCons.mk i b f)) :: acc
                              end) u nil.

Definition show_clauses (cl : @map_clauses int) :=
  IntMap.fold (fun i '(l1,l2) acc => (l1++l2)++acc) cl nil.

Definition show_state (h:hmap) (st: @state int) :=
  (show_units h (units st), unit_stack st , show_clauses (clauses st)).
