(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Cdcl.PatriciaR Cdcl.KeyInt Cdcl.ReifClasses Cdcl.Coqlib.
Require Import  Bool Setoid ZifyBool  ZArith Int63 Lia List.
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

Lemma compare_refl : forall i, (i ?= i)%int63 = Eq.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  replace (i <? i)%int63 with false by lia.
  replace (i =? i)%int63 with true by lia.
  reflexivity.
Qed.

Lemma compare_Eq : forall x y, (x ?= y)%int63 = Eq <-> (x =? y = true)%int63.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  destruct (x <?y)%int63 eqn:LT; try congruence.
  intuition (congruence || lia).
  destruct (x =?y)%int63 ;   intuition (congruence || lia).
Qed.

Lemma compare_Lt : forall x y, (x ?= y)%int63 = Lt <-> (x <? y = true)%int63.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  destruct (x <?y)%int63 eqn:LT; try congruence.
  intuition (congruence || lia).
  destruct (x =?y)%int63 ;   intuition (congruence || lia).
Qed.

Lemma compare_Gt : forall x y, (x ?= y)%int63 = Gt <-> (y <? x = true)%int63.
Proof.
  intros.
  rewrite compare_def_spec.
  unfold compare_def.
  destruct (x <?y)%int63 eqn:LT; try congruence.
  intuition (congruence || lia).
  destruct (x =?y)%int63 eqn:EQ;   intuition (congruence || lia).
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

    Definition eq_hc (f1 f2 : t) := (id f1 =? id f2)%int63 && Bool.eqb (is_dec f1) (is_dec f2).


  End S.

  Definition map [A B] (f: A -> B) (e: t A) : t B :=
    mk _ (id _ e) (is_dec _ e) (f (elt _ e)).

End HCons.
Import HCons.

Arguments HCons.mk {A} id is_dec elt.
Arguments HCons.elt {A} .
Arguments HCons.id {A} .
Arguments HCons.is_dec {A} .
Arguments HCons.eq_hc {A}.

Module IntMap  := PatriciaR.PTrie.

Arguments IntMap.ptrie [key] A.

Inductive op :=
| AND | OR | IMPL.
(* IFF - is complicated.  The main reason is that the clausal encoding
   introduces IMPL.  Those are not sub-formulae and therefore this
   requires some ad'hoc specific treatment *)

  Inductive kind : Type :=
  |IsProp
  |IsBool.

  Inductive BForm  : kind -> Type :=
  | BTT   : forall (k: kind), BForm k
  | BFF   : forall (k: kind), BForm k
  | BAT   : forall (k: kind), int -> BForm k
  | BOP   : forall (k: kind), op -> HCons.t (BForm k) ->
                             HCons.t (BForm k) -> (BForm k)
  | BIT   : (BForm IsBool) -> BForm IsProp.


  Inductive lop := LAND | LOR.

  Inductive LForm : Type :=
  | LFF
  | LAT : int -> LForm
  | LOP : lop -> list (HCons.t LForm) -> LForm
  | LIMPL : list (HCons.t LForm) ->  (HCons.t LForm)  -> LForm.


  Definition HFormula : Type := HCons.t LForm.


  Section MaxList.

    Variable Depth : LForm -> nat.

    Definition max_list (l: list (HCons.t LForm)) :=
      List.fold_right (fun e acc => max (Depth e.(elt)) acc) O l.

    Lemma in_max_elt : forall l x (IN: In x l),
        Depth (elt x) < S(max_list  l).
    Proof.
      induction l; simpl ; auto.
      - tauto.
      - intros. destruct IN ; simpl; auto.
        subst. lia.
        apply IHl in H.
        lia.
    Qed.

  End MaxList.


  Section FormInd.

  Fixpoint depth (f:LForm) : nat :=
    match f with
    | LFF    => O
    | LAT _ => O
    | LOP _ l => S (max_list depth l)
    | LIMPL l r => S (max (max_list depth l) (depth r.(elt)))
    end.

    Variable P : LForm -> Prop.

    Variable PF : P LFF.

    Variable PA : forall a, P (LAT a).

    Variable PLOP : forall o l,
        (forall x, In x l -> P (x.(elt))) ->  P (LOP o l).


    Variable PLIMP : forall l r,
        (forall x, In x l -> P (x.(elt))) ->
        (P r.(elt)) ->  P (LIMPL l r).

    Lemma form_ind : forall f, P f.
    Proof.
      intro f.
      remember (depth f) as n.
      revert f Heqn.
      induction n using Wf_nat.lt_wf_ind.
      destruct n.
      - destruct f ; simpl; auto; try discriminate.
      - destruct f; simpl ; try discriminate; intros.
        + apply PLOP; intros.
          apply (H (depth (elt x))); auto.
          inv Heqn.
          apply in_max_elt; auto.
        + intros.
          apply PLIMP; intros.
          *  apply (H (depth (elt x))); auto.
             inv Heqn.
             apply in_max_elt with (Depth:= depth) in H0.
             lia.
          *  apply (H (depth (elt t0))); auto.
             inv Heqn. lia.
    Qed.

  End FormInd.



  Definition FF := LFF.
  Definition TT := (LOP LAND nil).

  Definition lop_eqb (o o': lop) : bool :=
    match o , o' with
    | LAND , LAND => true
    | LOR  , LOR  => true
    | _ , _ => false
    end.

  Fixpoint lform_app (o:lop) (acc : list (HCons.t LForm)) (l: list (HCons.t LForm)) :=
    match l with
    | nil => acc
    | e :: l => match e.(elt) with
                | LOP o' l' => if lop_eqb o o'
                               then lform_app o (rev_append l' acc) l
                               else lform_app o (e::acc) l
                | LFF   => match o with
                           | LOR => lform_app o acc l
                           | LAND => e::nil
                           end
                | _ => lform_app o (e::acc) l
                end
    end.


  Definition mk_impl (l : list HFormula) (r : HFormula) : LForm :=
    match r.(elt) with
    | LIMPL l' r' => LIMPL (rev_append l l') r'
    | _      => LIMPL l r
    end.

    Definition  hFF := HCons.mk 0 true FF.
    Definition  hTT := HCons.mk 1 true TT.

  Definition is_TT (g: LForm) : bool :=
    match g with
    | LOP LAND nil => true
    | _  => false
    end.

  Lemma is_TT_true : forall f, is_TT f = true -> f = TT.
  Proof.
    destruct f ; simpl; try congruence.
    destruct l ; try congruence.
    destruct l0; try congruence.
    reflexivity.
  Qed.

  Definition mklform  (f : HFormula)  : HFormula :=
    if is_TT f.(elt) then hTT else f.

  Definition nform (F: LForm -> LForm) (f: HFormula) :=
    match F (elt f) with
    | LFF => hFF
    | LOP LAND nil => hTT
    | LAT i        => HCons.mk i (is_dec f) (LAT i)
    |   r          => HCons.mk (id f) (is_dec f) r
    end.

  Definition mk_op (o: lop) (l: list HFormula) :=
    match l with
    | nil => match o with
             | LOR => LFF
             |  _  => LOP o l
             end
    | e::nil => e.(elt)
    |   _    => LOP  o l
    end.


  Fixpoint lform (f : LForm) :=
    match f with
    | LFF   => LFF
    | LAT i => LAT i
    | LOP o l => LOP o (lform_app o nil (List.map (nform lform) l))
    | LIMPL l r => mk_impl
                     (lform_app LAND nil (List.map (nform lform) l))
                     (HCons.map lform r)
    end.


  Open Scope int63.


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


  Lemma lop_eqb_true : forall o o',
      lop_eqb o o' = true -> o = o'.
  Proof.
    destruct o,o' ; simpl ; intuition congruence.
  Qed.



  Definition hmap := IntMap.ptrie (key:=int) (bool*LForm)%type.


  Inductive literal : Type :=
  | POS (f:HFormula)
  | NEG (f:HFormula).

  Definition wf_map  {A: Type} (m : IntMap.ptrie A) := PTrie.wf None m.

  Module OBool.
    Definition t := option bool.

    Definition union (o1 o2: option bool) : option bool :=
      match o1 , o2 with
      | Some b1 , Some b2 => if Bool.eqb b1 b2 then o1 else None
      | _ , _ => None
      end.

    Definition has_boolb (b: bool) (o: option bool) :=
      match o with
      | None => true
      | Some b' =>  Bool.eqb b  b'
      end.

    Definition has_bool (b: bool) (o: option bool) := has_boolb b o = true.

    Definition lift_has_boolb (b:bool) (o : option (option bool)) :=
      match o with
      | None => false
      | Some o' => has_boolb b o'
      end.

    Definition lift_has_bool (b:bool) (o : option (option bool)) :=
      lift_has_boolb b o = true.


    Definition order (o o': option bool) :=
      match o , o' with
      | None , None | Some _ , None => True
      | Some b , Some b' => b = b'
      | None , Some b => False
      end.

    Definition lift_order (o o' : option (option bool)) :=
      match o , o' with
      | None , None   => True
      | None , Some _ => True
      | Some _ , None => False
      | Some b1 , Some b2 => order b1 b2
      end.

    Lemma order_refl : forall b, order b b.
    Proof.
      destruct b ; simpl; auto.
    Qed.

    Lemma order_trans : forall b1 b2 b3,
        order b1 b2 -> order b2 b3 -> order b1 b3.
    Proof.
      destruct b1,b2,b3; simpl; intuition congruence.
    Qed.

    
    Lemma order_union_l : forall b b',
        order b (union b b').
    Proof.
      destruct b,b'; simpl; auto.
      destruct (Bool.eqb b b0) eqn:E; auto.
    Qed.

    Lemma order_union_r : forall b b',
        order b' (union b b').
    Proof.
      destruct b,b'; simpl; auto.
      destruct (Bool.eqb b b0) eqn:E; auto.
      apply eqb_prop in E. congruence.
    Qed.

    Lemma has_bool_union : forall b o1 o2,
        (has_bool b o1 \/ has_bool b o2)  <->
        has_bool b (union o1 o2).
    Proof.
      unfold has_bool.
      destruct o1, o2; simpl ; intuition.
      - rewrite Bool.eqb_true_iff in H0.
        subst.
        destruct (Bool.eqb b0 b1) eqn:E;simpl;auto.
        apply Bool.eqb_reflx.
      - rewrite Bool.eqb_true_iff in H0.
        subst.
        destruct (Bool.eqb b0 b1) eqn:E;simpl;auto.
        rewrite Bool.eqb_true_iff in *. congruence.
      -
        destruct (Bool.eqb b0 b1) eqn:E;simpl in H ; try congruence.
        +
          apply eqb_prop in E. subst. tauto.
        +
          simpl in *. destruct b;destruct b0 ; destruct b1 ; simpl in *; intuition congruence.
    Qed.
  End OBool.



  Module LitSet.
    (** Set of literals.
        Though this may not occur in practice,
        in general, we may have (POS l) and (NEG l), this is encoded by None *)

    Definition t := IntMap.ptrie (key:= int) OBool.t.

    Definition empty : t := IntMap.empty OBool.t.


    Definition union (s s':t) : t := IntMap.combine' OBool.union s s'.

    Definition singleton (i:int) (b:bool) := IntMap.Leaf OBool.t i (Some b).

    Definition add (k:int) (b:bool) (s:t) : t := union (singleton k b) s.

    Definition fold {A: Type} : forall  (f: A -> int -> OBool.t -> A) (s:t) (a:A), A := @IntMap.fold' int OBool.t A.

    Definition mem (i:int) (s:t)  := IntMap.mem' i s.

    Definition get (i:int) (s:t)  := IntMap.get' i s.

    Definition remove (i:int) (s:t) := IntMap.remove' i s.


    Definition has (i:int) (b:bool) (s:t) :=
      OBool.lift_has_boolb b (get i s).

    Definition subset (s s':t) := forall k,
        OBool.lift_order (get k s) (get k s').

    Definition wf (s:t) := wf_map s.

    Lemma mem_empty : forall k, mem k empty = false.
    Proof. reflexivity. Qed.

    Lemma subset_trans : forall s1 s2 s3,
        subset s1 s2 -> subset s2 s3 ->
        subset s1 s3.
    Proof.
      unfold subset.
      intros.
      specialize (H k); specialize (H0 k).
      destruct (get k s1), (get k s2) , (get k s3) ; simpl in *;
        try tauto.
      eapply OBool.order_trans; eauto.
    Qed.

    Lemma subset_union_l : forall s s', wf_map s -> wf_map s' -> subset s (union s s').
    Proof.
      unfold subset,union,get, wf_map.
      intros.
      rewrite IntMap.gxcombine' with (opt:=None); auto.
      change (option bool) with OBool.t.
      destruct (IntMap.get' k s) ; simpl.
      destruct (IntMap.get' k s').
      apply OBool.order_union_l.
      apply OBool.order_refl.
      destruct (IntMap.get' k s') ; simpl; auto.
    Qed.

    Lemma subset_union_r : forall s s', wf_map s -> wf_map s' -> subset s' (union s s').
    Proof.
      unfold subset,union, wf_map.
      unfold get.
      intros.
      rewrite IntMap.gxcombine' with (opt:=None); auto.
      change (option bool) with OBool.t.
      destruct (IntMap.get' k s') ; simpl.
      destruct (IntMap.get' k s); simpl.
      apply OBool.order_union_r.
      apply OBool.order_refl.
      destruct (IntMap.get' k s); simpl; auto.
    Qed.


    Lemma mem_union :
      forall k s s'
             (WFT: wf s)
             (WFT': wf s'),
             (mem k s = true \/ mem k s' = true) <-> mem k (union s s') = true.
    Proof.
      unfold mem, union.
      intros. repeat rewrite IntMap.gmem'.
      rewrite IntMap.gxcombine' with (opt:=None) ; auto.
      change (option bool) with OBool.t.
      destruct (IntMap.get' k s).
      destruct (IntMap.get' k s') ; auto.
      simpl. intuition congruence.
      simpl. intuition congruence.
      destruct (IntMap.get' k s') ; simpl ; intuition congruence.
    Qed.

    Lemma lift_has_bool_union :
      forall b i d1 d2
             (WFT: wf d1)
             (WFT': wf d2),
        (OBool.lift_has_bool b (get i d1) \/
         OBool.lift_has_bool b (get i d2) ) <->
        OBool.lift_has_bool b
                            (get i (union d1 d2)).
    Proof.
      intros.
      unfold get, union, OBool.lift_has_bool.
      rewrite IntMap.gxcombine' with (opt:=None) ; auto.
      change (option bool) with OBool.t.
      destruct (IntMap.get' i d1).
      - simpl.
        destruct (IntMap.get' i d2) ; auto.
        apply OBool.has_bool_union.
        simpl. intuition congruence.
      - simpl.
        destruct (IntMap.get' i d2) ; simpl; intuition congruence.
    Qed.

    Lemma wf_union :
      forall s s'
             (WFT: wf s)
             (WFT': wf s'),
             wf (union s s').
    Proof.
      unfold union.
      intros. apply IntMap.wf_xcombine'; auto.
    Qed.


  End LitSet.

  Module Annot.

    Record t (A: Type) : Type := mk
    {
      elt : A;
      deps : LitSet.t (* Set of formulae that are needed to deduce elt *)
    }.

    Global Arguments mk {A}.
    Global Arguments elt {A}.
    Global Arguments deps {A}.

    Definition set {A B: Type} (a : t A) (e: B) :=
      mk e (deps  a).

    Definition map {A B: Type} (f : A -> B) (a: t A) : t B :=
      mk  (f (elt a)) (deps a).

    Definition mk_elt {A: Type} (e:A) : t A := mk e LitSet.empty.


    Lemma map_map : forall {A B C: Type} (f: B -> C) (g: A -> B) (a: t A),
        map f (map g a) = map (fun x => f (g x)) a.
    Proof.
      destruct a. reflexivity.
    Qed.

    Lemma map_id : forall {A: Type} (f:A -> A) x,
        (forall x, (f x = x)) ->
      map f x = x.
    Proof.
      destruct x; unfold map ; simpl.
      intros. congruence.
    Qed.

    Definition lift {A B: Type} (f: A -> B) (e : t A): B :=
      f (elt e).

    Definition lift_deps {A: Type} (f : LitSet.t -> Prop) (e: t A) :=
      f (deps e).

    Lemma lift_pred :
      forall {A: Type} (P Q : A -> Prop)
             (PQ : forall x, P x -> Q x)
             e,
        lift P e -> lift Q e.
    Proof.
      unfold lift.
      auto.
    Qed.

  End Annot.



  Module Prf.

    Inductive cnfOp :=
    | Proj1 (* [A /\ B] -> A *)
    | Proj2 (* [A /\ B] -> B *)
    | Conj  (* A -> B -> [A /\ B] *)
    | Or_introl (* A -> [A \/ B] *)
    | Or_intror (* B -> [A \/ B] *)
    | Or_dest   (* [A \/ B] -> A \/ B *)
    | Impl_introW (* B -> [A -> B] *)
    | Impl_introS (* A \/ [A -> B] *)
    | Impl_dest   (* [A -> B] -> A -> B *).

    Inductive t :=
    | Intro (f:HFormula)
    | Tauto (c:cnfOp) (f: HFormula)
    | MP (p1: HCons.t t) (cl: HCons.t t)
    | Case (i:int) (cl : HCons.t t).

  End Prf.


  Fixpoint forall2b {A B: Type} (F : A -> B -> bool) (l1 : list A) (l2 : list B) : bool :=
    match l1 , l2 with
    | nil , nil => true
    | e1::l1', e2::l2' => F e1 e2 && forall2b F l1' l2'
    | _      , _       => false
    end.

  Section S.

    Variable AT_is_dec : int -> bool.


    Definition chkHc_list  (l1 l2 : list HFormula) :=
      forall2b HCons.eq_hc l1 l2.

    Fixpoint chkHc (m: hmap) (f:LForm) (i:int) (b:bool) : bool :=
      match f with
      | LFF   => match IntMap.get' i m with
                 | Some(b',LFF) => Bool.eqb b b'
                 |  _   => false
                 end
      | LAT a => match IntMap.get' i m with
                 | Some(b',LAT a') => (a =? a') && Bool.eqb b (AT_is_dec a) && Bool.eqb b b'
                 |  _   => false
                 end
      | LOP o l => List.forallb (fun f => chkHc m f.(elt) f.(id) f.(is_dec)) l
                  &&
                  match IntMap.get' i m with
                  | Some (b',LOP o' l') =>
                    lop_eqb o o' &&
                    Bool.eqb b (forallb (fun f => f.(is_dec)) l) &&
                    Bool.eqb b b' && chkHc_list l l'
                  | _ => false
                  end
      | LIMPL l r => List.forallb (fun f => chkHc m f.(elt) f.(id) f.(is_dec)) l
                       && chkHc m r.(elt) r.(id) r.(is_dec)
                       && match IntMap.get' i m with
                          | Some (b',LIMPL l' r') =>
                            Bool.eqb b ((forallb is_dec l) && (is_dec r)) &&
                            Bool.eqb b b' && chkHc_list l l' && HCons.eq_hc r r'
                          | _ => false
                          end
      end.


  Record wf (m: IntMap.ptrie (bool * LForm)) : Prop :=
    {
    wf_false : IntMap.get' 0 m = Some (true,FF);
    wf_true : IntMap.get' 1 m = Some (true,TT);
    }.

    Inductive has_form (m:hmap) : HFormula -> Prop :=
    | wf_FF  : forall i b, IntMap.get' i m = Some (b,LFF) ->
                             has_form m (HCons.mk i b LFF)
    | wf_AT  : forall a i b, IntMap.get' i m = Some (b,LAT a) -> AT_is_dec a = b ->
                             has_form m (HCons.mk i b (LAT a))
    | wf_OP : forall o l l' i b,
        Forall (has_form m) l ->
        IntMap.get' i m = Some (b,LOP o l') ->
        chkHc_list l l' = true ->
        (b = forallb is_dec l) ->
        has_form m (HCons.mk i b (LOP o l))
    | wf_IMPL :
        forall l r l' r' i b,
          Forall (has_form m) l ->
          has_form m r ->
          IntMap.get' i m = Some (b,LIMPL l' r') ->
          chkHc_list l l' = true ->
          HCons.eq_hc r r' = true ->
          (b = forallb is_dec l && is_dec r) ->
          has_form m (HCons.mk i b (LIMPL l r)).

  Lemma chkHc_has_form : forall m f i b
(*      (WF: wf m) *),
      chkHc m f i b = true -> has_form m (HCons.mk i b f).
  Proof.
    intros m f i.
    revert i.
    induction f using form_ind.
    - simpl. intros.
      destruct (@IntMap.get' _ KInt _ i m) eqn:EQ; try congruence.
      destruct p as (b',f).
      destruct f ; try congruence.
      rewrite! eqb_true_iff in H.
      subst. constructor; auto.
    - simpl. intros.
      destruct (@IntMap.get' _ KInt _ i m) eqn:EQ; try congruence.
      destruct p as (b',f).
      destruct f ; try congruence.
      rewrite! andb_true_iff in H.
      rewrite! eqb_true_iff in H.
      destruct H as ((H1, H2),H3).
      subst.
      assert (a = i0) by lia ; subst.
      econstructor ; eauto.
    - simpl ; intros.
      repeat rewrite andb_true_iff in H0.
      destruct H0 as (ALL & GET).
      destruct (@IntMap.get' _ KInt _ i m)eqn:FIND; try congruence.
      destruct p as (b',f).
      destruct f ; intuition try congruence.
      rewrite! andb_true_iff in GET.
      destruct GET  as (((EQOP & ALLDEC) & EQB) & CHECK).
      rewrite eqb_true_iff in *. subst.
      apply lop_eqb_true in EQOP. subst.
      apply wf_OP with (l:= l) in FIND;auto.
      +
        rewrite forallb_forall in ALL.
        rewrite Forall_forall.
        intros.
        specialize (H _ H0 _ _ (ALL _ H0)).
        destruct x; auto.
    - simpl ; intros.
      repeat rewrite andb_true_iff in H0.
      destruct H0 as ((ALL1 & ALL2) & GET).
      destruct (@IntMap.get' _ KInt _ i m)eqn:FIND; try congruence.
      destruct p as (b',f).
      destruct f ; intuition try congruence.
      rewrite! andb_true_iff in GET.
      destruct GET  as (((EQOP & ALLDEC) & EQB) & CHECK).
      rewrite eqb_true_iff in *. subst.
      apply wf_IMPL with (l:= l) (r:=r) in FIND;auto.
      +
        rewrite forallb_forall in ALL1.
        rewrite Forall_forall.
        intros.
        specialize (H _ H0 _ _ (ALL1 _ H0)).
        destruct x; auto.
      +
        apply IHf in ALL2.
        destruct r; auto.
  Qed.

  Lemma forall2_eq_list : forall {A: Type} (l1 l2: list A),
      Forall2 (@eq A) l1 l2 -> l1 = l2.
  Proof.
    intros.
    induction H; auto.
    congruence.
  Qed.

  Lemma forall2b_rtrans  : forall {A: Type} (F : A -> A -> bool) l1 l2 l'
                                  (RTRANS : forall x y r, F x r = true ->
                                                           F y r = true -> F x y = true),
      forall2b F l1 l' = true ->
      forall2b F l2 l' = true ->
      forall2b F l1 l2 = true.
  Proof.
    induction l1 ; simpl.
    - destruct l' ; try congruence.
      destruct l2 ; simpl ; congruence.
    - destruct l' ; try congruence.
      intros.
      destruct l2 ; simpl in H0 ; try congruence.
      rewrite andb_true_iff in *.
      destruct H. destruct H0.
      split.
      eapply RTRANS ; eauto.
      eapply IHl1 ; eauto.
  Qed.

  Lemma eq_hc_trans : forall {A:Type} [x y r:HCons.t A],
      HCons.eq_hc x r = true -> eq_hc y r = true -> HCons.eq_hc x y = true.
  Proof.
    intros. unfold eq_hc in *.
    rewrite andb_true_iff in *.
    rewrite Bool.eqb_true_iff in *.
    destruct H; destruct H0 ; intuition try congruence.
    lia.
  Qed.

  Lemma chkHc_list_rtrans : forall l1 l2 l',
      chkHc_list l1 l' = true ->
      chkHc_list l2 l' = true ->
      chkHc_list l1 l2 = true.
  Proof.
    intros.
    eapply forall2b_rtrans; eauto.
    eapply eq_hc_trans.
  Qed.

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


  Lemma has_form_eq :
    forall m f1 f2
           (HASF1: has_form m f1)
           (HASF2: has_form m f2)
           (EQ   : f1.(id) = f2.(id)),
      f1 =  f2.
  Proof.
    intros m f1.
    destruct f1 as (i,b,f1).
    simpl. intros. subst.
    revert b f2 HASF1 HASF2.
    assert (SAMELIST :
              forall l l'0 l0
              (H : forall x : t LForm,
                  In x l ->
                  forall (b : bool) (f2 : HFormula),
                    has_form m {| id := id f2; is_dec := b; elt := elt x |} ->
                    has_form m f2 -> {| id := id f2; is_dec := b; elt := elt x |} = f2)
                (H4 : Forall (has_form m) l)
                (H6 : chkHc_list l l'0 = true)
                (H0 : Forall (has_form m) l0)
                (H2 : chkHc_list l0 l'0 = true),
              Forall2 eq l l0).
    {
      intros.
      specialize (chkHc_list_rtrans _ _ _ H6 H2).
      intro.
      apply forall2b_Forall2 in H1.
      clear H6 H2.
      induction H1.
      + constructor.
      +
        apply Forall_rew in H4.
        apply Forall_rew in H0.
        unfold eq_hc in H1.
        rewrite andb_true_iff in H1.
        rewrite Bool.eqb_true_iff in H1.
        destruct H1 ; subst.
        assert (id x = id y) by lia.
        constructor.
        *
        destruct x.
        simpl in  H5. subst.
        apply (H {| id := id y ; is_dec := is_dec0 ; elt := elt0 |}).
        simpl. tauto.
        tauto. tauto.
        * apply IHForall2; try tauto.
          intros.
          eapply H ; eauto.
          simpl. tauto.
    }
    induction f1 using form_ind.
    - intros.
      inv HASF1.
      inv HASF2; simpl in * ; congruence.
    - intros.
      inv HASF1.
      inv HASF2; simpl in * ; congruence.
    - intros.
      inv HASF1.
      inv HASF2; simpl in *; try congruence.
      rewrite H5 in H1. inv H1.
      f_equal. f_equal.
      apply forall2_eq_list.
      eapply SAMELIST; eauto.
    -  intros.
       inv HASF1.
       inv HASF2; simpl in *; try congruence.
       rewrite H6 in H2. inv H2.
       f_equal. f_equal.
       apply forall2_eq_list.
       eapply SAMELIST;eauto.
       eauto.
       specialize (eq_hc_trans H8 H9).
       intro.
       unfold eq_hc in H2.
       rewrite andb_true_iff in H2.
       rewrite Bool.eqb_true_iff in H2.
       destruct H2.
       assert (id r = id r0) by (clear - H2; lia).
       destruct r.
       simpl in *. subst.
       apply IHf1;auto.
  Qed.

  Variable eval_atom : int -> Prop.


  Definition eval_op (o: op) (f1 f2 : Prop) : Prop :=
    match o with
    | AND => f1 /\ f2
    | OR  => f1 \/ f2
    | IMP => f1 -> f2
    end.

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

  Fixpoint eval_formula (f: LForm) : Prop :=
    match f with
    | LFF   => False
    | LAT a => eval_atom a
    | LOP o l => eval_op_list (fun f => eval_formula f.(elt)) o l
    | LIMPL l r  => eval_impl_list (fun f => eval_formula f.(elt)) l (eval_formula r.(elt))
    end.

  Lemma eval_formula_rew : forall f,
      eval_formula f =
    match f with
    | LFF   => False
    | LAT a => eval_atom a
    | LOP o l => eval_op_list (fun f => eval_formula f.(elt)) o l
    | LIMPL l r  => eval_impl_list (fun f => eval_formula f.(elt)) l (eval_formula r.(elt))
    end.
  Proof. destruct f; reflexivity. Qed.



  Add Parametric Morphism (o:lop) : (eval_lop o) with signature iff ==> iff ==> iff as eval_lop_morph.
  Proof.
    destruct o; simpl; tauto.
  Qed.

  Lemma eval_mk_impl : forall l r,
      eval_formula (LIMPL l r) <-> eval_formula (mk_impl l r).
  Proof.
    unfold mk_impl.
    intros.
    destruct (elt r) eqn:EQ; try tauto.
    rewrite eval_formula_rew.
    symmetry.
    rewrite eval_formula_rew.
    rewrite<- !eval_impl_list_eq.
    rewrite! eval_and_list_eq.
    rewrite eval_and_list_rev_append.
    rewrite EQ.
    simpl. rewrite <- eval_impl_list_eq.
    rewrite eval_and_list_eq.
    tauto.
  Qed.

  Definition eval_hformula (f: HFormula) := eval_formula f.(elt).

  Lemma eval_mklform : forall f,
      eval_formula (elt (mklform f)) <-> eval_formula (elt f).
  Proof.
    unfold mklform.
    intros.
    destruct (is_TT (elt f)) eqn:EQ; try tauto.
    apply is_TT_true in EQ.
    rewrite EQ. simpl. tauto.
  Qed.

  Lemma eval_nform : forall
    (REC : forall f : LForm, eval_formula f <-> eval_formula (lform f)),
      forall f : HFormula, eval_hformula (nform lform f) <-> eval_hformula f.
  Proof.
    intro REC.
    intro.
    unfold eval_hformula.
    rewrite (REC (elt f)).
    unfold nform.
    destruct (lform (elt f)).
    - simpl. tauto.
    - simpl. tauto.
    - destruct l.
      destruct l0.
      + simpl. tauto.
      + unfold elt. tauto.
      + unfold elt. tauto.
    - unfold elt. tauto.
  Defined.

  Lemma eval_op_list_lform_app :
    forall (REC : forall f : LForm, eval_formula f <-> eval_formula (lform f))
           (o:lop) (l: list (t LForm)),
      eval_op_list (fun f : t LForm => eval_formula (elt f)) o l <->
      eval_op_list (fun f : t LForm => eval_formula (elt f)) o
    (lform_app o nil (List.map (nform lform) l)).
  Proof.
    intros.
    replace l  with (l++nil) at 1 by (rewrite app_nil_end; reflexivity).
    generalize (nil (A:= HCons.t LForm)).
    assert (forall f, eval_hformula (nform lform f) <-> eval_hformula f).
    {
      apply eval_nform; auto.
    }
    unfold eval_hformula in H.
    induction l.
    - simpl. tauto.
    - rewrite List.map_cons.
      simpl.
      destruct (elt (nform lform a)) eqn:EQ.
      + intros.
        rewrite! eval_op_list_cons.
        destruct o.
        * simpl. rewrite <- H.
          rewrite EQ. simpl.
          tauto.
        *
          rewrite IHl.
          simpl.  rewrite <- H.
          rewrite EQ. simpl.
          tauto.
      +
        intros.
        rewrite! eval_op_list_cons.
        rewrite <- IHl.
        rewrite !eval_op_list_app.
        rewrite eval_op_list_cons.
        rewrite <- (H a).
        rewrite EQ.
        destruct o ; simpl; tauto.
      +
        destruct (lop_eqb o l0) eqn:OP.
        * apply lop_eqb_true in OP.
          subst.
          intros.
          rewrite <- IHl.
          rewrite eval_op_list_cons.
          rewrite! eval_op_list_app.
          rewrite eval_op_list_rev_append.
          rewrite <- (H a).
          rewrite EQ.
          simpl.
          destruct l0; simpl; tauto.
        * intros.
          rewrite <- IHl.
          rewrite eval_op_list_cons.
          rewrite! eval_op_list_app.
          rewrite eval_op_list_cons.
          rewrite <- (H a).
          rewrite EQ.
          simpl.
          destruct o; simpl; tauto.
      +
        intros.
          rewrite <- IHl.
          rewrite eval_op_list_cons.
          rewrite! eval_op_list_app.
          rewrite eval_op_list_cons.
          rewrite <- (H a).
          rewrite EQ.
          simpl.
          destruct o; simpl; tauto.
  Defined.


  Fixpoint eval_formula_lform (f:LForm):
      eval_formula f <-> eval_formula (lform f).
  Proof.
    destruct f ; simpl.
    - tauto.
    - tauto.
    - apply eval_op_list_lform_app.
      auto.
    -
      rewrite <- eval_mk_impl.
      simpl.
      apply eval_impl_list_iff.
      apply (eval_op_list_lform_app eval_formula_lform LAND).
      auto.
  Qed.

  Lemma Forall_Forall : forall {T:Type} (P Q:T -> Prop) l,
      (forall x, P x -> Q x) ->
      List.Forall P l -> List.Forall Q l.
  Proof.
    intros.
    induction H0. constructor.
    constructor ; auto.
  Qed.


  Variable AT_is_dec_correct : forall a,
      AT_is_dec a = true -> eval_atom a \/ ~ eval_atom a.

  Lemma eval_formula_dec : forall m f,
      has_form m f ->
      is_dec f = true ->
      eval_formula f.(elt) \/ ~ eval_formula f.(elt).
  Proof.
    intros m f IND.
    remember (f.(elt)) as f' eqn:EQ.
    revert f EQ IND.
    induction f' using form_ind.
    - simpl. intros.
      inv IND ; simpl in EQ ; subst ; simpl in *; try congruence.
      inv EQ. auto.
    - simpl. intros.
      inv IND ; simpl in EQ ; subst ; simpl in *; try congruence.
      inv EQ. auto.
    - intros.
      destruct f ; simpl in EQ ; inv EQ.
      inv IND. simpl in *.
      apply eval_op_list_dec.
      rewrite Forall_forall in H6.
      apply Forall_forall.
      intros. apply H with (f:=x); auto.
      rewrite forallb_forall in H0.
      apply H0; auto.
    - intros.
      destruct f ; simpl in EQ ; inv EQ.
      inv IND. simpl in *.
      rewrite andb_true_iff in H0.
      destruct H0 as (H1L & H1R).
      apply eval_impl_list_dec.
      rewrite Forall_forall in H6.
      apply Forall_forall.
      intros. apply H with (f:=x); auto.
      rewrite forallb_forall in H1L.
      auto.
      eapply IHf';eauto.
  Qed.

  Record watched_clause : Type :=
    {
    watch1 : literal;
    watch2 : literal;
    unwatched : list literal
    }.


  Inductive clause_kind :=
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

  Definition has_clause (m:hmap) (cl:clause_kind) :=
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

  Definition eval_clause  (cl:clause_kind) :=
    match cl with
    | EMPTY => False
    | TRUE  => True
    | UNIT l => eval_literal l
    | CLAUSE cl => eval_watched_clause cl
    end.

  Definition hmap_order (h h' : hmap) :=
    forall k v, IntMap.get' k h = Some v -> IntMap.get' k h' = Some v.


  Record Thy : Type :=
    mkThy
      {
        (** The formula are restricted to atoms *)
        thy_prover  : hmap -> list literal -> option (hmap * list literal);
        thy_prover_sound : forall hm hm' cl cl',
            thy_prover hm cl = Some (hm',cl') ->
            eval_literal_list cl' /\
            hmap_order hm hm' /\
            Forall (has_literal hm') cl'
      }.


  Definition watch_map_elt := (IntMap.ptrie (key:=int) (Annot.t watched_clause) * IntMap.ptrie (key:=int) (Annot.t watched_clause) )%type.

  Definition watch_map := IntMap.ptrie (key:=int) watch_map_elt.

  Definition empty_watch_map  := IntMap.empty (key:=int) watch_map_elt.

  Definition iset := IntMap.ptrie (key:=int) unit.

  Record state : Type :=
    mkstate {
        fresh_clause_id : int;
        hconsmap : hmap;
        (* [arrows] :
           Formulae of the form a -> b need a special processing and are stored in arrows *)
        arrows : list  literal;
        (* [wneg] : watched negative litterals - are needed to generate complete conflict clauses*)
        wneg : iset;
        (* Formulae which cnf has been already unfolded *)
        defs : iset * iset ;
        units : IntMap.ptrie (key:=int) (Annot.t bool);
        unit_stack : list (Annot.t literal);
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
    wneg := IntMap.empty unit;
    defs := (IntMap.empty unit , IntMap.empty unit);
    units := IntMap.empty (Annot.t bool);
    unit_stack := nil;
    clauses := empty_watch_map
    |}.


  Definition find_clauses (v:int) (cls : watch_map) :=
    match IntMap.get' v cls with
    | None => (IntMap.empty (Annot.t watched_clause),IntMap.empty (Annot.t watched_clause))
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

  Definition add_clause (l:literal) (clause_id: int) (cl: Annot.t watched_clause) (cls : watch_map) :=
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


  Definition is_arrow (f:LForm) : bool :=
    match f with
    | LIMPL f1 f2 => true
    | _             => false
    end.

  Definition is_arrow_lit (l: literal) : bool :=
    match l with
    | POS f | NEG f => is_arrow f.(elt)
    end.


  Definition insert_unit (l:Annot.t literal) (st:state) : state :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    wneg   := wneg st;
    defs   := defs st;
    arrows :=  arrows st;
    units := units st;
    unit_stack := l:: unit_stack st;
    clauses := clauses st
    |}.

  Definition add_wneg_lit (l: literal) (wn: iset)  : iset :=
    match l with
    | POS _ => wn
    | NEG f => IntMap.set' (HCons.id f) tt wn
    end.

  Definition add_wneg_wcl (wn : iset) (cl:watched_clause) : iset :=
    add_wneg_lit (watch2 cl) (add_wneg_lit  (watch1 cl) wn) .

  Definition insert_lit_clause (l:literal) (clause_id: int) (cl: Annot.t watched_clause) (st : state) : state :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs   := defs st;
    wneg   := add_wneg_wcl (wneg st) cl.(Annot.elt);
    arrows := arrows st ;
    units := units st;
    unit_stack := unit_stack st;
    clauses := add_clause l clause_id cl (clauses st)
    |}.



  Definition is_cons (id: int) (l : IntMap.ptrie unit) :=
    match IntMap.get' id l with
    | Some _ => true
    | _ => false
    end.

  Definition set_cons (id:int) (l: IntMap.ptrie unit) := IntMap.set' id tt l.


  Definition literal_of_bool (b:bool) (f:HFormula) :=
    if b then POS f else NEG f.

  Fixpoint xrev_map [A B: Type] (f: A -> B) (acc: list B) (l : list A) : list B :=
    match l with
    | nil => acc
    | e::l => xrev_map f (f e :: acc) l
    end.

  Fixpoint xrev_map_filter [A B: Type] (p: A -> bool) (f: A -> B) (acc: list B) (l:list A) : list B :=
    match l with
    | nil => acc
    | e::l =>
      xrev_map_filter p f (if p e then f e::acc else acc) l
    end.


  Definition rev_map [A B: Type] (f: A -> B) := xrev_map f nil.


  Lemma in_xrev_map_iff:
    forall [A B : Type] (f : A -> B) (l : list A) (acc: list B) (y : B),
      In y (xrev_map f acc l) <->
      (In y acc \/ (exists x : A, f x = y /\ In x l)).
  Proof.
    induction l; simpl.
      - intuition.
        destruct H0. tauto.
      - intros.
        rewrite IHl.
        clear IHl.
        simpl.
        firstorder.
        subst.
        firstorder.
  Qed.

  Lemma in_xrev_map_filter_iff:
    forall [A B : Type] (p: A -> bool) (f : A -> B) (l : list A) (acc: list B) (y : B),
      In y (xrev_map_filter p f acc l) <->
      (In y acc \/ (exists x : A, p x = true /\ f x =  y /\ In x l)).
  Proof.
    induction l; simpl.
      - intuition.
        destruct H0. tauto.
      - intros.
        rewrite IHl. clear IHl.
        destruct (p a) eqn:Pa.
        + simpl.
          intuition subst.
          * firstorder.
          * firstorder.
          * firstorder congruence.
            apply 0%int63. (* ?? *)
        + simpl.
          intuition subst.
          firstorder.
          firstorder.
          firstorder congruence.
          apply 0%int63. (* ?? *)
  Qed.


  Lemma in_rev_map_iff:
    forall [A B : Type] (f : A -> B) (l : list A) (y : B),
      In y (rev_map f l) <-> (exists x : A, f x = y /\ In x l).
  Proof.
    unfold rev_map.
    intros.
    rewrite in_xrev_map_iff.
    simpl. tauto.
  Qed.


  (** Plaisted & Greenbaum cnf
      cnf+ f generate clauses to build f from sub-formulae (ways to deduce f)
      cnf- f generate clauses to deduce sub-formulae from f
   *)

  (** [watch_clause_of_list] does not make sure that the watched literals are distinct *)
  Definition watch_clause_of_list (l :list literal) : option watched_clause :=
    match l with
    | e1::e2::l => Some {| watch1 := e1 ; watch2 := e2 ; unwatched := l |}
    | _  => None
    end.

  Definition cnf_plus_and (l : list HFormula)  (f:HFormula) (rst: list watched_clause) :=
    match watch_clause_of_list (xrev_map NEG (POS f::nil) l) with
    | None => rst
    | Some cl => cl::rst
    end.

  Definition  cnf_plus_or (l: list HFormula) (f: HFormula) (rst: list watched_clause) :=
    xrev_map (fun fi =>
               {|
                 watch1 := NEG fi ;
                 watch2 := POS f;
                 unwatched := nil |}) rst l.

  Definition is_classic_or_dec (is_classic: bool) (f: HFormula) :=
    if is_classic then true
    else f.(is_dec).

  Definition cnf_plus_impl (is_classic: bool) (l: list HFormula) (r: HFormula) (f: HFormula) (rst: list watched_clause) : list watched_clause :=
  {| watch1 := NEG r ;
     watch2 := POS f;
     unwatched := nil
  |} ::
     xrev_map_filter (is_classic_or_dec is_classic)
     (fun fi =>
          {| watch1 := POS fi ;
             watch2 := POS f;
             unwatched := nil
          |}) rst l.


  Definition cnf_minus_and (l :list HFormula)  (f:HFormula) (rst: list watched_clause) :=
    xrev_map (fun fi =>   {| watch1 := NEG f ; watch2 := POS fi ; unwatched := nil|}) rst l.

  Definition cnf_minus_or (l:list HFormula)  (f:HFormula) (rst: list watched_clause) :=
    match l with
    | nil  => rst
    | f1::l'  =>
      {|
        watch1 := NEG f ;
        watch2 := POS f1 ;
        unwatched := rev_map POS l' |} :: rst
    end.

  Definition unit_or (r: HFormula) :=
    match r.(elt) with
    | LFF => nil
    |  _  => (POS r:: nil)
    end.

  Definition cnf_minus_impl (l:list HFormula) (r: HFormula) (f:HFormula) (rst: list watched_clause) :=
    match watch_clause_of_list (NEG f :: xrev_map NEG (unit_or r) l)  with
    | None => rst
    | Some wc => wc ::rst
    end.

  Definition cnf_of_op_plus (is_classic: bool) (o:lop) :=
    match o with
    | LAND => cnf_plus_and
    | LOR  => cnf_plus_or
    end.

  Definition cnf_of_op_minus (is_classic: bool) (o:lop) :=
    match o with
    | LAND => cnf_minus_and
    | LOR  => cnf_minus_or
    end.

  Definition polarity_of_op_1 (o: op) (b:bool):=
    match o with
    | AND => b
    | OR  => b
    | IMPL => negb b
    end.

(*  Definition cnf_of_atom (pol: bool) (f : HFormula) (rst: list watched_clause) :=
    if pol && f.(is_dec) then {| watch1 := NEG f ; watch2 := POS f ; unwatched := nil |} :: rst else rst.
*)

  Section S.
    Variable cnf : forall (pol:bool) (is_classic: bool) (cp cm: IntMap.ptrie (key:= int) unit)
                          (ar:list literal) (acc : list watched_clause)   (f: LForm) (hf: HFormula),
      IntMap.ptrie (key:=int) unit * IntMap.ptrie (key:=int) unit * list literal * list watched_clause.

    Fixpoint cnf_list (pol:bool) (is_classic: bool) (cp cm: IntMap.ptrie unit)
             (ar: list literal) (acc: list watched_clause) (l: list HFormula) :=
      match l with
      | nil => (cp,cm,ar,acc)
      | f :: l =>  let '(cp,cm,ar,acc) := cnf pol is_classic cp cm ar acc f.(elt) f in
                   cnf_list pol is_classic cp cm ar acc l
      end.

  End S.

  Fixpoint cnf (pol:bool) (is_classic: bool) (cp cm: IntMap.ptrie unit)
           (ar:list literal) (acc : list watched_clause)   (f: LForm) (hf: HFormula) :
    IntMap.ptrie unit * IntMap.ptrie unit * list literal * list watched_clause
    :=
    let h := hf.(id) in
    if is_cons h (if pol then cp else cm) then (cp,cm,ar,acc)
    else
      match f with
      | LFF   => (cp,cm,ar,acc)
      | LAT _ => (cp,cm,ar,acc)
(*        let cp  := if pol then set_cons h cp else cp in
        let cm  := if pol then cm else set_cons h cm in
        (cp,cm,ar,cnf_of_atom (negb is_classic && pol) hf acc) *)
      | LOP o l =>
        let cp  := if pol then set_cons h cp else cp in
        let cm  := if pol then cm else set_cons h cm in
        let acc := (if pol then cnf_of_op_plus else cnf_of_op_minus) is_classic o l hf acc in
        cnf_list cnf pol is_classic cp cm ar acc l
      | LIMPL l r =>
        let ar  := if negb (lazy_or is_classic (fun x => List.forallb HCons.is_dec l)) && pol then POS hf::ar else ar in
        let acc := (if pol then cnf_plus_impl is_classic else cnf_minus_impl)  l r hf acc in
        let '(cp,cm,ar,acc) := cnf_list cnf (negb pol) is_classic cp cm ar acc l in
        cnf pol is_classic cp cm ar acc r.(elt) r
      end.

  Definition neg_literal (l: literal) :=
    match l with
    | POS h => NEG h
    | NEG h => POS h
    end.

  Definition is_negative_literal (l:literal) :=
    match l with
    | POS _ => False
    | NEG _ => True
    end.

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

  Lemma eval_watched_clause_of_list : forall l w,
      eval_literal_list l ->
      watch_clause_of_list l = Some w ->
      eval_watched_clause w.
  Proof.
    unfold watch_clause_of_list.
    destruct l; try congruence.
    destruct l0; try congruence.
    intros. inv H0.
    unfold eval_watched_clause.
    simpl in *; auto.
  Qed.

  Lemma eval_literal_list_NEG_app : forall l r,
      eval_literal_list (List.map NEG l ++ r) <->
      (eval_and_list' eval_hformula l -> eval_literal_list r).
  Proof.
    induction l; simpl.
    - tauto.
    - intros.
      unfold eval_hformula at 1.
      rewrite IHl.
      tauto.
  Qed.

  Lemma eval_literal_list_POS : forall l ,
      eval_literal_list (List.map POS l) <->
      (eval_or_list' eval_hformula l).
  Proof.
    induction l; simpl.
    - tauto.
    - intros.
      unfold eval_hformula at 1.
      rewrite IHl.
      tauto.
  Qed.

  Lemma xmap_rev : forall [A B: Type] (f: A -> B) (l:list A) (r:list B),
      xrev_map f r l = (List.map f (List.rev l)) ++ r.
  Proof.
    induction l; simpl.
    - auto.
    - intros.
      rewrite IHl.
      rewrite List.map_app.
      simpl. rewrite <- app_assoc.
      reflexivity.
  Qed.

  Lemma xmap_filter_rev : forall [A B: Type] (p: A -> bool) (f: A -> B) (l:list A) (r:list B),
      xrev_map_filter p f r l = (List.map f (List.rev (List.filter p l))) ++ r.
  Proof.
    induction l; simpl.
    - auto.
    - intros.
      rewrite IHl.
      destruct (p a).
      + simpl.
        rewrite List.map_app.
        simpl. rewrite <- app_assoc.
        reflexivity.
      + reflexivity.
  Qed.



  Lemma eval_literal_list_plus_and : forall l hf,
      elt hf = LOP LAND l ->
      eval_literal_list (xrev_map NEG (POS hf :: nil) l).
 Proof.
   intros.
   rewrite xmap_rev.
   rewrite eval_literal_list_NEG_app.
   simpl. rewrite H. simpl.
   rewrite eval_and_list_rev.
   rewrite eval_and_list_eq.
   unfold eval_hformula. tauto.
 Qed.

 Lemma eval_plus_or : forall l hf,
     elt hf = LOP LOR l ->
  Forall eval_watched_clause
    (List.map
       (fun fi : HFormula =>
        {| watch1 := NEG fi; watch2 := POS hf; unwatched := nil |}) l).
 Proof.
   intros.
   rewrite Forall_forall.
   intros. rewrite in_map_iff in H0.
   destruct H0 as (f & (EQ & IN)).
   subst. unfold eval_watched_clause. simpl.
   intro.
   rewrite H.
   rewrite eval_formula_rew.
   left.
   simpl. rewrite eval_or_list_eq.
   rewrite eval_or_list'_Exists.
   rewrite Exists_exists.
   exists f ; split ; assumption.
 Qed.


  Lemma cnf_of_op_plus_correct :
    forall acc g o l hf
           (EQ : hf.(elt) = LOP o l)
           (ACC : (Forall eval_watched_clause acc -> eval_ohformula g)
                  -> eval_ohformula g),
      (Forall eval_watched_clause (cnf_of_op_plus (is_classic g) o l hf acc) ->  eval_ohformula g) -> eval_ohformula g.
  Proof.
    destruct o ; simpl.
    - intros. apply ACC.
      intro. apply H.
      unfold cnf_plus_and.
      destruct (watch_clause_of_list (xrev_map NEG (POS hf:: nil) l)) eqn:WC;auto.
      constructor;auto.
      apply eval_watched_clause_of_list in WC ; auto.
      apply eval_literal_list_plus_and; auto.
    - intros. apply ACC.
      intro. apply H.
      unfold cnf_plus_or.
      rewrite xmap_rev.
      apply Forall_app. split ; auto.
      rewrite map_rev.
      apply Forall_rev.
      apply eval_plus_or; auto.
  Qed.

  Lemma cnf_of_op_minus_correct :
    forall acc g o l hf
           (EQ : hf.(elt) = LOP o l)
           (ACC : (Forall eval_watched_clause acc -> eval_ohformula g)
                  -> eval_ohformula g),
      (Forall eval_watched_clause (cnf_of_op_minus (is_classic g) o l hf acc) ->  eval_ohformula g) -> eval_ohformula g.
  Proof.
    intros.
    apply ACC.
    intros. apply H.
    clear ACC H.
    destruct o ; simpl.
    -
      unfold cnf_minus_and.
      rewrite xmap_rev.
      apply Forall_app.
      split ; auto.
      rewrite Forall_forall.
      intros.
      rewrite in_map_iff in H.
      destruct H. destruct H.
      subst. unfold eval_watched_clause.
      simpl. rewrite EQ.
      rewrite eval_formula_rew.
      simpl. rewrite eval_and_list_eq.
      intros. left.
      rewrite <- in_rev in H1.
      revert x0 H1.
      rewrite <- Forall_forall.
      rewrite <- eval_and_list'_Forall.
      auto.
    - unfold cnf_minus_or.
      destruct l; auto.
      constructor ; auto.
      unfold eval_watched_clause.
      simpl. rewrite EQ.
      rewrite eval_formula_rew.
      unfold eval_op_list.
      rewrite eval_or_list_eq.
      simpl.
      unfold rev_map.
      rewrite xmap_rev.
      rewrite <- app_nil_end.
      rewrite eval_literal_list_POS.
      rewrite eval_or_list_rev.
      simpl. tauto.
  Qed.

  Lemma Forall_rev_iff : forall {A: Type} (P: A -> Prop) l,
      Forall P (rev l) <-> Forall P l.
  Proof.
    intros.
    induction l.
    - simpl. tauto.
    - simpl. rewrite Forall_app.
      rewrite (Forall_rew  (a::nil)).
      rewrite (Forall_rew (a::l)).
      rewrite (Forall_rew nil).
      tauto.
  Qed.

  Lemma not_not_and : forall (A B: Prop),
      ((A -> False) -> False) ->
      ((B -> False) -> False) ->
      (((A /\ B) -> False) -> False).
  Proof.
    tauto.
  Qed.

  Lemma not_not_or : forall (A B: Prop),
      ((A -> False) -> False) \/
      ((B -> False) -> False) ->
      (((A \/ B) -> False) -> False).
  Proof.
    tauto.
  Qed.


  Lemma Exists_rew : forall {A: Type} [P: A -> Prop] l,
      Exists P l <->  match l with
                      | nil => False
                      | a::l => P a \/ Exists P l
                      end.
  Proof.
    split ; intros.
    - inv H; tauto.
    - destruct l.
      tauto. destruct H.
      apply Exists_cons_hd; auto.
      eapply Exists_cons_tl;auto.
  Qed.

  Lemma Forall_Exists_neg_neg : forall {A: Type} (P: A -> Prop) l,
      ((Exists (fun x => not (P x)) l) -> False) ->
      ((Forall P l -> False) -> False).
  Proof.
    induction l.
    - intros. rewrite Forall_rew in H0. tauto.
    - intros.
      rewrite Forall_rew in H0.
      rewrite Exists_rew  in H.
      tauto.
  Qed.

  Lemma cnf_plus_impli :  forall hf l r
      (EQ : elt hf = LIMPL l r),
      eval_watched_clause {| watch1 := NEG r; watch2 := POS hf; unwatched := nil |}.
  Proof.
    unfold eval_watched_clause.
    simpl. intros. left.
    rewrite EQ.
    rewrite eval_formula_rew.
    rewrite <- eval_impl_list_eq.
    auto.
  Qed.

  Lemma modus_ponens_and : forall (A B C:Prop),
      A ->
      ((A /\ B) -> C) <-> (B -> C).
  Proof.
    tauto.
  Qed.


  Lemma eval_and_list_Forall : forall [A:Type] P (l:list A),
      eval_and_list P l <-> Forall P l.
  Proof.
    intros.
    rewrite eval_and_list_eq.
    induction l.
    - simpl. rewrite Forall_rew. tauto.
    - simpl. rewrite Forall_rew. tauto.
  Qed.

  Lemma filter_true : forall [A: Type] (l:list A),
      filter (fun _ => true) l = l.
  Proof.
    induction l ; simpl ; auto.
    congruence.
  Qed.

  Lemma cnf_plus_impl_correct :
    forall m l r hf g acc
           (HF : has_form m hf)
           (EQ : elt hf = LIMPL l r)
           (ACC : (Forall eval_watched_clause acc -> eval_ohformula g) ->
                  eval_ohformula g),
      (Forall eval_watched_clause (cnf_plus_impl (is_classic g) l r hf acc) -> eval_ohformula g) -> eval_ohformula g.
  Proof.
    unfold cnf_plus_impl.
    intros.
    rewrite Forall_rew in H.
    rewrite! xmap_filter_rev in H.
    rewrite Forall_app in H.
    rewrite! map_rev in H.
    rewrite! Forall_rev_iff in H.
    rewrite modus_ponens_and in H by (apply cnf_plus_impli with (l:= l); auto).
    apply ACC.
    intro. rewrite and_comm in H.
    rewrite modus_ponens_and in H by auto.
    clear ACC H0.
    unfold is_classic ; destruct g.
    - (* This is not classic *)
      simpl in *. apply H.
      rewrite Forall_forall.
      intros.
      rewrite in_map_iff in H0.
      destruct H0 as (f' & E & I).
      subst.
      rewrite filter_In in I.
      destruct I. simpl in H1.
      assert (has_form m f').
      {
        inv HF; try discriminate.
        simpl in *. inv EQ.
        revert H0.
        rewrite Forall_forall in H2; auto.
      }
      apply eval_formula_dec  with (m:=m) in H1; auto.
      unfold eval_watched_clause.
      simpl.
      destruct H1. tauto.
      right. left.
      rewrite EQ.
      rewrite eval_formula_rew.
      rewrite <- eval_impl_list_eq.
      intro.
      rewrite eval_and_list_Forall in H3.
      rewrite Forall_forall in H3.
      exfalso ; apply H1 ; auto.
    - (* this is classic *)
      simpl in *.
      unfold is_classic_or_dec in H.
      rewrite filter_true in H.
      revert H.
      apply Forall_Exists_neg_neg.
      intros.
      rewrite Exists_exists in H.
      destruct H.
      rewrite in_map_iff in H.
      destruct H.
      destruct H.
      destruct H; subst.
      unfold eval_watched_clause in H0.
      simpl in H0.
      rewrite EQ in H0.
      rewrite (eval_formula_rew (LIMPL l r)) in H0.
      rewrite <- eval_impl_list_eq in H0.
      rewrite eval_and_list_Forall in H0.
      unfold not in H0.
      assert (((eval_formula (elt x0) \/ ~ eval_formula (elt x0)) -> False) -> False).
      { tauto. }
      apply H. intro D.
      destruct D. tauto.
      apply H0.
      right. left.
      intros.
      rewrite Forall_forall in H3.
      specialize (H3 _ H1).
      tauto.
  Qed.

  Lemma unit_or_correct : forall f, eval_hformula f <-> eval_literal_list (unit_or f).
  Proof.
    unfold unit_or. intros.
    destruct (elt f) eqn:F; simpl; unfold eval_hformula; try tauto.
    rewrite F. simpl. tauto.
  Qed.

  Lemma cnf_minus_impl_correct :
    forall l r hf g acc
           (EQ : elt hf = LIMPL l r)
           (ACC : (Forall eval_watched_clause acc -> eval_ohformula g) ->
                  eval_ohformula g),
      (Forall eval_watched_clause (cnf_minus_impl  l r hf acc) -> eval_ohformula g) -> eval_ohformula g.
  Proof.
    unfold cnf_plus_impl.
    intros. apply ACC.
    intro ACC'; clear ACC.
    apply H; clear H.
    unfold cnf_minus_impl.
    destruct (watch_clause_of_list (NEG hf :: xrev_map NEG (unit_or r) l))
             eqn:WC;auto.
    constructor ; auto.
    apply eval_watched_clause_of_list in WC ; auto.
    rewrite xmap_rev.
    change (NEG hf :: List.map NEG (rev l) ++ (unit_or r)) with
        (List.map NEG (hf ::rev l) ++  (unit_or r)).
    rewrite eval_literal_list_NEG_app.
    simpl. unfold eval_hformula at 1.
    rewrite EQ. simpl.
    intros.
    rewrite eval_and_list_rev in H.
    rewrite <- eval_impl_list_eq in H.
    rewrite eval_and_list_eq in H.
    rewrite <- unit_or_correct.
    unfold eval_hformula.
    tauto.
  Qed.

  Lemma cnf_correct_list :
    forall m l
           (WF: Forall (has_form m) l)
           (H : forall x : t LForm,
               In x l ->
               forall (pol : bool) (g : option HFormula) (cp cm : IntMap.ptrie unit)
                      (ar : list literal) (acc : list watched_clause) (hf : t LForm),
                 has_form m hf ->
                 elt hf = elt x ->
                 ((Forall eval_watched_clause acc -> eval_ohformula g) -> eval_ohformula g) ->
                 (Forall eval_watched_clause
                         (snd (cnf pol (is_classic g) cp cm ar acc (elt x) hf)) ->
                  eval_ohformula g) -> eval_ohformula g)
           (g : option HFormula)
           pol
           (acc : list watched_clause)
           (hf : t LForm),
  forall (ar : list literal) (acc' : list watched_clause)
  (ACC' : (Forall eval_watched_clause acc' -> eval_ohformula g) -> eval_ohformula g),
  forall cm' cp' : IntMap.ptrie unit,
  (Forall eval_watched_clause
     (snd (cnf_list cnf pol (is_classic g) cp' cm' ar acc' l)) ->
   eval_ohformula g) -> eval_ohformula g.
  Proof.
    intros.
    revert cm' cp' ar acc' ACC' H0.
    induction l; simpl.
    * auto.
    * intros cm' cp' ar acc' ACC' .
      destruct (cnf pol
                    (is_classic g) cp' cm' ar acc' (elt a) a) as
          (((cp1,cm1),ar1),acc1) eqn:EQPf1.
      rewrite Forall_rew in WF.
      apply IHl; auto.
      tauto.
      intros.
      revert H4.
      apply H;auto. simpl. tauto.
      change acc1 with (snd (cp1,cm1,ar1,acc1)).
      rewrite <- EQPf1.
      apply H; auto.
      simpl. tauto.
      tauto.
  Defined.

  Lemma has_form_lop :
    forall m o l hf
           (WF : has_form m hf)
           (EQ : elt hf = LOP o l),
      Forall (has_form m) l.
  Proof.
    intros.
    inv WF ; try discriminate.
    inv EQ. auto.
  Qed.

  Lemma has_form_limpl :
    forall m l r hf
           (WF : has_form m hf)
           (EQ : elt hf = LIMPL l r),
      Forall (has_form m) (r::l).
  Proof.
    intros.
    inv WF ; try discriminate.
    inv EQ. rewrite Forall_rew.
    split; auto.
  Qed.

(*  Lemma cnf_atom_correct :
    forall m hf acc g b
           (WF : has_form m hf)
           (Acc : (Forall eval_watched_clause acc -> eval_ohformula g) -> eval_ohformula g)
           (CNF : Forall eval_watched_clause (cnf_of_atom b hf acc) ->
                  eval_ohformula g),
      eval_ohformula g.
  Proof.
    unfold cnf_of_atom.
    intros.
    destruct (b && is_dec hf) eqn:C.
    - rewrite andb_true_iff in C.
      destruct C.
      apply eval_formula_dec in WF; auto.
      rewrite Forall_rew in CNF.
      unfold eval_watched_clause at 1 in CNF.
      simpl in CNF.
      tauto.
    - tauto.
  Qed.
 *)

  Lemma cnf_correct :
    forall m f pol g cp cm ar acc hf
           (WF: has_form m hf)
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
      destruct (is_cons (id hf) (if pol then cp else cm)).
      tauto. tauto.
(*      unfold snd in CNF.
      simpl in CNF; try  tauto.
      eapply cnf_atom_correct; eauto. *)
    - simpl; intros.
      destruct (is_cons (id hf) (if pol then cp else cm)).
      + simpl in CNF ; tauto.
      +
        revert CNF.
        generalize (if pol then set_cons (id hf) cp else cp) as cp'.
        generalize (if pol then cm else set_cons (id hf) cm) as cm'.
        set (acc':= ((if pol then cnf_of_op_plus else cnf_of_op_minus)
               (is_classic g) o l hf acc)).
        assert (ACC' : (Forall eval_watched_clause acc' -> eval_ohformula g) -> eval_ohformula g).
        {
          destruct pol.
          apply cnf_of_op_plus_correct; auto.
          apply cnf_of_op_minus_correct; auto.
        }
        apply cnf_correct_list with (m:=m); auto.
        eapply has_form_lop; eauto.
    -  simpl.
       intros pol g cp cm ar acc hf.
       destruct (is_cons (id hf) (if pol then cp else cm)).
       + simpl. tauto.
       +
         set (ar' := (if negb (lazy_or (is_classic g) (fun _ : unit => forallb is_dec l)) && pol then POS hf :: ar else ar)).
         set (acc':= ((if pol then cnf_plus_impl (is_classic g) else cnf_minus_impl) l r hf acc)).
         intros HF EQ ACC.
         assert (ACC' : (Forall eval_watched_clause acc' -> eval_ohformula g) -> eval_ohformula g).
        {
          destruct pol.
          apply cnf_plus_impl_correct with (m:=m) ; auto.
          apply cnf_minus_impl_correct; auto.
        }
        destruct (cnf_list cnf (negb pol) (is_classic g) cp cm ar' acc' l)
        as (((cp0,cm0),ar0),acc0)  eqn:CNF1.
        eapply has_form_limpl in EQ;eauto.
        inv EQ.
        apply IHf; auto.
        change acc0 with (snd (cp0, cm0, ar0, acc0)).
        rewrite <- CNF1.
        apply cnf_correct_list with (m:=m) ;auto.
  Qed.

  Definition insert_defs (m : IntMap.ptrie unit * IntMap.ptrie unit) (ar : list literal) (st : state ) :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    wneg := wneg st;
    defs := m;
    arrows := ar;
    units  := units st;
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.

(*  Definition reset_arrows (ar : list  literal) (st: state) :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    wneg := wneg st;
    defs := defs st;
    arrows := ar;
    units  := units st;
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.
 *)

  Fixpoint removeb [A: Type] (P : A -> bool) (l:list A) :=
    match l with
    | nil => nil
    | e::l => if P e then l else e :: (removeb P l)
    end.

  Definition eq_literal (l1: literal) :=
    match l1 with
    | POS {| id := i ; |} =>
      fun l2 => match l2 with
                | POS f' => f'.(id) =? i
                | NEG _  => false
                end
    | NEG {| id := i ; |} =>
      fun l2 => match l2 with
                | NEG f' => f'.(id) =? i
                | POS _  => false
                end
    end.

  Definition remove_arrow (ar : literal) (st:state) :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    wneg := wneg st;
    defs := defs st;
    arrows := removeb (eq_literal ar) (arrows st);
    units  := units st;
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.



  Definition neg_bool (o : option (Annot.t bool)) : option (Annot.t bool) :=
    match o with
    | None => None
    | Some b => Some (Annot.map negb b)
    end.

  Definition find_lit (l: literal) (lit: IntMap.ptrie (Annot.t bool)) : option (Annot.t bool) :=
    match l with
    | POS l => IntMap.get' l.(id) lit
    | NEG l => neg_bool (IntMap.get' l.(id) lit)
    end.

  Definition find_lit' (l: literal) (lit : IntMap.ptrie (Annot.t bool))  : option (Annot.t bool) :=
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

  Fixpoint reduce (lit: IntMap.ptrie (Annot.t bool)) (ann: LitSet.t) (w:literal)  (cl : list literal) :=
    match cl with
    | nil => Annot.mk (UNIT w) ann
    | e::l => match find_lit e lit with
              | None => Annot.mk (CLAUSE {| watch1 := w ; watch2 := e ; unwatched := l |}) ann
              | Some b => if Annot.elt b then Annot.mk_elt TRUE
                          else reduce lit (LitSet.union (Annot.deps b) ann) w l
              end
    end.

  Fixpoint reduce_lits (lit: IntMap.ptrie (Annot.t bool)) (ann: LitSet.t) (cl : list literal) :=
    match cl with
    | nil => Some (Annot.mk nil ann)
    | e::cl => match find_lit e lit with
              | None => match reduce_lits lit ann cl with
                        | None => None
                        | Some l' => Some (Annot.map (fun x => e::x) l')
                        end
              | Some b => if Annot.elt b then None
                          else reduce_lits lit (LitSet.union (Annot.deps b) ann) cl
              end
    end.

  
  (** Either one or the other watched literal is set (not both) *)

  Definition shorten_clause (lit : IntMap.ptrie (Annot.t bool)) (ann : LitSet.t) (cl : watched_clause) :=
    match find_lit (watch1 cl) lit with
    | None => match find_lit (watch2 cl) lit with
              | None => (* Should not happen *) Annot.mk (CLAUSE cl) ann
              | Some b  => if Annot.elt b then (Annot.mk TRUE LitSet.empty)
                           else reduce lit (LitSet.union (Annot.deps b) ann) (watch1 cl) (unwatched cl)
              end
    | Some b => if Annot.elt b then Annot.mk TRUE LitSet.empty
                else reduce lit (LitSet.union (Annot.deps b) ann) (watch2 cl) (unwatched cl)
    end.

  Definition add_watched_clause  (st : state) (id: int) (acl: Annot.t watched_clause) : state :=
    let cl := Annot.elt acl in
    let w1 := watch1 cl in
    let w2 := watch2 cl in
    let mcl := clauses st in
    let mcl := add_clause w1 id acl mcl in
    let mcl := add_clause w2 id acl mcl in
    {|
      fresh_clause_id := fresh_clause_id st;
      hconsmap := hconsmap st;
      arrows := arrows st;
      wneg   := add_wneg_lit w1 (add_wneg_lit w2 (wneg st));
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
       wneg := wneg st;
       arrows := arrows st;
      defs := defs st;
      units := units st;
      unit_stack :=unit_stack st;
      clauses := clauses st
    |}).

  Inductive failure := OutOfFuel | Stuck | HasModel.

  Inductive result (A B: Type):=
  | Fail (f: failure)
  | Success (r : B)
  | Progress (st : A).

  Arguments Fail {A B}.
  Arguments Success {A B}.
  Arguments Progress {A B}.


  Definition dresult := result state (hmap * LitSet.t).

  Definition insert_normalised_clause (id: int) (cl:Annot.t clause_kind) (st: state)  : dresult :=
    match  cl.(Annot.elt) with
    | EMPTY => Success (hconsmap st,Annot.deps cl)
    | UNIT l => Progress (insert_unit (Annot.set cl l)  st)
    | TRUE   => Progress st
    | CLAUSE cl' => Progress (add_watched_clause st id (Annot.set cl cl'))
    end.

  Definition insert_watched_clause (id: int) (cl: Annot.t watched_clause) (st: state)  : dresult :=
    insert_normalised_clause id (shorten_clause (units st) (Annot.deps cl) (Annot.elt cl)) st .

  Definition insert_fresh_watched_clause (cl: watched_clause) (st: state) :=
    let (fr,st') := get_fresh_clause_id st in
    insert_watched_clause fr (Annot.mk cl LitSet.empty) st'.

  Definition insert_clause (id: int) (cl:Annot.t clause_kind) (st: state)  : dresult :=
    match Annot.elt cl with
    | EMPTY => Success (hconsmap st,Annot.deps cl)
    | UNIT l => Progress (insert_unit (Annot.set cl l) st)
    | CLAUSE cl' => insert_watched_clause id  (Annot.set cl cl') st
    | TRUE => Progress st
    end.

  Definition insert_fresh_clause (cl:Annot.t clause_kind) (st: state) :=
    let (fr,st') := get_fresh_clause_id st in
    insert_clause fr cl st'.


  Fixpoint fold_update {A : Type} (F : A -> state -> dresult) (l: list A) (st:state)  : dresult :=
    match l with
    | nil => Progress st
    | e::l => match F e st with
              | Success p => Success p
              | Progress st' => fold_update F  l st'
              | Fail s => Fail s
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

  Definition intro_impl (acc: list literal) (f: LForm) (hf: HFormula) :=
    match f with
    | LFF   => (acc, None)
    | LAT a => if hf.(is_dec) then  ((NEG hf) :: acc , None)
              else  (acc , Some hf)
    | LOP o l => if hf.(is_dec) then (NEG hf::acc, None)
                 else (acc, Some hf)
    | LIMPL l r =>
      if r.(is_dec)
      then (NEG r :: xrev_map POS acc l, None)
      else (xrev_map POS acc l, Some r)
    end.


  Definition cnf_of_literal (l:literal) := cnf  (negb (is_positive_literal l)).

  Definition augment_cnf (is_classic: bool) (h: literal) (st: state) :=
      let f := form_of_literal h in
      let '(cp,cm,ar,acc) := (cnf_of_literal h) is_classic (fst (defs st)) (snd (defs st)) (arrows st) nil f.(elt) f in
      fold_update insert_fresh_watched_clause  acc (insert_defs (cp,cm) ar  st).

  Definition annot_of_literal (h: literal) : LitSet.t :=
    (LitSet.singleton (id_of_literal h) (is_positive_literal h)).

  Definition annot_hyp (h: literal) :=
    Annot.mk h (annot_of_literal h).

  Definition augment_hyp (is_classic: bool) (h:  literal) (st:state) :=
    augment_cnf is_classic h (insert_unit (annot_hyp h) st).

  Definition cnf_hyps (is_classic: bool) (l: list  literal) (st: state) :=
    fold_update (augment_hyp is_classic) l st.


  Definition intro_state (st:state) (f: LForm) (hf: HFormula) :=
    let (hs,c) := intro_impl nil f hf in
    match cnf_hyps (is_classic c) hs st with
    | Fail f => Fail f
    | Success p => Success p
    | Progress st =>
      match c with
      | None => Progress(st,None)
      | Some g => match augment_cnf false (NEG g) st with
                  | Fail f => Fail f
                  | Success p => Success p
                  | Progress st' => Progress(st',Some g)
                  end
      end
    end.


  Lemma neg_bool_some : forall o b,
      neg_bool o = Some b ->
      o = Some (Annot.map negb b).
  Proof.
    destruct o ; simpl ; try congruence.
    intros. inv H.
    rewrite Annot.map_map.
    rewrite Annot.map_id.
    reflexivity.
    apply negb_involutive.
  Qed.


  Definition remove_clauses (l:literal) (st: state) : state :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs   := defs st;
    wneg  := wneg st; (* Should we remove ? *)
    arrows := arrows st;
    units := units st;
    unit_stack := unit_stack st;
    clauses := IntMap.remove' (id_of_literal l) (clauses st)
    |}.


  Definition add_literal (l:Annot.t literal) (lit : IntMap.ptrie (Annot.t bool)) :=
    IntMap.set' (id_of_literal (Annot.elt l)) (Annot.map is_positive_literal l) lit.


  Definition is_neg_arrow (l:literal) : bool :=
    match l with
    | POS _ => false
    | NEG f => is_arrow f.(elt)
    end.

  Definition remove_wneg (l:literal) (s:iset) :=
    IntMap.remove' (id_of_literal l) s.

  Definition insert_literal (l:Annot.t literal) (st: state) : state :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    defs := defs st;
    wneg := remove_wneg (Annot.elt l) (wneg st);
    arrows := if is_neg_arrow (Annot.elt l) then (Annot.elt l::arrows st) else arrows st;
    units := add_literal l (units st);
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.


 Definition is_FF (g: LForm) : bool :=
    match g with
    | LFF => true
    | _  => false
    end.




  Definition is_hFF (g: HFormula) :=
    (g.(id) =? 0) && Bool.eqb g.(is_dec) true && is_FF g.(elt).

  Definition is_unsat (lit: IntMap.ptrie (Annot.t bool)) (l:Annot.t literal) : option LitSet.t  :=
    match Annot.elt l with
    | POS l' => if is_hFF l' then Some (Annot.deps l)
               else
                 match IntMap.get' l'.(id) lit with
                 | Some b => if  Annot.lift negb  b
                             then Some (LitSet.union (Annot.deps b) (Annot.deps l))
                             else None
                 | None  => None
                 end
    | NEG l' => match IntMap.get' l'.(id) lit with
                | Some b => if Annot.elt b then Some (LitSet.union (Annot.deps b) (Annot.deps l))
                            else None
               | None         => None
                end
    end.

  Definition is_goal (goal : HFormula) (l:literal) : option int :=
    match l with
    | POS f => if f.(id) =? goal.(id) then Some f.(id) else None
    | NEG _ => None
    end.

    Definition is_goalb (goal : HFormula) (l:literal) : bool :=
    match l with
    | POS f => f.(id) =? goal.(id)
    | NEG _ => false
    end.


  Definition success (goal: option HFormula) (lit: IntMap.ptrie (Annot.t bool)) (l:Annot.t literal) :=
    match goal with
    | None => is_unsat lit l
    | Some g =>
      if is_goalb  g (Annot.elt l) then Some (Annot.deps l)
      else is_unsat lit  l
    end.

  Definition set_unit_stack (l : list (Annot.t literal)) (st : state) :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hconsmap st;
    wneg := wneg st;
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
    wneg := wneg st;
    arrows := l:: arrows st ;
    units := units st;
    unit_stack := unit_stack st;
    clauses := clauses st |}.


  Definition extract_unit (st:state) :=
    match unit_stack st with
    | nil => None
    | e::us => Some(e , set_unit_stack us st)
    end.




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
      wneg := wneg st;
      defs := defs st;
      units := units st;
      unit_stack := unit_stack st;
      clauses := cls
    |}.


  Definition update_watched_clause  (id : int) (cl: Annot.t watched_clause) (st: dresult) : dresult :=
    match st with
    | Fail f  => Fail f
    | Success p => Success p
    | Progress st => insert_watched_clause id cl (remove_watched_clause id (Annot.elt cl) st)
    end.

  Definition shorten_clauses (cl : IntMap.ptrie (Annot.t watched_clause)) (st:state) :=
    IntMap.fold' (fun acc i k => update_watched_clause i k acc) cl (Progress st).

  Fixpoint unit_propagation (n:nat)  (concl: option HFormula) (st: state) : dresult :=
    match n with
    | O => Fail OutOfFuel
    | S n =>
      match extract_unit st with
      | None => Progress st
      | Some(l,st) =>
        match success concl (units st) l with
        | Some deps => Success (hconsmap st,deps)
        | None =>
          let st := insert_literal l st in
          let lelt := Annot.elt l in
          let (ln,lp) := find_clauses (id_of_literal lelt) (clauses st) in
          let lc := match lelt with
                    | POS _ => ln
                    | NEG _ => lp end in
          match shorten_clauses lc st with
          | Success d => Success d
          | Progress st => unit_propagation n concl st
          | Fail f   => Fail f
          end
        end
      end
    end.

  Lemma unit_propagation_rew : forall (n:nat)  (concl: option  HFormula),
      unit_propagation n  concl  =
    match n with
    | O => fun st => Fail OutOfFuel
    | S n => fun st =>
      match extract_unit st with
      | None => Progress st
      | Some(l,st) =>
        match success concl (units st) l with
        | Some deps => Success (hconsmap st,deps)
        | None =>
          let st := insert_literal l st in
          let lelt := Annot.elt l in
          let (ln,lp) := find_clauses (id_of_literal lelt) (clauses st) in
          let lc := match lelt with
                    | POS _ => ln
                    | NEG _ => lp end in
          match shorten_clauses lc st with
          | Success d => Success d
          | Progress st => unit_propagation n concl st
          | Fail f   => Fail f
          end
        end
      end
    end.
  Proof. destruct n ; reflexivity. Qed.


  Definition units_has_literal (m: hmap) (u: IntMap.ptrie (Annot.t bool)) (l : Annot.t literal) :=
    IntMap.get' (Annot.lift id_of_literal l) u =
    Some (Annot.map is_positive_literal l) /\
    Annot.lift (has_literal m) l.


  Definition forall_units (P: Annot.t literal -> Prop) (m: hmap) (u: IntMap.ptrie (Annot.t bool))  :=
    forall l, units_has_literal m u l -> P l.

  Definition eval_units (m : hmap) (u : IntMap.ptrie (Annot.t bool)) :=
    forall_units  (Annot.lift eval_literal) m u.

  Definition eval_stack (lst : list (Annot.t literal)) : Prop :=
    List.Forall (Annot.lift eval_literal) lst.

  Definition IntMapForall {A:Type} (P: A -> Prop) (m: IntMap.ptrie A) :=
    forall k r, IntMap.get' k m = Some r -> P r.

  Definition IntMapForall2 {A: Type} (P: A -> Prop) (m: IntMap.ptrie A* IntMap.ptrie A) :=
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

  Lemma grspec : forall {A:Type} i j (m: IntMap.ptrie A)
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
    forall (A: Type) (i j: int) (x: A) (m: IntMap.ptrie A)
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

  Lemma wf_map_add : forall  {A: Type} x v (cls : IntMap.ptrie A)
                             (WF : wf_map cls),
      wf_map (IntMap.set' x v cls).
  Proof.
    intros.
    eapply IntMap.wf_set'; eauto.
    constructor.
  Qed.

  Hint Resolve wf_map_add : wf.

  Lemma wf_map_remove :
    forall {A: Type} x
           (m : IntMap.ptrie A)
           (WF: wf_map m),
      wf_map (IntMap.remove' x m).
  Proof.
    intros.
    apply IntMap.wf_remove'; auto.
  Qed.

  Hint Resolve wf_map_remove : wf.

  Definition ForallWatchedClause (F : Annot.t watched_clause -> Prop) (m : watch_map) :=
    IntMapForall (IntMapForall2 F) m.

  Definition eval_clauses  (h : watch_map) :=
    ForallWatchedClause (Annot.lift eval_watched_clause) h.

  Definition order_map ( m m' : IntMap.ptrie LForm) : Prop :=
    forall i f, IntMap.get' i m = Some f -> IntMap.get' i m' = Some f.

  Definition order_dom {A B:Type} (m : IntMap.ptrie A) (m': IntMap.ptrie B) : Prop :=
    forall i, IntMap.get' i m <> None -> IntMap.get' i m' <> None.


  Definition wf_watch_map (m : watch_map) :=
    IntMapForall (fun x => wf_map (fst x) /\ wf_map (snd x)) m.

  Definition valid_index (hm : hmap) (i : int) :=
    exists f, has_form hm f /\ f.(id) = i.

  Definition wf_units_def {A:Type} (u: IntMap.ptrie A) (m: hmap) : Prop :=
    forall i, IntMap.get' i u <> None -> valid_index m i.

  Record wf_pset (hm: hmap) (ps: LitSet.t) :=
    {
    wf_map_pset : LitSet.wf ps;
    wf_index  : forall i, LitSet.mem i ps = true -> valid_index hm i
    }.

  Definition is_literal_of_pset (d : LitSet.t) (l : literal) :=
    IntMap.get' (id_of_literal l) d = Some None \/
    IntMap.get' (id_of_literal l) d = Some (Some (is_positive_literal l)).

  Definition is_literal_of_units  (u: IntMap.ptrie (Annot.t bool)) (l:literal) :=
    exists b, IntMap.get' (id_of_literal l) u =  Some b /\ is_positive_literal l = Annot.elt b.

  Definition is_literal_of_state  (st: state) (l:  literal) :=
    is_literal_of_units  (units st) l \/ In l (List.map Annot.elt (unit_stack st)).

  Definition is_pset_units (u: IntMap.ptrie (Annot.t bool)) (d: LitSet.t) :=
    exists i b, IntMap.get' i u = Some b /\ d = Annot.deps b.

  Definition is_pset_stack (u: list  (Annot.t literal)) (d: LitSet.t) :=
    exists a, In a u /\ d = Annot.deps a.

  Definition is_pset_state (st: state) (d: LitSet.t) :=
    is_pset_units (units st) d \/
    is_pset_stack (unit_stack st) d.

  Definition is_covered_deps (hm: hmap) (p: LitSet.t) (Q: literal -> Prop) :=
    forall l,
      has_literal hm l ->
      is_literal_of_pset p l -> Q l.

  Definition all_deps_covered (hm: hmap) (P : LitSet.t -> Prop) (Q : literal -> Prop) :=
    forall p, P p -> is_covered_deps hm p Q.

  Definition only_deps (st: state) := all_deps_covered (hconsmap st) (is_pset_state st) (is_literal_of_state st).

  Definition wf_units_lit {A:Type} (u: IntMap.ptrie (Annot.t A)) (m: hmap) : Prop :=
    forall i b, IntMap.get' i u = Some b -> valid_index m i /\ wf_pset m (Annot.deps b).

  Record check_annot {A: Type} (C: hmap -> A -> Prop)  (h: hmap) (a: Annot.t A) : Prop :=
    {
    wf_deps : wf_pset h (Annot.deps a);
    wf_elt  : Annot.lift (C h) a;
    }.

  Definition has_clauses (m : hmap) (cl : watch_map) :=
    ForallWatchedClause (check_annot  has_watched_clause m) cl.

  Record wf_state  (st : state) : Prop :=
    {
    wf_hm      : wf (hconsmap st);
    wf_arrows  : List.Forall (has_literal (hconsmap st)) (arrows st) ;
    wf_wn_m    : wf_map (wneg st);
    wf_wneg    : wf_units_def (wneg st) (hconsmap st);
    wf_units   : wf_units_lit (units st) (hconsmap st);
    wf_stack   : List.Forall (check_annot  has_literal  (hconsmap st)) (unit_stack st);
    wf_clauses : has_clauses  (hconsmap st) (clauses st);
    wf_units_m : wf_map (units st);
    wf_clauses_m1 : wf_map (clauses st);
    wf_clauses_m2 : wf_watch_map (clauses st);
    }.

  Definition eval_obool (b:OBool.t) (f : HFormula) :=
    match b with
    | None => False
    | Some b => eval_literal (literal_of_bool b f)
    end.

  Definition eval_pset (m: hmap)  (ps: LitSet.t) :=
    forall f b,
      has_form m f ->
      OBool.lift_has_bool b (LitSet.get  f.(id) ps) -> eval_literal (literal_of_bool b f).

  Definition eval_annot {A: Type}  (eval : A -> Prop)  (m: hmap) (e: Annot.t A) :=
    eval_pset m (Annot.deps e) -> eval (Annot.elt e).


  Definition eval_annot_units  (u: IntMap.ptrie (Annot.t bool)) (m: hmap) : Prop :=
    forall_units (eval_annot eval_literal m) m u.

  Definition eval_annot_clauses  (m: hmap) (cl : watch_map) :=
    ForallWatchedClause (eval_annot  eval_watched_clause m) cl.

  Record eval_annot_state (st: state) : Prop :=
    {
    ev_an_stack : List.Forall (eval_annot  eval_literal (hconsmap st)) (unit_stack st);
    ev_an_units : eval_annot_units (units st) (hconsmap st);
    ev_an_clauses : eval_annot_clauses  (hconsmap st) (clauses st)
    }.

  Record eval_state  (st: state) : Prop :=
    {
    ev_units : eval_units (hconsmap st) (units st) ;
    ev_stack : eval_stack (unit_stack st) ;
    ev_clauses :  eval_clauses (clauses st)
    }.


  Definition has_oform (m: hmap) (o : option HFormula) : Prop :=
    match o with
    | None => True
    | Some f => has_form m f
    end.

  Lemma extract_unit_eval_state :
    forall st l st',
      eval_state st ->
      extract_unit st = Some (l,st') ->
      Annot.lift eval_literal l /\ eval_state st'.
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

  Lemma eval_annot_extract_state :
    forall st l st',
      eval_annot_state st ->
      extract_unit st = Some (l,st') ->
      eval_annot  eval_literal (hconsmap st) l /\ eval_annot_state st'.
  Proof.
    unfold extract_unit.
    intros.
    destruct (unit_stack st) eqn:EQ; try congruence.
    inv H0.
    destruct H.
    rewrite EQ in ev_an_stack0.
    unfold eval_stack in ev_an_stack0.
    inv ev_an_stack0.
    split ; auto.
    constructor; simpl ; auto.
  Qed.

  Lemma id_of_literal_of_bool : forall b f,
  (id_of_literal (literal_of_bool b f)) = f.(id).
  Proof.
    destruct b ; simpl ; auto.
  Qed.

  Lemma is_positive_literal_of_bool : forall b f,
      is_positive_literal (literal_of_bool b f) = b.
  Proof.
    unfold literal_of_bool.
    destruct b ; reflexivity.
  Qed.

  Lemma has_form_find_lit :
    forall m f lit
           (HL : has_form m f)
           (EU : eval_units m lit),
      match IntMap.get' (id f) lit with
      | None => True
      | Some b => eval_literal (Annot.lift literal_of_bool b f)
      end.
  Proof.
    intros.
    unfold eval_units in EU.
    unfold forall_units in EU.
    destruct (IntMap.get' (id f) lit) eqn:EQ; auto.
    assert (units_has_literal m lit (Annot.mk ((Annot.lift literal_of_bool t0 f)) (Annot.deps t0))).
    {
      unfold units_has_literal; intros.
      unfold Annot.lift,Annot.map.
      simpl. rewrite id_of_literal_of_bool.
      rewrite is_positive_literal_of_bool.
      rewrite EQ.
      destruct t0 ; simpl ; split ; auto.
      destruct elt0 ; auto.
    }
    apply EU in H.
    auto.
  Qed.

  Lemma is_FF_true : forall f, is_FF f = true -> f = FF.
  Proof.
    destruct f ; simpl; try congruence.
    reflexivity.
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
    apply is_FF_true in H3. subst.
    assert (id0 = 0) by lia.
    subst. reflexivity.
  Qed.


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

  Lemma is_unsat_correct :
    forall m lit (l:Annot.t literal) d
           (HL : Annot.lift (has_literal m) l)
           (EL : Annot.lift eval_literal l)
           (EU : eval_units m lit)
           (US : is_unsat lit l = Some d),
      False.
  Proof.
    unfold is_unsat.
    unfold Annot.lift. intros.
    destruct (Annot.elt l).
    - destruct (is_hFF f) eqn:FF.
      + apply is_hFF_true in FF. subst.
      simpl in EL ; auto.
      +
      generalize (has_form_find_lit _ _ _ HL EU).
      destruct (IntMap.get'  (id f) lit); try congruence.
      unfold Annot.lift in *.
      destruct_in_hyp US b; try discriminate.
      rewrite negb_true_iff in b.
      rewrite b. simpl. tauto.
    - simpl; intros.
      generalize (has_form_find_lit _ _ _ HL EU).
      destruct (IntMap.get' (id f) lit); try congruence.
      unfold Annot.lift.
      destruct_in_hyp US b; try discriminate.
      simpl. auto.
  Qed.

  Lemma eval_pset_union : forall m s1 s2,
      LitSet.wf s1 -> LitSet.wf s2 ->
      (eval_pset m (LitSet.union s1 s2) <->
       (eval_pset m s1 /\ eval_pset m s2)).
  Proof.
    intros.
    unfold eval_pset.
    split ; intros.
    - split ; intros.
      apply H1;auto.
      rewrite <- LitSet.lift_has_bool_union;auto.
      apply H1; auto.
      rewrite <- LitSet.lift_has_bool_union;auto.
    -
      rewrite <- LitSet.lift_has_bool_union in H3 by assumption.
      intuition.
    Qed.


    Lemma has_form_of_literal : forall m l,
      has_literal m l <->
      has_form m (form_of_literal l).
  Proof.
    destruct l ; simpl in *; tauto.
  Qed.


  Lemma units_has_literal_of_form :
    forall m u f b,
      IntMap.get' f.(id) u = Some b ->
      has_form m f ->
      (units_has_literal m u ((Annot.map  (fun b => literal_of_bool b f) b))).
  Proof.
    intros.
    unfold units_has_literal.
    unfold Annot.lift, Annot.map.
    simpl. rewrite id_of_literal_of_bool.
    rewrite H. destruct b ; simpl.
    rewrite is_positive_literal_of_bool.
    split ; auto.
    destruct elt0 ; auto.
  Qed.


  Lemma eval_units_find_lit :
    forall m h u b
           (EV : eval_units m u)
           (HAS : has_literal m h)
           (FD : find_lit h u = Some b),
      (if Annot.elt b then eval_literal h else
         eval_literal (neg_literal h)).
  Proof.
    unfold eval_units ; intros.
    rewrite has_form_of_literal in HAS.
    unfold find_lit in FD.
    destruct h; simpl in *.
    -
      apply units_has_literal_of_form with (m:=m) in FD ; auto.
      apply EV in FD.
      unfold Annot.lift, Annot.map in FD.
      simpl in *.
      destruct (Annot.elt b) ; auto.
    -
      apply neg_bool_some in FD.
      apply units_has_literal_of_form with (m:=m) in FD ; auto.
      apply EV in FD.
      unfold Annot.lift, Annot.map in FD.
      simpl in *.
      destruct (Annot.elt b) ; auto.
  Qed.

  Lemma eval_annot_units_find_lit :
    forall m h u b
           (EV : eval_annot_units u m)
           (HAS : has_literal m h)
           (FD : find_lit h u = Some b),
      eval_annot eval_literal m (Annot.map (fun (b:bool) => if b then h else neg_literal h) b).
  Proof.
    unfold eval_annot_units ; intros.
    rewrite has_form_of_literal in HAS.
    unfold find_lit in FD.
    destruct h; simpl in *.
    -
      apply units_has_literal_of_form with (m:=m) in FD ; auto.
    -
      apply neg_bool_some in FD.
      apply units_has_literal_of_form with (m:=m) in FD ; auto.
      apply EV in FD.
      unfold Annot.lift, Annot.map in FD.
      simpl in *.
      unfold eval_annot,Annot.map in *; simpl in *.
      destruct (Annot.elt b) ; auto.
  Qed.


  Lemma eval_annot_is_unsat :
    forall m u (l:Annot.t literal) d
           (WL : check_annot has_literal m l)
           (WU : wf_units_lit u m)
           (ED : eval_annot eval_literal m l)
           (EU : eval_annot_units u m)
           (US : is_unsat u l = Some d),
      eval_pset m d -> False.
  Proof.
  intros.
  unfold is_unsat in US.
  destruct (Annot.elt l) eqn:EQ.
  - destruct (is_hFF f) eqn:FF.
    + apply is_hFF_true in FF. subst.
      inv US.  unfold eval_annot in ED.
      rewrite EQ in ED.
      apply ED ;auto.
    +
      destruct (IntMap.get'  (id f) u) eqn:FD; try congruence.
      assert (FD':= FD).
      apply units_has_literal_of_form with (m:= m) in FD; auto.
      apply EU in FD.
      apply WU in FD'. destruct FD' as (WI & WFT).
      unfold eval_annot, Annot.map, Annot.lift in *.
      simpl in *.
      destruct_in_hyp US b; try discriminate.
      rewrite negb_true_iff in b.
      inv US.
      apply eval_pset_union in H; auto.
      destruct H as (E1 & E2).
      rewrite b in FD.
      simpl in FD.
      apply FD ;auto.
      rewrite EQ in ED.
      apply ED;auto.
      destruct WFT ; auto.
      destruct WL;auto.
      destruct wf_deps0;auto.
      destruct WL;auto.
      unfold Annot.lift in wf_elt0.
      rewrite EQ in wf_elt0.
      auto.
  - simpl; intros.
    destruct (IntMap.get'  (id f) u) eqn:FD; try congruence.
    assert (FD':= FD).
    apply units_has_literal_of_form with (m:= m) in FD; auto.
    apply EU in FD.
    apply WU in FD'. destruct FD' as (WI & WFT).
    unfold eval_annot, Annot.map, Annot.lift in *.
    simpl in *.
    destruct_in_hyp US b; try discriminate.
    inv US.
    apply eval_pset_union in H; auto.
    destruct H as (E1 & E2).
    simpl in FD.
    rewrite EQ in ED.
    simpl in ED.
    apply ED;auto.
    destruct WFT ; auto.
    destruct WL;auto.
    destruct wf_deps0;auto.
    destruct WL;auto.
    unfold Annot.lift in wf_elt0.
    rewrite EQ in wf_elt0.
    auto.
  Qed.

  Lemma success_correct :
    forall m g u l d
           (HASG : has_oform m g)
           (WFL  : Annot.lift (has_literal m) l)
           (SUC  : success g u l = Some d)
           (EU   : eval_units m u)
           (EL   : Annot.lift eval_literal l),
      eval_ohformula g.
  Proof.
    intros.
    unfold success in *.
    destruct g; simpl.
    destruct (is_goalb h (Annot.elt l)) eqn:G.
    - simpl in HASG.
      unfold Annot.lift in *.
      destruct (Annot.elt l) ; simpl in G ; try discriminate.
      assert (G2 : id f = id h) by lia.
      apply has_form_eq with (m:=m) in G2;auto.
      subst; auto.
    - exfalso ; eapply is_unsat_correct ; eauto.
    - exfalso ; eapply is_unsat_correct ; eauto.
  Qed.


  Lemma eval_annot_success :
    forall m g u l d
           (HASG : has_oform m g)
           (WFU  : wf_units_lit u m)
           (HL   : eval_annot eval_literal m l)
           (CL   : check_annot has_literal m l)
           (WFL  : Annot.lift (has_literal m) l)
           (SUC  : success g u l = Some d)
           (EU   : eval_annot_units u m),
           (eval_pset m d -> eval_ohformula g).
  Proof.
    intros.
    unfold success in *.
    destruct g; simpl.
    destruct (is_goalb h (Annot.elt l)) eqn:G.
    - simpl in HASG.
      inv SUC.
      unfold Annot.lift in *.
      unfold eval_annot in HL.
      destruct (Annot.elt l) ; simpl in G ; try discriminate.
      assert (G2 : id f = id h) by lia.
      apply has_form_eq with (m:=m) in G2;auto.
      subst; auto. apply HL;auto.
    - exfalso ; eapply eval_annot_is_unsat ; eauto.
    - exfalso ; eapply eval_annot_is_unsat ; eauto.
  Qed.


  Lemma hconsmap_set_unit_stack : forall l st,
      hconsmap (set_unit_stack l st) = hconsmap st.
  Proof.
    unfold set_unit_stack.
    reflexivity.
  Qed.

  Lemma units_set_unit_stack: forall s st,
      units (set_unit_stack s st) = units st.
  Proof.
    unfold set_unit_stack.
    reflexivity.
  Qed.


(*  Lemma only_set_unit_stack : forall x s st
      (OD : only_literal_deps st)
      (EQ : unit_stack st = x :: s),
      only_literal_deps (set_unit_stack s st).
  Proof.
    intros.
    unfold only_literal_deps in *.
    intros.
    rewrite hconsmap_set_unit_stack in *.
    specialize (OD l H).
    destruct H0.
    - left.
      rewrite units_set_unit_stack in *.
      apply is_literal_of_state_left in H0.
      apply OD in
*)

  
  Lemma wf_extract_unit : forall st l st',
      wf_state st ->
      extract_unit st = Some (l, st') ->
      wf_state st' /\ check_annot has_literal (hconsmap st') l.
  Proof.
    intros.
    unfold extract_unit in H0.
    destruct H.
    destruct (unit_stack st) eqn:EQ; try discriminate.
    inv H0.
    inv wf_stack0.
    split ; auto.
    constructor ; auto.

  Qed.

  Lemma wf_insert_unit :
    forall l st
           (WF : wf_state st)
           (WFAL : check_annot has_literal  (hconsmap st) l),
      wf_state (insert_unit l st).
  Proof.
    intros.
    destruct WF ; constructor ; simpl ; auto.
  Qed.

  Lemma eval_insert_unit :
    forall l st
           (WF : wf_state st)
           (ES : eval_state st)
           (EL : Annot.lift eval_literal l),
      eval_state (insert_unit l st).
  Proof.
    unfold insert_unit.
    intros.
    destruct ES ; constructor ; simpl ; auto.
    constructor;auto.
  Qed.

  Lemma eval_annot_insert_unit :
    forall l st
           (WF : wf_state st)
           (ES : eval_annot_state st)
           (EL : eval_annot eval_literal (hconsmap st) l),
      eval_annot_state (insert_unit l st).
  Proof.
    unfold insert_unit.
    intros.
    destruct ES ; constructor ; simpl ; auto.
  Qed.

  Lemma wf_remove_clauses :
    forall l st
           (WF : wf_state st),
      wf_state (remove_clauses l st).
  Proof.
    intros.
    destruct WF ; constructor ; simpl ; auto.
    - unfold has_clauses in *.
      apply IntMapForallRemove; auto.
    - apply IntMap.wf_remove'; auto.
    - unfold wf_watch_map in *.
      unfold IntMapForall in *.
      intros.
      rewrite grspec in H; auto.
      destruct (eqs k (id_of_literal l)); try congruence.
      eauto.
  Qed.

  Lemma eval_remove_clauses :
    forall l st
           (WF : wf_state st)
           (ES : eval_state st),
      eval_state  (remove_clauses l st).
  Proof.
    intros.
    destruct ES ; constructor ; simpl ; auto.
    unfold eval_clauses in * ; intros.
    apply IntMapForallRemove;auto.
    destruct WF ; auto.
  Qed.

  Lemma eval_annot_remove_clauses :
    forall l st
           (WF : wf_state st)
           (ES : eval_annot_state st),
      eval_annot_state  (remove_clauses l st).
  Proof.
    intros.
    destruct ES ; constructor ; simpl ; auto.
    unfold eval_clauses in * ; intros.
    apply IntMapForallRemove;auto.
    destruct WF ; auto.
  Qed.

  Lemma ForallWatchedClause_find_clauses :
    forall P i cl ln lp
           (EC : ForallWatchedClause P  cl)
           (FD : find_clauses i cl = (ln, lp)),
      IntMapForall P ln /\
      IntMapForall P lp.
  Proof.
    unfold find_clauses.
    intros.
    destruct (IntMap.get' i cl) eqn:EQ.
    -  destruct w. inv FD.
       apply EC in EQ; auto.
    - inv FD.
      split ; apply IntMapForallEmpty.
  Qed.



  Lemma literal_eq : forall l,
      literal_of_bool (is_positive_literal l) (form_of_literal l) = l.
  Proof.
    destruct l ; simpl ; auto.
  Qed.






  Lemma eval_neg_literal : forall h,
      eval_literal (neg_literal h) -> ~ eval_literal h.
  Proof.
    destruct h ; simpl ; auto.
  Qed.



  Lemma has_clause_reduce :
    forall m u w cl an
           (HASL : has_literal m w)
           (HASL : Forall (has_literal m) cl),
           Annot.lift (has_clause m) (reduce u an w cl).
  Proof.
    induction cl; simpl.
    - auto.
    - intros.
      inv HASL0.
      destruct (find_lit a u).
      destruct (Annot.elt t0) ; auto.
      +  unfold Annot.lift.
         simpl ; auto.
      + simpl.
        unfold Annot.lift.
        simpl.
        unfold has_watched_clause ; auto.
  Qed.


    Lemma check_annot_find_lit :
    forall hm a u b
           (FL: find_lit a u = Some b)
           (WF: wf_units_lit u hm),
      wf_pset  hm (Annot.deps b).
  Proof.
    intros.
    unfold find_lit in FL.
    destruct a.
    - apply WF in FL; auto. tauto.
    - apply neg_bool_some in FL.
      apply WF in FL ; auto.
      tauto.
  Qed.

  Lemma wf_pset_empty : forall hm, wf_pset hm LitSet.empty.
  Proof.
    intros.
    constructor;auto.
    constructor.
    intros. unfold LitSet.mem in H.
    rewrite PTrie.gmem' in H.
    unfold LitSet.empty in H.
    rewrite empty_o in H. simpl in H. congruence.
  Qed.

  Hint Resolve wf_pset_empty : wf.

  Lemma wf_pset_union : forall hm d d',
      wf_pset hm d -> wf_pset hm d' ->
      wf_pset hm (LitSet.union d d').
  Proof.
    intros.
    destruct H, H0 ; constructor ; auto.
    apply LitSet.wf_union; auto.
    intros.
    rewrite <- LitSet.mem_union in H by auto.
    intuition.
  Qed.


  Lemma wf_pset_remove : forall hm i d,
      wf_pset hm d ->
      wf_pset hm (LitSet.remove i d).
  Proof.
    intros.
    destruct H ; constructor ; auto.
    apply PTrie.wf_remove'; auto.
    intros.
    apply wf_index0.
    unfold LitSet.mem, LitSet.remove in *.
    rewrite PTrie.gmem' in *.
    rewrite grspec in H by assumption.
    destruct (eqs i0 i). discriminate.
    auto.
  Qed.




  Lemma wf_pset_reduce :
    forall u m cl d l
           (WFU : wf_units_lit u m)
           (WFP : wf_pset m d),
      wf_pset m
              (Annot.deps (reduce u d l cl)).
  Proof.
    induction cl.
    - simpl; auto.
    - simpl.
      intros.
      destruct_in_goal FD.
      + apply check_annot_find_lit with (hm:=m) in FD ; auto.
        destruct_in_goal A.
        apply wf_pset_empty.
        apply IHcl; auto.
        apply wf_pset_union;auto.
      + simpl; auto.
  Qed.


  Lemma check_annot_TRUE : forall hm,
    check_annot has_clause  hm (Annot.mk_elt TRUE).
  Proof.
    constructor ; auto.
    apply wf_pset_empty.
    exact I.
  Qed.

  Lemma wf_shorten_clause :
    forall m u cl an
           (WFU : wf_units_lit u m)
           (WFA : wf_pset m an)
           (WFC : has_watched_clause m cl),
      check_annot has_clause m (shorten_clause u an cl).
  Proof.
    intros.
    unfold shorten_clause.
    unfold has_watched_clause in WFC.
    inv WFC. inv H2.
    destruct (find_lit (watch1 cl) u) eqn:EQ.
    -
      apply check_annot_find_lit with (hm:=m) in EQ; auto.
      destruct (Annot.elt t0).
      + apply check_annot_TRUE.
      + unfold Annot.lift.
        split.
        apply wf_pset_reduce;auto.
        apply wf_pset_union;auto.
        apply has_clause_reduce; auto.
    -
      destruct (find_lit (watch2 cl) u) eqn:EQ'.
      apply check_annot_find_lit with (hm:=m) in EQ'; auto.
      destruct (Annot.elt t0) ; simpl ; auto.
      + apply check_annot_TRUE.
      + split.
        apply wf_pset_reduce; auto.
        apply wf_pset_union;auto.
        apply has_clause_reduce; auto.
      + split;auto.
        repeat constructor ; auto.
  Qed.

  Definition ohold {A: Type} (P: A -> Prop) (o : option A) :=
    match o with
    | None => True
    | Some v => P v
    end.

  Definition has_conflict_clause (m: hmap) (l: list literal) :=
    Forall (has_literal m) l.

  Lemma wf_reduce_lits :
    forall m u cl
           (WFU: wf_units_lit u m)
           (WFC : Forall (has_literal m) cl)
           an (WFA : wf_pset m an)
    ,
      ohold (check_annot has_conflict_clause m) (reduce_lits u an cl).
  Proof.
    intros m u cl WFU WFC.
    induction WFC ; simpl.
    -  constructor.
       auto. constructor.
    - destruct (find_lit x  u) eqn:FIND.
      + destruct (Annot.elt t0) ; simpl ; auto.
        intros.
        apply IHWFC.
        apply wf_pset_union;auto.
        apply check_annot_find_lit with (hm:=m) in FIND ;auto.
      +
        intros.
        specialize (IHWFC an WFA).
        destruct (reduce_lits u  an l); simpl;auto.
        simpl in *.
        unfold Annot.lift, Annot.map in *.
        destruct IHWFC ; constructor ;auto.
        constructor;auto.
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




    Lemma eval_reduce :
    forall m u cl w an
           (EV : eval_units m u)
           (HL : Forall (has_literal m) cl)
           (EC : eval_literal_rec w (eval_literal_list cl)),
      Annot.lift eval_clause (reduce u an w cl).
  Proof.
    induction cl; simpl.
    - destruct w ; simpl; tauto.
    - intros.
      destruct (find_lit a u) eqn:FD.
      + inv HL.
        apply eval_units_find_lit with (m:=m) in FD; auto.
        destruct (Annot.elt t0).
        exact I.
        apply IHcl; auto.
        apply eval_literal_rec_swap in EC ; auto.
      + simpl.
        unfold eval_watched_clause.
        simpl.
        auto.
  Qed.

    Lemma eval_annot_TRUE : forall m,
      eval_annot eval_clause m {| Annot.elt := TRUE; Annot.deps := LitSet.empty |}.
  Proof.
    repeat intro.
    simpl. exact I.
  Qed.

  Lemma eval_annot_reduce :
    forall m u cl w an
           (WF : wf_units_lit u m)
           (WA : wf_pset m an)
           (EV : eval_annot_units u m)
           (HL : Forall (has_literal m) cl)
           (EC : eval_pset m an -> eval_literal_rec w (eval_literal_list cl)),
      eval_annot eval_clause m (reduce u an w cl).
  Proof.
    induction cl; simpl.
    - repeat intro ; simpl in *.
      destruct w; simpl in *. tauto. tauto.
    - intros.
      destruct (find_lit a u) eqn:FD.
      + assert (FD':=FD).
        apply check_annot_find_lit with (hm:=m) in FD'; auto.
        inv HL.
        apply eval_annot_units_find_lit with (m:=m) in FD; auto.
        unfold Annot.map in FD.
        destruct (Annot.elt t0).
        apply eval_annot_TRUE.
        apply IHcl; auto.
        apply wf_pset_union;auto.
        intro U. destruct FD'. destruct WA.
        apply eval_pset_union in U as (ET &EA); auto.
        specialize (EC EA).
        apply eval_literal_rec_swap in EC ; auto.
      + unfold eval_annot. simpl.
        auto.
  Qed.


  Lemma shorten_clause_correct :
    forall m u cl an
           (EV : eval_units m u)
           (WFC : has_watched_clause m cl)
           (EC : eval_watched_clause cl),
      Annot.lift eval_clause (shorten_clause u an cl).
  Proof.
    unfold shorten_clause;intros.
    assert (HW1 : has_literal m (watch1 cl)).
    { inv WFC. auto. }
    assert (HW2 : has_literal m (watch2 cl)).
    { inv WFC. inv H2; auto. }
    assert (HUW : Forall (has_literal m) (unwatched cl)).
    { inv WFC. inv H2; auto. }
    destruct (find_lit (watch1 cl) u) eqn:FD1.
    apply eval_units_find_lit with (m:=m) in FD1; auto.
    destruct (Annot.elt t0) ; simpl ; auto.
    exact I.
    - unfold eval_watched_clause in EC.
      simpl in EC.
      apply eval_neg_literal_rec in EC; auto.
      apply  eval_reduce with (m:=m); auto.
    - destruct (find_lit (watch2 cl) u) eqn:FD2; simpl; auto.
      apply eval_units_find_lit with (m:=m) in FD2; auto.
      destruct (Annot.elt t0) ; simpl ; auto.
      exact I.
      apply  eval_reduce with (m:=m); auto.
      unfold eval_watched_clause in EC.
      simpl in EC.
      apply eval_literal_rec_swap in EC; auto.
  Qed.

  Lemma eval_reduce_lits :
    forall m u
           (EV : eval_units m u)
           cl
           (WFC : Forall (has_literal m) cl) an
           (EC : eval_literal_list cl),
      ohold (Annot.lift eval_literal_list) (reduce_lits u an cl).
  Proof.
    intros m u EV cl WFC. induction WFC.
    - simpl in *. auto.
    - simpl in *.
      destruct (find_lit x u) eqn:EQ.
      apply eval_units_find_lit with (m:=m) in EQ; auto.
      destruct (Annot.elt t0) ; simpl ; auto.
      intros.
      apply eval_neg_literal_rec in EC; auto.
      intros. generalize (IHWFC an).
      destruct (reduce_lits u an l); simpl in * ; auto.
      unfold Annot.map, Annot.lift.
      simpl.
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
      IntMapForall2 (check_annot has_watched_clause m) (ln,lp) /\
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
    destruct (is_positive_literal l); auto with wf.
  Qed.

  Hint Resolve wf_map_add_clause : wf.


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
    - inv H; simpl ; split ; auto with wf.
    - inv H; simpl ; split ; auto with wf.
  Qed.

  Lemma ForallWatchedClause_add_clause :
    forall (P: Annot.t watched_clause -> Prop) l i wc cls
           (WFM : wf_map cls)
           (WFW : wf_watch_map cls)
           (PWC : P wc)
           (ALL : ForallWatchedClause P cls),
      ForallWatchedClause P (add_clause l i wc cls).
  Proof.
    unfold add_clause. intros.
    destruct(find_clauses (id_of_literal l) cls) as (ln,lp) eqn:EQ.
    assert (EQ':= EQ).
    apply ForallWatchedClause_find_clauses with (P:=P) in EQ; auto.
    destruct EQ as (LN & LP).
    apply wf_find_clauses2  in EQ'; auto.
    destruct EQ' as (WLN & WLP).
    destruct (is_positive_literal l).
    apply IntMapForallAdd;auto.
    split ; simpl ; auto.
    apply IntMapForallAdd;auto.
    apply IntMapForallAdd;auto.
    split ; simpl ; auto.
    apply IntMapForallAdd;auto.
  Qed.

  Lemma wf_add_clause :
    forall m l i wc cls
           (WF: wf_map cls)
           (WFW : wf_watch_map cls)
           (WF : has_clauses m cls)
           (WCL : check_annot has_watched_clause m wc),
      has_clauses m (add_clause l i wc cls).
  Proof.
    unfold has_clauses.
    intros.
    apply ForallWatchedClause_add_clause; auto.
  Qed.

  Lemma eval_add_clause :
    forall l i wc cls
           (WFM : wf_map cls)
           (WF: wf_watch_map cls)
           (EC: eval_clauses cls)
           (EW: Annot.lift eval_watched_clause wc),
      eval_clauses (add_clause l i wc cls).
  Proof.
    unfold eval_clauses.
    intros.
    apply ForallWatchedClause_add_clause; auto.
  Qed.

  Lemma eval_annot_add_clause :
    forall m l i wc cls
           (WFM : wf_map cls)
           (WF: wf_watch_map cls)
           (EC: eval_annot_clauses m cls)
           (EW: eval_annot eval_watched_clause m wc),
      eval_annot_clauses m (add_clause l i wc cls).
  Proof.
    unfold eval_annot_clauses.
    intros.
    apply ForallWatchedClause_add_clause; auto.
  Qed.



  Lemma wf_add_wneg_lit :
    forall l wn hm
           (WFM :  wf_map wn)
           (WF: wf_units_def wn hm)
           (HL : has_literal hm l),
      wf_units_def (add_wneg_lit l wn) hm.
  Proof.
    unfold add_wneg_lit.
    intros.
    destruct l ; auto.
    unfold wf_units_def in *.
    intros.
    rewrite gsspec in H; auto.
    destruct (eqs i (id f)) ; auto.
    simpl in HL.
    exists f ; simpl ; auto.
  Qed.

  Lemma wf_map_add_wneg_lit : forall l wn,
      wf_map wn ->
      wf_map (add_wneg_lit l wn).
  Proof.
    unfold add_wneg_lit.
    destruct l; auto.
    intros.
    apply wf_map_add; auto.
  Qed.

  Lemma wf_add_wneg_wcl :
    forall wn hm cl
           (WFM : wf_map wn)
           (WF: wf_units_def wn hm)
           (WFC: has_watched_clause hm cl),
      wf_units_def (add_wneg_wcl wn cl) hm.
  Proof.
    unfold add_wneg_wcl.
    intros.
    unfold has_watched_clause in WFC.
    inv WFC. inv H2.
    apply wf_add_wneg_lit; auto.
    apply wf_map_add_wneg_lit ; auto.
    apply wf_add_wneg_lit;auto.
  Qed.

  Lemma wf_map_add_wneg_wcl :
    forall m cl,
      wf_map m ->
      wf_map (add_wneg_wcl m cl).
  Proof.
    unfold add_wneg_wcl.
    intros.
    apply wf_map_add_wneg_lit;auto.
    apply wf_map_add_wneg_lit;auto.
  Qed.


  Lemma wf_insert_lit_clause :
    forall l id cl st
           (WFS : wf_state st)
           (WFL : has_literal (hconsmap st) l)
           (WFC : check_annot  has_watched_clause (hconsmap st) cl),
           wf_state (insert_lit_clause l id cl st).
  Proof.
    intros.
    destruct WFS ; simpl in *.
    constructor ; simpl ; auto with wf.
    - apply wf_map_add_wneg_wcl;auto.
    - apply wf_add_wneg_wcl ; auto.
      destruct WFC ; auto.
    - apply wf_add_clause; auto.
    - apply wf_watch_map_add_clause; auto.
  Qed.

  Lemma eval_insert_lit_clause :
    forall u id cl st
           (WF : wf_state st)
           (ES : eval_state st)
           (ECL : Annot.lift eval_watched_clause cl),
      eval_state (insert_lit_clause u id cl st).
  Proof.
    unfold insert_lit_clause.
    intros. destruct st ; destruct ES ; destruct WF ; constructor ; simpl in *; auto.
    apply eval_add_clause;auto.
  Qed.

  Lemma eval_annot_insert_lit_clause :
    forall u id cl st
           (WF : wf_state st)
           (ES : eval_annot_state st)
           (ECL : eval_annot eval_watched_clause (hconsmap st) cl),
      eval_annot_state (insert_lit_clause u id cl st).
  Proof.
    unfold insert_lit_clause.
    intros. destruct st ; destruct ES ; destruct WF ; constructor ; simpl in *; auto.
    apply eval_annot_add_clause;auto.
  Qed.



  Lemma units_has_literal_add :
    forall m l u l'
           (WF : wf_map u)
           (HF : Annot.lift (has_literal m) l)
    ,
      units_has_literal m (add_literal l u) l' ->
      units_has_literal m u l' \/ l = l'.
  Proof.
    unfold units_has_literal.
    intros.
    destruct H.
    unfold add_literal in *.
    rewrite gsspec in H by auto.
    destruct (eqs (Annot.lift id_of_literal l') (id_of_literal (Annot.elt l))).
    - inv H.
      right.
      unfold Annot.lift in *.
      destruct l,l'.
      simpl in *.
      subst.
      f_equal.
      unfold id_of_literal in *.
      destruct elt1; destruct elt0 ; simpl in *; try congruence; f_equal.
      apply has_form_eq with (m:=m) ;auto.
      apply has_form_eq with (m:=m) ;auto.
    - left ; auto.
  Qed.


  Lemma forall_units_add :
    forall P m l u
           (WF : wf_map u)
           (EU:  forall_units P m u)
           (HL:Annot.lift (has_literal m) l)
           (PL: P l)
    ,
      forall_units P m (add_literal l u).
  Proof.
    intros.
    unfold forall_units in *.
    intros.
    apply units_has_literal_add in H; auto.
    destruct H ; auto.
    congruence.
  Qed.



  Lemma eval_add_literal :
    forall m l u
           (WF : wf_map u)
           (EU : eval_units m u)
           (EL : Annot.lift eval_literal l)
           (HL : Annot.lift (has_literal m) l),
      eval_units m (add_literal l u).
  Proof.
    unfold eval_units.
    intros.
    apply forall_units_add; auto.
  Qed.

  Lemma eval_annot_add_literal :
    forall m l u
           (WF : wf_map u)
           (EU : eval_annot_units u m)
           (HL : Annot.lift (has_literal m) l)
           (EL : eval_annot eval_literal m l),
      eval_annot_units  (add_literal l u) m.
  Proof.
    unfold eval_units.
    intros.
    unfold eval_annot_units.
    apply forall_units_add; auto.
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

  Hint Resolve wf_map_add_literal : wf.

  Lemma wf_remove_wneg :
    forall w l hm
           (WFM : wf_map w)
           (WF: wf_units_def w hm),
      wf_units_def (remove_wneg l w) hm.
  Proof.
    unfold wf_units_def, remove_wneg.
    intros.
    rewrite grspec in H by assumption.
    destruct (eqs i (id_of_literal l)).
    congruence.
    apply WF ; auto.
  Qed.

  Lemma IntMapForall_add_literal : forall P l u,
  wf_map u ->
  IntMapForall P u ->
  P (Annot.map is_positive_literal l) ->
  IntMapForall P (add_literal l u).
  Proof.
    unfold add_literal.
    intros.
    apply IntMapForallAdd; auto.
  Qed.


  Lemma wf_insert_literal : forall l st
           (WF : wf_state st)
           (HF : check_annot has_literal (hconsmap st) l),
      wf_state (insert_literal l st).
  Proof.
    intros.
    destruct WF ; constructor ; simpl ; auto with wf.
    {
      destruct (is_neg_arrow (Annot.elt l)).
      destruct HF;
        constructor ; auto.
      auto.
    }
    -
      unfold remove_wneg.
      auto with wf.
    -  apply wf_remove_wneg; auto.
    - unfold add_literal.
      unfold wf_units_lit.
      intros.
      rewrite gsspec  in H;auto.
      destruct (eqs i (id_of_literal (Annot.elt l)) ); auto.
      inv H.
      split.
      exists (form_of_literal (Annot.elt l)).
      split.
      apply has_form_of_literal; auto.
      destruct HF ; auto.
      auto.
      destruct HF ; auto.
  Qed.

  Lemma eval_insert_literal : forall l st
           (WF : wf_state st)
           (HF : check_annot has_literal (hconsmap st) l)
           (EV : eval_state st)
           (EL : Annot.lift eval_literal l),
      eval_state (insert_literal l st) /\ wf_state (insert_literal l st).
  Proof.
    split.
    -
      unfold insert_literal.
      destruct EV ; constructor ; simpl; auto.
      eapply eval_add_literal ; eauto.
      destruct WF ; auto.
      destruct HF ; auto.
    -  apply wf_insert_literal ; auto.
  Qed.



  Lemma eval_annot_insert_literal : forall l st
           (WF : wf_state st)
           (HF : check_annot has_literal (hconsmap st) l)
           (EV : eval_annot_state st)
           (EL : eval_annot eval_literal (hconsmap st) l),
      eval_annot_state (insert_literal l st).
  Proof.
    unfold insert_literal.
    intros.
    destruct EV ; constructor ; simpl; auto.
    eapply eval_annot_add_literal ; eauto.
    destruct WF ; auto.
    destruct HF ; auto.
  Qed.


  Definition wf_result_state  (st: dresult) :=
    match st with
    | Progress st => wf_state  st
    | Success (hm,d)   => wf_pset hm d
    | Fail _   => False
    end.


  Definition eval_result_state  (st: dresult) :=
    match st with
    | Success _ => False
    | Progress st => eval_state st
    | Fail _   => True
    end.

  Definition eval_annot_result_state  (st: dresult) :=
    match st with
    | Success (h,d) => eval_pset h d -> False
    | Progress st => eval_annot_state st
    | Fail _   => True
    end.


  Definition only_result_state  (st:state) (r: dresult) :=
    match r with
    | Progress st => only_deps st
    | Success (hm,d) => is_covered_deps hm d (is_literal_of_state st)
    | Fail _   => True
    end.


Definition is_fail  {A B: Type} (p : result A B) : Prop :=
  match p with
  | Fail _ => True
  | _          => False
  end.


  Lemma fold_update_rel_correct :
    forall {A: Type} (F: A -> state -> dresult)
           (R : state -> dresult -> Prop)
           (RSucc : forall st d, R st (Success d))
           (REFL : forall st : state, R st (Progress st))
           (FOUT : forall a st, ~ is_fail (F a st))
           (RTrans : forall s1 s2 s3,
               R s1 (Progress s2) ->
               R s2 (Progress s3) ->
               R s1 (Progress s3))
           (ROK : forall a st st',
               F a st =  Progress st' -> R st (Progress st'))
           l st,
      R st (fold_update F  l st).
  Proof.
    induction l; simpl.
    - auto.
    - intros.
      generalize (FOUT a st).
      destruct (F a st) eqn:EQ; simpl; auto.
      +  tauto.
      + apply ROK in EQ.
        specialize (IHl st0).
        assert (~ is_fail (fold_update F l st0)).
        {
          clear - FOUT.
          revert st0.
          induction l ; simpl.
          congruence.
          intros. specialize (FOUT a st0).
          destruct (F a st0) ; try congruence.
          apply IHl.
        }
        destruct (fold_update F l st0); try congruence.
        simpl in H. tauto.
        intros.
        apply RSucc.
        intros.
        eapply RTrans; eauto.
  Qed.

  Lemma fold_update_not_OutOfFuel :
    forall {A: Type} (F: A -> state -> dresult)
           (FOUT : forall a st, ~ is_fail (F a st)),
      forall l st, ~ is_fail (fold_update F  l st).
  Proof.
    induction l; simpl.
    - congruence.
    - intros.
      generalize (FOUT a st).
      destruct (F a st) eqn:EQ; try congruence.
      intros.
      apply IHl.
  Qed.



  Lemma fold_update_correct :
    forall {A: Type} (F: A -> state -> dresult)
           (Q: state -> A -> Prop)
            l
           (QOK : forall a st st',
               F a st = Progress st' -> forall x, Q st x -> Q st' x)
           (FOK : forall a st,
               Q st a  ->
               wf_state st ->
               wf_result_state (F a st))

           st
           (QALL : Forall (Q st) l)
           (Acc : wf_state st),
      wf_result_state (fold_update F  l st).
  Proof.
    induction l; simpl.
    - auto.
    - intros.
      inv QALL.
      generalize (FOK _ _ H1 Acc).
      destruct (F a st) eqn:EQ; simpl; auto.
      apply IHl; auto.
      revert H2.
      apply Forall_Forall.
      intros.
      eapply QOK ; eauto.
  Qed.

  Definition hconsmap_result (o: dresult) :=
    match o with
      Fail _  => IntMap.empty _
    | Success(h,_) => h
    | Progress st => hconsmap st
    end.


Definition hconsmap_progress_r (F : dresult -> dresult) (st : dresult):=
    ~ is_fail (F st) ->
    hconsmap_result (F st) = hconsmap_result st.

Definition hconsmap_progress  (F: state -> dresult) (st:state) :=
  not (is_fail (F  st)) ->
  hconsmap_result (F st) = hconsmap st.

  Lemma eval_fold_update :
    forall {A: Type} (EVAL : A -> Prop) (WP : hmap -> A -> Prop) F l
           (WPI : forall m m', hmap_order m m' -> forall x,
                 WP m x -> WP m' x)
           (FO :
              Forall (fun cl => forall st,wf_state st ->
                            eval_state st ->WP (hconsmap st) cl ->
                            hconsmap_progress  (F cl) st /\
                            wf_result_state (F cl st) /\ eval_result_state (F cl st)) l)
           st
           (WF : wf_state st)
           (ES : eval_state  st)
           (ALL : Forall (WP (hconsmap st)) l)
           (CLS : Forall EVAL l),
      eval_result_state  (fold_update F  l st).
  Proof.
    induction l ; simpl; auto.
    intros. inv CLS. inv ALL.
    inv FO.
    specialize (H5 _  WF ES).
    destruct (H5 H3) as (HH1 & HH2 & HH3).
    unfold hconsmap_progress in *.
    destruct (F a st) ; simpl in * ; auto.
    eapply IHl ; eauto.
    revert H4.
    apply Forall_Forall; auto.
    apply WPI.
    intuition congruence.
  Qed.


  Lemma eval_annot_fold_update :
    forall {A: Type} (EVAL : A -> Prop) (WP : hmap -> A -> Prop) F l
           (WPI : forall m m', hmap_order m m' -> forall x,
                 WP m x -> WP m' x)
           (FO :
              Forall (fun cl => forall st,wf_state st ->
                            eval_annot_state st ->WP (hconsmap st) cl ->
                            hconsmap_progress  (F cl) st /\
                            wf_result_state (F cl st) /\ eval_annot_result_state (F cl st)) l)
           st
           (WF : wf_state st)
           (ES : eval_annot_state  st)
           (ALL : Forall (WP (hconsmap st)) l)
           (CLS : Forall EVAL l),
      eval_annot_result_state  (fold_update F  l st).
  Proof.
    induction l ; simpl; auto.
    intros. inv CLS. inv ALL.
    inv FO.
    specialize (H5 _  WF ES).
    destruct (H5 H3) as (HH1 & HH2 & HH3).
    unfold hconsmap_progress in *.
    destruct (F a st) ; simpl in * ; auto.
    eapply IHl ; eauto.
    revert H4.
    apply Forall_Forall; auto.
    apply WPI.
    intuition congruence.
  Qed.


Definition isMono {A: Type} (F : hmap -> A -> Prop) :=
  forall m m' (OHM : hmap_order m m')
         x  (Fm: F m x), F m' x.

  Lemma ForallMono : forall {A: Type} (F: hmap -> A -> Prop) (M : isMono F),
      isMono (fun hm l => Forall (F hm) l).
  Proof.
    unfold isMono.
    intros. revert Fm.
    apply Forall_Forall.
    apply M; auto.
  Qed.


  Lemma has_form_mono : isMono has_form.
  Proof.
    unfold isMono.
    intros.
    revert Fm.
    remember (elt x) as f.
    revert x Heqf.
    induction f using form_ind; intros.
    - destruct x; simpl in * ; try congruence.
      subst. inv Fm.
      constructor ; auto.
    - destruct x; simpl in * ; try congruence.
      subst. inv Fm.
      constructor ; auto.
    - destruct x; simpl in * ; try congruence.
      subst. inv Fm.
      eapply wf_OP; eauto.
      rewrite Forall_forall in *.
      intros.
      specialize (H4 x H0).
      eapply H ; eauto.
    -  destruct x; simpl in * ; try congruence.
      subst. inv Fm.
      eapply wf_IMPL;eauto.
      rewrite Forall_forall in *.
      intros.
      specialize (H4 x H0).
      eapply H ; eauto.
  Qed.

  Lemma has_oform_mono : isMono has_oform.
  Proof.
    unfold isMono.
    intros.
    destruct x ; simpl in *; auto.
    eapply has_form_mono;eauto.
  Qed.

  Lemma has_literal_mono : isMono has_literal.
  Proof.
    unfold isMono.
    intros.
    destruct x ; simpl in *.
    eapply has_form_mono;eauto.
    eapply has_form_mono;eauto.
  Qed.

  Lemma has_watched_clause_mono : isMono has_watched_clause.
  Proof.
    unfold isMono.
    intros.
    unfold has_watched_clause in *.
    revert Fm.
    apply Forall_Forall.
    apply has_literal_mono;auto.
  Qed.

Lemma valid_index_mono : isMono valid_index.
Proof.
  repeat intro. destruct Fm. destruct H. exists x0 ; split ; auto.
  eapply has_form_mono ; eauto.
Qed.

Lemma wf_pset_mono : forall  m m' (a: LitSet.t)
    (LE : hmap_order m m')
    (WF : wf_pset m a),
    wf_pset m' a.
Proof.
  intros.
  destruct WF ; constructor ; auto.
  intros. apply wf_index0 in H.
  destruct H. destruct H. exists x; split; auto.
  eapply has_form_mono;eauto.
Qed.


Lemma check_annot_mono : forall {A: Type}(F: hmap -> A -> Prop),
    isMono (fun hm  => Annot.lift (F hm)) ->
    isMono (check_annot F).
Proof.
  unfold isMono.
  intros.
  destruct Fm ; constructor ; auto.
  eapply wf_pset_mono; eauto.
  eapply H ; eauto.
Qed.


  Lemma wf_add_watched_clause :
  forall i wc st
         (WFC: check_annot has_watched_clause (hconsmap st) wc)
         (WFS: wf_state st),
  wf_state  (add_watched_clause st i wc).
  Proof.
    intros.
    destruct WFS ; constructor ; auto with wf.
    - simpl.
      repeat apply wf_map_add_wneg_lit; auto.
    - simpl.
      inv WFC.
      inv wf_elt0. inv H2.
      repeat apply wf_add_wneg_lit ; auto.
      apply wf_map_add_wneg_lit; auto.
    - simpl.
    apply wf_add_clause; auto with wf.
    apply wf_watch_map_add_clause;auto.
    apply wf_add_clause; auto with wf.
    - simpl.
    apply wf_map_add_clause ;auto with wf.
    - simpl.
    apply wf_watch_map_add_clause ;auto with wf.
    apply wf_watch_map_add_clause ;auto with wf.
  Qed.

  Lemma eval_add_watched_clause :
  forall i wc st
         (WF : wf_state st)
         (ES : eval_state  st)
         (EC : Annot.lift eval_watched_clause wc),
    eval_state (add_watched_clause st i wc).
  Proof.
    unfold add_watched_clause. intros.
    destruct ES ; destruct WF ; constructor ; auto.
    simpl.
    apply eval_add_clause;auto with wf.
    apply wf_watch_map_add_clause;auto.
    apply eval_add_clause;auto.
  Qed.

  Lemma eval_annot_add_watched_clause :
  forall i wc st
         (WF : wf_state st)
         (ES : eval_annot_state  st)
         (EC : eval_annot eval_watched_clause (hconsmap st) wc),
    eval_annot_state (add_watched_clause st i wc).
  Proof.
    unfold add_watched_clause. intros.
    destruct ES ; destruct WF ; constructor ; auto.
    simpl.
    apply eval_annot_add_clause;auto with wf.
    apply wf_watch_map_add_clause;auto.
    apply eval_annot_add_clause;auto.
  Qed.

  Lemma check_annot_set : forall {A B: Type} (P: hmap -> A -> Prop)
        (Q: hmap -> B -> Prop) m v v'
        (C1 : check_annot P m v)
        (HAS : Q m v')
    ,
        check_annot Q m (Annot.set v v').
  Proof.
    intros.
    destruct C1.
    constructor ; auto.
  Qed.

  Lemma check_annot_set_UNIT :
    forall m cl l
           (HCL : check_annot has_clause m cl)
           (EQ : Annot.elt cl = UNIT l),
      check_annot has_literal m (Annot.set cl l).
  Proof.
    intros.
    destruct HCL; constructor ; auto.
    unfold Annot.set, Annot.lift in *.
    rewrite EQ in *.
    auto.
  Qed.

  Lemma check_annot_set_CLAUSE : forall m cl wc
      (HCL : check_annot has_clause m cl)
      (EQ : Annot.elt cl = CLAUSE wc),
      check_annot has_watched_clause m (Annot.set cl wc).
  Proof.
    intros.
    destruct HCL; constructor; auto.
    unfold Annot.set, Annot.lift in *.
    rewrite EQ in *.
    auto.
  Qed.

  Lemma wf_insert_normalised_clause :
    forall i cl st
           (HCL : check_annot has_clause (hconsmap st) cl)
           (WF : wf_state st),
  wf_result_state (insert_normalised_clause i cl st).
  Proof.
    unfold insert_normalised_clause.
    intros.
    unfold Annot.lift in HCL.
    destruct (Annot.elt cl) eqn:EQ; simpl ; auto.
    - destruct HCL ; auto.
    - apply wf_insert_unit;auto.
      eapply check_annot_set_UNIT; eauto.
    - apply wf_add_watched_clause; auto.
      eapply check_annot_set_CLAUSE; eauto.
  Qed.

  Lemma eval_insert_normalised_clause :
    forall i cl st
           (HCL : Annot.lift (has_clause (hconsmap st)) cl)
           (WF : wf_state st)
           (ES : eval_state st)
           (EC : Annot.lift eval_clause cl),
  eval_result_state  (insert_normalised_clause i cl st).
  Proof.
    unfold insert_normalised_clause.
    intros.
    unfold Annot.lift in *.
    destruct (Annot.elt cl) ; simpl ; auto.
    - intros; apply eval_insert_unit;auto.
    - intros.
      apply eval_add_watched_clause; auto.
  Qed.


    Lemma eval_annot_insert_normalised_clause :
    forall i cl st
           (HCL : Annot.lift (has_clause (hconsmap st)) cl)
           (WF : wf_state st)
           (ES : eval_annot_state st)
           (EC : eval_annot eval_clause  (hconsmap st) cl),
  eval_annot_result_state  (insert_normalised_clause i cl st).
  Proof.
    unfold insert_normalised_clause.
    intros.
    unfold eval_annot in EC.
    destruct (Annot.elt cl) ; simpl ; auto.
    -  intros; apply eval_annot_insert_unit;auto.
    - intros.
      apply eval_annot_add_watched_clause; auto.
  Qed.

  Lemma check_annot_reduce : forall hm u l d x
      (WFU : wf_units_lit u hm)
      (HL  : has_literal hm x)
      (HLL  : Forall (has_literal hm) l)
      (WFD: wf_pset hm d),
      check_annot has_clause hm (reduce u d x l).
  Proof.
    induction l.
    - simpl. intros.
      constructor; simpl ; auto.
    - simpl.
      destruct (find_lit a u) eqn:FL.
      intros.
      destruct (Annot.elt t0); auto.
      + apply check_annot_TRUE.
      + apply check_annot_find_lit with (hm:=hm) in FL; auto.
        inv HLL.
        apply IHl ; auto.
        apply wf_pset_union; auto.
      +  intros.
         constructor;simpl; auto.
         inv HLL;auto.
         unfold Annot.lift.
         simpl.
         unfold has_watched_clause.
         constructor ; auto.
  Qed.

  Lemma check_annot_shorten_clause :
    forall hm u wc d
           (WF : wf_units_lit u hm)
           (HCL : has_watched_clause hm wc)
           (HA : wf_pset hm  d),
      check_annot has_clause hm (shorten_clause u d wc).
  Proof.
    unfold shorten_clause.
    intros.
    destruct (find_lit (watch1 wc) u) eqn:EQ1.
    - destruct (Annot.elt t0).
      + constructor.
        unfold Annot.deps.
        apply wf_pset_empty.
        constructor.
      + apply check_annot_find_lit with (hm:=hm) in EQ1; auto.
        apply check_annot_reduce; auto.
        inv HCL. inv H2;auto.
        inv HCL. inv H2;auto.
        apply wf_pset_union; auto.
    - destruct (find_lit (watch2 wc) u) eqn:EQ2.
      + destruct (Annot.elt t0)eqn:EQ.
      *  apply check_annot_TRUE.
      * apply check_annot_find_lit with (hm:=hm) in EQ2; auto.
        apply check_annot_reduce; auto.
        inv HCL. inv H2;auto.
        inv HCL. inv H2;auto.
        apply wf_pset_union; auto.
      + constructor ; auto.
  Qed.


  Lemma wf_insert_clause :
        forall i cl st
               (HCL : check_annot has_clause (hconsmap st) cl)
               (WF  : wf_state  st),
          wf_result_state (insert_clause i cl st).
  Proof.
    unfold insert_clause.
    unfold Annot.lift.
    intros.
    destruct (Annot.elt cl) eqn:EQ; simpl.
    - destruct HCL; auto.
    - tauto.
    - intros; apply wf_insert_unit; auto.
      eapply check_annot_set_UNIT;eauto.
    - unfold insert_watched_clause.
      apply wf_insert_normalised_clause; auto.
      apply check_annot_shorten_clause; auto.
      destruct WF ; auto. eapply check_annot_set_CLAUSE; eauto.
      eapply check_annot_set_CLAUSE; eauto.
  Qed.


  Lemma eval_insert_clause :
        forall i cl st
               (HCL : check_annot has_clause (hconsmap st) cl)
               (WF  : wf_state  st)
               (ES : eval_state  st)
               (EC : Annot.lift eval_clause cl),
          eval_result_state (insert_clause i cl st).
  Proof.
    unfold insert_clause.
    unfold Annot.lift;intros.
    destruct (Annot.elt cl) eqn:E ; simpl.
    - tauto.
    - tauto.
    - intros.
      apply eval_insert_unit; auto.
    - unfold insert_watched_clause.
      assert (HAS:
                has_watched_clause (hconsmap st) (Annot.elt (Annot.set cl wc))).
      { destruct HCL.
          unfold Annot.lift in wf_elt0.
          rewrite E in wf_elt0.
          auto.
      }
      apply eval_insert_normalised_clause; auto.
      { apply wf_shorten_clause; auto.
        - destruct WF ; auto.
        - destruct HCL;auto.
      }
      apply shorten_clause_correct with (m:=hconsmap st); auto.
      destruct ES ;auto.
  Qed.


  Lemma eval_annot_shorten_clause :
    forall m u cl an
           (WF : wf_units_lit u m)
           (WFA: wf_pset m an)
           (EV : eval_annot_units u m)
           (WFC : has_watched_clause m cl)
           (EC :  eval_pset m an -> eval_watched_clause cl),
      eval_annot eval_clause m (shorten_clause u an cl).
  Proof.
    unfold shorten_clause;intros.
    assert (HW1 : has_literal m (watch1 cl)).
    { inv WFC. auto. }
    assert (HW2 : has_literal m (watch2 cl)).
    { inv WFC. inv H2; auto. }
    assert (HUW : Forall (has_literal m) (unwatched cl)).
    { inv WFC. inv H2; auto. }
    destruct (find_lit (watch1 cl) u) eqn:FD1.
    - assert (FD1' := FD1).
      apply eval_annot_units_find_lit with (m:=m) in FD1; auto.
      apply check_annot_find_lit with (hm:=m) in FD1'; auto.
      unfold Annot.map in FD1.
      destruct (Annot.elt t0) ; simpl in * ; auto.
      + apply eval_annot_TRUE.
      + apply eval_annot_reduce with (m:=m); auto.
        apply wf_pset_union; auto.
        intro U. destruct FD1'; destruct WFA.
        apply eval_pset_union in U as (U1 & U2);auto.
        specialize (EC U2).
        apply eval_neg_literal_rec in EC; auto.
    - destruct (find_lit (watch2 cl) u) eqn:FD2; simpl; auto.
      assert (FD2' := FD2).
      apply eval_annot_units_find_lit with (m:=m) in FD2; auto.
      apply check_annot_find_lit with (hm:=m) in FD2'; auto.
      unfold Annot.map in FD2.
      destruct (Annot.elt t0) ; simpl ; auto.
      apply eval_annot_TRUE.
      apply  eval_annot_reduce with (m:=m); auto.
      apply wf_pset_union; auto.
      intro U. destruct FD2'; destruct WFA.
      apply eval_pset_union in U as (U1 & U2);auto.
      specialize (EC U2).
      apply eval_literal_rec_swap in EC; auto.
  Qed.

  Lemma eval_annot_insert_clause :
        forall i cl st
               (HCL : check_annot has_clause (hconsmap st) cl)
               (WF  : wf_state  st)
               (ES : eval_annot_state  st)
               (CA : check_annot has_clause (hconsmap st) cl)
               (EC : eval_annot eval_clause  (hconsmap st) cl),
          eval_annot_result_state (insert_clause i cl st).
  Proof.
    unfold insert_clause.
    unfold eval_annot in *.
    unfold Annot.lift;intros.
    destruct (Annot.elt cl) eqn:E ; simpl.
    - tauto.
    - tauto.
    - intros.
      apply eval_annot_insert_unit; auto.
    - unfold insert_watched_clause.
      assert (HAS:
                has_watched_clause (hconsmap st) (Annot.elt (Annot.set cl wc))).
      { destruct HCL.
          unfold Annot.lift in wf_elt0.
          rewrite E in wf_elt0.
          auto.
      }
      apply eval_annot_insert_normalised_clause; auto.
      { apply wf_shorten_clause; auto.
        - destruct WF ; auto.
        - destruct HCL;auto.
      }
      apply eval_annot_shorten_clause with (m:=hconsmap st); auto.
      destruct ES ;auto.
      destruct WF;auto.
      unfold Annot.deps,Annot.set;simpl.
      destruct CA ; auto.
      destruct ES;auto.
  Qed.

  Lemma wf_get_fresh_clause_id : forall st,
      wf_state st ->
      wf_state (snd (get_fresh_clause_id st)).
  Proof.
    intros. destruct H ; constructor ; simpl;auto.
  Qed.

  Lemma eval_get_fresh_clause : forall st,
      eval_state st ->
      eval_state (snd (get_fresh_clause_id st)).
  Proof.
    intros. destruct H ; constructor ; simpl;auto.
  Qed.

Lemma eval_annot_get_fresh_clause : forall st,
      eval_annot_state st ->
      eval_annot_state (snd (get_fresh_clause_id st)).
  Proof.
    intros. destruct H ; constructor ; simpl;auto.
  Qed.

  Lemma hconsmap_get_fresh_clause_id :
    forall st,
      (hconsmap (snd (get_fresh_clause_id st)) = hconsmap st).
  Proof.
    reflexivity.
  Qed.


  
  Lemma wf_insert_fresh_clause :
  forall (cl : Annot.t clause_kind) (st : state)
         (WFCL : check_annot  has_clause (hconsmap st) cl)
         (WFST : wf_state st),
  wf_result_state (insert_fresh_clause cl st).
  Proof.
    unfold insert_fresh_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    - change s with (snd (i,s)).
      rewrite <- EQ.
      apply wf_insert_clause ; auto.
      apply wf_get_fresh_clause_id ; auto.
  Qed.


  Lemma eval_insert_fresh_clause :
  forall (cl : Annot.t clause_kind) (st : state)
         (WFCL : check_annot has_clause (hconsmap st) cl)
         (WFST : wf_state st)
         (EC   : Annot.lift eval_clause cl)
         (ES   : eval_state st),
  eval_result_state (insert_fresh_clause cl st).
  Proof.
    unfold insert_fresh_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    change s with (snd (i,s)).
    rewrite <- EQ.
    apply eval_insert_clause ; auto.
    apply wf_get_fresh_clause_id ; auto.
    apply eval_get_fresh_clause;auto.
  Qed.

  Lemma eval_annot_insert_fresh_clause :
  forall (cl : Annot.t clause_kind) (st : state)
         (WFCL : check_annot has_clause (hconsmap st) cl)
         (WFST : wf_state st)
         (EC   : eval_annot eval_clause (hconsmap st) cl)
         (ES   : eval_annot_state st),
  eval_annot_result_state (insert_fresh_clause cl st).
  Proof.
    unfold insert_fresh_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    change s with (snd (i,s)).
    rewrite <- EQ.
    apply eval_annot_insert_clause ; auto.
    apply wf_get_fresh_clause_id ; auto.
    apply eval_annot_get_fresh_clause;auto.
  Qed.

  Definition ohold2 {A B:Type} (P : A -> B -> Prop) (o: option A) (b:B) :=
    match o with
    | None => True
    | Some a => P a b
    end.

  Lemma fold_left_None_None :
    forall [A B: Type]
           (F : option A -> B -> option A)
           (FN : forall a, F None a = None),
      forall l,
        fold_left F l None = None.
  Proof.
    induction l; simpl ; auto.
    rewrite FN. auto.
  Qed.

  Lemma IntMapForall_Forall :
    forall {A: Type} (P Q: A -> Prop) m,
      (forall x, P x -> Q x) ->
      IntMapForall P m ->
      IntMapForall Q m.
  Proof.
    repeat intro.
    apply H0 in H1.
    auto.
  Qed.

  Lemma fold_lemma :
    forall {A E: Type} (UP: A -> int -> E -> A) (P: A -> E -> Prop) Q m acc
           (WFm  : wf_map m)
           (Pacc : IntMapForall (P acc) m)
           (PUP  : forall acc i e e',
               P acc e ->
               P acc e' ->
               Q acc   ->
               P (UP acc i e) e')
           (UPOK : forall acc a,
               Q acc ->
               IntMapForall (P acc) m ->
               P acc (snd a) ->
               Q (UP acc (fst a) (snd a)))
           (Qacc : Q acc)
    ,
           Q (IntMap.fold' UP m acc).
Proof.
  intros.
  rewrite PTrie.fold_elements'.
  assert (ALL : forall x, In x (IntMap.elements' m  nil) -> P acc (snd x)).
  {
    intros.
    unfold IntMapForall in Pacc.
    apply Pacc with (k:=fst x).
    destruct x.
    apply IntMap.in_elements' with (opt:= None) in H; auto.
    simpl in *. tauto.
  }
  revert acc Qacc Pacc ALL.
  induction ((IntMap.elements' m nil)).
  - simpl.
    auto.
  - simpl; intros.
    assert (ALLA := ALL _  (or_introl eq_refl)).
    apply IHl; auto.
    revert Pacc.
    repeat intro.
    apply Pacc in H.
    eapply PUP; eauto.
Qed.

Lemma fold_up : forall {A: Type} (P: hmap -> A -> Prop) (Q:  dresult -> Prop)
                         (WPI : forall m m', hmap_order m m' -> forall x,
                               P  m x -> P  m' x)
                         (UP : int -> A -> dresult -> dresult)
                         (QOUT : forall f, Q (Fail f) -> False)
                         (UPSuccess : forall i x d, UP  i x (Success d) = Success d)
                         (UPOK :  forall i  cl st ,
                             Q (Progress st) ->  P (hconsmap st) cl  ->
                             hconsmap_progress_r (UP  i cl) (Progress st) /\
                             Q (UP  i cl (Progress st)))
                         (cl: IntMap.ptrie A)
    (st: state)
    (WF: wf_map cl)
    (CL : IntMapForall (P (hconsmap st)) cl)
    (ES : Q (Progress st)),
      Q (IntMap.fold' (fun acc k el => UP k el acc) cl (Progress st)).
Proof.
  intros.
  set (P':= fun (o:dresult) cl => match o with Progress st => P (hconsmap st) cl | Success (h,_) => P h cl | _ => True end).
  apply fold_lemma with (P0:= P'); eauto.
  unfold P'. intros.
  destruct acc ; auto.
  - apply QOUT in H1. tauto.
  - destruct r. rewrite UPSuccess. auto.
  - clear P'.
    specialize (UPOK i _ _ H1 H).
    unfold hconsmap_progress_r in UPOK.
    destruct (UP  i e (Progress st0)) eqn:EQ; simpl in * ; auto.
    + destruct r.
      intuition congruence.
    +
      intuition congruence.
  - intros.
    destruct acc.
    apply QOUT in H. tauto.
    rewrite UPSuccess. auto.
    apply UPOK; auto.
Qed.



Lemma fold_slemma :
    forall {A E: Type} (UP: A -> int -> E -> A) (P: E -> Prop) Q m acc
           (UPOK : forall acc i v,
               Q acc ->
               P v -> 
               Q (UP acc i v))
           (WFm  : wf_map m)
           (Pacc : IntMapForall P m)
           (Qacc : Q acc)
    ,
           Q (IntMap.fold' UP m acc).
Proof.
  intros.
  rewrite PTrie.fold_elements'.
  assert (ALL : forall x, In x (IntMap.elements' m  nil) -> P  (snd x)).
  {
    intros.
    unfold IntMapForall in Pacc.
    apply Pacc with (k:=fst x).
    destruct x.
    apply IntMap.in_elements' with (opt:= None) in H; auto.
    simpl in *. tauto.
  }
  revert acc Qacc Pacc ALL.
  induction ((IntMap.elements' m nil)).
  - simpl.
    auto.
  - simpl; intros.
    assert (ALLA := ALL _  (or_introl eq_refl)).
    apply IHl; auto.
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

Lemma ForallWatchedClause_remove_watched_id :
  forall (P : Annot.t watched_clause -> Prop) l i cls
         (WFM: wf_map cls)
         (WF: wf_watch_map cls)
         (ALL : ForallWatchedClause P cls),
    ForallWatchedClause P (remove_watched_id l i cls).
Proof.
  unfold remove_watched_id.
  intros.
  destruct (find_clauses (id_of_literal l) cls) eqn: FID.
  assert (FID':= FID).
  apply ForallWatchedClause_find_clauses with (P:=P) in FID.
  apply wf_find_clauses2 in FID'; auto.
  destruct FID, FID'.
  destruct (is_positive_literal l).
  apply IntMapForallAdd; auto.
  split ; simpl ; auto.
  apply IntMapForallRemove;auto.
  apply IntMapForallAdd; auto.
  split ; simpl ; auto.
  apply IntMapForallRemove;auto.
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
  forall i cl s
         (WF : wf_state  s)
         (HAS : has_watched_clause (hconsmap s) cl),
  wf_state  (remove_watched_clause i cl s).
Proof.
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

Definition hconsmap_eq  (F: state ->state)  :=
  forall st, hconsmap (F st) = hconsmap st.

Lemma hconsmap_remove_watched_clause : forall i cl,
    hconsmap_eq (remove_watched_clause i cl).
Proof.
  unfold remove_watched_clause.
  unfold hconsmap_eq.
  simpl; reflexivity.
Qed.






Lemma wf_update_watched_clause : forall i cl st
    (WF: wf_result_state  st)
    (WFA : Annot.lift_deps (wf_pset (hconsmap_result st)) cl)
    (HAS : Annot.lift (has_watched_clause (hconsmap_result st)) cl),
    wf_result_state (update_watched_clause  i cl st ).
Proof.
  intros.
  destruct st ; simpl in * ; auto.
  unfold insert_watched_clause.
  apply wf_insert_normalised_clause; auto.
  - apply check_annot_shorten_clause.
    + unfold remove_watched_clause; simpl.
      destruct WF ; auto.
    + unfold remove_watched_clause ; simpl.
      auto.
    + rewrite hconsmap_remove_watched_clause.
      auto.
  -  apply wf_remove_watched_clause;auto.
Qed.

Lemma hmap_order_refl : forall m,
    hmap_order m m.
Proof.
  repeat intro; auto.
Qed.

Hint Resolve hmap_order_refl : wf.

Lemma insert_normalised_clause_mono : forall i cl st,
    hconsmap_progress (insert_normalised_clause i cl) st.
Proof.
  unfold insert_normalised_clause.
  repeat intro.
  destruct (Annot.elt cl) ; simpl ; auto with wf.
Qed.

Lemma hconsmap_insert_normalised_clause : forall i cl st,
    hconsmap_progress (insert_normalised_clause i cl) st.
Proof.
  unfold insert_normalised_clause.
  unfold hconsmap_progress.
  intros.
  destruct (Annot.elt cl) ; simpl ; auto with wf.
Qed.


Lemma hconsmap_insert_watched_clause :
  forall i cl st, hconsmap_progress  (insert_watched_clause i cl) st.
Proof.
  unfold insert_watched_clause; intros.
  unfold hconsmap_progress. intros.
  eapply hconsmap_insert_normalised_clause;auto.
Qed.


  Definition map_dresult  (F : state -> dresult)  (d : dresult) :=
    match d with
    | Fail f => Fail f
    | Success p => Success p
    | Progress st => F st
    end.


  Lemma hconsmap_map_dresult : forall F,
      (forall st, hconsmap_progress F st) ->
      (forall st, hconsmap_progress_r (map_dresult F) st).
  Proof.
    unfold hconsmap_progress_r.
    intros.
    destruct st ; simpl in *; auto.
    apply H ; auto.
  Qed.

    Lemma hconsmap_comp : forall  (F: state -> dresult) (G : state -> state),
      (hconsmap_eq G) ->
      (forall st, hconsmap_progress F st) ->
      (forall st, hconsmap_progress (fun st => F (G st)) st).
  Proof.
    unfold hconsmap_progress.
    intros.
    rewrite <- H.
    apply H0; auto.
  Qed.

  Lemma hconsmap_update_watched_clause : forall i cl st,
      hconsmap_progress_r (update_watched_clause i cl) st.
  Proof.
    intros.
    unfold update_watched_clause.
    apply hconsmap_map_dresult.
    apply hconsmap_comp;auto.
    apply hconsmap_remove_watched_clause;auto.
    apply hconsmap_insert_watched_clause;auto.
  Qed.


  Lemma isMono_lift : forall {A:Type} (F : hmap -> A -> Prop),
      isMono F ->
      isMono (fun hm : hmap => Annot.lift (F hm)).
  Proof.
    unfold isMono ; intros.
    eapply H ; eauto.
  Qed.


Lemma wf_shorten_clauses :
  forall l st
         (WFM: wf_map l)
         (ALL: IntMapForall (check_annot has_watched_clause (hconsmap st)) l)
         (WF: wf_state st),
        wf_result_state (shorten_clauses l st).
Proof.
  unfold shorten_clauses.
  intros.
  change (wf_result_state (Progress st)) in WF.
  revert WF.
  revert ALL.
  apply fold_up; auto.
  - intros.
    revert H0.
    eapply check_annot_mono;eauto.
    apply isMono_lift.
    apply has_watched_clause_mono.
  - intros.
    split.
    apply hconsmap_update_watched_clause.
    apply wf_update_watched_clause; auto.
    destruct H0 ; auto.
    destruct H0; auto.
Qed.

Lemma hconsmap_extract_unit :
  forall l st st'
         (EQ : extract_unit st = Some (l, st')),
    (hconsmap st) = (hconsmap st').
Proof.
  unfold extract_unit; intros.
  destruct (unit_stack st) eqn:EQ1; try congruence ; auto.
  inv EQ. destruct st ; simpl ; auto.
Qed.

Lemma hmap_order_trans : forall m1 m2 m3,
    hmap_order m1 m2 ->
    hmap_order m2 m3 -> hmap_order m1 m3.
Proof.
  unfold hmap_order.
  repeat intro.
  apply H in H1.
  apply H0 in H1.
  auto.
Qed.

Lemma hconsmap_fold  :
  forall {A: Type} (F: int -> A -> dresult -> dresult) cl st
         (FOK : forall i k st, hconsmap_progress_r (F i k) st)
         (NOTFAIL : forall i k st, ~ is_fail st -> ~ is_fail (F i k st))
  ,

    hconsmap_progress (fun  (st : state) =>
                         IntMap.fold'
                           (fun (acc : dresult) (i : int) (k : A) =>
                              F i k acc) cl (Progress st)) st.
Proof.
  unfold hconsmap_progress.
  intros.
  assert (ACC: ~ is_fail ((Progress st):dresult) /\ hconsmap_result (Progress st : dresult) = (hconsmap st)).
  { simpl. tauto. }
  rewrite PTrie.fold_elements' in *.
  revert H ACC.
  generalize (Progress st : dresult).
  induction (PTrie.elements' cl nil).
  - simpl.  tauto.
  - simpl in *; intros.
    eapply IHl ; eauto.
    specialize (FOK (fst a) (snd a) d).
    unfold hconsmap_progress_r in *.
    destruct ACC as (ACC1 & ACC2).
    apply (NOTFAIL (fst a) (snd a))  in ACC1; eauto.
    split ; auto.
    rewrite <- ACC2.
    apply FOK;auto.
Qed.

Lemma not_fail_insert_normalised_clause : forall i k st,
  ~
  is_fail
    (insert_normalised_clause i k st).
Proof.
  unfold insert_normalised_clause.
  intros. destruct (Annot.elt k); simpl ; congruence.
Qed.

Lemma not_fail_insert_watched_clause : forall i k st,
    ~ is_fail (insert_watched_clause i k st).
Proof.
  unfold insert_watched_clause.
  intros.
  apply not_fail_insert_normalised_clause.
Qed.


Lemma hconsmap_shorten_clauses : forall l st,
    hconsmap_progress  (shorten_clauses l) st.
Proof.
  unfold shorten_clauses.
  intros.
  apply hconsmap_fold.
  - intros. apply hconsmap_update_watched_clause.
  - destruct st0 ; simpl  in *; try tauto.
    intros.
    apply not_fail_insert_watched_clause.
Qed.


Lemma hconsmap_insert_literal : forall  l st,
    hconsmap (insert_literal l st) =  hconsmap st.
Proof.
  destruct st ; simpl.
  reflexivity.
Qed.

Lemma hconsmap_unit_propagation : forall n g st,
    hconsmap_progress (unit_propagation n g) st.
Proof.
  repeat intro.
  revert st H.
  induction n.
  - simpl.
    repeat intro.
    tauto.
  - intros.
    rewrite unit_propagation_rew in H.
    rewrite unit_propagation_rew.
    destruct (extract_unit st) eqn:EQ.
    +  destruct p.
       apply hconsmap_extract_unit in EQ.
       destruct (success g (units s) t0).
       * simpl.
         congruence.
       * generalize (hconsmap_insert_literal t0 s).
         set (sti :=  (insert_literal t0 s)) in * ; clearbody sti.
         simpl in *.
         intros.
         destruct (find_clauses (id_of_literal (Annot.elt t0)) (clauses sti)) as (ln & lp).
         generalize (hconsmap_shorten_clauses match Annot.elt t0 with
                      | POS _ => ln
                      | NEG _ => lp
                                              end sti).
         unfold hconsmap_progress.
         set (sts :=       shorten_clauses match Annot.elt t0 with
                      | POS _ => ln
                      | NEG _ => lp
                      end sti
             ) in *.
         clearbody sts.
         destruct sts ; simpl in *  ; intuition try congruence.
         rewrite IHn;auto.
         congruence.
    +  reflexivity.
Qed.

  Definition wf_result_state'  (st: dresult) :=
    match st with
    | Progress st => wf_state  st
    | Success (hm,d)   => wf_pset hm d
    | Fail _   => True
    end.

  Lemma wf_unsat : forall m l u d
      (AN : wf_pset m (Annot.deps l))
      (WFU : wf_units_lit u m)
      (US : is_unsat u l = Some d),
  wf_pset m d.
  Proof.
    unfold is_unsat in *.
    intros.
    destruct (Annot.elt l).
    destruct (is_hFF f). inv US. auto.
    destruct (IntMap.get' (id f) u) eqn:EQ; try congruence.
    apply WFU in EQ.
    destruct (Annot.lift negb t0); try congruence.
    inv US.
    apply wf_pset_union;auto.
    tauto.
    destruct (IntMap.get' (id f) u) eqn:EQ; try congruence.
    apply WFU in EQ.
    destruct (Annot.elt t0); try congruence.
    inv US.
    apply wf_pset_union;auto.
    tauto.
  Qed.

  Lemma wf_success :
    forall g m u l d
           (AN  : wf_pset m (Annot.deps l))
           (WFU : wf_units_lit u m),
      success g u l = Some d ->
      wf_pset m d.
  Proof.
    unfold success.
    destruct g.
    intros.
    destruct (is_goalb h (Annot.elt l)).
    - inv H. auto.
    - eapply wf_unsat in H; eauto.
    - intros.
      eapply wf_unsat in H; eauto.
  Qed.


Lemma wf_unit_propagation :
    forall n g st
           (WF  : wf_state st)
           (WFG : has_oform (hconsmap st) g),
      wf_result_state'  (unit_propagation n g st ).
  Proof.
    induction n.
    - simpl. tauto.
    - cbn. intros.
      destruct (extract_unit st) eqn:EQ ;[|auto with wf].
      destruct p as (l,st').
      assert (EQ':= EQ).
      apply wf_extract_unit in EQ; auto.
      apply hconsmap_extract_unit in EQ'.
      destruct EQ as (WFST' & WFA ).
      destruct (success g (units st') l) eqn:SUC.
      +
        simpl.
        eapply wf_success; eauto.
        destruct WFA ;auto.
        destruct WFST';auto.
      +
        destruct (find_clauses (id_of_literal (Annot.elt l)) (clauses st')) as (ln,lp) eqn:FD.
        set (L := match Annot.elt l with
                          | POS _ => ln
                          | NEG _ => lp
                          end) in *.
        assert (WFLL: IntMapForall (check_annot has_watched_clause (hconsmap st')) L /\ wf_map L).
        {
          apply wf_find_clauses with (m:=(hconsmap st')) in FD; auto.
          destruct FD as ((FD1 & FD2) & (WF1 & WF2)).
          destruct (Annot.elt l) ; tauto.
          destruct WFST' ; auto.
          destruct WFST' ; auto.
        }
        destruct WFLL as (WFL1 & WFL2).
        assert (WFS : wf_result_state  (shorten_clauses L (insert_literal l st'))).
        { apply wf_shorten_clauses ; auto.
          apply wf_insert_literal; auto.

        }
        assert (MONO := hconsmap_shorten_clauses L (insert_literal l st') ).
        unfold hconsmap_progress in MONO.
        destruct (shorten_clauses L  (insert_literal l st'))eqn:RES ; try tauto.
        simpl. auto.
        apply IHn;auto.
        {
          revert WFG.
          apply has_oform_mono.
          simpl in *.
          intuition congruence.
        }
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
    forall l i cls
           (WF: wf_map cls)
           (WFW: wf_watch_map cls)
           (EC : eval_clauses cls),
  eval_clauses
    (remove_watched_id l i cls).
  Proof.
    unfold eval_clauses.
    intros.
    apply ForallWatchedClause_remove_watched_id;auto.
  Qed.

  Lemma eval_annot_remove_watched_id :
    forall m l i cls
           (WF: wf_map cls)
           (WFW: wf_watch_map cls)
           (EC : eval_annot_clauses m cls),
  eval_annot_clauses m (remove_watched_id l i cls).
  Proof.
    unfold eval_annot_clauses.
    intros.
    apply ForallWatchedClause_remove_watched_id;auto.
  Qed.

  Lemma eval_remove_watched_clause :
    forall i cl st
           (ES: eval_state st)
           (WS: wf_state st)
           (EW : eval_watched_clause cl),
      eval_state (remove_watched_clause i cl st).
  Proof.
    unfold remove_watched_clause.
    intros. destruct ES ; destruct WS; constructor ; simpl ; auto.
    eapply eval_remove_watched_id;eauto.
    apply wf_map_remove_watched_id ; auto.
    apply wf_watch_map_remove_watched_id;auto.
    eapply eval_remove_watched_id;eauto.
  Qed.

  Lemma eval_annot_remove_watched_clause :
    forall i cl st
           (ES : eval_annot_state st)
           (WS : wf_state st),
      eval_annot_state (remove_watched_clause i cl st).
  Proof.
    unfold remove_watched_clause.
    intros. destruct ES ; destruct WS; constructor ; simpl ; auto.
    eapply eval_annot_remove_watched_id;eauto.
    apply wf_map_remove_watched_id ; auto.
    apply wf_watch_map_remove_watched_id;auto.
    eapply eval_annot_remove_watched_id;eauto.
  Qed.


  Lemma wf_insert_watched_clause :
    forall i cl st
           (WF: wf_state st)
           (WFA: check_annot has_watched_clause  (hconsmap st) cl),
           wf_result_state  (insert_watched_clause i cl st).
  Proof.
    unfold insert_watched_clause.
    intros.
    apply wf_insert_normalised_clause; auto.
    destruct WF. destruct WFA.
    apply wf_shorten_clause; auto.
  Qed.

  Lemma eval_insert_watched_clause :
    forall i cl st
           (WF : wf_state st)
           (WFC : Annot.lift (has_watched_clause (hconsmap st)) cl)
           (ES  : eval_state st)
           (EW  : Annot.lift eval_watched_clause cl)
    ,
      eval_result_state (insert_watched_clause i cl st).
  Proof.
    unfold insert_watched_clause.
    intros. unfold insert_normalised_clause.
    generalize (shorten_clause_correct
                  (hconsmap st) (units st) (Annot.elt cl) (Annot.deps cl) (ev_units st ES) WFC EW).
    destruct (shorten_clause (units st) (Annot.deps cl) (Annot.elt cl));simpl;auto.
    destruct elt0 ; simpl ; auto.
    unfold Annot.lift, Annot.set. simpl.
    intros.
    apply eval_insert_unit; auto.
    intros. apply eval_add_watched_clause; auto.
  Qed.


  Lemma eval_annot_insert_watched_clause :
    forall i cl st
           (WF : wf_state st)
           (WFC : check_annot  has_watched_clause (hconsmap st) cl)
           (ES  : eval_annot_state st)
           (EW  : eval_annot eval_watched_clause (hconsmap st) cl)
    ,
      eval_annot_result_state (insert_watched_clause i cl st).
  Proof.
    unfold insert_watched_clause.
    intros. unfold insert_normalised_clause.
    generalize (eval_annot_shorten_clause
                  (hconsmap st) (units st) (Annot.elt cl) (Annot.deps cl)
                  (wf_units st WF) (wf_deps _ _ _ WFC) (ev_an_units st ES)
                  (wf_elt _ _ _ WFC) EW
               ).
    destruct (shorten_clause (units st) (Annot.deps cl) (Annot.elt cl));simpl;auto.
    destruct elt0 ; simpl ; auto.
    -  intro.
       apply eval_annot_insert_unit; auto.
    -
      intros. apply eval_annot_add_watched_clause; auto.
  Qed.

  Lemma insert_normalised_clause_not_OutOfFuel : forall i cl st,
      ~is_fail (insert_normalised_clause i cl st).
  Proof.
    unfold insert_normalised_clause.
    intros. destruct (Annot.elt cl) ; simpl; try congruence.
  Qed.

  Lemma insert_watched_clause_not_OutOfFuel : forall i e st,
     ~ is_fail (insert_watched_clause i e st).
  Proof.
    unfold insert_watched_clause.
    intros ; eapply insert_normalised_clause_not_OutOfFuel ; eauto.
  Qed.

  Lemma units_remove_watched_clause : forall x y st,
      units (remove_watched_clause x y st) = units st.
  Proof.
    reflexivity.
  Qed.

  Lemma eval_shorten_clauses :
  forall l st
         (WFL: wf_map l)
         (ALL1: IntMapForall (Annot.lift eval_watched_clause) l)
         (ALL2: IntMapForall (check_annot has_watched_clause (hconsmap st)) l)
         (WF: wf_state st /\ eval_state  st),
    wf_result_state  (shorten_clauses l st) /\ eval_result_state  (shorten_clauses l st).
Proof.
  unfold shorten_clauses.
  intros.
  set (Q := fun x =>   wf_result_state x /\
                       eval_result_state x).
  change (Q (IntMap.fold' (fun (acc : dresult) (i : int) (k : Annot.t watched_clause) =>
        update_watched_clause i k acc) l (Progress st))).
  eapply fold_lemma
    with (P:= fun (o: dresult) cl =>
                match o with
                  Success _ => True
                | Fail _ => False
                | Progress st => Annot.lift eval_watched_clause  cl /\ check_annot  has_watched_clause (hconsmap st) cl end);auto.
  - apply IntMapForallAnd;auto.
  - destruct acc ; simpl ; auto.
    intros.
    destruct_in_goal EQ; auto.
    + eapply insert_watched_clause_not_OutOfFuel.
      rewrite EQ. simpl. auto.
    +  assert (OM : (hconsmap st1) =  (hconsmap st0)).
       {
         change (hconsmap_result (Progress st1) = hconsmap st0).
         rewrite <- EQ.
         eapply hconsmap_comp.
         apply hconsmap_remove_watched_clause.
         apply hconsmap_insert_watched_clause; auto.
         apply not_fail_insert_watched_clause.
       }
       intuition.
       * revert H6.
         apply check_annot_mono;auto.
         apply isMono_lift. apply has_watched_clause_mono.
         congruence.
  - destruct acc ; simpl ; auto.
    intros. destruct H. destruct H1 as (WFA & WFE & WFH).
    generalize (wf_remove_watched_clause (fst a) (Annot.elt (snd a)) st0 H WFH).
    intro.
    split.
    apply wf_insert_normalised_clause;auto.
    { rewrite hconsmap_remove_watched_clause.
      rewrite units_remove_watched_clause.
      apply wf_shorten_clause; auto.
      simpl in H. destruct H ; auto.
    }
    apply eval_insert_watched_clause; auto.
    apply eval_remove_watched_clause;auto.
Qed.


  Lemma eval_annot_shorten_clauses :
  forall l st
         (WFL: wf_map l)
         (ALL1: IntMapForall (eval_annot  eval_watched_clause (hconsmap st)) l)
         (ALL2: IntMapForall (check_annot has_watched_clause (hconsmap st)) l)
         (WF: wf_state st /\ eval_annot_state  st),
    wf_result_state  (shorten_clauses l st) /\ eval_annot_result_state  (shorten_clauses l st).
Proof.
  unfold shorten_clauses.
  intros.
  set (Q := fun x =>   wf_result_state x /\
                       eval_annot_result_state x).
  change (Q (IntMap.fold' (fun (acc : dresult) (i : int) (k : Annot.t watched_clause) =>
        update_watched_clause i k acc) l (Progress st))).
  eapply fold_lemma
    with (P:= fun (o: dresult) cl =>
                match o with
                  Success _ => True
                | Fail _ => False
                | Progress st => eval_annot eval_watched_clause (hconsmap st) cl /\ check_annot  has_watched_clause (hconsmap st) cl end);auto.
  - apply IntMapForallAnd;auto.
  - destruct acc ; simpl ; auto.
    intros.
    destruct_in_goal EQ; auto.
    + eapply insert_watched_clause_not_OutOfFuel.
      rewrite EQ. simpl. auto.
    +  assert (OM : (hconsmap st1) =  (hconsmap st0)).
       {
         change (hconsmap_result (Progress st1) = hconsmap st0).
         rewrite <- EQ.
         eapply hconsmap_comp.
         apply hconsmap_remove_watched_clause.
         apply hconsmap_insert_watched_clause; auto.
         apply not_fail_insert_watched_clause.
       }
       destruct H as (EA & CA).
       destruct H0 as (EA' & CA').
       rewrite OM in *.
       tauto.
  - destruct acc ; simpl ; auto.
    intros. destruct H. destruct H1 as (WFA & WFE & WFH).
    generalize (wf_remove_watched_clause (fst a) (Annot.elt (snd a)) st0 H WFH).
    intro.
    split.
    apply wf_insert_normalised_clause;auto.
    { rewrite hconsmap_remove_watched_clause.
      rewrite units_remove_watched_clause.
      apply wf_shorten_clause; auto.
      simpl in H. destruct H ; auto.
    }
    apply eval_annot_insert_watched_clause; auto.
    { rewrite hconsmap_remove_watched_clause.
      split ; auto. }
    apply eval_annot_remove_watched_clause;auto.
Qed.


Lemma eval_find_clauses : forall i m ln lp,
    ForallWatchedClause (Annot.lift eval_watched_clause) m ->
    find_clauses i m = (ln,lp) ->
    IntMapForall (Annot.lift eval_watched_clause) ln /\
    IntMapForall (Annot.lift eval_watched_clause) lp.
Proof.
  intros.
  eapply ForallWatchedClause_find_clauses in H ; eauto.
Qed.




Lemma unit_propagation_correct :
  forall n g st
         (WF  : wf_state st)
         (WFG : has_oform (hconsmap st)  g)
           (EST  : eval_state st),
    match unit_propagation n  g st with
    | Success _ => True
    | Fail _ => False
    | Progress st' =>
      (eval_state st' -> eval_ohformula g)
    end ->  eval_ohformula g.
Proof.
  induction n.
  - simpl. tauto.
  - cbn. intros.
    destruct (extract_unit st) eqn:EQ ;[|auto].
    destruct p as (l,st').
    assert (EQ':= EQ).
    apply wf_extract_unit  in EQ.
    destruct EQ as (WFST' & WFA).
    assert (HM:= hconsmap_extract_unit _ _ _ EQ').
    apply extract_unit_eval_state in EQ'.
    destruct EQ' as (EL & EST').
      destruct (success g (units st') l) eqn:SUC.
      +
        destruct WFST', EST'.
        apply success_correct with (m:=hconsmap st')  in SUC; auto.
        eapply has_oform_mono;eauto. congruence.
        destruct WFA;auto.
      +
        destruct (find_clauses (id_of_literal (Annot.elt l)) (clauses st')) as (ln,lp) eqn:FD.
        set (L := match Annot.elt l with
                          | POS _ => ln
                          | NEG _ => lp
                          end) in *.
        assert (WFLL: IntMapForall (check_annot has_watched_clause (hconsmap st')) L /\  wf_map L).
        {
          apply wf_find_clauses with (m:= hconsmap st') in FD; auto.
          destruct FD as ((FD1 & FD2)& WF1 & WF2).
          destruct (Annot.elt l) ; tauto.
          destruct WFST';auto.
          destruct WFST';auto.
        }
        destruct WFLL as (WFL1 & WFL2).
        assert (EVALL : IntMapForall (Annot.lift eval_watched_clause) L).
        {
          apply eval_find_clauses
            in FD.
          destruct (Annot.elt l) ; unfold L ; simpl in *.
          tauto. tauto.
          destruct EST' ; auto.
        }
        assert (eval_result_state  (shorten_clauses L (insert_literal l st'))).
        { apply  eval_shorten_clauses; auto.
          split. apply wf_insert_literal; auto.
          apply eval_insert_literal ; auto.
        }
        assert (wf_result_state (shorten_clauses L (insert_literal l st'))).
        { apply wf_shorten_clauses;auto.
          apply wf_insert_literal;auto.
        }
        assert (hconsmap_progress (shorten_clauses L) (insert_literal l st')).
        {
          apply hconsmap_shorten_clauses.
        }
        unfold hconsmap_progress in *.
        destruct (shorten_clauses L (insert_literal l st'))
        eqn:RES ; try tauto.
        simpl in H0. tauto.
        simpl in H2.
        revert H.
        apply IHn; auto.
        eapply has_oform_mono; eauto.
        rewrite H2 in * by tauto. congruence.
      +  auto.
      +  auto.
  Qed.


Lemma eval_annot_find_clauses : forall m i wc ln lp,
    ForallWatchedClause (eval_annot eval_watched_clause m) wc ->
    find_clauses i wc = (ln,lp) ->
    IntMapForall (eval_annot eval_watched_clause m) ln /\
    IntMapForall (eval_annot eval_watched_clause m) lp.
Proof.
  intros.
  eapply ForallWatchedClause_find_clauses in H ; eauto.
Qed.

Lemma eval_annot_unit_propagation :
  forall n g st
         (WF  : wf_state st)
         (WFG : has_oform (hconsmap st)  g)
         (EST  : eval_annot_state st),
    match unit_propagation n  g st with
    | Success (hm,d) => eval_pset hm d -> eval_ohformula g
    | Fail _ => True
    | Progress st' => eval_annot_state st'
    end.
Proof.
  induction n.
  - simpl. tauto.
  - cbn. intros.
    destruct (extract_unit st) eqn:EQ ;[|auto].
    destruct p as (l,st').
    assert (EQ':= EQ).
    apply wf_extract_unit  in EQ.
    destruct EQ as (WFST' & WFA).
    assert (HM:= hconsmap_extract_unit _ _ _ EQ').
    apply eval_annot_extract_state in EQ'.
    destruct EQ' as (EL & EST').
    destruct (success g (units st') l) eqn:SUC.
    + intro.
      apply eval_annot_success with (m:=hconsmap st')  in SUC; auto.
      { eapply has_oform_mono;eauto. congruence. }
      { destruct WFST';auto. }
      { rewrite <- HM. tauto. }
      { destruct WFA; auto. }
      { destruct EST'; auto. }
    +
      destruct (find_clauses (id_of_literal (Annot.elt l)) (clauses st')) as (ln,lp) eqn:FD.
      set (L := match Annot.elt l with
                | POS _ => ln
                | NEG _ => lp
                end) in *.
      assert (WFLL: IntMapForall (check_annot has_watched_clause (hconsmap st')) L /\  wf_map L).
        {
          apply wf_find_clauses with (m:= hconsmap st') in FD; auto.
          destruct FD as ((FD1 & FD2)& WF1 & WF2).
          destruct (Annot.elt l) ; tauto.
          destruct WFST';auto.
          destruct WFST';auto.
        }
        destruct WFLL as (WFL1 & WFL2).
        assert (EVALL : IntMapForall (eval_annot eval_watched_clause (hconsmap st')) L).
        {
          apply eval_annot_find_clauses with (m:= hconsmap st') in FD; eauto.
          destruct (Annot.elt l) ; unfold L ; simpl in *.
          tauto. tauto.
          destruct EST' ; auto.
        }
        assert (eval_annot_result_state  (shorten_clauses L (insert_literal l st'))).
        { apply  eval_annot_shorten_clauses; auto.
          split. apply wf_insert_literal; auto.
          apply eval_annot_insert_literal ; auto.
          rewrite <- HM. auto.
        }
        assert (wf_result_state (shorten_clauses L (insert_literal l st'))).
        { apply wf_shorten_clauses;auto.
          apply wf_insert_literal;auto.
        }
        assert (hconsmap_progress (shorten_clauses L) (insert_literal l st')).
        {
          apply hconsmap_shorten_clauses.
        }
        unfold hconsmap_progress in *.
        destruct (shorten_clauses L (insert_literal l st'))
        eqn:RES ; try tauto.
      * destruct r ; simpl in *.
        tauto.
      * simpl in H0.
        simpl in H1.
        revert H.
        apply IHn; auto.
        eapply has_oform_mono; eauto.
        rewrite H1 in * by tauto. congruence.
      +  auto.
      +  auto.
  Qed.

  Lemma eval_insert_defs : forall m' a st,
      eval_state st ->
      eval_state (insert_defs m' a st).
  Proof.
    intros.
    destruct H.
    unfold insert_defs.
    constructor ; simpl ; auto.
  Qed.

  Lemma eval_annot_insert_defs : forall m' a st,
      eval_annot_state st ->
      eval_annot_state (insert_defs m' a st).
  Proof.
    intros.
    destruct H.
    unfold insert_defs.
    constructor ; simpl ; auto.
  Qed.


  Lemma wf_insert_fresh_watched_clause :
    forall cl st
           (ES : wf_state st)
           (HS : has_watched_clause (hconsmap st) cl),
           wf_result_state (insert_fresh_watched_clause cl st).
  Proof.
    unfold insert_fresh_watched_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    change s with (snd (i,s)).
    rewrite <- EQ.
    unfold insert_watched_clause.
    apply wf_insert_normalised_clause;auto.
    {
      destruct ES.
      apply check_annot_shorten_clause;auto.
      apply wf_pset_empty.
    }
    apply wf_get_fresh_clause_id;auto.
  Qed.

  Lemma eval_insert_fresh_watched_clause :
    forall cl st
           (WF : wf_state st)
           (ES : eval_state  st)
           (EC : eval_watched_clause  cl)
           (HS : has_watched_clause (hconsmap st) cl)
    ,
      eval_result_state (insert_fresh_watched_clause cl st).
  Proof.
    unfold insert_fresh_watched_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    change s with (snd (i,s)).
    rewrite <- EQ.
    unfold insert_watched_clause.
    apply eval_insert_normalised_clause;auto.
    apply wf_shorten_clause;auto.
    apply wf_get_fresh_clause_id;auto.
    apply wf_pset_empty.
    apply wf_get_fresh_clause_id;auto.
    apply eval_get_fresh_clause; auto.
    eapply shorten_clause_correct; eauto.
    apply eval_get_fresh_clause ;auto.
  Qed.

  Lemma eval_annot_insert_fresh_watched_clause :
    forall cl st
           (WF : wf_state st)
           (ES : eval_annot_state  st)
           (EC : eval_watched_clause  cl)
           (HS : has_watched_clause (hconsmap st) cl)
    ,
      eval_annot_result_state (insert_fresh_watched_clause cl st).
  Proof.
    unfold insert_fresh_watched_clause.
    intros.
    destruct (get_fresh_clause_id st) eqn:EQ.
    change s with (snd (i,s)).
    rewrite <- EQ.
    unfold insert_watched_clause.
    apply eval_annot_insert_normalised_clause;auto.
    apply wf_shorten_clause;auto.
    apply wf_get_fresh_clause_id;auto.
    apply wf_pset_empty.
    apply wf_get_fresh_clause_id;auto.
    apply eval_annot_get_fresh_clause; auto.
    eapply eval_annot_shorten_clause; eauto.
    destruct WF;auto.
    simpl. apply wf_pset_empty.
    apply eval_annot_get_fresh_clause ;auto.
  Qed.


  Lemma eval_fold_update_correct :
    forall m  concl F
           (FOK : forall st cl, has_watched_clause m cl ->
                                eval_watched_clause cl ->
                                wf_state st  ->eval_state  st ->
                                wf_result_state  (F cl st) /\
                                eval_result_state (F cl st))
           acc st
           (WF: Forall (has_watched_clause m) acc)
           (EC: Forall eval_watched_clause acc)
           (WS: wf_state  st)
           (ES: eval_state  st),
      (eval_result_state  (fold_update F acc st) -> eval_formula concl) ->
      eval_formula concl.
  Proof.
    induction acc; simpl.
    - tauto.
    - intros. inv WF. inv EC.
      specialize (FOK _ _ H2 H4 WS ES).
      destruct (F a st) ; simpl in *; try tauto.
      destruct FOK.
      eapply IHacc with (st:=st0); eauto.
  Qed.

  Lemma eval_annot_fold_update_correct :
    forall m  concl F
           (FOK : forall st cl, has_watched_clause m cl ->
                                eval_watched_clause cl ->
                                wf_state st  ->eval_annot_state  st ->
                                wf_result_state  (F cl st) /\
                                eval_annot_result_state (F cl st))
           acc st
           (WF: Forall (has_watched_clause m) acc)
           (EC: Forall eval_watched_clause acc)
           (WS: wf_state  st)
           (ES: eval_annot_state  st),
      (eval_annot_result_state  (fold_update F acc st) -> eval_formula concl) ->
      eval_formula concl.
  Proof.
    induction acc; simpl.
    - tauto.
    - intros. inv WF. inv EC.
      specialize (FOK _ _ H2 H4 WS ES).
      destruct (F a st) ; simpl in *; try tauto.
      destruct FOK.
      eapply IHacc with (st:=st0); eauto.
  Qed.

  Lemma Forall_eval_literal_POS : forall l,
      Forall eval_literal (List.map POS l) <-> Forall eval_hformula l.
  Proof.
    induction l.
    - simpl.
      rewrite ! Forall_rew.
      tauto.
    - simpl.
      rewrite Forall_rew.
      symmetry.
      rewrite Forall_rew.
      tauto.
  Qed.




  Lemma intro_impl_aux :
    forall m f hf acc l o
           (WF: has_form m hf)
           (EQ: hf.(elt) = f),
      intro_impl acc f hf = (l,o) ->
      (Forall eval_literal l -> eval_ohformula o) <->
      (Forall eval_literal acc -> eval_formula f).
  Proof.
    destruct f.
    - simpl; intros.
      inv H.
      simpl. tauto.
    - simpl; intros.
      destruct (is_dec hf)eqn:D.
      + inv H.
        rewrite Forall_rew. simpl.
        apply eval_formula_dec in WF ; auto.
        rewrite EQ in *.
        simpl in *.
        tauto.
      + inv H.
        simpl.
        unfold eval_hformula.
        rewrite EQ in *; simpl in *; tauto.
    - simpl.
      intros.
      destruct (is_dec hf)eqn:D.
      * assert (WF':= WF).
        apply eval_formula_dec in WF ; auto.
        rewrite EQ in WF ; simpl in WF.
        inv H.
        rewrite Forall_rew.
        simpl. rewrite EQ.
        simpl.
        tauto.
      * inv H.
        simpl. unfold eval_hformula. rewrite EQ.
        simpl. tauto.
    - intros.
      simpl in H.
      destruct (is_dec t0)eqn:D.
      + inv H.
        assert (HFr : has_form m t0).
        {
          inv WF; simpl in EQ ; try congruence; auto.
        }
        apply eval_formula_dec in HFr ; auto.
        rewrite Forall_rew.
        simpl.
        rewrite xmap_rev.
        rewrite Forall_app.
        rewrite map_rev.
        rewrite Forall_rev_iff.
        rewrite <- eval_impl_list_eq.
        rewrite eval_and_list_eq.
        rewrite eval_and_list'_Forall.
        rewrite Forall_eval_literal_POS.
        change ((fun f : t LForm => eval_formula (elt f))) with eval_hformula.
        tauto.
      + inv H.
        simpl.
        rewrite xmap_rev.
        rewrite Forall_app.
        rewrite map_rev.
        rewrite Forall_rev_iff.
        rewrite <- eval_impl_list_eq.
        rewrite eval_and_list_eq.
        rewrite eval_and_list'_Forall.
        rewrite Forall_eval_literal_POS.
        change ((fun f : t LForm => eval_formula (elt f))) with eval_hformula.
        tauto.
  Qed.

  Lemma intro_impl_correct :
    forall m f hf l o
           (WF: has_form m hf)
           (EQ: hf.(elt) = f),
      intro_impl nil f hf = (l,o) ->
      (Forall eval_literal l -> eval_ohformula o) <->
      eval_formula f.
  Proof.
    intros.
    apply intro_impl_aux with (m:=m) in H ; auto.
    rewrite (Forall_rew nil) in H.
    tauto.
  Qed.




  Definition eval_oT {A:Type} (P: A -> Prop) (s : option A) :=
    match s with
    | None => True
    | Some v => P v
    end.


  
Lemma cnf_correct_opt
     : forall m (f : LForm) (pol : bool) (g : option HFormula) (cp cm : IntMap.ptrie unit)
         (ar : list literal) (acc : list watched_clause) (hf : t LForm),
      has_form m hf ->
      elt hf = f ->
       ((Forall eval_watched_clause acc -> eval_ohformula g) -> eval_ohformula g) ->
       (Forall eval_watched_clause (snd (cnf pol (is_classic g) cp cm ar acc f hf)) ->
        eval_ohformula g) -> eval_ohformula g.
Proof.
  destruct pol.
  -  apply cnf_correct.
  - intros *.
    apply cnf_correct.
Qed.

Lemma cnf_of_literal_correct : forall (m: hmap) g cp cm ar l
                                      (WF:has_form m (form_of_literal l)),
    (Forall eval_watched_clause (snd (cnf_of_literal l (is_classic g) cp cm
                                                     ar nil (elt (form_of_literal l)) (form_of_literal l))) -> eval_ohformula g) ->
      eval_ohformula g.
  Proof.
    unfold cnf_of_literal.
    intros.
    apply cnf_correct_opt with (m:=m) in H ; auto.
  Qed.

  Lemma Forall_has_literal_POS : forall m l,
      Forall (has_literal m) (List.map POS l) <-> Forall (has_form m) l.
  Proof.
    induction l.
    - simpl. rewrite !Forall_rew.
      tauto.
    - simpl.
      rewrite Forall_rew.
      symmetry. rewrite Forall_rew.
      tauto.
  Qed.


  Lemma Forall_has_literal_NEG : forall m l,
      Forall (has_literal m) (List.map NEG l) <-> Forall (has_form m) l.
  Proof.
    induction l.
    - simpl. rewrite !Forall_rew.
      tauto.
    - simpl.
      rewrite Forall_rew.
      symmetry. rewrite Forall_rew.
      tauto.
  Qed.


  Lemma wf_intro_impl :
    forall m f acc hf l o
           (WF: has_form m hf)
           (ACC: Forall (has_literal m) acc)
           (EQ: hf.(elt) = f),
      intro_impl acc f hf = (l, o) ->
      Forall (has_literal m) l /\ has_oform m o.
  Proof.
    destruct f.
    - simpl in *.
      intros.
      inv H. simpl.
      tauto.
    - simpl in *.
      intros.
      destruct (is_dec hf); inv H; auto.
      simpl ; split ; auto.
    - simpl in *.
      intros.
      assert (HF: Forall (has_form m) l0).
      {
        destruct hf ; simpl in *.
        subst. inv WF ; auto.
      }
      destruct (is_dec hf) ; inv H; auto.
      rewrite Forall_rew.
      simpl. tauto.
    - simpl in *.
      intros.
      assert (HF: Forall (has_form m) l).
      {
        destruct hf ; simpl in *.
        subst. inv WF ; auto.
      }
      assert (HT:  (has_form m) t0).
      {
        destruct hf ; simpl in *.
        subst. inv WF ; auto.
      }
      rewrite !xmap_rev in H.
      rewrite! map_rev in H.
      destruct (is_dec t0) ; inv H; auto.
      + rewrite Forall_rew.
        rewrite Forall_app.
        rewrite Forall_rev_iff.
        simpl.
        rewrite Forall_has_literal_POS.
        tauto.
      +         rewrite Forall_app.
        rewrite Forall_rev_iff.
        simpl.
        rewrite Forall_has_literal_POS.
        tauto.
  Qed.


  Lemma wf_watch_clause_of_list :
    forall m l w
           (HF : Forall (has_literal m) l)
           (WC : watch_clause_of_list l = Some w),
  has_watched_clause m w.
  Proof.
    intros.
    unfold watch_clause_of_list in WC.
    destruct l; try congruence.
    destruct l0; try congruence.
    inv WC.
    unfold has_watched_clause.
    simpl. auto.
  Qed.



  Lemma wf_cnf_of_op_plus :
    forall m b o l hf acc
           (HF1: Forall (has_form m) l)
           (HF: has_form m hf)
           (HACC: Forall (has_watched_clause m) acc),
  Forall (has_watched_clause m) (cnf_of_op_plus b o l hf acc).
  Proof.
    unfold cnf_of_op_plus.
    intros.
    destruct o ; auto.
    - unfold cnf_plus_and.
      destruct_in_goal WC;[constructor|];auto.
      eapply wf_watch_clause_of_list in WC; eauto.
      rewrite xmap_rev.
      rewrite Forall_app.
      rewrite map_rev.
      rewrite Forall_rev_iff.
      split.
      apply Forall_has_literal_NEG; auto.
      constructor ; auto.
    - unfold cnf_plus_or.
      rewrite xmap_rev.
      rewrite Forall_app.
      rewrite map_rev.
      rewrite Forall_rev_iff.
      split; auto.
      rewrite Forall_forall.
      intros. rewrite in_map_iff in H.
      destruct H. destruct H. subst.
      unfold has_watched_clause.
      simpl. rewrite Forall_rew;auto.
      split;auto. rewrite Forall_forall in HF1.
      apply HF1; auto.
  Qed.

  Lemma wf_cnf_of_op_minus :
    forall m b o l hf acc
           (HF1: Forall (has_form m) l)
           (HF: has_form m hf)
           (HACC: Forall (has_watched_clause m) acc),
  Forall (has_watched_clause m) (cnf_of_op_minus b o l hf acc).
  Proof.
    unfold cnf_of_op_plus.
    intros.
    destruct o ; auto.
    - simpl. unfold cnf_minus_and.
      rewrite xmap_rev.
      rewrite Forall_app.
      rewrite map_rev.
      rewrite Forall_rev_iff.
      split ; auto.
      rewrite Forall_forall.
      intros. rewrite in_map_iff in H.
      destruct H. destruct H. subst.
      unfold has_watched_clause.
      simpl.
      repeat rewrite Forall_rew;auto.
      repeat split ; auto.
      rewrite Forall_forall in HF1.
      apply HF1;auto.
    - simpl. unfold cnf_minus_or.
      destruct l; simpl; auto.
      rewrite Forall_rew.
      split ; auto.
      unfold has_watched_clause.
      simpl.
      inv HF1.
      rewrite Forall_rew;split; auto.
      rewrite Forall_rew;split; auto.
      unfold rev_map.
      rewrite xmap_rev.
      rewrite <- app_nil_end.
      rewrite map_rev.
      rewrite Forall_rev_iff.
      apply Forall_has_literal_POS;auto.
  Qed.

  Lemma wf_cnf_plus_impl :
    forall m b  l r hf acc
           (HF1: Forall (has_form m) l)
           (HFr : has_form m r)
           (HF: has_form m hf)
           (HACC: Forall (has_watched_clause m) acc),
  Forall (has_watched_clause m) (cnf_plus_impl b l r hf acc).
  Proof.
    unfold cnf_plus_impl.
    intros.
    rewrite Forall_rew.
    split.
    - repeat constructor ; auto.
    -
      rewrite xmap_filter_rev.
      rewrite Forall_app. split; auto.
      rewrite map_rev.
      rewrite Forall_rev_iff.
      rewrite Forall_forall.
      intros. rewrite in_map_iff in H.
      destruct H. destruct H ; subst.
      rewrite filter_In in H0.
      destruct H0 as (H0 & _).
      unfold has_watched_clause.
      simpl.
      repeat rewrite Forall_rew; auto.
      repeat split ; auto.
      rewrite Forall_forall in HF1 ; apply HF1 ; auto.
  Qed.

  Lemma wf_unit_or : forall m r
      (HFr : has_form m r),
      Forall (has_literal m) (unit_or r).
  Proof.
    unfold unit_or.
    intros.
    destruct (elt r); constructor ; auto.
  Qed.


  Lemma wf_cnf_minus_impl :
    forall m l r hf acc
           (HF1: Forall (has_form m) l)
           (HFr : has_form m r)
           (HF: has_form m hf)
           (HACC: Forall (has_watched_clause m) acc),
  Forall (has_watched_clause m) (cnf_minus_impl l r hf acc).
  Proof.
    unfold cnf_minus_impl.
    intros.
    destruct_in_goal WC; auto.
    constructor ; auto.
    eapply wf_watch_clause_of_list in WC; eauto.
    rewrite xmap_rev.
    constructor ; auto.
    rewrite Forall_app;split ; auto.
    rewrite map_rev.
    rewrite Forall_rev_iff.
    rewrite Forall_forall.
    rewrite Forall_forall in HF1.
    intros. rewrite in_map_iff in H.
    destruct H. destruct H ; subst.
    apply HF1;auto.
    apply wf_unit_or; auto.
  Qed.


  Lemma wf_cnf_list : forall
      (m : hmap) l ar acc  b1 b2 cp cm m' ar' w
      (H : forall x : t LForm,
          In x l ->
          forall (b1 b2 : bool) (cp cm : IntMap.ptrie unit) (ar : list literal)
                 (acc : list watched_clause) (hf : HFormula)
                 (m' : IntMap.ptrie unit * IntMap.ptrie unit) (ar' : list literal)
                 (w : list watched_clause),
            Forall (has_literal m) ar ->
            Forall (has_watched_clause m) acc ->
            has_form m hf ->
            elt hf = elt x ->
            cnf b1 b2 cp cm ar acc (elt x) hf = (m', ar', w) ->
            Forall (has_literal m) ar' /\ Forall (has_watched_clause m) w)
      (HA : Forall (has_literal m) ar)
      (ACC : Forall (has_watched_clause m) acc)
      (HF : Forall (has_form m) l)
      (EQ : cnf_list cnf b1 b2 cp cm ar
                     acc l =
            (m', ar', w)),
      (Forall (has_literal m) ar' /\ Forall (has_watched_clause m) w).
  Proof.
    induction l; simpl.
    - intros.
      destruct b1; inv EQ.
      + split ; auto.
      + split ; auto.
    - intros.
      destruct (cnf b1 b2 cp cm ar acc (elt a) a) as (((cp',cm'),ar2),acc') eqn:EQ1.
      revert EQ.
      apply H in EQ1;auto.
      destruct EQ1.
      apply IHl; auto.
      intros x IN.
      apply H; tauto.
      inv HF; auto.
      inv HF; auto.
  Qed.

(*  Lemma wf_cnf_of_atom :
    forall m acc hf b
           (ACC : Forall (has_watched_clause m) acc)
           (HF : has_form m hf),
      Forall (has_watched_clause m) (cnf_of_atom b hf acc).
  Proof.
    unfold cnf_of_atom.
    intros.
    destruct (b && is_dec hf); auto.
    constructor; auto.
    unfold has_watched_clause. simpl.
    constructor ; auto.
  Qed.
*)
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
      + inv EQ. split ; auto.
(*        apply wf_cnf_of_atom; auto.*)
    - destruct (is_cons (id hf) (if b1 then cp else cm)).
      + inv EQ. split; auto.
      + revert EQ.
        assert (HFL : Forall (has_form m) l).
        {
          inv HF; try discriminate.
          simpl in *; auto. congruence.
        }
        apply wf_cnf_list; auto.
        destruct b1.
        apply wf_cnf_of_op_plus;auto.
        apply wf_cnf_of_op_minus;auto.
    - destruct (is_cons (id hf) (if b1 then cp else cm)).
      + inv EQ. split; auto.
      + destruct (cnf_list cnf (negb b1) b2 cp cm (if negb (lazy_or b2 (fun _ : unit => forallb is_dec l)) && b1 then POS hf :: ar else ar)
                           ((if b1 then cnf_plus_impl b2 else cnf_minus_impl) l r hf acc) l) as (((cp1,cm1),ar1),acc1) eqn:ACC1.
        revert EQ.
        assert (HF' : Forall (has_form m) l).
        {
          inv HF; try discriminate.
          simpl in HFF. congruence.
        }
        assert (HR : has_form m r).
        {
           inv HF; try discriminate.
           simpl in HFF. congruence.
        }
        apply wf_cnf_list with (m:=m) in ACC1;auto.
        apply IHf;auto.
        tauto. tauto.
        destruct (negb (lazy_or b2 (fun _ : unit => forallb is_dec l)) && b1); auto.
        destruct b1.
        apply wf_cnf_plus_impl;auto.
        apply wf_cnf_minus_impl;auto.
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


  Lemma wf_insert_defs : forall m' ar st,
      wf_state  st ->
      Forall (has_literal (hconsmap st)) ar ->
      wf_state  (insert_defs m' ar st).
  Proof.
    intros.
    destruct H ; constructor ; simpl ; auto.
  Qed.

  Lemma get_fresh_clause_id_mono : forall st,
      hconsmap (snd (get_fresh_clause_id st)) = hconsmap st.
  Proof.
    destruct st ; simpl.
    reflexivity.
  Qed.

  Lemma hconsmap_insert_fresh_watched_clause : forall a st,
      hconsmap_progress (insert_fresh_watched_clause a) st.
  Proof.
    unfold insert_fresh_watched_clause.
    repeat intro.
    simpl in *.
    rewrite hconsmap_insert_watched_clause; simpl ; auto.
  Qed.

  Lemma insert_fresh_watched_clause_not_OutOfFuel : forall a st,
      ~ is_fail (insert_fresh_watched_clause a st).
  Proof.
    unfold insert_fresh_watched_clause.
    intros.
    destruct_in_goal H.
    eapply insert_watched_clause_not_OutOfFuel.
  Qed.

  Lemma wf_augment_cnf :
    forall b l st
           (HL : has_literal (hconsmap st) l)
           (WF : wf_state st),
      wf_result_state  (augment_cnf b l st).
  Proof.
    unfold augment_cnf.
    intros.
    destruct (cnf_of_literal l b (fst (defs st)) (snd (defs st)) (arrows st) nil
        (elt (form_of_literal l)) (form_of_literal l)) as (((cp,cm),ar),acc) eqn:EQ.
    apply wf_cnf_of_literal with (m:=hconsmap st) in EQ; auto.
    {

      apply fold_update_correct with (Q:= fun st cl => has_watched_clause (hconsmap st) cl).
      - intros.
        revert H0.
        apply has_watched_clause_mono.
        generalize (hconsmap_insert_fresh_watched_clause  a st0).
        unfold hconsmap_progress.
        rewrite H. simpl.
        intuition congruence.
      - intros.
        apply wf_insert_fresh_watched_clause; auto.
      - destruct EQ.
        revert H0.
        apply Forall_Forall.
        intros.
        unfold insert_defs; simpl; auto.
      -
        apply wf_insert_defs;auto.
        tauto.
    }
    destruct WF; auto.
    apply has_form_of_literal; auto.
  Qed.

  Lemma check_annot_hyp : forall [m l]
      (HL: has_literal m l),
      check_annot has_literal m (annot_hyp l).
  Proof.
    unfold annot_hyp.
    intros.
    constructor ;auto.
    simpl.
    constructor.
    repeat constructor.
    intros.
    unfold LitSet.mem in H.
    simpl in H.
    exists (form_of_literal l).
    split ; auto.
    apply has_form_of_literal; auto.
    replace i with (id_of_literal l) by lia.
    reflexivity.
  Qed.


  Lemma wf_augment_hyp :
    forall b l st
           (HL: has_literal (hconsmap st) l)
           (WF: wf_state st),
      wf_result_state (augment_hyp b l st).
  Proof.
    unfold augment_hyp.
    intros.
    apply wf_augment_cnf; auto.
    apply wf_insert_unit ; auto.
    apply check_annot_hyp; auto.
  Qed.

  Lemma hconsmap_insert_unit : forall l,
      hconsmap_eq  (insert_unit l).
  Proof.
    repeat intro.
    destruct st ; simpl ; auto.
  Qed.

  Lemma insert_defs_mono : forall d ar s,
      (hconsmap s) = (hconsmap (insert_defs d ar s)).
  Proof.
    destruct s; simpl; auto.
  Qed.


  Lemma hconsmap_augment_cnf : forall b a st,
      hconsmap_progress (augment_cnf b a) st.
  Proof.
    unfold augment_cnf.
    repeat intro.
    destruct (cnf_of_literal a b (fst (defs st)) (snd (defs st)) (arrows st) nil
        (elt (form_of_literal a)) (form_of_literal a)) as (((cp,cm),ar),acc).
    assert (HM := insert_defs_mono (cp,cm) ar st).
    revert H HM.
    generalize (insert_defs (cp, cm) ar st) as st'.
    intros. rewrite HM.
    clear.
    revert st'.
    induction acc; simpl; auto.
    intros.
    generalize (hconsmap_insert_fresh_watched_clause a st').
    unfold hconsmap_progress.
    intro.
    specialize (H (insert_fresh_watched_clause_not_OutOfFuel a st')).
    destruct (insert_fresh_watched_clause a st'); simpl in *; auto.
    rewrite <- H.
    eapply IHacc;auto.
  Qed.

  Lemma hconsmap_augment_hyp : forall b a st,
      hconsmap_progress  (augment_hyp b a) st.
  Proof.
    unfold augment_hyp.
    intros.
    apply hconsmap_comp.
    apply hconsmap_insert_unit.
    intros.
    apply hconsmap_augment_cnf.
  Qed.

  Lemma augment_hyp_not_OutOfFuel :
    forall b a st,
      ~ is_fail (augment_hyp b a st).
  Proof.
    unfold augment_hyp.
    intros.
    unfold augment_cnf.
    destruct (      cnf_of_literal a b (fst (defs (insert_unit (annot_hyp a) st)))
        (snd (defs (insert_unit (annot_hyp a) st)))
        (arrows (insert_unit (annot_hyp a) st)) nil (elt (form_of_literal a))
        (form_of_literal a)).
    destruct p. destruct p.
    apply fold_update_not_OutOfFuel.
    apply insert_fresh_watched_clause_not_OutOfFuel.
  Qed.

  
  Lemma wf_cnf_hyps :
    forall b l st
           (HL: Forall (has_literal (hconsmap st)) l)
           (WF: wf_state  st),
      wf_result_state  (cnf_hyps b l st).
  Proof.
    unfold cnf_hyps.
    intros *. intro.
    change (Forall ((fun s => (has_literal (hconsmap s))) st) l) in HL.
    revert HL.
    apply fold_update_correct.
    - intros.
      revert H0.
      apply has_literal_mono.
      generalize (hconsmap_augment_hyp b a st0).
      unfold hconsmap_progress. rewrite H.
      simpl. intuition congruence.
    - intros.
      apply wf_augment_hyp; auto.
  Qed.

  Lemma eval_augment_cnf :
    forall o l st
           (HL : has_literal (hconsmap st) l)
           (WF : wf_state st),
      (eval_result_state  (augment_cnf (is_classic o) l st) -> eval_ohformula o) ->
      (eval_state  st -> eval_ohformula o).
  Proof.
    intros.
    unfold augment_cnf in H.
    destruct (cnf_of_literal l (is_classic o) (fst (defs st))
            (snd (defs st)) (arrows st) nil (elt (form_of_literal l))
            (form_of_literal l)) as (((cp',cm'),ar'),acc') eqn:EQ .
    assert (EQ':= EQ).
    apply wf_cnf_of_literal with (m:=hconsmap st) in EQ' ; auto.

    change acc' with (snd (cp',cm',ar',acc')) in H.
    rewrite <- EQ in H.
    generalize (cnf_of_literal_correct (hconsmap st)  o (fst (defs st))
                                       (snd (defs st)) (arrows st) l
                                       ).
    rewrite EQ in *. clear EQ.
    simpl in *.
    intros W.
    apply W.
    apply has_form_of_literal; auto.
    intro A.
    apply H.
    apply eval_fold_update with (EVAL:=eval_watched_clause) (WP:=has_watched_clause); auto.
    {
      intros.
      eapply has_watched_clause_mono; eauto.
    }
    {
      rewrite Forall_forall.
      intros.
      split_and.
      apply hconsmap_insert_fresh_watched_clause.
      apply wf_insert_fresh_watched_clause; auto.
      apply eval_insert_fresh_watched_clause; auto.
      rewrite Forall_forall in * ; auto.
    }
    apply wf_insert_defs ; auto.
    tauto.
    apply eval_insert_defs ; auto.
    tauto.
    apply wf_arrows; auto.
    apply has_form_of_literal;auto.
  Qed.

  Lemma eval_annot_augment_cnf :
    forall o l st
           (HL : has_literal (hconsmap st) l)
           (WF : wf_state st),
      (eval_annot_result_state  (augment_cnf (is_classic o) l st) -> eval_ohformula o) ->
      (eval_annot_state  st -> eval_ohformula o).
  Proof.
    intros.
    unfold augment_cnf in H.
    destruct (cnf_of_literal l (is_classic o) (fst (defs st))
            (snd (defs st)) (arrows st) nil (elt (form_of_literal l))
            (form_of_literal l)) as (((cp',cm'),ar'),acc') eqn:EQ .
    assert (EQ':= EQ).
    apply wf_cnf_of_literal with (m:=hconsmap st) in EQ' ; auto.

    change acc' with (snd (cp',cm',ar',acc')) in H.
    rewrite <- EQ in H.
    generalize (cnf_of_literal_correct (hconsmap st) o (fst (defs st))
                                       (snd (defs st)) (arrows st) l
                                       ).
    rewrite EQ in *. clear EQ.
    simpl in *.
    intros.
    apply H1.
    apply has_form_of_literal;auto.
    intro.
    apply H.
    apply eval_annot_fold_update with (EVAL:=eval_watched_clause) (WP:=has_watched_clause); auto.
    {
      intros.
      eapply has_watched_clause_mono; eauto.
    }
    {
      rewrite Forall_forall.
      intros.
      split_and.
      apply hconsmap_insert_fresh_watched_clause.
      apply wf_insert_fresh_watched_clause; auto.
      apply eval_annot_insert_fresh_watched_clause; auto.
      rewrite Forall_forall in H2 ; auto.
    }
    apply wf_insert_defs ; auto.
    tauto.
    apply eval_annot_insert_defs ; auto.
    tauto.
    apply wf_arrows; auto.
    apply has_form_of_literal;auto.
  Qed.



  Lemma eval_augment_hyp :
    forall o l st
           (HL : has_literal (hconsmap st) l)
           (WF : wf_state  st),
      (eval_result_state  (augment_hyp (is_classic o) l st) -> eval_ohformula o) ->
      (eval_state  st -> eval_literal l -> eval_ohformula o).
  Proof.
    Proof.
      intros.
      apply eval_augment_cnf in H; auto.
      apply wf_insert_unit ; auto.
      apply check_annot_hyp; auto.
      apply eval_insert_unit;auto.
    Qed.

  Lemma eval_cnf_hyps : forall o l st
                               (HL: Forall (has_literal (hconsmap st)) l)
                               (WF: wf_state  st)
    ,
      (eval_result_state  (cnf_hyps (is_classic o) l st) -> eval_ohformula o) ->
       (eval_state  st -> Forall eval_literal l -> eval_ohformula o).
  Proof.
    unfold cnf_hyps.
    induction l ; simpl.
    - auto.
    - intros.
      inv H1. inv HL.
      specialize (eval_augment_hyp  o a st H3 WF).
      assert (WFA: wf_result_state  (augment_hyp (is_classic o) a st)).
      { apply wf_augment_hyp ; auto.  }
      generalize (hconsmap_augment_hyp  (is_classic o) a st).
      unfold hconsmap_progress.
      destruct (augment_hyp (is_classic o) a st).
      +  simpl in *. tauto.
      + simpl. tauto.
      +
        simpl in *.
      intros.
      assert (HL : Forall (has_literal (hconsmap st0)) l).
      { revert H6.
        apply Forall_Forall.
        apply has_literal_mono; auto.
        intuition congruence.
      }
      specialize (IHl st0 HL).
      tauto.
  Qed.


  Lemma eval_pset_singleton :
    forall m f b
      (HF : has_form m f),
      eval_pset m (LitSet.singleton (id f) b) -> eval_literal (literal_of_bool b f).
  Proof.
    intros.
    apply H; auto.
    unfold LitSet.get, LitSet.singleton.
    simpl. rewrite eqb_refl.
    unfold OBool.lift_has_bool.
    simpl. apply Bool.eqb_reflx.
  Qed.

  Lemma eval_annot_hyp :
    forall m l
           (HL: has_literal m l),
      eval_annot eval_literal m (annot_hyp l).
  Proof.
    unfold annot_hyp.
    unfold eval_annot, annot_of_literal.
    simpl.
    intros.
    apply eval_pset_singleton in H.
    rewrite <- literal_eq; auto.
    apply has_form_of_literal; auto.
  Qed.

  Definition annot_lit (f : HFormula) := annot_hyp (POS f).

  Lemma eval_annot_lit :
    forall m l
           (HL: has_form m l),
      eval_annot eval_literal m (annot_lit l).
  Proof.
    unfold annot_lit.
    intros.
    apply eval_annot_hyp;auto.
  Qed.

  Lemma eval_annot_augment_hyp :
    forall o l st
           (HL : has_literal (hconsmap st) l)
           (WF : wf_state  st),
      (eval_annot_result_state  (augment_hyp (is_classic o) l st) -> eval_ohformula o) ->
      (eval_annot_state  st -> eval_literal l -> eval_ohformula o).
  Proof.
    Proof.
      intros.
      apply eval_annot_augment_cnf in H; auto.
      apply wf_insert_unit ; auto.
      apply check_annot_hyp; auto.
      apply eval_annot_insert_unit;auto.
      apply eval_annot_hyp; auto.
    Qed.

  Lemma eval_annot_cnf_hyps : forall o l st
                               (HL: Forall (has_literal (hconsmap st)) l)
                               (WF: wf_state  st)
    ,
      (eval_annot_result_state  (cnf_hyps (is_classic o) l st) -> eval_ohformula o) ->
       (eval_annot_state  st -> Forall eval_literal l -> eval_ohformula o).
  Proof.
    unfold cnf_hyps.
    induction l ; simpl.
    - auto.
    - intros.
      inv H1. inv HL.
      specialize (eval_annot_augment_hyp  o a st H3 WF).
      assert (WFA: wf_result_state  (augment_hyp (is_classic o) a st)).
      { apply wf_augment_hyp ; auto.  }
      generalize (hconsmap_augment_hyp  (is_classic o) a st).
      unfold hconsmap_progress.
      destruct (augment_hyp (is_classic o) a st).
      +  simpl in *. tauto.
      + simpl. tauto.
      +
        simpl in *.
      intros.
      assert (HL : Forall (has_literal (hconsmap st0)) l).
      { revert H6.
        apply Forall_Forall.
        apply has_literal_mono; auto.
        intuition congruence.
      }
      specialize (IHl st0 HL).
      tauto.
  Qed.


  Lemma hconsmap_fold_update : forall {A: Type} (F: A -> state -> dresult),
      (forall x st, hconsmap_progress (F x) st) ->
        forall l st, hconsmap_progress (fold_update F l) st.
  Proof.
    unfold hconsmap_progress.
    induction l; simpl; auto.
    intros.
    specialize (H a st).
    destruct (F a st) eqn:EQ; simpl in *; try  tauto.
    rewrite <- H ; auto.
  Qed.


  Lemma hconsmap_cnf_hyps :
    forall o l st,
      hconsmap_progress (cnf_hyps (is_classic o) l) st.
  Proof.
    unfold cnf_hyps.
    intros.
    apply hconsmap_fold_update.
    apply hconsmap_augment_hyp.
  Qed.

  Lemma intro_state_correct :
    forall f st hf
           (EQ    : hf.(elt) = f)
           (WF    : has_form (hconsmap st) hf)
           (WFST : wf_state st)
           (EVAL  : eval_state  st)
           (EVALA  : eval_annot_state  st)
             ,
           match intro_state st f hf with
           | Fail _ => False
           | Success _ => True
           | Progress (st',f') =>
             eval_state  st' -> eval_annot_state st' -> eval_ohformula f'
           end ->
      eval_formula f.
  Proof.
    unfold intro_state.
    intros.
    destruct (intro_impl nil f hf) eqn:I.
    assert (I':=I).
    apply wf_intro_impl with (m:= hconsmap st) in I ; auto.
    generalize (intro_impl_correct (hconsmap st) _ _ _ _ WF EQ I').
    intros. rewrite <- H0. clear H0.
    assert (WFC : wf_result_state (cnf_hyps (is_classic o) l st)).
    { apply wf_cnf_hyps ; auto. tauto. }
    specialize (eval_cnf_hyps o l st).
    generalize (hconsmap_cnf_hyps  o l st).
    unfold hconsmap_progress.
    specialize (eval_annot_cnf_hyps o l st).
    destruct (cnf_hyps (is_classic o) l st).
    - simpl in WFC. tauto.
    - simpl in *. tauto.
    - simpl.
      intros. destruct I as (HL & HH).
      destruct o.
      +
        simpl in H1. eapply has_oform_mono in HH ; eauto.
        generalize (eval_augment_cnf  (Some h) (NEG h) st0 HH WFC).
        generalize (eval_annot_augment_cnf  (Some h) (NEG h) st0 HH WFC).
        simpl.
        destruct ((augment_cnf false (NEG h) st0)).
        * simpl in *. intros.
          unfold eval_hformula in *.
          tauto.
        * simpl in *. tauto.
        * simpl in *; intros.
          intuition.
        * intuition congruence.
      + simpl in *. tauto.
  Qed.

  Lemma eval_annot_intro_state :
    forall f st hf
           (EQ    : hf.(elt) = f)
           (WF    : has_form (hconsmap st) hf)
           (WFST : wf_state st)
           (EVAL  : eval_annot_state  st),
           match intro_state st f hf with
           | Fail _ => False
           | Success (hm',d) => eval_pset hm' d
           | Progress (st',f') => eval_annot_state  st' -> eval_ohformula f'
           end ->
      eval_formula f.
  Proof.
    unfold intro_state.
    intros.
    destruct (intro_impl nil f hf) eqn:I.
    assert (I':=I).
    apply wf_intro_impl with (m:= hconsmap st) in I ; auto.
    generalize (intro_impl_correct (hconsmap st) _ _ _ _ WF EQ I').
    intro IFF. rewrite <- IFF.
    revert EVAL.
    apply eval_annot_cnf_hyps;auto. tauto.
    intro EA.
    destruct I as (HL & HH).
    generalize (wf_cnf_hyps (is_classic o) l st HL WFST).
    generalize (hconsmap_cnf_hyps  o l st).
    unfold hconsmap_progress.
    destruct (cnf_hyps (is_classic o) l st).
    - simpl in EQ. tauto.
    - simpl in *. destruct r.
      tauto.
    - simpl.
      intros HM WFS0.
      destruct o.
      +
        rewrite <- HM in HH by tauto.
        simpl in *.
        generalize (eval_annot_augment_cnf  (Some h) (NEG h) st0 HH WFS0).
        simpl.
        destruct ((augment_cnf false (NEG h) st0)).
        * simpl in *. intros.
          unfold eval_hformula in *.
          tauto.
        * simpl in *. destruct r.
          tauto.
        * simpl in *. tauto.
      + simpl in *. tauto.
  Qed.



  Lemma hconsmap_insert_defs : forall m l,
      hconsmap_eq (insert_defs m l).
  Proof.
    (* weird: reflexivity does not work *)
    unfold insert_defs.
    unfold hconsmap_eq. simpl.
    reflexivity.
  Qed.


  Lemma hconsmap_intro_state :
    forall st f hf,
      ~ is_fail (intro_state st f hf) ->
      match intro_state st f hf with
      | Fail _ => False
      | Progress (st',_) => hconsmap st' = hconsmap st
      | Success (h,_) => h = hconsmap st
      end.
    Proof.
      unfold intro_state.
      intros.
      destruct (intro_impl nil f hf).
      generalize (hconsmap_cnf_hyps o l st).
      unfold hconsmap_progress.
      destruct (cnf_hyps (is_classic o) l st) eqn:EQ; simpl in *.
      - tauto.
      - destruct r ; auto.
      - destruct o ; auto.
        intros.
        generalize (hconsmap_augment_cnf false (NEG h) st0).
        unfold hconsmap_progress.
        destruct ((augment_cnf false (NEG h) st0)) ; simpl in *;
          try intuition congruence.
        + destruct r.
          intuition congruence.
    Qed.


  Lemma intro_state_correct_Some :
    forall f st hf st' f'
           (EQ    : hf.(elt) = f)
           (WF    : has_form (hconsmap st) hf)
           (WFST : wf_state st)
           (INTRO : intro_state st f hf = Progress (st',f'))
           (STEP  : eval_state st' -> eval_annot_state st' -> eval_ohformula f'),
      eval_state st -> eval_annot_state st -> eval_formula f.
  Proof.
    intros.
    generalize (intro_state_correct f st hf EQ WF WFST).
    rewrite INTRO.
    tauto.
  Qed.

  Lemma intro_state_correct_None :
    forall  f st hf d
           (EQ    : hf.(elt) = f)
           (WF    : has_form (hconsmap st) hf)
           (WFST : wf_state st)
           (INTRO : intro_state st f hf = Success d),
      eval_state  st -> eval_annot_state st -> eval_formula f.
  Proof.
    intros.
    generalize (intro_state_correct f st hf EQ WF WFST).
    rewrite INTRO.
    tauto.
  Qed.

  Lemma has_form_hFF :
    forall m, wf m ->
              has_form m hFF.
  Proof.
    unfold hFF.
    intros.
    unfold FF.
    destruct H.
    eapply wf_FF; eauto.
  Qed.

  Lemma wf_intro_state :
    forall f st hf           (*(WFM   : wf m)*)
           (EQ: elt hf = f)
           (WF    : has_form (hconsmap st) hf)
           (WFST : wf_state  st),

           match intro_state st f hf with
           | Progress (st', f') => wf_state  st' /\ has_oform (hconsmap st') f'
           | Success (h,d)          => wf_pset h d
           | Fail  _            => False
           end.
  Proof.
    unfold intro_state.
    intros.
    destruct (intro_impl nil f hf) eqn:WFI.
    apply wf_intro_impl with (m:=hconsmap st) in WFI ; auto.
    destruct WFI.
    generalize (wf_cnf_hyps (is_classic o)  l st).
    generalize (hconsmap_cnf_hyps o l st).
    unfold hconsmap_progress.
    intros.
    destruct (cnf_hyps (is_classic o) l st); try congruence.
    - simpl in H2. tauto.
    - simpl in H1.
      destruct r. simpl in H2; tauto.
    -
      assert (HF : has_oform (hconsmap st0) o).
      { eapply has_oform_mono; eauto.
        simpl in H1. intuition congruence.
      }
    destruct o; try congruence.
    + assert (AM := hconsmap_augment_cnf false (NEG h) st0).
      unfold hconsmap_progress in AM.
      generalize (wf_augment_cnf  false (NEG h) st0).
    destruct ((augment_cnf false (NEG h) st0)); try congruence.
      * simpl. tauto.
      * intros.
        destruct r ; simpl in H3.
        tauto.
      *  simpl in *.
         intuition.
         eapply has_form_mono ; eauto.
         intuition congruence.
    + simpl in *.
      tauto.
  Qed.

  Lemma intro_state_mono : forall st st' f hf g',
      intro_state st f hf = Progress (st', g') ->
  hmap_order (hconsmap st) (hconsmap st').
  Proof.
    unfold intro_state.
    intros.
    destruct (intro_impl nil f hf).
    generalize (hconsmap_cnf_hyps o l st).
    unfold hconsmap_progress.
    destruct (cnf_hyps (is_classic o) l st); try congruence.
    simpl.
    destruct o; simpl; try congruence.
    specialize (hconsmap_augment_cnf false (NEG h) st0).
    unfold hconsmap_progress.
    destruct (augment_cnf false (NEG h) st0); try congruence.
    inv H.
    simpl. intros.
    intuition congruence.
    intuition congruence.
  Qed.
    
  Definition is_classic_lit  (l:literal) : bool :=
    match l with
    | POS _ => true
    | NEG f => f.(is_dec)
    end.

  Fixpoint check_classic (l : list literal) :=
    match l with
    | nil => true
    | e::l => match is_classic_lit e with
              | true => check_classic l
              | false => false
              end
    end.


  Definition is_silly_split (l : list literal) := false.
(*    match l with
    | NEG f :: POS f1 :: POS f2 :: nil =>
      match f.(elt) with
      | OP OR f1' f2' => (f1'.(id) =? f1.(id)) && (f2'.(id) =? f2.(id))
      | _   => false
      end
    | NEG f :: POS f1 :: nil=>
      match f.(elt) with
      | OP AND f1' f2' => (f1'.(id) =? f1.(id)) || (f2'.(id) =? f1.(id))
      | _   => false
      end
    | NEG f1 :: NEG f2 :: nil =>
      match f1.(elt) with
      | OP IMPL f1' f2' => (is_FF f2'.(elt)) && (f1'.(id) =? f2.(id))
      | _   => false
      end
    | NEG f1 :: NEG f2 :: POS f3 :: nil =>
      match f1.(elt) with
      | OP IMPL f1' f2' =>  (f1'.(id) =? f2.(id)) && (f2'.(id) =? f3.(id))
      | _   => false
      end
    | POS f1 :: POS f2 :: nil =>
      match f2.(elt) with
      | OP IMPL f3 f4 => (f1.(id) =? f3.(id)) && (f4.(id) =? 0)
      | _ => false
      end
    | _ => false
    end.
 *)


  Section SEARCH.

    Context  {A: Type}.
    Variable search : forall (k:int) (cl: Annot.t watched_clause), option A.

    Definition  search_in_map  (m : IntMap.ptrie (Annot.t watched_clause))  :=
      IntMap.search search  m.

    Definition search_in_pair_map (pos : bool) (k:int) (e: IntMap.ptrie  (Annot.t watched_clause) * IntMap.ptrie (Annot.t watched_clause)) :=
      if pos then search_in_map (snd e)
      else search_in_map (fst e).

    Definition search_in_watch_map (only_pos:bool) (cl:watch_map) :=
      IntMap.search (search_in_pair_map only_pos) cl.


    Lemma search_in_watch_map_correct :
      forall P b m r
             (WF  : wf_map m)
             (WFE : wf_watch_map m)
             (ALL: ForallWatchedClause P m)
             (S  : search_in_watch_map b m = Some r),
             exists k c, P c /\ search k c = Some r.
    Proof.
      unfold search_in_watch_map.
      intros.
      apply IntMap.search_some with (opt:= None) in S; auto.
      destruct S as (k&v&G&S).
      assert (G':= G).
      apply ALL in G.  destruct G as (GF & GS).
      apply WFE in G'. destruct G' as (WFF & WFS).
      unfold search_in_pair_map in S.
      destruct b.
      - unfold search_in_map in S.
        apply IntMap.search_some with (opt:= None) in S; auto.
        destruct S as (k' & v' & G2 & S2).
        exists k', v'; split; auto.
        apply GS in G2 ; auto.
      - unfold search_in_map in S.
        apply IntMap.search_some with (opt:= None) in S; auto.
        destruct S as (k' & v' & G2 & S2).
        exists k', v'; split; auto.
        apply GF in G2 ; auto.
    Qed.

  End SEARCH.

  Definition is_empty {A: Type} (m: IntMap.ptrie (key:=int) A) :=
    match m with
    | IntMap.Leaf _ _ _ => true
    | _      => false
    end.

  Definition select_clause (is_bot: bool) (lit: IntMap.ptrie (Annot.t bool)) (k:int) (cl : Annot.t watched_clause) :     option (Annot.t (list literal)) :=
    let cl' := Annot.elt cl in
    let res := reduce_lits lit (Annot.deps cl) (watch1 cl' :: watch2 cl' :: unwatched cl') in
    match res with
    | None => None
    | Some l => if (lazy_or is_bot (fun x => Annot.lift check_classic l)) && negb (Annot.lift is_silly_split l) then Some l else None
    end.

  Definition select_in_watch_map (pos: bool) (lit : IntMap.ptrie (Annot.t bool)) (is_bot: bool) (cl:watch_map) : option (Annot.t (list literal)) :=
    search_in_watch_map (select_clause is_bot lit) pos cl.


  Definition find_split (lit : IntMap.ptrie (Annot.t bool)) (is_bot: bool) (cl:watch_map) : option (Annot.t (list literal)) :=
    match select_in_watch_map true lit is_bot cl with
    | None => select_in_watch_map false lit is_bot cl
    | Some r => Some r
    end.


  Definition progress_arrow (l:literal) (st:state): bool :=
    match  find_lit (POS (form_of_literal l)) (units st) with
     | None => true
     | Some b => Annot.lift negb b
    end.

  Fixpoint find_arrows (st: state) (l : list literal) :=
    match l with
    | nil => nil
    | f :: l => if progress_arrow f st
                then f::(find_arrows st l)
                else (find_arrows st l)
    end.

  Fixpoint make_clause (lit: IntMap.ptrie (Annot.t bool)) (ann: LitSet.t) (l: list literal) : Annot.t clause_kind :=
    match l with
    | nil => Annot.mk EMPTY ann
    | e::l => match find_lit e lit with
              | None => reduce lit ann e l
              | Some b => if Annot.elt b then Annot.mk TRUE LitSet.empty else
                            make_clause lit (LitSet.union (Annot.deps b) ann) l
              end
    end.


  Definition augment_with_clause (cl:  list literal) (st:state) : dresult :=
    let (fr,st') := get_fresh_clause_id st in
    insert_normalised_clause fr (make_clause (units st') LitSet.empty  cl) st'.

  Definition augment_clauses  (l: list (list literal)) (st: state) :=
    fold_update  augment_with_clause l st.

  Definition set_hmap (hm: hmap) (st:state) : state  :=
    {|
    fresh_clause_id := fresh_clause_id st;
    hconsmap := hm;
    wneg := wneg st;
    arrows := arrows st;
    defs := defs st;
    units := units st;
    unit_stack := unit_stack st;
    clauses := clauses st
    |}.



  Definition conflict_clause := list literal.

  Definition ProverT :=
    state -> option HFormula -> result state (hmap * list conflict_clause * LitSet.t).


  Lemma has_conflict_clause_mono : isMono has_conflict_clause.
  Proof.
    unfold has_conflict_clause.
    intros m m' cl LE.
    apply Forall_Forall.
    intro.
    apply has_literal_mono; auto.
  Qed.

  Lemma wf_make_clause :
    forall m u cl an
           (WFU: wf_units_lit u m)
           (WFA: wf_pset m an)
           (HAS: has_conflict_clause m cl),
      check_annot has_clause  m (make_clause u an cl).
  Proof.
    induction cl; simpl; auto.
    - intros. split; auto. constructor.
    - intros.
      destruct (find_lit a u) eqn:EQ; simpl ; intros.
      destruct (Annot.elt t0).
      + apply check_annot_TRUE.
      + apply IHcl; auto.
        apply wf_pset_union;auto.
        apply check_annot_find_lit with (hm:=m) in EQ;auto.
        inv HAS;auto.
      + inv HAS.
        apply check_annot_reduce; auto.
  Qed.

    Lemma hconsmap_augment_with_clause :
    forall cl st,
      hconsmap_progress (augment_with_clause cl) st.
  Proof.
    intros.
    unfold augment_with_clause.
    unfold hconsmap_progress.
    intro.
    specialize (hconsmap_get_fresh_clause_id st).
    destruct (get_fresh_clause_id st).
    intros.
    simpl in *.
    rewrite <- H0.
    apply hconsmap_insert_normalised_clause; auto.
  Qed.


  Lemma wf_augment_with_clause :
    forall cl st
           (HAS : has_conflict_clause (hconsmap st) cl)
           (WF: wf_state st),
      wf_result_state (augment_with_clause cl st).
  Proof.
    unfold augment_with_clause.
    intros.
    generalize (wf_get_fresh_clause_id st WF).
    generalize (hconsmap_get_fresh_clause_id st).
    destruct (get_fresh_clause_id st) as (fr,st').
    simpl. intros.
    rewrite <- H in *.
    apply wf_insert_normalised_clause; auto.
    apply wf_make_clause;auto.
    destruct H0; auto.
    auto with wf.
  Qed.


  Lemma eval_make_clause :
    forall m u cl an
           (EV: eval_units m u)
           (HL: Forall  (has_literal m) cl)
           (EC: eval_literal_list cl),
      Annot.lift eval_clause (make_clause u an cl).
  Proof.
    unfold has_conflict_clause.
    induction cl; simpl; auto.
    intros.
    destruct (find_lit a u) eqn:FD.
    - inv HL.
      apply eval_units_find_lit with (m:=m) in FD; auto.
      destruct (Annot.elt t0) ; simpl ; auto.
      + unfold Annot.lift ; simpl ; auto.
      +
        destruct a ; simpl in *.
        apply IHcl ; auto. tauto.
        apply IHcl ; auto.
    - inv HL.
      eapply eval_reduce ; eauto.
  Qed.

  Lemma eval_annot_make_clause :
    forall m u cl an
           (EV: eval_annot_units u m)
           (WFU: wf_units_lit u m)
           (HL: Forall  (has_literal m) cl)
           (WF: wf_pset m an)
           (EC: eval_pset m an -> eval_literal_list cl),
      eval_annot eval_clause m (make_clause u an cl).
  Proof.
    unfold has_conflict_clause.
    induction cl; simpl; auto.
    intros.
    destruct (find_lit a u) eqn:FD.
    - inv HL.
      assert (FD':=FD).
      apply eval_annot_units_find_lit with (m:=m) in FD; auto.
      apply check_annot_find_lit with (hm:=m) in FD'; auto.
      unfold eval_annot, Annot.map in FD.
      simpl in FD.
      destruct (Annot.elt t0) ; simpl ; auto.
      + apply eval_annot_TRUE.
      +
        apply IHcl ; auto.
        apply wf_pset_union;auto.
        intros.
        apply eval_pset_union in H; auto.
        destruct H. intuition.
        eapply eval_neg_literal_rec; eauto.
        destruct FD' ; auto.
        destruct WF;auto.
    - inv HL.
      eapply eval_annot_reduce ; eauto.
  Qed.


  Lemma eval_augment_with_clause :
    forall cl st
           (WS: wf_state st)
           (HC: has_conflict_clause (hconsmap st) cl)
           (ES: eval_state st)
           (EL: eval_literal_list cl),
      eval_result_state (augment_with_clause cl st).
  Proof.
    unfold augment_with_clause.
    intros.
    assert (ES'  := eval_get_fresh_clause st ES).
    assert (WFS' := wf_get_fresh_clause_id st WS).
    assert (MS'  := get_fresh_clause_id_mono st).
    assert (units st = units (snd (get_fresh_clause_id st))).
    {
      destruct st ; simpl; reflexivity.
    }
    destruct (get_fresh_clause_id st) as (i,st') ; simpl; intros.
    apply eval_insert_normalised_clause; auto.
    simpl in *.
    rewrite <- MS' in *.
    apply wf_make_clause; auto.
    destruct WFS';auto.
    auto with wf.
    simpl in *. rewrite <- H.
    eapply eval_make_clause with (m:= hconsmap st) ; eauto.
    destruct ES;auto.
  Qed.

  Lemma eval_annot_augment_with_clause :
    forall cl st
           (WS: wf_state st)
           (HC: has_conflict_clause (hconsmap st) cl)
           (ES: eval_annot_state st)
           (EL: eval_literal_list cl),
      eval_annot_result_state (augment_with_clause cl st).
  Proof.
    unfold augment_with_clause.
    intros.
    assert (ES'  := eval_annot_get_fresh_clause st ES).
    assert (WFS' := wf_get_fresh_clause_id st WS).
    assert (MS'  := get_fresh_clause_id_mono st).
    assert (units st = units (snd (get_fresh_clause_id st))).
    {
      destruct st ; simpl; reflexivity.
    }
    destruct (get_fresh_clause_id st) as (i,st') ; simpl; intros.
    apply eval_annot_insert_normalised_clause; auto.
    - simpl in *.
      rewrite <- MS' in *.
      apply wf_make_clause; auto.
      destruct WFS';auto.
      auto with wf.
    - simpl in *. rewrite <- H.
      rewrite MS'.
      eapply eval_annot_make_clause with (m:= hconsmap st) ; eauto.
      destruct ES;auto.
      destruct WS ; auto.
      apply wf_pset_empty.
  Qed.



  Lemma augment_with_clauses_correct :
    forall cl st
           (WF: wf_state st)
           (CL: has_conflict_clause (hconsmap st) cl),
      ((hconsmap_progress (augment_with_clause cl) st /\
      wf_result_state (augment_with_clause cl st) /\
      (eval_state st -> eval_literal_list cl -> eval_result_state (augment_with_clause cl st)) /\
      (eval_annot_state st -> eval_literal_list cl -> eval_annot_result_state (augment_with_clause cl st)))).
  Proof.
    intros.
    split_and.
    - apply hconsmap_augment_with_clause; auto.
    - apply wf_augment_with_clause;auto.
    - apply eval_augment_with_clause; auto.
    - apply eval_annot_augment_with_clause;auto.
  Qed.

  Lemma augment_with_clause_not_OutOfFuel :
    forall (a : (list literal)) (st : state),
      ~ is_fail (augment_with_clause a st).
  Proof.
    unfold augment_with_clause.
    intros.
    destruct_in_goal FR.
    apply insert_normalised_clause_not_OutOfFuel.
  Qed.

  Lemma Forall_and : forall {A: Type} [P Q: A -> Prop] [l],
      Forall P l -> Forall Q l -> Forall (fun x => P x /\ Q x) l.
  Proof.
    intros.
    rewrite Forall_forall in *.
    intuition.
  Qed.

  Lemma wf_augment_clauses :
    forall st prf
           (WC : Forall (has_conflict_clause (hconsmap st)) prf)
           (WF : wf_state st)
    ,
      wf_result_state (augment_clauses  prf st).
  Proof.
    unfold augment_clauses.
    intros.
    revert WF.
    revert WC.
    change (has_conflict_clause (hconsmap st))
      with
        ((fun st x  => has_conflict_clause (hconsmap st) x) st).
    apply fold_update_correct.
    - unfold augment_with_clause.
      intros.
      assert (HO :hconsmap_result (Progress st') = hconsmap st0).
      {
        rewrite <- H.
        generalize (hconsmap_get_fresh_clause_id st0).
        destruct (get_fresh_clause_id st0) as (fr,st2).
        simpl.
        intros.
        rewrite <- H1.
        apply hconsmap_insert_normalised_clause.
        apply not_fail_insert_normalised_clause.
      }
      {revert H0.
       apply has_conflict_clause_mono; auto.
       simpl in HO. congruence.
      }
    - intros.
      apply wf_augment_with_clause; auto.
  Qed.


  Lemma hconsmap_augment_clauses :
    forall prf st,
      hconsmap_progress (augment_clauses prf) st.
  Proof.
    intros.
    unfold augment_clauses.
    apply hconsmap_fold_update.
    intros.
    apply hconsmap_augment_with_clause.
  Qed.


  Lemma eval_augment_clauses :
    forall prf st
           (WF : wf_state st)
           (WPA  : Forall (has_conflict_clause  (hconsmap st)) prf)
           (EP : Forall eval_literal_list prf)
    ,
      eval_state st ->
      eval_result_state (augment_clauses prf st).
  Proof.
    unfold augment_clauses.
    induction prf; simpl; auto.
    - intros.
      inv EP. inv WPA.
      generalize (eval_augment_with_clause a st WF H4 H H2).
      generalize (wf_augment_with_clause a st H4 WF).
      generalize (hconsmap_augment_with_clause a st).
      unfold hconsmap_progress.
      destruct (augment_with_clause a st) ; simpl; auto.
      intros.
      eapply IHprf;eauto.
      + revert H5.
        apply ForallMono.
        apply has_conflict_clause_mono.
        rewrite H0 by auto.
        auto with wf.
  Qed.


  Lemma eval_annot_augment_clauses :
    forall prf st
           (WF : wf_state st)
           (WPA  : Forall (has_conflict_clause  (hconsmap st)) prf)
           (EP : Forall eval_literal_list prf)
    ,
      eval_annot_state st ->
      eval_annot_result_state (augment_clauses prf st).
  Proof.
    unfold augment_clauses.
    induction prf; simpl; auto.
    - intros.
      inv EP. inv WPA.
      generalize (eval_annot_augment_with_clause a st WF H4 H H2).
      generalize (wf_augment_with_clause a st H4 WF).
      generalize (hconsmap_augment_with_clause a st).
      unfold hconsmap_progress.
      destruct (augment_with_clause a st) ; simpl; auto.
      intros.
      eapply IHprf;eauto.
      + revert H5.
        apply ForallMono.
        apply has_conflict_clause_mono.
        rewrite H0 by auto.
        auto with wf.
  Qed.


  Definition is_correct_prover (Prover : ProverT) (st: state) :=
    forall (g: option HFormula) 
           (m: hmap) (prf : list conflict_clause) d
             (WFS : wf_state  st)
             (HASF: has_oform (hconsmap st) g)
           (PRF : Prover st g  = Success (m,prf,d )),
      (eval_state st -> eval_annot_state st -> eval_ohformula g)
      /\
      (eval_annot_state st -> eval_pset m d -> eval_ohformula g)
      /\
      Forall eval_literal_list prf
      /\
      hmap_order (hconsmap st) m
      /\
      Forall  (has_conflict_clause m) prf
      /\
      wf_pset m d.


  Definition is_correct_prover_progress (Prover : ProverT) (st st': state) :=
    forall (g: option HFormula)
             (WFS : wf_state  st)
             (HASF: has_oform (hconsmap st) g)
           (PRF : Prover st g  = Progress st'),
      ((eval_state st' -> eval_annot_state st' -> eval_ohformula g) ->
      (eval_state st -> eval_annot_state st -> eval_ohformula g))
      /\
      (eval_annot_state st -> eval_annot_state st') /\
      (wf_state st -> wf_state st')
      /\
      hmap_order (hconsmap st) (hconsmap st').

  Section P.


    Variable Prover : state -> option HFormula -> result state (hmap * list conflict_clause * LitSet.t).

    Definition has_lit (h: literal) (s : LitSet.t) :=
      match LitSet.get (id_of_literal h) s with
      | Some (Some b) => Bool.eqb b (is_positive_literal h)
      | _  => false
      end.

    Definition remove_lit (h:literal) (s: LitSet.t) :=
      LitSet.remove (id_of_literal h) s.

    Definition annot_holds (u: IntMap.ptrie (key:=int) (Annot.t bool)) (s : LitSet.t) :=
      IntMap.fold' (fun (acc:bool) i b => if acc
                                   then
                                     match b with
                                     | None => false
                                     | Some b' => match IntMap.get' i u with
                                                  | Some b2 => Bool.eqb b' (Annot.elt b2)
                                                  | _       => false
                                                  end
                                     end
                                   else acc) s true.

    Inductive result_dis :=
    | Backjump (b:bool) (hm:hmap) (prf: list conflict_clause) (deps: LitSet.t)
    | Failure (f:failure).


    Definition lazy_and (b:bool) (f: unit -> bool) :=
      match b with
      | true => f tt
      | false => false
      end.

    Lemma lazy_and_andb : forall b f, lazy_and b f = b && f tt.  Proof.  destruct b ; reflexivity.  Qed.

    Fixpoint case_split (cl: list literal) (st: state) (g : option HFormula)    : result_dis :=
      match cl with
      | nil => Backjump false (hconsmap st) nil LitSet.empty
      | f :: cl =>
        match Prover (insert_unit (annot_hyp f) st) g with
        | Success (m,prf,ann') =>
          if lazy_and (negb (has_lit f ann')) (fun _ =>  annot_holds (units st) ann')
          then Backjump true m prf ann'
          else
            match augment_clauses  prf (set_hmap m st) with
            | Success (m,d') => (* This case is weird *) Backjump true m prf d'
            | Progress st' =>
              match case_split cl st' g with
              | Failure f => Failure f
              | Backjump b m' prf' d' =>
                Backjump b m' (prf++prf')
                         (if b then d' else
                            (LitSet.union d'
                                        (if (has_lit f ann')
                                        then (remove_lit f ann') else ann')))
              end
            | Fail f => Failure f
            end
        | Fail f => Failure f
        | Progress st      => Failure OutOfFuel
        end
      end.


    Definition case_split_ann (an: LitSet.t) (cl:list literal) (st:state) (g: option HFormula)  : result state (hmap * list conflict_clause * LitSet.t) :=
      match case_split cl st g  with
      | Failure f => Fail f
      | Backjump b hm prf d =>
        Success (hm, prf, if b then d else LitSet.union an d)
      end.

    Lemma case_split_rew : forall (st: state) (g : option HFormula)   (cl: list literal),
        case_split  cl st g =
      match cl with
      | nil => Backjump false (hconsmap st) nil LitSet.empty
      | f :: cl =>
        match Prover (insert_unit (annot_hyp f) st) g with
        | Success (m,prf,ann') =>
          if negb (has_lit f ann') && annot_holds (units st) ann'
          then Backjump true m prf ann'
          else
            match augment_clauses  prf (set_hmap m st) with
            | Success (m,d') => (* This case is weird *) Backjump true m prf d'
            | Progress st' =>
              match case_split  cl st' g with
              | Failure f => Failure f
              | Backjump b m' prf' d' =>
                Backjump b m' (prf++prf')
                         (if b then d' else
                            (LitSet.union d'
                                        (if (has_lit f ann')
                                        then (remove_lit f ann') else ann')))
              end
            | Fail f => Failure f
            end
        | Fail f => Failure f
        | Progress st      => Failure OutOfFuel
        end
      end.
    Proof. destruct cl ; reflexivity. Qed.

    Fixpoint eval_or (l:list literal) :=
      match l with
      | nil => False
      | l::r => eval_literal l \/ eval_or r
      end.



    Definition prover_intro (st: state) (g:option HFormula)   :=
      match g with
      | None => Fail HasModel
      | Some g => 
        match intro_state st g.(elt) g with
        | Success (h,d) => Success (h,nil,d)
        | Progress (st',g') => Prover st' g'
        | Fail f => Fail f
        end
      end.


    Fixpoint prover_arrows (l : list literal) (st: state) (g : option HFormula)   :
      result state  (hmap * list conflict_clause * LitSet.t) :=
      match l with
      | nil => Fail Stuck
      | e::l =>
        let f := form_of_literal e in
        match  prover_intro (remove_arrow e st) (Some f)  with
        | Success (m,prf,d)  =>
          let st'' := insert_unit (annot_lit  f) st  in
          (* let st'' := insert_unit (Annot.mk f d) st in (* To track hyps used in the proof... *) *)
          match augment_clauses  prf (set_hmap m st'') with
          | Success (h,d) => Success (h,prf,d) (* CHECK *)
          | Progress st'' => Prover st'' g
          | Fail f        => Fail f
          end
        | Fail OutOfFuel as e => e
        | Fail (HasModel | Stuck)  | Progress _ =>  prover_arrows l st g
        end
      end.

    Lemma prover_arrows_rew : forall (g : option HFormula) (st: state) (l : list literal),
        prover_arrows l st g  =
      match l with
      | nil => Fail Stuck
      | e::l =>
        let f := form_of_literal e in
        match  prover_intro (remove_arrow e st) (Some f)  with
        | Success (m,prf,d)  =>
          let st'' := insert_unit (annot_lit  f) st  in
          match augment_clauses  prf (set_hmap m st'')with
          | Success (h,d) => Success (h,prf,d) (* CHECK *)
          | Progress st'' => Prover st'' g
          | Fail f        => Fail f
          end
        | Fail OutOfFuel as e => e
        | Fail (HasModel | Stuck)  | Progress _ =>  prover_arrows l st g
        end
      end.
    Proof. destruct l; reflexivity. Qed.


    Variable ProverCorrect : forall st, is_correct_prover Prover st.


    Lemma prover_intro_correct : forall st, is_correct_prover prover_intro st.
    Proof.
      repeat intro.
      unfold prover_intro in PRF.
      destruct g; try congruence.
      assert (WF := wf_intro_state (elt h) st h eq_refl HASF WFS).
      assert (HM := hconsmap_intro_state st (elt h) h).
      destruct (intro_state st (elt h) h) eqn:EQ; try congruence.
      - destruct r. inv PRF.
        simpl in *.
        split_and; intros.
        + apply intro_state_correct_None  in EQ; auto.
        + eapply eval_annot_intro_state;eauto.
          rewrite EQ ;auto.
        + constructor.
        + rewrite HM ; auto with wf.
        + constructor.
        + auto.
      - destruct st0 as (st',g').
        destruct WF as (WF' & HF).
        destruct (ProverCorrect _ _ _ _ _ WF' HF PRF) as
            (P1 & P2 & P3 & P4 & P5 & P6).
        split_and; auto.
        + intros.
          apply intro_state_correct_Some  in EQ; auto.
        + intros. eapply eval_annot_intro_state;eauto.
          rewrite EQ ;auto.
        + simpl in *.
          rewrite <- HM by auto.
          tauto.
    Qed.


    Lemma wf_order : forall m m',
        hmap_order m m' ->
        wf m -> wf m'.
    Proof.
      intros.
      destruct H0 ; constructor.
      apply H in wf_false0; auto.
      apply H in wf_true0; auto.
    Qed.

    Lemma order_dom_trans :
      forall {A B C: Type}
             (m1: IntMap.ptrie A)
             (m2: IntMap.ptrie B)
             (m3: IntMap.ptrie C),
        order_dom m1 m2 ->
        order_dom m2 m3 ->
        order_dom m1 m3.
    Proof.
      unfold order_dom.
      intros.
      apply H in H1.
      apply H0 in H1.
      auto.
    Qed.

    Lemma hmap_order_dom : forall m m',
        hmap_order m m' -> order_dom m m'.
    Proof.
      unfold hmap_order, order_dom.
      intros.
      intro.
      destruct (IntMap.get' i m) eqn:EQ; try congruence.
      apply H in EQ.
      congruence.
    Qed.

    Lemma IntMapForall_mono :
      forall {A: Type} (F:hmap -> A -> Prop) (m m' : hmap) (cl : IntMap.ptrie A)
             (FMono : forall x, F m x -> F m' x),
             hmap_order m m' ->
             IntMapForall (F m) cl ->
             IntMapForall (F m') cl.
    Proof.
      unfold IntMapForall.
      intros.
      apply H0 in H1.
      apply FMono ; auto.
    Qed.

    Lemma ForallWatchedClause_mono :
      forall (F:hmap -> Annot.t watched_clause -> Prop)
             (Mono:isMono F)
      , isMono (fun m => ForallWatchedClause (F m) ).
    Proof.
      unfold ForallWatchedClause.
      intros.
      unfold isMono.
      intros m m' ORD x.
      set (G := fun m => IntMapForall2 (F m)).
      change (IntMapForall (G m) x -> IntMapForall (G  m')x).
      apply IntMapForall_mono; auto.
      unfold G. intro.
      unfold IntMapForall2.
      intros.
      destruct H.
      split.
      revert H. apply IntMapForall_mono; auto.
      apply Mono; auto.
      revert H0. apply IntMapForall_mono; auto.
      apply Mono; auto.
    Qed.

    Lemma has_clauses_mono : isMono has_clauses.
    Proof.
      unfold has_clauses.
      apply ForallWatchedClause_mono; auto.
      apply check_annot_mono.
      apply isMono_lift.
      apply has_watched_clause_mono.
    Qed.

    Lemma forall_units_mono :
      forall m m' P u
             (OH: hmap_order m m')
             (WU: wf_units_lit u m)
             (EU: forall_units P m u),
        forall_units P m' u.
    Proof.
      unfold wf_units_lit.
      intros.
      unfold forall_units in *.
      intros.
      destruct H.
      assert (H':= H).
      apply WU in H.
      destruct H as (VI & WF).
      apply EU; auto.
      unfold units_has_literal.
      split ; auto.
      unfold Annot.lift.
      rewrite has_form_of_literal.
      destruct VI as (f1 & HF &EQ).
      assert (Annot.lift form_of_literal l = f1).
      {
        apply has_form_eq with (m:= m'); auto.
        unfold Annot.lift in *.
        apply has_form_of_literal ;auto.
        revert HF.
        apply has_form_mono; auto.
      }
      unfold Annot.lift in H.
      congruence.
    Qed.

    Lemma eval_units_mono :
      forall m m' u
             (OH: hmap_order m m')
             (WU: wf_units_lit u m)
             (EU: eval_units m u),
        eval_units m' u.
    Proof.
      unfold eval_units.
      intros.
      eapply forall_units_mono; eauto.
    Qed.

    Lemma wf_units_def_mono :
      forall {A: Type} m m' (w: @IntMap.ptrie int A)
             (LE : hmap_order m m')
             (WF : wf_units_def w m),
        wf_units_def w m'.
    Proof.
      unfold wf_units_def.
      intros.
      apply WF in H ; auto.
      destruct H as (f & FORM & ID).
      exists f ; split ; auto.
      revert FORM.
      apply has_form_mono;auto.
    Qed.


    Lemma wf_units_lit_mono : forall {A:Type}(u: IntMap.ptrie (Annot.t A)) m m',
        hmap_order m m' ->
        wf_units_lit u m ->
        wf_units_lit u m'.
    Proof.
      unfold wf_units_lit.
      intros.
      apply H0 in H1.
      destruct H1 ; split ; auto with wf.
      eapply valid_index_mono ; eauto.
      eapply wf_pset_mono;eauto.
    Qed.

    Lemma eval_pset_mono : forall m m' p,
        hmap_order m m' ->
        eval_pset m' p -> eval_pset m p.
    Proof.
      intros.
      unfold eval_pset in *.
      intros.
      apply H0 ; auto.
      eapply has_form_mono;eauto.
    Qed.

    Lemma eval_annot_mono : forall {A:Type} (P: A -> Prop),
        isMono (eval_annot P).
    Proof.
      unfold isMono.
      intros. unfold eval_annot in *.
      intros. apply Fm.
      eapply eval_pset_mono; eauto.
    Qed.

    Lemma forall_units_monoP :
      forall (P: hmap -> Annot.t literal -> Prop) m' m u
             (LE : hmap_order m' m)
             (PLE : forall l, P m' l -> P m l)
             (U  : forall_units (P m') m u),
        forall_units (P m) m u.
    Proof.
      unfold forall_units.
      intros.
      apply U in H.
      apply PLE; auto.
    Qed.

    Lemma set_hmap_correct :
      forall m st
             (LE: hmap_order (hconsmap st) m)
             (WF: wf_state st),
             (eval_state st -> eval_state (set_hmap m st)) /\
             (eval_annot_state st -> eval_annot_state (set_hmap m st)) /\
             wf_state (set_hmap m st) /\
             (hconsmap (set_hmap m st) = m).
    Proof.
      intros.
      split_and; simpl; auto.
      - intro ES; destruct ES; constructor; simpl; auto.
        destruct WF.
        eapply eval_units_mono ; eauto.
      - intro ES; destruct ES; constructor; simpl; auto.
        + revert ev_an_stack0.
          apply ForallMono; auto.
          apply eval_annot_mono; auto.
        + apply forall_units_mono with (m':= m) in ev_an_units0; auto.
          unfold eval_annot_units.
          eapply forall_units_monoP; eauto.
          apply eval_annot_mono; auto.
          destruct WF;auto.
        + unfold eval_annot_clauses in *.
          revert ev_an_clauses0.
          apply ForallWatchedClause_mono; auto.
          apply eval_annot_mono.
      - destruct WF.
        constructor ; simpl; auto.
        +  eapply wf_order; eauto.
        + revert wf_arrows0.
          apply Forall_Forall.
          intro. apply has_literal_mono; auto.
        + eapply wf_units_def_mono; eauto.
        + eapply wf_units_lit_mono; eauto.
        +
          revert wf_stack0.
          apply ForallMono; auto.
          apply check_annot_mono; auto.
          apply isMono_lift;auto.
          apply has_literal_mono.
        +
          revert wf_clauses0.
          apply has_clauses_mono; auto.
    Qed.

    Lemma Forall_removeb : forall [A: Type] (P : A -> Prop) (R: A-> bool) l,
        Forall P l ->
        Forall P (removeb R l).
    Proof.
      intros. induction H.
      - constructor.
      - simpl. destruct (R x); auto.
    Qed.

  Lemma remove_arrow_correct : forall e st,
        wf_state st ->
        wf_state (remove_arrow e st) /\
        (eval_state st -> eval_state (remove_arrow e st)) /\
        (eval_annot_state st -> eval_annot_state (remove_arrow e st)) /\
        hconsmap (remove_arrow e st) = hconsmap st.
    Proof.
      intros.
      destruct H.
      split_and.
      - constructor ; auto.
        unfold remove_arrow. simpl.
        apply Forall_removeb; auto.
      - intro H ; destruct H ; constructor ; auto.
      - intro H ; destruct H ; constructor ; auto.
      - reflexivity.
    Qed.

    Lemma wf_pset_singleton : forall hm f,
        has_form hm f -> wf_pset hm (LitSet.singleton (id f) true).
    Proof.
      constructor.
      constructor.
      intros.
      exists f; split;auto.
      unfold LitSet.mem,LitSet.singleton in H0.
      simpl in H0. lia.
    Qed.


    Lemma insert_unit_correct : forall l st,
        wf_state st ->
        check_annot has_literal (hconsmap st) l  ->
        wf_state (insert_unit l st) /\
        hconsmap (insert_unit l st) = hconsmap st /\
        (Annot.lift eval_literal l -> eval_state st ->
         eval_state (insert_unit l st)) /\
        (eval_annot_state st ->
         eval_annot eval_literal (hconsmap st) l ->
         eval_annot_state (insert_unit l st)).
    Proof.
      intros.
      split_and.
      - apply wf_insert_unit; auto.
      -  destruct st ; simpl; reflexivity.
      - intros. apply eval_insert_unit; auto.
      - intros. apply eval_annot_insert_unit; auto.
    Qed.

    Lemma check_annot_lit : forall [hm f],
        has_form hm f ->
        check_annot has_literal hm (annot_lit f).
    Proof.
      unfold annot_lit.
      split ; auto.
      simpl.
      apply wf_pset_singleton ; auto.
    Qed.


    Lemma prover_arrows_correct :
      forall l st
             (ALL : Forall (has_literal (hconsmap st)) l),
             is_correct_prover (prover_arrows l) st.
    Proof.
      induction l.
      - repeat intro.
        simpl in PRF. inv PRF.
      - repeat intro.
        rewrite prover_arrows_rew in PRF.
        inv ALL.
        generalize (remove_arrow_correct a st WFS).
        intros (WFR & EVAL & EVALA & HC).
        set (st' := remove_arrow a st) in *; clearbody st'.
        set (f := form_of_literal a) in *.
        unfold f in PRF.
        destruct (prover_intro st' (Some (form_of_literal a))) eqn:P; try congruence.
        + destruct f0 ; try congruence.
          eapply IHl; eauto.
          eapply IHl; eauto.
        + destruct r as (p,a').
          destruct p as (m',prf').
          assert (HASA : has_oform (hconsmap st') (Some (form_of_literal a))).
          {
            simpl. rewrite HC.
            apply has_form_of_literal; auto.
          }
          apply prover_intro_correct in P; auto.
          simpl in P.
          assert (HASL : (Annot.lift (has_literal (hconsmap st)) (annot_lit (form_of_literal a)))).
          {
            simpl.
            unfold Annot.lift.
            rewrite has_form_of_literal;auto.
            simpl in HASA.
            unfold annot_lit. simpl. congruence.
          }
          simpl in HASA. rewrite HC in HASA.
          generalize (insert_unit_correct (annot_lit (form_of_literal a)) st WFS (check_annot_lit HASA) ).
          intros (WFS' & HCS' & EVS' & EVA').
          set (la:= form_of_literal a) in * ; clearbody la.
          set (st1 := insert_unit (annot_lit la) st) in * ; clearbody st1.
          destruct P as (EP & EA & ALL & ORD & CFL &WFD ).
          assert (ORD1 : hmap_order (hconsmap st1) m').
          {
            eapply hmap_order_trans ; eauto.
            congruence.
          }
          generalize (set_hmap_correct m' st1 ORD1 WFS').
          intros (ESM & ASM & WSM & HCSM).
          set (sm := set_hmap m' st1) in * ; clearbody sm.
          assert (ACM :=  hconsmap_augment_clauses  prf' sm).
          unfold hconsmap_progress in ACM.
          assert (ALL' : Forall  (has_conflict_clause (hconsmap sm)) prf').
          {
            revert CFL.
            apply Forall_Forall.
            intro. apply has_conflict_clause_mono.
            congruence.
          }
          assert (ACW :=  wf_augment_clauses sm prf'  ALL' WSM).
          assert (ACE :=  eval_augment_clauses prf' sm WSM  ALL' ALL).
          assert (ACA :=  eval_annot_augment_clauses prf' sm WSM  ALL' ALL).
          destruct (augment_clauses  prf' sm); simpl in *; try congruence.
          {
            destruct r as (h,d').
            inv PRF.
            split_and ; try tauto.
            - intros.
              exfalso. apply ACA; auto.
              apply ASM. apply EVA' ; auto.
              apply eval_annot_lit; auto.
            - rewrite <- HC.
              eapply hmap_order_trans; eauto.
              intuition congruence.
            - revert ALL'.
              apply ForallMono.
              apply has_conflict_clause_mono.
              rewrite ACM in * by tauto.
              auto with wf.
          }
          {
            apply ProverCorrect in PRF; auto.
            destruct PRF as (PRF1 & PRF2 & PRF3 & PRF4 & PRF5).
            unfold eval_hformula in *.
            assert (ELA := eval_annot_lit (hconsmap st) la).
            split_and; try tauto.
            - subst.
            rewrite HC in *.
            rewrite ACM in * by tauto.
            eapply hmap_order_trans; eauto.
          -
            revert HASF.
            apply has_oform_mono.
            subst.
            rewrite HC in *.
            rewrite ACM in * by tauto.
            tauto.
          }
        +
          eapply IHl; eauto.
    Qed.

    Lemma eval_pset_remove :
      forall m a s
             (HF : has_literal m a)
             (HLIT: has_lit a s = true)
             (WFS: wf_pset m s)
      ,
        eval_literal a -> eval_pset m (remove_lit a s) -> eval_pset m s.
    Proof.
      intros.
      unfold eval_pset in *.
      intros.
      assert (HREM:= H0 f b H1).
      unfold remove_lit, LitSet.get, LitSet.remove in HREM, H1.
      unfold has_lit in *.
      rewrite grspec in HREM by (destruct WFS;auto).
      destruct (eqs (id f) (id_of_literal a)).
      -
        assert (f = form_of_literal a).
        {
          apply has_form_eq with (m:=m) ;auto.
          apply has_form_of_literal; auto.
        }
        subst. clear HREM.
        rewrite e in *.
        destruct ((LitSet.get (id_of_literal a) s)); try congruence.
        destruct t0 ; try congruence.
        unfold OBool.lift_has_bool in H2.
        simpl in *.
        rewrite eqb_true_iff in *.
        subst.
        rewrite literal_eq; auto.
      - apply HREM;auto.
    Qed.

    Lemma wf_remove_lit : forall a s,
        LitSet.wf s ->
        LitSet.wf (remove_lit a s).
    Proof.
      unfold remove_lit.
      intros.
      unfold LitSet.remove.
      apply IntMap.wf_remove'; auto.
    Qed.

    Lemma eval_units_get :
      forall m u f b
             (EVAL : eval_units m u)
             (HF : has_form m f)
             (G : IntMap.get' (id f) u = Some b),
        eval_literal (literal_of_bool (Annot.elt b) f).
    Proof.
      unfold eval_units.
      intros.
      unfold forall_units in EVAL.
      change (Annot.lift eval_literal (Annot.map (fun b => literal_of_bool b f) b)).
      apply EVAL.
      unfold units_has_literal.
      unfold Annot.lift, Annot.map.
      simpl. rewrite id_of_literal_of_bool.
      rewrite is_positive_literal_of_bool.
      destruct b ; simpl ; split; auto.
      destruct elt0; auto.
    Qed.

    Lemma annot_holds_correct :
      forall m u d ,
        annot_holds u d = true ->
        eval_units m u -> eval_pset m d.
    Proof.
      unfold annot_holds.
      intros.
      set (F := (fun (acc : bool) (i : int) (b : option bool) =>
         if acc
         then
          match b with
          | Some b' =>
              match IntMap.get' i u with
              | Some b2 => Bool.eqb b' (Annot.elt b2)
              | None => false
              end
          | None => false
          end
         else acc)) in *.
      rewrite IntMap.fold_elements' in H.
      unfold eval_pset. intros.
      destruct ((LitSet.get (id f) d)) eqn:GET; try discriminate.
      unfold LitSet.get in GET.
      apply IntMap.elements_correct' with (k:=nil) in GET.
      unfold OBool.lift_has_bool in H2.
      simpl in H2.
      revert f b H1 t0 GET H2.
      revert H.
      generalize true at 1.
      change (option bool) with OBool.t.
      induction (IntMap.elements' d nil).
      - simpl. tauto.
      - simpl. intros.
        destruct GET ; subst.
        simpl in H.
        destruct (F b (id f) t0) eqn:Fb.
        + unfold F in Fb.
          destruct b; try congruence.
          destruct t0 ; try congruence.
          destruct (IntMap.get' (id f) u) eqn:G' ; try congruence.
          rewrite eqb_true_iff in Fb.
          subst.
          simpl in H2.
          rewrite eqb_true_iff in H2.
          subst.
          apply eval_units_get with (m:=m) in G'; auto.
        + assert (fold_left (fun (a : bool) (p : int * OBool.t) => F a (fst p) (snd p)) l false = false).
          { clear. induction l; simpl ; auto.
          }
          congruence.
        +  eapply IHl ;eauto.
    Qed.


    Lemma case_split_correct :
      forall l g st m prf a d b
             (WF : wf_state st)
             (HASG : has_oform (hconsmap st) g)
             (HASAN : wf_pset  (hconsmap st) a)
             (HASL : Forall (has_literal (hconsmap st)) l)
             (EQ: case_split l st g = Backjump b m prf d)
      ,
        (eval_state st -> eval_annot_state st ->
         (if b then True else (eval_state st -> ( eval_or l -> eval_ohformula g) -> eval_ohformula g)) -> eval_ohformula g) /\
        (eval_annot_state st -> if b then eval_pset m d -> eval_ohformula g
         else (eval_pset m a -> ((eval_or l -> eval_ohformula g) -> eval_ohformula g) ->
              eval_pset m (LitSet.union a d) -> eval_ohformula g)) /\
        Forall eval_literal_list prf /\
        hmap_order (hconsmap st) m /\
        Forall (has_conflict_clause m) prf /\
        wf_pset m d.
    Proof.
      induction l.
      - simpl. intros.
        inv EQ.
        split_and;auto with wf.
        + tauto.
        + intros AS EV F EU.
          apply eval_pset_union in EU; auto.
          tauto.
          destruct HASAN;auto.
          constructor.
      -
        intros.
        rewrite case_split_rew in EQ.
        unfold is_correct_prover in ProverCorrect.
        inv HASL. rename H1 into HASA .
        rename H2 into HASL.
        assert (WFI:= wf_insert_unit (annot_hyp a) st WF (check_annot_hyp HASA)).
        assert (EI := eval_insert_unit (annot_hyp a) st WF).
        assert (EA := eval_annot_insert_unit (annot_hyp a) st WF).
        assert (ORD := hconsmap_insert_unit (annot_hyp a) st).
        unfold hconsmap_progress in ORD.
        assert (HASG' : has_oform (hconsmap (insert_unit (annot_hyp a) st)) g).
        { revert HASG.
          apply has_oform_mono; auto.
          rewrite hconsmap_insert_unit.
          apply hmap_order_refl.
        }
        set (st':= insert_unit (annot_hyp a) st) in *.
        clearbody st'.
        destruct (Prover st' g) eqn:PRF; try congruence.
        destruct r as (p & ann').
        destruct p as (m',prf').
        destruct (negb (has_lit a ann') && annot_holds (units st) ann') eqn:CHECK.
        + (* backjump *)
          rewrite andb_true_iff in CHECK.
          destruct CHECK as (C1 & HOLD).
          inv EQ.
          clear IHl.
          apply ProverCorrect in PRF.
          destruct PRF as (PRF1 & PRF2 & PRF3 & PRF4 & PRF5 & PRF6).
          assert (HOLD' : eval_state st -> eval_pset m d).
          {
            intros.
            apply annot_holds_correct with (m:= m) in HOLD;auto.
            destruct H.
            revert ev_units0.
            apply eval_units_mono.
            rewrite ORD in *. auto.
            destruct WF ; auto.
          }
          simpl.
          unfold Annot.lift, annot_hyp in EI.
          simpl in *.
          assert (eval_annot eval_literal (hconsmap st) (annot_hyp a)).
          {
            apply eval_annot_hyp; auto.
          }
          split_and; try tauto; auto.
          * eapply hmap_order_trans;eauto.
            rewrite ORD. auto with wf.
          * auto.
          * auto.
        + (* Normal case / no backjump *)
          generalize (ProverCorrect st' g m' prf' ann' WFI HASG' PRF).
          intros (EVAL' & EVALA & EPRF & ORD' & HASC& WFP).
          assert (LE: hmap_order (hconsmap st) m').
          {
            eapply hmap_order_trans ; eauto.
            rewrite ORD. apply hmap_order_refl.
          }
        generalize (set_hmap_correct m' st LE WF).
        set (st2 := set_hmap m' st) in *; clearbody st2.
        generalize (wf_augment_clauses st2 prf').
        intros WFST2' (EVST2 &EVAST2 & WFST2 & HMST2).
        subst.
        assert (CST2 :
                  (Forall  (has_conflict_clause (hconsmap st2)) prf')).
        {
          revert HASC.
          apply Forall_Forall.
          intro.
          apply has_conflict_clause_mono; auto.
          intuition congruence.
        }
        generalize (eval_augment_clauses prf' st2).
        generalize (hconsmap_augment_clauses prf' st2 ).
        unfold hconsmap_progress.
        generalize (wf_augment_clauses st2 prf'  CST2).
        generalize (eval_annot_augment_clauses prf' st2).
        destruct (augment_clauses prf' st2 ) ; try congruence.
        { simpl.
          intros.
          destruct r.
          inv EQ.
          simpl in *.
          rewrite H1 in * by tauto.
          split_and; try tauto.
        }
        {
          intros EVAST0 WFST0 HMST0 EVST0.
          simpl in HMST0.
          assert (HF : has_oform (hconsmap st0) g).
          {
            revert HASG'.
            apply has_oform_mono.
            eapply hmap_order_trans; eauto.
          intuition congruence.
          }
          assert (HASL' : Forall (has_literal (hconsmap st0)) l).
          {
            revert HASL.
            apply Forall_Forall.
            intro.
            apply has_literal_mono.
            eapply hmap_order_trans; eauto.
            intuition congruence.
          }
          assert (WFST0' : wf_state st0) by tauto.
          assert (WFA0  : wf_pset (hconsmap st0) a0).
        {
          eapply wf_pset_mono;eauto.
          rewrite ORD in *.
          rewrite HMST0 by tauto.
          tauto.
        }
        destruct (case_split l st0 g)eqn:DIS; try congruence.
        inv EQ.
        specialize (IHl g st0 m prf0 a0 deps b WFST0' HF WFA0 HASL' DIS).
        destruct IHl as (PRF1 & PRF2 & PRF3 & PRF4 & PRF5 & PRF6 ).
        simpl.
        rewrite HMST0 in * by tauto.
        assert (EA' :=eval_annot_hyp (hconsmap st) a).
        split_and.
          -  destruct b.
             + (* backjump *)
               intros.
               simpl in *.
               tauto.
             + tauto.
        -
          destruct b.
          tauto.
          intros ES EPS EOR EU.
          assert (WFA0' : LitSet.wf a0).
          { destruct WFA0 ; auto. }
          assert (WFD : LitSet.wf deps).
          { destruct PRF6; auto. }
          apply eval_pset_union in EU; auto.
          destruct EU as (EPSA0 & EPSD).
          apply eval_pset_union in EPSD; auto.
          destruct (has_lit a ann') eqn:HASLIT.
          {
          assert (eval_literal a -> eval_pset m (remove_lit a ann') -> eval_pset m ann').
          {
            apply eval_pset_remove;auto.
            revert HASA.
            apply has_literal_mono.
            eapply hmap_order_trans; eauto.
            revert WFP.
            apply wf_pset_mono.
            tauto.
          }
          apply EOR.
          intros OR.
          destruct OR.
          *
          apply EVALA. tauto.
          destruct EPSD as (ED & ER).
          specialize (H H0 ER).
          revert H.
          apply eval_pset_mono.
          tauto.
          *
            apply PRF2; auto.
            apply EVAST0; auto.
            apply eval_pset_union; auto.
            tauto.
          }
          {
          apply EVALA. tauto.
          destruct EPSD as (ED & ER).
          revert ER.
          apply eval_pset_mono.
          tauto.
          }
          + destruct (has_lit a ann').
            apply wf_remove_lit; auto.
            destruct WFP; auto.
            destruct WFP; auto.
          + destruct (has_lit a ann').
            apply LitSet.wf_union; auto.
            apply wf_remove_lit; auto.
            destruct WFP; auto.
            apply LitSet.wf_union; auto.
            destruct WFP; auto.
        -
          rewrite Forall_app.
          tauto.
        -
          eapply hmap_order_trans; eauto.
        - rewrite Forall_app.
          split.
          revert HASC.
          eapply ForallMono.
          apply has_conflict_clause_mono.
          tauto.
          tauto.
        - destruct b ; try tauto.
          + destruct (has_lit a ann').
            apply wf_pset_union;auto.
            unfold remove_lit.
            apply wf_pset_remove; auto.
            revert WFP.
            apply wf_pset_mono.
            tauto.
            apply wf_pset_union;auto.
            revert WFP.
            apply wf_pset_mono.
            tauto.
        }
    Qed.



    Lemma case_split_ann_correct :
      forall  st g a cl m prf d
              (UPWF : wf_state st)
              (PRF : case_split_ann a cl st g = Success (m, prf, d))
              (EVST : eval_state st -> (*eval_annot_state st ->*)
                      (eval_or cl -> eval_ohformula g) -> eval_ohformula g)
              (EVA : eval_annot_state st ->
                     (eval_pset  (hconsmap st)  a)  -> (( eval_or  cl  -> eval_ohformula g) -> eval_ohformula g))
              (AN :  wf_pset (hconsmap st) a)
              (WFD : (has_conflict_clause (hconsmap st)) cl)
              (HF  : has_oform (hconsmap st) g)

      ,

        (eval_state st -> eval_annot_state st -> eval_ohformula g) /\
        (eval_annot_state st -> eval_pset m d -> eval_ohformula g) /\
        Forall eval_literal_list prf /\
        hmap_order (hconsmap st) m /\ Forall (has_conflict_clause m) prf /\ wf_pset m d.
    Proof.
      unfold case_split_ann.
      intros.
      destruct (case_split cl st g) eqn:EQ; try congruence.
      inv PRF.
      unfold eval_annot in EVA.
      simpl in EVA.
      apply case_split_correct with (a:= a) in EQ; auto.
      destruct EQ as (PRF1 & PRF2 & PRF3 & PRF4 & PRF5 & PRF6).
      split_and; try tauto.
      -  destruct b; auto.
      - intros EPA EPS.
        destruct b.
        tauto.
        assert (EA : eval_pset m a).
        { apply eval_pset_union in EPS.
          destruct EPS; auto.
          destruct AN;auto.
          destruct PRF6;auto.
        }
        assert (EA' : eval_pset (hconsmap st) a).
        {
          revert EA.
          apply eval_pset_mono; auto.
        }
        apply PRF2 ; auto.
      - destruct b ; auto.
        apply wf_pset_union.
        revert AN. apply wf_pset_mono; auto.
        revert PRF6. apply wf_pset_mono; auto with wf.
    Qed.

  Section ThyProver.
    Variable thy: Thy.

    (** From a context,
        ¬ a₁,..., ¬aₙ , b₁, bₘ ⊢ c
        we run the prover with the following clause
        b₁ → ... bₘ → a₁ ∨ ... ∨ aₙ ∨ c
        It generates a conflict clause
        bᵢ → ... → bⱼ → aₖ ∨ ... ∨ aₗ ∨ (c)
        using a subset of the bᵢ and aᵢ
     *)

    Definition get_atom (m: hmap) (k: int)  :=
      match IntMap.get' k m with
      | None => None (* Should not happen *)
      | Some (d,f) =>
        match f with
        | LAT a => Some (HCons.mk k d f)
        |  _   => None
        end
      end.

    Definition get_literal (m:hmap) (k:int) (b:bool) : option literal :=
      match get_atom m k with
      | None => None
      | Some a => Some (literal_of_bool b a)
      end.

    (** [collect_literal] positive litteral are in the first list (but negated) *)
    Definition collect_literal (m:hmap) (acc: list literal * list  literal) (k:int) (b:Annot.t bool) :=
      match get_atom m k with
      | None => acc
      | Some f => if Annot.elt b then ( (NEG f):: fst acc, snd acc)
                  else (fst acc,  (POS f)::snd acc)
      end.

    Definition get_wneg (m:hmap) (acc: list  literal) (k:int) (b : unit) :=
      match get_atom m k with
      | None => acc
      | Some f => POS  f::acc
      end.


    Definition collect_all_wneg (m:hmap) (wn : IntMap.ptrie (key:=int) unit) :=
      IntMap.fold' (get_wneg m) wn nil.


    Definition extract_theory_problem (m : hmap) (u : IntMap.ptrie (key:=int) (Annot.t bool)) : list  literal * list literal :=
      IntMap.fold' (collect_literal m) u (nil,nil).


    Definition add_conclusion  (c : option HFormula) (acc : list  literal * list  literal) :=
      match c with
      | None => acc
      | Some f => match f.(elt) with
                  | LAT a => (fst acc, POS f:: snd acc)
                  | _    => acc
                  end
      end.

    Definition generate_conflict_clause (st:state) (g: option HFormula) :=
      let (ln,lp) := add_conclusion  g (extract_theory_problem (hconsmap st) (units st)) in
      let wn  := collect_all_wneg (hconsmap st) (wneg st) in
       ln ++ (wn++lp).


    Definition deps_of_clause (l : list literal) : LitSet.t := LitSet.empty. (* TODO *)


    Definition run_thy_prover (st: state) (g: option HFormula)  :=
      let cl := generate_conflict_clause st g in
      match thy.(thy_prover) (hconsmap st) cl with
      | None => Fail HasModel
      | Some (h',cl') =>
        match augment_with_clause cl'  (set_hmap h' st) with
        | Success (h',d) => Success (h',cl'::nil,d)
        | Progress st' => Prover st' g
        | Fail f       => Fail f
        end
      end.

  Lemma wf_extract_thy_pb : forall hm u l1 l2
                                   (WF  : wf_map u)
                                   (WFU : wf_units_def u hm ),
      extract_theory_problem hm u = (l1,l2) ->
      Forall (has_literal hm) l1 /\ Forall (has_literal hm) l2.
  Proof.
    unfold extract_theory_problem.
    intros.
    change l1 with (fst (l1,l2)).
    rewrite <- H.
    change l2 with (snd (l1,l2)).
    rewrite <- H.
    clear H.
    set (Q := fun (r:list literal * list literal) => Forall (has_literal hm) (fst r)
        /\
        Forall (has_literal hm) (snd r)).
    change (Q (IntMap.fold' (collect_literal hm) u (nil, nil))).
    rewrite PTrie.fold_elements'.
    unfold wf_units_def in WFU.
    assert (forall i v, In (i,v) (PTrie.elements' u nil) ->
                        forall b a,
                          IntMap.get' i hm = Some (b,LAT a) ->
                          has_form hm (HCons.mk i b (LAT a))).
    {
      intros.
      apply PTrie.in_elements' with (opt:=None) in H.
      simpl in H.
      destruct H ; [|tauto].
      assert (PTrie.get' i u <> None) by congruence.
      apply WFU in H1.
      destruct H1 as (f1 & HF & ID).
      inv HF; simpl in * ; try congruence.
      rewrite H0 in H1.
      inv H1. constructor; auto.
      auto.
    }
    assert (QACC : Q (nil,nil)).
    {
      unfold Q. simpl.
      split ; constructor.
    }
    revert QACC.
    generalize ((nil,nil): list literal * list literal).
    induction (PTrie.elements' u nil).
    -  simpl. auto.
    - intros.
      simpl in *.
      eapply IHl ; eauto.
      unfold Q.
      unfold collect_literal.
      destruct (get_atom hm (fst a)) eqn:GA ; auto.
      assert (has_form hm t0).
      {
        unfold get_atom in GA.
        destruct (IntMap.get' (fst a) hm) eqn:EQ ; try congruence.
        destruct p0.
        destruct l0 ; try congruence.
        inv GA.
        destruct a ; simpl in *.
        eapply H ; eauto.
      }
      destruct p ; simpl.
      destruct QACC.
      simpl in *.
      destruct (Annot.elt (snd a)) ; split ; simpl ; try constructor ; simpl; auto.
  Qed.

  Lemma wf_add_conclusion :
    forall [hm l1 l2 g]
           (WFL1: Forall (has_literal hm) l1)
           (WFL2: Forall (has_literal hm) l2)
           (HASG: has_oform hm g)
    ,
      Forall (has_literal hm) (fst (add_conclusion g (l1,l2)))
      /\
      Forall (has_literal hm) (snd (add_conclusion g (l1,l2))).
  Proof.
    unfold add_conclusion.
    destruct g ; auto.
    simpl.
    destruct (elt h) eqn:EQ; simpl; auto.
  Qed.

  Lemma wf_app_conflict_clause :
    forall [hm l1 l2]
           (WFL1: Forall (has_literal hm) l1)
           (WFL2: Forall (has_literal hm) l2),
      Forall (has_literal hm) (l1 ++ l2).
  Proof.
    unfold generate_conflict_clause.
    intros.
    rewrite Forall_app.
    tauto.
  Qed.

  Lemma wf_collect_all_wneg :
    forall hm w
           (WF : wf_map w)
           (WFU : wf_units_def w hm),
      Forall (has_literal hm) (collect_all_wneg hm w).
  Proof.
    unfold collect_all_wneg.
    intros.
    set (Q := fun (r:list literal) => Forall (has_literal hm) r).
    rewrite PTrie.fold_elements'.
    unfold wf_units_def in WFU.
    assert (forall i v, In (i,v) (PTrie.elements' w nil) ->
                        forall b a,
                          IntMap.get' i hm = Some (b,LAT a) ->
                          has_form hm (HCons.mk i b (LAT a))).
    {
      intros.
      apply PTrie.in_elements' with (opt:=None) in H.
      simpl in H.
      destruct H ; [|tauto].
      assert (PTrie.get' i w <> None) by congruence.
      apply WFU in H1.
      destruct H1 as (f1 & HF & ID).
      inv HF; simpl in * ; try congruence.
      rewrite H0 in H1.
      inv H1. constructor; auto.
      auto.
    }
    assert (QACC : Q nil).
    {
      unfold Q. simpl.
      constructor.
    }
    revert QACC.
    generalize (nil: list literal).
    induction (PTrie.elements' w nil).
    -  simpl. auto.
    - intros.
      simpl in *.
      eapply IHl ; eauto.
      unfold Q.
      unfold get_wneg.
      destruct (get_atom hm (fst a)) eqn:GA ; auto.
      assert (has_form hm t0).
      {
        unfold get_atom in GA.
        destruct (IntMap.get' (fst a) hm) eqn:EQ ; try congruence.
        destruct p.
        destruct l1 ; try congruence.
        inv GA.
        destruct a ; simpl in *.
        eapply H ; eauto.
      }
      constructor ; auto.
  Qed.

  Lemma wf_units_weaken : forall (u: IntMap.ptrie (Annot.t bool)) m,
      wf_units_lit u m ->
      wf_units_def u m.
  Proof.
    unfold wf_units_def, wf_units_lit.
    intros.
    destruct (IntMap.get' i u) eqn:EQ ; try congruence.
    apply H in EQ. tauto.
  Qed.

  Lemma wf_generate_conflict_clause :
    forall [st g]
           (WF: wf_state st)
           (HASG: has_oform (hconsmap st) g),
      Forall (has_literal (hconsmap st)) (generate_conflict_clause st g).
  Proof.
    unfold generate_conflict_clause.
    intros.
    destruct WF.
    destruct (extract_theory_problem (hconsmap st) (units st)) as (ln,lp) eqn:EQ.
    apply wf_extract_thy_pb in EQ; auto.
    destruct EQ as (C1 & C2).
    specialize (wf_add_conclusion  C1 C2 HASG).
    destruct (add_conclusion g (ln,lp)) as (ln1,lp1).
    simpl.
    intros (C1' & C2').
    repeat rewrite Forall_app.
    repeat split ; auto.
    apply wf_collect_all_wneg; auto.
    apply wf_units_weaken; auto.
  Qed.


  Lemma run_thy_prover_correct : forall st, is_correct_prover run_thy_prover  st.
    Proof.
      unfold is_correct_prover.
      intros.
      unfold run_thy_prover in PRF.
      specialize (wf_generate_conflict_clause WFS HASF).
      set (l := (generate_conflict_clause st g)) in * ; clearbody l.
      intro C.
      destruct (thy_prover thy (hconsmap st) l) eqn:THY ; try congruence.
      destruct p as (h',cl').
      apply thy_prover_sound in THY.
      destruct THY as (EV & ORD & WF).
      generalize (set_hmap_correct h' st ORD WFS).
      intros (EV' & EA' & WF' & ORD').
      set (st' := set_hmap h' st) in *.
      clearbody st'.  subst.
      generalize (augment_with_clauses_correct cl' st' WF'  WF).
      intros (ORD2 & WF2 & EVAL2 & EA2).
      unfold hconsmap_progress in ORD2.
      destruct (augment_with_clause cl' st'); try congruence.
      - destruct r.
        inv PRF.
        simpl in *.
        rewrite! Forall_rew.
        intuition.
        + (* hmap_order *) subst. auto.
        + revert WF.
          apply ForallMono.
          apply has_literal_mono.
          subst. auto with wf.
      -  apply ProverCorrect in PRF; auto.
         simpl in *.
         destruct PRF as (PRF1 & PRF2 & PRF3 & PRF4 & PRF5 & PRF6).
         split_and ; try tauto.
         +
            eapply hmap_order_trans;eauto.
            rewrite <- ORD2 by tauto.
            auto.
         + revert HASF.
           simpl in *.
           apply has_oform_mono.
           eapply hmap_order_trans;eauto.
           rewrite <- ORD2 by tauto.
           auto with wf.
    Qed.

    End ThyProver.




  End P.

  Section Prover.

    Definition seq_prover (p : ProverT) (q: ProverT) : ProverT :=
      fun st f  =>
        match p st f with
        | Success(h,l, d) => Success(h,l,d)
        | Progress st'   => q st' f
        | Fail Stuck  => q st f
        | Fail _ as e => e
        end.

    Fixpoint seq_provers (l: list ProverT) : ProverT :=
      match l with
      | nil  => fun st f => Fail HasModel
      | p :: nil => p
      | p::l => seq_prover p (seq_provers l)
      end.

    Definition prover_case_split (P: ProverT) (st:state) (g: option HFormula) :=
      match find_split (units st) (is_classic g) (clauses st) with
      | None => Fail Stuck
      | Some cl => case_split_ann P (Annot.deps cl)  (Annot.elt cl) st g
      end.

    Definition  prover_thy (P: ProverT) (thy: Thy) (use_prover: bool) (st: state) (g: option HFormula) :=
      if use_prover
      then run_thy_prover P thy st g
      else Fail HasModel.


    Definition prover_unit_propagation (n:nat) (st:state) (g : option HFormula) : result state (hmap * list conflict_clause * LitSet.t) :=
      match unit_propagation n  g st with
      | Success (hm,d) => Success (hm,nil,d)
      | Progress st'   => Progress st'
      | Fail f      => Fail f
      end.

    Definition prover_impl_arrows (P:ProverT) st g :=
      prover_arrows P (find_arrows st (arrows st)) st g.

    Fixpoint prover  (thy: Thy) (use_prover: bool) (n:nat)  (st:state) (g : option HFormula)   : result state (hmap * list conflict_clause * LitSet.t) :=
      match n with
      | O => Fail OutOfFuel
      | S n => let ProverRec := prover thy use_prover n in
               seq_prover (prover_unit_propagation n)
                          (seq_prover (prover_case_split ProverRec)
                                      (seq_prover (prover_impl_arrows ProverRec)
                                                  (prover_thy ProverRec thy use_prover))) st g
      end.


    Lemma prover_rew : forall thy up n,
        prover thy up (n:nat)     =
        match n with
      | O => fun _ _ => Fail OutOfFuel
      | S n => let ProverRec := prover thy up n in
               seq_prover (prover_unit_propagation n)
                          (seq_prover (prover_case_split ProverRec)
                                      (seq_prover (prover_impl_arrows ProverRec)
                                                  (prover_thy ProverRec thy up)))
        end.
    Proof.
      destruct n ; reflexivity.
    Qed.

    Fixpoint prover_opt  (thy: Thy) (use_prover: bool) (n:nat)  (st:state) (g : option HFormula)   : result state (hmap * list conflict_clause * LitSet.t) :=
      match n with
      | O => Fail OutOfFuel
      | S n => let ProverRec := prover_opt thy use_prover n in
               match unit_propagation n g st with
               | Success (hm,d) => Success(hm,nil,d)
               | Progress st'   =>
                 (seq_prover (prover_case_split ProverRec)
                             (seq_prover (prover_impl_arrows ProverRec)
                                         (prover_thy ProverRec thy use_prover))) st' g
               | Fail f => Fail f
               end
      end.

    Lemma prover_opt_rew : forall  (thy: Thy) (use_prover: bool) (n:nat)  (st:state) (g : option HFormula),
        prover_opt thy use_prover n st g = 
        match n with
      | O => Fail OutOfFuel
      | S n => let ProverRec := prover_opt thy use_prover n in
               match unit_propagation n g st with
               | Success (hm,d) => Success(hm,nil,d)
               | Progress st'   =>
                 (seq_prover (prover_case_split ProverRec)
                             (seq_prover (prover_impl_arrows ProverRec)
                                         (prover_thy ProverRec thy use_prover))) st' g
               | Fail f => Fail f
               end
      end.
    Proof.
      destruct n ; reflexivity.
    Qed.
      
    Lemma shorten_clauses_not_stuck : forall u st,
        shorten_clauses u st = Fail Stuck -> False.
    Proof.
      unfold shorten_clauses.
      intros u st.
      rewrite PTrie.fold_elements'.
      assert (Acc : (Progress st: dresult)  <> Fail Stuck).
      {
        congruence.
      }
      revert Acc.
      generalize ((Progress st: dresult)).
      set (F:= (fun (a : dresult) (p : int * Annot.t watched_clause) =>
     update_watched_clause (fst p) (snd p) a)).
      induction (PTrie.elements' u nil).
      - simpl. congruence.
      - simpl.
        intros.
        revert H.
        apply IHl.
        unfold  F.
        unfold update_watched_clause.
        destruct d. congruence.
        congruence.
        unfold insert_watched_clause.
        set (cl':= (shorten_clause
       (units (remove_watched_clause (fst a) (Annot.elt (snd a)) st0))
       (Annot.deps (snd a)) (Annot.elt (snd a)))).
        unfold insert_normalised_clause.
        destruct (Annot.elt cl') ; try congruence.
    Qed.


    Lemma unit_propagation_not_stuck : forall n g st,
        unit_propagation n g st = Fail Stuck -> False.
    Proof.
      induction n.
      - simpl. discriminate.
      - simpl. intros.
        destruct (extract_unit st).
        destruct p.
        destruct (success g (units s) t0).
        congruence.
        destruct (find_clauses (id_of_literal (Annot.elt t0)) (clauses s)).
        destruct (  shorten_clauses match Annot.elt t0 with
                        | POS _ => p
                        | NEG _ => p0
                        end (insert_literal t0 s)) eqn:E; try congruence.
        inv H.
        apply shorten_clauses_not_stuck in E; auto.
        congruence.
    Qed.

    Definition eq_prover (P1 P2: ProverT) :=
      forall st g, P1 st g = P2 st g.

    Lemma eq_seq_prover : forall P1 P2 Q1 Q2,
        eq_prover P1 Q1 -> eq_prover P2 Q2 ->
        eq_prover
          (seq_prover P1 P2) (seq_prover Q1 Q2).
    Proof.
      unfold seq_prover,eq_prover.
      intros.
      rewrite H.
      destruct (Q1 st g); try congruence.
      destruct f; try reflexivity.
      apply H0.
    Qed.

    Lemma eq_prover_case_split_ann : forall P Q,
        eq_prover P Q ->
        forall cl d,
        eq_prover (case_split_ann P d cl)
                  (case_split_ann Q d cl).
    Proof.
      unfold eq_prover, case_split_ann.
      intros.
      replace  (case_split P cl st g) with (case_split Q cl st g).
      reflexivity.
      revert st g.
      induction cl.
      + reflexivity.
      + simpl.
        intros.
        rewrite H.
        destruct_in_goal G; try reflexivity.
        destruct r,p.
        destruct_in_goal C2; try reflexivity.
        destruct_in_goal M1; try reflexivity.
        rewrite IHcl.
        reflexivity.
    Qed.


    Lemma eq_prover_case_split : forall P Q,
        eq_prover P Q ->
        eq_prover (prover_case_split P)
                  (prover_case_split Q).
    Proof.
      unfold eq_prover, prover_case_split.
      intros.
      destruct (find_split (units st) (is_classic g) (clauses st)); auto.
      unfold case_split_ann.
      apply eq_prover_case_split_ann; auto.
    Qed.
    
    Lemma eq_prover_impl_arrows : forall P Q,
        eq_prover P Q ->
        eq_prover (prover_impl_arrows P) (prover_impl_arrows Q).
    Proof.
      unfold eq_prover.
      unfold prover_impl_arrows.
      intros.
      revert g.
      generalize (find_arrows st (arrows st)).
      intro l; revert st.
      induction l; simpl.
      reflexivity.
      intros.
      destruct (intro_state (remove_arrow a st) (elt (form_of_literal a))
        (form_of_literal a)); try reflexivity.
      destruct f; try reflexivity.
      apply IHl; auto.
      apply IHl; auto.
      destruct r; try reflexivity.
      destruct_in_goal M1; try reflexivity.
      auto.
      destruct st0.
      rewrite H.
      destruct (Q s o); try reflexivity.
      destruct f; auto.
      destruct r,p.
      destruct_in_goal M1; try reflexivity.
      auto. auto.
    Qed.

    Lemma eq_prover_thy : forall thy up P Q,
        eq_prover P Q ->
        eq_prover (prover_thy P thy up)
                  (prover_thy Q thy up).
    Proof.
      unfold eq_prover, prover_thy.
      intros.
      destruct up; try reflexivity.
      unfold run_thy_prover.
      destruct (thy_prover thy (hconsmap st) (generate_conflict_clause st g)); auto.
      destruct p.
      destruct_in_goal M1; auto.
    Qed.


    Lemma prover_op_eq : forall thy use_prover n,
        eq_prover (prover thy use_prover n) (prover_opt thy use_prover n).
    Proof.
      unfold eq_prover.
      induction n.
      - simpl. reflexivity.
      - simpl. intros.
        unfold seq_prover at 1.
        unfold prover_unit_propagation.
        destruct (unit_propagation n g st) eqn:UP.
        + destruct f; try reflexivity.
          apply unit_propagation_not_stuck in UP.
          tauto.
        + destruct r; auto.
        + repeat apply eq_seq_prover.
          apply eq_prover_case_split;auto.
          apply eq_prover_impl_arrows; auto.
          apply eq_prover_thy;auto.
    Qed.


  Lemma eval_literal_list_classic :
    forall m l
           (HF : Forall (has_literal m) l)
           (EV: eval_literal_list l)
           (C : check_classic l = true),
      eval_or l.
  Proof.
    induction l; simpl ; auto.
    intros.
    destruct_in_hyp C ISC; try congruence.
    inv HF.
    destruct a; simpl in *.
    -  intuition.
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


  Lemma eval_select_clause :
    forall m g u k v
           (WFU: wf_units_lit u m)
           (EU : eval_units m u)
           (EW : Annot.lift eval_watched_clause v)
           (CHK : check_annot has_watched_clause m v)
           (EVAL : ohold (Annot.lift eval_or) (select_clause (is_classic g) u k v) -> eval_ohformula g),
      eval_ohformula g.
  Proof.
    intros.
    revert  EW.
    unfold select_clause in EVAL.
    destruct_in_hyp EVAL R; [|simpl in EVAL ; auto].
    destruct_in_hyp EVAL C; [| simpl in EVAL ; auto].
    rewrite <- R in EVAL.
    rewrite andb_true_iff in C.
    destruct C as (C & _).
    assert (WFR : ohold (check_annot has_conflict_clause m) (reduce_lits u (Annot.deps v)
                                                              (watch1 (Annot.elt v)
         :: watch2 (Annot.elt v) :: unwatched (Annot.elt v)))).
    { apply wf_reduce_lits; auto.
      destruct CHK ; auto.
      destruct CHK; auto.
    }
    destruct g ; simpl in C.
    - intro. apply EVAL.
      rewrite R. simpl.
      apply eval_literal_list_classic with (m:=m) ;auto.
      rewrite R in WFR;auto.
      simpl in WFR.
      destruct WFR ; auto.
      change (ohold (Annot.lift eval_literal_list) (Some t0)).
      rewrite <- R.
      eapply eval_reduce_lits; eauto.
      destruct CHK ;auto.
    - unfold eval_ohformula in *.
      intro EVAL'.
      eapply eval_reduce_lits in EVAL'; eauto.
      rewrite R in EVAL'.
      simpl in EVAL'.
      revert EVAL'.
      apply eval_literal_list_neg;auto.
      rewrite R in *. auto.
      destruct CHK;auto.
  Qed.



  Lemma subset_reduce_lits :
    forall u m (WFU: wf_units_lit u m) cl an
           (WF: wf_map an)
    ,
      ohold
        (fun x => wf_map (Annot.deps x) /\ LitSet.subset an (Annot.deps x))
        (reduce_lits u an cl).
  Proof.
    induction cl.
    - simpl. intro.
      split ; auto.
      unfold LitSet.subset. intros.
      destruct (LitSet.get k an) ; simpl ; auto.
      apply OBool.order_refl.
    - simpl.
      intros. destruct (find_lit a u) eqn:EQ.
      + apply check_annot_find_lit with (hm:=m) in EQ; auto.
      destruct (Annot.elt t0);simpl ; auto.
      specialize  (IHcl ((LitSet.union (Annot.deps t0) an))).
      destruct ((reduce_lits u (LitSet.union (Annot.deps t0) an) cl)); simpl in *; auto.
      assert (WFM : wf_map (LitSet.union (Annot.deps t0) an)).
      {
        apply LitSet.wf_union;auto.
        destruct EQ;auto.
      }
      specialize (IHcl WFM).
      destruct IHcl.
      split ; auto.
      eapply LitSet.subset_trans ; eauto.
      apply LitSet.subset_union_r;auto.
      destruct EQ ; auto.
      + specialize (IHcl _ WF).
        destruct (reduce_lits u an cl); simpl; auto.
  Qed.

  Lemma has_boolb_mono : forall b t1 t2,
      OBool.order t1 t2 ->
      OBool.has_boolb b t1 = true ->
      OBool.has_boolb b t2 = true.
  Proof.
    unfold OBool.has_boolb.
    destruct t1, t2 ; simpl; try tauto.
    intros; subst; auto.
  Qed.


  Lemma eval_pset_subset : forall m an an',
      LitSet.subset an an' ->
      eval_pset m an' -> eval_pset m an.
  Proof.
    unfold eval_pset.
    intros.
    apply H0; auto.
    unfold LitSet.subset in *.
    specialize (H (id f)).
    unfold OBool.lift_has_bool in *.
    destruct (LitSet.get (id f) an) , (LitSet.get (id f) an') ; simpl in *; intuition try congruence.
    -
      eapply has_boolb_mono    ; eauto.
  Qed.

  Lemma eval_annot_reduce_lits :
    forall m u
           (WFU : wf_units_lit u m)
           (EV : eval_annot_units u m)
           cl
           (WFC : Forall (has_literal m) cl) an
           (WFA : wf_pset m an)
           (EC : eval_pset m an ->  eval_literal_list cl),
      (ohold (eval_annot eval_literal_list m) (reduce_lits u an cl)).
  Proof.
    intros m u  WFU EV cl WFC. induction WFC.
    - simpl in *. auto.
    - simpl in *.
      destruct (find_lit x u) eqn:EQ.
      assert (EQ':=EQ).
      apply eval_annot_units_find_lit with (m:=m) in EQ; auto.
      apply check_annot_find_lit with (hm:=m) in EQ'; auto.
      unfold eval_annot, Annot.map in EQ,EQ'. simpl in EQ,EQ'.
      + destruct (Annot.elt t0) ; simpl ; auto.
        intros.
        assert (WFUnion : wf_pset m (LitSet.union (Annot.deps t0) an)).
        {
          apply wf_pset_union;auto.
        }
        apply IHWFC; auto.
        intro.
        apply eval_pset_union in H0 ; auto.
        apply eval_neg_literal_rec in EC; auto.
        tauto. tauto.
        destruct EQ';auto.
        destruct WFA;auto.
      +  intros.
         specialize (IHWFC an WFA).
         specialize (subset_reduce_lits u m WFU l an (wf_map_pset m _ WFA)).
         destruct (reduce_lits u an l) eqn:EQ1; simpl in *; auto.
         unfold Annot.map, eval_annot in *.
         simpl in *.
         intros (WFM & SUB).
         intro.
         eapply eval_pset_subset in SUB; eauto.
         destruct x ; simpl in *; auto.
         tauto.
  Qed.


  Lemma eval_annot_select_clause :
    forall m g u k v
           (WFU: wf_units_lit u m)
           (EU : eval_annot_units u m)
           (EW :  eval_annot eval_watched_clause m v)
           (CHK : check_annot has_watched_clause m v)
           (EVAL : ohold (eval_annot eval_or m) (select_clause (is_classic g) u k v) -> eval_ohformula g),
      eval_ohformula g.
  Proof.
    intros.
    revert  EW.
    unfold select_clause in EVAL.
    destruct_in_hyp EVAL R; [|simpl in EVAL ; auto].
    destruct_in_hyp EVAL C; [| simpl in EVAL ; auto].
    rewrite <- R in EVAL.
    rewrite andb_true_iff in C.
    destruct C as (C & _).
    assert (WFR : ohold (check_annot has_conflict_clause m) (reduce_lits u (Annot.deps v)
                                                              (watch1 (Annot.elt v)
         :: watch2 (Annot.elt v) :: unwatched (Annot.elt v)))).
    { apply wf_reduce_lits; auto.
      destruct CHK ; auto.
      destruct CHK; auto.
    }
    destruct g ; simpl in C.
    - intro.
      apply EVAL.
      rewrite R. simpl.
      unfold eval_annot.
      intro.
      apply eval_literal_list_classic with (m:=m) ;auto.
      rewrite R in WFR;auto.
      simpl in WFR.
      destruct WFR ; auto.
      revert H.
      change (ohold (eval_annot eval_literal_list m) (Some t0)).
      rewrite <- R.
      eapply eval_annot_reduce_lits;eauto.
      destruct CHK ;auto.
      destruct CHK ; auto.
    - unfold eval_ohformula in *.
      intro.
      eapply eval_annot_reduce_lits in EW; eauto.
      rewrite R in EW.
      simpl in EW.
      revert EW.
      unfold eval_annot in *.
      intros.
      rewrite R in *.
      simpl in EVAL.
      specialize (eval_literal_list_neg (Annot.elt t0)).
      intuition.
      destruct CHK;auto.
      destruct CHK;auto.
  Qed.



  Lemma check_annot_reduce_lits :
    forall m u l an
           (WFU: wf_units_lit u m)
           (WFL: has_conflict_clause m l)
           (WFA: wf_pset m an),
      ohold (check_annot has_conflict_clause  m) (reduce_lits u an l).
  Proof.
    induction l; simpl; auto; intros.
    - split ; simpl;auto.
    -
      inv WFL.
      destruct (find_lit a u) eqn:FD.
      apply check_annot_find_lit with (hm:= m) in FD; auto.
      destruct (Annot.elt t0); simpl ; auto.
      + apply IHl ; auto.
        apply wf_pset_union;auto.
      +
        specialize (IHl _ WFU H2 WFA).
        destruct (reduce_lits u an l); simpl in *; auto.
        destruct IHl.
        split ; simpl;auto.
        unfold Annot.map, Annot.lift.
        constructor ;auto.
  Qed.

  Lemma check_annot_select_clause :
    forall  b m u k v
            (WU : wf_units_lit u m)
            (CHK : check_annot has_watched_clause m v),
      ohold (check_annot has_conflict_clause m) (select_clause b u k v).
  Proof.
    unfold select_clause.
    intros.
    destruct CHK.
    destruct_in_goal R.
    rewrite lazy_or_orb.
    destruct_in_goal B.
    rewrite <- R.
    apply check_annot_reduce_lits; auto.
    simpl. auto.
    simpl. auto.
  Qed.


  Lemma ForallWatchedClauseAND : forall P Q cls,
      ForallWatchedClause P cls -> ForallWatchedClause Q cls ->
      ForallWatchedClause (fun cl : Annot.t watched_clause => P cl /\ Q cl) cls.
  Proof.
    intros.
    unfold ForallWatchedClause in *.
    specialize (IntMapForallAnd _ _ _  H H0).
    apply IntMapForall_Forall.
    intros.
    destruct H1. destruct H1. destruct H2.
    split.
    apply IntMapForallAnd ; auto.
    apply IntMapForallAnd ; auto.
  Qed.


  Lemma eval_select_in_watch_map :
    forall pos m g u cls
           (WFM: wf_map cls)
           (WFW: wf_watch_map cls)
           (WFU: wf_units_lit u m)
           (EU : eval_units m u)
           (WF : has_clauses m cls)
           (EV : eval_clauses  cls)
           (EVAL : ohold (Annot.lift eval_or) (select_in_watch_map pos u (is_classic g) cls) -> eval_ohformula g),
      eval_ohformula g.
  Proof.
    intros.
    unfold select_in_watch_map in EVAL.
    revert EVAL.
    destruct (search_in_watch_map (select_clause (is_classic g) u) pos cls) eqn:EQ; [|simpl; tauto].
    apply search_in_watch_map_correct
      with (P :=
              fun cl => Annot.lift eval_watched_clause cl /\ check_annot has_watched_clause m cl) in EQ; auto.
    destruct EQ as (k&v&P&S).
    rewrite <- S.
    destruct P as (P1 & P2).
    eapply eval_select_clause; eauto.
    apply ForallWatchedClauseAND; auto.
  Qed.

  Lemma eval_find_split :
    forall m g u cls
           (WFM: wf_map cls)
           (WFW: wf_watch_map cls)
           (WFU: wf_units_lit u m)
           (EU : eval_units m u)
           (WF : has_clauses m cls)
           (EV : eval_clauses  cls)
           (EVAL : ohold (Annot.lift eval_or) (find_split u (is_classic g) cls) -> eval_ohformula g),
      eval_ohformula g.
  Proof.
    intros.
    unfold find_split in EVAL.
    revert EVAL.
    destruct_in_goal SEL.
    rewrite <- SEL.
    eapply eval_select_in_watch_map; eauto.
    eapply eval_select_in_watch_map; eauto.
  Qed.

  Lemma eval_annot_select_in_watch_map :
    forall pos m g u cls
           (WFM: wf_map cls)
           (WFW: wf_watch_map cls)
           (WFU: wf_units_lit u m)
           (EU : eval_annot_units u m)
           (WF : has_clauses m cls)
           (EV : eval_annot_clauses m cls)
           (EVAL : ohold (eval_annot  eval_or m) (select_in_watch_map pos u (is_classic g) cls) -> eval_ohformula g),
      eval_ohformula g.
  Proof.
    intros.
    unfold select_in_watch_map in EVAL.
    revert EVAL.
    destruct (search_in_watch_map (select_clause (is_classic g) u) pos cls) eqn:EQ; [|simpl; tauto].
    apply search_in_watch_map_correct
      with (P :=
              fun cl =>   eval_annot eval_watched_clause m cl /\ check_annot has_watched_clause m cl) in EQ; auto.
    destruct EQ as (k&v&P&S).
    rewrite <- S.
    destruct P as (P1 & P2).
    eapply eval_annot_select_clause; eauto.
    apply ForallWatchedClauseAND; auto.
  Qed.

  Lemma eval_annot_find_split :
    forall m g u cls
           (WFM: wf_map cls)
           (WFW: wf_watch_map cls)
           (WFU: wf_units_lit u m)
           (EU : eval_annot_units u m)
           (WF : has_clauses m cls)
           (EV : eval_annot_clauses m cls)
           (EVAL : ohold (eval_annot  eval_or m) (find_split u (is_classic g) cls) -> eval_ohformula g),
      eval_ohformula g.
  Proof.
    intros.
    unfold find_split in EVAL.
    revert EVAL.
    destruct_in_goal SEL.
    rewrite <- SEL.
    apply eval_annot_select_in_watch_map; auto.
    apply eval_annot_select_in_watch_map; auto.
  Qed.

  Lemma wf_select_in_watch_map :
    forall pos m g u cls
           (WFM: wf_map cls)
           (WFU: wf_units_lit u m)
           (WFW: wf_watch_map cls)
           (WF : has_clauses m cls),
      ohold (check_annot has_conflict_clause  m) (select_in_watch_map pos u (is_classic g) cls) .
  Proof.
    intros.
    unfold select_in_watch_map.
    destruct (search_in_watch_map (select_clause (is_classic g) u) pos cls) eqn:EQ; [|simpl; tauto].
    apply search_in_watch_map_correct
      with (P :=
              fun cl => check_annot has_watched_clause m cl) in EQ; auto.
    destruct EQ as (k&v&P&S).
    rewrite <- S.
    apply check_annot_select_clause; auto.
  Qed.


  Lemma wf_find_split :
    forall m g u cls
           (WFM: wf_map cls)
           (WFU: wf_units_lit u m)
           (WFW: wf_watch_map cls)
           (WF : has_clauses m cls),
      ohold (check_annot has_conflict_clause  m) (find_split u (is_classic g) cls) .
  Proof.
    intros.
    unfold find_split.
    destruct_in_goal SEL.
    rewrite <- SEL.
    apply wf_select_in_watch_map ; auto.
    apply wf_select_in_watch_map ; auto.
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

  Lemma wf_remove_arrow :
    forall e st,
           wf_state st ->
      wf_state (remove_arrow e st).
  Proof.
    intros.
    destruct H; constructor ; auto.
    unfold remove_arrow. simpl.
    apply Forall_removeb ;auto.
  Qed.

  Lemma eval_remove_arrow :
    forall l st,
      eval_state  st ->
      eval_state (remove_arrow l st).
  Proof.
    intros.
    destruct H; constructor ; auto.
  Qed.

  Lemma is_correct_prover_seq :
    forall P Q
           (CP : forall st, is_correct_prover P st)
           (CPP : forall st st', is_correct_prover_progress P st st')
           (CQ : forall st, is_correct_prover Q st),
    forall st, is_correct_prover (seq_prover P Q) st.
  Proof.
    intros.
    unfold seq_prover.
    unfold is_correct_prover.
    intros.
    destruct (P st g) eqn:EQ ; try congruence.
    - destruct f ; try congruence.
      eapply CQ ; eauto.
    - destruct r. destruct p.
      inv PRF.
      eapply CP ; eauto.
    - eapply CPP in EQ ; eauto.
      eapply CQ in PRF.
      split_and; try tauto.
      + intuition.
        eapply hmap_order_trans; eauto.
      + tauto.
      + eapply has_oform_mono ; eauto.
        tauto.
  Qed.

  Definition never_progress (Prover : ProverT) (st: state) :=
    forall (g: option HFormula) st'
           (PRF : Prover st g  = Progress st'), False.

  Lemma never_progress_seq : forall P Q,
      (forall st, never_progress Q st) ->
      forall st,  never_progress (seq_prover P Q) st.
  Proof.
    unfold never_progress, seq_prover.
    intros.
    destruct (P st g) ; try congruence.
    destruct f ; try congruence.
    eapply H ; eauto.
    destruct r. destruct p ; try congruence.
    eapply H ; eauto.
  Qed.




  Lemma prover_correct : forall thy b n st, is_correct_prover (prover thy b n) st /\ never_progress (prover thy b n) st.
  Proof.
    induction n.
    - unfold is_correct_prover. simpl ; auto.
      split ; try congruence.
    -
      rewrite prover_rew.
      remember (prover thy b n) as P.
      simpl.
      split.
      repeat apply is_correct_prover_seq.
      + unfold is_correct_prover.
        intros.
        unfold prover_unit_propagation in PRF.
        assert (UPC := unit_propagation_correct n _ _  WFS HASF).
        assert (UPA := eval_annot_unit_propagation n _ _ WFS HASF).
        assert (UPWF := wf_unit_propagation n _ _  WFS HASF).
        assert (UPM := hconsmap_unit_propagation n g st0).
        unfold hconsmap_progress in UPM.
        destruct (unit_propagation n g st0) ; try discriminate.
        simpl in UPM.
        destruct r. inv PRF.
        split_and; auto with wf.
        rewrite UPM by auto.
        apply hmap_order_refl.
      +  unfold is_correct_prover_progress.
        intros.
        unfold prover_unit_propagation in PRF.
        assert (UPC := unit_propagation_correct n _ _  WFS HASF).
        assert (UPA := eval_annot_unit_propagation n _ _ WFS HASF).
        assert (UPWF := wf_unit_propagation n _ _  WFS HASF).
        assert (UPM := hconsmap_unit_propagation n g st0).
        unfold hconsmap_progress in UPM.
        destruct (unit_propagation n g st0) ; try discriminate.
        simpl in UPM.
        destruct r. inv PRF. inv PRF.
        split_and; auto with wf.
        simpl in UPM. rewrite UPM by auto.
        apply hmap_order_refl.
      + unfold is_correct_prover.
        intros.
        unfold prover_case_split in PRF.
        destruct (find_split (units st0) (is_classic g) (clauses st0)) eqn:FD ; try congruence.
        *
          assert (FDC : eval_state st0 -> (ohold (Annot.lift eval_or) (find_split (units st0) (is_classic g) (clauses st0)) -> eval_ohformula g) ->
                  eval_ohformula g).
          {
            intro ES'. destruct ES' ; destruct WFS.
            apply eval_find_split with (m:=(hconsmap st0)); auto.
          }
          assert (FDC' :
                    eval_annot_state st0 ->
                      eval_pset (hconsmap st0) (Annot.deps t0) ->
                        (eval_or (Annot.elt t0) -> eval_ohformula g) -> eval_ohformula g).
          {
            intro ES'. destruct ES' ; destruct WFS.
            intros.
            eapply eval_annot_find_split in ev_an_clauses0; eauto.
            rewrite FD. simpl. unfold eval_annot ; auto.
          }
          rewrite FD in FDC.
          simpl in FDC.
          assert (WFD : (ohold (check_annot has_conflict_clause  (hconsmap st0)) (find_split (units st0) (is_classic g) (clauses st0)))).
          {
            destruct WFS.
            apply wf_find_split; auto.
          }
          rewrite FD in WFD.
          assert (HF0 : has_oform (hconsmap st0) g).
          {
            revert HASF.
            apply has_oform_mono; auto.
            simpl in *.
            intuition congruence.
          }
          simpl in WFD.
          destruct WFD as (AN & WFD).
          unfold Annot.lift in *.
          eapply case_split_ann_correct; eauto.
          apply IHn.
      + intros.
        unfold is_correct_prover_progress.
        unfold prover_case_split.
        intros.
        destruct_in_hyp PRF F; try discriminate.
        unfold case_split_ann in PRF.
        destruct_in_hyp PRF C; try discriminate.
      + unfold is_correct_prover; intros.
        unfold prover_impl_arrows in PRF.
        assert (Forall (has_literal (hconsmap st0)) (find_arrows st0 (arrows st0))).
          {
            apply has_find_arrows.
            destruct WFS ; auto.
          }
          set (l := (find_arrows st0 (arrows st0))) in *.
          clearbody l.
          apply prover_arrows_correct in PRF ; auto.
          apply IHn.
      + unfold is_correct_prover_progress.
        intros.
        unfold prover_impl_arrows in PRF.
        exfalso.
        induction ((find_arrows st0 (arrows st0))).
        discriminate.
        simpl in PRF.
        destruct   (intro_state (remove_arrow a st0) (elt (form_of_literal a))
                                (form_of_literal a)).
        destruct f ; try congruence.
        destruct r. unfold augment_clauses in PRF.
        simpl in PRF.
        eapply IHn ; eauto.
        destruct st1.
        destruct (P s o) ; try discriminate.
        destruct f ; try discriminate.
        tauto.
        tauto.
        destruct r.
        destruct p.
        destruct_in_hyp PRF A; try discriminate.
        destruct r ; discriminate.
        eapply IHn; eauto.
        tauto.
      + intros.
        unfold is_correct_prover.
        unfold prover_thy.
        destruct b ; try congruence.
        apply run_thy_prover_correct.
        apply IHn ; auto.
      +
        repeat apply never_progress_seq.
        unfold never_progress, prover_thy.
        destruct b ; try congruence.
        unfold run_thy_prover.
        intros.
        destruct (thy_prover thy (hconsmap st0) (generate_conflict_clause st0 g)); try congruence.
        destruct p.
        destruct_in_hyp PRF H ; try congruence.
        destruct r ; try congruence.
        eapply IHn ; eauto.
  Qed.


  Definition wf_entry (p : LForm -> bool) (v : option (bool * LForm)) :=
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
      apply is_FF_true in H.
      congruence.
    - unfold wf_entry in H0.
      destruct (IntMap.get' 1 m) ; try congruence.
      destruct p.
      rewrite andb_true_iff in H0.
      destruct H0.
      rewrite Bool.eqb_true_iff in H1. subst.
      apply is_TT_true in H0.
      congruence.
  Qed.

  Definition prover_formula thy (up: bool) (m: hmap) (n:nat) (f: HFormula)  :=
    if wfb m && chkHc m f.(elt) f.(id) f.(is_dec)
    then prover_intro (prover_opt thy up n) (insert_unit (annot_lit hTT) (empty_state m)) (Some f)
    else Fail HasModel.

  Definition prover_bformula thy (m: hmap) (n:nat) (f: HFormula)  :=
    match prover_formula thy false m n f with
    | Success _ => true
    |  _    => false
    end.

  Lemma wf_units_def_empty : forall {A: Type} m,
      wf_units_def (IntMap.empty A) m.
  Proof.
    unfold wf_units_def.
    intros.
    rewrite empty_o in H.
    congruence.
  Qed.


  Lemma wf_empty : forall m,
      wf m ->
      wf_state (empty_state m).
  Proof.
    constructor ; simpl;auto.
    - apply wf_map_empty;auto.
    - apply wf_units_def_empty.
    - unfold wf_units_lit.
      intros. rewrite empty_o in H0.
      congruence.
    - apply IntMapForallEmpty.
   - apply wf_map_empty;auto.
   - apply wf_map_empty;auto.
   - apply IntMapForallEmpty.
  Qed.

  Lemma forall_units_empty : forall P m ,
      forall_units P m (IntMap.empty (Annot.t bool)).
  Proof.
    unfold forall_units.
    intros.
    unfold units_has_literal in H.
    destruct H.
    rewrite empty_o in H.
    congruence.
  Qed.

  Lemma eval_empty : forall m, eval_state (empty_state m).
  Proof.
    unfold empty_state.
    constructor ; simpl ; auto.
    - unfold eval_units.
      apply forall_units_empty.
    -  constructor.
    - repeat intro.
      unfold empty_watch_map in H.
      rewrite empty_o in H.
      congruence.
  Qed.

  Lemma eval_annot_empty : forall m,
      eval_annot_state (empty_state m).
  Proof.
    unfold empty_state.
    constructor ; simpl ; auto.
    apply forall_units_empty.
    repeat intro.
      unfold empty_watch_map in H.
      rewrite empty_o in H.
      congruence.
  Qed.

  Lemma eq_is_correct_prover : forall P Q,
      eq_prover P Q ->
      (forall st, is_correct_prover P st) ->
      forall st : state, is_correct_prover Q st.
  Proof.
    unfold is_correct_prover; intros.
    rewrite <- H in PRF.
    eauto.
  Qed.

  Lemma prover_formula_correct : forall thy up m m' prf d n f ,
      prover_formula thy up m n f = Success (m',prf, d) ->
      eval_hformula f.
  Proof.
    unfold prover_formula.
    intros.
    destruct (wfb m && chkHc m (elt f) (id f) (is_dec f)) eqn:EQ ; try congruence.
    rewrite andb_true_iff in EQ.
    destruct EQ as (WFM & CHK).
    apply wfb_correct in WFM.
    apply chkHc_has_form in CHK; auto.
    assert (WE := wf_empty m WFM).
    assert (EE := eval_empty m).
    assert (EA := eval_annot_empty m).
    assert (M : hconsmap (empty_state m) = m) by reflexivity.
    set (s0 := empty_state m) in *.
    clearbody s0.
    assert (HL : has_literal (hconsmap s0) (POS hTT)).
    {
      simpl. unfold hTT. unfold TT. apply wf_OP with (l':= nil).
      constructor.
      apply wf_true ; auto. congruence.
      reflexivity. reflexivity.
    }
    assert (HL' : check_annot has_literal (hconsmap s0) (annot_lit hTT)).
    {
      apply check_annot_lit.
      apply HL.
    }
    generalize (insert_unit_correct _ _ WE HL').
    intros (WF & HM & EV).
    simpl in EV.
    set (s1 := (insert_unit (annot_lit hTT) s0)) in * ; clearbody s1.
    destruct (prover_intro (prover_opt thy up n) s1 (Some f))
             eqn:PI ; try congruence.
    destruct r. destruct p.
    inv H.
    apply prover_intro_correct  in PI; auto.
    -  simpl in *. unfold annot_lit, Annot.lift in EV. simpl in EV.
       assert (ETT := eval_annot_hyp _ (POS hTT) HL) .
       tauto.
    -
      apply eq_is_correct_prover with (P:= prover thy up n).
      apply prover_op_eq.
      eapply prover_correct; eauto.
    - simpl.
      destruct f ; simpl in *.
      congruence.
  Qed.


(*  Definition incr (i:int) :=
    if i =? max_int then max_int else i + 1. *)

  Fixpoint hcons  (m : hmap) (f : LForm) : hmap :=
    match f with
    | LFF   => m
    | LAT a => m
    | LOP o l =>
      List.fold_left (fun m f =>
                        IntMap.set' f.(id) (f.(is_dec),f.(elt))
                                           (hcons m f.(elt))) l m
    | LIMPL l r =>
      List.fold_left (fun m f =>
                        IntMap.set' f.(id) (f.(is_dec),f.(elt))
                                           (hcons m f.(elt))) (r::l) m
    end.

  Definition hmap_empty := IntMap.set' 0 (true, FF) (IntMap.set' 1 (true,TT) (IntMap.empty _)).

  Definition hcons_form (f : HFormula) : hmap :=
    IntMap.set' f.(id) (f.(is_dec),f.(elt)) (hcons hmap_empty f.(elt)).

  Definition hcons_prover (thy:Thy) (n:nat) (f:HFormula) :=
    let m := hcons_form f in
    prover_bformula thy m n f.

  Lemma hcons_prover_correct : forall thy n f ,
      hcons_prover thy n f = true ->
      eval_hformula f.
  Proof.
    unfold hcons_prover.
    intros.
    unfold prover_bformula in H.
    destruct (prover_formula thy false (hcons_form f) n f) eqn:EQ; try congruence.
    destruct r. destruct p.
    apply prover_formula_correct in EQ.
    auto.
  Qed.


  End Prover.
  End S.


  Definition eval_kind (k:kind) : Type :=
    match k with
    | IsProp => Prop
    | IsBool => bool
    end.


Module BForm.


  Definition HBForm := HCons.t (BForm IsProp).


  Section S.
    Variable eval_atom : forall (k:kind), int -> eval_kind k.

    Definition eval_TT (k:kind) : eval_kind k :=
      match k with
      | IsProp => True
      | IsBool => true
      end.

    Definition eval_FF (k:kind) : eval_kind k :=
      match k with
      | IsProp => False
      | IsBool => false
      end.

    Definition eval_binop (fp : Prop -> Prop -> Prop) (fb : bool -> bool -> bool)  (k:kind) : eval_kind k -> eval_kind k -> eval_kind k :=
      match k with
      | IsProp => fp
      | IsBool => fb
      end.

    Definition eval_op (o:op) (k:kind) : eval_kind k -> eval_kind k -> eval_kind k :=
      match o with
      | AND => eval_binop and andb k
      | OR  => eval_binop or orb k
      | IMPL => eval_binop (fun x y => x -> y) implb k
      end.

    Fixpoint eval_bformula (k:kind) (f: BForm k) : eval_kind k :=
      match f with
      | BTT k => eval_TT k
      | BFF k => eval_FF k
      | BAT k i => eval_atom k i
      | BOP k o f1 f2 => eval_op o k
                                (eval_bformula k f1.(elt))
                                (eval_bformula k f2.(elt))
      | BIT f => Is_true (eval_bformula _ f)
      end.

    (** Certain atoms have no boolean counterpart *)
    Variable has_bool : int -> bool.

    Definition map_hcons {A B:Type} (f: A -> B) (e : HCons.t A) : HCons.t B :=
      HCons.mk e.(id) e.(is_dec) (f e.(elt)).

    Definition poll (o:op) (pol:bool)  :=
      match o with
      | AND | OR => pol
      | IMPL => negb pol
      end.

    Definition keep_atom (k:kind) (i:int) :=
      match k with
      | IsProp => true
      | IsBool => has_bool i
      end.

    Fixpoint to_formula (pol:bool) (k:kind) (f:BForm k) : LForm :=
      match f with
      | BTT k => TT
      | BFF k => FF
      | BAT k i => if keep_atom k i
                   then LAT i
                   else if pol then FF else TT
      | BOP k o f1 f2 =>
        match o with
        | AND  =>  LOP LAND
                       ((map_hcons (to_formula pol k) f1):: (map_hcons (to_formula pol k) f2)::nil)
        | OR   =>  LOP LOR
                       ((map_hcons (to_formula pol k) f1):: (map_hcons (to_formula pol k) f2)::nil)
        | IMPL => LIMPL ((map_hcons (to_formula (negb pol) k) f1):: nil) (map_hcons (to_formula pol k) f2)
        end
      | BIT f =>  (to_formula pol IsBool f)
      end.

    Definition hold (k:kind) : eval_kind k ->  Prop :=
      match k with
      | IsBool => fun v => Is_true v
      | IsProp => fun v => v
      end.

    Definition impl_pol (pol : bool) (p1 p2: Prop) :=
      if pol then p1 -> p2 else p2 -> p1.

    Lemma impl_pol_iff : forall pol p q, (p <-> q) -> impl_pol pol p q.
    Proof.
      unfold impl_pol.
      destruct pol; tauto.
    Qed.

    Lemma hold_eval_TT : forall k, hold k (eval_TT k) <-> True.
    Proof.
      destruct k ; simpl.
      tauto.
      unfold Is_true.
      tauto.
    Qed.

    Lemma hold_eval_FF : forall k,
        hold k (eval_FF k) <-> False.
    Proof.
      destruct k ; simpl.
      tauto.
      unfold Is_true.
      intuition congruence.
    Qed.

    Variable has_bool_correct :
      forall i : int,
        has_bool i = true -> eval_atom IsProp i <-> Is_true (eval_atom IsBool i).

    Lemma has_bool_hold_eval_atom :
      forall k i, has_bool i = true ->
                  eval_atom IsProp i <-> hold k (eval_atom k i).
    Proof.
      destruct k ; simpl; intros.
      tauto.
      apply has_bool_correct ; auto.
    Qed.

    Lemma hold_eval_binop_and : forall k f1 f2,
        hold k (eval_binop and andb k f1 f2) <->
        (hold k f1 /\ hold k f2).
    Proof.
      destruct k ; simpl; intros.
      - tauto.
      - split; intros.
        apply andb_prop_elim. auto.
        apply andb_prop_intro.  tauto.
    Qed.

    Lemma hold_eval_binop_or : forall k f1 f2,
        hold k (eval_binop or orb k f1 f2) <->
        (hold k f1 \/ hold k f2).
    Proof.
      destruct k ; simpl; intros.
      - tauto.
      - split; intros.
        apply orb_prop_elim. auto.
        apply orb_prop_intro.  tauto.
    Qed.

    Lemma hold_eval_binop_impl : forall k f1 f2,
        hold k (eval_binop (fun x y => x -> y) implb k f1 f2) <->
        (hold k f1 -> hold k f2).
    Proof.
      destruct k ; simpl; intros.
      - tauto.
      - split; intros.
        destruct f1,f2 ; unfold Is_true in *; simpl in *; auto.
        destruct f1,f2 ; unfold Is_true in *; simpl in *; auto.
    Qed.



    Fixpoint aux_to_formula_correct (pol:bool) (k:kind) (f:BForm k) {struct f} :
      if pol
      then eval_formula (eval_atom IsProp) (to_formula pol k f) -> hold k (eval_bformula k f)
      else hold k (eval_bformula k f) -> eval_formula (eval_atom IsProp) (to_formula pol k f).
    Proof.
      destruct f; simpl.
      -
        destruct pol.
        + rewrite hold_eval_TT. tauto.
        + rewrite hold_eval_TT. tauto.
      - destruct pol.
        + rewrite hold_eval_FF. tauto.
        + rewrite hold_eval_FF. tauto.
      -
        unfold keep_atom.
        destruct k.
        +  destruct pol ; simpl ; tauto.
        +
        destruct (has_bool i) eqn:EQ.
        * apply has_bool_hold_eval_atom with (k:=IsBool) in EQ.
          destruct pol.
          simpl. tauto.
          simpl. tauto.
        *  destruct pol; simpl.
           tauto.
           tauto.
      - generalize (aux_to_formula_correct pol k (elt t0)).
        generalize (aux_to_formula_correct pol k (elt t1)).
        destruct o; simpl.
        + destruct pol ; rewrite hold_eval_binop_and.
          tauto.
          tauto.
        + destruct pol ; rewrite hold_eval_binop_or.
          tauto.
          tauto.
        + generalize (aux_to_formula_correct (negb pol) k (elt t0)).
          destruct pol; rewrite hold_eval_binop_impl.
          * simpl.
            tauto.
          * simpl.
            tauto.
      - generalize (aux_to_formula_correct pol IsBool f).
        destruct pol.
        + simpl. tauto.
        + simpl. tauto.
    Qed.

    Lemma to_formula_correct : forall (f:BForm IsProp),
        eval_formula (eval_atom IsProp) (to_formula true IsProp f) ->
        eval_bformula IsProp f.
    Proof.
      apply (aux_to_formula_correct true IsProp).
    Qed.

    Definition to_hformula (f : HBForm) :=
      map_hcons (to_formula true IsProp) f.

    Definition eval_hbformula  (f: HBForm) :=
      eval_bformula  IsProp f.(elt).

    Lemma to_hformula_correct : forall (f:HBForm),
        eval_hformula (eval_atom IsProp) (to_hformula  f) ->
        eval_hbformula  f.
    Proof.
      intros.
      apply to_formula_correct.
      apply H.
    Qed.



  End S.

End BForm.

Definition empty (A:Type) : @IntMap.ptrie int A := IntMap.empty A.
Definition set (A:Type) (i:int) (v:A) (m : IntMap.ptrie A) :=
  IntMap.set' i v m.

Inductive atomT : Type :=
| NBool : forall (p : Prop), option (p \/ ~ p) -> atomT
| TBool : forall (b: bool) (p: Prop), p <-> Is_true b -> atomT.

Definition mkAtom (p:Prop) := NBool p None.
Definition mkAtomDec (p:Prop) (H:p\/ ~p) := NBool p (Some H).

Definition hold_prop (p:Prop) (k: kind) : eval_kind k :=
  match k with
  | IsProp => p
  | IsBool => false
  end.

Definition hold_bool (b:bool) (k: kind) : eval_kind k :=
  match k with
  | IsProp => False
  | IsBool => b
  end.

Definition eval_prop (m: IntMap.ptrie atomT) (k:kind) (i:int)  : eval_kind k :=
  match IntMap.get' i m with
  | None => BForm.eval_FF k
  | Some v => match v with
              | NBool p _ => hold_prop p k
              | TBool b p _ => match k with
                               | IsBool => b
                               | IsProp => p
                               end
              end
  end.

Definition has_bool (m:IntMap.ptrie atomT) (i:int) : bool :=
  match IntMap.get' i m with
  | None => false
  | Some v => match v with
              | NBool _ _ => false
              | TBool _ _ _ => true
              end
  end.

Lemma has_bool_correct : forall am i,
  has_bool am i = true -> eval_prop am IsProp i <-> Is_true (eval_prop am IsBool i).
Proof.
  unfold has_bool, eval_prop.
  intros.
  destruct (IntMap.get' i am).
  - destruct a ; try congruence.
  - simpl. tauto.
Qed.

Definition eval_is_dec (m: IntMap.ptrie atomT) (i:int)  :=
  match IntMap.get' i m with
  | None => false
  | Some v => match v with
              | NBool _ o =>
                match o with
                | None => false
                | Some _ => true
                end
              | TBool _ _ _ => true
              end
  end.

Lemma is_dec_correct : forall m i, eval_is_dec m i = true -> eval_prop m IsProp i  \/ ~ eval_prop m IsProp i .
Proof.
  unfold eval_is_dec, eval_prop.
  intros. destruct (IntMap.get' i m);[| tauto].
  destruct a.
  - destruct o ; try congruence.
    apply o.
  - rewrite i0.
    destruct b; simpl; tauto.
Qed.


Register HCons.mk as cdcl.HCons.mk.

Register AND as cdcl.op.AND.
Register OR as cdcl.op.OR.
Register IMPL as cdcl.op.IMPL.

Register Is_true as cdcl.Is_true.
Register iff_refl as cdcl.iff_refl.

(** Propositional formulae *)
Register LForm as cdcl.Formula.type.
Register TT as cdcl.Formula.TT.
Register FF as cdcl.Formula.FF.
Register LAT as cdcl.Formula.AT.
Register LOP as cdcl.Formula.OP.

(** Boolean formulae *)
Import BForm.
Register IsProp as cdcl.kind.IsProp.
Register IsBool as cdcl.kind.IsBool.
Register BForm as cdcl.BForm.type.
Register BTT as cdcl.BForm.BTT.
Register BFF as cdcl.BForm.BFF.
Register BAT as cdcl.BForm.BAT.
Register BOP as cdcl.BForm.BOP.
Register BIT as cdcl.BForm.BIT.

Register eval_hformula as cdcl.eval_hformula.
Register eval_hbformula as cdcl.eval_hbformula.
Register eval_formula as cdcl.eval_formula.
Register eval_prop as cdcl.eval_prop.
Register eval_is_dec as cdcl.eval_is_dec.

Register DecP1 as cdcl.DecP1.
Register decP1 as cdcl.decP1.
Register DecP2 as cdcl.DecP2.
Register decP2 as cdcl.decP2.

Register Reflect.Rbool1    as cdcl.Rbool1.type.
Register Reflect.p1        as cdcl.Rbool1.p1.
Register Reflect.p1_prf    as cdcl.Rbool1.p1_prf.
Register Reflect.Rbool2    as cdcl.Rbool2.type.
Register Reflect.p2        as cdcl.Rbool2.p2.
Register Reflect.p2_prf    as cdcl.Rbool2.p2_prf.

Register Reflect.RProp1    as cdcl.RProp1.type.
Register Reflect.b1        as cdcl.RProp1.b1.
Register Reflect.b1_prf    as cdcl.RProp1.b1_prf.
Register Reflect.RProp2    as cdcl.RProp2.type.
Register Reflect.b2        as cdcl.RProp2.b2.
Register Reflect.b2_prf    as cdcl.RProp2.b2_prf.

Register TheoryPropagation.NegBinRel as cdcl.NegBinRel.type.
Register TheoryPropagation.neg_bin_rel_clause as cdcl.neg_bin_rel_clause.
Register TheoryPropagation.neg_bin_rel_correct as cdcl.neg_bin_rel_correct.

Register atomT      as cdcl.atomT.type.
Register mkAtom     as cdcl.mkAtom.
Register mkAtomDec  as cdcl.mkAtomDec.
Register TBool      as cdcl.atomT.TBool.

Register empty as cdcl.IntMap.empty.
Register set   as cdcl.IntMap.add.

Definition empty_thy_prover  (hm:hmap ) (l:list literal) : option (hmap  * list (literal)) := None.

Definition empty_thy  (is_dec: int -> bool) (eA: int -> Prop) : Thy is_dec eA.
  apply mkThy  with (thy_prover := empty_thy_prover).
  - unfold empty_thy_prover.
    congruence.
Qed.

Definition hlform (hf : HFormula) :=
  nform lform hf.


Definition hcons_bprover (m : IntMap.ptrie atomT) (thy:Thy (eval_is_dec m) (eval_prop m IsProp)) (n:nat) (f: BForm.HBForm) :=
    hcons_prover (eval_is_dec m) (eval_prop m IsProp) thy n (hlform (BForm.to_hformula (has_bool m) f)).

Lemma eval_hformula_hlform : forall am f,
    eval_hformula (eval_prop am IsProp) (hlform f) <->
    eval_hformula (eval_prop am IsProp) f.
Proof.
  intros.
  apply eval_nform; auto.
  exact (fun _ => true). (* bizarre *)
  intro.
  rewrite <- eval_formula_lform.
  tauto.
  exact (fun _ => true). (* bizarre2 *)
Qed.

Lemma hcons_bprover_correct : forall n (f:BForm.HBForm) am,
    hcons_bprover am (empty_thy (eval_is_dec am) (eval_prop am IsProp)) n f = true ->
    BForm.eval_hbformula  (eval_prop am)  f.
Proof.
  intros n f am.
  intros.
  apply BForm.to_hformula_correct with (has_bool := has_bool am).
  - apply has_bool_correct.
  - unfold hcons_bprover in H.
    apply hcons_prover_correct in H.
    rewrite eval_hformula_hlform in H.
    auto.
    apply is_dec_correct.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
