(** Copyright 2020  Alix Trieu <alix.trieu@ens-rennes.fr>
  * Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> adapted from functor to record
*)

Require Import Lia.
Require Import Cdcl.Coqlib.

Definition le_o (o : option nat) (n:nat) :=
  match o with
  | None => True
  | Some n' => (n' <= n)%nat
  end.

Lemma le_o_dec :
  forall o n,
    le_o o n \/ ~ le_o o n.
Proof.
  destruct o; simpl.
  - intros. destruct (le_dec n n0); auto.
  - tauto.
Qed.

Module Keys_Base.
  Class Key (t: Type) :  Type := mk
  {
    zero: t;
    eqb: t -> t -> bool;
    testbit: t -> nat -> bool;
    interp: t -> t;
    land: t -> t -> t;
    lxor: t -> t -> t;
    lopp: t -> t;
    ltb: t -> t -> bool;
    (** specs *)
    digits : option nat;
    is_mask := (fun (m: t) (n: nat) => forall p, testbit m p = true <-> n = p);
    testbit_M : forall k n, le_o digits n -> testbit k n = false;
    zero_spec: forall n, testbit zero n = false;
    eqb_spec : forall k1 k2, eqb k1 k2 = true <-> k1 = k2;
    testbit_spec: forall k1 k2, (forall n, testbit k1 n = testbit k2 n) -> k1 = k2;
    interp_spec: forall m n, is_mask m n -> forall p, testbit (interp m) p = true <-> (p < n)%nat;
    land_spec: forall n k1 k2, testbit (land k1 k2) n = testbit k1 n && testbit k2 n;
    lxor_spec: forall n k1 k2, testbit (lxor k1 k2) n = xorb (testbit k1 n) (testbit k2 n);
    lopp_spec_low: forall k m, (forall p, (p < m)%nat -> testbit k p = false) -> testbit k m = true -> forall p, (p < m)%nat -> testbit (lopp k) p = false;
    lopp_spec_eq: forall k m, (forall p, (p < m)%nat -> testbit k p = false) -> testbit k m = true -> testbit (lopp k) m = true;
    lopp_spec_high: forall k m, (forall p, (p < m)%nat -> testbit k p = false) -> testbit k m = true ->
                                forall p, (p > m)%nat -> ~ le_o digits p -> testbit (lopp k) p = negb (testbit k p);
    ltb_spec: forall m1 n1 m2 n2, is_mask m1 n1 -> is_mask m2 n2 -> (ltb m1 m2 = true <-> (n1 < n2)%nat);
    LPO : forall (k:t), k <> zero -> exists p, testbit k p = true
  }.
End Keys_Base.


Module PTrie.
  Import Keys_Base.

  Section S.
  Context {key: Type}.
  Context {K: Key key}.

  Section K_More.

    Definition zerobit (k m: key) := eqb (land k m) zero.
    Definition mask (k m: key) := land k (interp m).
    Definition lowest_bit (x: key) := land x (lopp x).
    Definition branching_bit (p p': key) := lowest_bit (lxor p p').
    Definition match_prefix (k p m: key) := eqb (mask k m) p.


    Lemma eqb_false : forall (k1 k2:key), eqb k1 k2 = false <-> k1 <> k2.
    Proof.
      repeat intro.
      unfold not.
      rewrite <- eqb_spec.
      destruct (eqb k1 k2) ; intuition congruence.
    Qed.

    Lemma eqb_dec : forall (k1 k2:key), {k1 = k2} + {k1 <> k2}.
    Proof.
      intros. destruct (eqb k1 k2) eqn:EQ.
    - left. rewrite eqb_spec in EQ. auto.
    - right. apply eqb_false ; auto.
  Qed.


  Lemma eqb_eq : forall (k1 k2:key) r,
      (k1 = k2 -> r = true) ->
      (k1 <> k2 -> r = false) ->
      (eqb k1 k2) = r.
  Proof.
    intros.
    destruct (eqb k1 k2) eqn:EQ.
    - symmetry; apply H.
      rewrite eqb_spec in EQ; auto.
    - rewrite eqb_false in EQ. apply H0 in EQ; congruence.
  Qed.

  Theorem zerobit_spec:
    forall k m n,
      is_mask m n ->
      zerobit k m = negb (testbit k n).
  Proof.
    intros k m n P. unfold zerobit; simpl.
    apply eqb_eq; intro e.
    - assert (testbit m n = true) by (apply P; auto).
      assert (testbit (land k m) n = false).
      { rewrite e. rewrite zero_spec; simpl; auto. }
      rewrite land_spec in H0. rewrite H in H0.
      destruct (testbit k n); simpl; auto.
    - assert (forall p, p <> n -> testbit m p = false).
      + intros. case_eq (testbit m p); intros; auto.
        apply P in H0. elim H; auto.
      + assert (forall p, p <> n -> testbit (land k m) p = false).
        * intros; rewrite land_spec.
          rewrite H; auto. destruct (Keys_Base.testbit k p); simpl; auto.
        * case_eq (testbit k n); intros.
          { assert (land k m = m).
            - apply testbit_spec; intros.
              rewrite land_spec.
              destruct (Nat.eq_dec n0 n).
              + subst n0. rewrite (proj2 (P n)); auto.
                rewrite H1; auto.
              + rewrite H; auto. destruct (Keys_Base.testbit k n0); simpl; auto.
            - simpl; auto. }
          { elim e. apply testbit_spec.
            intros; rewrite zero_spec.
            destruct (Nat.eq_dec n0 n).
            - subst n0. rewrite land_spec; rewrite H1; simpl; auto.
            - rewrite H0; auto. }
  Qed.

  Theorem mask_spec:
    forall k m n,
      is_mask m n ->
      (forall p, (p < n)%nat -> testbit (mask k m) p = testbit k p) /\
      (forall p, (p >= n)%nat -> testbit (mask k m) p = false).
  Proof.
    intros k m n P. unfold mask; simpl. split.
    - intros. rewrite land_spec.
      assert (testbit (interp m) p = true).
      + eapply interp_spec. exact P. exact H.
      + rewrite H0. destruct (Keys_Base.testbit k p); auto.
    - intros. rewrite land_spec.
      assert (testbit (interp m) p = false).
      + case_eq (testbit (interp m) p); intros; auto.
        eapply interp_spec in H0; simpl in H0; eauto; try lia.
      + rewrite H0. destruct (Keys_Base.testbit k p); auto.
  Qed.

  Theorem mask_spec':
    forall k m n,
      is_mask m n ->
      mask (mask k m) m = mask k m.
  Proof.
    intros. generalize (mask_spec k m n H). intros [HA HB].
    generalize (mask_spec (mask k m) m n H). intros [HC HD].
    eapply testbit_spec; intros.
    unfold testbit in *. destruct (lt_dec n0 n).
    - apply HC; auto.
    - rewrite HB; try lia; auto.
      apply HD; lia.
  Qed.

  Fixpoint find_lowest (n: nat) (k: key) (p: nat) :=
    match p with
    | O => n
    | S q => if testbit k (n - p)%nat then (n - p)%nat else find_lowest n k q
    end.

  Lemma find_lowest_spec:
    forall n p k,
      testbit k n = true ->
      (forall q, ((n - p)%nat <= q < find_lowest n k p)%nat -> testbit k q = false) /\ testbit k (find_lowest n k p) = true.
  Proof.
    induction p; intros.
    - simpl. split; auto. intros; lia.
    - exploit IHp; eauto. intros [HA HB].
      simpl. case_eq (testbit k (n - S p)%nat); intros.
      + split; intros; auto; lia.
      + split; intros; auto.
        destruct (Nat.eq_dec (n - S p)%nat q).
        * subst q. auto.
        * apply HA; lia.
  Qed.

  Theorem lowest_bit_spec:
    forall k, k <> zero ->
         exists n, is_mask (lowest_bit k) n /\ (forall p, (p < n)%nat -> testbit k p = false).
  Proof.
    intros. unfold lowest_bit.
    destruct (Keys_Base.LPO k H) as [n H0].
    { generalize (find_lowest_spec n n k H0). intros [HA HB].
      assert (HC: forall p, (p < find_lowest n k n)%nat -> testbit k p = false) by (intros; apply HA; lia).
      generalize (lopp_spec_low _ _ HC HB). intros HD.
      generalize (lopp_spec_eq _ _ HC HB). intros HE.
      generalize (lopp_spec_high _ _ HC HB). intros HF.
      exists (find_lowest n k n). intros; split; intros.
      { intros; split; intros.
        - rewrite land_spec in H1. apply andb_true_iff in H1; destruct H1.
          unfold lopp in H2. destruct (lt_dec p (find_lowest n k n)).
          + rewrite HD in H2; auto. congruence.
          + destruct (gt_dec p (find_lowest n k n)).
            destruct (le_o_dec digits p).
            rewrite testbit_M in H1; auto. congruence.
            * rewrite HF in H2; auto. rewrite H1 in H2. simpl in H2. congruence.
            * lia.
        - subst. rewrite land_spec. apply andb_true_iff. split.
          + unfold testbit in HB. auto.
          + unfold lopp. auto. }
      { apply HC; auto. } }
  Qed.

  Lemma lxor_eq_zero:
    forall k1 k2,
      lxor k1 k2 = zero -> k1 = k2.
  Proof.
    intros; eapply testbit_spec; intros.
    assert (testbit (lxor k1 k2) n = false) by (rewrite H; rewrite zero_spec; auto).
    rewrite lxor_spec in H0. apply xorb_eq; auto.
  Qed.

  Theorem branching_bit_spec:
    forall k1 k2,
      k1 <> k2 ->
      exists n, is_mask (branching_bit k1 k2) n /\
           (forall p, (p < n)%nat -> testbit k1 p = testbit k2 p) /\
           (testbit k1 n <> testbit k2 n).
  Proof.
    intros. unfold branching_bit.
    destruct (eqb_dec (lxor k1 k2) zero).
    { elim H; apply lxor_eq_zero; auto. }
    { generalize (lowest_bit_spec _ n). intros [r [HA HB]].
      exists r; split; auto.
      split.
      - intros. apply xorb_eq.
        rewrite <- lxor_spec. apply HB; auto.
      - assert (testbit (lowest_bit (lxor k1 k2)) r = true) by (apply HA; auto).
        unfold lowest_bit in H0. rewrite land_spec in H0.
        rewrite lxor_spec in H0. red; intros.
        rewrite H1 in H0. rewrite xorb_nilpotent in H0.
        simpl in H0. inv H0. }
  Qed.

  Theorem branching_bit_sym:
    forall k1 k2,
      branching_bit k1 k2 = branching_bit k2 k1.
  Proof.
    unfold branching_bit; intros; f_equal.
    eapply testbit_spec; intros.
    rewrite ! lxor_spec. eapply xorb_comm.
  Qed.

  Theorem match_prefix_spec:
    forall k p m n,
      is_mask m n ->
      mask p m = p ->
      (match_prefix k p m = true <-> forall q, (q < n)%nat -> testbit k q = testbit p q).
  Proof.
    intros; unfold match_prefix; split; intros.
    - rewrite eqb_spec in H1.
      rewrite <- H1.
      symmetry.
      apply (proj1 (mask_spec _ _ _ H)); auto.
    - apply eqb_eq; auto.
      intro n0.
      elim n0. rewrite <- H0.
      apply testbit_spec; intros.
      generalize (mask_spec k _ _ H); intros [HA HB].
      generalize (mask_spec p _ _ H); intros [HC HD].
      destruct (lt_dec n1 n).
      + rewrite HA; auto; rewrite HC; auto.
      + rewrite HB; try lia; rewrite HD; try lia; auto.
  Qed.

  Theorem match_prefix_spec':
    forall k p m n,
      is_mask m n ->
      mask p m = p ->
      (match_prefix k p m = false <-> k <> p /\ exists n', (n' < n)%nat /\ testbit (branching_bit k p) n' = true).
  Proof.
    intros; unfold match_prefix; split; intros.
    - rewrite eqb_false in H1.
      rename H1 into n0.
      split.
      + red; intros. subst k. apply n0; auto.
      + assert (k <> p) by (red; intros; subst k; apply n0; auto).
        generalize (branching_bit_spec k p H1). intros [n' [HA [HB HC]]].
        exists n'; split; auto.
        * destruct (lt_dec n' n); auto.
          generalize (proj2 (match_prefix_spec k _ _ _ H H0)). intros.
          assert (match_prefix k p m = true).
          { apply H2. intros; apply HB; lia. }
          unfold match_prefix in H3. unfold proj_sumbool in H3.
          rewrite eqb_spec in H3; congruence.
        * apply HA; auto.
    - destruct H1 as [H1 [n' [H2 H3]]].
      rewrite eqb_false.
      intro.
      generalize (branching_bit_spec _ _ H1). intros [n'' [HA [HB HC]]].
      assert (n'' = n') by (apply HA; auto). subst n''.
      elim HC. eapply (match_prefix_spec k p m n H H0); auto.
      unfold match_prefix.
      apply eqb_eq; auto. congruence.
  Qed.

  End K_More.

    Inductive ptrie (A: Type): Type :=
    | Empty: ptrie A
    | Leaf (k: key) (v: A): ptrie A
    | Branch (prefix: key) (brbit: key) (l r: ptrie A): ptrie A.

    Arguments Empty {A}.
    Arguments Leaf [A] _ _.
    Arguments Branch [A] _ _ _ _.

    Inductive wf {A: Type} : option (key * key * nat * bool) -> ptrie A -> Prop :=
    | wf_Empty:
        forall opt,
          wf opt Empty
    | wf_Leaf_Some:
        forall p brb brb' lr k v
          (Hlr: zerobit k brb = lr)
          (Hmask: mask p brb = p)
          (Hbrb: is_mask brb brb')
          (Hlength: forall n, (n >= brb')%nat -> testbit p n = false)
          (Hprefix: forall n, (n < brb')%nat -> testbit p n = testbit k n),
          wf (Some (p, brb, brb', lr)) (Leaf k v)
    | wf_Leaf_None:
        forall k v,
          wf None (Leaf k v)
    | wf_Branch_Some:
        forall p brb brb' lr prefix brbit brbit' l r
          (Hl: l <> Empty)
          (Hr: r <> Empty)
          (Hlr: zerobit prefix brb = lr)
          (Hmask: mask p brb = p)
          (Hmask': mask prefix brbit = prefix)
          (Hbrb: is_mask brb brb')
          (Hincr: (brb' < brbit')%nat)
          (Hbrbit': is_mask brbit brbit')
          (Hlength: forall n, (n >= brbit')%nat -> testbit prefix n = false)
          (Hlength': forall n, (n >= brb')%nat -> testbit p n = false)
          (Hprefix: forall n, (n < brb')%nat -> testbit p n = testbit prefix n),
          wf (Some (prefix, brbit, brbit', true)) l ->
          wf (Some (prefix, brbit, brbit', false)) r ->
          wf (Some (p, brb, brb', lr)) (Branch prefix brbit l r)
    | wf_Branch_None:
        forall prefix brbit brbit' l r
          (Hl: l <> Empty)
          (Hr: r <> Empty)
          (Hbrbit': is_mask brbit brbit')
          (Hprefix: forall n, (n >= brbit')%nat -> testbit prefix n = false),
          wf (Some (prefix, brbit, brbit', true)) l ->
          wf (Some (prefix, brbit, brbit', false)) r ->
          wf None (Branch prefix brbit l r).

    Arguments wf [A] _ _.

    Lemma wf_Some_None:
      forall A p m n lr (pt: ptrie A),
        wf (Some (p, m, n, lr)) pt ->
        wf None pt.
    Proof.
      destruct pt; intros; inv H; econstructor; eauto.
    Qed.

    Lemma wf_weaken:
      forall {A:Type} (pt: ptrie A) p brb brb' lr,
        wf (Some (p, brb, brb', lr)) pt ->
        forall n n',
          (forall q, testbit n q = true <-> n' = q) ->
          (n' < brb')%nat ->
          wf (Some (mask p n, n, n', zerobit p n)) pt.
    Proof.
      intros A t; induction t; intros.
      - constructor.
      - inv H; constructor; auto.
        + symmetry. rewrite ! (zerobit_spec _ _ _ H0).
          f_equal. auto.
        + eapply mask_spec'. eauto.
        + intros. eapply mask_spec; eauto.
        + intros. rewrite <- Hprefix; try lia.
          eapply mask_spec; eauto.
      - inv H; econstructor; trivial.
        + symmetry. rewrite ! (zerobit_spec _ _ _ H0).
          f_equal. auto.
        + eapply mask_spec'. eauto.
        + eapply lt_trans; eauto.
        + assumption.
        + assumption.
        + intros; eapply mask_spec; eauto.
        + intros. rewrite <- Hprefix; try lia.
          eapply mask_spec; eauto.
        + assumption.
        + assumption.
    Qed.

    Lemma wf_Some_Branch:
      forall {A: Type} {p m n lr p' m'} {t1 t2: ptrie A},
        wf (Some (p, m, n, lr)) (Branch p' m' t1 t2) ->
        wf (Some (p, m, n, lr)) t1 /\ wf (Some (p, m, n, lr)) t2.
    Proof.
      intros; inv H; split.
      - assert (p = mask p' m).
        +
          eapply testbit_spec; intros.
          generalize (mask_spec p' _ _ Hbrb); intros [HA HB].
          destruct (lt_dec n0 n).
          * rewrite HA; eauto.
          * rewrite HB; try lia.
            eapply Hlength'. lia.
        + rewrite H.
          apply wf_weaken with (1:=H2); auto.
      - assert (p = mask p' m).
        + eapply testbit_spec; intros.
          generalize (mask_spec p' _ _ Hbrb); intros [HA HB].
          destruct (lt_dec n0 n).
          * rewrite HA; eauto.
          * rewrite HB; try lia.
            eapply Hlength'. lia.
        + rewrite H. apply wf_weaken with (1:= H9); auto.
    Qed.

    Definition empty (A: Type): ptrie A := Empty.

    (* Slow if key is not there *)
    Fixpoint get' {A: Type} (i: key) (t: ptrie A) :=
      match t with
      | Empty => None
      | Leaf k v => if eqb i k then Some v else None
      | Branch prefix brbit l r =>
        if zerobit i brbit then
          get' i l else
          get' i r
      end.

    Fixpoint mem' {A: Type} (i: key) (t: ptrie A) :=
      match t with
      | Empty => false
      | Leaf k v => eqb i k
      | Branch prefix brbit l r =>
        if zerobit i brbit then
          mem' i l else
          mem' i r
      end.



    Definition join {A: Type} (k1: key) (t1: ptrie A) (k2: key) (t2: ptrie A) :=
      let m := branching_bit k1 k2 in
      if zerobit k1 m
      then Branch (mask k1 m) m t1 t2
      else Branch (mask k1 m) m t2 t1.

    Lemma wf_join_Leaf:
      forall A opt k1 k2 (v1 v2: A),
        let m := branching_bit k1 k2 in
        k1 <> k2 ->
        wf opt (Leaf k1 v1) -> wf opt (Leaf k2 v2) ->
        wf opt (join k1 (Leaf k1 v1) k2 (Leaf k2 v2)).
    Proof. 
      intros; inv H0; inv H1.
      - unfold join. generalize (branching_bit_spec _ _ H). intros [n [HA [HB HC]]].
        case_eq (zerobit k1 (branching_bit k1 k2)); intros.
        + econstructor.
          * discriminate.
          * discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. fold m. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
                elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * eauto.
          * eapply mask_spec'; auto. exact HA.
          * auto.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * auto.
          * intros. eapply mask_spec. exact HA. auto.
          * auto.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * econstructor; eauto.
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
          * econstructor; eauto.
            { erewrite zerobit_spec; eauto.
              eapply negb_false_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_true_iff in H0. destruct (testbit k2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
        + econstructor.
          * discriminate.
          * discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. fold m. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
                elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * eauto.
          * eapply mask_spec'; auto. exact HA.
          * auto.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * auto.
          * intros. eapply mask_spec. exact HA. auto.
          * auto.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * econstructor; eauto.
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_false_iff in H0. destruct (testbit k2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
          * econstructor; eauto.
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
      - unfold join. generalize (branching_bit_spec _ _ H). intros [n [HA [HB HC]]].
        case_eq (zerobit k1 (branching_bit k1 k2)); intros.
        + econstructor.
          * discriminate.
          * discriminate.
          * eauto.
          * intros. eapply mask_spec. exact HA. auto.
          * econstructor; eauto.
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
          * econstructor; eauto.
            { erewrite zerobit_spec; eauto.
              eapply negb_false_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_true_iff in H0. destruct (testbit k2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
        + econstructor.
          * discriminate.
          * discriminate.
          * eauto.
          * intros. eapply mask_spec. exact HA. auto.
          * econstructor; eauto.
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_false_iff in H0. destruct (testbit k2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
          * econstructor; eauto.
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
    Qed.

    Lemma wf_join_Branch:
      forall A opt k1 k2 v1 m2 (t1 t2: ptrie A),
        let m := branching_bit k1 k2 in
        match_prefix k1 k2 m2 = false ->
        wf opt (Leaf k1 v1) -> wf opt (Branch k2 m2 t1 t2) ->
        wf opt (join k1 (Leaf k1 v1) k2 (Branch k2 m2 t1 t2)).
    Proof.
      intros; inv H0; inv H1.
      - rename H into HO. generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') HO).
        intros [H [n' [HP  HQ]]].
        unfold join. generalize (branching_bit_spec _ _ H). intros [n [HA [HB HC]]].
        apply HA in HQ. subst n'.
        case_eq (zerobit k1 (branching_bit k1 k2)); intros.
        + econstructor.
          * discriminate.
          * discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. fold m. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_true_iff in H0. rewrite H0.
                eapply mask_spec; eauto.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * eauto.
          * eapply mask_spec'; auto. exact HA.
          * auto.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * auto.
          * intros. eapply mask_spec. exact HA. auto.
          * auto.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * econstructor; eauto.
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_false_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_true_iff in H0. destruct (testbit k2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { destruct (lt_dec n brbit'). exact l.
              rewrite (zerobit_spec _ _ _ HA) in H0. apply negb_true_iff in H0.
              assert (testbit k2 n = false) by (eapply Hlength0; lia). congruence. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
        + econstructor.
          * discriminate.
          * discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. fold m. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_false_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
                elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * eauto.
          * eapply mask_spec'; auto. exact HA.
          * auto.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_false_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * auto.
          * intros. eapply mask_spec. exact HA. auto.
          * auto.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_false_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit k1 brb'); destruct (testbit k2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_false_iff in H0. destruct (testbit k2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { exact HP. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
          * econstructor; eauto.
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
      - rename H into HO. assert (Hmask': mask k2 m2 = k2).
        { inv H4; try congruence; auto. }
        generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') HO).
        intros [H [n' [HP  HQ]]].
        unfold join. generalize (branching_bit_spec _ _ H). intros [n [HA [HB HC]]].
        apply HA in HQ. subst n'.
        case_eq (zerobit k1 (branching_bit k1 k2)); intros.
        + econstructor.
          * discriminate.
          * discriminate.
          * eauto.
          * intros. eapply mask_spec. exact HA. auto.
          * econstructor; eauto.
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_false_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_true_iff in H0. destruct (testbit k2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { exact HP. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
        + econstructor.
          * discriminate.
          * discriminate.
          * eauto.
          * intros. eapply mask_spec. exact HA. auto.
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_false_iff in H0. destruct (testbit k2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { exact HP. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
          * econstructor; eauto.
            { eapply mask_spec'; auto. exact HA. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
    Qed.
  
    Fixpoint set' {A: Type} (i: key) (x: A) (t: ptrie A) :=
      match t with
      | Empty => Leaf i x
      | Leaf j v => if  eqb i j then Leaf i x else join i (Leaf i x) j (Leaf j v)
      | Branch prefix brbit l r =>
        if match_prefix i prefix brbit then
          if zerobit i brbit then
            Branch prefix brbit (set' i x l) r
          else
            Branch prefix brbit l (set' i x r)
        else join i (Leaf i x) prefix (Branch prefix brbit l r)
      end.

    Lemma set'_not_empty:
      forall A k x (pt: ptrie A),
        set' k x pt <> Empty.
    Proof.
      intros; induction pt; simpl; try congruence.
      - destruct (eqb k k0)eqn:EQ; try congruence.
        unfold join; simpl. destruct (zerobit k (branching_bit k k0)); discriminate.
      - destruct (match_prefix k prefix brbit).
        + destruct (zerobit k brbit); discriminate.
        + unfold join; simpl. destruct (zerobit k (branching_bit k prefix)); discriminate.
    Qed.
    
    Lemma wf_set':
      forall A opt k x (t: ptrie A),
        wf opt t ->
        wf opt (Leaf k x) ->
        wf opt (set' k x t).
    Proof.
      induction 1; intros.
      - simpl; auto.
      - simpl. destruct (eqb k k0) eqn:EQ; auto.
        rewrite eqb_false in EQ.
        eapply wf_join_Leaf; eauto; try constructor; auto.
      - simpl. destruct (eqb k k0) eqn:EQ; auto.
        rewrite eqb_false in EQ.
        eapply wf_join_Leaf; eauto; try constructor; auto.
      - simpl. case_eq (match_prefix k prefix brbit); intros.
        + case_eq (zerobit k brbit); intros; econstructor; trivial; try eassumption.
          * eapply set'_not_empty; eauto.
          * apply IHwf1. constructor; auto. intros; symmetry.
            eapply match_prefix_spec; eauto.
          * eapply set'_not_empty; eauto.
          * apply IHwf2. constructor; auto. intros; symmetry.
            eapply match_prefix_spec; eauto.
        + generalize H2. intros HX.
          eapply (match_prefix_spec') in H2; eauto. destruct H2 as [HO [n [HA HB]]].
          eapply wf_join_Branch; eauto.
          econstructor; trivial; try eassumption.
      - simpl. case_eq (match_prefix k prefix brbit); intros.
        + case_eq (zerobit k brbit); intros; econstructor; trivial; try eassumption.
          * eapply set'_not_empty; eauto.
          * apply IHwf1. constructor; auto.
            inv H; congruence.
            intros; symmetry.
            eapply match_prefix_spec; eauto. inv H; congruence.
          * eapply set'_not_empty; eauto.
          * apply IHwf2. constructor; auto.
            inv H; congruence.
            intros; symmetry.
            eapply match_prefix_spec; eauto. inv H; congruence.
        + generalize H2; intros HX.
          eapply (match_prefix_spec') in H2; eauto. destruct H2 as [n [HA HB]].
          eapply wf_join_Branch; eauto; try econstructor; trivial; try eassumption.
          inv H; congruence.
    Qed.

    Definition branch {A: Type} (prefix m: key) (t1 t2: ptrie A) :=
      match t1 with
      | Empty => t2
      | _ => match t2 with
            | Empty => t1
            | _ => Branch prefix m t1 t2
            end
      end.

    Lemma wf_branch:
      forall A prefix brb brb' lr p m m' (t1 t2: ptrie A)
        (Hlr: zerobit p brb = lr)
        (Hincr: (brb' < m')%nat)
        (Hbrb: is_mask brb brb')
        (Hlength: forall n, (n >= brb')%nat -> testbit prefix n = false)
        (Hprefix: forall n, (n < brb')%nat -> testbit prefix n = testbit p n),
        (forall n, (n >= m')%nat -> testbit p n = false) ->
        wf (Some (p, m, m', true)) t1 ->
        wf (Some (p, m, m', false)) t2 ->
        wf (Some (prefix, brb, brb', lr)) (branch p m t1 t2).
    Proof.
      unfold branch; intros.
      inv H0; try constructor; auto.
      - inv H1; try econstructor; trivial.
        + erewrite ! zerobit_spec; try eassumption.
          f_equal; symmetry; apply Hprefix0; auto.
        + generalize (mask_spec prefix _ _ Hbrb). intros [HA HB].
          eapply testbit_spec; intros.
          destruct (lt_dec n brb').
          * apply HA; auto.
          * rewrite HB; try lia; auto. rewrite Hlength; auto; lia.
        + intros. rewrite Hprefix; auto.
          apply Hprefix0. lia.
        + erewrite ! zerobit_spec; try eassumption.
          f_equal; symmetry; apply Hprefix0; auto.
        + generalize (mask_spec prefix _ _ Hbrb). intros [HA HB].
          eapply testbit_spec; intros.
          destruct (lt_dec n brb').
          * apply HA; auto.
          * rewrite HB; try lia; auto. rewrite Hlength; auto; lia.
        + instantiate (1 := brbit'); lia.
        + assumption.
        + assumption.
        + intros. rewrite Hprefix; try lia. rewrite Hprefix0; auto; lia.
        + assumption.
        + assumption.
      - inv H1; try econstructor; trivial.
        + erewrite ! zerobit_spec; try eassumption.
          f_equal; symmetry; apply Hprefix0; auto.
        + generalize (mask_spec prefix _ _ Hbrb). intros [HA HB].
          eapply testbit_spec; intros.
          destruct (lt_dec n brb').
          * apply HA; auto.
          * rewrite HB; try lia; auto. rewrite Hlength; auto; lia.
        + intros. rewrite Hprefix; try lia. rewrite Hprefix0; auto; lia.
        + congruence.
        + congruence.
        + generalize (mask_spec prefix _ _ Hbrb). intros [HA HB].
          eapply testbit_spec; intros.
          destruct (lt_dec n brb').
          * apply HA; auto.
          * rewrite HB; try lia; auto. rewrite Hlength; auto; lia.
        + eassumption.
        + auto.
        + auto.
        + constructor; auto.
        + constructor; auto.
        + congruence.
        + congruence.
        + generalize (mask_spec prefix _ _ Hbrb). intros [HA HB].
          eapply testbit_spec; intros.
          destruct (lt_dec n brb').
          * apply HA; auto.
          * rewrite HB; try lia; auto. rewrite Hlength; auto; lia.
        + eassumption.
        + assumption.
        + assumption.
        + constructor; auto.
        + econstructor; trivial; try eassumption.
      - inv H1; try econstructor; trivial.
        + erewrite ! zerobit_spec; try eassumption.
          f_equal; symmetry; apply Hprefix0; auto.
        + generalize (mask_spec prefix _ _ Hbrb). intros [HA HB].
          eapply testbit_spec; intros.
          destruct (lt_dec n brb').
          * apply HA; auto.
          * rewrite HB; try lia; auto. rewrite Hlength; auto; lia.
        + instantiate (1 := brbit'). lia.
        + assumption.
        + assumption.
        + intros. rewrite Hprefix; try lia. rewrite Hprefix0; auto; lia.
        + congruence.
        + congruence.
        + congruence.
        + congruence.
        + generalize (mask_spec prefix _ _ Hbrb). intros [HA HB].
          eapply testbit_spec; intros.
          destruct (lt_dec n brb').
          * apply HA; auto.
          * rewrite HB; try lia; auto. rewrite Hlength; auto; lia.
        + eassumption.
        + assumption.
        + assumption.
        + econstructor; trivial; eassumption.
        + econstructor; auto.
        + congruence.
        + congruence.
        + generalize (mask_spec prefix _ _ Hbrb). intros [HA HB].
          eapply testbit_spec; intros.
          destruct (lt_dec n brb').
          * apply HA; auto.
          * rewrite HB; try lia; auto. rewrite Hlength; auto; lia.
        + eassumption.
        + assumption.
        + assumption.
        + econstructor; trivial; try apply H7; try apply H8; try eassumption.
        + econstructor; trivial; try eapply H6; try eapply H9; try eassumption.
    Qed.
    
    Lemma wf_branch':
      forall A p m m' (t1 t2: ptrie A),
        (forall n, (n >= m')%nat -> testbit p n = false) ->
        wf (Some (p, m, m', true)) t1 ->
        wf (Some (p, m, m', false)) t2 ->
        wf None (branch p m t1 t2).
    Proof.
      unfold branch; intros.
      inv H0; try constructor; auto.
      - inv H1; try econstructor; eauto.
      - inv H1; try econstructor; trivial; try congruence; try eassumption.
        + constructor; auto.
        + constructor; auto.
        + constructor; auto.
        + econstructor; trivial; try eapply H6; try eapply H7; try eassumption.
      - inv H1; try econstructor; trivial; try congruence; try eassumption.
        + econstructor; trivial; try eapply H7; try eapply H8; try eassumption.
        + econstructor; trivial.
        + econstructor; trivial; try eapply H7; try eapply H8; try eassumption.
        + econstructor; trivial; try eapply H6; try eapply H9; try eassumption.
    Qed.

    Fixpoint remove' {A: Type} (i: key) (t: ptrie A) :=
      match t with
      | Empty => Empty
      | Leaf k v => if eqb k i then Empty else t
      | Branch p m l r =>
        if match_prefix i p m then
          if zerobit i m then
            branch p m (remove' i l) r
          else
            branch p m l (remove' i r)
        else t
      end.

    Lemma wf_remove':
      forall A opt i (t: ptrie A),
        wf opt t ->
        wf opt (remove' i t).
    Proof.
      induction 1; intros.
      - constructor.
      - simpl; destruct (eqb k i) eqn:EQ; constructor; auto.
      - simpl; destruct (eqb k i); constructor; auto.
      - simpl. case_eq (match_prefix i prefix brbit); intros.
        + destruct (zerobit i brbit); eapply wf_branch; eauto.
        + econstructor; eauto.
      - simpl. case_eq (match_prefix i prefix brbit); intros.
        + destruct (zerobit i brbit); eapply wf_branch'; eauto.
        + econstructor; eauto.
    Qed.

    Lemma eqb_refl : forall i, eqb i i = true.
    Proof.
      intro.
      rewrite eqb_spec.
      reflexivity.
    Qed.

    Lemma gss':
      forall (A: Type) opt (i: key) (x: A) (m: ptrie A),
        wf opt m ->
        get' i (set' i x m) = Some x.
    Proof.
      induction 1; intros.
      - simpl. rewrite eqb_refl; congruence.
      - simpl. destruct (eqb i k) eqn:EQ; auto.
        + simpl. rewrite eqb_refl. congruence.
        + unfold join. rewrite eqb_false in EQ.
          generalize (branching_bit_spec _ _ EQ). intros [m' [HA HB]].
          case_eq (zerobit i (branching_bit i k)); intros; simpl; rewrite H; rewrite (eqb_refl); congruence.
      - simpl. destruct (eqb i k); auto.
        + simpl; rewrite eqb_refl; congruence.
        + unfold join.
          case_eq (zerobit i (branching_bit i k)); intros; simpl; rewrite H; rewrite (eqb_refl); congruence.
      - simpl. case_eq (match_prefix i prefix brbit); intros.
        + case_eq (zerobit i brbit); intros; simpl; rewrite H2; auto.
        + unfold join.
          case_eq (zerobit i (branching_bit i prefix)); intros; simpl; rewrite H2; rewrite (eqb_refl); congruence.
      - simpl. case_eq (match_prefix i prefix brbit); intros.
        + case_eq (zerobit i brbit); intros; simpl; rewrite H2; auto.
        + unfold join. eapply match_prefix_spec' in H1; auto.
          * destruct H1 as [HO [n [HA HB]]].
            case_eq (zerobit i (branching_bit i prefix)); intros; simpl; rewrite H1; rewrite (eqb_refl); congruence.
          * inv H; eauto; congruence.
          * inv H; eauto; congruence.
    Qed.
    
    Lemma get_not_same_prefix:
      forall A (t: ptrie A) p brb brb' lr,
        wf (Some (p, brb, brb', lr)) t ->
        forall k n, (n < brb')%nat ->
               testbit p n <> testbit k n ->
               get' k t = None.
    Proof.
      intros A t. induction t; intros.
      - reflexivity.
      - inv H; simpl. destruct (eqb k0 k)eqn:EQ; auto.
        rewrite eqb_spec in EQ.
        subst k0. elim H1. apply Hprefix; auto.
      - inv H; simpl. case_eq (zerobit k brbit); intros; auto.
        + eapply IHt1 with (n := n); eauto. lia.
        + eapply IHt2 with (n := n); eauto. lia.
    Qed.
    
    Lemma eq : forall (k1 k2:key), {k1 = k2} + {k1 <> k2}.
    Proof.
      apply eqb_dec.
    Qed.

    Lemma eqb_is_dec : forall k1 k2,
        eqb k1 k2 = proj_sumbool (eq k1 k2).
    Proof.
      intros.
      destruct (eq k1 k2); simpl.
      rewrite eqb_spec; auto.
      rewrite eqb_false.
      auto.
    Qed.

    Lemma gso':
      forall (A: Type) opt (i j: key) (x: A) (m: ptrie A),
        wf opt m ->
        i <> j -> get' i (set' j x m) = get' i m.
    Proof.
      induction 1; intros.
      - simpl. rewrite eqb_is_dec. destruct (eq i j); simpl ; congruence.
      - simpl. rewrite! eqb_is_dec. destruct (eq j k); simpl; auto.
        + simpl. rewrite eqb_is_dec. destruct (eq i k); destruct (eq i j); simpl ; congruence.
        + unfold join.
          case_eq (zerobit j (branching_bit j k)); intros; simpl; case_eq (zerobit i (branching_bit j k));
            intros; simpl; repeat rewrite eqb_is_dec ;
              destruct (eq i j); destruct (eq i k); simpl; try congruence.
          * subst i. generalize (branching_bit_spec j k n). intros [n' [HA [HB HC]]].
            elim HC. erewrite zerobit_spec in H0; eauto.
            erewrite zerobit_spec in H1; eauto.
            eapply negb_true_iff in H0. eapply negb_true_iff in H1. congruence.
          * subst i. generalize (branching_bit_spec  j k n). intros [n' [HA [HB HC]]].
            elim HC. erewrite zerobit_spec in H0; eauto.
            erewrite zerobit_spec in H1; eauto.
            eapply negb_false_iff in H0. eapply negb_false_iff in H1. congruence.
      - simpl.
        repeat rewrite eqb_is_dec.
        destruct (eq j k); simpl; auto.
        + simpl. rewrite eqb_is_dec.
          destruct (eq i k); destruct (eq i j); simpl; congruence.
        + unfold join.
          case_eq (zerobit j (branching_bit j k)); intros; simpl; case_eq (zerobit i (branching_bit j k));
            intros; simpl; rewrite eqb_is_dec ; destruct (eq i j); destruct (eq i k); simpl; try congruence.
          * subst i. generalize (branching_bit_spec j k n). intros [n' [HA [HB HC]]].
            elim HC. erewrite zerobit_spec in H0; eauto.
            erewrite zerobit_spec in H1; eauto.
            eapply negb_true_iff in H0. eapply negb_true_iff in H1. congruence.
          * subst i. generalize (branching_bit_spec  j k n). intros [n' [HA [HB HC]]].
            elim HC. erewrite zerobit_spec in H0; eauto.
            erewrite zerobit_spec in H1; eauto.
            eapply negb_false_iff in H0. eapply negb_false_iff in H1. congruence.
      - simpl. case_eq (match_prefix j prefix brbit); intros.
        + case_eq (zerobit j brbit); intros; simpl; destruct (zerobit i brbit); simpl; auto.
        + unfold join.
          case_eq (zerobit j (branching_bit j prefix)); intros; simpl;
            case_eq (zerobit i (branching_bit j prefix));
            intros; simpl; repeat rewrite eqb_is_dec ;
              destruct (eq i j); simpl; try congruence.
          * case_eq (zerobit i brbit); intros.
            { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_true_iff in H3. rewrite negb_true_iff in H4. congruence. }
            { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_true_iff in H3. rewrite negb_true_iff in H4. congruence. }
          * case_eq (zerobit i brbit); intros.
            { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_false_iff in H3. rewrite negb_false_iff in H4. congruence. }
            { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_false_iff in H3. rewrite negb_false_iff in H4. congruence. }
      - simpl. case_eq (match_prefix j prefix brbit); intros.
        + case_eq (zerobit j brbit); intros; simpl; destruct (zerobit i brbit); simpl; auto.
        + unfold join.
          case_eq (zerobit j (branching_bit j prefix)); intros; simpl; case_eq (zerobit i (branching_bit j prefix));
            intros; simpl; repeat rewrite eqb_is_dec ; destruct (eq i j); try congruence.
          * case_eq (zerobit i brbit); intros.
            { assert (Hmask' : mask prefix brbit = prefix) by (inv H; try congruence; auto).
              generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_true_iff in H3. rewrite negb_true_iff in H4. congruence. }
            { assert (Hmask' : mask prefix brbit = prefix) by (inv H; try congruence; auto).
              generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_true_iff in H3. rewrite negb_true_iff in H4. congruence. }
          * case_eq (zerobit i brbit); intros.
            { assert (Hmask' : mask prefix brbit = prefix) by (inv H; try congruence; auto).
              generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_false_iff in H3. rewrite negb_false_iff in H4. congruence. }
            { assert (Hmask' : mask prefix brbit = prefix) by (inv H; try congruence; auto).
              generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_false_iff in H3. rewrite negb_false_iff in H4. congruence. }
    Qed.

    
    Lemma get_not_same_lr:
      forall {A: Type} {t: ptrie A} {p brb brb' lr k},
        wf (Some (p, brb, brb', lr)) t ->
        zerobit k brb = negb lr ->
        get' k t = None.
    Proof.
      intros A t; induction t; intros.
      - reflexivity.
      - inv H. simpl. rewrite eqb_is_dec ; destruct (eq k0 k); auto.
        subst k0. destruct (zerobit k brb); simpl in H0; congruence.
      - inv H. simpl. case_eq (zerobit k brbit); intros.
        + eapply IHt1.
          * eapply wf_weaken; trivial. exact H3. auto.
          * eauto.
        + eapply IHt2.
          * eapply wf_weaken; trivial. exact H10. auto.
          * eauto.
    Qed.        
    
    Lemma grs':
      forall (A: Type) opt (i: key) (m: ptrie A),
        wf opt m ->
        get' i (remove' i m) = None.
    Proof.
      induction 1; intros.
      - reflexivity.
      - simpl. rewrite! eqb_is_dec ; destruct (eq k i); simpl; auto.
        rewrite eqb_is_dec. destruct (eq i k); simpl; congruence.
      - simpl. rewrite eqb_is_dec; destruct (eq k i); simpl; auto.
        rewrite eqb_is_dec; destruct (eq i k); simpl;congruence.
      - simpl. case_eq (match_prefix i prefix brbit); intros.
        + case_eq (zerobit i brbit); intros.
          * unfold branch. case_eq (remove' i l); intros.
            { eapply get_not_same_lr; eauto. }
            { rewrite <- H3. destruct r; auto.
              - simpl. rewrite H2; auto.
              - simpl. rewrite H2; auto. }
            { rewrite <- H3. destruct r; auto.
              - simpl. rewrite H2; auto.
              - simpl. rewrite H2; auto. }
          * unfold branch. destruct l; auto.
            { case_eq (remove' i r); intros.
              - simpl. rewrite eqb_is_dec ; destruct (eq i k); auto.
                subst i. inv H; congruence.
              - rewrite <- H3. simpl. rewrite H2. auto.
              - rewrite <- H3. simpl. rewrite H2. auto. }
            { case_eq (remove' i r); intros.
              - inv H; simpl. case_eq (zerobit i brbit0); intros; eapply get_not_same_prefix; eauto.
                + erewrite zerobit_spec in Hlr0; eauto.
                  erewrite zerobit_spec in H2; eauto.
                  rewrite negb_true_iff in Hlr0. rewrite negb_false_iff in H2. congruence.
                + erewrite zerobit_spec in Hlr0; eauto.
                  erewrite zerobit_spec in H2; eauto.
                  rewrite negb_true_iff in Hlr0. rewrite negb_false_iff in H2. congruence.
              - rewrite <- H3. simpl. rewrite H2. auto.
              - rewrite <- H3. simpl. rewrite H2. auto. }
        + eapply match_prefix_spec' in H1; auto.
          destruct H1 as [HO [n [HA HB]]].
          simpl. case_eq (zerobit i brbit); intros.
          * eapply get_not_same_prefix; eauto.
            apply not_eq_sym. generalize (branching_bit_spec _ _ HO).
            intros [n' [HX [HY HZ]]]. eapply HX in HB; subst; auto.
          * eapply get_not_same_prefix; eauto.
            apply not_eq_sym. generalize (branching_bit_spec _ _ HO).
            intros [n' [HX [HY HZ]]]. eapply HX in HB; subst; auto.
          * assumption.
      - simpl. case_eq (match_prefix i prefix brbit); intros.
        + case_eq (zerobit i brbit); intros.
          * unfold branch. case_eq (remove' i l); intros.
            { eapply get_not_same_lr; eauto. }
            { rewrite <- H3. destruct r; auto.
              - simpl. rewrite H2; auto.
              - simpl. rewrite H2; auto. }
            { rewrite <- H3. destruct r; auto.
              - simpl. rewrite H2; auto.
              - simpl. rewrite H2; auto. }
          * unfold branch. destruct l; auto.
            { case_eq (remove' i r); intros.
              - simpl. rewrite eqb_is_dec ; destruct (eq i k); auto.
                subst i. inv H; congruence.
              - rewrite <- H3. simpl. rewrite H2. auto.
              - rewrite <- H3. simpl. rewrite H2. auto. }
            { case_eq (remove' i r); intros.
              - inv H; simpl. case_eq (zerobit i brbit0); intros; eapply get_not_same_prefix; eauto.
                + erewrite zerobit_spec in Hlr; eauto.
                  erewrite zerobit_spec in H2; eauto.
                  rewrite negb_true_iff in Hlr. rewrite negb_false_iff in H2. congruence.
                + erewrite zerobit_spec in Hlr; eauto.
                  erewrite zerobit_spec in H2; eauto.
                  rewrite negb_true_iff in Hlr. rewrite negb_false_iff in H2. congruence.
              - rewrite <- H3. simpl. rewrite H2. auto.
              - rewrite <- H3. simpl. rewrite H2. auto. }
        + eapply match_prefix_spec' in H1; auto.
          destruct H1 as [HO [n [HA HB]]].
          simpl. case_eq (zerobit i brbit); intros.
          * eapply get_not_same_prefix; eauto.
            apply not_eq_sym. generalize (branching_bit_spec _ _ HO).
            intros [n' [HX [HY HZ]]]. eapply HX in HB; subst; auto.
          * eapply get_not_same_prefix; eauto.
            apply not_eq_sym. generalize (branching_bit_spec _ _ HO).
            intros [n' [HX [HY HZ]]]. eapply HX in HB; subst; auto.
          * inv H; auto; congruence.
          * inv H; auto; congruence.
    Qed.
    
    Lemma gro':
      forall (A: Type) opt (i j: key) (m: ptrie A),
        wf opt m ->
        i <> j -> get' i (remove' j m) = get' i m.
    Proof.
      induction 1; intros.
      - reflexivity.
      - simpl. repeat rewrite eqb_is_dec.
        destruct (eq k j); simpl; repeat rewrite eqb_is_dec; destruct (eq i k); simpl; try congruence.
      - simpl. repeat rewrite eqb_is_dec; destruct (eq k j); simpl; repeat rewrite eqb_is_dec; destruct (eq i k); simpl; congruence.
      - simpl. case_eq (match_prefix j prefix brbit); intros.
        + case_eq (zerobit j brbit); intros.
          * unfold branch. case_eq (remove' j l); intros.
            { case_eq (zerobit i brbit); intros; auto.
              rewrite <- IHwf1; auto. rewrite H4; simpl.
              eapply get_not_same_lr; eauto. }
            { destruct r.
              - rewrite <- H4. rewrite IHwf1; auto.
                case_eq (zerobit i brbit); intros; auto.
                simpl. eapply get_not_same_lr; eauto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto. }
            { destruct r.
              - rewrite <- H4. rewrite IHwf1; auto.
                case_eq (zerobit i brbit); intros; auto.
                simpl. eapply get_not_same_lr; eauto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto. }
          * unfold branch. destruct l; auto.
            { rewrite IHwf2; auto. 
              case_eq (zerobit i brbit); intros; auto.
              simpl. eapply get_not_same_lr; eauto. }
            { case_eq (remove' j r); intros.
              - case_eq (zerobit i brbit); intros; auto.
                symmetry. simpl. repeat rewrite eqb_is_dec; destruct (eq i k).
                + subst k. inv H; congruence.
                + rewrite <- IHwf2; auto. rewrite H4. reflexivity.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto. }
            { case_eq (remove' j r); intros.
              - simpl. case_eq (zerobit i brbit); intros; auto.
                rewrite <- IHwf2; auto. rewrite H4; simpl.
                case_eq (zerobit i brbit0); intros.
                + inv H. eapply get_not_same_prefix; eauto.
                  erewrite zerobit_spec in Hlr0; eauto.
                  erewrite zerobit_spec in H5; eauto. congruence.
                + inv H. eapply get_not_same_prefix; eauto.
                  erewrite zerobit_spec in Hlr0; eauto.
                  erewrite zerobit_spec in H5; eauto. congruence.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto. }
        + simpl. auto.
      - simpl. case_eq (match_prefix j prefix brbit); intros.
        + case_eq (zerobit j brbit); intros.
          * unfold branch. case_eq (remove' j l); intros.
            { case_eq (zerobit i brbit); intros; auto.
              rewrite <- IHwf1; auto. rewrite H4; simpl.
              eapply get_not_same_lr; eauto. }
            { destruct r.
              - rewrite <- H4. rewrite IHwf1; auto.
                case_eq (zerobit i brbit); intros; auto.
                simpl. eapply get_not_same_lr; eauto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto. }
            { destruct r.
              - rewrite <- H4. rewrite IHwf1; auto.
                case_eq (zerobit i brbit); intros; auto.
                simpl. eapply get_not_same_lr; eauto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto. }
          * unfold branch. destruct l; auto.
            { rewrite IHwf2; auto. 
              case_eq (zerobit i brbit); intros; auto.
              simpl. eapply get_not_same_lr; eauto. }
            { case_eq (remove' j r); intros.
              - case_eq (zerobit i brbit); intros; auto.
                symmetry. simpl. repeat rewrite eqb_is_dec;destruct (eq i k).
                + subst k. inv H; congruence.
                + rewrite <- IHwf2; auto. rewrite H4. reflexivity.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto. }
            { case_eq (remove' j r); intros.
              - simpl. case_eq (zerobit i brbit); intros; auto.
                rewrite <- IHwf2; auto. rewrite H4; simpl.
                case_eq (zerobit i brbit0); intros.
                + inv H. eapply get_not_same_prefix; eauto.
                  erewrite zerobit_spec in Hlr; eauto.
                  erewrite zerobit_spec in H5; eauto. congruence.
                + inv H. eapply get_not_same_prefix; eauto.
                  erewrite zerobit_spec in Hlr; eauto.
                  erewrite zerobit_spec in H5; eauto. congruence.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto.
              - rewrite <- H4. simpl. case_eq (zerobit i brbit); intros; auto. }
        + simpl. auto.
    Qed.


    Fixpoint map' {A B: Type} (f: key -> A -> B) (m: ptrie A): ptrie B :=
      match m with
      | Empty => Empty
      | Leaf k v => Leaf k (f k v)
      | Branch p m l r => Branch p m (map' f l) (map' f r)
      end.

    Lemma wf_map':
      forall (A B: Type) (f: key -> A -> B) (m: ptrie A) opt,
        wf opt m ->
        wf opt (map' f m).
    Proof.
      induction m; intros.
      - simpl; constructor.
      - simpl. inv H; constructor; auto.
      - simpl. inv H; econstructor; trivial; try eassumption.
        + destruct m1; simpl; congruence.
        + destruct m2; simpl; congruence.
        + auto.
        + auto.
        + destruct m1; simpl; congruence.
        + destruct m2; simpl; congruence.
        + auto.
        + auto.
    Qed.
  
    Lemma gmap':
      forall (A B: Type) (f: key -> A -> B) (i: key) (m: ptrie A),
        get' i (map' f m) = option_map (f i) (get' i m).
    Proof.
      induction m; intros.
      - reflexivity.
      - simpl. repeat rewrite eqb_is_dec;destruct (eq i k); simpl; auto; congruence.
      - simpl. destruct (zerobit i brbit); simpl; auto.
    Qed.
    
    Fixpoint map1' {A B: Type} (f: A -> B) (m: ptrie A): ptrie B :=
      match m with
      | Empty => Empty
      | Leaf k v => Leaf k (f v)
      | Branch p m l r => Branch p m (map1' f l) (map1' f r)
      end.

    Lemma wf_map1':
      forall (A B: Type) (f: A -> B) (m: ptrie A) opt,
        wf opt m ->
        wf opt (map1' f m).
    Proof.
      induction m; intros.
      - simpl; constructor.
      - simpl. inv H; constructor; auto.
      - simpl. inv H; econstructor; trivial; try eassumption.
        + destruct m1; simpl; congruence.
        + destruct m2; simpl; congruence.
        + auto.
        + auto.
        + destruct m1; simpl; congruence.
        + destruct m2; simpl; congruence.
        + auto.
        + auto.
    Qed.
    
    Lemma gmap1':
      forall (A B: Type) (f: A -> B) (i: key) (m: ptrie A),
        get' i (map1' f m) = option_map f (get' i m).
    Proof.
      induction m; intros.
      - reflexivity.
      - simpl. repeat rewrite eqb_is_dec;destruct (eq i k); simpl; auto; congruence.
      - simpl. destruct (zerobit i brbit); simpl; auto.
    Qed.
    
    Fixpoint elements' {A: Type} (m: ptrie A) (acc: list (key * A)): list (key * A) :=
      match m with
      | Empty => acc
      | Leaf k v => (k, v)::acc
      | Branch p m l r => elements' l (elements' r acc)
      end.
    
    Lemma elements_incl':
      forall (A: Type) (m: ptrie A) k x,
        In x k -> In x (elements' m k).
    Proof. induction m; simpl; intros; auto. Qed.
    
    Lemma elements_correct':
      forall (A: Type) (m: ptrie A) (i: key) (v: A) k,
        get' i m = Some v -> In (i, v) (elements' m k).
    Proof.
      induction m; intros.
      - inv H.
      - simpl in H. repeat rewrite eqb_is_dec in *;destruct (eq i k); inv H.
        simpl. eapply in_eq.
      - simpl in H. case_eq (zerobit i brbit); intros; rewrite H0 in H.
        + eapply IHm1; eauto.
        + simpl. eapply IHm2 in H.
          eapply elements_incl'; eauto.
    Qed.
    
    Lemma in_elements':
      forall {A: Type} (m: ptrie A) k i v opt,
        wf opt m ->
        In (i, v) (elements' m k) -> get' i m = Some v \/ In (i, v) k.
    Proof.
      induction m; intros.
      - simpl in H0; right; auto.
      - simpl in H0; simpl; destruct H0; auto.
        inv H0. rewrite eqb_refl. left; reflexivity.
      - simpl in H0. inv H.
        { eapply IHm1 in H0. destruct H0.
          + left. simpl. case_eq (zerobit i brbit); intros; auto.
            generalize (get_not_same_lr  H4 H0); congruence.
          + eapply IHm2 in H; eauto. destruct H; auto.
            left. simpl. case_eq (zerobit i brbit); intros; auto.
            generalize (get_not_same_lr H7 H0); congruence.
          + exact H4. }
        { eapply IHm1 in H0. destruct H0.
          + left. simpl. case_eq (zerobit i brbit); intros; auto.
            generalize (get_not_same_lr H4 H0); congruence.
          + eapply IHm2 in H; eauto. destruct H; auto.
            left. simpl. case_eq (zerobit i brbit); intros; auto.
            generalize (get_not_same_lr H7 H0); congruence.
          + exact H4. }
    Qed.
    
    Lemma elements_append':
      forall A (m: ptrie A) k1 k2,
        elements' m (k1 ++ k2) = elements' m k1 ++ k2.
    Proof.
      induction m; simpl; intros; auto.
      rewrite IHm2. rewrite IHm1. auto.
    Qed.      
    
    Lemma elements_branch':
      forall A (t1 t2: ptrie A) p m,
        elements' (Branch p m t1 t2) nil =
        elements' t1 nil ++ elements' t2 nil.
    Proof.
      intros; simpl. rewrite <- elements_append'. auto.
    Qed.

    Definition keys' {A: Type} (m: ptrie A) :=
      List.map (@fst key A) (elements' m nil).

    Lemma keys_norepet':
      forall (A: Type) (m: ptrie A) opt,
        wf opt m ->
        list_norepet (keys' m).
    Proof.
      induction m; intros.
      - constructor.
      - constructor; auto. constructor.
      - unfold keys'. rewrite elements_branch'.
        rewrite map_app. apply list_norepet_append.
        + inv H; eapply IHm1; eauto.
        + inv H; eapply IHm2; eauto.
        + red; intros.
          eapply in_map_iff in H0; eapply in_map_iff in H1.
          destruct H0 as [x1 [HA HB]]. destruct H1 as [x2 [HC HD]].
          destruct x1; destruct x2; subst.
          simpl. inv H.
          * eapply in_elements' in HB; eauto.
            eapply in_elements' in HD; eauto.
            destruct HB; auto. destruct HD; auto.
            case_eq (zerobit k brbit); intros; case_eq (zerobit k0 brbit); intros.
            { generalize (get_not_same_lr  H6 H2). congruence. }
            { red; intros; congruence. }
            { generalize (get_not_same_lr H3 H1). congruence. }
            { generalize (get_not_same_lr H3 H1). congruence. }
          * eapply in_elements' in HB; eauto.
            eapply in_elements' in HD; eauto.
            destruct HB; auto. destruct HD; auto.
            case_eq (zerobit k brbit); intros; case_eq (zerobit k0 brbit); intros.
            { generalize (get_not_same_lr H6 H2). congruence. }
            { red; intros; congruence. }
            { generalize (get_not_same_lr H3 H1). congruence. }
            { generalize (get_not_same_lr H3 H1). congruence. }
    Qed.
    
    Fixpoint fold' {A B: Type} (f: B -> key -> A -> B) (m: ptrie A) (acc: B): B :=
      match m with
      | Empty => acc
      | Leaf k v => f acc k v
      | Branch p m l r => fold' f r (fold' f l acc)
      end.
    
    Lemma fold_elements':
      forall (A B: Type) (f: B -> key -> A -> B) (m: ptrie A) (v: B),
        fold' f m v = List.fold_left (fun a p => f a (fst p) (snd p)) (elements' m nil) v.
    Proof.
      induction m; intros; auto.
      simpl. replace (elements' m2 nil) with (nil ++ elements' m2 nil); auto.
      rewrite elements_append'. rewrite fold_left_app.
      rewrite IHm1. auto.
    Qed.      
    
    Fixpoint fold1' {A B: Type} (f: B -> A -> B) (m: ptrie A) (acc: B): B :=
      match m with
      | Empty => acc
      | Leaf k v => f acc v
      | Branch p m l r => fold1' f r (fold1' f l acc)
      end.
    
    Lemma fold1_elements':
      forall (A B: Type) (f: B -> A -> B) (m: ptrie A) (v: B),
        fold1' f m v = List.fold_left (fun a p => f a (snd p)) (elements' m nil) v.
    Proof.
      induction m; intros; auto.
      simpl. replace (elements' m2 nil) with (nil ++ elements' m2 nil); auto.
      rewrite elements_append'. rewrite fold_left_app.
      rewrite IHm1. auto.
    Qed.

    Fixpoint insert' {A: Type} (c: A -> A -> A) (i: key) (x: A) (m: ptrie A): ptrie A :=
      match m with
      | Empty => Leaf i x
      | Leaf j v => if eqb i j then Leaf i (c x v) else join i (Leaf i x) j (Leaf j v)
      | Branch prefix brbit l r =>
        if match_prefix i prefix brbit then
          if zerobit i brbit then
            Branch prefix brbit (insert' c i x l) r
          else
            Branch prefix brbit l (insert' c i x r)
        else join i (Leaf i x) prefix (Branch prefix brbit l r)
      end.

    Ltac destruct_eq X Y :=
      rewrite? (eqb_is_dec X Y) in *; destruct (eq X Y) ; unfold proj_sumbool in *.


    Lemma insert'_not_empty:
      forall A c k x (pt: ptrie A),
        insert' c k x pt <> Empty.
    Proof.
      intros; induction pt; simpl; try congruence.
      - destruct_eq k k0; try congruence.
        unfold join; simpl. destruct (zerobit k (branching_bit k k0)); discriminate.
      - destruct (match_prefix k prefix brbit).
        + destruct (zerobit k brbit); discriminate.
        + unfold join; simpl. destruct (zerobit k (branching_bit k prefix)); discriminate.
    Qed.

    Lemma wf_insert':
      forall A opt c k x (t: ptrie A),
        wf opt t ->
        wf opt (Leaf k x) ->
        wf opt (insert' c k x t).
    Proof.
      induction 1; intros.
      - simpl; auto.
      - simpl. destruct_eq k k0; auto.
        + inv H; econstructor; eauto.
        + eapply wf_join_Leaf; eauto; try constructor; auto.
      - simpl. destruct_eq k k0; auto.
        + econstructor.
        + eapply wf_join_Leaf; eauto; try constructor; auto.
      - simpl. case_eq (match_prefix k prefix brbit); intros.
        + case_eq (zerobit k brbit); intros; econstructor; trivial; try eassumption.
          * eapply insert'_not_empty; eauto.
          * apply IHwf1. constructor; auto. intros; symmetry.
            eapply match_prefix_spec; eauto.
          * eapply insert'_not_empty; eauto.
          * apply IHwf2. constructor; auto. intros; symmetry.
            eapply match_prefix_spec; eauto.
        + generalize H2. intros HX.
          eapply (match_prefix_spec') in H2; eauto. destruct H2 as [HO [n [HA HB]]].
          eapply wf_join_Branch; eauto.
          econstructor; trivial; try eassumption.
      - simpl. case_eq (match_prefix k prefix brbit); intros.
        + case_eq (zerobit k brbit); intros; econstructor; trivial; try eassumption.
          * eapply insert'_not_empty; eauto.
          * apply IHwf1. constructor; auto.
            inv H; congruence.
            intros; symmetry.
            eapply match_prefix_spec; eauto. inv H; congruence.
          * eapply insert'_not_empty; eauto.
          * apply IHwf2. constructor; auto.
            inv H; congruence.
            intros; symmetry.
            eapply match_prefix_spec; eauto. inv H; congruence.
        + generalize H2; intros HX.
          eapply (match_prefix_spec') in H2; eauto. destruct H2 as [n [HA [HB HC]]].
          eapply wf_join_Branch; eauto; try econstructor; eauto.
          inv H; congruence.
    Qed.

    Lemma gis':
      forall (A: Type) opt c (i: key) (x: A) (m: ptrie A),
        wf opt m ->
        get' i (insert' c i x m) = match get' i m with
                                   | None => Some x
                                   | Some y => Some (c x y)
                                   end.
    Proof.
      induction 1; intros.
      - simpl. rewrite (eqb_refl); congruence.
      - simpl. repeat rewrite eqb_is_dec ; destruct (eq i k); auto.
        + simpl; rewrite eqb_refl; congruence.
        + unfold join. generalize (branching_bit_spec _ _ n). intros [m' [HA HB]].
          case_eq (zerobit i (branching_bit i k));
            intros; simpl; rewrite H; rewrite eqb_is_dec ; destruct (eq i i); simpl; congruence.
      - simpl. repeat rewrite eqb_is_dec ; destruct (eq i k); auto.
        + simpl; rewrite eqb_refl; congruence.
        + unfold join.
          case_eq (zerobit i (branching_bit i k));
            intros; simpl; rewrite H; rewrite (eqb_refl); congruence.
      - simpl. case_eq (match_prefix i prefix brbit); intros.
        + case_eq (zerobit i brbit); intros; simpl; rewrite H2; auto.
        + generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H1). intros [Hne [n [HA HB]]].
          generalize (branching_bit_spec _ _ Hne). intros [n' [HX [HY HZ]]]. eapply HX in HB; subst.
          unfold join.
          case_eq (zerobit i (branching_bit i prefix));
            intros; simpl; rewrite H2; rewrite eqb_refl ; try congruence.
          * case_eq (zerobit i brbit); intros.
            { assert (get' i l = None).
              - eapply get_not_same_prefix; eauto.
              - rewrite H4; auto. }
            { assert (get' i r = None).
              - eapply get_not_same_prefix; eauto.
              - rewrite H4; auto. }
          * case_eq (zerobit i brbit); intros.
            { assert (get' i l = None).
              - eapply get_not_same_prefix; eauto.
              - rewrite H4; auto. }
            { assert (get' i r = None).
              - eapply get_not_same_prefix; eauto.
              - rewrite H4; auto. }
      - simpl. case_eq (match_prefix i prefix brbit); intros.
        + case_eq (zerobit i brbit); intros; simpl; rewrite H2; auto.
        + unfold join. eapply match_prefix_spec' in H1; auto.
          * destruct H1 as [HO [n [HA HB]]].
            case_eq (zerobit i (branching_bit i prefix));
              intros; simpl; rewrite H1; rewrite (eqb_refl); try congruence.
            { generalize (branching_bit_spec _ _ HO). intros [n' [HX [HY HZ]]]. eapply HX in HB; subst.
              case_eq (zerobit i brbit); intros.
              - assert (get' i l = None).
                + eapply get_not_same_prefix; eauto.
                + rewrite H3; auto.
              - assert (get' i r = None).
                + eapply get_not_same_prefix; eauto.
                + rewrite H3; auto. }
            { generalize (branching_bit_spec _ _ HO). intros [n' [HX [HY HZ]]]. eapply HX in HB; subst.
              case_eq (zerobit i brbit); intros.
              - assert (get' i l = None).
                + eapply get_not_same_prefix; eauto.
                + rewrite H3; auto.
              - assert (get' i r = None).
                + eapply get_not_same_prefix; eauto.
                + rewrite H3; auto. }
          * inv H; auto; congruence.
          * inv H; auto; congruence.
    Qed.
    

    Lemma gio':
      forall (A: Type) opt c (i j: key) (x: A) (m: ptrie A),
        wf opt m ->
        i <> j -> get' i (insert' c j x m) = get' i m.
    Proof.
      induction 1; intros.
      - simpl. destruct_eq i j; simpl ; congruence.
      - simpl. destruct_eq j k; auto.
        + simpl. rewrite! eqb_is_dec ; destruct (eq i k); destruct (eq i j); simpl ; congruence.
        + unfold join. 
          case_eq (zerobit j (branching_bit j k)); intros; simpl; case_eq (zerobit i (branching_bit j k));
            intros; simpl; rewrite! eqb_is_dec ; destruct (eq i j); destruct (eq i k); simpl; try congruence.
          * subst i. generalize (branching_bit_spec j k n). intros [n' [HA [HB HC]]].
            elim HC. erewrite zerobit_spec in H0; eauto.
            erewrite zerobit_spec in H1; eauto.
            eapply negb_true_iff in H0. eapply negb_true_iff in H1. congruence.
          * subst i. generalize (branching_bit_spec  j k n). intros [n' [HA [HB HC]]].
            elim HC. erewrite zerobit_spec in H0; eauto.
            erewrite zerobit_spec in H1; eauto.
            eapply negb_false_iff in H0. eapply negb_false_iff in H1. congruence.
      - simpl. destruct_eq j k; auto.
        + simpl. destruct_eq i k; destruct_eq i j; simpl ; congruence.
        + unfold join.
          case_eq (zerobit j (branching_bit j k)); intros; simpl; case_eq (zerobit i (branching_bit j k));
            intros; simpl; destruct_eq i j; destruct_eq i k; try congruence.
          * subst i. generalize (branching_bit_spec j k n). intros [n' [HA [HB HC]]].
            elim HC. erewrite zerobit_spec in H0; eauto.
            erewrite zerobit_spec in H1; eauto.
            eapply negb_true_iff in H0. eapply negb_true_iff in H1. congruence.
          * subst i. generalize (branching_bit_spec  j k n). intros [n' [HA [HB HC]]].
            elim HC. erewrite zerobit_spec in H0; eauto.
            erewrite zerobit_spec in H1; eauto.
            eapply negb_false_iff in H0. eapply negb_false_iff in H1. congruence.
      - simpl. case_eq (match_prefix j prefix brbit); intros.
        + case_eq (zerobit j brbit); intros; simpl; destruct (zerobit i brbit); simpl; auto.
        + unfold join.
          case_eq (zerobit j (branching_bit j prefix)); intros; simpl; case_eq (zerobit i (branching_bit j prefix)); intros; simpl; destruct_eq i j; try congruence.
          * case_eq (zerobit i brbit); intros.
            { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_true_iff in H3. rewrite negb_true_iff in H4. congruence. }
            { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_true_iff in H3. rewrite negb_true_iff in H4. congruence. }
          * case_eq (zerobit i brbit); intros.
            { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_false_iff in H3. rewrite negb_false_iff in H4. congruence. }
            { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_false_iff in H3. rewrite negb_false_iff in H4. congruence. }
      - simpl. case_eq (match_prefix j prefix brbit); intros.
        + case_eq (zerobit j brbit); intros; simpl; destruct (zerobit i brbit); simpl; auto.
        + unfold join. 
          case_eq (zerobit j (branching_bit j prefix)); intros; simpl; case_eq (zerobit i (branching_bit j prefix)); intros; simpl; destruct_eq i j; try congruence.
          * case_eq (zerobit i brbit); intros.
            { assert (Hmask' : mask prefix brbit = prefix) by (inv H; try congruence; auto).
              generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_true_iff in H3. rewrite negb_true_iff in H4. congruence. }
            { assert (Hmask' : mask prefix brbit = prefix) by (inv H; try congruence; auto).
              generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_true_iff in H3. rewrite negb_true_iff in H4. congruence. }
          * case_eq (zerobit i brbit); intros.
            { assert (Hmask' : mask prefix brbit = prefix) by (inv H; try congruence; auto).
              generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_false_iff in H3. rewrite negb_false_iff in H4. congruence. }
            { assert (Hmask' : mask prefix brbit = prefix) by (inv H; try congruence; auto).
              generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [HO [n0 [HP HQ]]].
              symmetry; eapply get_not_same_prefix; eauto.
              generalize (branching_bit_spec _ _ HO). intros [n1 [HX [HY HZ]]].
              eapply HX in HQ. subst n1. rewrite (zerobit_spec _ _ _ HX) in H3.
              rewrite (zerobit_spec _ _ _ HX) in H4.
              rewrite negb_false_iff in H3. rewrite negb_false_iff in H4. congruence. }
    Qed.

    Fixpoint combine' {A: Type} (c: A -> A -> A) (t1: ptrie A) { struct t1 } :=
      fix combine_aux t2 { struct t2 } :=
        match t1, t2 with
        | Empty, _ => t2
        | _, Empty => t1
        | Leaf i x, _ => insert' c i x t2
        | _, Leaf i x => insert' (fun a b => c b a) i x t1
        | Branch p1 m1 l1 r1, Branch p2 m2 l2 r2 =>
          if eqb p1 p2 && eqb m1 m2
          then Branch p1 m1 (combine' c l1 l2) (combine' c r1 r2)
          else if ltb m1 m2 && match_prefix p2 p1 m1 then
                 if zerobit p2 m1 then Branch p1 m1 (combine' c l1 t2) r1 else Branch p1 m1 l1 (combine' c r1 t2)
               else if ltb m2 m1 && match_prefix p1 p2 m2 then
                      if zerobit p1 m2 then Branch p2 m2 (combine_aux l2) r2 else Branch p2 m2 l2 (combine_aux r2)
                    else join p1 t1 p2 t2
        end.

    Lemma combine'_not_empty:
      forall A c (t1 t2: ptrie A),
        t1 <> Empty \/ t2 <> Empty ->
        combine' c t1 t2 <> Empty.
    Proof.
      induction t1; intros.
      - destruct H; try congruence.
        destruct t2; simpl; congruence.
      - destruct H; destruct t2; unfold combine'; try congruence; eapply insert'_not_empty.
      - destruct H; destruct t2; unfold combine'; try congruence.
        + eapply insert'_not_empty.
        + unfold join; destruct (eqb prefix prefix0 && eqb brbit brbit0); destruct (ltb brbit brbit0 && match_prefix prefix0 prefix brbit); destruct (zerobit prefix0 brbit); destruct (ltb brbit0 brbit && match_prefix prefix prefix0 brbit0); destruct (zerobit prefix brbit0); destruct (zerobit prefix (branching_bit prefix prefix0)); try discriminate .
        + eapply insert'_not_empty.
        + unfold join; destruct (eqb prefix prefix0 && eqb brbit brbit0); destruct (ltb brbit brbit0 && match_prefix prefix0 prefix brbit); destruct (zerobit prefix0 brbit); destruct (ltb brbit0 brbit && match_prefix prefix prefix0 brbit0); destruct (zerobit prefix brbit0); destruct (zerobit prefix (branching_bit prefix prefix0)); try discriminate .
    Qed.

    Lemma wf_join_Branch_Branch_0:
      forall A opt p1 m (l1 r1: ptrie A) p2 l2 r2,
        p1 <> p2 ->
        wf opt (Branch p1 m l1 r1) ->
        wf opt (Branch p2 m l2 r2) ->
        wf opt (join p1 (Branch p1 m l1 r1) p2 (Branch p2 m l2 r2)).
    Proof.
      intros. generalize (branching_bit_spec _ _ H). intros [n [HA [HB HC]]].
      inv H0; inv H1.
      - generalize (proj2 (Hbrbit'0 _) eq_refl); intros Heq.
        apply Hbrbit' in Heq. subst brbit'0.
        unfold join. case_eq (zerobit p1 (branching_bit p1 p2)); intros.
        + econstructor; try discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_false_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
                elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * assumption.
          * eapply mask_spec'; eauto.
          * assumption.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * assumption.
          * intros; eapply mask_spec; eauto.
          * assumption.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * econstructor; trivial.
            { eapply mask_spec'; eauto. }
            { destruct (lt_dec n brbit'); try eassumption.
              elim HC. rewrite Hlength; try lia; rewrite Hlength0; try lia; auto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
          * econstructor; trivial.
            { erewrite zerobit_spec in H0; eauto.
              erewrite zerobit_spec; eauto.
              eapply negb_true_iff in H0. eapply negb_false_iff.
              destruct (testbit p2 n); congruence. }
            { eapply mask_spec'; eauto. }
            { destruct (lt_dec n brbit'); try eassumption.
              elim HC. rewrite Hlength; try lia; rewrite Hlength0; try lia; auto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { intros; rewrite <- HB; auto. eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
        + econstructor; try discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_false_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
                elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * assumption.
          * eapply mask_spec'; eauto.
          * assumption.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * assumption.
          * intros; eapply mask_spec; eauto.
          * assumption.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * econstructor; trivial.
            { erewrite zerobit_spec in H0; eauto.
              erewrite zerobit_spec; eauto.
              eapply negb_false_iff in H0. eapply negb_true_iff.
              destruct (testbit p2 n); congruence. }
            { eapply mask_spec'; eauto. }
            { destruct (lt_dec n brbit'); try eassumption.
              elim HC. rewrite Hlength; try lia; rewrite Hlength0; try lia; auto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { intros; rewrite <- HB; auto. eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
          * econstructor; trivial.
            { eapply mask_spec'; eauto. }
            { destruct (lt_dec n brbit'); try eassumption.
              elim HC. rewrite Hlength; try lia; rewrite Hlength0; try lia; auto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
      - generalize (proj2 (Hbrbit'0 _) eq_refl); intros Heq.
        apply Hbrbit' in Heq. subst brbit'0.
        unfold join. case_eq (zerobit p1 (branching_bit p1 p2)); intros.
        + econstructor; try discriminate.
          * eassumption.
          * intros; eapply mask_spec; eauto.
          * econstructor; trivial.
            { eapply mask_spec'; eauto. }
            { inv H5; auto; congruence. }
            { destruct (lt_dec n brbit'); try eassumption.
              assert (Hlength : forall n : nat, (n >= brbit')%nat -> testbit p1 n = false) by (inv H5; try congruence; auto).
              assert (Hlength0 : forall n : nat, (n >= brbit')%nat -> testbit p2 n = false) by (inv H4; try congruence; auto).
              elim HC. rewrite Hlength; try lia; rewrite Hlength0; try lia; auto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
          * econstructor; trivial.
            { erewrite zerobit_spec in H0; eauto.
              erewrite zerobit_spec; eauto.
              eapply negb_true_iff in H0. eapply negb_false_iff.
              destruct (testbit p2 n); congruence. }
            { eapply mask_spec'; eauto. }
            { inv H4; auto; congruence. }
            { destruct (lt_dec n brbit'); try eassumption.
              assert (Hlength : forall n : nat, (n >= brbit')%nat -> testbit p1 n = false) by (inv H5; try congruence; auto).
              assert (Hlength0 : forall n : nat, (n >= brbit')%nat -> testbit p2 n = false) by (inv H4; try congruence; auto).
              elim HC. rewrite Hlength; try lia; rewrite Hlength0; try lia; auto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { intros; rewrite <- HB; auto. eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
        + econstructor; try discriminate.
          * eassumption.
          * intros; eapply mask_spec; eauto.
          * econstructor; trivial.
            { erewrite zerobit_spec in H0; eauto.
              erewrite zerobit_spec; eauto.
              eapply negb_false_iff in H0. eapply negb_true_iff.
              destruct (testbit p2 n); congruence. }
            { eapply mask_spec'; eauto. }
            { inv H4; auto; congruence. }
            { destruct (lt_dec n brbit'); try eassumption.
              assert (Hlength : forall n : nat, (n >= brbit')%nat -> testbit p1 n = false) by (inv H5; try congruence; auto).
              assert (Hlength0 : forall n : nat, (n >= brbit')%nat -> testbit p2 n = false) by (inv H4; try congruence; auto).
              elim HC. rewrite Hlength; try lia; rewrite Hlength0; try lia; auto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { intros; rewrite <- HB; auto. eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
          * econstructor; trivial.
            { eapply mask_spec'; eauto. }
            { inv H5; auto; congruence. }
            { destruct (lt_dec n brbit'); try eassumption.
              assert (Hlength : forall n : nat, (n >= brbit')%nat -> testbit p1 n = false) by (inv H5; try congruence; auto).
              assert (Hlength0 : forall n : nat, (n >= brbit')%nat -> testbit p2 n = false) by (inv H4; try congruence; auto).
              elim HC. rewrite Hlength; try lia; rewrite Hlength0; try lia; auto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
    Qed.

    Lemma wf_join_Branch_Branch_1:
      forall A opt p1 m1 (l1 r1: ptrie A) p2 m2 l2 r2 (HLT: ltb m2 m1 = true),
        match_prefix p1 p2 m2 = false ->
        wf opt (Branch p1 m1 l1 r1) ->
        wf opt (Branch p2 m2 l2 r2) ->
        wf opt (join p1 (Branch p1 m1 l1 r1) p2 (Branch p2 m2 l2 r2)).
    Proof.
      intros; inv H0; inv H1.
      - rename H into HO. generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) HO).
        intros [H [n' [HP  HQ]]].
        unfold join. generalize (branching_bit_spec _ _ H). intros [n [HA [HB HC]]].
        apply HA in HQ. subst n'.
        case_eq (zerobit p1 (branching_bit p1 p2)); intros.
        + econstructor.
          * discriminate.
          * discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
                elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * eauto.
          * eapply mask_spec'; auto. exact HA.
          * auto.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * auto.
          * intros. eapply mask_spec. exact HA. auto.
          * auto.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * rewrite <- H0. econstructor; trivial.
            { eapply mask_spec'; eauto. }
            { rewrite (zerobit_spec _ _ _ HA) in H0. apply negb_true_iff in H0.
              eapply lt_trans; try eassumption. eapply ltb_spec; try eapply HLT; eauto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_false_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_true_iff in H0. destruct (testbit p2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { eassumption. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
        + econstructor.
          * discriminate.
          * discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
                elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * eauto.
          * eapply mask_spec'; auto. exact HA.
          * auto.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * auto.
          * intros. eapply mask_spec. exact HA. auto.
          * auto.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_false_iff in H0. destruct (testbit p2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { eassumption. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
          * rewrite <- H0. econstructor; trivial.
            { eapply mask_spec'; eauto. }
            { rewrite (zerobit_spec _ _ _ HA) in H0. apply negb_true_iff in H0.
              eapply lt_trans; try eassumption. eapply ltb_spec; try eapply HLT; eauto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
      - rename H into HO. assert (Hmask'0: mask p2 m2 = p2) by (inv H4; auto; congruence).
        generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) HO).
        intros [H [n' [HP  HQ]]].
        unfold join. generalize (branching_bit_spec _ _ H). intros [n [HA [HB HC]]].
        apply HA in HQ. subst n'.
        case_eq (zerobit p1 (branching_bit p1 p2)); intros.
        + econstructor.
          * discriminate.
          * discriminate.
          * eauto.
          * intros. eapply mask_spec. exact HA. auto.
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_true_iff in H0. assumption. }
            { eapply mask_spec'; auto. exact HA. }
            { inv H5; auto; congruence. }
            { auto. }
            { eapply lt_trans; try eassumption.
              eapply ltb_spec; try eapply HLT; eauto. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
          * econstructor; try eassumption.
            { erewrite zerobit_spec; eauto.
              erewrite zerobit_spec in H0; eauto.
              rewrite negb_true_iff in H0. rewrite negb_false_iff.
              destruct (testbit p2 n); auto; congruence. }
            { eapply mask_spec'; eauto. }
            { eapply mask_spec; auto. }
            { intros; rewrite <- HB; auto; eapply mask_spec; eauto. }
        + econstructor.
          * discriminate.
          * discriminate.
          * eauto.
          * intros. eapply mask_spec. exact HA. auto.
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_false_iff in H0. destruct (testbit p2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { eassumption. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
          * rewrite <- H0. econstructor; trivial.
            { eapply mask_spec'; eauto. }
            { inv H5; auto; congruence. }
            { rewrite (zerobit_spec _ _ _ HA) in H0. apply negb_true_iff in H0.
              eapply lt_trans; try eassumption. eapply ltb_spec; try eapply HLT; eauto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
    Qed.

    Lemma wf_join_Branch_Branch_2:
      forall A opt p1 m1 (l1 r1: ptrie A) p2 m2 l2 r2 (HLT: ltb m1 m2 = true),
        match_prefix p2 p1 m1 = false ->
        wf opt (Branch p1 m1 l1 r1) ->
        wf opt (Branch p2 m2 l2 r2) ->
        wf opt (join p1 (Branch p1 m1 l1 r1) p2 (Branch p2 m2 l2 r2)).
    Proof.
      intros; inv H0; inv H1.
      - rename H into HO. generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') HO).
        intros [H [n' [HP  HQ]]]. eapply not_eq_sym in H.
        unfold join. generalize (branching_bit_spec _ _ H). intros [n [HA [HB HC]]].
        rewrite branching_bit_sym in HQ. apply HA in HQ. subst n'.
        case_eq (zerobit p1 (branching_bit p1 p2)); intros.
        + econstructor.
          * discriminate.
          * discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
                elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * eauto.
          * eapply mask_spec'; auto. exact HA.
          * auto.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * auto.
          * intros. eapply mask_spec. exact HA. auto.
          * auto.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_true_iff in H0. assumption. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { eassumption. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
          * econstructor; trivial.
            { erewrite zerobit_spec; eauto.
              erewrite zerobit_spec in H0; eauto.
              apply negb_true_iff in H0. destruct (testbit p2 n); auto; congruence. }
            { eapply mask_spec'; eauto. }
            { rewrite (zerobit_spec _ _ _ HA) in H0. apply negb_true_iff in H0.
              eapply lt_trans; try eassumption. eapply ltb_spec; try eapply HLT; eauto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { intros; rewrite <- HB; auto; eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
        + econstructor.
          * discriminate.
          * discriminate.
          * rewrite ! (zerobit_spec _ _ _ Hbrb).
            f_equal. destruct (lt_dec brb' n).
            { eapply mask_spec; eauto. }
            { destruct (eq_nat_dec brb' n).
              - subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
                eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
                elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence.
              - elim HC. rewrite <- Hprefix; try lia; auto.
                apply Hprefix0; lia. }
          * eauto.
          * eapply mask_spec'; auto. exact HA.
          * auto.
          * destruct (lt_dec brb' n); eauto.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * auto.
          * intros. eapply mask_spec. exact HA. auto.
          * auto.
          * intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto.
            destruct (lt_dec brb' n); try lia.
            destruct (eq_nat_dec brb' n).
            { subst n. rewrite (zerobit_spec _ _ _ HA) in H0.
              eapply negb_true_iff in H0. rewrite ! (zerobit_spec _ _ _ Hbrb) in Hlr.
              elim HC. destruct (testbit p1 brb'); destruct (testbit p2 brb'); auto; congruence. }
            { elim HC. rewrite <- Hprefix; try lia; auto.
              apply Hprefix0; lia. }
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_false_iff in H0. destruct (testbit p2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { eapply lt_trans; try eassumption. eapply ltb_spec; try eapply HLT; eauto. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
          * rewrite <- H0. econstructor; trivial.
            { eapply mask_spec'; eauto. }
            { eassumption. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
      - rename H into HO. assert (Hmask': mask p1 m1 = p1) by (inv H5; auto; congruence).
        generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') HO).
        intros [H [n' [HP  HQ]]]. eapply not_eq_sym in H.
        unfold join. generalize (branching_bit_spec _ _ H). intros [n [HA [HB HC]]].
        rewrite branching_bit_sym in HQ. apply HA in HQ. subst n'.
        case_eq (zerobit p1 (branching_bit p1 p2)); intros.
        + econstructor.
          * discriminate.
          * discriminate.
          * eassumption.
          * intros. eapply mask_spec. exact HA. auto.
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_true_iff in H0. assumption. }
            { eapply mask_spec'; auto. exact HA. }
            { auto. }
            { auto. }
            { eassumption. }
            { auto. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
          * econstructor; trivial.
            { erewrite zerobit_spec; eauto.
              erewrite zerobit_spec in H0; eauto.
              apply negb_true_iff in H0. destruct (testbit p2 n); auto; congruence. }
            { eapply mask_spec'; eauto. }
            { inv H4; auto; congruence. }
            { rewrite (zerobit_spec _ _ _ HA) in H0. apply negb_true_iff in H0.
              eapply lt_trans; try eassumption. eapply ltb_spec; try eapply HLT; eauto. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { intros; rewrite <- HB; auto; eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
        + econstructor.
          * discriminate.
          * discriminate.
          * eassumption.
          * intros. eapply mask_spec. exact HA. auto.
          * econstructor.
            { auto. }
            { auto. }
            { erewrite zerobit_spec; eauto.
              eapply negb_true_iff. erewrite zerobit_spec in H0; eauto.
              eapply negb_false_iff in H0. destruct (testbit p2 n); congruence; auto. }
            { eapply mask_spec'; auto. exact HA. }
            { inv H4; auto; congruence. }
            { auto. }
            { eapply lt_trans; try eassumption. eapply ltb_spec; try eapply HLT; eauto. }
            { inv H4; auto; congruence. }
            { auto. }
            { intros; eapply mask_spec. exact HA. auto. }
            { intros. rewrite (proj1 (mask_spec _ _ _ HA)); auto. }
            { auto. }
            { auto. }
          * rewrite <- H0. econstructor; trivial.
            { eapply mask_spec'; eauto. }
            { eassumption. }
            { assumption. }
            { assumption. }
            { eapply mask_spec; eauto. }
            { eapply mask_spec; eauto. }
            { assumption. }
            { assumption. }
    Qed.

    Lemma combine_aux_combine':
      forall {A: Type} c prefix brbit t1_1 t1_2 (t2: ptrie A),
        combine' c (Branch prefix brbit t1_1 t1_2) t2 = 
        ((fix combine_aux (t2 : ptrie A) : ptrie A :=
            match t2 with
            | Empty => Branch prefix brbit t1_1 t1_2
            | Leaf i x =>
              if match_prefix i prefix brbit
              then
                if zerobit i brbit
                then Branch prefix brbit (insert' (fun a b : A => c b a) i x t1_1) t1_2
                else Branch prefix brbit t1_1 (insert' (fun a b : A => c b a) i x t1_2)
              else join i (Leaf i x) prefix (Branch prefix brbit t1_1 t1_2)
            | Branch p2 m2 l2 r2 =>
              if eqb prefix p2 && eqb brbit m2
              then Branch prefix brbit (combine' c t1_1 l2) (combine' c t1_2 r2)
              else
                if ltb brbit m2 && match_prefix p2 prefix brbit
                then
                  if zerobit p2 brbit
                  then Branch prefix brbit (combine' c t1_1 t2) t1_2
                  else Branch prefix brbit t1_1 (combine' c t1_2 t2)
                else
                  if ltb m2 brbit && match_prefix prefix p2 m2
                  then if zerobit prefix m2 then Branch p2 m2 (combine_aux l2) r2 else Branch p2 m2 l2 (combine_aux r2)
                  else join prefix (Branch prefix brbit t1_1 t1_2) p2 t2
            end) t2).
    Proof.
      intros; unfold combine'.
      fold (@combine' A).
      unfold insert'; fold (@insert' A). reflexivity.
    Qed.

    Lemma wf_combine':
      forall (A: Type) c (t1 t2: ptrie A) opt,
        wf opt t1 ->
        wf opt t2 ->
        wf opt (combine' c t1 t2).
    Proof.
      induction t1; induction t2; intros.
      - simpl; econstructor.
      - simpl; auto.
      - simpl; auto.
      - simpl; auto.
      - simpl. destruct_eq k k0.
        + inv H; econstructor; eauto.
        + eapply wf_join_Leaf; eauto.
      - unfold combine'. eapply wf_insert'; eauto.
      - simpl; auto.
      - unfold combine'. eapply wf_insert'; eauto.
      - simpl. erewrite <- ! (combine_aux_combine' c prefix brbit t1_1 t1_2 t2_2).
        erewrite <- ! (combine_aux_combine' c prefix brbit t1_1 t1_2 t2_1).
        Local Opaque combine'. destruct_eq brbit brbit0.
        + destruct_eq prefix prefix0.
          * simpl; subst. inv H; inv H0; econstructor; eauto.
            { eapply combine'_not_empty. left; auto. }
            { eapply combine'_not_empty. left; auto. }
            { eapply IHt1_1; eauto. assert (brbit'0 = brbit').
              - generalize (proj2 (Hbrbit'0 _) eq_refl). intros; symmetry; eapply Hbrbit'; auto.
              - subst; auto. }
            { eapply IHt1_2; eauto. assert (brbit'0 = brbit').
              - generalize (proj2 (Hbrbit'0 _) eq_refl). intros; symmetry; eapply Hbrbit'; auto.
              - subst; auto. }
            { eapply combine'_not_empty. left; auto. }
            { eapply combine'_not_empty. left; auto. }
            { eapply IHt1_1; eauto. assert (brbit'0 = brbit').
              - generalize (proj2 (Hbrbit'0 _) eq_refl). intros; symmetry; eapply Hbrbit'; auto.
              - subst; auto. }
            { eapply IHt1_2; eauto. assert (brbit'0 = brbit').
              - generalize (proj2 (Hbrbit'0 _) eq_refl). intros; symmetry; eapply Hbrbit'; auto.
              - subst; auto. }
          * subst. case_eq (ltb brbit0 brbit0); intros.
            { inv H; inv H0; eapply ltb_spec in H1; eauto; lia. }
            { simpl. eapply wf_join_Branch_Branch_0; eauto. }
        + case_eq (ltb brbit brbit0); intros.
          * case_eq (match_prefix prefix0 prefix brbit); intros.
            { rewrite andb_comm. simpl. case_eq (zerobit prefix0 brbit); intros.
              - inv H; inv H0; econstructor; trivial.
                + eapply combine'_not_empty; eauto; right; discriminate.
                + exact Hincr.
                + assumption.
                + assumption.
                + eapply IHt1_1; eauto. econstructor; try eassumption.
                  * eapply ltb_spec; eauto.
                  * generalize (proj1 (match_prefix_spec _ _ _ _ Hbrbit' Hmask') H2).
                    intros; symmetry; eapply H; eauto.
                + assumption.
                + eapply combine'_not_empty; eauto; right; discriminate.
                + eassumption.
                + assumption.
                + eapply IHt1_1; eauto. econstructor; try eassumption.
                  * inv H7; auto; congruence.
                  * inv H6; auto; congruence.
                  * eapply ltb_spec; eauto.
                  * assert (Hmask': mask prefix brbit = prefix) by (inv H7; auto; congruence).
                    generalize (proj1 (match_prefix_spec _ _ _ _ Hbrbit' Hmask') H2).
                    intros; symmetry; eapply H; eauto.
                + assumption.
              - inv H; inv H0; econstructor; trivial.
                + eapply combine'_not_empty; eauto; right; discriminate.
                + exact Hincr.
                + assumption.
                + assumption.
                + assumption.
                + eapply IHt1_2; eauto. econstructor; try eassumption.
                  * eapply ltb_spec; eauto.
                  * generalize (proj1 (match_prefix_spec _ _ _ _ Hbrbit' Hmask') H2).
                    intros; symmetry; eapply H; eauto.
                + eapply combine'_not_empty; eauto; right; discriminate.
                + eassumption.
                + assumption.
                + assumption.
                + eapply IHt1_2; eauto. econstructor; try eassumption.
                  * inv H7; auto; congruence.
                  * inv H6; auto; congruence.
                  * eapply ltb_spec; eauto.
                  * assert (Hmask': mask prefix brbit = prefix) by (inv H7; auto; congruence).
                    generalize (proj1 (match_prefix_spec _ _ _ _ Hbrbit' Hmask') H2).
                    intros; symmetry; eapply H; eauto. }
            { rewrite andb_comm; simpl.
              case_eq (ltb brbit0 brbit); intros.
              - inv H; inv H0.
                + eapply ltb_spec in H1; eauto.
                  eapply ltb_spec in H3; eauto.
                  assert (brbit'0 = brbit') by lia. subst.
                  elim n. eapply testbit_spec; intros.
                  case_eq (testbit brbit n0); case_eq (testbit brbit0 n0); intros; auto.
                  * eapply Hbrbit' in H0. subst n0.
                    generalize (proj2 (Hbrbit'0 _) eq_refl); intros; congruence.
                  * eapply Hbrbit'0 in H. subst n0.
                    generalize (proj2 (Hbrbit' _) eq_refl); intros; congruence.
                + eapply ltb_spec in H1; eauto.
                  eapply ltb_spec in H3; eauto.
                  assert (brbit'0 = brbit') by lia. subst.
                  elim n. eapply testbit_spec; intros.
                  case_eq (testbit brbit n0); case_eq (testbit brbit0 n0); intros; auto.
                  * eapply Hbrbit' in H0. subst n0.
                    generalize (proj2 (Hbrbit'0 _) eq_refl); intros; congruence.
                  * eapply Hbrbit'0 in H. subst n0.
                    generalize (proj2 (Hbrbit' _) eq_refl); intros; congruence.
              - simpl. eapply wf_join_Branch_Branch_2; eauto. }
          * rewrite andb_comm; simpl.
            case_eq (ltb brbit0 brbit); intros.
            { case_eq (match_prefix prefix prefix0 brbit0); intros.
              - simpl. case_eq (zerobit prefix brbit0); intros.
                + inv H; inv H0; econstructor; eauto.
                  * eapply combine'_not_empty; eauto; left; discriminate.
                  * eapply IHt2_1; eauto.
                    econstructor; try eassumption.
                    { eapply ltb_spec; eauto. }
                    { generalize (proj1 (match_prefix_spec _ _ _ _ Hbrbit'0 Hmask'0) H3).
                      intros; symmetry; eapply H; eauto. }
                  * eapply combine'_not_empty; eauto; left; discriminate.
                  * eapply IHt2_1; eauto.
                    econstructor; try eassumption.
                    { inv H7; auto; congruence. }
                    { inv H8; auto; congruence. }
                    { eapply ltb_spec; eauto. }
                    { assert (Hmask'0: mask prefix0 brbit0 = prefix0) by (inv H7; auto; congruence).
                      generalize (proj1 (match_prefix_spec _ _ _ _ Hbrbit'0 Hmask'0) H3).
                      intros; symmetry; eapply H; eauto. }
                + inv H; inv H0; econstructor; eauto.
                  * eapply combine'_not_empty; eauto; left; discriminate.
                  * eapply IHt2_2; eauto.
                    econstructor; try eassumption.
                    { eapply ltb_spec; eauto. }
                    { generalize (proj1 (match_prefix_spec _ _ _ _ Hbrbit'0 Hmask'0) H3).
                      intros; symmetry; eapply H; eauto. }
                  * eapply combine'_not_empty; eauto; left; discriminate.
                  * eapply IHt2_2; eauto.
                    econstructor; try eassumption.
                    { inv H7; auto; congruence. }
                    { inv H8; auto; congruence. }
                    { eapply ltb_spec; eauto. }
                    { assert (Hmask'0: mask prefix0 brbit0 = prefix0) by (inv H7; auto; congruence).
                      generalize (proj1 (match_prefix_spec _ _ _ _ Hbrbit'0 Hmask'0) H3).
                      intros; symmetry; eapply H; eauto. }
              - simpl. eapply wf_join_Branch_Branch_1; eauto. }
            { inv H; inv H0.
              - destruct (eq_nat_dec brbit'0 brbit').
                + subst. elim n. eapply testbit_spec; intros.
                  case_eq (testbit brbit n0); case_eq (testbit brbit0 n0); intros; auto.
                  * eapply Hbrbit' in H0. subst n0.
                    generalize (proj2 (Hbrbit'0 _) eq_refl); intros; congruence.
                  * eapply Hbrbit'0 in H. subst n0.
                    generalize (proj2 (Hbrbit' _) eq_refl); intros; congruence.
                + destruct (lt_dec brbit' brbit'0).
                  * generalize (proj2 (ltb_spec _ _ _ _ Hbrbit' Hbrbit'0) l).
                    intros;  congruence.
                  * assert (brbit'0 < brbit')%nat by lia.
                    generalize (proj2 (ltb_spec _ _ _ _ Hbrbit'0 Hbrbit') H).
                    intros; congruence.
              - destruct (eq_nat_dec brbit'0 brbit').
                + subst. elim n. eapply testbit_spec; intros.
                  case_eq (testbit brbit n0); case_eq (testbit brbit0 n0); intros; auto.
                  * eapply Hbrbit' in H0. subst n0.
                    generalize (proj2 (Hbrbit'0 _) eq_refl); intros; congruence.
                  * eapply Hbrbit'0 in H. subst n0.
                    generalize (proj2 (Hbrbit' _) eq_refl); intros; congruence.
                + destruct (lt_dec brbit' brbit'0).
                  * generalize (proj2 (ltb_spec _ _ _ _ Hbrbit' Hbrbit'0) l).
                    intros; congruence.
                  * assert (brbit'0 < brbit')%nat by lia.
                    generalize (proj2 (ltb_spec _ _ _ _ Hbrbit'0 Hbrbit') H).
                    intros; congruence. }
    Qed.

    Local Transparent combine'.
    Local Opaque insert'.

    Lemma gcombine':
      forall (A: Type) (c: A -> A -> A) (t1 t2: ptrie A) opt i,
        wf opt t1 ->
        wf opt t2 ->
        get' i (combine' c t1 t2) = match get' i t1, get' i t2 with
                                    | None, None => None
                                    | None, Some x2 => Some x2
                                    | Some x1, None => Some x1
                                    | Some x1, Some x2 => Some (c x1 x2)
                                    end.
    Proof.
      induction t1; induction t2; intros; simpl; try reflexivity.
      - destruct_eq i k; simpl; auto.
      - case_eq (zerobit i brbit); intros; simpl; auto.
        + destruct (get' i t2_1); auto.
        + destruct (get' i t2_2); auto.
      - destruct_eq i k; simpl; auto.
      - destruct_eq i k.
        + subst. eapply gis'. eauto.
        + erewrite gio'; eauto. simpl.
          destruct_eq i k0; auto.
      - destruct_eq i k.
        + subst. eapply gis'; eauto.
        + erewrite gio'; eauto. simpl.
          destruct (zerobit i brbit); destruct (get' i t2_1); destruct (get' i t2_2); auto.
      - destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); auto.
      - destruct_eq i k.
        + subst; eapply gis'; eauto.
        + erewrite gio'; eauto. simpl.
          destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); auto.
      - rewrite andb_comm. Local Transparent insert'. simpl.
        erewrite <- ! (combine_aux_combine' c prefix brbit t1_1 t1_2 t2_2).
        erewrite <- ! (combine_aux_combine' c prefix brbit t1_1 t1_2 t2_1).
        Local Opaque combine'.
        destruct_eq brbit brbit0.
        + destruct_eq prefix prefix0.
          * simpl. subst. inv H; inv H0.
            { case_eq (zerobit i brbit0); intros.
              - eapply IHt1_1; eauto. 
                replace brbit' with brbit'0; auto.
                symmetry; eapply Hbrbit'. eapply (proj2 (Hbrbit'0 _) eq_refl).
              - eapply IHt1_2; eauto.
                replace brbit' with brbit'0; auto.
                symmetry; eapply Hbrbit'. eapply (proj2 (Hbrbit'0 _) eq_refl). }
            { case_eq (zerobit i brbit0); intros.
              - eapply IHt1_1; eauto. 
                replace brbit' with brbit'0; auto.
                symmetry; eapply Hbrbit'. eapply (proj2 (Hbrbit'0 _) eq_refl).
              - eapply IHt1_2; eauto.
                replace brbit' with brbit'0; auto.
                symmetry; eapply Hbrbit'. eapply (proj2 (Hbrbit'0 _) eq_refl). }
          * subst. simpl. case_eq (ltb brbit0 brbit0); intros.
            { inv H; eapply ltb_spec in H1; eauto; lia. }
            { simpl. unfold join; auto. case_eq (zerobit prefix (branching_bit prefix prefix0)); intros.
              - simpl. case_eq (zerobit i (branching_bit prefix prefix0)); intros.
                + case_eq (zerobit i brbit0); intros.
                  * inv H; inv H0.
                    { generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                      generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                      subst brbit'0. destruct (lt_dec n' brbit').
                      - assert (get' i t2_1 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_true_iff in H2. eapply negb_true_iff in H3.
                          rewrite H3; destruct (testbit prefix n'); congruence.
                        + rewrite H. destruct (get' i t1_1); auto.
                      - elim HC. rewrite Hlength; try lia.
                        rewrite Hlength0; try lia; auto. }
                    { generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                      generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                      subst brbit'0. destruct (lt_dec n' brbit').
                      - assert (get' i t2_1 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_true_iff in H2. eapply negb_true_iff in H3.
                          rewrite H3; destruct (testbit prefix n'); congruence.
                        + rewrite H. destruct (get' i t1_1); auto.
                      - elim HC. assert (Hlength: forall n, (n >= brbit')%nat -> testbit prefix n = false) by (inv H8; auto; congruence).
                        assert (Hlength0: forall n, (n >= brbit')%nat -> testbit prefix0 n = false) by (inv H7; auto; congruence).
                        rewrite Hlength; try lia.
                        rewrite Hlength0; try lia; auto. }
                  * inv H; inv H0.
                    { generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                      generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                      subst brbit'0. destruct (lt_dec n' brbit').
                      - assert (get' i t2_2 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_true_iff in H2. eapply negb_true_iff in H3.
                          rewrite H3; destruct (testbit prefix n'); congruence.
                        + rewrite H. destruct (get' i t1_2); auto.
                      - elim HC. rewrite Hlength; try lia.
                        rewrite Hlength0; try lia; auto. }
                    { generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                      generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                      subst brbit'0. destruct (lt_dec n' brbit').
                      - assert (get' i t2_2 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_true_iff in H2. eapply negb_true_iff in H3.
                          rewrite H3; destruct (testbit prefix n'); congruence.
                        + rewrite H. destruct (get' i t1_2); auto.
                      - elim HC. assert (Hlength: forall n, (n >= brbit')%nat -> testbit prefix n = false) by (inv H8; auto; congruence).
                        assert (Hlength0: forall n, (n >= brbit')%nat -> testbit prefix0 n = false) by (inv H7; auto; congruence).
                        rewrite Hlength; try lia.
                        rewrite Hlength0; try lia; auto. }
                + inv H; inv H0.
                  * generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                    generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                    subst brbit'0. destruct (lt_dec n' brbit').
                    { assert (get' i t1_1 = None).
                      - eapply get_not_same_prefix; eauto.
                        erewrite zerobit_spec in H2; eauto.
                        erewrite zerobit_spec in H3; eauto.
                        eapply negb_true_iff in H2. eapply negb_false_iff in H3. congruence.
                      - assert (get' i t1_2 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_true_iff in H2. eapply negb_false_iff in H3. congruence.
                        + rewrite H, H0. destruct (zerobit i brbit0); destruct (get' i t2_1); destruct (get' i t2_2); auto. }
                    { elim HC. rewrite Hlength; try lia. rewrite Hlength0; lia. }
                  * generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                    generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                    subst brbit'0. destruct (lt_dec n' brbit').
                    { assert (get' i t1_1 = None).
                      - eapply get_not_same_prefix; eauto.
                        erewrite zerobit_spec in H2; eauto.
                        erewrite zerobit_spec in H3; eauto.
                        eapply negb_true_iff in H2. eapply negb_false_iff in H3. congruence.
                      - assert (get' i t1_2 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_true_iff in H2. eapply negb_false_iff in H3. congruence.
                        + rewrite H, H0. destruct (zerobit i brbit0); destruct (get' i t2_1); destruct (get' i t2_2); auto. }
                    { elim HC. assert (Hlength: forall n, (n >= brbit')%nat -> testbit prefix n = false) by (inv H7; auto; congruence).
                      assert (Hlength0: forall n, (n >= brbit')%nat -> testbit prefix0 n = false) by (inv H6; auto; congruence).
                      rewrite Hlength; try lia. rewrite Hlength0; lia.  }
              - simpl. case_eq (zerobit i (branching_bit prefix prefix0)); intros.
                + case_eq (zerobit i brbit0); intros.
                  * inv H; inv H0.
                    { generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                      generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                      subst brbit'0. destruct (lt_dec n' brbit').
                      - assert (get' i t1_1 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_false_iff in H2. eapply negb_true_iff in H3.
                          rewrite H3; destruct (testbit prefix n'); congruence.
                        + rewrite H. destruct (get' i t2_1); auto.
                      - elim HC. rewrite Hlength; try lia.
                        rewrite Hlength0; try lia; auto. }
                    { generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                      generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                      subst brbit'0. destruct (lt_dec n' brbit').
                      - assert (get' i t1_1 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_false_iff in H2. eapply negb_true_iff in H3.
                          rewrite H3; destruct (testbit prefix n'); congruence.
                        + rewrite H. destruct (get' i t2_1); auto.
                      - elim HC. assert (Hlength: forall n, (n >= brbit')%nat -> testbit prefix n = false) by (inv H8; auto; congruence).
                        assert (Hlength0: forall n, (n >= brbit')%nat -> testbit prefix0 n = false) by (inv H7; auto; congruence).
                        rewrite Hlength; try lia.
                        rewrite Hlength0; try lia; auto. }
                  * inv H; inv H0.
                    { generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                      generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                      subst brbit'0. destruct (lt_dec n' brbit').
                      - assert (get' i t1_2 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_false_iff in H2. eapply negb_true_iff in H3.
                          rewrite H3; destruct (testbit prefix n'); congruence.
                        + rewrite H. destruct (get' i t2_2); auto.
                      - elim HC. rewrite Hlength; try lia.
                        rewrite Hlength0; try lia; auto. }
                    { generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                      generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                      subst brbit'0. destruct (lt_dec n' brbit').
                      - assert (get' i t1_2 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_false_iff in H2. eapply negb_true_iff in H3.
                          rewrite H3; destruct (testbit prefix n'); congruence.
                        + rewrite H. destruct (get' i t2_2); auto.
                      - elim HC. assert (Hlength: forall n, (n >= brbit')%nat -> testbit prefix n = false) by (inv H8; auto; congruence).
                        assert (Hlength0: forall n, (n >= brbit')%nat -> testbit prefix0 n = false) by (inv H7; auto; congruence).
                        rewrite Hlength; try lia.
                        rewrite Hlength0; try lia; auto. }
                + inv H; inv H0.
                  * generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                    generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                    subst brbit'0. destruct (lt_dec n' brbit').
                    { assert (get' i t2_1 = None).
                      - eapply get_not_same_prefix; eauto.
                        erewrite zerobit_spec in H2; eauto.
                        erewrite zerobit_spec in H3; eauto.
                        eapply negb_false_iff in H2. eapply negb_false_iff in H3. congruence.
                      - assert (get' i t2_2 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_false_iff in H2. eapply negb_false_iff in H3. congruence.
                        + rewrite H, H0. destruct (zerobit i brbit0); destruct (get' i t1_1); destruct (get' i t1_2); auto. }
                    { elim HC. rewrite Hlength; try lia. rewrite Hlength0; lia. }
                  * generalize (branching_bit_spec _ _ n). intros [n' [HA [HB HC]]].
                    generalize (proj2 (Hbrbit'0 _) eq_refl); intros HD; eapply Hbrbit' in HD.
                    subst brbit'0. destruct (lt_dec n' brbit').
                    { assert (get' i t2_1 = None).
                      - eapply get_not_same_prefix; eauto.
                        erewrite zerobit_spec in H2; eauto.
                        erewrite zerobit_spec in H3; eauto.
                        eapply negb_false_iff in H2. eapply negb_false_iff in H3. congruence.
                      - assert (get' i t2_2 = None).
                        + eapply get_not_same_prefix; eauto.
                          erewrite zerobit_spec in H2; eauto.
                          erewrite zerobit_spec in H3; eauto.
                          eapply negb_false_iff in H2. eapply negb_false_iff in H3. congruence.
                        + rewrite H, H0. destruct (zerobit i brbit0); destruct (get' i t1_1); destruct (get' i t1_2); auto. }
                    { elim HC. assert (Hlength: forall n, (n >= brbit')%nat -> testbit prefix n = false) by (inv H7; auto; congruence).
                      assert (Hlength0: forall n, (n >= brbit')%nat -> testbit prefix0 n = false) by (inv H6; auto; congruence).
                      rewrite Hlength; try lia. rewrite Hlength0; lia. } }
        + simpl. case_eq (ltb brbit brbit0); intros.
          * case_eq (match_prefix prefix0 prefix brbit); intros; simpl.
            { case_eq (zerobit prefix0 brbit); intros.
              - simpl. case_eq (zerobit i brbit); intros.
                + erewrite IHt1_1; eauto. generalize H; intros HO. inv H.
                  * eapply (wf_Some_Branch HO); eauto.
                  * eapply wf_Some_None; eauto.
                + inv H; inv H0.
                  * erewrite zerobit_spec in H3; eauto.
                    erewrite zerobit_spec in H4; eauto.
                    apply negb_true_iff in H3. apply negb_false_iff in H4.
                    generalize (proj1 (ltb_spec _ _ _ _ Hbrbit' Hbrbit'0) H1). intros HLT.
                    assert (get' i t2_1 = None).
                    { eapply get_not_same_prefix; eauto. congruence. }
                    assert (get' i t2_2 = None).
                    { eapply get_not_same_prefix; eauto. congruence. }
                    rewrite H, H0. destruct (zerobit i brbit0); destruct (get' i t1_2); auto.
                  * erewrite zerobit_spec in H3; eauto.
                    erewrite zerobit_spec in H4; eauto.
                    apply negb_true_iff in H3. apply negb_false_iff in H4.
                    generalize (proj1 (ltb_spec _ _ _ _ Hbrbit' Hbrbit'0) H1). intros HLT.
                    assert (get' i t2_1 = None).
                    { eapply get_not_same_prefix; eauto. congruence. }
                    assert (get' i t2_2 = None).
                    { eapply get_not_same_prefix; eauto. congruence. }
                    rewrite H, H0. destruct (zerobit i brbit0); destruct (get' i t1_2); auto.
              - simpl. case_eq (zerobit i brbit); intros.
                + inv H; inv H0.
                  * erewrite zerobit_spec in H3; eauto.
                    erewrite zerobit_spec in H4; eauto.
                    apply negb_false_iff in H3. apply negb_true_iff in H4.
                    generalize (proj1 (ltb_spec _ _ _ _ Hbrbit' Hbrbit'0) H1). intros HLT.
                    assert (get' i t2_1 = None).
                    { eapply get_not_same_prefix; eauto. congruence. }
                    assert (get' i t2_2 = None).
                    { eapply get_not_same_prefix; eauto. congruence. }
                    rewrite H, H0. destruct (zerobit i brbit0); destruct (get' i t1_1); auto.
                  * erewrite zerobit_spec in H3; eauto.
                    erewrite zerobit_spec in H4; eauto.
                    apply negb_false_iff in H3. apply negb_true_iff in H4.
                    generalize (proj1 (ltb_spec _ _ _ _ Hbrbit' Hbrbit'0) H1). intros HLT.
                    assert (get' i t2_1 = None).
                    { eapply get_not_same_prefix; eauto. congruence. }
                    assert (get' i t2_2 = None).
                    { eapply get_not_same_prefix; eauto. congruence. }
                    rewrite H, H0. destruct (zerobit i brbit0); destruct (get' i t1_1); auto.
                + erewrite IHt1_2; eauto. generalize H; intros HO. inv H.
                  * eapply (wf_Some_Branch HO); eauto.
                  * eapply wf_Some_None; eauto. }
            { case_eq (ltb brbit0 brbit); intros.
              - inv H; inv H0; eapply ltb_spec in H1; eauto; eapply ltb_spec in H3; eauto; lia.
              - simpl. inv H; inv H0.
                + generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [Hne [n' [HLT Hbr]]].
                  generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                  eapply HA in Hbr. subst n''. unfold join; simpl.
                  case_eq (zerobit prefix (branching_bit prefix prefix0)); intros.
                  * simpl. case_eq (zerobit i (branching_bit prefix prefix0)); intros.
                    { assert (get' i t2_1 = None).
                      - rewrite branching_bit_sym in HA.
                        erewrite zerobit_spec in H; eauto.
                        erewrite zerobit_spec in H0; eauto.
                        apply negb_true_iff in H; apply negb_true_iff in H0.
                        eapply get_not_same_prefix with (n := n'); eauto.
                        eapply lt_trans; eauto. eapply ltb_spec; eauto.
                      - assert (get' i t2_2 = None).
                        + rewrite branching_bit_sym in HA.
                          erewrite zerobit_spec in H; eauto.
                          erewrite zerobit_spec in H0; eauto.
                          apply negb_true_iff in H; apply negb_true_iff in H0.
                          eapply get_not_same_prefix with (n := n'); eauto.
                          eapply lt_trans; eauto. eapply ltb_spec; eauto.
                        + rewrite H4, H6. destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); destruct (zerobit i brbit0); auto. }
                    { assert (get' i t1_1 = None).
                      - rewrite branching_bit_sym in HA.
                        erewrite zerobit_spec in H; eauto.
                        erewrite zerobit_spec in H0; eauto.
                        apply negb_true_iff in H; apply negb_false_iff in H0.
                        eapply get_not_same_prefix with (n := n'); eauto. congruence.
                      - assert (get' i t1_2 = None).
                        + rewrite branching_bit_sym in HA.
                          erewrite zerobit_spec in H; eauto.
                          erewrite zerobit_spec in H0; eauto.
                          apply negb_true_iff in H; apply negb_false_iff in H0.
                          eapply get_not_same_prefix with (n := n'); eauto. congruence.
                        + rewrite H4, H6. destruct (if zerobit i brbit0 then get' i t2_1 else get' i t2_2); destruct (zerobit i brbit); auto. }
                  * simpl. case_eq (zerobit i (branching_bit prefix prefix0)); intros.
                    { assert (get' i t1_1 = None).
                      - rewrite branching_bit_sym in HA.
                        erewrite zerobit_spec in H; eauto.
                        erewrite zerobit_spec in H0; eauto.
                        apply negb_false_iff in H; apply negb_true_iff in H0.
                        eapply get_not_same_prefix with (n := n'); eauto. congruence.
                      - assert (get' i t1_2 = None).
                        + rewrite branching_bit_sym in HA.
                          erewrite zerobit_spec in H; eauto.
                          erewrite zerobit_spec in H0; eauto.
                          apply negb_false_iff in H; apply negb_true_iff in H0.
                          eapply get_not_same_prefix with (n := n'); eauto. congruence.
                        + rewrite H4, H6. destruct (if zerobit i brbit0 then get' i t2_1 else get' i t2_2); destruct (zerobit i brbit); auto. }
                    { assert (get' i t2_1 = None).
                      - rewrite branching_bit_sym in HA.
                        erewrite zerobit_spec in H; eauto.
                        erewrite zerobit_spec in H0; eauto.
                        apply negb_false_iff in H; apply negb_false_iff in H0.
                        eapply get_not_same_prefix with (n := n'); eauto.
                        eapply lt_trans; eauto. eapply ltb_spec; eauto.
                      - assert (get' i t2_2 = None).
                        + rewrite branching_bit_sym in HA.
                          erewrite zerobit_spec in H; eauto.
                          erewrite zerobit_spec in H0; eauto.
                          apply negb_false_iff in H; apply negb_false_iff in H0.
                          eapply get_not_same_prefix with (n := n'); eauto.
                          eapply lt_trans; eauto. eapply ltb_spec; eauto.
                        + rewrite H4, H6. destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); destruct (zerobit i brbit0); auto. }
                + assert (Hmask': mask prefix brbit = prefix) by (inv H7; auto; congruence).
                  generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit' Hmask') H2). intros [Hne [n' [HLT Hbr]]].
                  generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                  eapply HA in Hbr. subst n''. unfold join; simpl.
                  case_eq (zerobit prefix (branching_bit prefix prefix0)); intros.
                  * simpl. case_eq (zerobit i (branching_bit prefix prefix0)); intros.
                    { assert (get' i t2_1 = None).
                      - rewrite branching_bit_sym in HA.
                        erewrite zerobit_spec in H; eauto.
                        erewrite zerobit_spec in H0; eauto.
                        apply negb_true_iff in H; apply negb_true_iff in H0.
                        eapply get_not_same_prefix with (n := n'); eauto.
                        eapply lt_trans; eauto. eapply ltb_spec; eauto.
                      - assert (get' i t2_2 = None).
                        + rewrite branching_bit_sym in HA.
                          erewrite zerobit_spec in H; eauto.
                          erewrite zerobit_spec in H0; eauto.
                          apply negb_true_iff in H; apply negb_true_iff in H0.
                          eapply get_not_same_prefix with (n := n'); eauto.
                          eapply lt_trans; eauto. eapply ltb_spec; eauto.
                        + rewrite H4, H5. destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); destruct (zerobit i brbit0); auto. }
                    { assert (get' i t1_1 = None).
                      - rewrite branching_bit_sym in HA.
                        erewrite zerobit_spec in H; eauto.
                        erewrite zerobit_spec in H0; eauto.
                        apply negb_true_iff in H; apply negb_false_iff in H0.
                        eapply get_not_same_prefix with (n := n'); eauto. congruence.
                      - assert (get' i t1_2 = None).
                        + rewrite branching_bit_sym in HA.
                          erewrite zerobit_spec in H; eauto.
                          erewrite zerobit_spec in H0; eauto.
                          apply negb_true_iff in H; apply negb_false_iff in H0.
                          eapply get_not_same_prefix with (n := n'); eauto. congruence.
                        + rewrite H4, H5. destruct (if zerobit i brbit0 then get' i t2_1 else get' i t2_2); destruct (zerobit i brbit); auto. }
                  * simpl. case_eq (zerobit i (branching_bit prefix prefix0)); intros.
                    { assert (get' i t1_1 = None).
                      - rewrite branching_bit_sym in HA.
                        erewrite zerobit_spec in H; eauto.
                        erewrite zerobit_spec in H0; eauto.
                        apply negb_false_iff in H; apply negb_true_iff in H0.
                        eapply get_not_same_prefix with (n := n'); eauto. congruence.
                      - assert (get' i t1_2 = None).
                        + rewrite branching_bit_sym in HA.
                          erewrite zerobit_spec in H; eauto.
                          erewrite zerobit_spec in H0; eauto.
                          apply negb_false_iff in H; apply negb_true_iff in H0.
                          eapply get_not_same_prefix with (n := n'); eauto. congruence.
                        + rewrite H4, H5. destruct (if zerobit i brbit0 then get' i t2_1 else get' i t2_2); destruct (zerobit i brbit); auto. }
                    { assert (get' i t2_1 = None).
                      - rewrite branching_bit_sym in HA.
                        erewrite zerobit_spec in H; eauto.
                        erewrite zerobit_spec in H0; eauto.
                        apply negb_false_iff in H; apply negb_false_iff in H0.
                        eapply get_not_same_prefix with (n := n'); eauto.
                        eapply lt_trans; eauto. eapply ltb_spec; eauto.
                      - assert (get' i t2_2 = None).
                        + rewrite branching_bit_sym in HA.
                          erewrite zerobit_spec in H; eauto.
                          erewrite zerobit_spec in H0; eauto.
                          apply negb_false_iff in H; apply negb_false_iff in H0.
                          eapply get_not_same_prefix with (n := n'); eauto.
                          eapply lt_trans; eauto. eapply ltb_spec; eauto.
                        + rewrite H4, H5. destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); destruct (zerobit i brbit0); auto. } }
          * simpl. case_eq (ltb brbit0 brbit); intros.
            { case_eq (match_prefix prefix prefix0 brbit0); intros; simpl.
              - case_eq (zerobit prefix brbit0); intros.
                + simpl. case_eq (zerobit i brbit0); intros.
                  * generalize H0; intros HO. inv H0; eapply IHt2_1; eauto.
                    { eapply (wf_Some_Branch HO). }
                    { eapply wf_Some_None; eauto. }
                  * inv H; inv H0.
                    { erewrite zerobit_spec in H4; eauto.
                      erewrite zerobit_spec in H5; eauto.
                      apply negb_true_iff in H4. apply negb_false_iff in H5.
                      generalize (proj1 (ltb_spec _ _ _ _ Hbrbit'0 Hbrbit') H2). intros HLT.
                      assert (get' i t1_1 = None).
                      { eapply get_not_same_prefix; eauto. congruence. }
                      assert (get' i t1_2 = None).
                      { eapply get_not_same_prefix; eauto. congruence. }
                      rewrite H, H0. destruct (zerobit i brbit); destruct (get' i t2_2); auto. }
                    { erewrite zerobit_spec in H4; eauto.
                      erewrite zerobit_spec in H5; eauto.
                      apply negb_true_iff in H4. apply negb_false_iff in H5.
                      generalize (proj1 (ltb_spec _ _ _ _ Hbrbit'0 Hbrbit') H2). intros HLT.
                      assert (get' i t1_1 = None).
                      { eapply get_not_same_prefix; eauto. congruence. }
                      assert (get' i t1_2 = None).
                      { eapply get_not_same_prefix; eauto. congruence. }
                      rewrite H, H0. destruct (zerobit i brbit); destruct (get' i t2_2); auto. }
                + simpl. case_eq (zerobit i brbit0); intros.
                  * inv H; inv H0.
                    { erewrite zerobit_spec in H4; eauto.
                      erewrite zerobit_spec in H5; eauto.
                      apply negb_false_iff in H4. apply negb_true_iff in H5.
                      generalize (proj1 (ltb_spec _ _ _ _ Hbrbit'0 Hbrbit') H2). intros HLT.
                      assert (get' i t1_1 = None).
                      { eapply get_not_same_prefix; eauto. congruence. }
                      assert (get' i t1_2 = None).
                      { eapply get_not_same_prefix; eauto. congruence. }
                      rewrite H, H0. destruct (zerobit i brbit); destruct (get' i t2_1); auto. }
                    { erewrite zerobit_spec in H4; eauto.
                      erewrite zerobit_spec in H5; eauto.
                      apply negb_false_iff in H4. apply negb_true_iff in H5.
                      generalize (proj1 (ltb_spec _ _ _ _ Hbrbit'0 Hbrbit') H2). intros HLT.
                      assert (get' i t1_1 = None).
                      { eapply get_not_same_prefix; eauto. congruence. }
                      assert (get' i t1_2 = None).
                      { eapply get_not_same_prefix; eauto. congruence. }
                      rewrite H, H0. destruct (zerobit i brbit); destruct (get' i t2_1); auto. }
                  * generalize H0; intros HO. inv H0; eapply IHt2_2; eauto.
                    { eapply (wf_Some_Branch HO). }
                    { eapply wf_Some_None; eauto. }
              - unfold join; simpl. case_eq (zerobit prefix (branching_bit prefix prefix0)); simpl; intros.
                + case_eq (zerobit i (branching_bit prefix prefix0)); intros.
                  * inv H; inv H0.
                    { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) H3). intros [Hne [n' [HLT Hbr]]].
                      generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                      eapply HA in Hbr. subst n''. 
                      assert (get' i t2_1 = None).
                      - erewrite zerobit_spec in H4; eauto.
                        erewrite zerobit_spec in H5; eauto.
                        apply negb_true_iff in H4; apply negb_true_iff in H5.
                        eapply get_not_same_prefix with (n := n'); eauto.
                      - assert (get' i t2_2 = None).
                        + erewrite zerobit_spec in H4; eauto.
                          erewrite zerobit_spec in H5; eauto.
                          apply negb_true_iff in H4; apply negb_true_iff in H5.
                          eapply get_not_same_prefix with (n := n'); eauto.
                        + rewrite H, H0. destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); destruct (zerobit i brbit0); auto. }
                    { assert (Hmask'0: mask prefix0 brbit0 = prefix0) by (inv H8; auto; congruence).
                      generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) H3). intros [Hne [n' [HLT Hbr]]].
                      generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                      eapply HA in Hbr. subst n''. 
                      assert (get' i t2_1 = None).
                      - erewrite zerobit_spec in H4; eauto.
                        erewrite zerobit_spec in H5; eauto.
                        apply negb_true_iff in H4; apply negb_true_iff in H5.
                        eapply get_not_same_prefix with (n := n'); eauto.
                      - assert (get' i t2_2 = None).
                        + erewrite zerobit_spec in H4; eauto.
                          erewrite zerobit_spec in H5; eauto.
                          apply negb_true_iff in H4; apply negb_true_iff in H5.
                          eapply get_not_same_prefix with (n := n'); eauto.
                        + rewrite H, H0. destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); destruct (zerobit i brbit0); auto. }
                  * inv H; inv H0.
                    { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) H3). intros [Hne [n' [HLT Hbr]]].
                      generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                      eapply HA in Hbr. subst n''. 
                      assert (get' i t1_1 = None).
                      - erewrite zerobit_spec in H4; eauto.
                        erewrite zerobit_spec in H5; eauto.
                        apply negb_true_iff in H4; apply negb_false_iff in H5.
                        eapply get_not_same_prefix with (n := n'); eauto; try congruence.
                        eapply lt_trans; eauto. eapply ltb_spec; eauto.
                      - assert (get' i t1_2 = None).
                        + erewrite zerobit_spec in H4; eauto.
                          erewrite zerobit_spec in H5; eauto.
                          apply negb_true_iff in H4; apply negb_false_iff in H5.
                          eapply get_not_same_prefix with (n := n'); eauto; try congruence.
                          eapply lt_trans; eauto. eapply ltb_spec; eauto.
                        + rewrite H, H0. destruct (if zerobit i brbit0 then get' i t2_1 else get' i t2_2); destruct (zerobit i brbit); auto. }
                    { assert (Hmask'0: mask prefix0 brbit0 = prefix0) by (inv H8; auto; congruence).
                      generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) H3). intros [Hne [n' [HLT Hbr]]].
                      generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                      eapply HA in Hbr. subst n''. 
                      assert (get' i t1_1 = None).
                      - erewrite zerobit_spec in H4; eauto.
                        erewrite zerobit_spec in H5; eauto.
                        apply negb_true_iff in H4; apply negb_false_iff in H5.
                        eapply get_not_same_prefix with (n := n'); eauto; try congruence.
                        eapply lt_trans; eauto. eapply ltb_spec; eauto.
                      - assert (get' i t1_2 = None).
                        + erewrite zerobit_spec in H4; eauto.
                          erewrite zerobit_spec in H5; eauto.
                          apply negb_true_iff in H4; apply negb_false_iff in H5.
                          eapply get_not_same_prefix with (n := n'); eauto; try congruence.
                          eapply lt_trans; eauto. eapply ltb_spec; eauto.
                        + rewrite H, H0. destruct (if zerobit i brbit0 then get' i t2_1 else get' i t2_2); destruct (zerobit i brbit); auto. }
                + case_eq (zerobit i (branching_bit prefix prefix0)); intros.
                  * inv H; inv H0.
                    { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) H3). intros [Hne [n' [HLT Hbr]]].
                      generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                      eapply HA in Hbr. subst n''. 
                      assert (get' i t1_1 = None).
                      - erewrite zerobit_spec in H4; eauto.
                        erewrite zerobit_spec in H5; eauto.
                        apply negb_true_iff in H4; apply negb_false_iff in H5.
                        eapply get_not_same_prefix with (n := n'); eauto; try congruence.
                        eapply lt_trans; eauto. eapply ltb_spec; eauto.
                      - assert (get' i t1_2 = None).
                        + erewrite zerobit_spec in H4; eauto.
                          erewrite zerobit_spec in H5; eauto.
                          apply negb_true_iff in H4; apply negb_false_iff in H5.
                          eapply get_not_same_prefix with (n := n'); eauto; try congruence.
                          eapply lt_trans; eauto. eapply ltb_spec; eauto.
                        + rewrite H, H0. destruct (if zerobit i brbit0 then get' i t2_1 else get' i t2_2); destruct (zerobit i brbit); auto. }
                    { assert (Hmask'0: mask prefix0 brbit0 = prefix0) by (inv H8; auto; congruence).
                      generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) H3). intros [Hne [n' [HLT Hbr]]].
                      generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                      eapply HA in Hbr. subst n''. 
                      assert (get' i t1_1 = None).
                      - erewrite zerobit_spec in H4; eauto.
                        erewrite zerobit_spec in H5; eauto.
                        apply negb_true_iff in H4; apply negb_false_iff in H5.
                        eapply get_not_same_prefix with (n := n'); eauto; try congruence.
                        eapply lt_trans; eauto. eapply ltb_spec; eauto.
                      - assert (get' i t1_2 = None).
                        + erewrite zerobit_spec in H4; eauto.
                          erewrite zerobit_spec in H5; eauto.
                          apply negb_true_iff in H4; apply negb_false_iff in H5.
                          eapply get_not_same_prefix with (n := n'); eauto; try congruence.
                          eapply lt_trans; eauto. eapply ltb_spec; eauto.
                        + rewrite H, H0. destruct (if zerobit i brbit0 then get' i t2_1 else get' i t2_2); destruct (zerobit i brbit); auto. }
                  * inv H; inv H0.
                    { generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) H3). intros [Hne [n' [HLT Hbr]]].
                      generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                      eapply HA in Hbr. subst n''. 
                      assert (get' i t2_1 = None).
                      - erewrite zerobit_spec in H4; eauto.
                        erewrite zerobit_spec in H5; eauto.
                        apply negb_false_iff in H4; apply negb_false_iff in H5.
                        eapply get_not_same_prefix with (n := n'); eauto. 
                      - assert (get' i t2_2 = None).
                        + erewrite zerobit_spec in H4; eauto.
                          erewrite zerobit_spec in H5; eauto.
                          apply negb_false_iff in H4; apply negb_false_iff in H5.
                          eapply get_not_same_prefix with (n := n'); eauto.
                        + rewrite H, H0. destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); destruct (zerobit i brbit0); auto. }
                    { assert (Hmask'0: mask prefix0 brbit0 = prefix0) by (inv H8; auto; congruence).
                      generalize (proj1 (match_prefix_spec' _ _ _ _ Hbrbit'0 Hmask'0) H3). intros [Hne [n' [HLT Hbr]]].
                      generalize (branching_bit_spec _ _ Hne). intros [n'' [HA [HB HC]]].
                      eapply HA in Hbr. subst n''. 
                      assert (get' i t2_1 = None).
                      - erewrite zerobit_spec in H4; eauto.
                        erewrite zerobit_spec in H5; eauto.
                        apply negb_false_iff in H4; apply negb_false_iff in H5.
                        eapply get_not_same_prefix with (n := n'); eauto.
                      - assert (get' i t2_2 = None).
                        + erewrite zerobit_spec in H4; eauto.
                          erewrite zerobit_spec in H5; eauto.
                          apply negb_false_iff in H4; apply negb_false_iff in H5.
                          eapply get_not_same_prefix with (n := n'); eauto.
                        + rewrite H, H0. destruct (if zerobit i brbit then get' i t1_1 else get' i t1_2); destruct (zerobit i brbit0); auto. } }
            { inv H; inv H0.
              - destruct (lt_dec brbit' brbit'0).
                + generalize (proj2 (ltb_spec _ _ _ _ Hbrbit' Hbrbit'0) l). intros; congruence.
                + destruct (eq_nat_dec brbit'0 brbit').
                  * subst. elim n. apply testbit_spec; intros.
                    case_eq (testbit brbit n1); intros.
                    { eapply Hbrbit' in H; eauto. subst n1.
                      symmetry. eapply Hbrbit'0; eauto. }
                    { case_eq (testbit brbit0 n1); intros; auto.
                      eapply Hbrbit'0 in H0; eauto. subst n1.
                      generalize (proj2 (Hbrbit' _) eq_refl). congruence. }
                  * assert (brbit'0 < brbit')%nat by lia.
                    generalize (proj2 (ltb_spec _ _ _ _ Hbrbit'0 Hbrbit') H).
                    intros; congruence.
              - destruct (lt_dec brbit' brbit'0).
                + generalize (proj2 (ltb_spec _ _ _ _ Hbrbit' Hbrbit'0) l). intros; congruence.
                + destruct (eq_nat_dec brbit'0 brbit').
                  * subst. elim n. apply testbit_spec; intros.
                    case_eq (testbit brbit n1); intros.
                    { eapply Hbrbit' in H; eauto. subst n1.
                      symmetry. eapply Hbrbit'0; eauto. }
                    { case_eq (testbit brbit0 n1); intros; auto.
                      eapply Hbrbit'0 in H0; eauto. subst n1.
                      generalize (proj2 (Hbrbit' _) eq_refl). congruence. }
                  * assert (brbit'0 < brbit')%nat by lia.
                    generalize (proj2 (ltb_spec _ _ _ _ Hbrbit'0 Hbrbit') H).  intros; congruence. }
    Qed.

    Fixpoint beq' {A: Type} (beqA: A -> A -> bool) (m1 m2: ptrie A): bool :=
      match m1, m2 with
      | Empty, Empty => true
      | Leaf k1 v1, Leaf k2 v2 => eq k1 k2 && beqA v1 v2
      | Branch p1 brbit1 l1 r1, Branch p2 brbit2 l2 r2 =>
        eq p1 p2 && eq brbit1 brbit2 && beq' beqA l1 l2 && beq' beqA r1 r2
      | _, _ => false
      end.

    Lemma bempty:
      forall {A: Type} {m: ptrie A} {opt},
        wf opt m ->
        (forall x, get' x m = None) <-> m = Empty.
    Proof.
      induction m; intros.
      - split; intros; simpl; auto.
      - split; try discriminate; intros.
        generalize (H0 k); simpl; rewrite eqb_refl; congruence.
      - split; intros; try discriminate.
        inv H.
        + elim Hl. eapply IHm1; eauto.
          simpl in H0. intros.
          case_eq (zerobit x brbit); intros.
          * generalize (H0 x); rewrite H; auto.
          * eapply get_not_same_lr; eauto.
        + elim Hl. eapply IHm1; eauto.
          simpl in H0. intros.
          case_eq (zerobit x brbit); intros.
          * generalize (H0 x); rewrite H; auto.
          * eapply get_not_same_lr; eauto.
    Qed.

    Lemma not_empty_get':
      forall {A: Type} {pt: ptrie A} {opt},
        wf opt pt ->
        pt <> Empty ->
        exists k v, get' k pt = Some v.
    Proof.
      induction pt; intros.
      - elim H0; reflexivity.
      - exists k, v; simpl; rewrite eqb_refl; congruence.
      - assert (HA: exists k1 v1, get' k1 pt1 = Some v1) by (inv H; eapply IHpt1; eauto).
        assert (HB: exists k2 v2, get' k2 pt2 = Some v2) by (inv H; eapply IHpt2; eauto).
        simpl. destruct HA as [k1 [v1 HA]].
        exists k1, v1; rewrite HA.
        case_eq (zerobit k1 brbit); intros; auto.
        assert (get' k1 pt1 = None) by (inv H; eapply get_not_same_lr; eauto).
        congruence.
    Qed.

    Lemma is_mask_same:
      forall {m p q},
        is_mask m p ->
        is_mask m q ->
        p = q.
    Proof.
      intros; unfold is_mask in *; unfold is_mask in *.
      generalize (proj2 (H0 q) eq_refl); intros.
      eapply H; auto.
    Qed.

    Lemma is_mask_same':
      forall [m m' p],
        is_mask m p ->
        is_mask m' p ->
        m = m'.
    Proof.
      intros; eapply testbit_spec; intros.
      destruct (Nat.eq_dec p n).
      - subst p. rewrite (proj2 (H _) eq_refl).
        rewrite (proj2 (H0 _) eq_refl).
        reflexivity.
      - case_eq (testbit m n); intros.
        + elim n0. eapply (proj1 (H _) H1).
        + case_eq (testbit m' n); intros; auto.
          elim n0. eapply (proj1 (H0 _) H2).
    Qed.

    Lemma get_some_implies:
      forall {A: Type} [m: ptrie A] [k: key] [v: A] [opt],
        wf opt m ->
        get' k m = Some v ->
        match m with
        | Empty => False
        | Leaf k' v' => k = k'
        | Branch prefix brbit _ _ =>
          forall brbit', is_mask brbit brbit' ->
                    (forall n, (n < brbit')%nat -> testbit k n = testbit prefix n)
        end.
    Proof.
      induction m; intros.
      - simpl in H0; inv H0.
      - simpl in H0. destruct_eq k0 k; congruence.
      - simpl in H0. case_eq (zerobit k brbit); intros; rewrite H3 in H0.
        + inv H.
          * generalize (IHm1 _ _ _ H7 H0). intros HA.
            inv H7; try tauto.
            { subst k0. generalize (is_mask_same H1 Hbrbit'). intros; subst brbit'0.
              symmetry. eapply Hprefix0. auto. }
            { generalize (is_mask_same H1 Hbrbit'). intros; subst brbit'0.
              specialize (HA _ Hbrbit'0). rewrite HA; try lia.
              rewrite Hprefix0; try lia; auto. }
          * generalize (IHm1 _ _ _ H7 H0). intros HA.
            inv H7; try tauto.
            { subst k0. generalize (is_mask_same H1 Hbrbit'). intros; subst brbit'0.
              symmetry. eapply Hprefix0. auto. }
            { generalize (is_mask_same H1 Hbrbit'). intros; subst brbit'0.
              specialize (HA _ Hbrbit'0). rewrite HA; try lia.
              rewrite Hprefix0; try lia; auto. }
        + inv H.
          * generalize (IHm2 _ _ _ H10 H0). intros HA.
            inv H10; try tauto.
            { subst k0. generalize (is_mask_same H1 Hbrbit'). intros; subst brbit'0.
              symmetry. eapply Hprefix0. auto. }
            { generalize (is_mask_same H1 Hbrbit'). intros; subst brbit'0.
              specialize (HA _ Hbrbit'0). rewrite HA; try lia.
              rewrite Hprefix0; try lia; auto. }
          * generalize (IHm2 _ _ _ H10 H0). intros HA.
            inv H10; try tauto.
            { subst k0. generalize (is_mask_same H1 Hbrbit'). intros; subst brbit'0.
              symmetry. eapply Hprefix0. auto. }
            { generalize (is_mask_same H1 Hbrbit'). intros; subst brbit'0.
              specialize (HA _ Hbrbit'0). rewrite HA; try lia.
              rewrite Hprefix0; try lia; auto. }
    Qed.
    
    Lemma beq_correct':
      forall (A: Type) (eqA: A -> A -> bool) (t1 t2: ptrie A) opt,
        wf opt t1 ->
        wf opt t2 ->
        beq' eqA t1 t2 = true <->
        (forall (x: key),
            match get' x t1, get' x t2 with
            | None, None => True
            | Some y1, Some y2 => eqA y1 y2 = true
            | _, _ => False
            end).
    Proof.
      induction t1; intros; split; intros.
      { simpl in H1. destruct t2; inv H1.
        simpl; reflexivity. }
      { simpl in H1. generalize (proj1 (bempty H0)). intros HA.
        erewrite HA; simpl; auto.
        intros; generalize (H1 x); destruct (get' x t2); tauto. }
      { destruct t2; simpl in H1; inv H1.
        simpl. destruct_eq k k0; simpl in H3; inv H3.
        destruct_eq x k0; simpl; auto. rewrite H2. reflexivity. }
      { simpl in H1. destruct t2.
        - generalize (H1 k); rewrite eqb_refl; simpl; tauto.
        - generalize (H1 k); rewrite eqb_refl; simpl; try congruence.
          destruct_eq k k0; tauto.
        - generalize (H1 k); rewrite eqb_refl; simpl; try congruence.
          case_eq (zerobit k brbit); intros.
          + assert (t2_2 <> Empty) by (inv H0; auto).
            assert (exists o, wf o t2_2) by (inv H0; eauto).
            destruct H5.
            generalize (not_empty_get' H5 H4). intros [k' [v' HA]].
            generalize (H1 k'); simpl. assert (get' k t2_2 = None) by (inv H0; eapply get_not_same_lr; eauto).
            destruct_eq k' k; try congruence.
            rewrite HA; case_eq (zerobit k' brbit); intros; try tauto.
            assert (get' k' t2_2 = None) by (inv H0; eapply get_not_same_lr; eauto). congruence.
          + assert (t2_1 <> Empty) by (inv H0; auto).
            assert (exists o, wf o t2_1) by (inv H0; eauto).
            destruct H5.
            generalize (not_empty_get' H5 H4). intros [k' [v' HA]].
            generalize (H1 k'); simpl. assert (get' k t2_1 = None) by (inv H0; eapply get_not_same_lr; eauto).
            destruct_eq k' k; try congruence.
            rewrite HA; case_eq (zerobit k' brbit); intros; try tauto.
            assert (get' k' t2_1 = None) by (inv H0; eapply get_not_same_lr; eauto). congruence. }
      { destruct t2; simpl in H1; inv H1.
        destruct (eq prefix prefix0); destruct (eq brbit brbit0); simpl in H3; inv H3.
        simpl. rewrite H2.  apply andb_true_iff in H2. destruct H2.
        inv H; inv H0.
        - generalize (is_mask_same Hbrbit' Hbrbit'0). intros; subst brbit'0.
          generalize (proj1 (IHt1_1 _ _ H6 H4) H1); intros HA.
          generalize (proj1 (IHt1_2 _ _ H9 H13) H2); intros HB.
          case_eq (zerobit x brbit0); intros.
          + apply HA.
          + apply HB.
        - generalize (is_mask_same Hbrbit' Hbrbit'0). intros; subst brbit'0.
          generalize (proj1 (IHt1_1 _ _ H6 H5) H1); intros HA.
          generalize (proj1 (IHt1_2 _ _ H9 H8) H2); intros HB.
          case_eq (zerobit x brbit0); intros.
          + apply HA.
          + apply HB. }
      { destruct t2; simpl in H1.
        - generalize (not_empty_get' H ltac:(congruence)). intros [k [v HA]].
          simpl in HA. generalize (H1 k); simpl in HA; rewrite HA; tauto.
        - case_eq (zerobit k brbit); intros.
          + assert (HA: t1_2 <> Empty) by (inv H; auto).
            assert (HB: exists o, wf o t1_2) by (inv H; eauto).
            destruct HB as [o HB]. generalize (not_empty_get' HB HA). intros [k' [v' HC]].
            generalize (H1 k'). rewrite HC. case_eq (zerobit k' brbit); intros.
            * assert (get' k' t1_2 = None) by (inv H; eapply get_not_same_lr; eauto). congruence.
            * destruct_eq k' k; try congruence; tauto.
          + assert (HA: t1_1 <> Empty) by (inv H; auto).
            assert (HB: exists o, wf o t1_1) by (inv H; eauto).
            destruct HB as [o HB]. generalize (not_empty_get' HB HA). intros [k' [v' HC]].
            generalize (H1 k'). rewrite HC. case_eq (zerobit k' brbit); intros.
            * destruct_eq k' k; try congruence; tauto.
            * assert (get' k' t1_1 = None) by (inv H; eapply get_not_same_lr; eauto). congruence.
        - destruct (eq prefix prefix0).
          + subst prefix0.
            assert (Hbrbit: exists brbit', is_mask brbit brbit' /\ (forall n, (n >= brbit')%nat -> testbit prefix n = false)) by (inv H; eauto).
            destruct Hbrbit as [brbit' [Hbrbit Hprefix]].
            assert (Hbrbit0: exists brbit0', is_mask brbit0 brbit0' /\ (forall n, (n >= brbit0')%nat -> testbit prefix n = false)) by (inv H0; eauto).
            destruct Hbrbit0 as [brbit0' [Hbrbit0 Hprefix']].
            assert (Hmask: mask prefix brbit = prefix).
            { eapply testbit_spec. intros.
              generalize (mask_spec prefix _ _ Hbrbit). intros [HA HB].
              destruct (lt_dec n brbit').
              - apply HA; auto.
              - rewrite Hprefix; try lia.
                rewrite HB; auto; lia. }
            assert (Hmask': mask prefix brbit0 = prefix).
            { eapply testbit_spec. intros.
              generalize (mask_spec prefix _ _ Hbrbit0). intros [HA HB].
              destruct (lt_dec n brbit0').
              - apply HA; auto.
              - rewrite Hprefix'; try lia.
                rewrite HB; auto; lia. }
            destruct (Nat.eq_dec brbit' brbit0').
            * subst brbit0'. generalize (is_mask_same' Hbrbit0 Hbrbit). intros; subst brbit0.
              simpl. destruct (eq prefix prefix); try congruence.
              destruct (eq brbit brbit); try congruence; simpl.
              assert (Ho1: exists o1, wf o1 t1_1 /\ wf o1 t2_1) by (inv H; inv H0; generalize (is_mask_same Hbrbit'0 Hbrbit'); intros; subst; eauto).
              assert (Ho2: exists o2, wf o2 t1_2 /\ wf o2 t2_2) by (inv H; inv H0; generalize (is_mask_same Hbrbit'0 Hbrbit'); intros; subst; eauto).
              destruct Ho1 as [o1 [HA HB]]. destruct Ho2 as [o2 [HC HD]].
              rewrite (proj2 (IHt1_1 _ _ HA HB)), (proj2 (IHt1_2 _ _ HC HD)); simpl; auto.
              { intros. generalize (H1 x).
                case_eq (zerobit x brbit); intros.
                - assert (get' x t1_2 = None) by (inv H; eapply get_not_same_lr; eauto).
                  assert (get' x t2_2 = None) by (inv H0; eapply get_not_same_lr; eauto).
                  rewrite H4, H5. auto.
                - auto. }
              { intros. generalize (H1 x).
                case_eq (zerobit x brbit); intros.
                - auto.
                - assert (get' x t1_1 = None) by (inv H; eapply get_not_same_lr; eauto).
                  assert (get' x t2_1 = None) by (inv H0; eapply get_not_same_lr; eauto).
                  rewrite H4, H5. auto. }
            * assert (brbit' < brbit0' \/ brbit0' < brbit')%nat by lia. destruct H2.
              { assert (HA: testbit prefix brbit' = false) by (eapply Hprefix; lia).
                assert (Ht1_2: t1_2 <> Empty) by (inv H; assumption).
                assert (HB: exists o, wf o t1_2) by (inv H; eauto).
                destruct HB as [o HB].
                generalize (not_empty_get' HB Ht1_2).
                intros [k [v HC]]. case_eq (zerobit k brbit); intros.
                - assert (get' k t1_2 = None) by (inv H; eapply get_not_same_lr; eauto). congruence.
                - generalize (H1 k); rewrite H3; rewrite HC.
                  case_eq (get' k (Branch prefix brbit0 t2_1 t2_2)); intros.
                  + generalize (get_some_implies H0 H4 _ Hbrbit0 _ H2). intros HD.
                    erewrite zerobit_spec in H3; eauto. rewrite HD in H3.
                    rewrite HA in H3. simpl in H3. congruence.
                  + simpl in H4. rewrite H4 in H5. elim H5. }
              { assert (HA: testbit prefix brbit0' = false) by (eapply Hprefix'; lia).
                assert (Ht2_2: t2_2 <> Empty) by (inv H0; assumption).
                assert (HB: exists o, wf o t2_2) by (inv H0; eauto).
                destruct HB as [o HB].
                generalize (not_empty_get' HB Ht2_2).
                intros [k [v HC]]. case_eq (zerobit k brbit0); intros.
                - assert (get' k t2_2 = None) by (inv H0; eapply get_not_same_lr; eauto). congruence.
                - generalize (H1 k); rewrite H3; rewrite HC.
                  case_eq (get' k (Branch prefix brbit t1_1 t1_2)); intros.
                  + generalize (get_some_implies H H4 _ Hbrbit _ H2). intros HD.
                    erewrite zerobit_spec in H3; eauto. rewrite HD in H3.
                    rewrite HA in H3. simpl in H3. congruence.
                  + simpl in H4. rewrite H4 in H5. elim H5. }
          + assert (Hbrbit: exists brbit', is_mask brbit brbit' /\ (forall n, (n >= brbit')%nat -> testbit prefix n = false)) by (inv H; eauto).
            destruct Hbrbit as [brbit' [Hbrbit Hprefix]].
            assert (Hbrbit0: exists brbit0', is_mask brbit0 brbit0' /\ (forall n, (n >= brbit0')%nat -> testbit prefix0 n = false)) by (inv H0; eauto).
            destruct Hbrbit0 as [brbit0' [Hbrbit0 Hprefix']].
            assert (Hmask: mask prefix brbit = prefix).
            { eapply testbit_spec. intros.
              generalize (mask_spec prefix _ _ Hbrbit). intros [HA HB].
              destruct (lt_dec n0 brbit').
              - apply HA; auto.
              - rewrite Hprefix; try lia.
                rewrite HB; auto; lia. }
            assert (Hmask': mask prefix0 brbit0 = prefix0).
            { eapply testbit_spec. intros.
              generalize (mask_spec prefix0 _ _ Hbrbit0). intros [HA HB].
              destruct (lt_dec n0 brbit0').
              - apply HA; auto.
              - rewrite Hprefix'; try lia.
                rewrite HB; auto; lia. }
            destruct (lt_dec brbit' brbit0').
            * case_eq (testbit prefix0 brbit'); intros.
              { assert (HA: t1_1 <> Empty) by (inv H; auto).
                assert (HB: exists o, wf o t1_1) by (inv H; eauto).
                destruct HB as [o HB]. generalize (not_empty_get' HB HA). intros [k' [v' HC]].
                generalize (H1 k'). rewrite HC. case_eq (zerobit k' brbit); intros.
                - case_eq (get' k' (Branch prefix0 brbit0 t2_1 t2_2)); intros.
                  + generalize (get_some_implies H0 H5 _ Hbrbit0 _ l). intros.
                    erewrite zerobit_spec in H3; eauto. eapply negb_true_iff in H3.
                    rewrite H6 in H3. rewrite H2 in H3. congruence.
                  + simpl in H5; rewrite H5 in H4. elim H4.
                - assert (get' k' t1_1 = None) by (inv H; eapply get_not_same_lr; eauto).
                  congruence. }
              { assert (HA: t1_2 <> Empty) by (inv H; auto).
                assert (HB: exists o, wf o t1_2) by (inv H; eauto).
                destruct HB as [o HB]. generalize (not_empty_get' HB HA). intros [k' [v' HC]].
                generalize (H1 k'). rewrite HC. case_eq (zerobit k' brbit); intros.
                - assert (get' k' t1_2 = None) by (inv H; eapply get_not_same_lr; eauto).
                  congruence.
                - case_eq (get' k' (Branch prefix0 brbit0 t2_1 t2_2)); intros.
                  + generalize (get_some_implies H0 H5 _ Hbrbit0 _ l). intros.
                    erewrite zerobit_spec in H3; eauto. eapply negb_false_iff in H3.
                    rewrite H6 in H3. rewrite H2 in H3. congruence.
                  + simpl in H5; rewrite H5 in H4. elim H4. }
            * destruct (lt_dec brbit0' brbit').
              { case_eq (testbit prefix brbit0'); intros.
                { assert (HA: t2_1 <> Empty) by (inv H0; auto).
                  assert (HB: exists o, wf o t2_1) by (inv H0; eauto).
                  destruct HB as [o HB]. generalize (not_empty_get' HB HA). intros [k' [v' HC]].
                  generalize (H1 k'). rewrite HC. case_eq (zerobit k' brbit0); intros.
                  - case_eq (get' k' (Branch prefix brbit t1_1 t1_2)); intros.
                    + generalize (get_some_implies H H5 _ Hbrbit _ l). intros.
                      erewrite zerobit_spec in H3; eauto. eapply negb_true_iff in H3.
                      rewrite H6 in H3. rewrite H2 in H3. congruence.
                    + simpl in H5; rewrite H5 in H4. elim H4.
                  - assert (get' k' t2_1 = None) by (inv H0; eapply get_not_same_lr; eauto).
                    congruence. }
                { assert (HA: t2_2 <> Empty) by (inv H0; auto).
                  assert (HB: exists o, wf o t2_2) by (inv H0; eauto).
                  destruct HB as [o HB]. generalize (not_empty_get' HB HA). intros [k' [v' HC]].
                  generalize (H1 k'). rewrite HC. case_eq (zerobit k' brbit0); intros.
                  - assert (get' k' t2_2 = None) by (inv H0; eapply get_not_same_lr; eauto).
                    congruence.
                  - case_eq (get' k' (Branch prefix brbit t1_1 t1_2)); intros.
                    + generalize (get_some_implies H H5 _ Hbrbit _ l). intros.
                      erewrite zerobit_spec in H3; eauto. eapply negb_false_iff in H3.
                      rewrite H6 in H3. rewrite H2 in H3. congruence.
                    + simpl in H5; rewrite H5 in H4. elim H4. } }
              { assert (brbit0' = brbit') by lia. subst. clear n1; clear n0.
                generalize (branching_bit_spec _ _ n). intros [p [HA [HB HC]]].
                generalize (not_empty_get' H ltac:(congruence)). intros [k [v HD]].
                assert (p < brbit')%nat.
                { destruct (lt_dec p brbit'); auto.
                  rewrite Hprefix in HC; try lia.
                  rewrite Hprefix' in HC; try congruence; lia. }
                generalize (get_some_implies H HD _ Hbrbit _ H2). intros HE.
                generalize (H1 k). simpl in HD; rewrite HD.
                generalize (is_mask_same' Hbrbit Hbrbit0). intros; subst.
                case_eq (get' k (Branch prefix0 brbit0 t2_1 t2_2)); intros.
                - generalize (get_some_implies H0 H3 _ Hbrbit _ H2). intros HF.
                  elim HC; congruence.
                - simpl in H3; rewrite H3 in H4. elim H4. } }
    Qed.

    Lemma ptrie_extensional:
      forall (A: Type) (t1 t2: ptrie A) o,
        wf o t1 ->
        wf o t2 ->
        (forall k, get' k t1 = get' k t2) ->
        t1 = t2.
    Proof.
      induction t1; intros.
      - destruct t2; auto.
        + generalize (H1 k); simpl; intros.
          rewrite eqb_refl in H2; congruence.
        + generalize (not_empty_get' H0 ltac:(congruence)). intros [k [v HA]].
          rewrite <- H1 in HA. simpl in HA; congruence.
      - destruct t2.
        + generalize (H1 k); simpl; intros. rewrite eqb_refl in H2; congruence.
        + generalize (H1 k); generalize (H1 k0); simpl.
          rewrite! eqb_refl; destruct_eq k0 k; destruct_eq k k0; congruence.
        + assert (Ht2_1: t2_1 <> Empty) by (inv H0; auto).
          assert (Ht2_2: t2_2 <> Empty) by (inv H0; auto).
          assert (Ho1: exists o1, wf o1 t2_1) by (inv H0; eauto). destruct Ho1 as [o1 Ho1].
          assert (Ho2: exists o2, wf o2 t2_2) by (inv H0; eauto). destruct Ho2 as [o2 Ho2].
          generalize (H1 k); simpl; destruct (eq k k); try congruence; intros.
          apply eq_sym in H2. case_eq (zerobit k brbit); intros; rewrite H3 in H2.
          * generalize (not_empty_get' Ho2 Ht2_2). intros [k' [v' HA]].
            case_eq (zerobit k' brbit); intros.
            { assert (get' k' t2_2 = None) by (inv H0; eapply get_not_same_lr; eauto); congruence. }
            { generalize (H1 k'); simpl. destruct_eq k' k; try congruence.
              rewrite H4; congruence. }
          * generalize (not_empty_get' Ho1 Ht2_1). intros [k' [v' HA]].
            case_eq (zerobit k' brbit); intros.
            { generalize (H1 k'); simpl. destruct_eq k' k; try congruence.
              rewrite H4; congruence. }
            { assert (get' k' t2_1 = None) by (inv H0; eapply get_not_same_lr; eauto); congruence. }
      - destruct t2.
        + generalize (not_empty_get' H ltac:(congruence)). intros [k [v HA]].
          rewrite H1 in HA; simpl in HA; congruence.
        + assert (Ht1_1: t1_1 <> Empty) by (inv H; auto).
          assert (Ht1_2: t1_2 <> Empty) by (inv H; auto).
          assert (Ho1: exists o1, wf o1 t1_1) by (inv H; eauto). destruct Ho1 as [o1 Ho1].
          assert (Ho2: exists o2, wf o2 t1_2) by (inv H; eauto). destruct Ho2 as [o2 Ho2].
          generalize (H1 k); simpl; destruct (eq k k); try congruence; intros.
          case_eq (zerobit k brbit); intros; rewrite H3 in H2.
          * generalize (not_empty_get' Ho2 Ht1_2). intros [k' [v' HA]].
            case_eq (zerobit k' brbit); intros.
            { assert (get' k' t1_2 = None) by (inv H; eapply get_not_same_lr; eauto); congruence. }
            { generalize (H1 k'); simpl. destruct_eq k' k; try congruence.
              rewrite H4; congruence. }
          * generalize (not_empty_get' Ho1 Ht1_1). intros [k' [v' HA]].
            case_eq (zerobit k' brbit); intros.
            { generalize (H1 k'); simpl. destruct_eq k' k; try congruence.
              rewrite H4; congruence. }
            { assert (get' k' t1_1 = None) by (inv H; eapply get_not_same_lr; eauto); congruence. }
        +
          generalize (proj2 (beq_correct' _ (fun a b => true) _ _ _ H H0) ltac:(intros; rewrite H1; destruct (get' x (Branch prefix0 brbit0 t2_1 t2_2)); auto)). intros.
          simpl in H2. destruct (eq prefix prefix0); simpl in H2; try congruence.
          subst prefix0. destruct (eq brbit brbit0); simpl in H2; try congruence. subst brbit0.
          f_equal; auto.
          * inv H; inv H0; eapply IHt1_1; eauto.
            { assert (brbit'0 = brbit') by (eapply is_mask_same; eauto).
              subst brbit'0. eauto. }
            { intros. generalize (H1 k); simpl.
              case_eq (zerobit k brbit); intros; auto.
              erewrite ! (get_not_same_lr); eauto. }
            { assert (brbit'0 = brbit') by (eapply is_mask_same; eauto).
              subst brbit'0. eauto. }
            { intros. generalize (H1 k); simpl.
              case_eq (zerobit k brbit); intros; auto.
              erewrite ! (get_not_same_lr); eauto. }
          * inv H; inv H0; eapply IHt1_2; eauto.
            { assert (brbit'0 = brbit') by (eapply is_mask_same; eauto).
              subst brbit'0. eauto. }
            { intros. generalize (H1 k); simpl.
              case_eq (zerobit k brbit); intros; auto.
              erewrite ! (get_not_same_lr); eauto. }
            { assert (brbit'0 = brbit') by (eapply is_mask_same; eauto).
              subst brbit'0. eauto. }
            { intros. generalize (H1 k); simpl.
              case_eq (zerobit k brbit); intros; auto.
              erewrite ! (get_not_same_lr); eauto. }
    Qed.
    
    Lemma elements_extensional:
      forall {A: Type} (m n: ptrie A) o,
        wf o m ->
        wf o n ->
        (forall i, get' i m = get' i n) ->
        elements' m = elements' n.
    Proof.
      intros. generalize (ptrie_extensional _ _ _ _ H H0 H1).
      intro; subst; auto.
    Qed.

    Lemma remove_branch_not_empty:
      forall {A} [m: ptrie A] [prefix brbit m1 m2 o],
        wf o m ->
        m = Branch prefix brbit m1 m2 ->
        forall k, remove' k m <> Empty.
    Proof.
      induction m; intros; try congruence.
      eapply eq_sym in H0. inv H0. simpl. case_eq (match_prefix k prefix brbit); intros; try congruence.
      case_eq (zerobit k brbit); intros.
      - destruct m1.
        + inv H; congruence.
        + simpl. destruct_eq k0 k; simpl; try congruence.
          * inv H; congruence.
          * destruct m2; congruence.
        + assert (Ho: exists o1, wf o1 (Branch prefix0 brbit0 m1_1 m1_2)) by (inv H; eauto).
          destruct Ho as [o1 Ho1].
          generalize (IHm1 _ _ _ _ _ Ho1 eq_refl k). intros HA.
          destruct (remove' k (Branch prefix0 brbit0 m1_1 m1_2)); destruct m2; simpl; inv H; try congruence.
      - destruct m2.
        + inv H; congruence.
        + simpl. destruct_eq k0 k; simpl; try congruence.
          * destruct m1; inv H; simpl; congruence.
          * destruct m1; inv H; simpl; congruence.
        + assert (Ho: exists o2, wf o2 (Branch prefix0 brbit0 m2_1 m2_2)) by (inv H; eauto).
          destruct Ho as [o2 Ho2].
          generalize (IHm2 _ _ _ _ _ Ho2 eq_refl k). intros HA.
          destruct (remove' k (Branch prefix0 brbit0 m2_1 m2_2)); destruct m1; simpl; inv H; try congruence.
    Qed.

    Lemma branch_not_empty:
      forall A prefix brbit (m1 m2: ptrie A),
        m1 <> Empty ->
        m2 <> Empty ->
        branch prefix brbit m1 m2 = Branch prefix brbit m1 m2.
    Proof.
      intros; destruct m1; destruct m2; simpl; congruence.
    Qed.
    
    Lemma elements_remove:
      forall (A: Type) i v (m: ptrie A) o,
        wf o m ->
        get' i m = Some v ->
        exists l1 l2, elements' m nil = l1 ++ (i,v) :: l2 /\ elements' (remove' i m) nil = l1 ++ l2.
    Proof.
      induction m; intros.
      - simpl in H0; inv H0.
      - generalize (get_some_implies H H0). intros; subst i.
        simpl in H0.
        simpl; eauto. exists nil, nil. rewrite eqb_refl in *; try congruence.
        split; auto. rewrite app_nil_l. inv H0; auto.
      - generalize (get_some_implies H H0). intros HA.
        simpl in H0. rewrite elements_branch'.
        simpl. assert (Hmask: exists brbit', is_mask brbit brbit' /\ mask prefix brbit = prefix).
        { inv H; eexists; split; eauto. eapply testbit_spec. intros.
          generalize (mask_spec prefix _ _ Hbrbit'). intros [HX HY].
          destruct (lt_dec n brbit').
          - rewrite HX; auto.
          - rewrite Hprefix; try lia.
            apply HY; lia. }
        destruct Hmask as [brbit' [Hmask1 Hmask2]].
        generalize (proj2 (match_prefix_spec _ _ _ _ Hmask1 Hmask2) (HA _ Hmask1)). intros HB.
        rewrite HB. case_eq (zerobit i brbit); intros.
        + rewrite H1 in H0.
          assert (exists o1, wf o1 m1) by (inv H; eauto).
          destruct H2 as [o1 Ho1]. generalize (IHm1 o1 Ho1 H0).
          intros [l1 [l2 [HC HD]]].
          rewrite HC. exists l1, (l2 ++ elements' m2 nil). split.
          * rewrite app_assoc_reverse. rewrite app_comm_cons. reflexivity.
          * destruct m1.
            { inv H; congruence. }
            { simpl in H0. destruct_eq i k; try congruence.
              inv H0. simpl. simpl in HD. rewrite eqb_refl in *; try congruence. simpl in HD.
              simpl. generalize (app_eq_nil l1 l2 (eq_sym HD)). intros [HX HY]; subst.
              simpl. reflexivity. }
            { generalize (remove_branch_not_empty Ho1 eq_refl i). intros HE.
              assert (Hm2: m2 <> Empty) by (inv H; auto).
              rewrite branch_not_empty; eauto.
              rewrite elements_branch'. rewrite HD. apply app_assoc_reverse. }
        + rewrite H1 in H0.
          assert (exists o2, wf o2 m2) by (inv H; eauto).
          destruct H2 as [o2 Ho2]. generalize (IHm2 o2 Ho2 H0).
          intros [l1 [l2 [HC HD]]].
          rewrite HC. exists (elements' m1 nil ++ l1), l2. split.
          * rewrite app_assoc_reverse. reflexivity.
          * destruct m2.
            { inv H; congruence. }
            { simpl in H0. destruct_eq i k; try congruence.
              inv H0. simpl. simpl in HD. rewrite eqb_refl in *; try congruence. simpl in HD.
              simpl. generalize (app_eq_nil l1 l2 (eq_sym HD)). intros [HX HY]; subst.
              destruct m1; unfold branch; try reflexivity.
              rewrite ! app_nil_r. reflexivity. }
            { generalize (remove_branch_not_empty Ho2 eq_refl i). intros HE.
              assert (Hm1: m1 <> Empty) by (inv H; auto).
              rewrite branch_not_empty; eauto.
              rewrite elements_branch'. rewrite HD. apply app_assoc. }
    Qed.
    
End S.

End PTrie.
