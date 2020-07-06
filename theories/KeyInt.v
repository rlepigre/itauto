Require Import Cdcl.PatriciaR.
Require Import Bool ZifyClasses ZArith Lia.
Require Import Cdcl.ZifyInt.

Require Int63.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Section S.
  Import Int63.
  Definition zero := 0%int63.
  Definition one :=  1%int63.
End S.

Definition int_of_nat (n:nat) := Int63.of_Z (Z.of_nat n).

Program Instance Op_int_of_nat : UnOp int_of_nat :=
    {| TUOp := fun x => x mod 9223372036854775808%Z ; TUOpInj := _ |}%Z.
Next Obligation.
  unfold int_of_nat.
  rewrite Int63.of_Z_spec.
  reflexivity.
Qed.
Add Zify UnOp Op_int_of_nat.

Lemma int_of_nat_inj : forall n n',
    n < 63 -> n' < 63 ->
    int_of_nat n = int_of_nat n' -> n = n'.
Proof.
  intros.
  unfold int_of_nat in *.
  lia.
Qed.

Definition testbit (i:Int63.int) (n:nat) :=
  if 63 <=? n then false else Int63.bit i (int_of_nat n).

Lemma zero_spec: forall n, testbit zero n = false.
Proof.
  intros. unfold testbit,zero.
  rewrite Int63.bit_0.
  destruct (63 <=?n); auto.
Qed.

Lemma eqb_spec : forall k1 k2, Int63.eqb k1 k2 = true <-> k1 = k2.
Proof.
  split ; intros.
  apply Int63.eqb_correct; auto.
  apply Int63.eqb_complete; auto.
Qed.

Lemma testbit_spec: forall k1 k2, (forall n, testbit k1 n = testbit k2 n) -> k1 = k2.
  Proof.
    intros.
    unfold testbit in *.
    apply Int63.bit_ext;auto ; intros.
    specialize (H (Z.to_nat (Int63.to_Z n))).
    destruct (63 <=? Z.to_nat (Int63.to_Z n)) eqn:EQ.
    -  assert (Int63.leb Int63.digits n = true).
       { unfold Int63.digits. lia. }
       rewrite Int63.bit_M by assumption.
       rewrite Int63.bit_M by assumption.
       reflexivity.
    -
      assert ( int_of_nat (Z.to_nat (Int63.to_Z n)) = n)
        by (unfold int_of_nat ; lia).
    congruence.
  Qed.

  Definition interp:= (fun i => (Int63.sub i one)).

  Definition is_mask := (fun (m: Int63.int) (n: nat) => forall p, testbit m p = true <-> n = p).

  Import Int63.


  Section NatUP.
    Variable P : nat -> bool.

    Fixpoint forall_n  (n:nat) : bool :=
      match n with
    | O => P O
    | S n' => P n && forall_n n'
      end.

    Lemma forall_n_correct : forall n, forall_n n = true -> forall p, p <= n -> P p = true.
    Proof.
      induction n ; simpl.
      - intros. assert (p = 0) by lia.
        congruence.
      - intros.
        rewrite andb_true_iff in H.
        destruct H.
        specialize (IHn H1 p).
        assert (p = S n \/ p <= n) by lia.
        destruct H2 ; subst; auto.
    Qed.

  End NatUP.

  Section NatUP2.
    Variable P : nat -> nat -> bool.

    Fixpoint forall_2n (n:nat) (m:nat) :=
      match n with
      | O => forall_n (P O) m
      | S n' => forall_n (P n) m && forall_2n n' m
      end.

    Lemma forall_2n_correct : forall n m, forall_2n n m = true -> forall p q, p <= n -> q <= m -> P p q = true.
    Proof.
      induction n ; simpl.
      - intros. assert (p = 0) by lia.
        subst.
        eapply forall_n_correct in H ; eauto.
      - intros.
        rewrite andb_true_iff in H.
        destruct H.
        specialize (IHn _ H2 p q).
        assert (p = S n \/ p <= n) by lia.
        destruct H3 ; subst; auto.
        eapply forall_n_correct; eauto.
    Qed.

  End NatUP2.

(*  Lemma testbit_M : forall m n,
      63 <= n ->
      testbit m n = false.
  Proof.
    intros.
    unfold testbit.
    destruct (63 <=?n) eqn:LE; auto.
    lia.
  Qed.

  Lemma testbit_M' : forall m n,
      testbit m n = true ->
      n < 63.
  Proof.
    intros.
    assert (63 <= n \/ n < 63)%nat by lia.
    destruct H0 ; auto.
    apply testbit_M with (m:=m) in H0 ; auto.
    congruence.
  Qed.
 *)

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


  Lemma mask_small :
    forall m n
           (BOUND : n < 63)
           (BITN : is_mask m n),
      m = Int63.lsl one (int_of_nat n).
  Proof.
    unfold one.
    intros.
    apply testbit_spec.
    intros.
    destruct (testbit m n0) eqn:TEST.
    - assert (n = n0).
      { apply BITN;auto. }
      subst. clear BITN.
      unfold testbit in *.
      revert TEST.
      rewrite Int63.bit_lsl.
      unfold Int63.digits.
      rewrite bit_1.
      repeat elim_if.
      lia.
    - assert (n <> n0).
      { specialize (BITN n0).
        intuition congruence. }
      unfold testbit.
      rewrite Int63.bit_lsl.
      unfold Int63.digits.
      rewrite bit_1.
      repeat elim_if ; intuition try lia.
  Qed.

  Lemma mask_big :
    forall m n
           (BOUND : n >= 63)
           (BITN : is_mask m n),
      False.
  Proof.
    unfold is_mask.
    intros.
    generalize (BITN n).
    generalize (BITN (n+1)).
    intros.
    unfold testbit in *.
    replace (63 <=? n +1) with true in * by lia.
    replace ( 63 <=? n) with true in * by lia.
    intuition lia.
  Qed.

  Definition mask_spec : forall m n, is_mask m n ->
                                     if 63 <=? n then
                                       False
                                     else
                                       m = Int63.lsl one (int_of_nat n).
  Proof.
    intros.
    destruct (63 <=? n) eqn:EQ.
    eapply mask_big with (n:= n) ; eauto.
    lia.
    eapply mask_small with (n:= n) ; eauto.
    lia.
  Qed.

  Lemma eqb_iff : forall b1 b2,
      Bool.eqb b1 b2 = true <-> (b1 = true <-> b2 = true).
  Proof.
    intros.
    destruct b1,b2; intuition congruence.
  Qed.


  Lemma interp_spec: forall m n, is_mask m n -> forall p, testbit (interp m) p = true <-> (p < n)%nat.
  Proof.
    intros.
    apply mask_spec in H.
    destruct (63 <=? n) eqn:N; [tauto|].
    subst.
    unfold testbit.
    destruct (63 <=?p) eqn:EQ.
    - lia.
    -
      assert (NS : n <= 62) by lia.
      assert (NP : p <= 62) by lia.
      rewrite <- Nat.ltb_lt.
        apply eqb_iff.
        set (Q:= fun n p =>  Bool.eqb (bit (interp (one << int_of_nat n)) (int_of_nat p)) (p <? n)).
        change (Q n p = true).
        eapply (forall_2n_correct _ 62 62);auto.
  Qed.


  Lemma land_spec: forall n k1 k2, testbit (Int63.land k1 k2) n = testbit k1 n && testbit k2 n.
  Proof.
    intros.
    unfold testbit.
    rewrite Int63.land_spec.
    destruct (63 <=? n) eqn:T; reflexivity.
  Qed.



  Lemma lxor_spec: forall n k1 k2, testbit (Int63.lxor k1 k2) n = xorb (testbit k1 n) (testbit k2 n).
  Proof.
    intros.
    unfold testbit.
    rewrite Int63.lxor_spec.
    destruct (63 <=? n) eqn:T; reflexivity.
  Qed.

  Ltac unfold_wB :=
    let f := fresh "w" in
    set (f := wB) in *;
    compute in f ;
    unfold f in *; clear f.


  Definition  ones (n:int) := ((1 << n) - 1)%int63.

  Lemma power2_mod : forall n m,
      (0 <= n -> 0 <= m ->
      ((2 ^ n) mod (2 ^ m) =  if Z.ltb n m then 2^n else  0))%Z.
  Proof.
    intros.
    destruct (n <?m)%Z eqn:T.
    - apply Z.mod_small; auto.
      split.
      apply Z.pow_nonneg. lia.
      apply Z.pow_lt_mono_r; lia.
    - assert ((2 ^ n) = 0 + 2^(n-m) * 2^m)%Z.
      rewrite <- Z.pow_add_r.
      simpl. f_equal. lia.
      lia. lia.
      rewrite H1.
      rewrite Z_mod_plus_full.
      apply Z.mod_0_l.
      generalize (Z.pow_pos_nonneg 2 m).
      lia.
  Qed.

  Lemma bit_ones : forall n p,
                          (*(SMALL: (n < Int63.digits = true)%int63),*)
      bit (ones n) p = if (ltb p n && (ltb p  63))%int63 then true else false.
  Proof.
    unfold ones,one.
    intros.
    rewrite bitE.
    rewrite sub_spec.
    rewrite lsl_spec.
    replace (((φ (1)%int63 * 2 ^ φ (n)%int63)))%Z with
        (2 ^ (to_Z n))%Z by lia.
    unfold wB.
    rewrite power2_mod by (unfold size ; lia).
    destruct ((φ (n)%int63 <? Z.of_nat size)%Z) eqn:T.
    - unfold size in *.
      rewrite Z.mod_small.
      replace ( 2 ^ φ (n)%int63 - φ (1)%int63)%Z
        with (Z.pred (2 ^ φ (n)%int63))%Z by lia.
      rewrite <- Z.ones_equiv.
      rewrite Z.testbit_ones_nonneg by lia.
      destruct ((p < n) && (p < 63))%int63 eqn:LT.
      lia. lia.
      assert (BOUND : (0 < 2 ^ to_Z n < wB)%Z).
      { unfold wB.
        split.
        apply Z.pow_pos_nonneg; lia.
        apply Z.pow_lt_mono_r.
        lia. unfold size. lia.
        unfold digits, size in *.
        lia.
      }
      unfold wB,size in BOUND. lia.
    -
      assert (1 < 2 ^ Z.of_nat size)%Z.
      {
        apply Z.pow_gt_1.
        lia.
        unfold size. lia.
      }
      rewrite Z_mod_nz_opp_full; rewrite Z.mod_small ; try lia.
      replace ( 2 ^ Z.of_nat size - φ (1)%int63)%Z
        with (Z.pred (2 ^ Z.of_nat size))%Z by lia.
      rewrite <- Z.ones_equiv.
      rewrite Z.testbit_ones_nonneg by lia.
      destruct ((p < n)%int63 && (p < 63)%int63) eqn:T2.
      unfold size in *; lia.
      unfold size in *; lia.
  Qed.


  Definition split_m (i: int) (m: int) :=
    ( (i land ((ones digits) << m)) lor ((i land (ones m))))%int63.

  Lemma split_all : forall i m,
      i = split_m i m.
  Proof.
    intros.
    unfold split_m.
    apply bit_ext.
    intros.
    rewrite lor_spec.
    rewrite Int63.land_spec.
    rewrite bit_lsl.
    rewrite Int63.land_spec.
    rewrite! bit_ones.
    generalize (bit_M i n).
    destruct ((n < m)%int63 || (digits ≤ n)%int63) eqn:T1.
    destruct ((n < m)%int63 && (n < 63)%int63) eqn:T2.
    - unfold digits in *.
      destruct (bit i n); try lia.
    - unfold digits in *.
      destruct (bit i n); try lia.
    - destruct ((n - m < digits)%int63 && (n - m < 63)%int63) eqn:T2.
      destruct ((n < m)%int63 && (n < 63)%int63) eqn:T3.
      unfold digits in *.
      destruct (bit i n); try lia.
      unfold digits in *.
      destruct (bit i n); try lia.
      destruct ((n < m)%int63 && (n < 63)%int63) eqn:T3.
      unfold digits in *.
      destruct (bit i n); try lia.
      unfold digits in *.
      destruct (bit i n); try lia.
  Qed.


  Definition is_set (k:int) (m:nat) :=
      (forall p, (p < m)%nat -> testbit k p = false) /\
      testbit k m = true.

  Definition is_set_int (k:int) (m:int) :=
      (forall p, (p < m = true)%int63 -> bit k p = false) /\
      bit k m = true.

  Ltac split_and :=
    match goal with
      | |- ?A /\ ?B => split ; intros; split_and
      | _ => idtac
    end.

  Definition nat_of_int (i:int) := Z.to_nat (to_Z i).

  Lemma is_set_small : forall k m, is_set k m -> m < 63.
  Proof.
    intros.
    unfold is_set in *.
    destruct H.
    unfold testbit in *.
    destruct (63 <=? m) eqn:EQ ; lia.
  Qed.

  Lemma is_set_eq :
    forall k m, is_set k  m ->
                exists n, n = int_of_nat m /\
                          (n < digits = true)%int63 /\
                          is_set_int k n.
  Proof.
    intros.
    assert (SM := is_set_small _ _ H).
    unfold is_set, is_set_int in *.
    destruct H.
    exists (int_of_nat m).
    split_and; intros.
    - reflexivity.
    - unfold digits ; lia.
    - unfold testbit in H.
      rewrite <- H with (p := nat_of_int p).
      replace (63 <=? nat_of_int p) with false by (unfold nat_of_int in* ; lia).
      f_equal. unfold nat_of_int ; lia.
      unfold nat_of_int ; lia.
    - unfold testbit in H0.
      rewrite <- H0.
      destruct (63 <=? m) ; congruence.
  Qed.

  Lemma is_set_decomp : forall k m,
      is_set k m ->
      (k = ((k >> (int_of_nat m + 1)) << (int_of_nat m + 1))  lor (1 << int_of_nat m))%int63.
  Proof.
    intros.
    apply is_set_eq in H.
    destruct H as (n & EQ & LT & SET).
    unfold is_set_int in SET.
    destruct SET as [F T].
    rewrite <- EQ.
    clear EQ.
    apply bit_ext.
    intros.
    rewrite lor_spec.
    rewrite ! bit_lsl.
    rewrite ! bit_lsr.
    assert (n0 = n \/ n0 < n = true \/ (Int63.ltb n n0  && Int63.ltb n0 digits) = true \/ (Int63.leb digits n0) = true)%int63 by lia.
    destruct H as [H | [H | [H |H]]].
    + subst.
      rewrite T.
      repeat elim_if.
      rewrite bit_1.
        lia.
    + rewrite F by auto.
      repeat elim_if.
      rewrite bit_1.
      lia.
    + rewrite andb_true_iff in H.
      destruct H.
      replace (n0 < n + 1)%int63 with false by lia.
      simpl.
      replace (digits <= n0)%int63 with false by lia.
      replace ((n0 - (n + 1) ≤ n + 1 + (n0 - (n + 1)))%int63) with true by lia.
      replace ((n + 1 + (n0 - (n + 1))))%int63 with n0 by lia.
      elim_if.
      rewrite bit_1.
      destruct (bit k n0); lia.
    + rewrite bit_M; auto.
      repeat elim_if.
      rewrite! bit_1.
      unfold digits in *.
      lia.
  Qed.



  Lemma sub_pow2 : forall x k m,
      (0 <= k < m)%Z ->
      (0<= x < 2^m)%Z  ->
      (x - x mod 2 ^ (k+1) + 2^k < 2^ m )%Z.
  Proof.
    intros.
    assert (2 ^(k +1) = 2 * 2^k)%Z.
    {
      rewrite Z.pow_add_r; lia.
    }
    rewrite H1.
    clear H1.
    assert (exists n, Z.of_nat n = m).
    {
      exists (Z.to_nat m).
      lia.
    }
    destruct H1 as (m' & EQ).
    subst.
    revert x k H0 H.
    induction m'.
    - intros.
      change (2^ Z.of_nat 0)%Z with 1%Z in *.
      assert (x = 0)%Z by lia.
      subst. lia.
    - intros.
      replace (Z.of_nat (S m'))%Z with (1 + Z.of_nat m')%Z  in * by lia.
      assert (DB : (0 <= x / 2 < 2^ Z.of_nat m')%Z).
      {
        rewrite Z.pow_add_r in H0 by lia.
        lia.
      }
      assert (k = 0 \/ 0<= k-1 < Z.of_nat m')%Z by lia.
      destruct H1.
      +  subst.
         change (2 * 2^0)%Z with 2%Z.
         rewrite Z.pow_add_r in * by lia.
         lia.
      +
        specialize (IHm' (x / 2)%Z _ DB H1).
        rewrite Z.pow_add_r by lia.
        assert (2 * 2^ (k-1) = 2 ^k)%Z.
        {
          change 2%Z with (2^1)%Z at 1.
          rewrite <- Z.pow_add_r by lia.
          f_equal. lia.
        }
        rewrite H2 in IHm'.
        assert (2^0 <= 2 ^ k)%Z.
        {
          apply Z.pow_le_mono_r; lia.
        }
        assert (2 * (x / 2 - (x / 2) mod 2 ^ k + 2 ^ (k - 1)) + 1 < 2 * 2 ^ Z.of_nat m')%Z by lia.
        eapply Z.le_lt_trans ; eauto.
        ring_simplify.
        rewrite H2.
        cut (x - x mod (2 * 2 ^ k) <=
                2 * (x / 2) - 2 * ((x / 2) mod 2 ^ k) + 1)%Z.
        lia.
        clear - H3.
        zify.
        rewrite H5 by lia.
        rewrite H10 by lia.
        assert (q1 = q0) by nia.
        lia.
  Qed.



  Lemma to_Z_branch_bit : forall k m
      (SMALL : (m < 63 = true)%int63),
      to_Z
        ((k >> (m + 1)) << (m + 1) + 1 << m)%int63 =

      ((to_Z k  / 2^ (to_Z m + 1)) * 2^ (to_Z m + 1) + 2^ (to_Z m))%Z.
  Proof.
    intros.
    rewrite add_spec.
    rewrite! lsl_spec.
    rewrite lsr_spec.
    rewrite add_spec.
    change (to_Z m + to_Z 1%int63)%Z with (to_Z m + 1)%Z.
    assert (B1 : (0 <= φ (1)%int63 * 2 ^ φ (m)%int63 < wB)%Z).
    {
      replace (φ (1)%int63 * 2 ^ φ (m)%int63)%Z with (2 ^ to_Z m)%Z by lia.
      split.
      apply Z.pow_nonneg.
      lia.
      unfold wB.
      apply Z.pow_lt_mono_r.
      lia. unfold size.
      lia. unfold size.
      lia.
    }
    assert (B2 : (2^1 <= 2 ^ ((φ (m)%int63 + 1)))%Z).
    {
      apply Z.pow_le_mono_r.
      lia.
      lia.
    }
    assert (B3 :  (0 <=  φ (k)%int63 / 2 ^ ((φ (m)%int63 + 1)))%Z).
    {
      nia.
    }
    assert (B4 :  (0 <=
   φ (k)%int63 / 2 ^ ((φ (m)%int63 + 1) mod wB) * 2 ^ ((φ (m)%int63 + 1) mod wB) <
   wB)%Z).
    {
    unfold wB in *.
      change (Z.of_nat size) with 63%Z in *.
      rewrite Z.mod_small by lia.
      split.
      apply Z.mul_nonneg_nonneg ; nia.
      nia.
    }
    rewrite! Z.mod_small; auto.
    - lia.
    - unfold wB.
      change (Z.of_nat size) with 63%Z.
      lia.
    - rewrite Z.mod_small;auto.
      rewrite Z.mod_small;auto.
      rewrite Z.mod_small;auto.
      split.
      lia.
      clear B4.
      unfold wB in *.
      change (Z.of_nat size) with 63%Z.
      assert (φ (k)%int63 / 2 ^ (φ (m)%int63 + 1) * 2 ^ (φ (m)%int63 + 1) =
              to_Z k - to_Z k mod 2 ^ (φ (m)%int63 + 1))%Z.
      nia.
      rewrite H.
      change (to_Z 1%int63) with 1%Z.
      rewrite Z.mul_1_l.
      apply sub_pow2.
      lia.
      lia.
      unfold wB.
      change (Z.of_nat size) with 63%Z.
      lia.
  Qed.

  Lemma testbit_0 : forall a n,
      (0 <= n)%Z ->
      Z.testbit a n = ((a / 2 ^ n) mod 2 =? 1)%Z.
  Proof.
    intros.
    generalize  (Z.testbit_true a n H).
    destruct (Z.testbit a n); intuition.
    - rewrite H0. reflexivity.
    - assert ((a / 2 ^ n) mod 2 = 0 \/ a / 2 ^ n mod 2 = 1)%Z.
      clear. lia.
      destruct H0.
      rewrite H0. reflexivity.
      intuition congruence.
  Qed.


  Definition not_int (x : int) := (- x - 1)%int63.

  Lemma bit_not_int : forall x n
      (SN : (n < digits = true)%int63),
      bit (not_int x) n = negb (bit x n).
  Proof.
    unfold not_int.
    intros.
    rewrite! bitE.
    unfold Int63.opp.
    rewrite sub_spec.
    assert (x = 0 \/ x <> 0)%int63 by lia.
    destruct H.
    - subst.
      change (to_Z (0 - 0)%int63) with 0%Z.
      rewrite Z.bits_0. simpl.
      change ( - to_Z 1%int63 mod wB)%Z with (wB - 1)%Z.
      assert (nat_of_int n <= 62).
      { unfold nat_of_int, digits in * ; lia. }
      replace (to_Z n) with (Z.of_nat (nat_of_int n)) by
          (unfold nat_of_int in * ; lia).
      set (P := fun n =>   Z.testbit (wB - 1) (Z.of_nat n)).
      change (P (nat_of_int n) = true).
      eapply (forall_n_correct _ 62); auto.
    -
      rewrite sub_spec.
      rewrite Z.sub_0_l.
      unfold digits in SN.
      rewrite Z.mod_opp_l_nz.
      rewrite (Z.mod_small  (to_Z x)%Z).
      rewrite Z.mod_small.
      rewrite <- (Z.opp_involutive  (wB - φ (x)%int63 - φ (1)%int63)).
      rewrite Z.bits_opp.
      f_equal.
      replace ((Z.pred (- (wB - φ (x)%int63 - φ (1)%int63))))%Z with
          (to_Z x + (-1) * wB)%Z by lia.
      rewrite! testbit_0 by lia.
      replace (-1 * wB)%Z with ((2 * (-1 * 2^(62 - to_Z n))) * 2^(to_Z n))%Z.
      rewrite Z_div_plus.
      rewrite Z.mul_comm.
      rewrite Z_mod_plus_full.
      reflexivity.
      apply pow2_pos.
      lia.
      unfold wB.
      change (Z.of_nat size) with 63%Z.
      replace 63%Z with (1 + (62 - to_Z n) + to_Z n)%Z by lia.
      rewrite! Z.pow_add_r.
      all: try (change wB with (2^63)%Z ; lia).
  Qed.


  Lemma opp_spec : forall x, (- x = not_int x + 1)%int63.
  Proof.
    unfold not_int.
    intros. lia.
  Qed.

  Lemma bit_ext' : forall a b,
      (forall n, n < digits = true -> bit a n = bit b n)%int63 ->
      a = b.
  Proof.
    intros.
    apply bit_ext.
    intros.
    assert (digits <= n = true \/ n < digits = true)%int63 by lia.
    destruct H0.
    - rewrite! bit_M by auto.
      reflexivity.
    - apply H ; auto.
  Qed.

  Lemma not_int_lor : forall a b,
      (not_int (a lor b) = (not_int a) land (not_int b))%int63.
  Proof.
    intros.
    apply bit_ext'; intros.
    rewrite Int63.land_spec.
    rewrite! bit_not_int by auto.
    rewrite Int63.lor_spec.
    apply negb_orb.
  Qed.

  Definition bit_excl (x y: int) :=
    (forall n : int, bit x n = true -> bit y n = true -> False).


  Lemma lsl_1_spec : forall n,
      (n < digits = true)%int63 ->
      (φ (1 << n)%int63 = 2 ^ to_Z n)%Z.
  Proof.
    intros.
    rewrite lsl_spec.
    rewrite Z.mod_small.
    lia.
    replace (φ (1)%int63 * 2 ^ φ (n)%int63)%Z with
        (2^ to_Z n)%Z by lia.
    split.
    apply Z.pow_nonneg. lia.
    unfold wB.
    unfold size.
    apply  Z.pow_lt_mono_r. lia.
    lia.
    unfold digits in *; lia.
  Qed.

  Lemma bit_pred_1_lsl : forall n i ,
      (n < digits = true)%int63 ->
      (bit (1 << n - 1) i)%int63 =  (to_Z i <? to_Z n)%Z.
  Proof.
    intros.
    rewrite bitE.
    rewrite sub_spec.
    rewrite Z.mod_small.
    rewrite lsl_1_spec by auto.
    replace (2 ^ φ (n)%int63 - φ (1)%int63)%Z with
          (Z.pred (2 ^ (to_Z n)))%Z by lia.
    rewrite <- Z.ones_equiv.
    apply Z.testbit_ones_nonneg.
    lia.
    lia.
    rewrite lsl_1_spec by auto.
    assert (2^0 <= 2 ^ to_Z n)%Z.
    { apply Z.pow_le_mono_r ; lia. }
    unfold wB, size. change (Z.of_nat 63) with 63%Z.
    assert (2^ to_Z n < 2 ^ 63)%Z.
    {
      apply Z.pow_lt_mono_r. lia.  lia.
      unfold digits in * ; lia.
    }
    lia.
  Qed.


  Lemma not_int_lsl : forall k m,
      (m < digits = true)%int63 ->
      (not_int ((k >> (m+1)) << (m+1) lor (1 << m)) =
         (((not_int k) >> (m+1) << (m+1)) lor (1 << m - 1)))%int63.
  Proof.
    intros.
    apply bit_ext'; intros.
    rewrite! bit_not_int by auto.
    rewrite! Int63.lor_spec.
    rewrite bit_pred_1_lsl by auto.
    rewrite bit_lsl.
    rewrite! bit_lsr.
    rewrite! bit_lsl.
    rewrite bit_lsr.
    rewrite bit_not_int by lia.
    replace ((m + 1 + (n - (m + 1))))%int63 with n by (unfold digits in * ; lia).
    rewrite bit_1.
    repeat elim_if.
    intuition try lia.
    destruct (bit k n); lia.
  Qed.


  Lemma bit_add_or :
    forall x y : int,
      (forall n : int, bit x n = true -> bit y n = true -> False) ->
      (x + y)%int63 = (x lor y)%int63.
  Proof.
    intros.
    now apply Int63.bit_add_or.
  Qed.


  Lemma opp_mask : forall k m,
      (m < digits = true)%int63 ->
      (- ((k >> (m + 1)) << ( m + 1) lor 1 <<  m)
      =
      (((not_int k) >> (m+1)) << (m+1)) lor ((1 << m)))%int63.
  Proof.
    intros.
    rewrite opp_spec.
    rewrite! not_int_lsl by auto.
    repeat rewrite <- bit_add_or.
    lia.
    - intros.
      rewrite bit_lsl in H1.
      rewrite bit_1 in H1.
      rewrite bit_lsl in H0.
      rewrite bit_lsr in H0.
      revert H0 H1.
      repeat elim_if.
      intuition try lia.
    - intros.
      rewrite bit_pred_1_lsl in H1 by lia.
      rewrite bit_lsl in H0.
      revert H0 H1.
      elim_if; intuition try lia.
  Qed.

  Lemma LPO : forall (k:Int63.int), k <> zero -> exists p, testbit k p = true.
  Proof.
    intros.
    unfold zero in *.
    assert (LPO: (exists p, ((p < int_of_nat size) = true) /\ (bit k p = true))%int63).
    {
      case (to_Z_bounded k).
      unfold wB.
      assert (0 < size <= 63).
      {
        unfold size. lia.
      }
      revert k H.
      induction size; try lia.
      intros.
      assert (n = 0 \/ 0 < n) by lia.
      destruct H3.
      - subst.
        assert (k = one).
        {
          change (2 ^Z.of_nat 1)%Z with 2%Z in H2.
          unfold one. lia.
        }
        subst.
        exists 0%int63.
        split. unfold int_of_nat.  lia.
        apply bit_1.
      -
        assert ((k >> 1) = 0 \/ (k  >> 1) <> 0)%int63 by lia.
        destruct H4.
        + exists 0%int63.
          unfold int_of_nat.
          split.
          lia.
          destruct (bit k 0) eqn:B0;auto.
          rewrite (bit_split k) in H.
          rewrite B0 in H.
          rewrite H4 in H.
          compute in  H.
          lia.
        +
          assert (exists p : int, (p < int_of_nat n)%int63 = true /\ bit (k >> 1) p = true).
          {
            apply IHn ; auto.
            lia.
            lia.
            rewrite lsr_spec.
            replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z in H2 by lia.
            rewrite Z.pow_add_r  in H2 by lia.
            lia.
          }
          destruct H5.
          exists (x+1)%int63.
          split.
          unfold int_of_nat in *.
          lia.
          destruct H5.
          rewrite bit_lsr in H6.
          destruct ((x ≤ 1 + x)%int63) eqn:EQ ; try lia.
          rewrite <- H6.
          f_equal. lia.
    }
    destruct LPO.
    exists (Z.to_nat (to_Z x)).
    unfold testbit.
    destruct (63 <=? Z.to_nat (to_Z x))%int63 eqn:LE.
    unfold int_of_nat,size in H0.
    lia.
    destruct H0.
    rewrite <- H1.
    f_equal.
    unfold int_of_nat; lia.
  Qed.


  Definition lowest_bit (x: int) :=  (x land (opp x))%int63.

  Fixpoint find_lowest (n: nat) (k: int) (p: nat) :=
    match p with
    | O => n
    | S q => if testbit k (n - p)%nat then (n - p)%nat else find_lowest n k q
    end.

  Require Import Cdcl.Coqlib.

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

  Lemma lopp_spec_low:
    forall k m,
      (forall p, (p < m)%nat -> testbit k p = false) ->
      testbit k m = true ->
      forall p, (p < m)%nat -> testbit (Int63.opp k) p = false.
  Proof.
    intros.
    assert (IS : is_set k m).
    { unfold is_set ; auto. }
    assert (MSMALL := is_set_small k m IS).
    apply is_set_decomp in IS.
    rewrite IS.
    rewrite opp_mask by (unfold digits; lia).
    unfold testbit.
    replace (int_of_nat (Init.Nat.min p 62)) with (int_of_nat p) by lia.
    rewrite Int63.lor_spec.
    rewrite bit_lsl.
    rewrite bit_lsl.
    rewrite bit_1.
    repeat elim_if ; lia.
  Qed.


  Lemma lopp_spec_eq: forall k m,
      (forall p, (p < m)%nat -> testbit k p = false) ->
      testbit k m = true ->
      testbit (Int63.opp k) m = true.
  Proof.
    intros.
    assert (IS : is_set k m).
    { unfold is_set ; auto. }
    assert (MSMALL := is_set_small k m IS).
    apply is_set_decomp in IS.
    rewrite IS.
    rewrite opp_mask by (unfold digits; lia).
    unfold testbit.
    replace (int_of_nat (Init.Nat.min m 62)) with (int_of_nat m) by lia.
    rewrite Int63.lor_spec.
    rewrite bit_lsl.
    rewrite bit_lsl.
    rewrite bit_1.
    unfold digits.
    repeat elim_if ; lia.
  Qed.

    Definition digits := Some 63%nat.

  Lemma testbit_M : forall k n, le_o digits n -> testbit k n = false.
  Proof.
    simpl.
    intros. unfold testbit.
    replace (63 <=? n)%nat with true by lia.
    reflexivity.
  Qed.




  Lemma lopp_spec_high: forall k m, (forall p, (p < m)%nat -> testbit k p = false) -> testbit k m = true ->
                                    forall p, (p > m)%nat -> ~ le_o digits p ->  testbit (Int63.opp k) p = negb (testbit k p).
  Proof.
    intros.
    assert (IS : is_set k m).
    { unfold is_set ; auto. }
    assert (MSMALL := is_set_small k m IS).
    apply is_set_decomp in IS.
    rewrite IS. clear IS.
    simpl in H2.
    rewrite opp_mask by (unfold Int63.digits; lia).
    unfold testbit.
    replace (63 <=?p)%nat with false by lia.
    rewrite! Int63.lor_spec.
    rewrite bit_lsl.
    rewrite! bit_lsl.
    rewrite bit_1.
    rewrite! bit_lsr.
    unfold Int63.digits.
    repeat elim_if ; intuition try lia.
    + rewrite bit_not_int by (unfold Int63.digits ; lia).
    destruct (bit k (int_of_nat m + 1 + (int_of_nat p - (int_of_nat m + 1)))).
    lia.
    lia.
  Qed.


  Lemma ltb_spec: forall m1 n1 m2 n2, is_mask m1 n1 -> is_mask m2 n2 -> (Int63.ltb m1 m2 = true <-> (n1 < n2)%nat).
  Proof.
    intros.
    apply mask_spec in H.
    apply mask_spec in H0.
    destruct (63 <=? n1)%nat eqn:N1; [tauto|].
    destruct (63 <=? n2)%nat eqn:N2; [tauto|].
    subst.
    assert (NS : (n1 <= 62)%nat) by lia.
    assert (NP : (n2 <= 62)%nat) by lia.
    rewrite <- Nat.ltb_lt.
    apply eqb_iff.
    set (Q:= fun n1 n2=>   Bool.eqb (one << int_of_nat n1 < one << int_of_nat n2)%int63 (n1 <? n2)%nat).
    change (Q n1 n2 = true).
    eapply (forall_2n_correct _ 62 62);auto.
  Qed.

Instance KInt : Keys_Base.Key  Int63.int :=
    {|
      Keys_Base.eqb:= Int63.eqb;
      Keys_Base.testbit:= testbit;
      Keys_Base.interp:= (fun i => (Int63.sub i one));
      Keys_Base.land:= Int63.land;
      Keys_Base.lxor:= Int63.lxor;
      Keys_Base.lopp:= Int63.opp;
      Keys_Base.ltb:= Int63.ltb;
      Keys_Base.digits := digits;
      Keys_Base.testbit_M := testbit_M;
      Keys_Base.zero_spec:= zero_spec;
      Keys_Base.eqb_spec := KeyInt.eqb_spec;
      Keys_Base.testbit_spec:= testbit_spec;
      Keys_Base.interp_spec:= interp_spec;
      Keys_Base.land_spec:= land_spec;
      Keys_Base.lxor_spec:= lxor_spec;
      Keys_Base.lopp_spec_low:= lopp_spec_low;
      Keys_Base.lopp_spec_eq:= lopp_spec_eq;
      Keys_Base.lopp_spec_high:= lopp_spec_high;
      Keys_Base.ltb_spec:= ltb_spec;
      Keys_Base.LPO := LPO;
  |}.
