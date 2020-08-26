Require Import Cdcl.Itauto.

Require Import Bool  ZArith Lia.

Open Scope Z_scope.
Lemma l1 : forall (x:Z), x >= 0 -> x <= 0 -> x <> 0 -> False.
Proof.
  intros.
  itauto lia.
Qed.

Lemma cc : forall (A:Type) (a b c:A) (d e:Z),
    d >= e ->
    a = b -> b = c -> a = c.
Proof.
  intros.
  itauto congruence.
Qed.

Lemma false_true :  Is_true (false) -> Is_true true.
Proof. itauto. Qed.


Lemma true_andb_true : Is_true (true && true).
Proof.
  intros.
  itauto.
Qed.

Lemma x_andb_true : forall x, Is_true (x && true) -> Is_true x.
Proof.
  intros.
  itauto.
Qed.

Instance Zge_dec : DecP2 Z.ge.
Proof.
 unfold DecP2. intros. lia.
Qed.

Instance Zle_dec : DecP2 Z.le.
Proof.
 unfold DecP2. intros. lia.
Qed.

Instance Zeq_dec : DecP2 (@eq Z).
Proof.
 unfold DecP2. intros. lia.
Qed.


Lemma l2 : forall (x:Z), x >= 0 -> x <= 0 -> x <> 0 -> False.
Proof.
  intros.
  itauto lia.
Qed.

Lemma comb : forall (p: Prop) (x: Z),
    p ->
    (p -> x = 0) ->  x = 0.
Proof.
  intros.
  Fail lia.
Abort.

Lemma comb2 : forall (p: Prop) (x: Z),
    p ->
    (p -> x = 0) ->  x = 0.
Proof.
  intros.
  intuition lia.
Qed.

Lemma combt : forall (p: Prop) (x: Z),
    p ->
    (p -> x = 0) ->  x = 0.
Proof.
  intros.
  tauto.
Qed.

Lemma comb3 : forall (p: Prop) (x: Z),
    x >= 0 -> x <= 0 ->
    (x = 0 -> p) -> p.
Proof.
  intros.
  Fail intuition lia.
  itauto lia.
Qed.

Lemma comp_congr : forall (T:Type) (a b c:T) (p:Prop),
    a = b -> b = c -> (a = c -> p) -> p.
Proof.
  Fail intuition congruence.
  itauto congruence.
Qed.

(* From https://github.com/coq/coq/issues/10743#issuecomment-643391083 *)

Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Axiom word: Type.
Axiom stmt: Type.
Axiom stackalloc_size: stmt -> Z.
Axiom bytes_per_word: Z.
Axiom list_union: forall {A: Type}, (A -> A -> bool) -> list A -> list A -> list A.
Axiom modVars_as_list: (Z -> Z -> bool) -> stmt -> list Z.

Module word.
  Axiom of_Z: Z -> word.
End word.

Declare Scope word_scope.
Notation "! n" := (word.of_Z n) (at level 0, n at level 0, format "! n") : word_scope.
Notation "# n" := (Z.of_nat n) (at level 0, n at level 0, format "# n") : word_scope.
Delimit Scope word_scope with word.
Open Scope word_scope.

Open Scope Z_scope.

Goal forall (rem_framewords : Z) (program_base : word) (pos : Z) (pos0 : Z) (body: stmt)
            (unused_scratch old_argvals old_retvals : list word) (old_ra : word)
            (old_modvarvals ToSplit old_scratch : list word)
            (argnames retnames: list Z),
  0 <= rem_framewords ->
  rem_framewords +
  (stackalloc_size body / bytes_per_word +
   #(length argnames + length retnames + 1 +
     length (list_union Z.eqb (modVars_as_list Z.eqb body) argnames))) <=
  #(length
      ((((((ToSplit ++ old_scratch) ++ old_modvarvals) ++ [old_ra]) ++ old_retvals) ++ old_argvals) ++
       unused_scratch)) ->
  bytes_per_word = 4 \/ bytes_per_word = 8 ->
  0 <= stackalloc_size body / bytes_per_word ->
  length
    (((((ToSplit ++ old_scratch) ++ old_modvarvals) ++ [old_ra]) ++ old_retvals) ++ old_argvals) =
  (length
     ((((((ToSplit ++ old_scratch) ++ old_modvarvals) ++ [old_ra]) ++ old_retvals) ++ old_argvals) ++
      unused_scratch) - Z.to_nat rem_framewords)%nat ->
  length unused_scratch = Z.to_nat rem_framewords ->
  length ((((ToSplit ++ old_scratch) ++ old_modvarvals) ++ [old_ra]) ++ old_retvals) =
  (length
     (((((ToSplit ++ old_scratch) ++ old_modvarvals) ++ [old_ra]) ++ old_retvals) ++ old_argvals) -
   length argnames)%nat ->
  length old_argvals = length argnames ->
  length (((ToSplit ++ old_scratch) ++ old_modvarvals) ++ [old_ra]) =
  (length ((((ToSplit ++ old_scratch) ++ old_modvarvals) ++ [old_ra]) ++ old_retvals) -
   length retnames)%nat ->
  length old_retvals = length retnames ->
  length ((ToSplit ++ old_scratch) ++ old_modvarvals) =
  (length (((ToSplit ++ old_scratch) ++ old_modvarvals) ++ [old_ra]) - 1)%nat ->
  length [old_ra] = 1%nat ->
  length (ToSplit ++ old_scratch) =
  (length ((ToSplit ++ old_scratch) ++ old_modvarvals) -
   length (list_union Z.eqb (modVars_as_list Z.eqb body) argnames))%nat ->
  length old_modvarvals = length (list_union Z.eqb (modVars_as_list Z.eqb body) argnames) ->
  length ToSplit =
  (length (ToSplit ++ old_scratch) - Z.to_nat (stackalloc_size body / bytes_per_word))%nat ->
  length old_scratch = Z.to_nat (stackalloc_size body / bytes_per_word) ->
  length old_scratch = Z.to_nat (stackalloc_size body / bytes_per_word) /\
  length old_modvarvals = length (list_union Z.eqb (modVars_as_list Z.eqb body) argnames) /\
  length old_retvals = length retnames /\
  length old_argvals = length argnames /\
  length unused_scratch = Z.to_nat rem_framewords.
Proof.
  intros.
  (* zify. (* creates many disjunctions of the form "0 < z /\ z0 = z \/ z <= 0 /\ z0 = 0" *) *)
  (* Time repeat split; assumption. (* 0 secs *) *)
  Time itauto lia.
Qed.


Goal
  forall x y,
   (x = 0 -> y = 0) ->
   (x = 1 -> y = 0) ->
   (~ (x = 0 \/ x = 1) -> y = 0) ->
   y = 0.
Proof.
  intros.
  unfold not in *.
  itauto lia.
Qed.

Require Import Bool.

Open Scope bool_scope.
Require Import ZifyClasses.
Program Instance Op_eq_bool : BinRel (@eq bool) :=
  {TR := fun x y => Is_true (implb x y) /\ Is_true (implb y x) ; TRInj := _ }.
Next Obligation.
  destruct n,m; simpl; intuition congruence.
Qed.
Add Zify BinRel Op_eq_bool.

Program Instance Op_negb : UnOp negb :=
  {TUOp := fun x => implb x false ;  TUOpInj:= _ }.
Add Zify UnOp Op_negb.

Goal forall b, orb b true = true.
Proof.
  intros.
  zify;
  itauto idtac.
Qed.

Goal forall b, andb b b = b.
Proof.
  intros.
  zify.
  itauto idtac.
Qed.

Goal forall b b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14
            b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27
            b28 b29 b30 b31 : bool,
    (b && negb b0 || b1 && b2 || b3 && b4 || b5 && b6 ||
     b7 && b8 || b9 && b10 || b11 && b12
     || b13 && b14) && negb b15 =
    b16 && negb b17 || b18 && b19 || b20 && b21 || b22 && b23
    || b24 && b25 || b26 && b27
    || b28 && b29 || b30 && b31.
Proof.
  intros.
  zify.
  clear.
  Fail itauto idtac.
Abort.



Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.
Open Scope Z_scope.

Goal
  forall (r2 : Z) (L : nat),
  r2 = 8 * Z.of_nat L ->
  r2 <> 0 ->
  0 <= Z.of_nat L ->
  forall q r r1 : Z,
  (2 ^ r1 <> 0 -> r2 = 2 ^ r1 * q + r) ->
  (0 < 2 ^ r1 -> 0 <= r < 2 ^ r1) ->
  (2 ^ r1 < 0 -> 2 ^ r1 < r <= 0) ->
  (2 ^ r1 = 0 -> q = 0) ->
  (2 ^ r1 = 0 -> r = 0) ->
  forall q0 r0 M : Z,
  (M <> 0 -> 3 = M * q0 + r0) ->
  (0 < M -> 0 <= r0 < M) ->
  (M < 0 -> M < r0 <= 0) ->
  (M = 0 -> q0 = 0) ->
  (M = 0 -> r0 = 0) ->
  forall q1 : Z,
  (M <> 0 -> 4 = M * q1 + r1) ->
  (0 < M -> 0 <= r1 < M) ->
  (M < 0 -> M < r1 <= 0) ->
  (M = 0 -> q1 = 0) ->
  (M = 0 -> r1 = 0) ->
  forall q2 y1 y2 : Z,
  (M <> 0 -> y2 - y1 = M * q2 + r2) ->
  (0 < M -> 0 <= r2 < M) ->
  (M < 0 -> M < r2 <= 0) ->
  (M = 0 -> q2 = 0) -> (M = 0 -> r2 = 0) ->
  0 <= y2 - (y1 + q * 2 ^ r0 + 8) < M.
Proof.
  intros.
  Fail itauto lia.
Abort.

Require Import Classical.


Lemma discr : forall {A:Type} (a: A), a::nil = nil -> a::nil = a::nil -> False.
Proof.
  intros.
  itauto congruence.
Qed.

Lemma ifb : forall (P: bool -> Prop) (a b c:bool),
    P(if a then b else c) <-> ((a = true -> P b) /\ (a = false -> P c)).
Proof.
  intros.
  destruct a ; intuition try congruence.
Qed.

Lemma ifb_eq : forall (a b c: bool),
    (if a then b else c) = andb (implb a b) (implb (negb a) c).
Proof.
  intros.
  destruct a,b,c; simpl; auto.
Qed.

Lemma is_true_eq : forall b, is_true b <-> Is_true b.
Proof.
  unfold is_true.
  destruct b; simpl;
  intuition congruence.
Qed.

Lemma negb_eq : forall b, negb b = implb b false.
Proof.
  destruct b ; simpl; auto.
Qed.

Lemma test_orb a b : (if a || b then negb (negb b && negb a) else negb a && negb b) = true.
Proof.
  rewrite ifb_eq.
  match goal with
  | |- ?A = true => change (is_true A)
  end.
  rewrite is_true_eq.
  repeat rewrite negb_eq.
  itauto.
Time Qed.

Lemma test_orb2 : forall a b,
  Is_true
    (implb (a || b) (implb (implb b false && implb a false) false) &&
     implb (implb (a || b) false) (implb a false && implb b false)).
Proof.
  itauto.
Time Qed.

