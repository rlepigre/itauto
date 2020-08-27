Require Import Cdcl.Itauto.
Require Import Lia.

Record ok (n: nat) := { getOk1: n <= 10 }.

Record ok' := { getP: Prop; getOk': getP }.

Section TEST.
  Context (x: nat).
  Context (o: ok x).
  Context (o': ok').

  Lemma foo1: forall (a: nat), a + a = a * 2.
  Proof.
    intuition lia.
  Qed.

  Lemma foo2: forall (a: nat), a + a = a * 2.
  Proof.
    intros.
    itauto lia.
  Qed.

  Ltac itauto_use_tauto ::= constr:(true).

  Lemma foo3: forall (a: nat), a + a = a * 2.
  Proof.
    intros.
    itauto lia.
  Qed.


End TEST.

About foo1. (* foo1 : forall a : nat, a + a = a * 2 *)
About foo2. (* foo2 : forall x : nat, ok x -> forall a : nat, a + a = a * 2 *)
About foo3. (* foo2 : forall x : nat, a + a = a * 2 *)
