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
  Proof using.
    intros.
    itauto lia.
  Qed.

  Lemma foo3: forall (a: nat), a + a = a * 2.
  Proof using o x.
    intros.
    revert o.
    itauto lia.
  Qed.

End TEST.

About foo1. (* foo1 : forall a : nat, a + a = a * 2 *)
About foo2. (* foo2 : forall a : nat, a + a = a * 2 *)
About foo3. (*forall x : nat, ok x -> forall a : nat, a + a = a * 2*)

Ltac same_type T1 T2 :=
  let t1 := type of T1 in
  let t2 := type of T2 in
  match constr:((t1,t2)) with
  | (?X,?X) => exact I
  |   _     => fail
  end.

Goal True.
  same_type foo1 foo2.
Qed.

Goal True.
  Fail same_type foo1 foo3.
Abort.
