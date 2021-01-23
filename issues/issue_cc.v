Require Import  Cdcl.Itauto.
Require Import List ZArith Lia.
Open Scope Z_scope.

Variables A B : Set.
Variable P : A -> bool.
Variable R : A -> B -> Prop.
Definition Q (b : B) (r : A) :=  P r = true -> R r b.

Goal forall
    (b : B)
    (r r0 : A)
    (H0 : Q b r)
    (H1 : r = r0),
  Q b r0.
Proof.
  intros.
  Fail congruence.
  Opaque Q.
  itauto congruence.
Qed.

Goal  (False -> False \/ False) /\ (False \/ False -> False).
Proof.
  itauto idtac.
Qed.

(* Set as left hand side -> ignored *)
Goal true = true <-> (Z -> False <-> False).
Proof.
  split;intros.
  itauto reflexivity.
  itauto reflexivity.
Qed.

Goal forall (A: Prop) (B:Type),
True <-> (forall l' : B, False -> A).
Proof.
  intros.
  let t := itauto idtac in
  itauto t.
Qed.

Goal forall (A: Prop),
    False <-> False /\ A.
Proof.
  itauto idtac.
Qed.

Goal forall (mem: Type) (block: Type) (perm_kind permission: Type)
            (perm : mem -> block -> Z -> perm_kind -> permission -> Prop)
     (m m' : mem)
     (b : block)
     (lo hi : Z)
     (A : 0 <= lo)
     (C : forall (i : Z) (k : perm_kind) (p : permission),
      lo <= i < hi -> perm m b i k p)
     (H0 : forall (i : Z) (k : perm_kind) (p : permission),
       lo <= i < hi -> perm m b i k p -> perm m' b i k p)
     (i : Z)
     (k : perm_kind)
     (p : permission)
     (H1 : lo <= i)
     (H2 : i < hi),
perm m' b i k p.
Proof.
  intros.
  itauto auto.
Qed.

Goal forall (A B:Prop),
    A -> B ->
    A /\ B \/ (A /\ False).
Proof.
  intros.
  itauto idtac.
Qed.


Goal forall (ident: Type) (debuginfo: Type)
            (v' : ident)
            (i' : debuginfo),
    v' = v' /\ i' = i' \/ (v' <> v' /\ False).
Proof.
  intros.
  itauto congruence.
Qed.

Goal (True -> False) -> False.
  itauto idtac.
Qed.
