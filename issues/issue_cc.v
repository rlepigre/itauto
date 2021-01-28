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
  itautor reflexivity.
Qed.

Goal forall (A: Prop) (B:Type),
True <-> (forall l' : B, False -> A).
Proof.
  intros.
  itautor idtac.
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

Goal forall
    (ok : list Z -> Prop)
    (x l h : Z)
    (s : list Z)
    (BOUNDS : l < h)
    (H : ok s)
    (l0 h0 : Z)
    (g : h >= l0)
    (g0 : h0 >= l),
    Z.min l l0 <= x < Z.max h h0 \/ In x s <-> l0 <= x < h0 \/ l <= x < h \/ In x s.
Proof.
  intros.
  let t := solve[lia|itauto lia] in
  gen_conflicts t.
  revert g0.
  vitautog.
Qed.


Goal forall l x l0 s h h0,
  (l <= x -> (Z.min l l0 <= x -> False) -> False) ->
  (x < h -> (x < Z.max h h0 -> False) -> False) ->
  (x < Z.max h h0 -> In x s \/ x < h0 \/ x < h) ->
  (l < h -> h >= l0 -> Z.min l l0 <= x -> x < Z.max h h0 -> In x s \/ l0 <= x \/ x < h) ->
  (l < h -> h0 >= l -> l0 <= x -> In x s \/ x < h0 \/ l <= x) ->
  (l < h -> h >= l0 -> In x s \/ x < h0 \/ l <= x \/ x < h) ->
  (Z.min l l0 <= x -> In x s \/ l0 <= x \/ l <= x) ->
  (l < h -> Z.min l l0 <= x -> In x s \/ l0 <= x \/ l <= x \/ x < h) ->
  (l < h -> h >= l0 -> In x s \/ l0 <= x \/ x < h0 \/ l <= x \/ x < h) ->
  (l0 <= x -> (Z.min l l0 <= x -> False) -> False) ->
  (x < h0 -> (x < Z.max h h0 -> False) -> False) ->
  h0 >= l ->
  h >= l0 ->
  l < h ->
  (Z.min l l0 <= x < Z.max h h0 \/ In x s -> l0 <= x < h0 \/ l <= x < h \/ In x s) /\
  (l0 <= x < h0 \/ l <= x < h \/ In x s -> Z.min l l0 <= x < Z.max h h0 \/ In x s).
Proof.
  itauto idtac.
Qed.

Ltac mp :=
  repeat match goal with
         | H : ?A -> ?B , H1 : ?A |- _ => specialize (H H1)
         end.


