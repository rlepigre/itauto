Require Import Cdcl.Itauto.

Goal forall (P:Prop), ~ ~ P -> P.
  Fail itauto.
Abort.

Require Import Classical.
Goal forall (P:Prop), ~ ~ P -> P.
  Fail itauto.
Abort.

Require Import Cdcl.Ctauto.

Test Itauto Classic.

Goal forall (P:Prop), ~ ~ P -> P.
  itauto.
Abort.
