Require Export Cdcl.Itauto.
From Coq Require Import Zify.
From Coq Require Import Lia.
(** itauto is using the `classic` axiom if available *)
#[export] Unset Itauto Use Implication Clauses.

Ltac lia := zify ; itauto (xlia zchecker).
