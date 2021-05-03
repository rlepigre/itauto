(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Cdcl.Itauto.
Require Import Lia.

Ltac no_tac :=
  match goal with
  | H : ?X -> False |-  False => apply H ; no congruence lia
  |  _  => no congruence lia
  end.

  

Ltac smt :=
  let tac := no_tac in
  itauto tac.

(* Missing in ZifyClasses *)
Register ZifyClasses.InjTyp as ZifyClasses.InjTyp.
Register ZifyClasses.CstOp as ZifyClasses.CstOp.
Register ZifyClasses.UnOp as ZifyClasses.UnOp.
Register ZifyClasses.BinOp as ZifyClasses.BinOp.
Register ZifyClasses.BinRel as ZifyClasses.BinRel.
