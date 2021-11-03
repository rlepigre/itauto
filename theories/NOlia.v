(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Cdcl.Itauto.
Require Import ZifyClasses Lia.

Record ZarithThy : Type.

(** Get the theory from zify *)

#[export] Instance CstOpThy (S T: Type) (I : InjTyp S T) (C: S) (COp : @CstOp S T C I) :
  TheorySig ZarithThy C := {}.

#[export] Instance UnOpThy (S1 S2 T1 T2: Type)
         (I1 : InjTyp S1 T1) (I2 : InjTyp S2 T2)
         (unop : S1 -> S2)
         (UOp : @UnOp S1 S2 T1 T2 unop I1 I2) :
  TheorySig ZarithThy  unop := {}.

#[export] Instance BinOpThy (S1 S2 S3 T1 T2 T3: Type)
         (I1 : InjTyp S1 T1) (I2 : InjTyp S2 T2)
         (I3 : InjTyp S3 T3)
         (binop : S1 -> S2 -> S3)
         (BOp : @BinOp S1 S2 S3 T1 T2 T3 binop I1 I2 I3) :
  TheorySig ZarithThy  binop := {}.

#[export] Instance BinRelThy (S T: Type) (I: InjTyp S T) (R: S -> S -> Prop)
         (BR : @BinRel S T R I) : TheorySig ZarithThy  R := {}.

#[export] Instance InjTypThy (S T: Type) (I: InjTyp S T) : TheoryType ZarithThy S := {}.

Ltac smt := itauto (no ZarithThy congruence lia).
