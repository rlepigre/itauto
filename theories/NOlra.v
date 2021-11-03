(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Cdcl.Itauto.
Require Import ZifyClasses Lra Reals.

Record RarithThy : Type.

#[export] Instance RThy  : TheoryType RarithThy R := {}.

#[export] Instance R0Thy     : TheorySig RarithThy R0 := {}.
#[export] Instance R1Thy     : TheorySig RarithThy R1 := {}.
#[export] Instance RplusThy  : TheorySig RarithThy Rplus := {}.
#[export] Instance RminusThy : TheorySig RarithThy Rminus := {}.
#[export] Instance RmultThy  : TheorySig RarithThy Rmult := {}.
#[export] Instance IZRThy    : TheorySig RarithThy IZR := {}.
#[export] Instance ReqThy    : TheorySig RarithThy (@eq R) := {}.
#[export] Instance RltThy    : TheorySig RarithThy Rlt := {}.
#[export] Instance RleThy    : TheorySig RarithThy Rle := {}.
#[export] Instance RgeThy    : TheorySig RarithThy Rge := {}.
#[export] Instance RgtThy    : TheorySig RarithThy Rgt := {}.

(* Integer constant are also part of theory *)
#[export] Instance Z0Thy   : TheorySig RarithThy Z0 := {}.
#[export] Instance ZposThy : TheorySig RarithThy Zpos := {}.
#[export] Instance ZnegThy : TheorySig RarithThy Zneg := {}.
#[export] Instance xHThy   : TheorySig RarithThy xH := {}.
#[export] Instance xIThy   : TheorySig RarithThy xI := {}.
#[export] Instance xOThy   : TheorySig RarithThy xO := {}.


Ltac smt := itauto (no RarithThy congruence lra).
