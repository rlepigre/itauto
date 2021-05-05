(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Cdcl.Itauto.
Require Import ZifyClasses Lra Reals.

Record RarithThy : Type.

Instance RThy  : TheoryType RarithThy R := {}.

Instance R0Thy     : TheorySig RarithThy R0 := {}.
Instance R1Thy     : TheorySig RarithThy R1 := {}.
Instance RplusThy  : TheorySig RarithThy Rplus := {}.
Instance RminusThy : TheorySig RarithThy Rminus := {}.
Instance RmultThy  : TheorySig RarithThy Rmult := {}.
Instance IZRThy    : TheorySig RarithThy IZR := {}.
Instance ReqThy    : TheorySig RarithThy (@eq R) := {}.
Instance RltThy    : TheorySig RarithThy Rlt := {}.
Instance RleThy    : TheorySig RarithThy Rle := {}.
Instance RgeThy    : TheorySig RarithThy Rge := {}.
Instance RgtThy    : TheorySig RarithThy Rgt := {}.

(* Integer constant are also part of theory *)
Instance Z0Thy   : TheorySig RarithThy Z0 := {}.
Instance ZposThy : TheorySig RarithThy Zpos := {}.
Instance ZnegThy : TheorySig RarithThy Zneg := {}.
Instance xHThy   : TheorySig RarithThy xH := {}.
Instance xIThy   : TheorySig RarithThy xI := {}.
Instance xOThy   : TheorySig RarithThy xO := {}.


Ltac smt := itauto (no RarithThy congruence lra).
