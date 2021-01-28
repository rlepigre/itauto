(* Copyright 2020 Frédéric Besson <frederic.besson@inria.fr> *)

Require Extraction.
Require Import Int63.

Extract Constant int => "Uint63.t".
Extract Constant Int63.ltb => "Uint63.lt".
Extract Constant Int63.eqb => "Uint63.equal".
Extract Constant Int63.add => "Uint63.add".
Extract Constant Int63.lsl => "Uint63.l_sl".
Extract Constant Int63.lsr => "Uint63.l_sr".
Extract Constant Int63.land => "Uint63.l_and".
Extract Constant Int63.lor => "Uint63.l_or".
Extract Constant Int63.lxor => "Uint63.l_xor".
Extract Constant Int63.sub => "Uint63.sub".
Extract Inductive bool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive list => list [ "[]" "(::)" ].

Require Import Cdcl.Formula.

(* This extracts at the right place only if Pwd is itauto top-level
directory *)
Extraction "src/prover.ml" hcons_bprover LitSet.is_empty LitSet.fold LitSet.mem.
