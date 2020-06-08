Require Import Cdcl.Formula.
Require Import Int63.
Extract Constant int => "Uint63.t".
Extract Constant Int63.ltb => "Uint63.lt".
Extract Constant Int63.eqb => "Uint63.equal".
Extract Inductive bool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive list => list [ "[]" "(::)" ].

Extraction "../src/prover.ml" hcons_prover.
