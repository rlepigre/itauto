Require Import Lia ZArith List.
Require Import Cdcl.Itauto.
Open Scope Z_scope.

Unset Lia Cache.
Set Itauto Theory Time.


Goal forall Y r0 r q q0 r1 q1 : Z,
  131072 <= r0 < 139264 \/
  268468224 <= r0 < 268500992 \/
  268509184 <= r0 < 268513280 \/
  268513280 <= r0 < 268517376 \/ 268582912 <= r0 < 268587008 ->
  ~
  (131072 <= Y < 139264 \/
   268468224 <= Y < 268500992 \/
   268509184 <= Y < 268513280 \/
   268513280 <= Y < 268517376 \/ 268582912 <= Y < 268587008) ->
  r = 0 ->
  0 <= Y < 4294967296 ->
  (4 <> 0 -> r0 = 4 * q + r) ->
  (4294967296 = 0 -> q0 = 0 /\ r0 = 0 /\ q1 = 0 /\ r1 = 0) ->
  (4 < 0 -> 4 < r <= 0 /\ 4294967296 < r0 <= 0 /\ 4294967296 < r1 <= 0) ->
  (0 < 4 -> 0 <= r < 4 /\ 0 <= r0 < 4294967296 /\ 0 <= r1 < 4294967296) ->
  (4294967296 <> 0 -> Y - r1 = 4294967296 * q0 + r0 /\ 3 = 4294967296 * q1 + r1) ->
  (4 = 0 -> q = 0 /\ r = 0) -> False.
Proof.
  intros.
  Time itauto lia. (* still slow, down to 38s - but a lia subcall takes 17 secs *)
Qed.
