Require Import Cdcl.Itauto.
Require Import Lia.
Require Import ZArith.

Ltac tlia := time "lia" lia.

Lemma elim_eq : forall (x y: Z), x = y <-> not (x < y \/ x > y)%Z.
Proof.
  intros. lia.
Qed.

Goal forall input mapper0In mapper1In reducer0In reducer1In aggregatorIn output : nat,
 mapper0In = input \/
 mapper1In = mapper0In \/
 reducer0In = mapper1In \/
 reducer1In = reducer0In \/
 aggregatorIn = reducer1In \/
 output = aggregatorIn \/
 mapper1In = input \/
 reducer0In = mapper0In \/
 reducer1In = mapper1In \/
 aggregatorIn = reducer0In \/
 output = reducer1In \/
 reducer0In = input \/
 reducer1In = mapper0In \/
 aggregatorIn = mapper1In \/
 output = reducer0In \/
 reducer1In = input \/
 aggregatorIn = mapper0In \/
 output = mapper1In \/ aggregatorIn = input \/ output = mapper0In \/ output = input \/ 0 = 1.
Proof.
  intros.
  Zify.zify. (* zify needs to be called before. Otherwise, we get equalities over nat. *)
  Fail itauto tlia.
Abort.
