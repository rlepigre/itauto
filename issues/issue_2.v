Require Import ZArith List.
Require Import Cdcl.Itauto.

Fixpoint compile(program: nat): list Z :=
  match program with
  | S n => Z.of_nat n :: compile n
  | O => nil
  end.

Axiom F: list Z -> list Z.

Goal F (compile 1000) = compile 1000 -> 0 = 0.
Proof. intros. Time itauto reflexivity. Qed.   (* 0.206 secs *)
Goal F (compile 2000) = compile 2000 -> 0 = 0.
Proof. intros. Time itauto reflexivity. Qed.   (* 0.754 secs *)
Goal F (compile 3000) = compile 3000 -> 0 = 0.
Proof. intros. Time itauto reflexivity. Qed.   (* 1.678 secs *)
Goal F (compile 4000) = compile 4000 -> 0 = 0.
Proof. intros. Time itauto reflexivity. Qed.   (* 2.987 secs *)

Require Import Cdcl.Formula.
Require Import Int63.

Require Import Classical.

Lemma id :  F (compile 2000) = compile 2000 -> F (compile 2000) = compile 2000.
Proof.
       set (y := mkAtomDec (F (compile 2000) = compile 2000) (classic (F (compile 2000) = compile 2000))).
       set (map := (set atomT 2 (mkAtom (F (compile 2000) = compile 2000)) (empty atomT))).
       set (f := {|
    HCons.id := 3;
    HCons.is_dec := false;
    HCons.elt := BForm.BOP IsProp IMPL
                   {| HCons.id := 2; HCons.is_dec := false; HCons.elt := BForm.BAT IsProp 2 |}
                   {| HCons.id := 2; HCons.is_dec := false; HCons.elt := BForm.BAT IsProp 2 |} |}).
     set (map' := set atomT 3 y map).
    change (BForm.eval_hbformula (eval_prop map') f).
    apply (hcons_bprover_correct 100%nat).
    unfold map'.
    unfold y.
    generalize ((F (compile 2000) = compile 2000)).
    vm_compute.
    set (map := (set atomT 2%int63 (mkAtom (F (compile 2000) = compile 2000)) (empty atomT))).
       vm_compute. reflexivity.
       simpl
       Time itauto idtac. Qed.   (* 2.987 secs *)

Print id.



Axiom opaque_compile: nat -> list Z.

Goal F (opaque_compile 1000) = opaque_compile 1000 -> 0 = 0.
Proof. intros. Time itauto reflexivity. Qed.   (* 0.016 secs *)
Goal F (opaque_compile 2000) = opaque_compile 2000 -> 0 = 0.
Proof. intros. Time itauto reflexivity. Qed.   (* 0.029 secs *)
Goal F (opaque_compile 3000) = opaque_compile 3000 -> 0 = 0.
Proof. intros. Time itauto reflexivity. Qed.   (* 0.042 secs *)
Goal F (opaque_compile 4000) = opaque_compile 4000 -> 0 = 0.
