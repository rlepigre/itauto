(* Copyright 2023 Frédéric Besson <frederic.besson@inria.fr> *)
Require Import Bool Uint63.

Module HCons.
  (* The [HCons] module allows to tag a term with
      - a unique identifier [id]
      - a boolean stating whether the term is decidable
   *)
  Section S.
    Variable A: Type.

    Record t : Type :=
      mk {
          id : int;
          is_dec: bool;
          elt: A
        }.


    Lemma dest_eq : forall f,
        mk (id f) (is_dec f) (elt f) = f.
    Proof.
      destruct f ; reflexivity.
    Qed.

    Definition eq_hc (f1 f2 : t) := (id f1 =? id f2)%uint63 && Bool.eqb (is_dec f1) (is_dec f2).


  End S.

  Definition map [A B] (f: A -> B) (e: t A) : t B :=
    mk _ (id _ e) (is_dec _ e) (f (elt _ e)).

End HCons.
Arguments HCons.mk {A} id is_dec elt.
Arguments HCons.elt {A} .
Arguments HCons.id {A} .
Arguments HCons.is_dec {A} .
Arguments HCons.eq_hc {A}.

(* [BForm] stands for boolean formula.
   This provides the surface of formulae.
   The formulae are either interpreted over [bool] or [Prop].
 *)

Inductive op :=
| NOT | AND | OR | IMPL | IFF (i1 i2:int).

Inductive bprop := EQB (i1 i2:int).

Inductive ite := ITE (i1 i2:int).

Inductive kind : Type :=
|IsProp
|IsBool.

Inductive BForm  : kind -> Type :=
| BTT   : forall (k: kind), BForm k
| BFF   : forall (k: kind), BForm k
| BAT   : forall (k: kind), int -> BForm k
| BOP   : forall (k: kind), op -> HCons.t (BForm k) ->
                            HCons.t (BForm k) -> BForm k
| BITE  : forall (k:kind), ite -> HCons.t (BForm IsBool) -> HCons.t (BForm k) ->
                           HCons.t (BForm k) -> BForm k
| BPROP   : bprop -> HCons.t (BForm IsBool) -> HCons.t (BForm IsBool) -> BForm IsProp
.

(** [LForm] is the desuggared syntax for formulae.
      The operators take a list of formulae *)

Inductive lop := LAND | LOR.

Inductive LForm : Type :=
| LAT : int -> LForm
| LOP : lop -> list (HCons.t LForm) -> LForm
| LIMPL : list (HCons.t LForm) ->  (HCons.t LForm)  -> LForm.

Definition HFormula : Type := HCons.t LForm.

(** A [literal] is either a positive or negative formula.
    A clause is a list of literals. *)
Inductive literal : Type :=
| POS (f:HFormula)
| NEG (f:HFormula).

Definition lop_eqb (o o': lop) : bool :=
  match o , o' with
  | LAND , LAND => true
  | LOR  , LOR  => true
  | _ , _ => false
  end.

Lemma lop_eqb_true : forall o o',
    lop_eqb o o' = true -> o = o'.
Proof.
  destruct o,o' ; simpl ; intuition congruence.
Qed.

Lemma lop_eqb_refl : forall l,
    lop_eqb l l = true.
Proof.
  destruct l;reflexivity.
Qed.
