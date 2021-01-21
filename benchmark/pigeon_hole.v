(* Encoding of Pigeon Hole Principle *)
Require Import List.

Axiom Pigeon_In_Hole : nat -> nat -> Prop.

Definition cons_option {A: Type} (e: option A) (l: list A) :=
  match e with
  | None => l
  | Some v => v:: l
  end.

Fixpoint map_n (F: nat -> option Prop) (n: nat) :=
  cons_option (F n)
              (match n with
               | O => nil
               | S n' => map_n F n'
               end).

Fixpoint or_list (l: list Prop) :=
  match l with
  | nil => False
  | e::nil => e
  | e::l   => e  \/ or_list l
  end.

Fixpoint and_list (l: list Prop) :=
  match l with
  | nil => True
  | e::nil => e
  | e::l   => e /\ and_list l
  end.

Definition big_or (n:nat) (F: nat -> option Prop)  :=
  or_list (map_n F n).

Definition big_and (n:nat) (F: nat -> option Prop)  :=
  and_list (map_n F n).

Fixpoint pigeon_in_hole (b:nat) (n:nat) : Prop :=
  (big_or n (fun n => Some (Pigeon_In_Hole b n)) /\
   match b with
   | O => True
   | S b' => pigeon_in_hole b' n
   end).

Fixpoint forall_2 (P : nat -> nat -> option Prop) (i:nat) (j:nat) :=
  big_and j (P i) /\ match i with
                     | O => True
                     | S i' => forall_2 P i' j
                     end.

Definition at_most_one_pigeon_per_hole (dis:bool) (b:nat) (k:nat) :=
  let F i j := if dis then (not (Pigeon_In_Hole i k) \/ not (Pigeon_In_Hole j k))
               else (Pigeon_In_Hole i k -> Pigeon_In_Hole j k -> False)
                 in
  Some (forall_2 (fun i j => if Nat.ltb i j then  Some (F i j) else None) b b).

Definition at_most_one_pigeon (dis: bool) (b:nat) (n:nat)  :=
  big_and n (at_most_one_pigeon_per_hole dis b).

Definition pigeon_hole (dis: bool) (b:nat) (n:nat) :=
  pigeon_in_hole b n /\ at_most_one_pigeon dis b n.

Ltac simpl_pigeon :=
  unfold pigeon_hole; cbn; unfold not.
