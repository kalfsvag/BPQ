Require Import HoTT.
Require Import type_over.
Require Import finite_lemmas.
Require Import pointed_lemmas.

Context (A : Finite_Types).
Context (X : pType).

(* Want to define the union over all (B -> X) where B are finite subtypes of A *)
(* Filter finite subtypes of A by cardinality *)

Definition finite_subtype_card (n : nat) :=
  { B : Type & (merely (B <~> Fin n)) * {f : B -> A & forall b1 b2 : B, f b1 = f b2 -> b1 = b2}}.

Definition finite_subtype_is_dprop (n : nat):
  finite_subtype_card n <~> {B : A -> DProp & fcard ({a : A & B a}) = n}.
Proof.
  srapply @equiv_adjointify.
  intros [B [e [f inj_f]]].
