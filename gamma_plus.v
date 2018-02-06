(* Trying to define \Gammma^+ as in Jardines "The Barratt-Priddy-Quillen Theorem" from 2009 *)
(* There it is defined as the homotopy colimit over all monomorphisms of a certain functor.*)
(* Monomorphisms can be factored into permutations and the inclusions n->n+1 not hitting the last point. *)
(* This we take advantage of to define the colimit in HoTT. The permutations come from univalence, and the rest is a normal HIT *)

Require Import HoTT.
Require Import UnivalenceAxiom.
Load stuff.
Open Scope nat.
(* Canonical pointed finite sets as subsets of N *)
Definition pFin (n : nat) := {i : nat | i <= n}.
Global Instance ispointed_pFin {n : nat} : IsPointed (pFin n) := (0;tt).
(* General pointed finite sets of cardinality n *)
Definition Pointed_Finite (n : nat) := {A : Type & merely (A <~> pFin n)}.

(* Definition Canonical_Pointed_Finite (n : nat) : Pointed_Finite n:= *)
(*   (pFin n; tr 1%equiv). *)

(* The symmetric product (I think) *)
Definition Symmetric_Product (n : nat) (X : Type) :=
  (* {n : nat & {A : Type & {h : merely (A <~> pFin n) | (A -> X)}}}. *)
  {A : Pointed_Finite n & (A.1 -> X)}.

(* Another way of defining the symmetric product *)
(* I feel I have done this before, but I cannot find it. . . *)
Definition equiv_other_SP {n : nat} {X : Type} :
  Symmetric_Product n X <~> {A : Type & ((merely (A <~> pFin n)) * (A -> X))%type}.
Proof.
  unfold Symmetric_Product. unfold Pointed_Finite.
  srapply @equiv_adjointify.
  - intros [[A Hx] x]. exists A. exact (Hx, x).
  - intros [A [Hx x]]. exists (A; Hx). exact x.
  - unfold Sect. intros [A [Hx x]]. reflexivity.
  - unfold Sect. intros [[A Hx] x]. reflexivity.
Defined.

Definition prod_to_SP {n : nat} {X : Type} : (pFin n -> X) -> Symmetric_Product n X :=
  fun x => ((pFin n; tr 1%equiv); x).  

(* Given elements (A,x) (B,y) in the symmetric product, the identity type (A,x) = (B,y) should be the type
 {f : A<~>B & x o f = y}.*)

Definition path_SM {n : nat} {X : Type} (x y : Symmetric_Product n X) :
  x = y <~> {f : x.1.1 <~> y.1.1 & x.2 = y.2 o f}.
Proof.
  refine (_ oE (equiv_ap equiv_other_SP x y)).
  refine (_ oE equiv_path_sigma _ _ _).
  destruct x as [[A Hx] x]. simpl in x.
  destruct y as [[B Hy] y]. simpl in y.
  simpl.
  apply equiv_inverse.
  apply (equiv_functor_sigma' (equiv_path_universe A B)).
  intro f. simpl.
  transitivity ((transport (fun a : Type => (a -> X)) (path_universe_uncurried f) x) = y).
  transitivity (x o f^-1 = y).
  (*  *) -admit.
  - apply equiv_concat_l.
    apply transport_exp.
  - admit.
    
 


(* Prove this first in a base case. *)
Example path_SM' {n : nat}  {X : Type} (x y : pFin n -> X) :
  prod_to_SP x = prod_to_SP y <~> {f : pFin n <~> pFin n & x o f = y}.
Proof.
  unfold prod_to_SP.
  transitivity {f : pFin n = pFin n & transport  x = y}. 
