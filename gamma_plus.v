(* Trying to define \Gammma^+ as in Jardines "The Barratt-Priddy-Quillen Theorem" from 2009 *)
(* There it is defined as the homotopy colimit over all monomorphisms of a certain functor.*)
(* Monomorphisms can be factored into permutations and the inclusions n->n+1 not hitting the last point. *)
(* This we take advantage of to define the colimit in HoTT. The permutations come from univalence, and the rest is a normal HIT *)

Require Import HoTT.
Require Import UnivalenceAxiom.
Load stuff.
Open Scope nat.

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

(* (* This is a general statement that should perhaps go elsewhere *) *)
(* Definition equiv_transport_prod {A : Type} {P Q : A -> Type} {a1 a2 : A} (p : a1 = a2) (z1 : P a1 * Q a1) (z2%type : *)
(*   transport (fun a : A => P a * Q a)%type p z  *)


Definition path_SM {n : nat} {X : Type} (x y : Symmetric_Product n X) :
  x = y <~> {f : x.1.1 <~> y.1.1 & x.2 = y.2 o f}.
Proof.
  refine (_ oE (equiv_ap equiv_other_SP x y)).
  refine (_ oE equiv_path_sigma _ _ _).
  destruct x as [[A Hx] x]. simpl in x.
  destruct y as [[B Hy] y]. simpl in y.
  simpl.
  transitivity {p : A = B & transport (fun a : Type => a -> X) p x = y}.
  - apply equiv_functor_sigma_id. intro p.
    transitivity ((transport (fun a : Type => merely (a <~> pFin n)) p Hx = Hy)*
                    (transport (fun a : Type => a -> X) p x = y))%type.
    + refine (_ oE (equiv_concat_l (transport_prod p _) _)^-1).
      apply equiv_inverse.
      (* For some reason, [apply equiv_path_prod] doesn't work here *)
      exact (equiv_path_prod
               (transport (fun a : Type => Trunc (-1) (a <~> pFin n)) p Hx,
                transport (fun a : Type => a -> X) p x) (Hy, y)).
    + refine ((prod_unit_l _) oE _).
      refine (equiv_functor_prod' _ 1%equiv).
      apply equiv_contr_unit.
  - apply equiv_inverse.
    refine (equiv_functor_sigma'(equiv_path_universe A B) _).
    intro e. simpl.
    change (fun x0 : A => y (e x0)) with (y o e).
    transitivity (x o e^-1 = y).
    + 

      admit.                    (* should be simple *)
    + apply equiv_concat_l.
      apply transport_exp. 

(* Prove this first in a base case. *)
Example path_SM' {n : nat}  {X : Type} (x y : pFin n -> X) :
  prod_to_SP x = prod_to_SP y <~> {f : pFin n <~> pFin n & x o f = y}.
Proof.
  unfold prod_to_SP.
  transitivity {f : pFin n = pFin n & transport  x = y}. 
