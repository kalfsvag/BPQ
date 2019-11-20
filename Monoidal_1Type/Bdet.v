Require Import HoTT.

Require Import pointed_lemmas finite_lemmas monoids_and_groups delooping permutations determinants
               BSigma .

Definition iso_path_finite_types (m : nat)
  : Isomorphism (SymGrp m) (loopGroup (Finite_Types m) (canon m)).
Proof.
  srapply Build_Grp_Iso'.
  - simpl. apply (equiv_path_finite_types m (canon m) (canon m)).
  - intros alpha beta. simpl.
    apply (path_finite_types_compose m (canon m) (canon m) (canon m) alpha beta).
Defined.


Definition equiv_functor_hom_fin (m n : nat)
  : Homomorphism (SymGrp m) (SymGrp n) <~> Homomorphism (loopGroup (pFin m) (canon m))
                                                        (loopGroup (pFin n) (canon n)).
Proof.
  apply equiv_functor_hom'; apply iso_path_finite_types.
Defined.  

(* Definition equiv_deloop_fin (m n : nat) *)
(*   : Homomorphism (SymGrp m) (SymGrp n) <~> pMap (pFin m) (pFin n). *)
(* Proof. *)
(*   refine (equiv_functor_deloop' _ _ oE _). *)
(*   apply (equiv_functor_hom). *)
(*   - apply iso_inv. *)
(*     apply iso_path_finite_types. *)
(*   - apply iso_path_finite_types. *)
(* Defined. *)   

Definition deloop_fin (m n : nat)
  : Homomorphism (SymGrp m) (SymGrp n) -> Finite_Types m ->* Finite_Types n.
Proof.
(*   intro e. apply (equiv_deloop_fin m n). exact e. *)
(* Defined. *)
  
  intro f. apply (functor_deloop (pFin m) (pFin n)).
  apply (equiv_functor_hom_fin m n). exact f.
  (* apply (deloop_rec_uncurried *)
  (* srefine (deloop_rec (pFin m) (Finite_Types n) (canon n) _ _). *)
  (* - apply ((equiv_functor_hom_fin m n) f). *)
  (* - intros. *)
  (*   apply (preserve_mult *)
  (*            (functor_hom (iso_inv (iso_path_finite_types m)) (iso_path_finite_types n) f)). *)
Defined.

Definition deloop_fin_canon (m n : nat) (f : Homomorphism (SymGrp m) (SymGrp n))
  : deloop_fin m n f (canon m) = canon n.
Proof.
  apply (point_eq (deloop_fin m n f)).
Defined.

(* move *)
Definition deloop_fin_loop (m n : nat) (f : Homomorphism (SymGrp m) (SymGrp n))
           (ω : canon m = canon m)
  : (* (deloop_fin_canon m n f)^ @ ap (deloop_fin m n f) ω  @ (deloop_fin_canon m n f) *)
    loops_functor (deloop_fin m n f) ω
    = (functor_hom
         (iso_inv (iso_path_finite_types m))
         (iso_path_finite_types n) f) ω.
Proof.  
  apply functor_deloop_loop.
Defined.

Definition dethom (m : nat) : Homomorphism (SymGrp m) (SymGrp 2).
Proof.
  srapply @Build_GrpHom.
  + apply determinant.
  + apply det_compose.
Defined.

Definition BDet (m : nat) :=
  deloop_fin m 2 (dethom m).

Definition BDet_uncurry : BSigma -> Finite_Types 2.
Proof.
  intros [a A]. exact (BDet a A).
Defined.


