Require Import HoTT.

From GC Require Import BSigma.
From GC Require Import group_complete_1type.
Require Import delooping.
Require Import monoids_and_groups (* B_Aut *) permutations.

Definition iso_loop_symgrp (m : nat) :
  Isomorphism  (SymGrp m)
                 (loopGroup
                    (Build_pType
                       (Finite_Types m) _)).
  Proof.
    srapply @Build_Grp_Iso'.
    - simpl. unfold point. unfold ispointed_finite_types.
      apply (equiv_path_finite_types m (canon m) (canon m)).
    - intros e1 e2. simpl in e1, e2.
      apply (path_finite_types_compose m (canon m) (canon m) (canon m) e1 e2).
  Defined.
Section loop_BSigma.

  Definition loop_BSigma (m n : nat) :
    pMap (pFin m) (pFin n)
    -> Homomorphism (SymGrp m) (SymGrp n)
    := Compose (functor_hom
                  (iso_loop_symgrp m) (iso_inv (iso_loop_symgrp n)))
               (functor_loop (pFin m) (pFin n)).

  Global Instance isequiv_loop_BSigma (m n : nat) : IsEquiv (loop_BSigma m n) :=
    @isequiv_compose _ _
                     (functor_loop (pFin m) (pFin n))
                     (isequiv_functor_loop _ _)
                     _
                     (functor_hom (iso_loop_symgrp m) (iso_inv (iso_loop_symgrp n)))
                     (isequiv_functor_hom _ _).

  Definition equiv_loop_BSigma (m n : nat)
    : pMap (pFin m) (pFin n) <~>
           Homomorphism (SymGrp m) (SymGrp n).
  Proof.
    refine (_ oE equiv_functor_loop _ _).
    apply equiv_functor_hom.
    - apply iso_loop_symgrp.
    - apply iso_inv. apply iso_loop_symgrp.
  Defined.
  
  (* Definition equiv_loop_BSigma (m n : nat) := *)
  (*   BuildEquiv _ _ (loop_BSigma m n) (isequiv_loop_BSigma m n). *)

  Definition loop_BSigma_prod (l m n : nat) :
    pMap (conn_ptype_prod (pFin l) (pFin m)) (pFin n) ->
    Homomorphism (grp_prod (SymGrp l) (SymGrp m)) (SymGrp n).
  Proof.
    srefine (compose _ (functor_loop
                          (conn_ptype_prod (pFin l) (pFin m))
                          (pFin n))).
    (* srefine (_ o (functor_loop *)
    (*                 (conn_ptype_prod (pFin l) (pFin m)) *)
    (*                 (pFin n))). *)
    - apply functor_hom.
      + refine (iso_compose 
                (iso_inv (iso_prod_loopGroup
                   (pFin l)
                   (pFin m))) _).
        apply iso_prod_hom; apply iso_loop_symgrp.
      + apply iso_inv. apply iso_loop_symgrp.
  Defined.

  Global Instance isequiv_loop_BSigma_prod (l m n : nat) :
    IsEquiv (loop_BSigma_prod l m n)
    := @isequiv_compose
         (pMap (conn_ptype_prod (pFin l) (pFin m)) (pFin n)) _
         (functor_loop  _ _) (isequiv_functor_loop _ _ )
         _
         (functor_hom _ _) (isequiv_functor_hom _ _).

  Definition equiv_loop_BSigma_prod (l m n : nat)
    : pMap (conn_ptype_prod (pFin l) (pFin m)) (pFin n) <~>
           Homomorphism (grp_prod (SymGrp l) (SymGrp m)) (SymGrp n).
  Proof.
    refine (_ oE equiv_functor_loop _ _).
    apply equiv_functor_hom.
    - refine (iso_compose 
                (iso_inv (iso_prod_loopGroup
                   (pFin l)
                   (pFin m))) _).
      apply iso_prod_hom; apply iso_loop_symgrp.
    - apply iso_inv. apply iso_loop_symgrp.
  Defined.

  (* Definition equiv_loop_BSigma_prod (l m n : nat) := *)
  (*   BuildEquiv _ _ (loop_BSigma_prod l m n) (isequiv_loop_BSigma_prod l m n). *)
  
  
  Definition loop_BSigma_1 (m : nat) :
    (loop_BSigma m m (pmap_idmap _)) = idhom.
  Proof.
    unfold loop_BSigma.
    unfold Compose.
    transitivity
      (functor_hom (iso_loop_symgrp m) (iso_inv (iso_loop_symgrp m)) idhom).
    - apply (ap (functor_hom (iso_loop_symgrp m) (iso_inv (iso_loop_symgrp m)))).
      apply path_hom. apply path_arrow. apply (functor_loop_id (pFin m)).
    - apply path_hom. apply path_arrow. intro x.
      refine (functor_hom_id _ _ (iso_inv (iso_loop_symgrp m)) x ).
  Qed.

  Open Scope monoid_scope.
  Definition loop_BSigma_compose (l m n : nat)
             (f : pMap (pFin l) (pFin m))
             (g : pMap (pFin m) (pFin n))
    : loop_BSigma l n (pmap_compose g f) = (loop_BSigma m n g) oH (loop_BSigma l m f).
  Proof.    
    unfold loop_BSigma. 
    refine (ap (functor_hom (iso_loop_symgrp l) (iso_inv (iso_loop_symgrp n)))
               (path_hom _ _
                         (path_arrow _ _
                               (functor_loop_compose
                                  (pFin l)
                                  (pFin m)
                                  (pFin n) _ _)))^ @ _).
    apply functor_hom_compose_001.
  Defined.

    Definition loop_BSigma_prod_compose (k l m n : nat)
             (f : pMap (conn_ptype_prod (pFin k) (pFin l)) (pFin m))
             (g : pMap (pFin m) (pFin n))
    : loop_BSigma_prod k l n (pmap_compose g f)
      = (loop_BSigma m n g) oH (loop_BSigma_prod k l m f).
  Proof.
    unfold loop_BSigma_prod. unfold loop_BSigma.
    unfold functor_hom.
    refine (_ @ homcompose_f_ff _ _ _).
    refine (_ @ homcompose_f_ff _ _ _).
    refine ((homcompose_f_ff _ _ _)^ @ _).
    apply (ap (fun f => iso_inv (iso_loop_symgrp n) oH f)).
    refine ((homcompose_f_ff _ _ _) @ _).
    refine (_ @ (homcompose_f_ff _ _ _)^).
    refine (_ @ (homcompose_f_ff _ _ _)^).
    refine (_ @ (homcompose_f_ff _ _ _)^).
    apply (ap (fun f => f oH iso_prod_hom (iso_loop_symgrp k) (iso_loop_symgrp l))).
    apply (ap (fun f => f oH iso_inv (iso_prod_loopGroup (pFin k) (pFin l)))).
    refine ((path_hom _ _
              (path_arrow
                 _ _
                 (functor_loop_compose _ _ _ f g)))^ @ _).
    refine (_ @ homcompose_f_ff _ _ _).
    refine (_ @ (ap (fun h => functor_loop (pFin m) (pFin n) g oH h)
                    (homcompose_f_ff _ _ _)^)).
    apply (ap (fun h => functor_loop (pFin m) (pFin n) g oH h)).
    refine (_ @ ap (fun h => h oH functor_loop (conn_ptype_prod (pFin k) (pFin l)) (pFin m) f)
              (isoisretr (iso_loop_symgrp m))^).
    apply path_hom. reflexivity.
  Qed.
  
  Definition BSigma_sum_uncurried (m n : nat) :
    pMap (Build_pType ((Finite_Types m)*(Finite_Types n)) (point _, point _))
         (Build_pType (Finite_Types (n+m)) _).
  Proof.
    srapply @Build_pMap.
    - intros [A B]. apply (sum_finite_types A B).
    - simpl.  unfold point. unfold ispointed_finite_types.
      apply path_finite_types.
      apply equiv_finsum.
  Defined.

    Definition loop_BSigma_sum (m n : nat)
    : loop_BSigma_prod m n (n+m) (BSigma_sum_uncurried m n) = block_sum_hom m n.
  Proof.
    
    unfold loop_BSigma_prod. unfold functor_hom.
    (* unfold block_sum_hom. unfold block_sum. *)
    
    apply path_hom. 
    apply path_arrow. intro x.
    apply moveR_equiv_V. simpl. unfold point. unfold ispointed_finite_types.
    destruct x as [s t]. simpl.
    unfold block_sum.
    apply moveR_Vp.
    refine (_ @ path_finite_types_compose _ _ _ _ _ _).
    apply moveR_pM.
    refine (_ @ (ap (fun p => _ @ p)
                    (path_finite_types_V
                       (sum_finite_types (canon m) (canon n)) (canon (n + m))
                       (equiv_finsum m n)))).
    refine (_ @ path_finite_types_compose _ _ _ _ _ _).
    transitivity
      (path_finite_types
         (n + m)
         (sum_finite_types (canon m) (canon n))
         (sum_finite_types (canon m) (canon n))
         (s +E t)).
    - refine (_ @
                (ap011 (fun g h =>
                          path_finite_types
                            (n + m)
                            (sum_finite_types (canon m) (canon n))
                            (sum_finite_types (canon m) (canon n))
                            (g +E h))
                       (eissect (equiv_path_finite_types m (canon m) (canon m)) s)
                       (eissect (equiv_path_finite_types n (canon n) (canon n)) t))).
      change ((equiv_path_finite_types ?m (canon ?m) (canon ?m)) ?s) with
      ((path_finite_types m (canon m) (canon m)) s).
      generalize ((path_finite_types m (canon m) (canon m)) s). clear s. intro s.
      generalize ((path_finite_types n (canon n) (canon n)) t). clear t. intro t.
      revert s t.
      cut (forall (A : Finite_Types m) (B: Finite_Types n)
                  (s : canon m = A) (t : canon n = B),
              ap (fun X : Finite_Types m * Finite_Types n => sum_finite_types (fst X) (snd X))
                 (path_prod (canon m, canon n) (A, B) s t) =
              path_finite_types (n + m) (sum_finite_types (canon m) (canon n))
                                    (sum_finite_types A B)
                                    ((equiv_path_finite_types m (canon m) A)^-1 s
                                     +E (equiv_path_finite_types n (canon n) B)^-1 t)).
      { intro H. apply H. }
      intros A B [] []. simpl. 
      apply inverse.
      refine (_ @ path_finite_types_id _ _).
      apply (ap (path_finite_types _ _ _)).
      apply path_equiv. apply path_arrow. intros [x | x]; reflexivity.                       
                       
    - apply (ap (path_finite_types _ _ _ )).
      apply path_equiv. apply path_arrow. intro x.
      apply inverse. ev_equiv.
      refine (eissect (equiv_finsum m n) ((s +E t) ((equiv_finsum m n)^-1 ((equiv_finsum m n) x))) @ _).
      apply (ap (s +E t)).
      apply eissect.
  Defined.

  Require Import determinants.

Definition det_hom (m : nat) : Homomorphism (SymGrp m) (SymGrp 2).
Proof.
  srapply @Build_GrpHom.
    - exact (determinant m).
    - apply det_compose.
Defined.

Definition block_sum_id_hom (m n : nat) :
  Homomorphism (SymGrp n) (SymGrp (n+m)).
Proof.
  srapply @Build_GrpHom.
  - apply (block_sum equiv_idmap).
  - simpl. intros. apply path_equiv. apply path_arrow. intro x.
    refine (_ @ block_sum_compose _ _ _ _ x).
    rewrite ecompose_e1. reflexivity.
Defined.

Definition BDet (m : nat) := (loop_BSigma m 2)^-1 (det_hom m).

(*   pMap (Build_pType (Finite_Types m) _) (Build_pType (Finite_Types 2) _) . *)
(* Proof. *)
(*   apply pMap_BSigma. apply (det_hom m). *)
(*   srapply @Build_GrpHom. *)
(*   - exact (determinant m). *)
(*   - apply det_compose. *)
(* Defined. *)

Definition deloop_mult_uncurried
  : pMap
      (Build_pType (Finite_Types 2 * Finite_Types 2) (point _, point _))
      (Build_pType (Finite_Types 2) _).
Proof.
  apply (loop_BSigma_prod 2 2 2)^-1.
  apply mult_hom.
  intros x y. apply symm_sigma2.
Defined.

(* move up *)
Definition compose_loop_BSigma_functor_prod {j k l m n}
           (f1 : pMap (Build_pType (Finite_Types j) _) (Build_pType (Finite_Types l) _))
           (f2 : pMap (Build_pType (Finite_Types k) _) (Build_pType (Finite_Types m) _))
           (g : pMap
                  (Build_pType (Finite_Types l * Finite_Types m) (point _, point _))
                  (Build_pType (Finite_Types n)  _))
  : loop_BSigma_prod j k n (pmap_compose g (pointed_functor_prod f1 f2))
    = (loop_BSigma_prod l m n g) oH (mon_prod_hom (loop_BSigma j l f1) (loop_BSigma k m f2)).
Proof.
  (* apply path_hom. apply path_arrow. intros [s t]. *)
  unfold loop_BSigma_prod. unfold loop_BSigma. unfold Compose.
  refine
    (_ @ ap (fun f => _ oH f)
       (functor_mon_prod _ _ _ _ _ _)^).
  unfold functor_hom.
  repeat rewrite <- homcompose_f_ff.
  apply (ap (fun f => (iso_inv (iso_loop_symgrp n)) oH f)).
  rewrite <- (path_hom _ _ (path_arrow
                              _ _
                              (functor_loop_compose
                                 (conn_ptype_prod (pFin j) (pFin k))
                                 (conn_ptype_prod (pFin l) (pFin m))
                                 (pFin n)
                                 (pointed_functor_prod f1 f2) g))).
  rewrite <- homcompose_f_ff.
  apply (ap (fun f => (functor_loop (conn_ptype_prod (pFin l) (pFin m)) (pFin n) g) oH f)).
  change (?f oH (iso_compose ?g ?h)) with
  (f oH (g oH h)).
  change (?f oH (iso_prod_hom ?g ?h)) with (f oH (mon_prod_hom g h)).
  repeat rewrite homcompose_f_ff.
  change (?f oH (iso_prod_hom ?g ?h)) with (f oH (mon_prod_hom g h)).
  apply (ap (fun f => f oH mon_prod_hom (iso_loop_symgrp j) (iso_loop_symgrp k))).
  transitivity
    (iso_inv (iso_prod_loopGroup (pFin l) (pFin m)) oH idhom
             oH
             (mon_prod_hom (functor_loop (pFin j) (pFin l) f1) (functor_loop (pFin k) (pFin m) f2))).
  { apply path_hom. apply path_arrow. simpl.  intros [s t].
    pointed_reduce. unfold ispointed_finite_types in *.
    destruct s. destruct t. simpl.
    reflexivity. }
  apply (ap (fun f => f
                        oH mon_prod_hom
                        (functor_loop (pFin j) (pFin l) f1) (functor_loop (pFin k) (pFin m) f2))).
  rewrite <- homcompose_f_ff.
  apply (ap (fun f => (iso_inv (iso_prod_loopGroup (pFin l) (pFin m))) oH f)).
  apply inverse.
  refine (_ @ mon_prod_hom_id _ _).
  refine ((mon_prod_hom_compose _ _ _ _)^ @ _).
  apply (ap011 mon_prod_hom); apply isoisretr.
Qed.
  



Definition loop_BDet_sum (m n : nat) :
  pmap_compose (BDet (n+m)) (BSigma_sum_uncurried m n) =
  pmap_compose deloop_mult_uncurried (pointed_functor_prod (BDet m) (BDet n)).
Proof.
  apply (equiv_inj (equiv_loop_BSigma_prod _ _ _)).
  refine (loop_BSigma_prod_compose _ _ _ _ _ _ @ _).
  rewrite (eisretr (loop_BSigma (n+m) 2)).
  rewrite loop_BSigma_sum.
  refine (_ @ (compose_loop_BSigma_functor_prod _ _ _)^).
  rewrite (eisretr (loop_BSigma m 2)).
  rewrite (eisretr (loop_BSigma n 2)).
  rewrite (eisretr (loop_BSigma_prod 2 2 2)).
  apply path_hom. apply path_arrow. intros [s t]. simpl.
  apply det_block_sum.
Qed.     

Definition add_canon_is_block_sum_id (m n : nat) :
  loop_BSigma n (n+m) (add_canon m n) = (block_sum_id_hom m n).
Proof.
  (* unfold add_canon. *)
  (* refine (loop_BSigma_prod_compose n _ (n+m) _ (BSigma_sum_uncurried m n) @ _). *)
  
  unfold loop_BSigma. unfold Compose. unfold functor_hom.
  apply path_hom.
  apply path_arrow. intro s.
  unfold block_sum_id_hom.
  change (Build_GrpHom ?f _ ?x) with (f x). unfold block_sum.
  change ((?f oH ?g oH ?h) s) with (f (g (h s))).
  apply moveR_equiv_V.
  change ((iso_loop_symgrp ?n) ?x) with (path_finite_types n (canon n) (canon n) x).
  change ((functor_loop _ _ ?f) ?p) with ((point_eq f)^ @ (ap f p @ point_eq f)).
  refine (_ @ (path_finite_types_compose (n+m) (canon (n+m))
                                             (sum_finite_types (canon m) (canon n))
                                             (canon (n+m))
                                             _
                                             (equiv_finsum m n oE (equiv_idmap +E s)))^).
  apply concat2.
  { simpl.  unfold point. unfold ispointed_finite_types.
    apply inverse.
    apply path_finite_types_V. }
  refine (_ @ (path_finite_types_compose (n+m)
                                           (sum_finite_types (canon m) (canon n))
                                           (sum_finite_types (canon m) (canon n))
                                           (canon (n+m))
                                           (equiv_idmap +E s)
                                           (equiv_finsum m n))^).
  apply whiskerR.
  refine (_ @
            ap (fun e => _ (equiv_idmap +E e))
            (eissect (equiv_path_finite_types n (canon n) (canon n)) s)).
  change (equiv_path_finite_types n (canon n) (canon n) s) with
  (path_finite_types n (canon n) (canon n) s).
  generalize (path_finite_types n (canon n) (canon n) s). clear s. intro s.
  revert s.
  cut (forall (A : Finite_Types n) (s : canon n = A),
          ap (add_canon m n) s =
          path_finite_types (n + m)
                                (sum_finite_types (canon m) (canon n))
                                (sum_finite_types (canon m) A)
                                (equiv_idmap +E (equiv_path_finite_types _ _ _)^-1 s)).
  { intro H. apply H. }
  intros A []. simpl.
  apply inverse.
  refine (_ @ path_finite_types_id _ _).
  apply (ap (path_finite_types _ _ _)).
  apply path_equiv. apply path_arrow.
  intros [x | x]; reflexivity.
Defined.

Definition isretr_BDet (m : nat) :
    pmap_compose (BDet (2 + m)) (add_canon m 2) = pmap_idmap _.
Proof.
  apply (equiv_inj (loop_BSigma 2 2)).
  refine (loop_BSigma_compose _ _ _ _ _ @ _).
  transitivity (det_hom (2 + m) oH (block_sum_id_hom m 2)).
  { apply (ap011 compose_hom).
    { apply (eisretr (equiv_loop_BSigma m.+2 2)). }
    { apply add_canon_is_block_sum_id. }
  }
  refine (_ @ (loop_BSigma_1 _)^).
  apply path_hom. apply path_arrow. intro s.
  refine (@det_block_sum m 2 _ _ @ _).
  refine (ap (fun f => _ oE f) (det_id m) @ _).
  refine (ecompose_e1 _ @ _).
  apply (det2_is_id s).
Defined.


End loop_BSigma.