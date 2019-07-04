Require Import HoTT.
Require Import pointed_lemmas finite_lemmas.

Require Import group_complete_1type. (* not necessary? *)
Require Import trunc_lemmas.

(*Defining the monoidal 1-type of finite sets and isomorphisms*)
Section BSigma.
    
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Definition BSigma :=
    {m : nat & Finite_Types m}.
    (* { S : Type & Finite S}. *)
  Definition type_of_fin : BSigma -> Type := (fun A => A.2.1).
  Coercion type_of_fin : BSigma  >-> Sortclass.

  Global Instance istrunc_BSigma : IsTrunc 1 BSigma.
  Proof.
    apply (trunc_equiv' {S : Type & Finite S}).
    - apply equiv_inverse. apply fin_decompose.
    - apply trunc_sigma'.
      +  intro A. exact _.
      +  intros A B.
         srapply @istrunc_paths_Type. 
         apply isset_Finite. exact B.2.
  Defined.

  (*Canonical objects in BSigma*)
  Definition canon_BSigma (n : nat) : BSigma := (n; canon n).

  Lemma finite_types_eqcard {m n : nat} (A : Finite_Types m) (B : Finite_Types n) :
    A <~> B -> m = n.
  Proof.
    destruct A as [A fA]. destruct B as [B fB]. simpl. intro e.
    strip_truncations.
    apply nat_eq_fin_equiv.
    exact (fB oE e oE (equiv_inverse fA)).
  Qed.

  (* in finite_lemmas: *)
  (* (* Describing the path type of BSigma *) *)
  Definition path_BSigma {A B : BSigma} : A <~> B -> A = B
       := equiv_path_BSigma A B.
  (* Proof. *)
  (*   destruct A as [m A]. destruct B as [n B]. simpl. *)
  (*   intro e. *)
  (*   destruct (finite_types_eqcard A B e). *)
  (*   apply (path_sigma (fun m : nat => Finite_Types m) (m; A) (m;B) idpath). simpl. *)
  (*   apply path_finite_types_fix. *)
  (*   exact e. *)
  (* Defined. *)
    
 

  (* Definition isequiv_path_BSigma {A B : BSigma} : IsEquiv (@path_BSigma A B). *)
  (* Proof. *)
  (*   srapply @isequiv_adjointify. *)
  (*   - intros []. exact equiv_idmap. *)
  (*   - intros []. *)
  (*     unfold path_BSigma. *)
  (*     assert (H : (finite_types_eqcard (pr2 A) (pr2 A) equiv_idmap) = idpath). *)
  (*     { apply hset_nat. } destruct H. *)
  (*     destruct . *)


  (* shorter proof than in finite_lemmas *)

  Definition path_BSigma_1 (A : BSigma) :
    path_BSigma (equiv_idmap A) = idpath.
  Proof.
    refine (ap (path_BSigma) (eissect (@path_BSigma A A) equiv_idmap)^ @ _).
    apply moveR_equiv_M.
    refine (eissect _ _ @ _). simpl.
    reflexivity.
  Defined.

  (* (* path_BSigma respects composition *) *)  
  Definition path_BSigma_compose {A B C : BSigma} (e1 : A <~> B) (e2 : B <~> C) :
    path_BSigma (e2 oE e1) = path_BSigma e1 @ path_BSigma e2.
  Proof.
    (* path_BSigma e2 @ path_BSigma e1 = path_BSigma (e1 oE e2). *)
  Proof.
    refine
      (ap011 (fun g1 g2 => path_BSigma (g2 oE g1))
             (eissect (@path_BSigma A B) e1)^ (eissect (@path_BSigma B C) e2)^ @ _).
    generalize (path_BSigma e2). intros []. 
    generalize (path_BSigma e1). intros []. simpl.
    refine (path_BSigma_1 A).
  Qed.
    

  (* Move to finite_types.v when created *)
  Definition sum_finite_types {m n : nat} (A : Finite_Types m) (B : Finite_Types n) :
    Finite_Types (n + m).
  Proof.
    exists (A + B).
    destruct A as [A fA]. destruct B as [B fB]. strip_truncations.
    apply tr. simpl.
    refine (_ oE equiv_functor_sum' fA fB).
    apply fin_resp_sum.
  Defined.
    
  
  Definition plus_BSigma : BSigma -> BSigma -> BSigma.
  Proof.
    intros [m A] [n B].
    exists (n + m)%nat.
    exact (sum_finite_types A B).
  Defined.

  Definition BSigma_id : BSigma := canon_BSigma 0.

  Local Notation "S1 ⊕ S2" := (plus_BSigma S1 S2) (at level 50, no associativity).  

  (* path_BSigma behaves well with respect to sum *)
  Definition natural_path_BSigma_l {S1 S2 S3: BSigma} (e : S1 <~> S2)
    : ap (fun x : BSigma => x ⊕ S3) (path_BSigma e)
    = path_BSigma (A := S1 ⊕ S3) (B := S2 ⊕ S3) (equiv_functor_sum_r (B := S3) e).
  Proof.    
    refine (_ @ ap (fun e' => @path_BSigma (S1⊕ S3) (S2 ⊕ S3) (equiv_functor_sum_r e'))
              (eissect (@path_BSigma S1 S2) e)).
    generalize (path_BSigma e). intros [].
    simpl. apply inverse.
    refine (_ @ path_BSigma_1 (S1 ⊕ S3)).
    apply (ap (path_BSigma )).
    apply path_equiv. apply path_arrow. intros [s1 | s3]; reflexivity.
  Qed.

  Definition natural_path_BSigma_r {S1 S2 S3: BSigma} (e : S2 <~> S3)
    : ap (fun x : BSigma => S1 ⊕ x) (path_BSigma e)
      = path_BSigma (A := S1 ⊕ S2) (B := S1 ⊕ S3) (equiv_functor_sum_l (A := S1) e).
  Proof.
    refine (_ @ ap (fun e' => @path_BSigma (S1 ⊕ S2) (S1 ⊕ S3) (equiv_functor_sum_l e'))
              (eissect (@path_BSigma S2 S3) e)).
    generalize (path_BSigma e). intros [].
    simpl. apply inverse.
    refine (_ @ path_BSigma_1 (S1 ⊕ S2)).
    apply (ap (path_BSigma)).
    apply path_equiv. apply path_arrow. intros [s1 | s2]; reflexivity.
  Qed.
  
  (*The monoidal structure on BSigma*)
  
  Definition BSigma_assoc : associative plus_BSigma.
  Proof.
    intros S1 S2 S3.
    apply path_BSigma.
    apply equiv_sum_assoc. 
  Defined.

  Definition BSigma_lid : left_identity_mult plus_BSigma (canon_BSigma 0).
  Proof.
    intro S. apply path_BSigma.
    apply sum_empty_l.
  Defined.
  
  Definition BSigma_rid : right_identity_mult plus_BSigma (canon_BSigma 0).
  Proof.
    intro S. apply path_BSigma.
    apply sum_empty_r.
  Defined.

  Definition BSigma_symmetric : symmetric plus_BSigma. 
  Proof.
    intros S1 S2. apply path_BSigma. apply equiv_sum_symm.
  Defined.  
  
  Definition BSigma_triangle1 : coherence_triangle1 BSigma_assoc BSigma_lid.
  Proof.
    intros S1 S2.
    unfold BSigma_lid.
    refine (natural_path_BSigma_l _ @ _).
    unfold BSigma_assoc.
    refine (_ @ (path_BSigma_compose _ _)).
    apply (ap path_BSigma).
    apply path_equiv. apply path_arrow.
    intros [[[] | s1] | s2]; reflexivity.
  Qed.

  Definition BSigma_triangle2 : coherence_triangle2 BSigma_assoc BSigma_lid BSigma_rid.
  Proof.
    intros S1 S2. unfold BSigma_rid. unfold BSigma_assoc. unfold BSigma_lid. simpl.
    refine (natural_path_BSigma_l _ @ _).
    refine (_ @ whiskerL _ (natural_path_BSigma_r _)^).
    refine (_ @ (path_BSigma_compose  _ _)).
    apply (ap path_BSigma).
    apply path_equiv. apply path_arrow.
    intros [[s1 | []] | s2]; reflexivity.
  Qed.
  
  Definition BSigma_pentagon : coherence_pentagon BSigma_assoc.
  Proof.
    intros S1 S2 S3 S4.
    refine (natural_path_BSigma_l _  @ _).
    apply moveL_pV.
    refine ((path_BSigma_compose _ _)^ @ _).
    apply moveL_pV.
    refine (whiskerL _ (natural_path_BSigma_r _) @ _).
    refine ((path_BSigma_compose _ _)^ @ _).
    refine (_ @ (path_BSigma_compose _ _)).
    apply (ap path_BSigma).
    apply path_equiv. apply path_arrow.
    intros [[[s1 | s2]| s3] | s4]; reflexivity.
  Defined.

  (* The next two lemmas should be moved *)
  Definition isinj_functor_sum {A1 A2 B1 B2 : Type} (f1 f1' : A1 -> B1) (f2 f2': A2 -> B2) :
    functor_sum f1 f2 = functor_sum f1' f2' -> (f1 = f1') * (f2 = f2').
  Proof.
    intro p.
    set (p' := ap10 p).
    apply pair.
    - apply path_arrow. intro a.
      apply (path_sum_inl B2). exact (p' (inl a)).
    - apply path_arrow. intro a.
      apply (path_sum_inr B1). exact (p' (inr a)).
  Defined.

  Definition isinj_equiv_functor_sum_r {A1 A2 B : Type} (e1 e2 : A1 <~> A2) :
    equiv_functor_sum_r (B := B) e1 = equiv_functor_sum_r e2 -> e1 = e2.
  Proof.
    intro p. apply path_equiv.
    refine (fst ((isinj_functor_sum e1 e2 idmap idmap) _)).
    apply (path_equiv^-1 p).
  Defined.    
  
  Definition BSigma_lcancel (S1 S2 : BSigma) (p q : S1 = S2) (T : BSigma) :
    ap (fun x => x ⊕ T) p = ap (fun x => x ⊕ T) q -> p = q.
  Proof.
    intro h.
    apply (equiv_inj (@path_BSigma S1 S2)^-1).
    apply (isinj_equiv_functor_sum_r (B:=T)
                                     ((equiv_path_BSigma _ _)^-1 p) ((equiv_path_BSigma _ _)^-1 q)) .
    apply (equiv_inj (@path_BSigma (S1 ⊕ T) (S2 ⊕ T))).
    refine ((natural_path_BSigma_l _)^ @ _ @ natural_path_BSigma_l _).
    refine (_ @ h @ _);
      apply (ap (ap (fun x : BSigma => x ⊕ T))).
      - apply eisretr.
      - apply inverse. apply eisretr.
  Defined.

  Definition BSigma_moncat : Monoidal_1Type :=
    Build_Monoidal_1Type
      (BuildTruncType 1 BSigma) plus_BSigma (canon_BSigma 0) BSigma_assoc BSigma_lid BSigma_rid
      BSigma_triangle1 BSigma_triangle2 BSigma_pentagon.

  Definition group_completion_BSigma := group_completion BSigma_moncat BSigma_lcancel .


  (* Lemma equiv_toempty (A : Type) : *)
  (*   (A -> Empty) <~> (A <~> Empty). *)
  (* Proof.     *)
  (*   apply equiv_iff_hprop. *)
  (*   - intro f. apply (BuildEquiv A Empty f). apply all_to_empty_isequiv. *)
  (*   - apply equiv_fun. *)
  (* Qed. *)
    
  Lemma sum_empty_is_empty (A B : Type) :
    A + B <~> Empty -> A <~> Empty.
  Proof.
    intro e.
    apply (BuildEquiv A Empty (fun a => e (inl a)) ). apply all_to_empty_isequiv.
  Defined.    

  Definition univalent_group_completion_BSigma :
    Categories.IsCategory group_completion_BSigma.
  Proof.
    apply univalent_monactcat; simpl.
    - intros A B.
      intro p.
      apply path_BSigma. simpl.
      apply (sum_empty_is_empty A B).
      apply ((path_BSigma)^-1 p).
    - intro A.
      apply (trunc_equiv' (Empty <~> A)).
      + apply (equiv_path_BSigma (canon_BSigma 0)).
      + apply (trunc_equiv' (A <~> Empty)).
        * apply equiv_equiv_inverse.
        * exact _.
  Qed.    
  
End BSigma.


Require Import delooping.
Require Import monoids_and_groups B_Aut permutations.

Definition iso_loop_symgrp (m : nat) :
  Isomorphism  (SymGrp m)
                 (loopGroup
                    (Build_pType
                       (Finite_Types m) _)).
  Proof.
    srapply @Build_Grp_Iso'.
    - simpl. unfold point. unfold ispointed_finite_types.
      apply (equiv_path_finite_types_fix m (canon m) (canon m)).
    - intros e1 e2. simpl in e1, e2.
      apply (path_finite_types_fix_compose m (canon m) (canon m) (canon m) e1 e2).
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

  (* move *)
  Definition isoisretr {M N : Monoid} (f : Isomorphism M N) :
    f oH (iso_inv f) = idhom.
  Proof.
    apply path_hom. apply path_arrow. apply (eisretr f).
  Defined.

  Definition homcompose_f_ff {K L M N : Monoid}
             (f : Hom K L) (g : Hom L M) (h : Hom M N)
    : h oH (g oH f) = (h oH g) oH f.
  Proof.
    apply path_hom. reflexivity.
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
      apply path_finite_types_fix.
      apply fin_resp_sum.
  Defined.

  (* move *)
  Definition path_finite_types_fix_inv {m : nat} (A B : Finite_Types m) (e : A <~> B)
    : path_finite_types_fix m B A (equiv_inverse e) = (path_finite_types_fix m A B e)^.
  Proof.
    unfold path_finite_types_fix.
    refine (ap (path_sigma_hprop B A)
               (path_universe_V_uncurried e) @ _).
    apply path_sigma_hprop_V.
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
    refine (_ @ path_finite_types_fix_compose _ _ _ _ _ _).
    apply moveR_pM.
    refine (_ @ (ap (fun p => _ @ p)
                    (path_finite_types_fix_inv
                       (sum_finite_types (canon m) (canon n)) (canon (n + m))
                       (fin_resp_sum m n)))).
    refine (_ @ path_finite_types_fix_compose _ _ _ _ _ _).
    transitivity
      (path_finite_types_fix
         (n + m)
         (sum_finite_types (canon m) (canon n))
         (sum_finite_types (canon m) (canon n))
         (s +E t)).
    - refine (_ @
                (ap011 (fun g h =>
                          path_finite_types_fix
                            (n + m)
                            (sum_finite_types (canon m) (canon n))
                            (sum_finite_types (canon m) (canon n))
                            (g +E h))
                       (eissect (equiv_path_finite_types_fix m (canon m) (canon m)) s)
                       (eissect (equiv_path_finite_types_fix n (canon n) (canon n)) t))).
      change ((equiv_path_finite_types_fix ?m (canon ?m) (canon ?m)) ?s) with
      ((path_finite_types_fix m (canon m) (canon m)) s).
      generalize ((path_finite_types_fix m (canon m) (canon m)) s). clear s. intro s.
      generalize ((path_finite_types_fix n (canon n) (canon n)) t). clear t. intro t.
      revert s t.
      cut (forall (A : Finite_Types m) (B: Finite_Types n)
                  (s : canon m = A) (t : canon n = B),
              ap (fun X : Finite_Types m * Finite_Types n => sum_finite_types (fst X) (snd X))
                 (path_prod (canon m, canon n) (A, B) s t) =
              path_finite_types_fix (n + m) (sum_finite_types (canon m) (canon n))
                                    (sum_finite_types A B)
                                    ((equiv_path_finite_types_fix m (canon m) A)^-1 s
                                     +E (equiv_path_finite_types_fix n (canon n) B)^-1 t)).
      { intro H. apply H. }
      intros A B [] []. simpl. 
      apply inverse.
      refine (_ @ path_finite_types_fix_id _ _).
      apply (ap (path_finite_types_fix _ _ _)).
      apply path_equiv. apply path_arrow. intros [x | x]; reflexivity.                       
                       
    - apply (ap (path_finite_types_fix _ _ _ )).
      apply path_equiv. apply path_arrow. intro x.
      apply inverse. ev_equiv.
      refine (eissect (fin_resp_sum m n) ((s +E t) ((fin_resp_sum m n)^-1 ((fin_resp_sum m n) x))) @ _).
      apply (ap (s +E t)).
      apply eissect.
  Defined.
      
  (* TODO *)
End loop_BSigma.

Definition add_canon (m n : nat) :
  pMap (Build_pType (Finite_Types n) _) (Build_pType (Finite_Types (n+m)) _).
Proof.
  srapply @Build_pMap.
  - simpl. intro B. exact (sum_finite_types (canon m) B).
  - exact (path_finite_types_fix
             (n+m)
             (sum_finite_types (canon m) (canon n))
             (canon (n+m))
             (fin_resp_sum m n)).
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

(* move *)
Definition pointed_functor_prod {A1 B1 A2 B2 : pType} (f1 : pMap A1 B1) (f2 : pMap A2 B2)
  : pMap (Build_pType (A1 * A2) (point _, point _)) (Build_pType (B1 * B2) (point _, point _)).
Proof.
  srapply @Build_pMap.
  { exact (functor_prod f1 f2). }
  apply path_prod; apply point_eq.
Defined.

(* move *)
Definition functor_mon_prod {A1 A2 B1 B2 C1 C2 D1 D2}
           (f1 : Homomorphism C1 A1)
           (f2 : Homomorphism C2 A2)
           (g1 : Homomorphism B1 D1)
           (g2 : Homomorphism B2 D2)
           (h1 : Homomorphism A1 B1)
           (h2 : Homomorphism A2 B2)
  : mon_prod_hom
      (functor_hom f1 g1 h1)
      (functor_hom f2 g2 h2)
    = functor_hom (mon_prod_hom f1 f2) (mon_prod_hom g1 g2) (mon_prod_hom h1 h2).
Proof.
  apply path_hom. apply path_arrow. intros [c1 c2]; reflexivity.
Defined.

(* move *)
Definition mon_prod_hom_compose {A1 A2 A3 B1 B2 B3 : Monoid}
           (f1 : Homomorphism A1 A2)
           (f2 : Homomorphism A2 A3)
           (g1 : Homomorphism B1 B2)
           (g2 : Homomorphism B2 B3)
  : mon_prod_hom (f2 oH f1) (g2 oH g1) = mon_prod_hom f2 g2 oH mon_prod_hom f1 g1.
Proof.
  apply path_hom. apply path_arrow. intros [a b]. reflexivity.
Defined.

Definition mon_prod_hom_id (A1 A2 : Monoid)
  : mon_prod_hom (@idhom A1) (@idhom A2) = @idhom (mon_prod A1 A2).
Proof.
  apply path_hom. apply path_arrow. intros [a1 a2]. reflexivity.
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
  change ((iso_loop_symgrp ?n) ?x) with (path_finite_types_fix n (canon n) (canon n) x).
  change ((functor_loop _ _ ?f) ?p) with ((point_eq f)^ @ (ap f p @ point_eq f)).
  refine (_ @ (path_finite_types_fix_compose (n+m) (canon (n+m))
                                             (sum_finite_types (canon m) (canon n))
                                             (canon (n+m))
                                             _
                                             (fin_resp_sum m n oE (equiv_idmap +E s)))^).
  apply concat2.
  { simpl.  unfold point. unfold ispointed_finite_types.
    apply inverse.
    apply path_finite_types_fix_inv. }
  refine (_ @ (path_finite_types_fix_compose (n+m)
                                           (sum_finite_types (canon m) (canon n))
                                           (sum_finite_types (canon m) (canon n))
                                           (canon (n+m))
                                           (equiv_idmap +E s)
                                           (fin_resp_sum m n))^).
  apply whiskerR.
  refine (_ @
            ap (fun e => _ (equiv_idmap +E e))
            (eissect (equiv_path_finite_types_fix n (canon n) (canon n)) s)).
  change (equiv_path_finite_types_fix n (canon n) (canon n) s) with
  (path_finite_types_fix n (canon n) (canon n) s).
  generalize (path_finite_types_fix n (canon n) (canon n) s). clear s. intro s.
  revert s.
  cut (forall (A : Finite_Types n) (s : canon n = A),
          ap (add_canon m n) s =
          path_finite_types_fix (n + m)
                                (sum_finite_types (canon m) (canon n))
                                (sum_finite_types (canon m) A)
                                (equiv_idmap +E (equiv_path_finite_types_fix _ _ _)^-1 s)).
  { intro H. apply H. }
  intros A []. simpl.
  apply inverse.
  refine (_ @ path_finite_types_fix_id _ _).
  apply (ap (path_finite_types_fix _ _ _)).
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
