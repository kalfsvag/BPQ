Require Import HoTT.
Require Import finite_lemmas.

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


(* move *)
Global Instance istrunc_finite_types {m : nat} : IsTrunc 1 (Finite_Types m).
Proof.
  intros x y.
  change (IsTrunc_internal 0) with IsHSet.
  apply (trunc_equiv' (x <~> y)).
  - apply equiv_path_finite_types_fix.
  - apply istrunc_equiv.
Qed.

Global Instance ispointed_finite_types {m : nat} : IsPointed (Finite_Types m) := canon m.

Lemma isconn_finite_types (m : nat) :
  forall x : Finite_Types m,
    merely (canon m = x).
Proof.
  intros [A fA]. strip_truncations.
  apply tr. apply inverse. apply path_finite_types_fix.
  exact fA.
Qed.

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
    pMap (Build_pType (Finite_Types m) _) (Build_pType (Finite_Types n) _)
    -> Homomorphism (SymGrp m) (SymGrp n)
    := functor_hom
         (iso_loop_symgrp m) (iso_inv (iso_loop_symgrp n))
         o
         functor_loop
         (Build_pType (Finite_Types m) _) (isconn_finite_types m)  
         (Build_pType (Finite_Types n) _).

  Global Instance isequiv_loop_BSigma (m n : nat) : IsEquiv (loop_BSigma m n) :=
    @isequiv_compose _ _
                     (functor_loop
                        (Build_pType (Finite_Types m) _) (isconn_finite_types m)  
                        (Build_pType (Finite_Types n) _))
                     (isequiv_functor_loop _ _ _)
                     _
                     (functor_hom (iso_loop_symgrp m) (iso_inv (iso_loop_symgrp n)))
                     (isequiv_functor_hom _ _).

  Definition equiv_loop_BSigma (m n : nat) :=
    BuildEquiv _ _ (loop_BSigma m n) (isequiv_loop_BSigma m n).

  Definition loop_BSigma_prod (l m n : nat) :
    pMap (Build_pType ((Finite_Types l) * (Finite_Types m)) (point _,point _))
                      (Build_pType (Finite_Types n) _) ->
    Homomorphism (grp_prod (SymGrp l) (SymGrp m)) (SymGrp n).
  Proof.
    srefine (_ o (functor_loop
                    (Build_pType ((Finite_Types l) * (Finite_Types m)) (point _,point _)) _
                    (Build_pType (Finite_Types n) _))).
    - apply functor_hom.
      + refine (iso_compose 
                (iso_inv (iso_prod_loopGroup
                   (Build_pType (Finite_Types l) _)
                   (Build_pType (Finite_Types m) _))) _).
        apply iso_prod_hom; apply iso_loop_symgrp.
      + apply iso_inv. apply iso_loop_symgrp.
    - simpl. intros [x1 x2].
      generalize (isconn_finite_types l x1). intro p.
      generalize (isconn_finite_types m x2). intro q.
      strip_truncations. destruct p. destruct q.
      apply tr. reflexivity.
  Defined.

  Global Instance isequiv_loop_BSigma_prod (l m n : nat) : IsEquiv (loop_BSigma_prod l m n) :=
    @isequiv_compose _ _
                     (functor_loop _ _ _) (isequiv_functor_loop _ _ _)
                     _
                     (functor_hom _ _)
                     (isequiv_functor_hom _ _).

  Definition equiv_loop_BSigma_prod (l m n : nat) :=
    BuildEquiv _ _ (loop_BSigma_prod l m n) (isequiv_loop_BSigma_prod l m n).
  
  
  Definition loop_BSigma_1 (m : nat) :
    (loop_BSigma m m (pmap_idmap _)) = idhom.
  Proof.
    unfold loop_BSigma.
    transitivity
      (functor_hom (iso_loop_symgrp m) (iso_inv (iso_loop_symgrp m)) idhom).
    - apply (ap (functor_hom (iso_loop_symgrp m) (iso_inv (iso_loop_symgrp m)))).
      apply path_hom. apply path_arrow. apply functor_loop_id.
    - apply path_hom. apply path_arrow. intro x.
      refine (functor_hom_id _ _ (iso_inv (iso_loop_symgrp m)) x ).
  Qed.

  Open Scope monoid_scope.
  Definition loop_BSigma_compose (l m n : nat)
             (f : pMap (Build_pType (Finite_Types l) _) (Build_pType (Finite_Types m) _))
             (g : pMap (Build_pType (Finite_Types m) _) (Build_pType (Finite_Types n) _))
    : loop_BSigma l n (pmap_compose g f) = (loop_BSigma m n g) oH (loop_BSigma l m f).
  Proof.    
    unfold loop_BSigma. 
    refine (ap (functor_hom (iso_loop_symgrp l) (iso_inv (iso_loop_symgrp n)))
               (path_hom _ _
                         (path_arrow _ _
                               (functor_loop_compose
                                  {| pointed_type := Finite_Types l; ispointed_type := canon l |}
                                  (isconn_finite_types l)
                                  {| pointed_type := Finite_Types m; ispointed_type := canon m |}
                                  (isconn_finite_types m)
                                  {| pointed_type := Finite_Types n;
                                     ispointed_type := ispointed_finite_types |} _ _)))^ @ _).
    apply functor_hom_compose_001.
  Defined.

  Definition loop_BSigma_prod_compose (k l m n : nat)
             (f : pMap (Build_pType ((Finite_Types k)*(Finite_Types l)) (point _, point _))
                       (Build_pType (Finite_Types m) _))
             (g : pMap (Build_pType (Finite_Types m) _) (Build_pType (Finite_Types n) _))
    : loop_BSigma_prod k l n (pmap_compose g f)
      = (loop_BSigma m n g) oH (loop_BSigma_prod k l m f).
  Proof.
    apply path_hom. apply path_arrow. intros [s t]. simpl. simpl in s,t.
    unfold point.
    apply (ap (equiv_path _ _)).
    generalize (path_finite_types_fix l (canon l) (canon l) t) as q.
    generalize (path_finite_types_fix k (canon k) (canon k) s) as p. clear s t.
    intros p q.
    cut (((ap g (point_eq f) @ point_eq g)^ @
     (ap (fun x : Finite_Types k * Finite_Types l => g (f x))
        (path_prod (canon k, canon l) (canon k, canon l) p q) @
      (ap g (point_eq f) @ point_eq g)))
         =
         ((point_eq g)^ @
     (ap g
        (path_finite_types_fix m (canon m) (canon m)
           (equiv_path (Fin m) (Fin m)
              (ap pr1
                 ((point_eq f)^ @
                  (ap f (path_prod (canon k, canon l) (canon k, canon l) p q) @
                   point_eq f))))) @ point_eq g))).
    { intro H. refine (ap pr1_path H). }
    change (path_finite_types_fix m (canon m) (canon m) ?x) with
    (equiv_path_finite_types_fix m (canon m) (canon m) x).
    rewrite inv_pp. repeat rewrite concat_pp_p. apply whiskerL.
    repeat rewrite concat_p_pp. apply whiskerR.
    transitivity
      (ap g (((point_eq f)^
              @ ap f (path_prod (canon k, canon l) (canon k, canon l) p q)) @ point_eq f)).
    - refine (_ @ (ap_pp g _ _)^).
      apply whiskerR.
      refine (_ @ (ap_pp g _ _)^).
      apply concat2.
      { apply inverse. apply ap_V. }
      destruct p. destruct q. reflexivity.
    - apply (ap (ap g)).
      change (path_finite_types_fix m (canon m) (canon m) ?x) with
      (equiv_path_finite_types_fix m (canon m) (canon m) x).
      apply (moveL_equiv_M (f := equiv_path_finite_types_fix m (canon m) (canon m))). simpl.
      unfold pr1_path. reflexivity.
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

  Definition loop_BSigma_sum (m n : nat)
    : loop_BSigma_prod m n (n+m) (BSigma_sum_uncurried m n) = block_sum_hom m n.
  Proof.
    apply path_hom. apply path_arrow. intro x. 
    destruct x as [s t].
    unfold block_sum. simpl. 
    unfold pr1_path.
    rewrite ap_pp. rewrite ap_pp.
    rewrite equiv_path_pp. rewrite equiv_path_pp.
    apply (ap011 (fun f g => f oE g)).
    - apply (ap011 (fun f g => f oE g)).
      + refine (eissect (equiv_path_finite_types_fix (n+m)
                                                     (sum_finite_types (canon m) (canon n))
                                                     (canon (n+m))) (fin_resp_sum m n)).
      + simpl in s,t.
        refine (_ @ ap011 (fun f g => f +E g)
                  (eissect (equiv_path_finite_types_fix m (canon m) (canon m)) s)
                  (eissect (equiv_path_finite_types_fix n (canon n) (canon n)) t)). simpl.
        unfold pr1_path.
        generalize (path_finite_types_fix n (canon n) (canon n) t) as q.
        generalize (path_finite_types_fix m (canon m) (canon m) s) as p. intros.
        clear s t.
        transitivity
          (equiv_path
             (Fin m + Fin n) (Fin m + Fin n)
             (ap pr1
                 (ap (fun X : Finite_Types m * Finite_Types n => sum_finite_types (fst X) (snd X))
                     (path_prod (_,_) (_,_) p q)))).
        { reflexivity. }

        cut (forall (A : Finite_Types m) (B : Finite_Types n)
                    (p : canon m = A) (q : canon n = B),
                equiv_path
                  (Fin m + Fin n) (A + B)
                  (ap pr1
                      (ap (fun X : Finite_Types m * Finite_Types n => sum_finite_types (fst X) (snd X))
                                   (path_prod (canon m, canon n) (A, B) p q))) =
                equiv_path (Fin m) A (ap pr1 p) +E equiv_path (Fin n) B (ap pr1 q)).
        { intro H. apply (H (canon m) (canon n)). }
        intros A B [] []. simpl.
        apply path_equiv. simpl. apply path_arrow. intros [x | x]; reflexivity.
    - rewrite ap_V. rewrite equiv_path_V. apply (ap (equiv_inverse)).
      refine (eissect (equiv_path_finite_types_fix (n+m)
                                                   (sum_finite_types (canon m) (canon n))
                                                   (canon (n+m)))
                      ((fin_resp_sum m n))).
  Defined.
  
  
  (* Definition deloop_BSigma_rec (m : nat) *)
  (*            (Y : 1-Type) *)
  (*            (y0 : Y) *)
  (*            (f : (canon m <~> canon m) -> y0 = y0) *)
  (*            (ishom_f : *)
  (*               forall (e g : canon m <~> canon m), *)
  (*                 f (g oE e) = f e @ f g) : *)
  (*   Finite_Types m -> Y. *)
  (* Proof. *)
  (*   srefine (deloop_rec (Finite_Types m) (canon m) _ Y y0 _ _). *)
  (*   - apply isconn_finite_types. *)
  (*   - intro p. *)
  (*     apply f. apply ((path_finite_types_fix m (canon m) (canon m))^-1 p). *)
  (*   - simpl. intros. *)
  (*     refine (_ @ ishom_f _ _). *)
  (*     apply (ap f). *)
  (*     revert α ω. *)
      
  (*     cut (forall (x y: Finite_Types m) (p : canon m = x) (q : x = y), *)
  (*             equiv_path (Fin m) y (p @ q) ..1 = *)
  (*             equiv_path x y  q ..1 oE equiv_path (Fin m) x p ..1). *)
  (*     { intro H. apply H.  } *)
  (*     intros x y p []. destruct p. reflexivity. *)
  (* Defined. *)

  (* Definition functor_BSigma (m n : nat)  *)
  (*   (f : (canon m <~> canon m) -> (canon n <~> canon n)) *)
  (*   (ishom_f :  *)
  (*     forall (e g : canon m <~> canon m), *)
  (*       f (g oE e) = f g oE f e) *)
  (*   : Finite_Types m -> Finite_Types n. *)
  (* Proof. *)
  (*   srefine (deloop_BSigma_rec m _ (canon n) _ _). *)
  (*   - exact ((path_finite_types_fix n (canon n) (canon n)) o f).       *)
  (*   - intros. *)
  (*     refine (_ @ path_finite_types_fix_compose n _ _ _ (f e) (f g)). *)
  (*     apply (ap (path_finite_types_fix n (canon n) (canon n))). *)
  (*     apply ishom_f. *)
  (* Defined. *)

  (* Definition functor_BSigma_of {m n : nat} (g : Finite_Types m -> Finite_Types n) *)
  (*   (ispointed_g : g (canon m) = canon n) : *)
  (*   Finite_Types m -> Finite_Types n. *)
  (* Proof. *)
  (*   srefine (functor_BSigma m n _ _). *)
  (*   - refine ( *)
  (*         (path_finite_types_fix n (canon n) (canon n))^-1 *)
  (*                  o _ o *)
  (*                  (path_finite_types_fix m (canon m) (canon m))). *)
  (*     intro p. *)
  (*     refine (_ @ ap g p @ _). + exact ispointed_g^. + exact ispointed_g. *)
  (*   - simpl. intros. *)
      
  (*     exact  *)
  (* := *)
  (*   rec_of _ (canon m) (isconn_finite_types m) _ g. *)

  (* Definition functor_BSigma_eta (m n : nat) (g : Finite_Types m -> Finite_Types n) : *)
  (*   functor_BSigma_of g == g. *)
  (* Proof. *)
  (*   apply is_rec. *)
  (* Defined. *)


  (* Definition functor_BSigma_of {m n : nat} (g : Finite_Types m -> Finite_Types n): *)
  (*   Finite_Types m -> Finite_Types n := *)
  (*   rec_of _ (canon m) (isconn_finite_types m) _ g. *)

  (* Definition functor_BSigma_eta (m n : nat) (g : Finite_Types m -> Finite_Types n) : *)
  (*   functor_BSigma_of g == g. *)
  (* Proof. *)
  (*   apply is_rec. *)
  (* Defined. *)

  (* Definition ishom_compose {l m n : nat} *)
  (*            (f1 : canon m <~> canon m -> canon n <~> canon n) *)
  (*            (ishom_f1 : forall (e g : canon m <~> canon m), *)
  (*                f1 (g oE e) = f1 g oE f1 e) *)
  (*            (f2 : canon l <~> canon l -> canon m <~> canon m) *)
  (*            (ishom_f2 : forall (e g : canon l <~> canon l), *)
  (*                f2 (g oE e) = f2 g oE f2 e) : *)
  (*   forall (e g : canon l <~> canon l), *)
  (*     f1 (f2 (g oE e)) = f1 (f2 g) oE f1 (f2 e). *)
  (* Proof. *)
  (*   intros. *)
  (*   refine (_ @ ishom_f1 _ _). apply (ap f1). apply ishom_f2. *)
  (* Defined. *)

  (* Definition functor_BSigma_compose (l m n : nat) *)
  (*            (f1 : canon m <~> canon m -> canon n <~> canon n) *)
  (*            (ishom_f1 : forall (e g : canon m <~> canon m), *)
  (*                f1 (g oE e) = f1 g oE f1 e) *)
  (*            (f2 : canon l <~> canon l -> canon m <~> canon m) *)
  (*            (ishom_f2 : forall (e g : canon l <~> canon l), *)
  (*                f2 (g oE e) = f2 g oE f2 e) : *)
  (*   functor_BSigma m n f1 ishom_f1 o functor_BSigma l m f2 ishom_f2 == *)
  (*   functor_BSigma l n(f1 o f2) (ishom_compose f1 ishom_f1 f2 ishom_f2). *)
  (* Proof. *)
  (*   intro x. revert x. *)
  (*   srapply @ *)
  (*   refine (_ @ functor_BSigma_eta _ _ _ _ ). *)
  (*   unfold  *)
             
      

                  
                  
      

    

             (* (ishom_f : *)
             (*    forall (e g : canon m <~> canon m), *)
             (*      f (g oE e) = transport_pp P *)
             (*                                (path_finite_types_fix m _ _ e) *)
             (*                                (path_finite_types_fix m _ _ g) *)
  (* : forall x : Finite_Types m, P x. *)
  (* Proof. *)
  (*   srefine (deloop_ind (Finite_Types m) (canon m) _ P p0 _ _). *)
  (*   - intros [A fA]. strip_truncations. *)
  (*     apply tr. apply inverse. *)
  (*     apply path_finite_types_fix. exact fA. *)
  (*   - intro ω. *)
  (*     refine (_ @ f ((path_finite_types_fix m (canon m) (canon m))^-1 ω)). *)
  (*     apply (ap (fun x => *)
  (*              transport P x p0)). *)
  (*     apply inverse. apply eisretr. *)
  (*   - intros. hnf. *)
  (*     repeat rewrite concat_1p. *)
  
  (* TODO *)
End loop_BSigma.

Definition add_canon (m n : nat) :
  pMap (Build_pType (Finite_Types n) _) (Build_pType (Finite_Types (n+m)) _).
Proof.
  srapply @Build_pMap.
  - apply (sum_finite_types (canon m)).
  - apply path_finite_types_fix. 
    apply fin_resp_sum.
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

Definition deloop_mult_uncurried : pMap
                                     (Build_pType (Finite_Types 2 * Finite_Types 2) (point _, point _))
                                     (Build_pType (Finite_Types 2) _).
Proof.
  apply (loop_BSigma_prod 2 2 2)^-1.
  apply mult_hom.
  intros x y. apply symm_sigma2.
Defined.

Definition loop_BDet_sum {m n : nat} (A : Finite_Types m) (B : Finite_Types n) :
  BDet (n+m) (sum_finite_types A B) = deloop_mult_uncurried (BDet m A, BDet n B).
Proof.
  change (sum_finite_types A B)
         with
         (BSigma_sum_uncurried m n (A,B)).
  change ((BDet m) A, (BDet n) B)
         with
         ((functor_prod (BDet m) (BDet n)) (A,B)).
  cut (pmap_compose (BDet (n+m)) (BSigma_sum_uncurried m n) =
       pmap_compose (deloop_mult_uncurried)
                    (Build_pMap
                       (Build_pType (_*_) (_,_))
                       (Build_pType (_*_) (_,_))
                       (functor_prod (BDet m) (BDet n))
                       (path_prod (_,_) (_,_)
                                  (point_eq (BDet m))
                                  (point_eq (BDet n))))).
  { intro H.
    destruct ((equiv_path_pmap _ _)^-1 H).
    apply pointed_htpy. }       (* make this quicker. . . *)
  apply (equiv_inj (equiv_loop_BSigma_prod _ _ _)).
  refine (loop_BSigma_prod_compose _ _ _ _ _ _ @ _).
  rewrite (eisretr (loop_BSigma (n+m) 2)).
  rewrite loop_BSigma_sum.

  det_block_sum
  
    
  
  unfold BDet.
  apply moveR_equiv_V.
simpl.

  loop_BSigma_prod_compose
  
         

Definition add_canon_is_block_sum_id (m n : nat) :
  loop_BSigma n (n+m) (add_canon m n) = (block_sum_id_hom m n).
Proof.
  unfold loop_BSigma.
  apply path_hom.
  apply path_arrow. intro p. 
  unfold functor_hom. simpl.
  unfold block_sum. unfold pr1_path.

  hnf.
  change ((BuildEquiv _ _ ?f _) ?x) with (f x).
  unfold functor_hom.
  change ((?f oH ?g oH ?h) p) with (f (g (h p))).
  hnf.

  apply moveL_equiv_M.
  simpl. unfold block_sum.
  unfold point. unfold ispointed_finite_types.
  unfold pr1_path.
  rewrite ap_pp. rewrite ap_pp.
  rewrite equiv_path_pp. rewrite equiv_path_pp.
  apply (ap011 (equiv_compose')); try apply (ap011 (equiv_compose')).
  - cut (ap pr1
            (path_sigma_hprop
               (sum_finite_types (canon m) (canon n)) (canon (n + m))
               (path_universe_uncurried (fin_resp_sum m n))) =
         path_universe_uncurried (fin_resp_sum m n)).
    { apply (moveR_equiv_M). }
    refine (pr1_path_path_sigma_hprop _ _ _).
  - simpl.
    simpl in p. 
    revert p.
    cut (forall (x : Finite_Types n) (p : point (Finite_Types n) = x),
            equiv_path (Fin m + Fin n) (Fin m + x) (ap pr1 (ap (sum_finite_types (canon m)) p)) =
            1 +E equiv_path (Fin n) x (ap pr1 p)).
    { intro H. apply H. }
    intros x []. simpl.
    apply path_equiv.  simpl. apply path_arrow. intros [y | y]; reflexivity.
  - rewrite ap_V. refine (equiv_path_V _ _ _ @ _).
    apply (ap (equiv_inverse)).
    cut (ap pr1
            (path_sigma_hprop
               (sum_finite_types (canon m) (canon n)) (canon (n + m))
               (path_universe_uncurried (fin_resp_sum m n))) =
         path_universe_uncurried (fin_resp_sum m n)).
    { apply moveR_equiv_M. }    
    refine (pr1_path_path_sigma_hprop _ _ _).
Qed.

Definition isretr_BDet (m : nat) :
    pmap_compose (BDet m.+2) (add_canon m 2) = pmap_idmap _.
Proof.
  apply (equiv_inj (equiv_inverse (pMap_BSigma 2 2))).
  assert (p : idhom =
              equiv_inverse
                (pMap_BSigma 2 2)
                (pmap_idmap
                   {| pointed_type := Finite_Types 2; ispointed_type := ispointed_finite_types |})
              ).
  { apply moveL_equiv_V. apply pMap_BSigma_1. }
  refine (_ @ p). clear p.
  transitivity
    (compose_hom (det_hom (m.+2)) (equiv_inverse (pMap_BSigma _ _) (add_canon m 2))).
  - apply moveR_equiv_V.
    refine (_ @ pMap_BSigma_compose 2 (m.+2) 2 _ _).
    apply (ap (pmap_compose (BDet m.+2))). apply inverse.
    apply eisretr.
  - transitivity (det_hom m.+2 oH (block_sum_id_hom m 2)).
    + apply (ap (compose_hom (det_hom m.+2))).
      apply moveR_equiv_V.
      apply add_canon_is_block_sum_id.
    + apply path_hom. apply path_arrow.
      intro x.
      refine (det_block_sum equiv_idmap x @ _).
      rewrite det_id. rewrite det2_is_id.
      apply ecompose_e1.
Qed.

Definition iso_transport_sym {M N : Monoid} (f : Isomorphism M N) :
  symmetric (@mon_mult N) -> symmetric (@mon_mult M).
Proof.
  unfold symmetric. intros symm_N m1 m2.
  apply (equiv_inj f).
  refine (preserve_mult f @ _ @ (preserve_mult f)^).
  apply symm_N.
Qed.  

Definition deloop_mult : Finite_Types 2 -> Finite_Types 2 -> Finite_Types 2.
Proof.
  cut ((Finite_Types 2) * (Finite_Types 2) -> (Finite_Types 2)).
  - intro f.
    intros x y. exact (f (x,y)).
  - apply (pointed_fun (Build_pType (Finite_Types 2 * Finite_Types 2) (point _, point _))
                       (Build_pType (Finite_Types 2) _ )).
    srapply @functor_deloop. 
    + simpl.
      intros [x1 x2].
      generalize (isconn_finite_types 2 x1). intro p.
      generalize (isconn_finite_types 2 x2). intro q.
      strip_truncations. destruct p. destruct q.
      apply tr. reflexivity.
    + refine (_ oH prod_loopGroup (Build_pType (Finite_Types 2) _) (Build_pType (Finite_Types 2) _)).
      apply mult_hom.
      apply (iso_transport_sym (iso_inv (iso_loop_aut (canon 2)))).
      intros x y. simpl.
      apply (symm_sigma2 y x).
Defined.

Definition deloop_det_sum {m n : nat} (A : Finite_Types m) (B : Finite_Types n) :
  BDet (n+m) (sum_finite_types A B) = deloop_mult (BDet n B) (BDet m A).
Proof.
  revert A B.
  srapply (deloop_double_ind_set
           (Build_pType (Finite_Types m) _) (isconn_finite_types m)
           (Build_pType (Finite_Types n) _) (isconn_finite_types n)).
  - hnf. unfold point.
    unfold ispointed_type.
    transitivity (BDet (n+m) (canon (n+m))).
    { apply (ap (BDet (n+m))).
      apply path_finite_types_fix.
      exact (BuildEquiv _ _ (finsum m n) _). }
    refine (point_eq _ @ _). unfold point. unfold ispointed_type. unfold ispointed_finite_types.
    apply inverse.
    refine (ap011 (deloop_mult) (point_eq (BDet n)) (point_eq (BDet m)) @ _).
    simpl.
    unfold deloop_mult. unfold functor_deloop. hnf.
    refine (deloop_rec_beta_pt _ _ _ _ _ _ ).
  - hnf.
    intros.
    refine (transport_paths_FlFr ω _ @ _).
    admit.
  - admit.

    
simpl.
      apply equiv_finsum.
    
    unfold canon. unfold point. unfold ispointed_BAut.
    
    change
      
      (sum_finite_types (ispointed_type {| pointed_type := Finite_Types m; ispointed_type := canon m |})
       (ispointed_type {| pointed_type := Finite_Types n; ispointed_type := canon n |}))
    
    unfold sum_finite_types. hnf.
           
           

           
  unfold BDet.
  
  
  unfold BDet. unfold pMap_BSigma. 
simpl.