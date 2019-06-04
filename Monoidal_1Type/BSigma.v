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
  Definition path_BSigma {A B : BSigma} : A <~> B <~> A = B
       := path_finite_types A B.
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

  (* (* path_BSigma respects composition *) *)
  (* shorter proof than in finite_lemmas *)
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
    refine (path_finite_types_1 A).
  Qed.
  (* Proof. *)
  (*   apply (equiv_inj path_BSigma^-1). *)
  (*   refine (_ @ (eissect (path_BSigma) (e1 oE e2))^). *)
  (*   apply path_equiv. simpl. *)
  (*   unfold pr1_path. *)
  (*   rewrite ap_pp. *)
  (*   rewrite ap_pr1_path_sigma_hprop. rewrite ap_pr1_path_sigma_hprop. apply path_arrow. intro s. *)
  (*   refine (transport_pp idmap _ _ _ @ _). *)
  (*   refine (ap10 (transport_idmap_path_universe e1) _ @ _). apply (ap e1). *)
  (*   apply (ap10 (transport_idmap_path_universe e2)). *)
  (* Qed. *)

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
  Definition natural_path_BSigma_l {S1 S2 S3: BSigma} (e : S1 <~> S2) :
    ap (fun x : BSigma => x ⊕ S3) (path_BSigma e) = path_BSigma (A := S1 ⊕ S3) (B := S2 ⊕ S3) (equiv_functor_sum_r (B := S3) e).
  Proof.
    
    refine (_ @ ap (fun e' => @path_BSigma (S1⊕ S3) (S2 ⊕ S3) (equiv_functor_sum_r e'))
              (eissect (@path_BSigma S1 S2) e)).
    generalize (path_BSigma e). intros [].
    simpl. unfold path_BSigma. apply inverse.
    refine (_ @ path_finite_types_1 (S1 ⊕ S3)).
    apply (ap (path_finite_types (S1 ⊕ S3) (S1 ⊕ S3))).
    apply path_equiv. apply path_arrow. intros [s1 | s3]; reflexivity.
  Qed.

  Definition natural_path_BSigma_r {S1 S2 S3: BSigma} (e : S2 <~> S3) :
    ap (fun x : BSigma => S1 ⊕ x) (path_BSigma e) = path_BSigma (A := S1 ⊕ S2) (B := S1 ⊕ S3) (equiv_functor_sum_l (A := S1) e).
  Proof.
    refine (_ @ ap (fun e' => @path_BSigma (S1 ⊕ S2) (S1 ⊕ S3) (equiv_functor_sum_l e'))
              (eissect (@path_BSigma S2 S3) e)).
    generalize (path_BSigma e). intros [].
    simpl. unfold path_BSigma. apply inverse.
    refine (_ @ path_finite_types_1 (S1 ⊕ S2)).
    apply (ap (path_finite_types (S1 ⊕ S2) (S1 ⊕ S2))).
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



  
  
  (*TODO: How [cardinal] respects associativity and identity proofs *)
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
    apply (isinj_equiv_functor_sum_r (B:=T) (path_BSigma^-1 p) (path_BSigma^-1 q)) .
    apply (equiv_inj (@path_BSigma (S1 ⊕ T) (S2 ⊕ T))).
    refine ((natural_path_BSigma_l _)^ @ _ @ natural_path_BSigma_l _).
    refine (_ @ h @ _);
      apply (ap (ap (fun x : BSigma => x ⊕ T))).
      - apply eisretr.
      - apply inverse. apply eisretr.
  Defined.

  Definition BSigma_moncat : Monoidal_1Type :=
    Build_Monoidal_1Type (BuildTruncType 1 BSigma) plus_BSigma (canon_BSigma 0) BSigma_assoc BSigma_lid BSigma_rid BSigma_triangle1 BSigma_triangle2 BSigma_pentagon.

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
      + apply (path_BSigma (A := (canon_BSigma 0))).
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
  - apply path_finite_types_fix.
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
Require Import monoids_and_groups B_Aut.
Section deloop_BSigma.

  Definition pMap_BSigma (m n : nat) :
    Homomorphism (AutGroup (Fin m)) (AutGroup (Fin n)) <~>
                 pMap (Build_pType (Finite_Types m) _) (Build_pType (Finite_Types n) _).
  Proof.
    transitivity (Homomorphism (loopGroup (Build_pType (Finite_Types m) _))
                               (loopGroup (Build_pType (Finite_Types n) _))).
    - apply equiv_functor_hom.
      + 
        admit.
      + unfold Finite_Types. unfold ispointed_finite_types.
        change (canon n) with (ispointed_BAut (Fin n)).
        refine (iso_compose _ (iso_loop_aut (Fin n))). simpl.
        apply iso_id.
         Bsrapply @Build_Isomorphism.
        apply (iso_id (loopGroup
                         {| pointed_type := B_Aut.B_Aut (Fin n); ispointed_type := B_Aut.ispointed_BAut (Fin n) |})).
        unfold B_Aut. unfold Finite_Types. simpl.
        
        

      srefine (BuildEquiv _ _ (functor_hom _ _) _).
      + 
  
  Definition deloop_BSigma_rec (m : nat)
             (Y : 1-Type)
             (y0 : Y)
             (f : (canon m <~> canon m) -> y0 = y0)
             (ishom_f :
                forall (e g : canon m <~> canon m),
                  f (g oE e) = f e @ f g) :
    Finite_Types m -> Y.
  Proof.
    srefine (deloop_rec (Finite_Types m) (canon m) _ Y y0 _ _).
    - apply isconn_finite_types.
    - intro p.
      apply f. apply ((path_finite_types_fix m (canon m) (canon m))^-1 p).
    - simpl. intros.
      refine (_ @ ishom_f _ _).
      apply (ap f).
      revert α ω.
      
      cut (forall (x y: Finite_Types m) (p : canon m = x) (q : x = y),
              equiv_path (Fin m) y (p @ q) ..1 =
              equiv_path x y  q ..1 oE equiv_path (Fin m) x p ..1).
      { intro H. apply H.  }
      intros x y p []. destruct p. reflexivity.
  Defined.

  Definition functor_BSigma (m n : nat) 
    (f : (canon m <~> canon m) -> (canon n <~> canon n))
    (ishom_f : 
      forall (e g : canon m <~> canon m),
        f (g oE e) = f g oE f e)
    : Finite_Types m -> Finite_Types n.
  Proof.
    srefine (deloop_BSigma_rec m _ (canon n) _ _).
    - exact ((path_finite_types_fix n (canon n) (canon n)) o f).      
    - intros.
      refine (_ @ path_finite_types_fix_compose n _ _ _ (f e) (f g)).
      apply (ap (path_finite_types_fix n (canon n) (canon n))).
      apply ishom_f.
  Defined.

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

  Definition ishom_compose {l m n : nat}
             (f1 : canon m <~> canon m -> canon n <~> canon n)
             (ishom_f1 : forall (e g : canon m <~> canon m),
                 f1 (g oE e) = f1 g oE f1 e)
             (f2 : canon l <~> canon l -> canon m <~> canon m)
             (ishom_f2 : forall (e g : canon l <~> canon l),
                 f2 (g oE e) = f2 g oE f2 e) :
    forall (e g : canon l <~> canon l),
      f1 (f2 (g oE e)) = f1 (f2 g) oE f1 (f2 e).
  Proof.
    intros.
    refine (_ @ ishom_f1 _ _). apply (ap f1). apply ishom_f2.
  Defined.

  Definition functor_BSigma_compose (l m n : nat)
             (f1 : canon m <~> canon m -> canon n <~> canon n)
             (ishom_f1 : forall (e g : canon m <~> canon m),
                 f1 (g oE e) = f1 g oE f1 e)
             (f2 : canon l <~> canon l -> canon m <~> canon m)
             (ishom_f2 : forall (e g : canon l <~> canon l),
                 f2 (g oE e) = f2 g oE f2 e) :
    functor_BSigma m n f1 ishom_f1 o functor_BSigma l m f2 ishom_f2 ==
    functor_BSigma l n(f1 o f2) (ishom_compose f1 ishom_f1 f2 ishom_f2).
  Proof.
    intro x. revert x.
    srapply @
    refine (_ @ functor_BSigma_eta _ _ _ _ ).
    unfold 
             
      

                  
                  
      

    

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
End deloop_BSigma.

Require Import determinants.

Definition BDet (m : nat) : Finite_Types m -> Finite_Types 2.
Proof.
  srapply (deloop_BSigma_rec m _ (canon 2)).
  - exact (determinant m).

    
  srapply (deloop_rec (Finite_Types m) (canon m) (isconn_finite_types m)).
  - exact (canon 2).
  - refine (path_finite_types_fix 2 _ _ o _ o (path_finite_types_fix m _ _)^-1).
    exact (determinant m).
  - intros .
    refine (_ @ path_finite_types_fix_compose 2 _ _ _ _ _).
    apply (ap (path_finite_types_fix 2 (canon 2) (canon 2))).
    refine (_ @ det_compose m _ _).
    apply (ap (determinant m)).
    apply moveR_equiv_V.
    refine (_ @ (path_finite_types_fix_compose m _ _ _ _ _)^).
    apply inverse.
    apply concat2; apply eisretr.
Defined.

Definition isretr_BDet (m : nat) :
  forall x : Finite_Types 2,
    BDet m.+2 (sum_finite_types (canon m) x) = x.
Proof.
  srapply (deloop_ind_set (Finite_Types 2) (canon 2) (isconn_finite_types 2)).
  - simpl.
    refine (ap (BDet m.+2) (fin_resp_sum_id m 2) @ _).
    apply deloop_rec_beta_x0.
  - 



    
  
