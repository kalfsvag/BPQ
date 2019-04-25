Require Import HoTT.
Require Import monoidal_1type.
Require Import group_complete_1type.
Require Import finite_lemmas.
Require Import trunc_lemmas.

(*Defining the monoidal 1-type of finite sets and isomorphisms*)
Section BΣ.
    
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Definition BΣ :=
    {m : nat & Finite_Types m}.
    (* { S : Type & Finite S}. *)
  Definition type_of_fin : BΣ -> Type := (fun A => A.2.1).
  Coercion type_of_fin : BΣ  >-> Sortclass.

  Global Instance istrunc_BΣ : IsTrunc 1 BΣ.
  Proof.
    apply (trunc_equiv' {S : Type & Finite S}).
    - apply equiv_inverse. apply sum_finite.
    - apply trunc_sigma'.
      +  intro A. exact _.
      +  intros A B.
         srapply @istrunc_paths_Type. 
         apply isset_Finite. exact B.2.
  Defined.

  (*Canonical objects in BΣ*)
  Definition canon_BΣ (n : nat) : BΣ := (Fin n; Build_Finite (Fin n) n (tr 1%equiv)).
  


  (* Describing the path type of BΣ *)
  Definition path_BΣ {S T : BΣ} : S <~> T <~> S = T
    := path_finite_types_sum S T.

  (* path_BΣ respects composition *)
  Definition path_BΣ_compose {S1 S2 S3 : BΣ} (e1 : S2 <~> S1) (e2 : S3 <~> S2) :
    path_BΣ e2 @ path_BΣ e1 = path_BΣ (e1 oE e2).
  Proof.
    apply (equiv_inj path_BΣ^-1).
    refine (_ @ (eissect (path_BΣ) (e1 oE e2))^).
    apply path_equiv. simpl.
    unfold pr1_path.
    rewrite ap_pp.
    rewrite ap_pr1_path_sigma_hprop. rewrite ap_pr1_path_sigma_hprop. apply path_arrow. intro s.
    refine (transport_pp idmap _ _ _ @ _).
    refine (ap10 (transport_idmap_path_universe e1) _ @ _). apply (ap e1).
    apply (ap10 (transport_idmap_path_universe e2)).
  Qed.

  Definition plus_BΣ : BΣ -> BΣ -> BΣ.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (S1 + S2 ; finite_sum _ _)%type.
  Defined.

  Definition BΣ_id : BΣ := canon_BΣ 0.

  Local Notation "S1 ⊕ S2" := (plus_BΣ S1 S2) (at level 50, no associativity).  

  (* path_BΣ behaves well with respect to sum *)
  Definition natural_path_BΣ_l {S1 S2 S3: BΣ} (e : S1 <~> S2) :
    ap (fun x : BΣ => x ⊕ S3) (path_BΣ e) = path_BΣ (S := S1 ⊕ S3) (T := S2 ⊕ S3) (equiv_functor_sum_r (B := S3) e).
  Proof.
    apply (equiv_inj (path_BΣ)^-1).
    refine (_ @ (eissect (path_finite_types_sum (S1 ⊕ S3) (S2 ⊕ S3)) (equiv_functor_sum_r e))^).
    apply path_equiv. simpl.
    unfold pr1_path. 
    transitivity
      (transport idmap (ap (fun X : Type => X + S3) (ap Overture.pr1
                             (path_sigma_hprop S1 S2 (path_universe_uncurried e))))).
    { apply (ap (transport idmap)).
      refine
        ((ap_compose (fun x : BΣ => x ⊕ S3) Overture.pr1 _)^ @
                    ap_compose Overture.pr1 (fun X : Type => X + S3) _). }
    apply path_arrow. intro s.
    refine ((transport_idmap_ap _ _ _ _ _ _)^ @ _).
    refine ((ap (fun p => transport (fun X : Type => X + S3) p s) (ap_pr1_path_sigma_hprop _ _ _)) @ _).
    destruct S1 as [S1 fin1]. destruct S2 as [S2 fin2]. destruct S3 as [S3 fin3]. simpl in *.
    clear fin1 fin2 fin3.
    revert e s.
    apply (equiv_induction
           (fun S2 e => forall s : (S1 + S3), transport (fun X : Type => X + S3) (path_universe_uncurried e) s = functor_sum e idmap s)).
    change (path_universe_uncurried 1) with (path_universe (A := S1) idmap).      
    rewrite path_universe_1. simpl.
    intros [s1 | s3]; reflexivity.
  Qed.

  Definition natural_path_BΣ_r {S1 S2 S3: BΣ} (e : S2 <~> S3) :
    ap (fun x : BΣ => S1 ⊕ x) (path_BΣ e) = path_BΣ (S := S1 ⊕ S2) (T := S1 ⊕ S3) (equiv_functor_sum_l (A := S1) e).
  Proof.
    apply (equiv_inj (path_BΣ)^-1).
    refine (_ @ (eissect (path_finite_types_sum (S1 ⊕ S2) (S1 ⊕ S3)) (equiv_functor_sum_l e))^).
    apply path_equiv. simpl.
    unfold pr1_path. 
    transitivity
      (transport idmap (ap (fun X : Type => S1 + X) (ap Overture.pr1 (path_sigma_hprop S2 S3 (path_universe_uncurried e))))).
    { apply (ap (transport idmap)).
      refine ((ap_compose (fun x : BΣ => S1 ⊕ x) Overture.pr1 _)^ @ ap_compose Overture.pr1 (fun X : Type => S1 + X ) _). }
    apply path_arrow. intro s.
    refine ((transport_idmap_ap _ _ _ _ _ _)^ @ _).
    refine ((ap (fun p => transport (fun X : Type => S1 + X) p s) (ap_pr1_path_sigma_hprop _ _ _)) @ _).
    destruct S1 as [S1 fin1]. destruct S2 as [S2 fin2]. destruct S3 as [S3 fin3]. simpl in *.
    clear fin1 fin2 fin3. change (path_universe_uncurried e) with (path_universe e). 
    revert e s. 
    apply (equiv_induction
           (fun S3 e => forall s : (S1 + S2), transport (fun X : Type => S1 + X) (path_universe e) s = functor_sum idmap e s)).
    rewrite path_universe_1. simpl.
    intros [s1 | s2]; reflexivity.
  Qed.
  
  (*The monoidal structure on BΣ*)
  
  Definition BΣ_assoc : associative plus_BΣ.
  Proof.
    intros S1 S2 S3.
    apply path_BΣ.
    apply equiv_sum_assoc. 
  Defined.

  Definition BΣ_lid : left_identity_mult plus_BΣ (canon_BΣ 0).
  Proof.
    intro S. apply path_BΣ.
    apply sum_empty_l.
  Defined.
  
  Definition BΣ_rid : right_identity_mult plus_BΣ (canon_BΣ 0).
  Proof.
    intro S. apply path_BΣ.
    apply sum_empty_r.
  Defined.

  Definition BΣ_symmetric : symmetric plus_BΣ. 
  Proof.
    intros S1 S2. apply path_BΣ. apply equiv_sum_symm.
  Defined.



  
  
  (*TODO: How [cardinal] respects associativity and identity proofs *)
  Definition BΣ_triangle1 : coherence_triangle1 BΣ_assoc BΣ_lid.
  Proof.
    intros S1 S2.
    unfold BΣ_lid.
    refine (natural_path_BΣ_l _ @ _).
    unfold BΣ_assoc.
    refine (_ @ (path_BΣ_compose _ _)^).
    apply (ap path_BΣ).
    apply path_equiv. apply path_arrow.
    intros [[[] | s1] | s2]; reflexivity.
  Qed.

  Definition BΣ_triangle2 : coherence_triangle2 BΣ_assoc BΣ_lid BΣ_rid.
  Proof.
    intros S1 S2. unfold BΣ_rid. unfold BΣ_assoc. unfold BΣ_lid. simpl.
    refine (natural_path_BΣ_l _ @ _).
    refine (_ @ whiskerL _ (natural_path_BΣ_r _)^).
    refine (_ @ (path_BΣ_compose  _ _)^).
    apply (ap path_BΣ).
    apply path_equiv. apply path_arrow.
    intros [[s1 | []] | s2]; reflexivity.
  Qed.
  
  Definition BΣ_pentagon : coherence_pentagon BΣ_assoc.
  Proof.
    intros S1 S2 S3 S4.
    refine (natural_path_BΣ_l _  @ _).
    apply moveL_pV.
    refine (path_BΣ_compose _ _ @ _).
    apply moveL_pV.
    refine (whiskerL _ (natural_path_BΣ_r _) @ _).
    refine (path_BΣ_compose _ _ @ _).
    refine (_ @ (path_BΣ_compose _ _)^).
    apply (ap path_BΣ).
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
      refine ((path_sum (inl (f1 a)) (inl (f1' a)))^-1 (p' (inl a))).
      apply (@isequiv_path_sum B1 B2 (inl (f1 a)) (inl (f1' a))).
    - apply path_arrow. intro a.
      refine ((path_sum (inr (f2 a)) (inr (f2' a)))^-1 (p' (inr a))).
      apply (@isequiv_path_sum B1 B2 (inr (f2 a)) (inr (f2' a))).
  Defined.

  Definition isinj_equiv_functor_sum_r {A1 A2 B : Type} (e1 e2 : A1 <~> A2) :
    equiv_functor_sum_r (B := B) e1 = equiv_functor_sum_r e2 -> e1 = e2.
  Proof.
    intro p. apply path_equiv.
    refine (fst ((isinj_functor_sum e1 e2 idmap idmap) _)).
    apply (path_equiv^-1 p).
  Defined.    
  
  Definition BΣ_lcancel (S1 S2 : BΣ) (p q : S1 = S2) (T : BΣ) :
    ap (fun x => x ⊕ T) p = ap (fun x => x ⊕ T) q -> p = q.
  Proof.
    intro h.
    apply (equiv_inj (@path_BΣ S1 S2)^-1).
    apply (isinj_equiv_functor_sum_r (B:=T) (path_BΣ^-1 p) (path_BΣ^-1 q)) .
    apply (equiv_inj (@path_BΣ (S1 ⊕ T) (S2 ⊕ T))).
    refine ((natural_path_BΣ_l _)^ @ _ @ natural_path_BΣ_l _).
    refine (_ @ h @ _);
      apply (ap (ap (fun x : BΣ => x ⊕ T))).
      - apply eisretr.
      - apply inverse. apply eisretr.
  Defined.

  Definition BΣ_moncat : Monoidal_1Type :=
    Build_Monoidal_1Type (BuildTruncType 1 BΣ) plus_BΣ (canon_BΣ 0) BΣ_assoc BΣ_lid BΣ_rid BΣ_triangle1 BΣ_triangle2 BΣ_pentagon.

  Definition group_completion_BΣ := group_completion BΣ_moncat BΣ_lcancel .


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

  Definition univalent_group_completion_BΣ :
    IsCategory group_completion_BΣ.
  Proof.
    apply univalent_monactcat; simpl.
    - intros A B.
      intro p.
      apply path_BΣ. simpl.
      apply (sum_empty_is_empty A B).
      apply ((path_BΣ)^-1 p).
    - intro A.
      apply (trunc_equiv' (Empty <~> A)).
      apply (path_BΣ (S := (canon_BΣ 0))).
      apply (trunc_equiv' (A <~> Empty)).
      apply equiv_equiv_inverse.
      exact _.
  Qed.

  
       
      

  
    
  
End BΣ.
