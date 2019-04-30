Require Import HoTT.
Require Import finite_lemmas.

Require Import group_complete_1type.
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
  Definition canon_BΣ (n : nat) : BΣ := (n; canon n).

  Lemma finite_types_eqcard {m n : nat} (A : Finite_Types m) (B : Finite_Types n) :
    A <~> B -> m = n.
  Proof.
    destruct A as [A fA]. destruct B as [B fB]. simpl. intro e.
    strip_truncations.
    apply nat_eq_fin_equiv.
    exact (fB oE e oE (equiv_inverse fA)).
  Qed.

  (* in finite_lemmas: *)
  (* (* Describing the path type of BΣ *) *)
  Definition path_BΣ {A B : BΣ} : A <~> B <~> A = B
       := path_finite_types A B.
  (* Proof. *)
  (*   destruct A as [m A]. destruct B as [n B]. simpl. *)
  (*   intro e. *)
  (*   destruct (finite_types_eqcard A B e). *)
  (*   apply (path_sigma (fun m : nat => Finite_Types m) (m; A) (m;B) idpath). simpl. *)
  (*   apply path_finite_types_fix. *)
  (*   exact e. *)
  (* Defined. *)
    
 

  (* Definition isequiv_path_BΣ {A B : BΣ} : IsEquiv (@path_BΣ A B). *)
  (* Proof. *)
  (*   srapply @isequiv_adjointify. *)
  (*   - intros []. exact equiv_idmap. *)
  (*   - intros []. *)
  (*     unfold path_BΣ. *)
  (*     assert (H : (finite_types_eqcard (pr2 A) (pr2 A) equiv_idmap) = idpath). *)
  (*     { apply hset_nat. } destruct H. *)
  (*     destruct . *)

  (* (* path_BΣ respects composition *) *)
  (* shorter proof than in finite_lemmas *)
  Definition path_BΣ_compose {A B C : BΣ} (e1 : A <~> B) (e2 : B <~> C) :
    path_BΣ (e2 oE e1) = path_BΣ e1 @ path_BΣ e2.
  Proof.
    (* path_BΣ e2 @ path_BΣ e1 = path_BΣ (e1 oE e2). *)
  Proof.
    refine
      (ap011 (fun g1 g2 => path_BΣ (g2 oE g1))
             (eissect (@path_BΣ A B) e1)^ (eissect (@path_BΣ B C) e2)^ @ _).
    generalize (path_BΣ e2). intros []. 
    generalize (path_BΣ e1). intros []. simpl.
    refine (path_finite_types_1 A).
  Qed.
  (* Proof. *)
  (*   apply (equiv_inj path_BΣ^-1). *)
  (*   refine (_ @ (eissect (path_BΣ) (e1 oE e2))^). *)
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
    Finite_Types (m + n).
  Proof.
    exists (A + B).
    destruct A as [A fA]. destruct B as [B fB]. strip_truncations.
    apply tr. simpl.
    refine (_ oE equiv_functor_sum' fA fB).
    apply equiv_inverse.
    apply Fin_resp_sum.
  Defined.
    
  
  Definition plus_BΣ : BΣ -> BΣ -> BΣ.
  Proof.
    intros [m A] [n B].
    exists (m + n)%nat.
    exact (sum_finite_types A B).
  Defined.

  Definition BΣ_id : BΣ := canon_BΣ 0.

  Local Notation "S1 ⊕ S2" := (plus_BΣ S1 S2) (at level 50, no associativity).  

  (* path_BΣ behaves well with respect to sum *)
  Definition natural_path_BΣ_l {S1 S2 S3: BΣ} (e : S1 <~> S2) :
    ap (fun x : BΣ => x ⊕ S3) (path_BΣ e) = path_BΣ (A := S1 ⊕ S3) (B := S2 ⊕ S3) (equiv_functor_sum_r (B := S3) e).
  Proof.
    
    refine (_ @ ap (fun e' => @path_BΣ (S1⊕ S3) (S2 ⊕ S3) (equiv_functor_sum_r e'))
              (eissect (@path_BΣ S1 S2) e)).
    generalize (path_BΣ e). intros [].
    simpl. unfold path_BΣ. apply inverse.
    refine (_ @ path_finite_types_1 (S1 ⊕ S3)).
    apply (ap (path_finite_types (S1 ⊕ S3) (S1 ⊕ S3))).
    apply path_equiv. apply path_arrow. intros [s1 | s3]; reflexivity.
  Qed.

  Definition natural_path_BΣ_r {S1 S2 S3: BΣ} (e : S2 <~> S3) :
    ap (fun x : BΣ => S1 ⊕ x) (path_BΣ e) = path_BΣ (A := S1 ⊕ S2) (B := S1 ⊕ S3) (equiv_functor_sum_l (A := S1) e).
  Proof.
    refine (_ @ ap (fun e' => @path_BΣ (S1 ⊕ S2) (S1 ⊕ S3) (equiv_functor_sum_l e'))
              (eissect (@path_BΣ S2 S3) e)).
    generalize (path_BΣ e). intros [].
    simpl. unfold path_BΣ. apply inverse.
    refine (_ @ path_finite_types_1 (S1 ⊕ S2)).
    apply (ap (path_finite_types (S1 ⊕ S2) (S1 ⊕ S2))).
    apply path_equiv. apply path_arrow. intros [s1 | s2]; reflexivity.
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
    refine (_ @ (path_BΣ_compose _ _)).
    apply (ap path_BΣ).
    apply path_equiv. apply path_arrow.
    intros [[[] | s1] | s2]; reflexivity.
  Qed.

  Definition BΣ_triangle2 : coherence_triangle2 BΣ_assoc BΣ_lid BΣ_rid.
  Proof.
    intros S1 S2. unfold BΣ_rid. unfold BΣ_assoc. unfold BΣ_lid. simpl.
    refine (natural_path_BΣ_l _ @ _).
    refine (_ @ whiskerL _ (natural_path_BΣ_r _)^).
    refine (_ @ (path_BΣ_compose  _ _)).
    apply (ap path_BΣ).
    apply path_equiv. apply path_arrow.
    intros [[s1 | []] | s2]; reflexivity.
  Qed.
  
  Definition BΣ_pentagon : coherence_pentagon BΣ_assoc.
  Proof.
    intros S1 S2 S3 S4.
    refine (natural_path_BΣ_l _  @ _).
    apply moveL_pV.
    refine ((path_BΣ_compose _ _)^ @ _).
    apply moveL_pV.
    refine (whiskerL _ (natural_path_BΣ_r _) @ _).
    refine ((path_BΣ_compose _ _)^ @ _).
    refine (_ @ (path_BΣ_compose _ _)).
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
    Categories.IsCategory group_completion_BΣ.
  Proof.
    apply univalent_monactcat; simpl.
    - intros A B.
      intro p.
      apply path_BΣ. simpl.
      apply (sum_empty_is_empty A B).
      apply ((path_BΣ)^-1 p).
    - intro A.
      apply (trunc_equiv' (Empty <~> A)).
      + apply (path_BΣ (A := (canon_BΣ 0))).
      + apply (trunc_equiv' (A <~> Empty)).
        * apply equiv_equiv_inverse.
        * exact _.
  Qed.

  
       
      

  
    
  
End BΣ.

Require Import delooping.
(* Section deloop_BΣ. *)
(*   Definition finite_types_ind_1type (m : nat) *)
(*              (P : Finite_Types m -> 1-Type) *)
(*              (p0 : P (canon m)) *)
(*              (f : forall (e : canon m <~> canon m), *)
(*                  transport P (path_finite_types_fix m _ _ e) p0 = p0) *)
(*              (* (ishom_f : *) *)
(*              (*    forall (e g : canon m <~> canon m), *) *)
(*              (*      f (g oE e) = transport_pp P *) *)
(*              (*                                (path_finite_types_fix m _ _ e) *) *)
(*              (*                                (path_finite_types_fix m _ _ g) *) *)
(*   : forall x : Finite_Types m, P x. *)
(*   Proof. *)
(*     srefine (deloop_ind (Finite_Types m) (canon m) _ P p0 _ _).  *)
(*     - intros [A fA]. strip_truncations. *)
(*       apply tr. apply inverse. *)
(*       apply path_finite_types_fix. exact fA. *)
(*     - intro ω. *)
(*       refine (_ @ f ((path_finite_types_fix m (canon m) (canon m))^-1 ω)). *)
(*       apply (ap (fun x => *)
(*                transport P x p0)). *)
(*       apply inverse. apply eisretr. *)
(*     - intros. hnf. *)
(*       repeat rewrite concat_1p. *)
  
(*   (* TODO *) *)
(* End deloop_BΣ. *)

Add Rec LoadPath "~/groupoids" as GR.
Require Import cquot.
Require Import cquot_principles.


Definition tr1_group_completion_BΣ := cquot (group_completion_BΣ).

Lemma isconn_finite_types (m : nat) :
  forall x : Finite_Types m,
    merely (canon m = x).
Proof.
  intros [A fA]. strip_truncations.
  apply tr. apply inverse. apply path_finite_types_fix.
  exact fA.
Qed.

Definition grp_compl_BΣ_ind_set
           (P : tr1_group_completion_BΣ -> hSet)
           (f : forall (m n : nat), P (ccl group_completion_BΣ ((canon_BΣ m), (canon_BΣ n))))
           : forall z : tr1_group_completion_BΣ, P z.
  Proof.
    srapply @cquot_ind_set. 
    - simpl.
      intros [[m x] [n y]]. revert x y.
      srefine (deloop_double_ind_set
               (Finite_Types m) (canon m) (isconn_finite_types m)
               (Finite_Types n) (canon n) (isconn_finite_types n)
               _
               (f m n)
               _ _
               
             ).
      + admit.
      + admit.
    - simpl. unfold monoidal_action_morphism.
      intros [[m a1] [n a2]] b [s p].  destruct p. simpl.
      revert a2.
      srefine (deloop_ind_prop
               (Finite_Types n) (canon n) (isconn_finite_types n)
               _ _).
      revert a1.
      srefine (deloop_ind_prop
               (Finite_Types m) (canon m) (isconn_finite_types m)
               _ _).
      destruct s as [s x]. revert x.
      srefine (deloop_ind_prop
               (Finite_Types s) (canon s) (isconn_finite_types s)
               _ _).
      simpl.
      
      admit.
    
    
    
  
