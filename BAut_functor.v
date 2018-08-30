Require Import HoTT.
Require Import UnivalenceAxiom.
Load finite.



Section Generalized_Sphere.
  (* Want a map Type -> Type sending canon n to the n-sphere *)
  (* I.e. a generalization of the sphere to all types *)
  (* What we need is that all these contain North and South, and then a map gSphere A -> North (A+Unit) = South (A+Unit) *)

  (* gSphere is for generalized_sphere *)
  Private Inductive gSphere : Type -> Type :=
  |gNorth (A : Type) : gSphere (A)
  |gSouth (A : Type) : gSphere (A)
  .

  Axiom gMerid : forall A : Type, gSphere A ->  gNorth (A + Unit) = gSouth (A + Unit).

  Definition gSphere_ind (P : forall A : Type, gSphere A -> Type)
             (H_N : forall A : Type, P A (gNorth A))
             (H_S : forall A : Type, P A (gSouth A))
             (H_merid : forall (A : Type) (x : gSphere A), transport (P (A + Unit)) (gMerid A x) (H_N (A + Unit)) = H_S (A + Unit))
    : forall (A : Type) (x : gSphere A), P A x.
  Proof.
    intros A x. destruct x. exact (H_N A). exact (H_S A).
  Defined.

  Axiom gSphere_ind_beta_merid : forall (P : forall A : Type, gSphere A -> Type)
                                        (H_N : forall A : Type, P A (gNorth A))
                                        (H_S : forall A : Type, P A (gSouth A))
                                        (H_merid : forall (A : Type) (x : gSphere A), transport (P (A + Unit)) (gMerid A x) (H_N (A + Unit)) = H_S (A + Unit))
                                        (A : Type) (x : gSphere A),
      apD (gSphere_ind P H_N H_S H_merid (A+Unit)) (gMerid A x) = H_merid A x. 

End Generalized_Sphere.

Definition gSphere_rec (P : forall A : Type, Type)
           (H_N : forall A : Type, P A)
           (H_S : forall A : Type, P A)
           (H_merid : forall A : Type, gSphere A -> H_N (A + Unit) = H_S (A + Unit))
  : forall A : Type, gSphere A -> P A.
Proof.
  apply (gSphere_ind (fun A _ => P A) H_N H_S).
  intros A x.
  exact (transport_const _ _ @ H_merid A x).
Defined.

Definition gSphere_rec_beta_merid (P : forall A : Type, Type)
           (H_N : forall A : Type, P A)
           (H_S : forall A : Type, P A)
           (H_merid : forall A : Type, gSphere A -> H_N (A + Unit) = H_S (A + Unit))
           (A : Type) (x : gSphere A)
  : ap (gSphere_rec P H_N H_S H_merid (A+Unit)) (gMerid A x) = H_merid A x.
Proof.
  apply (cancelL (transport_const (gMerid A x) (H_N (A + Unit)))).
  transitivity (apD (gSphere_rec P H_N H_S H_merid (A + Unit)) (gMerid A x)).
  symmetry; refine (apD_const (gSphere_rec P H_N H_S H_merid (A + Unit)) _).
  refine (gSphere_ind_beta_merid (fun A _  => P A) _ _ _ _ _).
Defined.

Definition gSphere_to_pSphere (A : Type) (n : nat) (e : A <~> Fin n) : gSphere A -> pSphere n.
Proof.
  revert A e.
  induction n.
  - intros A e x. revert A x e.
    srapply @gSphere_rec; cbn.
    intros. exact (inl tt). intros. exact (inr tt).
    cbn. intros. apply path_arrow. intro e. apply Empty_rec. exact (e (inr tt)).
  - intro A. intros e x. revert A x n e IHn.
    srapply @gSphere_rec; cbn.
    intros. exact North.
    intros. exact South.
    intros A x. cbn. apply path_forall. intro n. apply path_forall. intro e. apply path_forall. intro H.
    apply merid. apply (H A). exact (equiv_restrict e). exact x.
Defined.

  
(*   intro x. revert A x n e. *)
(*   srapply (@gSphere_rec (fun A => forall n : nat, A <~> Fin n -> pSphere n)); cbn.  *)
(*   - intros A n e. *)
(*     destruct n. exact (inl tt). exact North. *)
(*   -  intros A n e. *)
(*      destruct n. exact (inr tt). exact South. *)
(*   - cbn.  *)
(*     intro A. intro x. apply path_forall. intro n. apply path_forall. intro e. revert e. *)
(*     revert x. revert A. *)
(*     destruct n. *)
(*     { intros. apply Empty_rec. exact (e (inr tt)).  } (* Do away with base case *) *)
(*     intros. *)
(*     apply merid. *)
(*     refine (gSphere_to_pSphere A n _ x). *)
(*     exact (equiv_restrict e). *)
(* Defined. *)

(* (* Have to prove that this respects the beta rule *) *)
(* Definition gSphere_to_pSphere_beta_merid (A : Type) (n : nat) (e : A + Unit <~> Fin n.+1) (x : gSphere A) : *)
(*   ap (gSphere_to_pSphere (A + Unit) n.+1 e) (gMerid A x) = merid (gSphere_to_pSphere A n (equiv_restrict e) x). *)
(* Proof. *)
(*   revert n e. *)
(*   revert A x. srapply @gSphere_ind. *)
(*   intros. cbn. intros. *)
(*   refine (_ @ gSphere_rec_beta_merid *)
(*   rewrite (gSphere_rec_beta_merid). *)

Definition pSphere_to_gSphere (* (A : Type) *) (n : nat) (* (e : A <~> Fin n) *) : pSphere n -> gSphere (Fin n).
Proof.
  (* intro x. apply (transport gSphere (path_universe e)^). revert x. clear e. clear A. *)
  induction n.
  - intros [[]|[]]. exact (gNorth _). exact (gSouth _).
  - srapply @Susp_rec.
    exact (gNorth _). exact (gSouth _).
    intro x. apply gMerid. apply IHn. exact x.
Defined.

Definition gSphere_finite_equal_sphere : forall (* (A : Type) *) (n : nat) (* (e : A <~> Fin n) *), gSphere (Fin n) <~> pSphere n.
Proof.
  (* induction n. *)
  (* - intro e. *)
  (*   destruct (path_universe e)^. *)
  (*   srapply @equiv_adjointify. *)
  (*   + intro x. induction x. *)
  (*     { exact (inl tt). } {exact (inr tt). } *)
  intros.
  - srapply @equiv_adjointify.
    apply (gSphere_to_pSphere (Fin n) n equiv_idmap).
    apply (pSphere_to_gSphere n).
    +  unfold Sect.
       induction n.
       { intros [[]|[]]; reflexivity. }
       srapply @Susp_ind.
       * cbn. reflexivity.
       * cbn. reflexivity.
       * intro x.
         refine (transport_paths_FlFr (f := (fun y : Susp (pSphere n) => gSphere_to_pSphere (Fin n.+1) n.+1 1 (pSphere_to_gSphere n.+1 y)))
                                      (merid x) idpath @ _).
         rewrite ap_idmap. rewrite concat_p1.
         apply moveR_Vp. rewrite concat_p1. apply inverse.
         rewrite (ap_compose (pSphere_to_gSphere n.+1) (gSphere_to_pSphere (Fin n.+1) (n.+1) equiv_idmap)).
         rewrite Susp_rec_beta_merid.
         change  with (Fin n).
         
         cbn. simpl.
         rewrite gSphere_rec_beta_merid.
         
         
         
         
         cbn.
         
         (* Must define gSphere differently so that gSphere_to_pSphere is only by induction? *)
         
         
.
         
    + 

       
    
    + intro x. revert e. revert n. revert x. revert A.
      srapply (@gSphere_rec (fun A => forall n : nat, A <~> Fin n -> pSphere n)); cbn. 
      * intros A n e.
        destruct n. exact (inl tt). exact North.
      * intros A n e.
        destruct n. exact (inr tt). exact South.
      * cbn. 
        intro A. intro x. apply path_forall. intro n. apply path_forall. intro e.
        revert e. revert x. revert A.
        destruct n.
        { intros. apply Empty_rec. apply e. exact (inr tt). } (* Do away with base case *)
        intros.
        apply merid. 
        
        

        cbn. apply path_arrow. intro e.
        induction n.
      
      * intros n e. destruct n.
        exact (inl tt). exact North.
      * intros n e. destruct n.
        { exact (inr tt). } exact South.
    + revert A e. induction n.
      intros A e [_ |_ ]. exact (north A). exact (south A).
      intros A e.
      srapply @Susp_rec.
      * exact (north A).
      * exact (south A).
      * intro x.
        rewrite (path_universe e).
        apply merid'.
        apply IHn. apply equiv_idmap. exact x.
    + unfold Sect.
      destruct n.
      { cbn. intros [[]|[]]; reflexivity. }
      srapply @Susp_ind; try reflexivity.
      * cbn. 
      


        destruct (fin_empty n e^-1)^. exact (inr tt).
      * intros n e. 
        cut (exists m : nat, n = m.+1%nat).
        { intros [m p]. rewrite p. rewrite p in e. clear p.
          north A x
          
          apply (IHx m.+1%nat).
          revert x.
          
          