Require Import HoTT.
Local Open Scope pointed_scope.

Ltac pHomotopy_via mid := apply (phomotopy_compose (g := mid)).

Ltac path_via mid := apply (concat (y:=mid)).


Section pType_prelim.
  
  (*Make pointed variant of equiv_inv.*)
  (*Move to pointed.v*)
  Definition pequiv_inv {A B : pType} (f: A->*B) {feq : IsEquiv f} :=
    pequiv_inverse (Build_pEquiv _ _ f feq).

  (*The constant map between ptypes.*)
  (*Mt pointed.v*)
  Definition pconst (A B: pType) : pMap A B := 
	Build_pMap A B (const (point B)) idpath.

  (*The constant map is base point for the type pMap A B*)
  (*Mt pointed.v*)
  Global Instance ispointed_pmap {A B:pType} : IsPointed (pMap A B) := 	pconst A B.
  
  (*Define the pointed sphere. 
	The basepoint is North.
    Should be able to define instance of ispointed_sphere instead, but that is not true for n=-1,-2*)
  (*Move to HIT/Sphere*)
  Fixpoint pSphere (n:nat) : pType := 
	match n with
	  |O => Build_pType (Sphere O) _
	  |S n => psusp (pSphere n)
	end.

  (*TODO*)
  (*Move to HIT/Sphere*)
(*  Open Scope trunc_scope.
  Notation "a + b" := (trunc_index_add a b) : trunc_scope.
  Definition trunc_add_sym : forall a b : trunc_index, a + b = b + a.
    apply (trunc_index_ind (fun a => forall b : trunc_index, a + b = b + a)).
    apply trunc_index_ind.
    - exact idpath.
    - intro t.
      intro p.
      simpl. (*Whut?*)
    intros a b. induction a.
  
  Lemma minustwo_plus_two : forall n : nat, -2 + n + 2 = n.
  Proof.
    intro n.
    refine (concat (y := n - 2 + 2) _ _).
    - apply (ap (fun m => m + 2)).
      induction n.
      + exact idpath.
      + 
    
    
    
    induction n.
    - refine (concat (y := -2 + 2)
    (*Todo*)
  Lemma pointed_Sphere : forall n : nat, IsPointed (Sphere n).
    Abort.
*)
  (*The functor from Type to pType*)
  (*Mt pointed.v?*)
  Definition add_pt (A:Type) :  pType := Build_pType (A+Unit) (inr tt).

  (*Is this needed?*)
  Global Instance ispointed_unit : IsPointed Unit := tt.

  (*Postcomposing with pconst is pconst.*)
  (*Mt pointed.v*)
  Lemma pmap_postcompose_const (A B C: pType) (f:A->*B) : 
	pconst B C o* f = pconst A C.
  Proof.
    unfold pconst.
	unfold pmap_compose ; simpl.
	unfold const.
	rewrite ap_const; simpl.
	reflexivity.
  Qed.

  (*Sphere as a functor nat -> Type is natural*)
  (*Mt HIT/Sphere*)
  Definition natural_sphere {m n:nat} (k:nat) (f:pSphere m->*pSphere n) :
	pSphere (k+m) ->* pSphere (k+n).
	induction k.
	-exact f.
	-exact (psusp_functor IHk).
  Defined.
End pType_prelim.

Section Nat_and_truncindex.
  Local Open Scope trunc_scope.
  Set Printing Coercions.

  Fixpoint plustwo (t : trunc_index) : nat :=
    match t with
      | -2 => O
      | t.+1 => S (plustwo t)
    end.
  
  Definition truncind_to_twoplusnat (t : trunc_index) : Unit + Unit + nat :=
    match t with
      | -2 => (inl (inl tt))
      | -1 => (inl (inr tt))
      | t.+2 => (inr (plustwo t))
    end.

  Definition twoplusnat_to_truncind (x : Unit + Unit + nat) : trunc_index :=
    match x with
      | (inl (inl tt) ) => -2
      | (inl (inr tt) ) => -1
      | (inr n) => nat_to_trunc_index n
    end.

  Lemma plustwo_commute1 : forall t : trunc_index,   nat_to_trunc_index (plustwo t) = t.+2.
    apply trunc_index_rect.
    - exact idpath.
    - intros t IHt.
      simpl.
      exact (ap trunc_S IHt).
  Defined.

  Lemma plustwo_commute2 : forall n : nat, plustwo (nat_to_trunc_index n) = (n.+2)%nat.
    induction n.
    - exact idpath.
    - simpl.
      exact (ap S IHn).
  Defined.
      
  Lemma equiv_twoplusnat_truncind : Equiv (Unit + Unit + nat) trunc_index.
    apply (equiv_adjointify twoplusnat_to_truncind truncind_to_twoplusnat).
    - intro t.
      destruct t.
      + exact idpath.
      + destruct t.
        exact idpath.
        exact (plustwo_commute1 t).        
    - intro x.
      destruct x.
      + destruct s.
        * destruct u. exact idpath.
        * destruct u. exact idpath.
      + unfold truncind_to_twoplusnat.
        unfold twoplusnat_to_truncind.
        destruct n.
        * exact idpath.
        * destruct n.
          exact idpath.
          simpl.
          apply (ap inr).
          exact (plustwo_commute2 n).
  Defined.

  Lemma natisplustwo (n:nat) : { t:trunc_index |  nat_to_trunc_index n = t.+2}.
    induction n.
    - exact (minus_two; idpath). 
    - exact ((pr1 IHn).+1; ap trunc_S (pr2 IHn)). 
  Defined.
  
  Lemma ispointed_sphere (n : nat) : IsPointed (Sphere n).
    unfold IsPointed.
    rewrite (natisplustwo n).2.
    exact North.
  Qed.
  
  (*Global Instance ispointed_sphere (n:nat) : IsPointed (Sphere n) := 
    transport Sphere (pr2 (natisplustwo n))^ North.
*)
  Definition pSphere2 (n:nat) := Build_pType (Sphere n) (ispointed_sphere n).
(*
  Definition sph_to_sph2 (n:nat) : pSphere n ->* pSphere2 n.
    refine (Build_pMap _ _ _ _).
    - induction n.
      + exact idmap.
      + refine (Susp_rec _ _ _).
        unfold pSphere2.
        induction n.
        * exact idmap.
        * refine (Susp_rec North South _). exact (merid o IHn).
    - induction n.
        exact idpath.
      induction n.
        exact idpath.
      simpl.
      clear IHn0.
      
      unfold point. unfold ispointed_sphere. simpl.
      induction n.
        exact idpath.
      simpl.
      cbn.
      change ((natisplustwo n.+2).2) with 

      simpl.  unfold natisplustwo. simpl.
      unfold point in IHn. simpl in IHn. unfold ispointed_sphere in IHn. unfold ispointed_susp in IHn. simpl in IHn.
      simpl in IHn. unfold point in IHn.
  Admitted.
  

*) 