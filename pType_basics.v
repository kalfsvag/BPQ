Require Import HoTT.
Local Open Scope pointed_scope.

Ltac pHomotopy_via mid := apply (phomotopy_compose (g := mid)).

Ltac path_via mid := apply (concat (y:=mid)).


Section pType_prelim.
  
  (*Make pointed variant of equiv_inv.*)
  Definition pequiv_inv {A B : pType} (f: A->*B) {feq : IsEquiv f} :=
    pequiv_inverse (Build_pEquiv _ _ f feq).

  (*The constant map between ptypes.*)
  Definition pconst (A B: pType) : pMap A B := 
	Build_pMap A B (const (point B)) idpath.

  (*The constant map is base point for the type pMap A B*)
  Global Instance ispointed_pmap {A B:pType} : IsPointed (pMap A B) := 	pconst A B.
  
  (*Define the pointed sphere. 
	The basepoint is North.
    Should be able to define instance of ispointed_sphere instead, but that is not true for n=-1,-2*)
  Fixpoint pSphere (n:nat) : pType := 
	match n with
	  |O => Build_pType (Sphere O) _
	  |S n => psusp (pSphere n)
	end.
  

  (*The functor from Type to pType*)
  Definition add_pt (A:Type) :  pType := Build_pType (A+Unit) (inr tt).
  
  Global Instance ispointed_unit : IsPointed Unit := tt.
  
  Lemma const_comp (A B C: pType) (f:A->*B) : 
	pconst B C o* f = pconst A C.
  Proof.
    unfold pconst.
	unfold pmap_compose ; simpl.
	unfold const.
	rewrite ap_const; simpl.
	reflexivity.
  Qed.
  
  Definition natural_sphere {m n:nat} (k:nat) (f:pSphere m->*pSphere n) :
	pSphere (k+m) ->* pSphere (k+n).
	induction k.
	-exact f.
	-exact (psusp_functor IHk).
  Defined.
End pType_prelim.

Section Sphere_vs_pSphere.
  Local Open Scope trunc_scope.
  Lemma natisplustwo (n:nat) : exists t:trunc_index, nat_to_trunc_index n = t.+2.
    induction n.
    - exists minus_two. exact idpath.
    - exists (pr1 IHn).+1.
             exact (ap trunc_S (pr2 IHn)).
  Defined.

  Global Instance ispointed_sphere (n:nat) : IsPointed (Sphere n) := 
    transport Sphere (pr2 (natisplustwo n))^ North.

  Definition pSphere2 (n:nat) := Build_pType (Sphere n) _.

  Definition sph_to_sph2 (n:nat) : pSphere n ->* pSphere2 n.
    refine (Build_pMap _ _ _ _).
    - induction n.
      + exact idmap.
      + induction n.
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
      change ((natisplustwo n.+2).2) with 

      simpl.  unfold natisplustwo. simpl.
      unfold point in IHn. simpl in IHn. unfold ispointed_sphere in IHn. unfold ispointed_susp in IHn. simpl in IHn.
      simpl in IHn. unfold point in IHn.
  Admitted.
  

