Require Import HoTT.
Load pType_basics.

(*The main result in this file is the fact that S^n->*A <~> loops n A.
I also use this to construct a map between homotopy groups from a map between spheres.
Lastly I (assuming the Hopf map) construct a map pi_(n+1) A ->* pi_n A. *)


(*Show that precomposing with a pointed equivalence induces an equivalence. *) (*TODO: do also with postcompose. . .*)
Section Precompose_pointed_equivalence.

	Definition pointed_precompose {A B C:pType} (f:A->*B) : 
		(B->*C) -> (A->*C)
		:= fun g => g o* f.
	Definition pt_precomose_inv {A B C:pType} (f : A<~>*B) :
		(A->*C) -> (B->*C)
		:= pointed_precompose (pequiv_inverse f).
	
 	Lemma eissect_pt {A B: pType} (f:A<~>*B) : 
 		pequiv_inverse f o* f ==* pmap_idmap A.
 		Proof.
 		rapply (@Build_pHomotopy A A).
				+exact (eissect f).
				+unfold point_eq. cbn.
				unfold moveR_equiv_V.
				rewrite <- (point_eq f).
				hott_simpl.
	Qed.
	
 	Lemma eisretr_pt {A B: pType} (f:A<~>*B) : 
 		f o* pequiv_inverse f ==* pmap_idmap B.
 		Proof.
 		rapply (@Build_pHomotopy B B).
				+exact (eisretr f).
				+unfold point_eq. cbn.
				unfold moveR_equiv_V.
				rewrite <- (point_eq f).
				rewrite eisadj.
				hott_simpl.
	Qed.
	
	Lemma isequiv_pt_precomose `{Funext} {A B C:pType} (f : A<~>*B)  : 
		IsEquiv (@pointed_precompose A B C f).
		Proof.
		rapply (isequiv_adjointify (@pointed_precompose A B C f) (pt_precomose_inv f)).
		-(*Right inverse*)
		intro g.
		apply path_pmap.
		phomotopy_via (g o* ( (pequiv_inverse f) o* f)).
			apply pmap_compose_assoc.
		phomotopy_via (g o* (pmap_idmap _)).
			apply pmap_postwhisker.
			apply eissect_pt.
		apply pmap_precompose_idmap.
		-(*Left inverse*)
		intro g.
		apply path_pmap.
		phomotopy_via (g o* (f o* pequiv_inverse f)).
			apply pmap_compose_assoc.
		phomotopy_via (g o* (pmap_idmap _)).
			apply pmap_postwhisker.
			apply eisretr_pt.
		apply pmap_precompose_idmap.
	Defined.
End Precompose_pointed_equivalence.


(*Prove that addpoint:Type->pType, and the forgetful functor pType->Type are adjoint. This is lemma 6.5.3 in the book.*)
Section Addpoint_forgetful_adjointness.
	(*Get a map from the pointed map by forgetting the extra point.*)
	Definition pMap_to_Map {A:Type } {B:pType} : 
	( (add_pt A) ->* B  ) -> ( A -> (pointed_type B) ) := fun f => f o inl.
	
	(*To go the other way, just let the extra point get mapped to point B.*)
	Definition Map_to_pMap {A:Type } {B:pType} : ( A->(pointed_type B) ) -> ( (add_pt A) ->* B  ).
		intro f.
		rapply Build_pMap.
			-intros [a | [] ].
				*exact (f a).
				*exact (point B).
			-exact idpath.
	Defined.
	
	Lemma isequiv_pMap_to_Map {A:Type } {B:pType} `{Funext} : 
	IsEquiv (@pMap_to_Map A B).
	Proof.
		apply (@isequiv_adjointify ((add_pt A)->*B) (A->B) pMap_to_Map Map_to_pMap).
			-exact (fun _ => idpath).
			-	intros [pf pe]. cbn in pe.
			unfold pMap_to_Map; unfold Map_to_pMap.
			apply path_pmap.
			rapply (@Build_pHomotopy (add_pt A) B).
				+(*Homotopy*) (*cbn. (*Makes it easier to read*)*)
				intros [a|[]].
					exact idpath.
					exact pe^.
				+cbn. hott_simpl.
	Qed.
	
	
	(*Lemma 6_5_3 in book:*)
	Lemma addpt_forget_adjoint `{Funext} (A:Type) (B:pType) : 
		( (add_pt A) ->* B  ) <~> ( A -> (pointed_type B) ).
	Proof.
		exact (BuildEquiv _ _ pMap_to_Map isequiv_pMap_to_Map).
	Qed.
End Addpoint_forgetful_adjointness.


(*Show that my two-pointed types are equivalent*)
Section Two_points.
	Definition two_pts := add_pt Unit. (*TODO: Sphere 0 instead of pBool. . .*)
	
	Definition sph0_to_two_pts : (pSphere 0) ->* two_pts.
		refine (Build_pMap _ _ _ _).
			(*Construct map*)
			-apply (Susp_rec (inr tt) (inl tt)).
				+intros [].
			-exact idpath.
	Defined.
	
	Definition two_pts_to_sph0 : two_pts -> (pSphere 0).
		intros [].
			-exact (Unit_rec (pSphere 0) South).
			-exact (Unit_rec (pSphere 0) North).
	Defined.
	
	Definition isretr_sph_to_2 : Sect two_pts_to_sph0 sph0_to_two_pts.
		intros [ [] | [] ] ; exact idpath.
	Defined.
	
	Definition issect_sph_to_2 : Sect sph0_to_two_pts two_pts_to_sph0.
		refine (Susp_ind _ idpath idpath _).
		intros [].
	Defined.
	
	Lemma isequiv_sph0_to_two_pts : IsEquiv sph0_to_two_pts.
		apply (isequiv_adjointify sph0_to_two_pts two_pts_to_sph0).
			-exact isretr_sph_to_2.
			-exact issect_sph_to_2.
	Qed.
	
	Definition equiv_sph0_to_two_pts := 
		Build_pEquiv _ _ sph0_to_two_pts  isequiv_sph0_to_two_pts.
	
	Lemma equiv_twotoA_A `{Funext} {A:pType} : A <~> (two_pts ->* A).
		equiv_via (Unit->A).
			-rapply BuildEquiv.
				+exact (Unit_rec A).
				+exact (isequiv_unit_rec A).
			-exact ( (addpt_forget_adjoint Unit A)^-1 ).
	Qed.
End Two_points.


Section Loops.
	(*Define Omega n A as pointed maps from the n-sphere*)
	Definition Omega (n:nat) (A:pType) :pType :=
		Build_pType (pMap (pSphere n) A) _.
		

	Lemma equiv_A_omegaA `{Funext} {A:pType} : A <~> Omega 0 A.
			equiv_via (two_pts ->* A).
				-exact equiv_twotoA_A.
				-rapply BuildEquiv.
					+apply pointed_precompose.
					exact sph0_to_two_pts.
					+exact (isequiv_pt_precomose equiv_sph0_to_two_pts).
	Defined.

	Theorem omega_loops_equiv `{Funext} : forall n:nat, forall A:pType,
		iterated_loops n A  <~>  Omega n A.
		induction n.
			-intro A. exact equiv_A_omegaA.
			-intro A.
			equiv_via (pSphere n ->* loops A).
				+exact (IHn (loops A) ).
				+exact (loop_susp_adjoint _ _)^-1.
	Qed.
End Loops.

Section homotopy_groups.
	Definition homotopy_group (n:nat) (A:pType) : pType :=
		pTr 0 (Omega n A).

	Local Notation pi := homotopy_group.

	Definition SphereToOmega_functor {m n:nat} (f:pSphere m ->* pSphere n) (A:pType) :
		Omega n A ->* Omega m A.
		rapply Build_pMap.
		(*Define the map*)
		* intro h. exact (h o* f).
		(*Prove that it is pointed map.*)
		* apply const_comp.
	Defined.

	Definition OmegaToHtGr_functor {m n : nat} {A:pType} (f : Omega n A ->* Omega m A) :
		pi n A ->* pi m A.
		
		rapply Build_pMap.
		(*Construct map*)
		*apply Trunc_rec.
		intro loop.
		apply tr.
		exact (f loop).
		(*Show that it is pointed.*)
		*apply (ap tr).
		rewrite (point_eq f).
		reflexivity.
	Defined.

	Definition SphereToHtGr_functor {m n : nat} (f:pSphere m ->* pSphere n) (A:pType) :
		pi n A ->* pi m A :=
			OmegaToHtGr_functor (SphereToOmega_functor f A).
		
	End homotopy_groups.

Section Hopf.
	Local Notation pi := homotopy_group.
	Definition Hopf : pSphere 3 ->* pSphere 2.
		Admitted.
	
	Definition Hopf_induced (n:nat){A:pType}: 
		pi (n+2) A ->* pi (n+3) A 
		:=
		SphereToHtGr_functor (natural_sphere n Hopf) A.
		
End Hopf.
