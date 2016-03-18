Require Import HoTT.
Load pType_basics.


(*In this section we prove that addpoint and the forgetful functor pType->Type are adjoint. This is lemma 6.5.3 in book.*)
Section Addpoint_forgetful_adjointness.
	Definition pMap_to_Map {A:Type } {B:pType} : ( (add_pt A) ->* B  ) -> ( A -> (pointed_type B) ).
		intro f.
		exact (f o inl).
	Defined.
	
	Definition Map_to_pMap {A:Type } {B:pType} : ( A->(pointed_type B) ) -> ( (add_pt A) ->* B  ).
		intro f.
		refine (Build_pMap _ _ _ _).
			-intros [a | [] ].
				*exact (f a).
				*exact (point B).
			-exact idpath.
	Defined.
	
	Lemma isequiv_pMap_to_Map {A:Type } {B:pType} `{Funext} : IsEquiv (@pMap_to_Map A B).
	Proof.
		apply (@isequiv_adjointify ( (add_pt A) ->* B  ) (A->B) pMap_to_Map Map_to_pMap).
			-exact (fun _ => idpath).
			-intros [pf pe].
			unfold pMap_to_Map; unfold Map_to_pMap.
			pointed_reduce. (*Is this magic?*)
			
			assert (Ht : (fun X : A + Unit =>
               match X with
               | inl a => pf (inl a)
               | inr tt => pf (inr tt)
               end )
               ==
               pf ).
				+intros [ a | [] ];exact idpath.
			+assert (path : (fun X : A + Unit =>
               match X with
               | inl a => pf (inl a)
               | inr tt => pf (inr tt)
               end )
               =
               pf ).
				apply path_forall. exact Ht.
			clear Ht.
			pointed_reduce.
			exact idpath.
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
	        exact (isequiv_adjointify sph0_to_two_pts two_pts_to_sph0 isretr_sph_to_2 issect_sph_to_2).
	Qed.
	

	
	
	Lemma equiv_twotoA_A `{Funext} {A:pType} : A <~> (two_pts ->* A).
		equiv_via (Unit->A).
                        -refine (BuildEquiv _ _ _ _).
				+exact (Unit_rec A).
				+exact (isequiv_unit_rec A).
			
			-exact ( (addpt_forget_adjoint Unit A)^-1 ).
	Qed.
	
(* 	Lemma sph0_is_twopts`{Univalence}  : (pSphere 0) = (two_pts).
		exact (path_universe sph0_to_two_pts).
		Abort. *)
		

			
End Two_points.


Section Loops.
	(*Define Omega n A as pointed maps from the n-sphere*)
	Definition Omega (n:nat) (A:pType) :pType :=
		Build_pType (pMap (pSphere n) A) _.
		
Lemma Omega0_Equiv_A `{Funext} {A:pType} : Omega 0 A <~> A.
		cut ( (pSphere 0 ->* A) <~> (two_pts ->* A) ).
			-intro f.
			equiv_via (two_pts ->* A).
				exact f.
				exact (equiv_twotoA_A)^-1.
			-refine (BuildEquiv _ _ _ _).
				+ (* Construct map. *)
				intro f. admit.
			  
				
			(*TODO*)
			(* exact (equiv_compose addpt_forget_adjoint f).
			
			exact ( functor_arrow pBool_to_two_pts idmap ).
	 *)
	Admitted.

	(*This should be equivalent to the loop space in the library*)
	Theorem omega_loops_equiv `{Funext} : forall n:nat, forall A:pType,
		Omega n A <~> iterated_loops n A.
		induction n.
			-intro A. exact Omega0_Equiv_A.
			-intro A.
			equiv_via (pSphere n ->* loops A).
				+apply loop_susp_adjoint.
				+exact (IHn (loops A) ).
	Qed.
	
	(*TODO*) Theorem omega_loops_peq `{Funext} :forall n:nat, forall A:pType,
		Omega n A <~>* iterated_loops n A. Admitted.

End Loops.

Section homotopy_groups.


	Definition homotopy_group (n:nat) (A:pType) :pType :=
		pTr 0 (Omega n A).

	Notation "'HtGr'" := homotopy_group.

	Definition SphereToOmega_functor {m n:nat} (f:pSphere m ->* pSphere n) (A:pType) :
		Omega n A ->* Omega m A.
	
		refine (Build_pMap _ _ _ _).
		(*Define the map*)
		* intro h. exact (h o* f).
		(*Prove that it is pointed map.*)
		* apply const_comp.
	Defined.

	Definition OmegaToHtGr_functor {m n : nat} {A:pType} (f : Omega n A ->* Omega m A) :
		HtGr n A ->* HtGr m A.
	
		refine (Build_pMap _ _ _ _).
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
		HtGr n A ->* HtGr m A :=
			OmegaToHtGr_functor (SphereToOmega_functor f A).
		
	End homotopy_groups.

Section Hopf.
	Definition Hopf : pSphere 3 ->* pSphere 2.
		Admitted. (*TODO*)
	
	Definition Hopf_induced (n:nat){A:pType}: 
		homotopy_group (n+2) A ->* homotopy_group (n+3) A 
		:=
		SphereToHtGr_functor (functor_sphere n Hopf) A.
		
End Hopf.

Section Precompose_pointed_equivalence.
	
	Definition pointed_precompose {A B C:pType} (f:A->*B) : (B->*C) -> (A->*C)
		:= (* fun g => Build_pMap _ _ (functor_arrow f idmap g) (ap g (point_eq f) @ point_eq g). *)
		fun g => g o* f.
	 
	
	Definition pt_precomose_inverse {A B C:pType} (f : A<~>*B) :
		(A->*C) -> (B->*C)
		:= pointed_precompose (pequiv_inverse f).
	
	Lemma isequiv_pt_precomose `{Funext} {A B C:pType} (f : A<~>*B)  : 
		IsEquiv (@pointed_precompose A B C f).
		Proof.

		refine (isequiv_adjointify (pointed_precompose f) (pt_precomose_inverse f) _ _).



			- intro g.
			
			unfold pointed_precompose.
			unfold pt_precomose_inverse.
			unfold pointed_precompose.
			apply equiv_path_pmap.
			assert (asso : ((g o* pequiv_inverse f) o* f == g o* ( (pequiv_inverse f) o* f))).
				apply pmap_compose_assoc.
			assert (inv : ((pequiv_inverse f o* f) ==* (pmap_idmap _))).
				+refine (Build_pHomotopy _ _).
					*cbn. intro x. apply eissect.
					*cbn.
				
				
				apply (pHomotopy_rec A A (pequiv_inverse f o* f) (pmap_idmap A)).
				
				unfold pmap_compose.
			unfold pmap_compose.
			cbn.
			unfold moveR_equiv_V.
(*			rewrite (ap_pp g (ap f^-1 (point_eq f)^) (eissect f (point A))).
			rewrite (ap_compose (f^-1) g (point_eq f)). (*TODO : Not rewrite*)
			rewrite (concat_p_pp _ _ _).
			rewrite (concat_p_pp _ _ _).
			rewrite <- (ap_pp g (ap f^-1 (point_eq f)) (ap f^-1 (point_eq f)^) ).
			rewrite <- (ap_pp f^-1 (point_eq f) (point_eq f)^).
			rewrite concat_pV.
			cbn.
			rewrite concat_1p.  
 			assert (point A = f^-1 (point B)).
				exact (point_eq (pequiv_inverse f))^.
			assert (eissect f (point A) = eissect f (f^-1 (point B))).
				rewrite <- X. reflexivity.
 			assert (ap g (eissect f (point A)) = ap g (eissect f (f^-1(point B)))).
 				rewrite X0. reflexivity.
(*  			rewrite <- X1. 

			
			rewrite <- (point_eq (pequiv_inverse f)).
 *)			 
			transparent assert (funpath : ((fun x:A => g (f^-1 (f x))) = g)).
				apply path_arrow.
				intro x. exact (ap g (eissect f x)).
			
			
			
(* 			assert (transport = v.2 
			
				use issig_pmap, and path_sigma . . .*)
			
			
			pointed_reduce; rename ispointed_type1 into a; rename ispointed_type0 into b.
			
			admit.
			
			- intro g.
			unfold pointed_precompose.
			unfold pt_precomose_inverse.
			unfold pmap_compose.
			cbn.
			unfold moveR_equiv_V.
			
			admit. *)
	Admitted.

End Precompose_pointed_equivalence.







(* 	Lemma equiv_sph0toA_A `{Funext} {A:pType} : A <~> (pSphere 0 ->* A).
		equiv_via (two_pts ->* A).
			-exact equiv_twotoA_A.
			-
			refine (BuildEquiv _ _ _ _).
				+exact (fun g => g o* sph0_to_two_pts).
				+refine (BuildIsEquiv _ _ _ _ _ _ _).
				admit. admit. admit. admit.
				(* 
				apply isequiv_precompose. *)
		Abort.
				 *)