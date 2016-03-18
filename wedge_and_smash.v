Require Import HoTT.
Load pType_basics.

Section wedge_and_smash.
	(*Define the wedge. The basepoint could just as well have been pushr tt,
	but some choice had to be made.*)
(* 	Definition wedge (A B:pType) := 
		Build_pType 
			(pushout (unit_name (point A)) (unit_name (point B) ) )
			(pushl tt). *)
	Definition wedge (A B : pType) := pushout (unit_name (point A)) (unit_name (point B) ).
	
	Global Instance ispointed_wedge {A B:pType} : IsPointed (wedge A B) := pushl tt.
	
	Definition sum_to_wedge {A B:pType} : (A+B)->(wedge A B) := push.
	
	Definition wedgepath {A B:pType} : 
		sum_to_wedge (inl (point A)) = sum_to_wedge (inr (point B)) 
		:= pp tt.
	
	
	Definition wedge_ind {A B:pType} 
		(P : (wedge A B)->Type) 
		(f:forall x:A + B, P (sum_to_wedge x)) 
		(pp' : forall u : Unit, transport P (pp u) (f (inl (point A))) = f (inr (point B)) )
		:forall w : wedge A B, P w.
			exact (pushout_ind 
				(unit_name (point A)) 
				(unit_name (point B)) 
				P
				f
				pp').
	Defined.
	
	(*To construct a map out of a wedge, you need:
		-map from A
		-map from B 
		-and a proof that these map the basepoints to the same point.*)
	Definition wedge_rec {A B : pType}
		(P : Type)
		(f : A+B->P)
		(pp' : f (inl (point A)) = f (inr (point B) )) : (wedge A B) -> P.
			refine (pushout_rec _ f _).
			 -exact (fun _ => pp'). (* intros []. exact pp'. *)
	Defined.
	
	Ltac path_via mid :=
		apply (concat (y:=mid)).
	
	Definition wedge_functor {A B C D:pType} (f:A->*C) (g:B->*D) : 
		(wedge A B) -> (wedge C D).
			rapply (@wedge_rec A B).
				-exact (sum_to_wedge o (functor_sum f g)).
				-
				path_via (@sum_to_wedge C D (inl (point C))).
					exact (ap (sum_to_wedge o inl) (point_eq f)).
					path_via (@sum_to_wedge C D (inr (point D))).
						exact wedgepath.
						exact (ap (sum_to_wedge o inr) (point_eq g)^).
	Defined.
	(*Todo:	Show that the result is a pMap*)
	
	Definition sum_to_product {A B:pType} (x : A+B) : A*B:=
		match x with
			|inl a => (a, point B)
			|inr b => (point A, b)
		end.
	
	Definition wedge_in_prod {A B:pType} : wedge A B -> A*B :=
		wedge_rec (A*B) sum_to_product idpath.
	
	Definition pair' {A B:Type} : B->A->A*B := fun (b:B) (a:A) => pair a b.
	
	Definition natural_wedge_in_prod {A B C D: pType} (f:A->*C) (g:B->*D) : 
		forall w : wedge A B, 
		functor_prod f g (wedge_in_prod w) = wedge_in_prod (wedge_functor f g w).
		rapply (@wedge_ind A B).
			intros [a|b].
				(* +apply path_prod.
					exact idpath.*)
				+exact (ap (pair (f a)) (point_eq g) ).
				+exact (ap (pair' (g b)) (point_eq f) ).
				(*
				exact (ap011 pair (point_eq f) idpath).
				 
				apply (ap (fun d:D => (f a, d))).
				exact (point_eq g).
				+apply (ap (fun c:C => (c, g b))).
				exact (point_eq f). *)
				+intros [].
			
			transparent assert (Fl : (wedge A B -> C*D)).
				exact (fun w => functor_prod f g (wedge_in_prod w) ).
			transparent assert (Fr : (wedge A B -> C*D)).
				exact (fun w => wedge_in_prod (wedge_functor f g w) ).
(* 			transparent assert (p1 : (wedge A B) ).
				exact (sum_to_wedge (inl (point A))).
			transparent assert (p2 : (wedge A B) ).
				exact (sum_to_wedge (inr (point B))). *)
(* 			transparent assert (pth : (p1 = p2)).
				exact (pp tt). 
			transparent assert (F_pth : (Fl p1 = Fr p1)).
				exact (ap (fun d : D => (f (point A), d)) (point_eq g)). *)
			path_via ( (ap Fl (pp tt))^ @ (ap (pair (f (point A))) (point_eq g)) @ (ap Fr (pp tt) )). 
				exact (transport_paths_FlFr (pp tt) (ap (pair (f (point A))) (point_eq g))).
 				
			(* unfold Fl.
			unfold Fr.
			unfold F_pth.
			 *)
			assert ( (ap Fl (pp tt)) = idpath).
				rewrite (ap_apply_Fr (pp tt) (functor_prod f g) (wedge_in_prod)).
				rewrite ((pushout_rec_beta_pp (A*B) sum_to_product (unit_name idpath)) tt ).
				exact idpath.
			
			rewrite X. clear X.
			simpl.
 			rewrite concat_1p.
			unfold Fr.
			rewrite (ap_apply_Fr (pp tt) wedge_in_prod (wedge_functor f g)).
			
			rewrite (pushout_rec_beta_pp (wedge C D) 
				(sum_to_wedge o (functor_sum f g) )
				(unit_name ((ap (fun x : C => sum_to_wedge (inl x)) (point_eq f) @
        (wedgepath @ ap (fun x : D => sum_to_wedge (inr x)) (point_eq g)^
        ))))
				).
				unfold wedgepath.
			
			rewrite ap_pp. rewrite ap_pp.
			rewrite ((pushout_rec_beta_pp (C*D) sum_to_product (unit_name idpath)) tt ).
			rewrite concat_1p.
			
			
				unfold functor_prod.
				unfold wedge_in_prod.
				unfold wedge_functor.
				unfold wedge_rec.
				unfold sum_to_product.
				unfold sum_to_wedge.
				unfold wedgepath.
				unfold pth.
				
				cbn.
				simpl.
				 
		Admitted.
	
	Definition smash (A B : pType) :=
		pushout (@const (wedge A B) Unit tt) (wedge_in_prod).
	
(* 	Definition smashpush {A B:pType} :=
		@push (wedge A B) pUnit (A*B) (@const (wedge A B) Unit tt) wedge_in_prod.
		(*TODO: Remove residues of smashpush*)
 *)	
	Definition prod_to_smash {A B:pType} (pair:A*B) : smash A B
		 := push (inr pair).
	
	Global Instance ispointed_smash {A B:pType} : IsPointed (smash A B) := push (inl tt).
	
	Definition smash_rec {A B:pType} 
		(P:Type)
		(basepoint:P)
		(f:A*B->P)
		(Ht: forall w : wedge A B, basepoint = f (wedge_in_prod w)) : (smash A B) -> P.
			refine (pushout_rec _ _ _).
			-intros [ [] | pair ].
				+exact (basepoint).
				+exact (f pair).
			-exact Ht.
	Defined.
	
	
	(*TODO : Smash and wedge are pointed. Functors map to pointed maps.*)
	(*TODO: Comment better.*)
	
		Definition smash_functor {A B C D:pType} (f:A->*C) (g:B ->* D) :
		smash A B -> smash C D.
 			rapply (@smash_rec A B).
			-exact (ispointed_smash). (*Basepoint*)
			-exact (prod_to_smash o (functor_prod f g)). (* : A*B -> smash C D*)
			(*Well defined:*)
			-simpl. intro w.
			path_via (prod_to_smash (wedge_in_prod (wedge_functor f g w))).
				+unfold prod_to_smash. unfold ispointed_smash.
				exact (pp (wedge_functor f g w)).
				+exact (ap prod_to_smash (natural_wedge_in_prod f g w))^.
		Defined.
End wedge_and_smash.



(*Results on the relation between smash product and spheres.*)
Section Smash_and_Spheres.

	Definition sph0xA_to_A {A:pType} : A*(Sphere 0) -> A.
		intros [a].
		exact (Susp_rec (point A) (a) (Empty_rec)).
	Defined.
	
	(* 
	Definition smashpush' {A:pType} : A*(pSphere 0) + pUnit -> A.
		intro x; elim x.
			-exact sph0xA_to_A.
			-exact (pconst _ _).
	Defined. *)
	
	Definition f {A:pType} (a : A+pSphere 0) : A := 
		sph0xA_to_A (wedge_in_prod (@sum_to_wedge A (pSphere 0) a)).
	Definition g {A:pType} (_ : A+pSphere 0) : A := point A.
	
	Definition welldefined {A:pType} : forall w : A + pSphere 0, 
		f w = g w.
		
		apply sum_ind.
			-intro a. exact idpath.
			-apply (@Susp_ind Empty _ idpath idpath); apply Empty_ind.
	Defined.
	
	
	Definition smash_A_to_A  {A:pType} : smash A (pSphere 0)  -> A.
	(*Use smash functor?*)
		refine (smash_rec A (point A) _ _).
			-intros [a].
			apply (Susp_rec (point A) a  ). intros []. (*Basepoint goes to basepoint.*)
			-refine (wedge_ind _ _ _).
				+intros [a|].
					*exact idpath.
				  *refine (Susp_ind _ idpath idpath _ ).
					intros [].
				+simpl. intros [].
				
	Admitted.
	
	Definition A_to_smash_A {A:pType} : A->smash A (pSphere 0) :=
		fun a:A => @prod_to_smash A (pSphere 0) (a,South).
	
	Definition ispointed_A_to_smash_A {A:pType} : 
		A_to_smash_A (point A) = ispointed_smash
		 :=
			(pp (@sum_to_wedge A (pSphere 0) (inr South)))^.
	
	Lemma isretr_AtoSm {A:pType} : Sect (@A_to_smash_A A) (@smash_A_to_A A).
		Admitted.
	
	Lemma issect_AtoSm {A:pType} : Sect (@smash_A_to_A A) (@A_to_smash_A A).
		Admitted.
	
	Lemma isequiv_A_to_smash_A {A:pType} : IsEquiv (@A_to_smash_A A).
		refine (BuildIsEquiv _ _ A_to_smash_A smash_A_to_A issect_AtoSm isretr_AtoSm _).
		Admitted.

	Lemma is_pequiv_A_smash_A (A:pType) : A <~>* p (smash A (pSphere 0)).
		refine (Build_pEquiv A (p (smash A (pSphere 0))) _ _).
				-exact (Build_pMap A (p (smash A (pSphere 0))) (@A_to_smash_A A) ispointed_A_to_smash_A).
		-exact isequiv_A_to_smash_A.
	Qed.
	
	Lemma commute_smash_susp {A B:pType} : p (smash (psusp A) B) <~>* psusp p (smash A B).
	Admitted.
	
	


End Smash_and_Spheres.






(* 		
		
		
		Alternative wedge_functor
		
			rapply (@functor_coeq Unit (A+B)).
				-exact idmap.
				-intros [a|b].
					+exact (inl (f a)).
					+exact (inr (g b)).
				-intros [].
				apply (ap inl).
				exact (point_eq f).
				-intros [].
				apply (ap inr).
				exact (point_eq g).
				
				 *)
							(* Alternative smash_functor

			rapply (@functor_coeq (wedge A B) (Unit+(A*B))).
				-exact (wedge_functor f g).
				-intros [[]|ab].
					+exact (inl tt).
					+exact (inr (functor_prod f g ab)).
				-apply ap10. exact idpath.
				-intro w.
				apply (ap inr).
				exact (natural_wedge_in_prod f g w). *)