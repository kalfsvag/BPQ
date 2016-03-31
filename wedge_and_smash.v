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
	     (pp' : transport P (pp tt) (f (inl (point A))) = f (inr (point B)) )
  :forall w : wedge A B, P w.
    apply (pushout_ind 
	     (unit_name (point A)) 
	     (unit_name (point B)) 
	     P
	     f).
    intros[]. exact pp'.
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

  Definition wedge_functor {A B C D:pType} (f:A->*C) (g:B->*D) : 
    (wedge A B) -> (wedge C D).
    rapply (@wedge_rec A B).
    -exact (sum_to_wedge o (functor_sum f g)).
    -path_via (@sum_to_wedge C D (inl (point C))).
     exact (ap (sum_to_wedge o inl) (point_eq f)).
     path_via (@sum_to_wedge C D (inr (point D))).
     exact wedgepath.
     exact (ap (sum_to_wedge o inr) (point_eq g)^).
  Defined.
  (*Todo:	Show that the result is a pMap*)

  Lemma ap_wedge_functor {A B C D: pType} (f:A->*C) (g:B->*D) : 
    ap (wedge_functor f g) (wedgepath) = (ap (sum_to_wedge o inl) (point_eq f) @
   (wedgepath @ ap (sum_to_wedge o inr) (point_eq g)^)).
    refine (pushout_rec_beta_pp _ _ _ _).
  Qed.


  Definition sum_pr1 {A B:pType} (x:A+B) : A :=
    match x with
      |inl a => a
      |inr b => point A
    end.
  Definition sum_pr2 {A B:pType} (x:A+B) : B :=
    match x with
      |inl a => point B
      |inr b => b
    end.

  Definition sum_to_product {A B:pType} (x : A+B) : A*B:= (sum_pr1 x, sum_pr2 x).

  Definition wedge_in_prod {A B:pType} : wedge A B -> A*B.
    rapply (@wedge_rec A B).
    -exact sum_to_product.
    -exact idpath.
  Defined.
  
  Lemma ap_wedge_in_prod {A B:pType} : ap (@wedge_in_prod A B) wedgepath = idpath.
    refine (pushout_rec_beta_pp _ _ _ _).
  Qed.
    
  Definition swap {A B: Type} : A*B -> B*A.
    intros [a b]. exact (b,a).
  Defined.
  Definition pair' {A B:Type} (a:A) (b:B) :B*A := swap (pair a b).
  
  Definition natural_wedge_in_prod {A B C D: pType} (f:A->*C) (g:B->*D) : 
    forall w : wedge A B, 
      functor_prod f g (wedge_in_prod w) = wedge_in_prod (wedge_functor f g w).
    rapply (@wedge_ind A B).
    intros [a|b].
    -exact (ap (pair (f a)) (point_eq g) ).
    -exact (ap (pair' (g b)) (point_eq f) ).
    -rewrite transport_paths_FlFr.
     rewrite concat_pp_p.
     rewrite (ap_compose wedge_in_prod (functor_prod f g)).
     rewrite (ap_compose (wedge_functor f g) wedge_in_prod).
     rewrite (@ap_wedge_in_prod A B). hott_simpl.
     rewrite (@ap_wedge_functor A B C D f g).
     rewrite ap_pp. rewrite ap_pp. 
     rewrite (@ap_wedge_in_prod C D). hott_simpl.
     rewrite (ap_compose inr sum_to_wedge).
     rewrite (ap_compose inl sum_to_wedge).
     rewrite <- (ap_compose sum_to_wedge wedge_in_prod).     
     rewrite <- (ap_compose sum_to_wedge wedge_in_prod).
     pointed_reduce.
     exact idpath.
  Qed.

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