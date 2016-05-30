Require Import HoTT.
Load pType_basics.

Section Wedge.
  (*Define the wedge as a pushout.*)
  Definition wedge (A B : pType) := pushout (unit_name (point A)) (unit_name (point B) ).

  (*Give the basepoint of the wedge. It could just as well have been pushr tt.*)
  Global Instance ispointed_wedge {A B:pType} : IsPointed (wedge A B) := pushl tt.
  Definition pWedge (A B : pType) := Build_pType (wedge A B) _.

  (*The projection from sum to wedge:*)
  Definition sum_to_wedge {A B:pType} : (A+B)->(wedge A B) := push.
  
  (*The path between the two basepoints in the wedge:*)
  Definition pw {A B:pType} : 
    sum_to_wedge (inl (point A)) = sum_to_wedge (inr (point B)) 
    := pp tt.
  
  (*Wedge induction: You need compatible products over A and B.*)
  Definition wedge_ind {A B:pType} 
	     (P : (wedge A B)->Type) 
	     (f: forall a : A, P (sum_to_wedge (inl a)))
         (g : forall b : B, P (sum_to_wedge (inr b)))
	     (pw' : transport P pw (f (point A)) = g (point B) )
  : forall w : wedge A B, P w.
  Proof.
    rapply (@pushout_ind Unit A B).
    - intros [a | b].
      exact (f a).
      exact (g b).
    - intros [].
      exact pw'.
  Defined.
  
  (*Wedge recursion: You need compatible maps from A and B.*)
  Definition wedge_rec {A B: pType}
             (P : Type) (f : A -> P) (g : B -> P) (pw' : f (point A) = g (point B) ) : (wedge A B) -> P.
    Proof.
      rapply (@pushout_rec Unit A B).
      - intros [a | b].
        exact (f a). exact (g b).
      - intros []. exact pw'.
    Defined.
    (*Could also do this:
  := wedge_ind (fun _ : wedge A B => P) f g (transport_const pw (f (point A)) @ pw').

     But then it would be less convenient to use pushout_rec_beta_pp. . .*)

  (*Pointed recursion*)
  Definition wedge_pRec {A B : pType}
             (P : pType) (f : A ->* P) (g : B ->* P)  : (pWedge A B) ->* P.
    Proof.
      refine (Build_pMap _ _ _ _).
      - rapply (wedge_rec P f g).
        refine (concat _ _).
        + exact (point P).
        + exact (point_eq f).
        + exact (point_eq g)^.
     - exact (point_eq f).
    Defined.
    
  (*Wedge is a functor.*)
  Definition wedge_functor {A B C D:pType} (f:A->*C) (g:B->*D) : 
    (wedge A B) -> (wedge C D) :=
    wedge_rec
      (wedge C D)
      (sum_to_wedge o functor_sum f g o inl)
      (sum_to_wedge o functor_sum f g o inr)
      (ap (sum_to_wedge o inl) (point_eq f) @ pw @ (ap (sum_to_wedge o inr) (point_eq g))^).
  (*Todo:	Show that the result is a pMap*)

  (*wedge_rec takes the path pw to what it should.*)
  Lemma wedge_rec_beta_pw {A B : pType}
        (P : Type) (f : A -> P) (g : B -> P) (pw' : f (point A) = g (point B) ) :
    ap (wedge_rec P f g pw') pw = pw'.
  Proof.
    refine (pushout_rec_beta_pp P _ _ _).
  Defined.
    
  (*For instance, wedge_functor takes pw to pw (more or less).*)
  Lemma ap_wedge_functor {A B C D: pType} (f:A->*C) (g:B->*D) : 
    ap (wedge_functor f g) (pw) =
    ap (sum_to_wedge o inl) (point_eq f) @ pw @ (ap (sum_to_wedge o inr) (point_eq g))^.
  Proof.
    apply wedge_rec_beta_pw.
  Defined.
End Wedge.

Section Smash.
  (*First some simple maps used to define the smash product.*)
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

  (*The inclusion of the wedge into the product.*)
  Definition wedge_in_prod {A B:pType} : wedge A B -> A*B :=
    wedge_rec (A*B) (sum_to_product o inl) (sum_to_product o inr) idpath.
  (*This projects the path pw to idpath.*)
  Lemma ap_wedge_in_prod {A B:pType} : ap (@wedge_in_prod A B) pw = idpath.
    refine (pushout_rec_beta_pp _ _ _ _).
  Defined.

  (*This is just used to make the next proof more readable. . .*)
  Definition pair' {A B : Type}  : A -> B -> B*A := fun a b => (b,a).

  (*The inclusion of the wedge in the product is natural.*)
  Definition natural_wedge_in_prod {A B C D: pType} (f:A->*C) (g:B->*D) : 
    forall w : wedge A B, 
      functor_prod f g (wedge_in_prod w) = wedge_in_prod (wedge_functor f g w).
    rapply (@wedge_ind A B).
    - intro a. exact (ap (pair (f a)) (point_eq g) ).
    - intro b. exact (ap (pair' (g b)) (point_eq f) ).
    -rewrite transport_paths_FlFr.
     rewrite concat_pp_p.
     rewrite (ap_compose wedge_in_prod (functor_prod f g)).
     rewrite (ap_compose (wedge_functor f g) wedge_in_prod).
     rewrite (@ap_wedge_in_prod A B). hott_simpl.
     rewrite (@ap_wedge_functor A B C D f g).
     rewrite (ap_compose inr sum_to_wedge).
     rewrite (ap_compose inl sum_to_wedge).
     rewrite ap_pp. rewrite ap_pp. 
     rewrite (@ap_wedge_in_prod C D). hott_simpl.
     rewrite <- (ap_compose sum_to_wedge wedge_in_prod).     
     rewrite <- (ap_compose sum_to_wedge wedge_in_prod).
     pointed_reduce.
     exact idpath.
  Qed.

  (*Define the smash as a pushout.*)
  Definition smash (A B : pType) :=
    pushout (@const (wedge A B) Unit tt) (wedge_in_prod).

  (*The projection from the product to smash.*)
  Definition prod_to_smash {A B:pType} (pair:A*B) : smash A B
    := push (inr pair).

  (*Define the base point of smash.*)
  Global Instance ispointed_smash {A B:pType} : IsPointed (smash A B) := push (inl tt).
  Definition pSmash (A B: pType) := Build_pType (smash A B) _.

  (*The wedge collapses to a point in smash.*)
  Definition ps {A B : pType} :
    forall w : wedge A B, ispointed_smash = pushr w
    := pp.

  (*These are nice if you want to use smash without refering to wedge.*)
  Definition psA {A B : pType} :
    forall a : A, ispointed_smash = prod_to_smash (a, point B).
    intro a.
    exact (ps (sum_to_wedge (inl a))).
  Defined.
  
  Definition psB {A B : pType} :
    forall b : B, ispointed_smash = prod_to_smash (point A, b).
    intro b.
    exact (ps (sum_to_wedge (inr b))).
  Defined.

  (*Smash recursion : You need a map from A*B that is constant on the wedge.*)
  Definition smash_rec {A B : pType}
             (P:Type)
	         (f:A*B->P)
             (const_w : forall w : wedge A B, f (point A, point B) = f (wedge_in_prod w))
  : smash A B -> P.
  Proof.
    refine (pushout_rec _ _ _).
    - intros [ [] | pair].
      + (*What the basepoint of smash A B should be mapped to*)
        exact (f (point A, point B)).
      + (*What a general element of smash A B should be mapped to*)
        exact (f pair).
    - exact const_w.
  Defined.

  (*Variant of the recursion that doesn't use wedge.*)
  Definition smash_rec' {A B:pType} 
	     (P:Type)
	     (f:A*B->P)
         (const_w_1 : forall a : A, f (point A, point B) = f (a, point B))
         (const_w_2 : forall b : B, f (point A, point B) = f (point A, b))
         (const_w_12 : const_w_1 (point A) = const_w_2 (point B))
  : smash A B -> P.
  Proof.
    apply (smash_rec P f).
    -(*Now we show that f is constant on the wedge*)
      rapply (@wedge_ind A B).
      + exact const_w_1.
      + exact const_w_2.
      + simpl.
        path_via (const_w_1 (point A)).
        * path_via ((const_w_1 (point A)) @ ap (f o wedge_in_prod) pw).
            refine (transport_paths_Fr _ _).
            path_via (const_w_1 (point A) @ 1).
            { apply whiskerL.
              path_via (ap f (ap wedge_in_prod pw)).
              { apply ap_compose. }
              refine (concat _ _).
              exact (ap f idpath).
               apply ap.
               apply ap_wedge_in_prod.
              apply ap_1.
              }
            apply concat_p1.
        * exact const_w_12.
  Defined.
  
  Definition smash_pRec {A B : pType}
             (P : pType)
             (f : Build_pType (A*B) _ ->* P)
             (const_w : forall w: wedge A B, point P = f (wedge_in_prod w))
  : pSmash A B ->* P.
    Proof.
      refine (Build_pMap _ _ _ _).
      - apply (smash_rec P f ).
        intro w.
        exact ((point_eq f) @ (const_w w)).
      - exact (point_eq f).
    Defined.
        

  (*TODO: smash_rec_beta?*)
  (*TODO: smash_ind*)
  (*TODO : Smash and wedge are pointed. Functors map to pointed maps.*)
  (*TODO: Smash and wedge are product and coproduct in pType*)
  (*TODO: Comment better.*)
  
  Definition smash_functor {A B C D:pType} (f:A->*C) (g:B ->* D) :
    smash A B -> smash C D.
  Proof.
    rapply (@smash_rec A B).
    - (*First give the map A*B -> smash C D *)
      exact (prod_to_smash o (functor_prod f g)). (* : A*B -> smash C D*)
    - (*Then show it is well defined.*)
      intro w.
      (*Show that everything contracts to the basepoint: *)
      path_via (@ispointed_smash C D).
      path_via (prod_to_smash (B:=D) (wedge_in_prod (sum_to_wedge (inl (f (point A)))))).
      + apply (ap prod_to_smash). 
        apply (ap (fun d : D => (f (point A), d))).
        apply point_eq. 
      + apply (ps _)^. 
      + path_via (prod_to_smash (wedge_in_prod (wedge_functor f g w))).
        { apply ps. }
        apply (ap prod_to_smash).
        apply (natural_wedge_in_prod f g w)^.
  Defined.
              
(*      rewrite (natural_wedge_in_prod).
      path_via (prod_to_smash (B:=D) (wedge_in_prod (sum_to_wedge (inl a)))).
      
      path_via (prod_to_smash (f a, point D)).
      path_via (prod_to_smash (f (point A), point D)).
      { apply (ap prod_to_smash).
        apply (ap (fun d:D => (f (point A), d))).
        apply point_eq. }
      { apply ((psA (f (point A)))^ @ (psA (f a))). }
      apply (ap prod_to_smash). 
      apply (ap (fun d:D => (f a, d))).
      apply (point_eq g)^.
    - intro b.
      path_via (prod_to_smash (point C, g b)).
      path_via (prod_to_smash (point C, g (point B))).
      { apply (ap prod_to_smash).
        apply (ap (fun c : C => (c, g (point B)))).
        apply point_eq. }
      { apply ((psB (g (point B)))^ @ (psB (g b))). }
      { apply (ap prod_to_smash).
        apply (ap (fun c : C => (c, g b))).
        apply (point_eq _)^. }
    - simpl. hott_simpl.
      rewrite <- ap_pp.
      rewrite <- ap_pp.
      apply (ap (ap prod_to_smash)).
      rewrite ap_V. rewrite ap_V. rewrite concat_pV. rewrite concat_pV.
      reflexivity.
  Qed.
      
  *)
End Smash.



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
    refine (smash_rec' A  _ _ _ _).
    - apply (prod_curry ).
      intro a.
      apply (Susp_rec (point A) a  ). apply Empty_ind. (*Basepoint goes to basepoint.*)
    - intro a. exact idpath.
    - rapply (@Susp_ind Empty).
      + exact idpath.
      + exact idpath.
      + apply Empty_ind.
    - exact idpath.
  Defined.  
  
  Definition A_to_smash_A {A:pType} : A->smash A (pSphere 0) :=
    fun a:A => @prod_to_smash A (pSphere 0) (a,South).
    
  Definition ispointed_A_to_smash_A {A:pType} : 
    A_to_smash_A (point A) = ispointed_smash
    :=
      (pp (@sum_to_wedge A (pSphere 0) (inr South)))^.
	                                            
  Lemma isretr_AtoSm {A:pType} : Sect (@A_to_smash_A A) (@smash_A_to_A A).
    intro a.
    exact idpath.
  Defined.
  
  Lemma issect_AtoSm {A:pType} : Sect (@smash_A_to_A A) (@A_to_smash_A A).
    intro a.
    unfold A_to_smash_A.
    unfold prod_to_smash.
    unfold smash_A_to_A.
    unfold smash_rec'.
    unfold smash_rec.
    simpl.
    unfold prod_curry.
    simpl.
    unfold wedge_ind.
    simpl.
    unfold Susp_rec.
    unfold wedge_in_prod.
    simpl.
    unfold wedge_rec.
    simpl.
    unfold pushout_rec.
    simpl.
    unfold pushout_ind.
    simpl.
    unfold pushout.
    simpl.
    unfold Susp_ind.
    unfold ap_wedge_in_prod.
    simpl.
    unfold pushout_rec_beta_pp.
    unfold pushout_ind_beta_pp.
    unfold pushout.
    
    refine (pp _)^.

    
  Admitted.
  
  Lemma isequiv_A_to_smash_A {A:pType} : IsEquiv (@A_to_smash_A A).
    refine (BuildIsEquiv _ _ A_to_smash_A smash_A_to_A issect_AtoSm isretr_AtoSm _).
  Admitted.
(*
  Lemma is_pequiv_A_smash_A (A:pType) : A <~>* p (smash A (pSphere 0)).
    refine (Build_pEquiv A (p (smash A (pSphere 0))) _ _).
    -exact (Build_pMap A (p (smash A (pSphere 0))) (@A_to_smash_A A) ispointed_A_to_smash_A).
    -exact isequiv_A_to_smash_A.
  Qed.
  
  Lemma commute_smash_susp {A B:pType} : p (smash (psusp A) B) <~>* psusp p (smash A B).
  Admitted.
  *)
  
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
				exact (natural_wedge_in_prod f g w). *)*)