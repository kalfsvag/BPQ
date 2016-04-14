(*TODO: Read STYLE.md and put this into HoTT library*)
Require Import HoTT. 
Load pType_basics.

(*The main result in this file is the fact that S^n->*A <~> loops n A.
I also use this to construct a map between homotopy groups from a map between spheres.
Lastly I (assuming the Hopf map) construct a map pi_(n+1) A ->* pi_n A. *)


(*Show that precomposing with a pointed equivalence induces an equivalence. *)
(*TODO: do also with postcompose. . .*)
Section Precompose_pointed_equivalence.
  Definition pointed_precompose {A B C:pType} (f:A->*B) : (B->*C) -> (A->*C)
    := fun g => g o* f.  
  
  Definition pt_precompose_inv {A B C:pType} (f : A->*B) {feq : IsEquiv f} :
    (A->*C) -> (B->*C)
    := pointed_precompose (pequiv_inv f).

  (*Precomposing with inverse is pointed homotopic to the idmap*)
  Lemma pcompose_inverse {A B:pType} (f : A->*B) {feq : IsEquiv f} :
    pequiv_inv f o* f ==* pmap_idmap A.
  Proof.
    apply issig_phomotopy.
    exists (fun x => eissect _ x).
    hott_simpl. 
    unfold pequiv_inverse; simpl.
    unfold moveR_equiv_V. 
    rewrite <- ap_pp_p.
    hott_simpl.
  Qed.
  
  (*The inverse of the inverse is pointed homotopic to the map itself.*)
  Lemma pequiv_inverse_twice {A B:pType} (f: A->*B) {feq : IsEquiv f} : 
    f ==* pequiv_inverse (pequiv_inv f).
  Proof.
    apply issig_phomotopy.
    exists (ap10 idpath).
    hott_simpl; simpl.
    unfold moveR_equiv_V; simpl.
    rewrite <- (point_eq f).
    rewrite eisadj.
    rewrite <- ap_pp.
    hott_simpl.
  Qed.
  
  (*Precomposing with pointed equivalence results in an equivalence.*)
  (*Should this just follow from isequiv_precompose?*)
  Lemma isequiv_pt_precompose `{Funext} {A B C:pType} (f : A->*B) {feq : IsEquiv f} : 
    IsEquiv (@pointed_precompose A B C f).
  Proof.    
    refine (isequiv_adjointify (pointed_precompose f) (pt_precompose_inv f) _ _).
    -intro g.
     apply equiv_path_pmap.
     pHomotopy_via (g o* ( (pequiv_inv f) o* f)).
     +apply pmap_compose_assoc.
     +pHomotopy_via (g o* (pmap_idmap A)).
      *apply pmap_postwhisker.
       apply pcompose_inverse.
      *exact (pmap_precompose_idmap g).
    -intro g.
     apply equiv_path_pmap.
     pHomotopy_via (g o* (f o* (pequiv_inv f))).
     +apply pmap_compose_assoc.
     +pHomotopy_via (g o* (pmap_idmap B)).
      *apply pmap_postwhisker.
       pHomotopy_via 
         ((pequiv_inverse (pequiv_inv f)) o* pequiv_inv f ).
       apply pmap_prewhisker.
       apply pequiv_inverse_twice.
       apply pcompose_inverse.
      *apply pmap_precompose_idmap.
  Qed.
End Precompose_pointed_equivalence.

(*Prove that addpoint and the forgetful functor pType->Type are adjoint. This is lemma 6.5.3 in book.*)
Section Addpoint_forgetful_adjointness.
  Definition pMap_to_Map {A:Type } {B:pType} : 
    ( (add_pt A) ->* B  ) -> ( A -> (pointed_type B) ) :=
    fun f => (f o inl).
  
  Definition Map_to_pMap {A:Type } {B:pType} : ( A->(pointed_type B) ) -> ( (add_pt A) ->* B  ).
    intro f.
    rapply Build_pMap.
    -intros [a | [] ].
     *exact (f a). (*What inl a maps to*)
     *exact (point B). (*What the basepoint maps to*)
    -exact idpath.
  Defined.

  Lemma isequiv_Map_to_pMap {A:Type } {B:pType} `{Funext} : IsEquiv (@Map_to_pMap A B).
  Proof.
    apply (@isequiv_adjointify (A->B) ( (add_pt A) ->* B  ) Map_to_pMap pMap_to_Map).

    -intros [pf pe].
     apply path_pmap.
     apply issig_phomotopy.
     unfold pMap_to_Map; unfold Map_to_pMap; simpl.
     refine (ex_intro _ _ _).
     +intros [a | [] ].
      *exact idpath.
      *exact pe^ .
     +simpl. hott_simpl.
    -exact (fun _ => idpath).
  Qed. 

  (*Lemma 6_5_3 in book:*)
  Lemma adjoint_addpt_forget `{Funext} (A:Type) (B:pType) : 
    ( A -> (pointed_type B) ) <~> ( (add_pt A) ->* B  ).
  Proof.
    exact (BuildEquiv _ _ Map_to_pMap isequiv_Map_to_pMap).
  Qed.
End Addpoint_forgetful_adjointness.


(*Show that my two-pointed types are equivalent*)
Section Two_points.
  Definition two_pts := add_pt Unit. 

  Definition sph0_to_two_pts : (pSphere 0) ->* two_pts.
    rapply Build_pMap.
    (*Construct map*)
    -apply (Susp_rec (inr tt) (inl tt)).
     +intros [].
    -exact idpath.
  Defined.
  
  Definition two_pts_to_sph0 : two_pts -> (pSphere 0).
    intros [].
      - exact (Unit_rec (pSphere 0) South).
      - exact (Unit_rec (pSphere 0) North).
  Defined.
    
  Lemma isequiv_sph0_to_two_pts : IsEquiv sph0_to_two_pts.
    rapply (isequiv_adjointify sph0_to_two_pts two_pts_to_sph0).
    - intros [ [] | [] ] ; repeat exact idpath.
    - exact (Susp_ind _ idpath idpath (Empty_ind _)).
  Defined. 
End Two_points.


Section Loops.

  (*Define Omega n A as pointed maps from the n-sphere*)
  Definition Omega (n:nat) (A:pType) : pType :=
    Build_pType (pMap (pSphere n) A) _.
  
  Definition A_to_Omega0 {A:pType} : A -> Omega 0 A := 
    (pointed_precompose sph0_to_two_pts) o Map_to_pMap o (Unit_rec A).
  
  (*A_to_Omega0 is pointed:*)
  Definition pointed_A_to_Omega0 `{Funext} {A:pType}  : A_to_Omega0 (point A) = point (Omega 0 A).
    apply path_pmap.
    apply issig_phomotopy.
    refine (ex_intro _ _ idpath).
    - refine (Susp_ind _ idpath idpath _).
      + intros [].
  Defined.

  Definition pA_to_Omega0 `{Funext} {A:pType} := 
    Build_pMap A (Omega 0 A)  A_to_Omega0 pointed_A_to_Omega0.

  Lemma isequiv_A_to_Omega0 `{Funext} {A:pType} : IsEquiv (@A_to_Omega0 A).
    Proof.
      refine isequiv_compose.
      refine isequiv_compose.
      - exact isequiv_Map_to_pMap.
      - exact (isequiv_pt_precompose sph0_to_two_pts (feq := isequiv_sph0_to_two_pts)).
  Defined.
  
  Definition equiv_A_Omega0 `{Funext} {A:pType} := 
    BuildEquiv _ _ (@A_to_Omega0 A) isequiv_A_to_Omega0.
  
  Definition it_loop_susp_adj `{Funext} (n:nat) : 
    forall A:pType, Omega n A -> Omega 0 (iterated_loops n A).
    induction n.
    -intro A. exact idmap.
    -intro A.
     exact ( (IHn (loops A)) o (loop_susp_adjoint _ _) ) .
  Defined.

  Lemma pointed_it_loop_susp_adj `{Funext} {A:pType} (n:nat) :
    it_loop_susp_adj n A (point (Omega n A)) = point (Omega 0 (iterated_loops n A)).
    Proof.
      induction n.
      - exact idpath.
      - admit.
    Admitted. (*TODO*)
      



  Lemma isequiv_it_loop_susp_adj `{Funext} (n:nat) : 
    forall A:pType, IsEquiv (it_loop_susp_adj n A).
  Proof.
    induction n.
    -intro A.
     apply isequiv_idmap.
    -intro A.
     refine isequiv_compose.
  Defined.

  (*My loop spaces and HoTT's loop spaces are equivalent*)
  Definition loops_to_omega `{Funext} {A:pType} (n:nat) : Omega n A -> iterated_loops n A :=
    (equiv_A_Omega0)^-1 o (it_loop_susp_adj n A).
  
  Lemma isequiv_loops_to_omega `{Funext} {A:pType} (n:nat) : IsEquiv (loops_to_omega (A:=A) n).
    refine isequiv_compose.
    exact (isequiv_it_loop_susp_adj n A).
  Defined.

  (*TODO: Show that this equivalence is natural in A.*)

  (*TODO:*)
  Theorem omega_loops_peq `{Funext} :forall n:nat, forall A:pType,
                                       iterated_loops n A <~>* Omega n A. 
  Admitted.

End Loops.

Section homotopy_groups.
  Definition homotopy_group (n:nat) (A:pType) :pType :=
    pTr 0 (Omega n A).

  Notation "'HtGr'" := homotopy_group.

  Definition SphereToOmega_functor {m n:nat} (f:pSphere m ->* pSphere n) (A:pType) :
    Omega n A ->* Omega m A.
    
    rapply Build_pMap. 
    (*Define the map*)
    * intro h. exact (h o* f).
    (*Prove that it is pointed map.*)
    * apply const_comp.
  Defined.

  Definition OmegaToHtGr_functor {m n : nat} {A:pType} (f : Omega n A ->* Omega m A) :
    HtGr n A ->* HtGr m A.
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





(*  Lemma equiv_sph0toA_A `{Funext} {A:pType} : A <~> (pSphere 0 ->* A).
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
