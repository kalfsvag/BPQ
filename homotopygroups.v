(*TODO: Read STYLE.md and put this into HoTT library.*)
Require Import HoTT. 
Load pType_basics.
(*The main result in this file is the fact that S^n->*A <~> loops n A.
I also use this to construct a map between homotopy groups from a map between spheres.
Lastly I (assuming the Hopf map) construct a map pi_(n+1) A ->* pi_n A. *)

(*Setting some notation for the pointed type of pointed maps. Level is chosen arbitrarily. . .*)
Notation "A '*->*' B" := (Build_pType (A ->* B) _) (at level 50).
Notation sph := pSphere.
  

(*Show that precomposing with a pointed equivalence induces an equivalence. *)
(*TODO: do also with postcompose. . .*)
Section Compose_pointed_equivalence.
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

  Definition pointed_postcompose {A B C : pType} (g:B->*C) : (A->*B) -> (A->*C)
    := fun f => g o* f.

  Lemma isequiv_pt_postcompose `{Funext} {A B C:pType} (g : B->*C) {geq : IsEquiv g} :
    IsEquiv (@pointed_postcompose A B C g).
  Admitted. (*TODO*)
  
End Compose_pointed_equivalence.

(*Prove that addpoint and the forgetful functor pType->Type are adjoint. This is lemma 6.5.3 in book.*)
(*Move section to pointed.v*)
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
(*Move to HOT/Sphere*)
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
    - intros [ [] | [] ] ; exact idpath.
    - exact (Susp_ind _ idpath idpath (Empty_ind _)).
  Defined.

  (*TODO: Is pEquiv*)
End Two_points.


Section Loops.
  (*Move to HIT/Sphere*)
  (*TODO: Give new name? Regexp: "Omega \\((.+)\\|.\\) \\((.+)\\|.\\)"*)
  (*Define Omega n A as pointed maps from the n-sphere*)

(*  Definition Omega (n:nat) (A:pType) : pType :=
    Build_pType (pMap (pSphere n) A) _. *)
  
  Definition A_to_So2A {A:pType} : A -> (sph 0 ->* A) := 
    (pointed_precompose sph0_to_two_pts) o Map_to_pMap o (Unit_rec A).
  
  (*A_to_Omega0 is pointed:*)
  Definition pointed_A_to_So2A `{Funext} {A:pType}  : A_to_So2A (point A) = point (sph 0 ->* A).
    apply path_pmap.
    refine (Build_pHomotopy _ _).
    - refine (Susp_ind _ idpath idpath _).
      + intros [].
    - exact idpath.    
  Defined.

  Definition pA_to_So2A `{Funext} {A:pType}  := 
    Build_pMap A (sph 0 *->* A)  A_to_So2A pointed_A_to_So2A.

  Lemma isequiv_A_to_So2A `{Funext} {A:pType} : IsEquiv (@A_to_So2A A).
    Proof.
      refine isequiv_compose.
      refine isequiv_compose.
      - exact isequiv_Map_to_pMap.
      - exact (isequiv_pt_precompose sph0_to_two_pts (feq := isequiv_sph0_to_two_pts)).
  Defined.
  
  Definition pEquiv_A_So2A `{Funext} {A:pType} : A <~>* (sph 0 *->* A) := 
    Build_pEquiv _ _ pA_to_So2A isequiv_A_to_So2A.

  Fixpoint it_loop_susp_adj `{Funext} (n:nat) (A : pType) :
    (sph n ->* A) -> (sph 0 ->* (iterated_loops n A)) :=
    match n with
      | O => idmap
      | S n => (it_loop_susp_adj n (loops A)) o (loop_susp_adjoint _ _)
    end
  .
 (*
  Definition it_loop_susp_adj `{Funext} (n:nat) : 
    forall A:pType, Omega n A -> Omega 0 (iterated_loops n A).
    induction n.
    -intro A. exact idmap.
    -intro A.
     exact ( (IHn (loops A)) o (loop_susp_adjoint _ _) ) .
  Defined.
*)
  Lemma pointed_loop_susp_adjoint `{Funext} (A B:pType)  :
    loop_susp_adjoint A B (point (psusp A ->* B)) = point (A ->* (loops B)).
    Proof.
      refine (concat _ (pmap_postcompose_const A _ (loops B) (loop_susp_unit A))).
      apply path_pmap.
      apply pmap_prewhisker.
      refine (Build_pHomotopy _ _).
      - intro loop.
        refine (concat (concat_1p _) _).
        refine (concat (concat_p1 _) _).
        apply ap_const. 
      - hott_simpl.
    Qed.
        
  Lemma pointed_it_loop_susp_adj `{Funext} (n:nat) : forall A:pType,
    it_loop_susp_adj n A (point (sph n ->* A)) = point (sph 0 ->* (iterated_loops n A)).
    Proof.
      induction n.
      - reflexivity.
      - intro A.
        change (it_loop_susp_adj n.+1 A (point (sph n.+1 ->* A))) with
        ( (it_loop_susp_adj n (loops A)) ((loop_susp_adjoint _ _) (point (sph n.+1 ->* A))) ).
        rewrite (pointed_loop_susp_adjoint (pSphere n) A).
        exact (IHn (loops A)).
    Qed.

  Lemma isequiv_it_loop_susp_adj `{Funext} (n:nat) : 
    forall A:pType, IsEquiv (it_loop_susp_adj n A).
  Proof.
    induction n.
    -intro A.
     apply isequiv_idmap.
    -intro A.
     refine isequiv_compose.
  Defined.

  Definition pEquiv_S2A_So2lA `{Funext} (n:nat) (A:pType) :
    (sph n *->* A) <~>* (sph 0 *->* iterated_loops n A).
    refine (Build_pEquiv _ _ _ _).
    - refine (Build_pMap _ _ _ _).
      + apply it_loop_susp_adj.
      + apply pointed_it_loop_susp_adj.
    - apply isequiv_it_loop_susp_adj.
  Defined.

  (*Now we can prove the main theorem of this section:
    Omega is pointed equivalent to iterated_loops.*)
  Theorem pEquiv_S2A_loops `{Funext} (n:nat) (A:pType) :
    (sph n *->* A) <~>* iterated_loops n A.
  Proof.
    exact (Build_pEquiv _ _
                        ((pequiv_inverse pEquiv_A_So2A)  o* (pEquiv_S2A_So2lA n A))
                        isequiv_compose).
  Defined.
End Loops.

Section homotopy_groups.

  Definition homotopy_group (n:nat) (A:pType) : pType :=
    pTr 0 (sph n *->* A).

  Notation "'HtGr'" := homotopy_group.

  Definition SphereToS2A_functor {m n:nat} (f:pSphere m ->* pSphere n) (A:pType) :
    (sph n *->* A) ->* (sph m *->* A).
  Proof.
    rapply Build_pMap. 
    (*Define the map*)
    * intro h. exact (h o* f).
    (*Prove that it is pointed map.*)
    * apply pmap_postcompose_const.
  Defined.

  Definition S2A_to_HtGr_functor {m n : nat} {A:pType} (f : (sph n *->* A) ->* (sph m *->* A)) :
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
  Qed.

  Definition SphereToHtGr_functor {m n : nat} (f:pSphere m ->* pSphere n) (A:pType) :
    HtGr n A ->* HtGr m A :=
    S2A_to_HtGr_functor (SphereToS2A_functor f A).
  
End homotopy_groups.

Section Hopf.
  Definition Hopf : pSphere 3 ->* pSphere 2.
  Admitted. (*TODO*)
  
  Definition Hopf_induced (n:nat){A:pType}: 
    homotopy_group (n+2) A ->* homotopy_group (n+3) A 
    :=
      SphereToHtGr_functor (natural_sphere n Hopf) A.
  
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

