Require Import HoTT.
Require Import UnivalenceAxiom.
Load stuff.

Section Group_completion.
  (*The Grothendieck group completion*)
  (*The group completion of a symmetric monoid M is M*M/~ where m~s+m *)
  (*Assume S is a symmetric monoid with cancellation. (Group completion is nicer then.)*)
  Variable S : Symmetric_Monoid.
  (* Variable rc : right_cancellation_law S. *)

  Open Scope monoid_scope . 

  (*Take a triple (a, b ,s) to (s*a, s*b)*)
  Definition as_bs : S*S*S -> S*S.
    intros [[a b] s].
    exact (a+s, b+s).
  Defined.

  Definition grp_compl_set (S:Monoid) := Trunc 0 (Coeq as_bs fst).
  Definition grp_compl_mult : grp_compl_set S -> grp_compl_set S -> grp_compl_set S.
    refine (Trunc_rec _).
    intro g1.
    refine (Trunc_rec _).
    intro g2.
    revert g2.
    srapply @Coeq_rec.
    - (*Fix second variable*)
      intros [n1 n2].
      revert g1.
      srapply @Coeq_rec.
      + (*Fix first variable*)
        intros [m1 m2].
        exact (tr (coeq (m1 + n1, m2 + n2))).
      + (*First variable runs along cp*)
        intros [[a b] s].
        apply (ap (tr)).
        simpl.
        refine (_ @ cp (a + n1 ,b + n2,s)).
        apply (ap coeq). unfold as_bs.
        apply path_prod;
             refine ((mon_assoc)^ @ _ @ (mon_assoc));
             apply (ap (mon_mult _));
             apply mon_sym.
    - (*Second variable runs along cp*)
      intros [[a b] s].
      revert g1.
      srapply @Coeq_ind.
      + (*First variable is fixed*)
        intros [m1 m2].
        apply (ap (tr)).
        simpl.
        refine (_ @ cp (m1+a,m2+b,s)).
        apply (ap coeq). unfold as_bs.
        apply path_prod; apply mon_assoc.
      + (*First variable runs along cp*)
        intro abs'.
        apply (istrunc_truncation 0).
  Defined.
  
(*  Unset Printing Notations.
  Set Printing Implicit. *)
  Definition grp_compl_assoc : associative grp_compl_mult.
    Proof.
      unfold associative.
      srapply @Trunc_ind. intro a.
      srapply @Trunc_ind. intro b.
      srapply @Trunc_ind.
      srapply @Coeq_ind.
      - (*Fix third variable*)
        intros [n1 n2]; revert b.
        srapply @Coeq_ind.
        + (*Fix second variable*)
          intros [m1 m2]; revert a.
          srapply @Coeq_ind.
          * (*Fix first variable*)
            intros [l1 l2].
            apply (ap tr). apply (ap coeq).
            apply path_prod; apply mon_assoc.
          * (*First variable runs along cp*)
            intro abs. apply (istrunc_truncation 0).
        + (*Second variable runs along cp*)
          intro abs.
          apply (istrunc_truncation 0).
      - (*Third variable runs along cp*)
        intro abs. apply (istrunc_truncation 0).
    Defined.
          
  Definition grp_compl_id : grp_compl_set S := tr (coeq (mon_id S, mon_id S)).
  
  Definition grp_compl_lid : left_identity grp_compl_mult grp_compl_id.
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Variable is fixed*)
      intros [m1 m2].
      simpl.
      apply (ap tr).
      apply (ap coeq).
      apply path_prod; apply mon_lid.
    - (*Variable runs along cp*)
      intro x.
      apply (istrunc_truncation 0).
  Defined.
  
  Definition grp_compl_rid : right_identity grp_compl_mult grp_compl_id.
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Variable is fixed*)
      intros [m1 m2].
      simpl.
      apply (ap tr).
      apply (ap coeq).
      apply path_prod; apply mon_rid.
    - (*Variable runs along cp*)
      intro x.
      apply (istrunc_truncation 0).
  Defined.

  Definition grp_compl_sym : symmetric grp_compl_mult.
  Proof.
    srapply @Trunc_ind. intro a.
    srapply @ Trunc_ind.
    srapply @Coeq_ind.
    - (*Fix second variable*)
      intros [n1 n2]. revert a.
      srapply @Coeq_ind.
      + (*Fix first variable*)
        intros [m1 m2].
        apply (ap tr). apply (ap coeq).
        apply path_prod; apply mon_sym.
      + (*First variable runs along cp*)
        intro abs. apply (istrunc_truncation 0).
    - (*Second variable runs along cp*)
      intro abs. apply (istrunc_truncation 0).
  Defined.    

  Definition grp_compl_inv : grp_compl_set S -> grp_compl_set S.
  Proof.
    apply Trunc_rec.
    srapply @Coeq_rec.
    - intros [m1 m2].
      exact (tr (coeq (m2, m1))).
    - intros [[a b] s].
      simpl.
      apply (ap tr).
      exact (cp (b, a, s)).
  Defined.

  Definition grp_compl_linv : left_inverse grp_compl_mult grp_compl_id grp_compl_inv.
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Fix variable*)
      intros [m1 m2].
      simpl.
      apply (ap tr).
      refine (_ @ cp (mon_id S, mon_id S, m1 + m2)).
      apply (ap coeq).
      unfold as_bs.
      apply path_prod.
      + refine (_ @ (mon_lid (m1 + m2))^ ). apply mon_sym.
      + exact (mon_lid (m1+m2))^ .
    - intro abs.
      apply (istrunc_truncation 0).
  Defined.
  
  (*Can choose to prove right identity using lift identity and symmetry, or do the same proof again. . .*)
  Definition grp_compl_rinv : right_inverse grp_compl_mult grp_compl_id grp_compl_inv.
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Fix variable*)
      intros [m1 m2].
      simpl.
      apply (ap tr).
      refine (_ @ cp (mon_id S, mon_id S, m1 + m2)).
      apply (ap coeq).
      unfold as_bs.
      apply path_prod.
      + simpl.
        exact (mon_lid (m1+m2))^ .
      + simpl.
        refine (_ @ (mon_lid (m1+m2))^).
        apply mon_sym.
    - intro abs.
      apply (istrunc_truncation 0).
  Defined.

  Definition group_completion : Abelian_Group :=
    Build_Abelian_Group
      (Build_Group
         (Build_Monoid
            (grp_compl_set S) 
            (grp_compl_mult) grp_compl_id grp_compl_assoc grp_compl_lid grp_compl_rid )
         grp_compl_inv grp_compl_linv grp_compl_rinv)
      grp_compl_sym.

  
  (*Defining the (monoid) homomorphism from a monoid to its group completion*)
   Definition S_to_grpcmplS : Homomorphism S group_completion.
     srapply @Build_Homomorphism.
    - (*The map on set level*)
      intro m.
      exact (tr (coeq (m, mon_id S))).
    - (*The map preserves identity*)
      exact idpath.
    - (*The map is an isomorphism*)
      intros m1 m2.
      apply (ap tr); apply (ap coeq).
      apply path_prod.
        exact idpath.
        exact (mon_lid (mon_id S))^.
  Defined.

End Group_completion.

Section Functoriality.
  Open Scope monoid_scope.
  Definition functor_group_completion {S S' : Symmetric_Monoid} :
    Hom S S' -> Hom (group_completion S) (group_completion S').
  Proof.
    intro f.
    srapply Build_Homomorphism.
    - (*Construct the map.*)
      apply Trunc_rec.
      srapply @Coeq_rec.
      + (* (a,b) => (f a, f b) *)
        intros [m n].
        exact (tr (coeq (hom_map f m, hom_map f n))).
      + (*The map is well defined.*)
        intros [[a b] s].
        apply (ap tr).
        refine (_ @ cp (hom_map f a, hom_map f b, hom_map f s)).
        apply (ap coeq).
        apply path_prod; apply preserve_mult.
    - (*Preserves identity*)
      apply (ap tr). apply (ap coeq).
      apply path_prod; apply preserve_id.
    - (*Preserves multiplication.*)
      srapply @Trunc_ind. intro a.
      srapply @Trunc_ind.
      srapply @Coeq_ind.
      + (*Second variable is fixed*)
        intros [n1 n2]. revert a.
        srapply @Coeq_ind.
        * (*First variable is fixed*)
          intros [m1 m2].
          apply (ap tr). apply (ap coeq).
          apply path_prod; apply preserve_mult.
        * (*First variable runs along cp*)
          intro abs. apply (istrunc_truncation 0).
      + (*Second variable runs along cp*)
        intro abs. apply (istrunc_truncation 0).
  Defined.        
        
  Definition natural_S_to_grpcmplS {S S' : Symmetric_Monoid} (h : Hom S' S):
    compose_hom (S_to_grpcmplS S) h = compose_hom (functor_group_completion h) (S_to_grpcmplS S').
  Proof.
    apply path_hom.
    apply path_forall.
    intro m.
    apply (ap tr). apply (ap coeq).
    apply path_prod.
      exact idpath.
      exact (preserve_id h)^.
  Defined.      
  
End Functoriality.                                             

Section Adjointness.
  (*Prove that group completion is left adjoint to the forgetful functor from abelian groups to symmetric monoids*)
  Open Scope monoid_scope.
  
  Definition hom_map_extend_to_inv {S : Symmetric_Monoid} {A : Abelian_Group} :
    Homomorphism S A -> ((group_completion S) -> A).
  Proof.
    intro f.
    refine (Trunc_rec (H:=grp_isset _) _).
    srapply @Coeq_rec.
    + (*The variable is fixed*)
      intro m12.
      exact ((hom_map f (fst m12)) - (hom_map f (snd m12))).
    + (*The variable runs along cp (i.e. map is well defined)*)
      intros [[a b] s]. simpl.
      refine (path_group2 (preserve_mult f) (ap grp_inv (preserve_mult f)) @ _).
      refine (grp_assoc^ @ _ ).
      apply grp_whiskerL.
      apply grp_moveR_gV.
      refine (_ @ grp_assoc^ ).
      refine (_ @ grp_whiskerR (grp_linv _)^ ).
      exact (grp_lid _)^ .
  Defined.

  Definition extend_to_inv {S : Symmetric_Monoid} {A : Abelian_Group} :
    Homomorphism S A -> Homomorphism (group_completion S) A.
  Proof.
    intro f.
    refine (Build_Homomorphism _ _ (hom_map_extend_to_inv f) (grp_rinv _) _).
    (*Preserves multiplication*)
    (*First we need to use Trunc_ind
         This is made difficult by Trunc_ind behaving weirdly. . .*)

    (*Trunc_ind uses about 5 minutes to find a proof of this, faster to prove it manually.*)
    assert (Pt : forall m1 m2 : (group_completion S),
                   IsTrunc 0
                           (hom_map_extend_to_inv f (m1 + m2) =
                            hom_map_extend_to_inv f m1 + hom_map_extend_to_inv f m2) ). (*Can also use [enough]. . .*)
    { intros m1 m2.  exact (@trunc_succ -1 _ (mon_isset _ _ _)). }
    intro m1.
    refine (@Trunc_ind 0 (Coeq (as_bs S) fst) _ (Pt m1) _ ).
    intro b. revert m1.
    set (m2 := tr b : (group_completion S)).
    refine (@Trunc_ind 0 (Coeq (as_bs S) fst) _ (fun m1 => Pt m1 m2) _); unfold m2; clear m2.
    intro a. revert b.
    (*Now the truncations are done with. . .*)
    srapply @Coeq_ind.
    - (*Second variable fixed*)
      intros [n1 n2]. revert a.
      srapply @Coeq_ind.
      + (*First variable fixed*)
        intros [m1 m2]. simpl.
        refine (grp_whiskerR (preserve_mult f) @ _).
        refine (grp_assoc^ @ _ @ grp_assoc).
        apply grp_whiskerL.
        refine (grp_whiskerL (ap grp_inv (preserve_mult f)) @ _).
        refine (grp_whiskerL grp_inv_distr @ _).
        refine (_ @ grp_sym).
        exact grp_assoc.
      + (*First variable runs along cp*)
        intro abs. apply (grp_isset A).
    - (*Second variable runs along cp*)
      intro abs. apply (grp_isset A).
  Defined.

  Theorem grp_compl_adjoint (S : Symmetric_Monoid) (A: Abelian_Group) :
    Homomorphism S A <~> Homomorphism (group_completion S) A.
  Proof.
    refine (equiv_adjointify extend_to_inv (fun f => compose_hom f (S_to_grpcmplS S)) _ _).
    (*Prove that the maps are inverses*)
    - intro f.
      refine (path_hom _ _ _) ; simpl.
      apply path_forall.
      (*Trunc_ind uses about 5 minutes to find a proof of this, faster to prove it manually.*)
      assert (Pt : forall m : (group_completion S),
                   IsTrunc 0
                           (hom_map_extend_to_inv (compose_hom f (S_to_grpcmplS S)) m = hom_map f m)).
      { intro m. exact (@trunc_succ -1 _ (mon_isset _ _ _)). }
      refine (@Trunc_ind 0 (Coeq (as_bs S) fst) _ Pt _ ).
      srapply @Coeq_ind. 
      + (*Variable fixed*)
        intros [m1 m2].
        simpl.
        apply grp_moveR_gV.
        refine (_ @ preserve_mult f).
        apply (ap (hom_map f)); apply (ap tr).
        refine ((cp (m1, mon_id S, m2))^ @ _); unfold as_bs.
        apply (ap coeq).
        apply (ap (fun s : S => (m1 + m2, s))).
        exact (mon_lid m2 @ (mon_rid m2)^).
      + (*Variable runs along cp*)
        intro abs.
        apply (grp_isset A).
    - intro f.
      refine (path_hom _ _ _) ; simpl.
      apply path_forall.
      intro m.
      apply grp_moveR_gV.
      refine ((grp_rid _)^ @ _).
      exact (grp_whiskerL (preserve_id f)^ ).
  Defined.

  (*Naturality follows from [natural_S_to_grpcmplS], since the map [Hom (group_completion S) A -> Hom S A is exactly precomposing with [S_to_grpcmplS].*)

End Adjointness.
