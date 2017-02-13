Load group_completion.
(* Load monoids_and_groups. *)

(*TODO: Make M not implicit. Use 1%nat_scope*)
Section Classifying_Space.
  Open Scope monoid_scope.
  (*Define the classifying space of a monoid as a cell complex*)

  (*The 1-skeleton of B.*)
  Definition pre_B (M : Monoid)  := @Coeq M Unit (const tt) (const tt).
  
  (*pre_B has one point:*)
  Global Instance ispointed_pre_B {M : Monoid} : IsPointed (pre_B M) := coeq tt.
  
  (*pre_B has one loop for every m : M*)
  Definition pre_B_loop {M : Monoid} : M -> point (pre_B M) = point (pre_B M) := cp.

  Definition pre_B_rec {M : Monoid}
             (P : Type)
             (bp : P)
             (l : forall m : M, bp = bp) :
    pre_B M -> P.
    srapply @Coeq_rec.
    - exact (const bp). (*intros []. exact bp.*)
    - exact l.
  Defined.

  Definition pre_B_rec_beta_l {M : Monoid}
             (P : Type)
             (bp : P)
             (l : forall m : M, bp = bp)
             (m : M):
    ap (pre_B_rec P bp l) (pre_B_loop m) = l m :=
    Coeq_rec_beta_cp P (const bp) l m.

  Definition pre_B_ind {M : Monoid}
             (P : pre_B M -> Type) (bp : P (point (pre_B M)))
             (loop' : forall (m : M), transport P (pre_B_loop m) bp = bp)
             : forall a : pre_B M, P a.
  Proof.
    srapply @Coeq_ind.
    - intros []. exact bp.
    - exact loop'.
  Defined.


  Definition pre_B_ind_beta_l {M : Monoid}
             (P : pre_B M -> Type) (bp : P (point (pre_B M)))
             (loop' : forall (m : M), transport P (pre_B_loop m) bp = bp)
             (m : M) :
    apD (pre_B_ind P bp loop') (pre_B_loop m) = loop' m
    :=
      Coeq_ind_beta_cp P _ loop' m.

  
  Definition looptofill (M : Monoid) (m1 m2 : M) : S1 -> pre_B M.
    refine (S1_rec (pre_B M) (point (pre_B M)) _).
    exact ((pre_B_loop m1) @ (pre_B_loop m2) @ (pre_B_loop (m1 + m2))^).
  Defined.

  Definition looptofill_curried (M : Monoid) : M*M*S1 -> pre_B M :=
    prod_curry (prod_curry (looptofill M)).  
  
  Definition S1topre_B {M : Monoid} (m1 m2 : M) : S1 -> pre_B M :=
    looptofill M m1 m2.

  Definition collapseS1 (M : Monoid) : M*M*S1 -> M*M.
    intros [[m1 m2] x].
    exact (m1, m2).
  Defined. 

  (*Construct 2-cells*)
  Definition B2 (M : Monoid) := pushout
                                  (looptofill_curried M)
                                  (collapseS1 M).

  Definition ispointed_MMS1 {M : Monoid} : IsPointed (M * M * S1) := (mon_id M, mon_id M, base).

  Definition pre_BtoB2 {M : Monoid} : pre_B M -> B2 M := (push o inl).

  Global Instance ispointed_B2 {M : Monoid} : IsPointed (B2 M) := pre_BtoB2 ispointed_pre_B.

  Definition B2_loop {M : Monoid} (m : M) : point (B2 M) = point (B2 M) :=
    ap pre_BtoB2 (pre_B_loop m).

  Definition nullhom_S1toB2 {M : Monoid} (m1 m2 : M) :
    pre_BtoB2 o (S1topre_B m1 m2) == (fun _ : S1 => pre_BtoB2 (S1topre_B m1 m2 base)) .
  Proof.
    intro x.
    refine (concat (pp (m1, m2, x)) _).
    exact (pp (m1, m2, base))^. (*Weirdly enough, putting this inside the concat doesn't work. . .*)
  Defined.


  Definition const_S1toB2 {M : Monoid} (m1 m2 : M) :
    pre_BtoB2 o (S1topre_B m1 m2) = (fun _ : S1 => pre_BtoB2 (S1topre_B m1 m2 base)) :=
    path_forall _ _ (nullhom_S1toB2 m1 m2).

  Definition B2_resp_mul {M : Monoid} (m1 m2: M) :
     B2_loop (m1 + m2) = B2_loop m1 @ B2_loop m2.
  Proof.
    unfold B2_loop.
    apply moveR_1M.
    refine (_ @ whiskerR (ap_pp pre_BtoB2 _ _) _).
    refine (_ @ whiskerL _ (ap_V pre_BtoB2 _)).
    refine (_ @ (ap_pp pre_BtoB2 _ _)).
    refine (_ @ ap02 _ (S1_rec_beta_loop _ _ _)).
    refine (_ @ (ap_compose _ _ _)).
    refine ((ap_const loop (pre_BtoB2 (S1topre_B m1 m2 base)))^ @ _).
    refine ((ap12 loop (const_S1toB2 m1 m2))^ @ _).
    change
      (S1_rec (Coeq (const tt) (const tt)) (coeq tt)
              ((pre_B_loop m1 @ pre_B_loop m2) @ (pre_B_loop (m1 + m2))^)) with
    (S1topre_B m1 m2).
    assert (p : (ap10 (const_S1toB2 m1 m2) base) = idpath).
    { refine ((ap10_path_forall _ _ (nullhom_S1toB2 m1 m2) _) @ _).
      apply concat_pV. }
    refine (whiskerL _ p @ _).
    refine (concat_p1 _ @ _).
    refine (whiskerR (inverse2 p) _ @ _).
    apply concat_1p.
  Defined.

  Definition B2_rec {M : Monoid}
             (C : Type)
             (c0 : C)
             (Cp : M -> c0 = c0)
             (resp_mul_C : forall m1 m2 : M, Cp (m1 + m2) = Cp m1 @ Cp m2) :
    B2 M -> C.
    (*B2 is the pushout of pre_B M and M*M*S1*)
    srapply @pushout_rec.
    - apply sum_rect.      
      + (*The map defined on pre_B is given by l*)
        exact (pre_B_rec _ c0 Cp).
        (*The map on M*M*S1 is the constant map (it gives the loops that will be killed)*)
      + exact (const c0).
    - (*Show that the map is well-defined, e.g. m1@m2=m1*m2 *)
      simpl.
      intros [[m1 m2]].
      unfold const.      
      unfold looptofill_curried.
      unfold prod_curry.
      simpl.
      unfold looptofill.
      srapply @S1_ind.
      + exact idpath.
      + refine (concat (transport_paths_Fl loop idpath) _).
        refine (concat_p1 _ @ _).
        unfold pre_B_rec.
        apply (inverse2 (q := idpath)).
        refine (ap_compose _ _ _ @ _).
        refine (concat (y:= ap (Coeq_rec C (const c0) Cp)
                               ((pre_B_loop m1 @ pre_B_loop m2) @ (pre_B_loop (m1 + m2))^) ) _ _).
        { apply (ap (ap _)). apply S1_rec_beta_loop. }
        refine (ap_pp _ _ _ @ _).
        refine (whiskerR (ap_pp _ _ _) _ @ _).
        refine (whiskerL _ (ap_V _ _) @ _).
        apply moveR_pV.
        refine (_ @ (concat_1p _)^).
        unfold pre_B_loop.
        refine (_ @ (Coeq_rec_beta_cp C (const c0) Cp (m1 + m2))^).
        refine (_ @ (resp_mul_C m1 m2)^).
        apply concat2; refine (Coeq_rec_beta_cp C (const c0) Cp _).
  Defined.

  Definition B2_rec_beta_l {M : Monoid}
             (C : Type)
             (c0 : C)
             (Cp : M -> c0 = c0)
             (resp_mul_C : forall m1 m2 : M, Cp (m1 + m2) = Cp m1 @ Cp m2)
             (m : M):
    ap (B2_rec C c0 Cp resp_mul_C) (B2_loop m) = Cp m.
  Proof.
    unfold B2_loop.
    refine ((ap_compose pre_BtoB2 _ _)^ @ _).
    apply pre_B_rec_beta_l.
  Defined.

  (*Should probably switch to lean or implement pathovers here. . .*)
  Definition B2_ind {M : Monoid}
             (C : B2 M -> Type)
             (c0 : C (point (B2 M)))
             (Cp : forall (m : M), transport C (B2_loop m) c0 = c0)
             (resp_mul_C : forall (m1 m2 : M),
                    transport
                      (fun pth => transport C pth c0 = c0)
                      (B2_resp_mul m1 m2)
                      (Cp (m1 + m2))
                    = concat_over _ _ _ (Cp m1) (Cp m2))
             : forall a : B2 M, C a.
  Admitted.

    
  Definition B2_resp_id {M : Monoid} : B2_loop (mon_id M) = idpath.
    apply (cancelL (B2_loop (mon_id M)) _ _).
    refine (concat (B2_resp_mul _ _)^ _).
    refine (concat _ (concat_p1 _)^).
    apply (ap B2_loop).
    apply mon_lid.
  Defined.

  Definition trB (M : Monoid) := Tr 1 (B2 M).

  Global Instance ispointed_trB {M : Monoid} : IsPointed (trB M) := tr (point (B2 M)).

  Definition trB_loop {M : Monoid} (m : M) : point (trB M) = point (trB M) := ap tr (B2_loop m).
  Definition trB_resp_mul {M : Monoid} (m1 m2: M) :
    trB_loop (m1 + m2) = (trB_loop m1) @ (trB_loop m2).
    refine (_ @ (ap_pp tr _ _)).
    apply (ap (ap tr)).
    apply B2_resp_mul.
  Defined.

  Definition trB_resp_id {M : Monoid} : trB_loop (mon_id M) = idpath.
    unfold trB_loop.
    refine (concat _ (ap_1 _ tr)).
    apply (ap (ap tr)).
    apply B2_resp_id.
  Defined.

  Definition trB_rec {M : Monoid}
             (C : Type) {istrunc : IsTrunc 1 C}
             (c0 : C)
             (Cp : M -> c0 = c0)
             (resp_mul_C : forall m1 m2 : M, Cp (m1 + m2) = Cp m1 @ Cp m2)
              : trB M -> C.
  Proof.
    apply Trunc_rec.
    exact (B2_rec C c0 Cp resp_mul_C ).
  Defined.

  Definition trB_rec_beta_l {M : Monoid}
             (C : Type) {istrunc : IsTrunc 1 C}
             (c0 : C)
             (Cp : M -> c0 = c0)
             (resp_mul_C : forall m1 m2 : M, Cp (m1 + m2) = Cp m1 @ Cp m2)
             (m : M) :
    ap (trB_rec C c0 Cp resp_mul_C) (trB_loop m) = Cp m.
  Proof.
    unfold trB_rec.
    unfold trB_loop.
    refine ((ap_compose tr _ _)^ @ _). simpl.
    apply B2_rec_beta_l.
  Defined.

  Definition trB_ind {M : Monoid}
             (C : trB M -> Type) {istrunc : forall (a : trB M), IsTrunc 1 (C a)}
             (c0 : C (point (trB M)))
             (Cp : forall (m : M), transport C (trB_loop m) c0 = c0)
             (resp_mul_C : forall (m1 m2 : M),
                    transport
                      (fun pth => transport C pth c0 = c0)
                      (trB_resp_mul m1 m2)
                      (Cp (m1 + m2))
                    = concat_over _ _ _ (Cp m1) (Cp m2))
             : forall a : trB M, C a.
    apply Trunc_ind.
    exact istrunc.
    srapply @B2_ind.
    - exact c0.
    - intro m.
      refine (_ @ Cp m).
      apply (transport_compose C tr).
    - intros m1 m2.
      simpl.
      unfold concat_over.
      refine (transport_paths_Fl (B2_resp_mul m1 m2) _ @ _).
      hott_simpl.
  Admitted.

  (*Computation rule that becomes unessecary when B_ind is properly defined.*)
  Definition trB_ind_beta_bp {M : Monoid}
             (C : trB M -> Type) {istrunc : forall (a : trB M), IsTrunc 1 (C a)}
             (c0 : C (point (trB M)))
             (Cp : forall (m : M), transport C (trB_loop m) c0 = c0)
             (resp_mul_C : forall (m1 m2 : M),
                    transport
                      (fun pth => transport C pth c0 = c0)
                      (trB_resp_mul m1 m2)
                      (Cp (m1 + m2))
                    = concat_over _ _ _ (Cp m1) (Cp m2)) :
    trB_ind C c0 Cp resp_mul_C (point (trB M)) = c0.
  Admitted.
    
End Classifying_Space.



Section looptrBM_is_groupcompletion.
  Open Scope monoid_scope.
  Fixpoint iterloop (n : nat) :=
    match n with
      | O => idpath
      | S n => loop @ (iterloop n)
    end.

  (*A simple case first. . .*)
  Lemma trBN_is_S1 : S1 <~> trB nat_monoid.
  Proof.
    srapply @equiv_adjointify.
    - (*Map from S1 to trBN*)
      srapply @S1_rec.
        exact (point _).
      refine (trB_loop _). exact 1.
    - (*Map from trBN to S1*)
      srapply @trB_rec.
      + exact base.
      + exact iterloop.
      + induction m1; intro m2.
        { apply (concat_1p _)^. }
        { simpl.
          refine (_ @ concat_p_pp _ _ _ ).
          apply whiskerL.
          apply IHm1. }
    - (*Composition is identity on trBN*)
      srapply @trB_ind.
      reflexivity.
      +  simpl.
         intro m.
         refine
           (transport_paths_FlFr
              (f := fun a =>
                    S1_rec (trB nat_monoid) (point (trB nat_monoid)) 
                           (trB_loop (M := nat_monoid) (S O))
                           (trB_rec (M := nat_monoid) S1 base iterloop
                                    (fun m1 : nat =>
                                       nat_rect
                                         (fun m0 : nat =>
                                            forall m2 : nat, iterloop (m0 + m2) = iterloop m0 @ iterloop m2)
                                         (fun m2 : nat => (concat_1p (iterloop m2))^)
                                         (fun (m0 : nat)
                                              (IHm1 : forall m2 : nat,
                                                        iterloop (m0 + m2) = iterloop m0 @ iterloop m2)
                                              (m2 : nat) =>
                                            whiskerL loop (IHm1 m2) @
                                                     concat_p_pp loop (iterloop m0) (iterloop m2)) m1) a))
              (trB_loop (M := nat_monoid) m) idpath @ _).
         simpl.
         apply moveR_pM.
         refine (concat_p1 _ @ _ @ (concat_1p _)^).
         apply inverse2.
         refine (ap_compose
                   (trB_rec (M := nat_monoid) S1 base iterloop
                            (fun m1 : nat =>
                               nat_rect
                                 (fun m0 : nat =>
                                    forall m2 : nat, iterloop (m0 + m2) = iterloop m0 @ iterloop m2)
                                 (fun m2 : nat => (concat_1p (iterloop m2))^)
                                 (fun (m0 : nat)
                                      (IHm1 : forall m2 : nat,
                                                iterloop (m0 + m2) = iterloop m0 @ iterloop m2)
                                      (m2 : nat) =>
                                    whiskerL loop (IHm1 m2) @
                                             concat_p_pp loop (iterloop m0) (iterloop m2)) m1))
                   (S1_rec (trB nat_monoid) (point (trB (nat_monoid))) (trB_loop (M := nat_monoid)
                                                                                 (S O)))
                   (trB_loop (M := nat_monoid) m) @ _).
         transitivity
           (ap
              (S1_rec (trB nat_monoid) (point (trB nat_monoid))
                      (trB_loop (M := nat_monoid) 1)) (iterloop m)).
         apply (ap (ap (S1_rec (trB nat_monoid) (point (trB nat_monoid))
                               (trB_loop (M := nat_monoid) 1)))).
         apply trB_rec_beta_l.
         induction m.
         { hott_simpl. apply inverse.
           apply (trB_resp_id (M := nat_monoid) ). }
         hott_simpl.
         refine (ap_pp (S1_rec (trB nat_monoid) (point (trB nat_monoid))
                               (trB_loop (M := nat_monoid) (S O)))
                       loop (iterloop m) @ _).
         rewrite IHm.
         rewrite S1_rec_beta_loop.
         apply inverse.
         apply (trB_resp_mul (M:=nat_monoid) (S O) m). 
      + intros m1 m2.
        apply (istrunc_truncation 1).
    - (*Composition is identity on S1*)
      srapply @S1_ind.
      + exact idpath.
      + simpl.
        refine (transport_paths_FlFr
                  (f :=
                     fun x : S1 =>
                       trB_rec
                         (M := nat_monoid) S1 base iterloop
                         (fun m1 : nat =>
                            nat_rect
                              (fun m0 : nat =>
                                 forall m2 : nat, iterloop (m0 + m2) = iterloop m0 @ iterloop m2)
                              (fun m2 : nat => (concat_1p (iterloop m2))^)
                              (fun (m0 : nat)
                                   (IHm1 : forall m2 : nat,
                                             iterloop (m0 + m2) = iterloop m0 @ iterloop m2)
                                   (m2 : nat) =>
                                 whiskerL loop (IHm1 m2) @
                                          concat_p_pp loop (iterloop m0) (iterloop m2)) m1)
                         (S1_rec
                            (trB nat_monoid) (point (trB nat_monoid)) (trB_loop (M := nat_monoid) (S O)) x))
                  loop idpath @ _).
        apply moveR_pM.
        refine (concat_p1 _ @ _ @ (concat_1p _)^).
        apply inverse2.
        refine (_ @ (ap_idmap loop)^).
        refine (ap_compose
                  (S1_rec (trB nat_monoid) (point (trB (nat_monoid))) (trB_loop (M := nat_monoid) (S O)))
                  (trB_rec (M := nat_monoid) S1 base iterloop _)
                  loop @ _).
        transitivity (ap
                        (trB_rec (M := nat_monoid) S1 base iterloop
                               (fun m1 : nat =>
        nat_rect
          (fun m0 : nat =>
           forall m2 : nat, iterloop (m0 + m2) = iterloop m0 @ iterloop m2)
          (fun m2 : nat => (concat_1p (iterloop m2))^)
          (fun (m0 : nat)
             (IHm1 : forall m2 : nat,
                     iterloop (m0 + m2) = iterloop m0 @ iterloop m2)
             (m2 : nat) =>
           whiskerL loop (IHm1 m2) @
           concat_p_pp loop (iterloop m0) (iterloop m2)) m1))
                        (trB_loop (M := nat_monoid) (S O))).
        { apply (ap _).
          apply S1_rec_beta_loop. }
        refine (trB_rec_beta_l (M := nat_monoid) S1 base iterloop _ (S O) @ _).
        unfold iterloop. apply concat_p1.
  Defined.

  (*Lage alternativ til apD?*)

    
  (*Classifying space as a pointed type*)
  Definition ptrB (M : Monoid) := Build_pType (trB M) _.

  Definition grpcplS_to_loopstrB {S : Symmetric_Monoid} : Hom (group_completion S) (loopGroup (ptrB S)) :=
    extend_to_inv 
      (Build_Homomorphism S (loopGroup (ptrB S)) trB_loop trB_resp_id trB_resp_mul).
  
  (*Fibration over trB S with fiber groupcompletion S*)
  Definition trB_code (S : Symmetric_Monoid) : trB S -> hSet.
  Proof.
    srapply @trB_rec.
        - exact (BuildTruncType 0 (group_completion S)).
        - intro a.
          apply (ap trunctype_type)^-1.
          exact (path_universe (grp_mult_equiv (to_groupcompletion a))).
        - intros m1 m2.
          apply (equiv_inj (ap trunctype_type)).
          refine (_ @ (ap_pp trunctype_type _ _)^).
          refine (eisretr (ap trunctype_type) _ @ _).
          refine (_ @ concat2 (eisretr (ap trunctype_type) _)^
                              (eisretr (ap trunctype_type) _)^).          
          refine (_ @ path_universe_compose _ _).
          refine (equiv_path2_universe
                    (grp_mult_equiv (to_groupcompletion (m1 + m2)))
                    (grp_mult_equiv (to_groupcompletion m2) oE
                                    grp_mult_equiv (to_groupcompletion m1))
                    (fun m => (grp_whiskerL (preserve_mult to_groupcompletion) @ grp_assoc)) ).
  Defined.

  Definition trB_code_beta {S : Symmetric_Monoid} (m : S) :
    ap (trB_code S) (trB_loop m) =
    (ap trunctype_type)^-1 (path_universe (grp_mult_equiv (to_groupcompletion m))).
  Proof.
    srapply @trB_rec_beta_l.
  Defined.

  Definition transport_code_is_mult {S : Symmetric_Monoid} (m : S) :
    transport (trB_code S) (trB_loop m) == fun g : (group_completion S) => g + (to_groupcompletion m).
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Variable is fixed*)
      intros [a b].
      refine (transport_compose trunctype_type (trB_code S) (trB_loop m) (tr (coeq (a, b))) @ _).
      refine (transport_compose idmap (trunctype_type)
                                (ap (trB_code S) (trB_loop m)) (tr (coeq (a, b))) @ _).
      assert (trB_code_beta' : ap trunctype_type (ap (trB_code S) (trB_loop m))  =
                             path_universe (grp_mult_equiv (to_groupcompletion m))).
      { refine (ap (ap trunctype_type) (trB_code_beta m) @ _).
        apply (eisretr (ap trunctype_type)). }      
      refine (ap (fun p : trunctype_type (trB_code S (point (trB S))) =
                          trunctype_type (trB_code S (point (trB S))) =>
                    transport (fun X : Type => X) p (tr (coeq (a, b)))) trB_code_beta' @ _).
      refine (ap10 (transport_idmap_path_universe (grp_mult_equiv (to_groupcompletion m))) _).
    - (*Variable runs along cp*)
      intro abs.
      apply (istrunc_truncation 0).
  Defined.

  Definition transport_code_is_mult_V {S : Symmetric_Monoid} (m : S) :
    transport (trB_code S) (trB_loop m)^ == fun g : (group_completion S) => g - (to_groupcompletion m).
  Proof.
    intro x.
    refine (moveR_transport_V (trB_code S) (trB_loop m) x _ _).
    apply inverse.
    refine (transport_code_is_mult m _ @ _).
    refine (_ @ grp_rid x).
    refine (grp_assoc^ @ _).
    refine (grp_whiskerL _).
    apply grp_linv.
  Defined.

  Definition trB_encode {S : Symmetric_Monoid} (x : trB S) :
    (point _ = x) -> trB_code S x := fun p => transport (trB_code S) p (point _).

  (*I hope this is useful for proving truncations
   Something like this is probably already implemented. . .*)
  Definition generalize_paths {X : Type} {x1 x2 : X} {p1 p2 : x1 = x2} :
    (IsTrunc 0 X) -> p1 = p2.
  Proof.
    intro H. apply H.
  Defined.

  Definition trB_decode {S : Symmetric_Monoid} (x : trB S) :
    trB_code S x -> (point _ = x).
  Proof.
    revert x.
    srapply @trB_ind.
    - (*x is point*)
      simpl.
      apply grpcplS_to_loopstrB.
    - (*x is trB_loop m*)
      intro m.
      apply path_arrow. intro x.
      refine (transport_arrow (trB_loop m) _ x @ _).
      (*This is more readable, but then it protests when writing x - m*)
      (*unfold trB_code in x. simpl in x.  *)
      refine (transport_paths_r (trB_loop m) _ @ _).      
      apply moveR_pM.
      refine (ap (fun g : group_completion S => grpcplS_to_loopstrB g)
                 (transport_code_is_mult_V m x) @ _).
      refine (preserve_mult grpcplS_to_loopstrB @ _).
      refine (whiskerL (grpcplS_to_loopstrB x) _).
      refine (whiskerR trB_resp_id (trB_loop m)^ @ _).
      apply concat_1p.
    - (*x is ishom m1 m2*)
      intros m1 m2.
      srapply @generalize_paths.
  Defined.

  Definition trB_decode_beta_bp {S : Symmetric_Monoid} :
    trB_decode (point (trB S)) = grpcplS_to_loopstrB .
  Proof.
    srapply @trB_ind_beta_bp.
  Defined.

  Definition trB_encodeisretr {S : Symmetric_Monoid} (x : trB S):
    Sect (trB_encode x) (trB_decode x).
  Proof.
    intro p.
    destruct p. simpl.
    (*This should be automatic if trB_ind was properly defined:*)
    refine (ap10 trB_decode_beta_bp (point (group_completion S)) @ _).
    unfold grpcplS_to_loopstrB. simpl.
    apply concat_pV.
  Defined.

  Definition trB_encodeissect {S : Symmetric_Monoid} (x : trB S) :
    Sect (trB_decode x) (trB_encode x).
  Proof.
    revert x.
    srapply @trB_ind.
    - intro m.
      rewrite (ap10 trB_decode_beta_bp m).
      revert m.
      srapply @Trunc_ind.
      srapply @Coeq_ind.
      + intros [a b].
        unfold trB_encode.
        simpl.
        refine (transport_pp (trB_code S) (trB_loop a) (trB_loop b)^ (point (group_completion S)) @ _).
        apply (moveR_transport_V (trB_code S)).
        refine (transport_code_is_mult a _ @ _ @ (transport_code_is_mult b _)^).
        apply (ap tr).
        refine ((cp (mon_id S + a, mon_id S + mon_id S, b))^ @ _).
        apply (ap coeq).
        apply path_prod.
        { simpl.
          refine (mon_assoc^ @ _).
          apply mon_lid. }
        { simpl.
          refine (mon_assoc ^ @ _).
          refine (mon_lid _ @ _).
          exact (mon_lid b @ (mon_rid b)^). }
      + intro abs.
        srapply @generalize_paths.        
    - intros m. unfold Sect.
      apply (trunc_forall (n := -1)).
    - intros m1 m2.
      srapply @generalize_paths.
  Defined.
  

  Definition equiv_pathstrB_code {S : Symmetric_Monoid} (x : trB S) :
    point (trB S) = x <~> trB_code S x :=
    equiv_adjointify (trB_encode x) (trB_decode x) (trB_encodeissect x) (trB_encodeisretr x).
  
  Definition equiv_loopstrB_group_completion (S : Symmetric_Monoid):
       loops (ptrB S) <~> group_completion S:=
    equiv_pathstrB_code (point (trB S)).
