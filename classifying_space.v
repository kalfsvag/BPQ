Require Import HoTT.
Require Import UnivalenceAxiom.
Load stuff.

Section Classifying_Space.
  Open Scope monoid_scope.
  (*Define the classifying space of a monoid as a cell complex*)

  (*The 1-skeleton of B.*)
  Definition B1 (M : Monoid)  := @Coeq M Unit (const tt) (const tt).
  
  (*B1 has one point:*)
  Global Instance ispointed_B1 {M : Monoid} : IsPointed (B1 M) := coeq tt.
  
  (*B1 has one loop for every m : M*)
  Definition B_loop1 {M : Monoid} : M -> point (B1 M) = point (B1 M) := cp.

  Definition B1_rec {M : Monoid}
             (P : Type)
             (bp : P)
             (l : forall m : M, bp = bp) :
    B1 M -> P.
    srapply @Coeq_rec.
    - exact (const bp). (*intros []. exact bp.*)
    - exact l.
  Defined.

  Definition B1_ind {M : Monoid}
             (P : B1 M -> Type) (bp : P (point (B1 M)))
             (loop' : forall (m : M), transport P (B_loop1 m) bp = bp)
             : forall a : B1 M, P a.
  Proof.
    srapply @Coeq_ind.
    - intros []. exact bp.
    - exact loop'.
  Defined.
  
  Definition looptofill (M : Monoid) (m1 m2 : M) : S1 -> B1 M.
    refine (S1_rec (B1 M) (point (B1 M)) _).
    exact ((B_loop1 m1) @ (B_loop1 m2) @ (B_loop1 (m1 + m2))^).
  Defined.

  Definition looptofill_curried (M : Monoid) : M*M*S1 -> B1 M :=
    prod_curry (prod_curry (looptofill M)).  
  
  Definition S1toB1 {M : Monoid} (m1 m2 : M) : S1 -> B1 M :=
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
  
(*  (*Not sure if this is needed. . .*)
  Definition path_to_other_pt {M : Monoid} (x : M * M * S1) : pushl x = point (B2 M) := pp x. *)

  Definition B1toB2 {M : Monoid} : B1 M -> B2 M := (push o inl).

  Global Instance ispointed_B2 {M : Monoid} : IsPointed (B2 M) := B1toB2 ispointed_B1.
  (*  Definition otherpt_B2 {M : Monoid} (m1 m2 : M) : B2 M := push (inr (m1, m2)).
  Definition path_to_otherpt_B2 {M : Monoid} (m1 m2 : M) : point (B2 M) = otherpt_B2 m1 m2 :=
    pp (m1, m2, base). *)

  Definition B_loop2 {M : Monoid} (m : M) : point (B2 M) = point (B2 M) :=
    ap B1toB2 (B_loop1 m).

(*  Definition nullhom_S1toB2' {M : Monoid} (m1 m2 : M) :
    B1toB2 o (S1toB1 m1 m2) == const (otherpt_B2 m1 m2).
  Proof.
    intro x.
    exact (pp (m1, m2, x)).
  Defined. *)

  Definition nullhom_S1toB2 {M : Monoid} (m1 m2 : M) :
    B1toB2 o (S1toB1 m1 m2) == (fun _ : S1 => B1toB2 (S1toB1 m1 m2 base)) .
  Proof.
    intro x.
    refine (concat (pp (m1, m2, x)) _).
    exact (pp (m1, m2, base))^. (*Weirdly enough, putting this inside the concat doesn't work. . .*)
  Defined.


  Definition const_S1toB2 `{Funext} {M : Monoid} (m1 m2 : M) :
    B1toB2 o (S1toB1 m1 m2) = (fun _ : S1 => B1toB2 (S1toB1 m1 m2 base)) :=
    path_forall _ _ (nullhom_S1toB2 m1 m2).

  

  Definition ishom_MtoB2 `{Funext} {M : Monoid} (m1 m2: M) :
     B_loop2 m1 @ B_loop2 m2 = B_loop2 (m1 + m2).
  Proof.
    unfold B_loop2.
    apply moveL_1M.
    refine (whiskerR (ap_pp B1toB2 _ _)^ _ @ _).
    refine (whiskerL _ (ap_V B1toB2 _)^ @ _).
    refine ((ap_pp B1toB2 _ _)^ @ _).
    refine (ap02 _ (S1_rec_beta_loop _ _ _)^ @ _).
    refine ((ap_compose _ _ _)^ @ _).
    refine (_ @ ap_const loop (B1toB2 (S1toB1 m1 m2 base))) .
    refine (_ @ ap12 loop (const_S1toB2 m1 m2)).
    change
      (S1_rec (Coeq (const tt) (const tt)) (coeq tt)
              ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (m1 + m2))^)) with
    (S1toB1 m1 m2).
    assert (p : (ap10 (const_S1toB2 m1 m2) base) = idpath).
    { refine ((ap10_path_forall _ _ (nullhom_S1toB2 m1 m2) _) @ _).
      apply concat_pV. }
    refine (_ @ whiskerL _ p^).
    refine (_ @ (concat_p1 _ )^).
    refine (_ @ whiskerR (inverse2 p)^  _).
    exact (concat_1p _)^.
  Defined.                          

  Definition B2_rec {M : Monoid}
             (P : Type)
             (bp : P)
             (l : M -> bp = bp)
             (h : forall m1 m2 : M, l m1 @ l m2 = l (m1 + m2) ) :
    B2 M -> P.
    (*B2 is the pushout of B1 M and M*M*S1*)
    srapply @pushout_rec.
    - apply sum_rect.      
      + (*The map defined on B1 is given by l*)
        exact (B1_rec _ bp l).
        (*The map on M*M*S1 is the constant map (it gives the loops that will be killed)*)
      + exact (const bp).
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
        unfold B1_rec.
        refine (concat (y := 1^) (inverse2 _) idpath). (*This feels stupid. . .*)
        refine (ap_compose _ _ _ @ _).
        refine (concat (y:= ap (Coeq_rec P (const bp) l)
                               ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (m1 + m2))^) ) _ _).
        { apply (ap (ap _)). apply S1_rec_beta_loop. }
        refine (ap_pp _ _ _ @ _).
        refine (whiskerR (ap_pp _ _ _) _ @ _).
        refine (whiskerL _ (ap_V _ _) @ _).
        apply moveR_pV.
        refine (_ @ (concat_1p _)^).
        unfold B_loop1.
        refine (_ @ (Coeq_rec_beta_cp P (const bp) l (m1 + m2))^).
        refine (_ @ h m1 m2).
        apply concat2; refine (Coeq_rec_beta_cp P (const bp) l _).
  Defined.

  (*Should probably switch to lean or implement pathovers here. . .*)
  Definition B2_ind {M : Monoid}
             (P : B2 M -> Type)
             (bp : P (point (B2 M)))
             (l : forall (m : M), transport P (B_loop2 m) bp = bp)
             (h : forall (m1 m2 : M),
                    transport
                      (fun pth => transport P pth bp = bp)
                      (ishom_MtoB2 m1 m2)
                      (transport_pp P (B_loop2 m1) (B_loop2 m2) bp @
                                    ap (transport P (B_loop2 m2)) (l m1) @ (l m2))
                    = l (m1 + m2))
             : forall a : B2 M, P a.
    srapply @pushout_ind.
    - apply sum_ind.
      + srapply @B1_ind.
        * (*Variable is basepoint*)
          exact bp.
        * (*Variable runs along B_loop2*)
          intro m.
          refine (transport_compose P (push o inl) (B_loop1 m) bp @ _).
          exact (l m).
      + (*Variable is hub point*)
        intros [m1 m2].
        exact (transport P (pp (m1, m2, base)) bp).
    - intros [[m1 m2]].
      srapply @S1_ind.
      + reflexivity.
      + (*Variable runs along ishom (I think. . . )*)
        cbn.

        (* dpath_path_FlFr *)
        (* transport_paths_FlFr_D *)
        refine (transport_paths_Fl loop idpath  @ _).
        (*apD_const?*)
        apply moveR_Vp.
        refine (_ @ (concat_p1 _)^).
        
        set (Pl := fun a : B1 M => P (push (inl a))).

        set (f :=
               (fun x : S1 =>
                  transport
                    P (pp (m1, m2, x))
                    (B1_ind
                       Pl bp
                       (fun m : M =>
                          transport_compose P (fun x0 : B1 M => push (inl x0)) 
                                            (B_loop1 m) bp @ l m) (looptofill_curried M (m1, m2, x))))).
        change (fun x : S1 =>
                  transport
                    P (pp (m1, m2, x))
                    (B1_ind
                       Pl bp
                       (fun m : M =>
                          transport_compose P (fun x0 : B1 M => push (inl x0)) 
                                            (B_loop1 m) bp @ l m) (looptofill_curried M (m1, m2, x))))
               with f.
        unfold pushr in f. unfold collapseS1 in f.
        apply (cancelL (transport_const loop (f base)) _ _).
        refine (concat_p1 _ @ _).
        refine (_ @ apD_const f loop).
        apply inverse.
        
        








        
        
        Eval compute in (f base).
        

        

        assert (forall x : S1, P (pushr (m1, m2, x)) -> P (pushl (m1, m2, base))).
        { intro x. refine (_ o transport P (pp (m1, m2, x))^ ).
          revert x.
          srapply @S1_ind.
            exact idmap.
            apply path_forall. intro.
            refine ((transport_arrow
                       (B := fun x => P (pushl (m1, m2, x)))
                       (C := fun _ => P (pushl (m1, m2, base))) loop idmap _ )@ _).
            
        
        
        unfold pushr in f. unfold collapseS1 in f.
        enough
          (ap (transport P (pp (m1, m2, base))^) 1 = ap (transport P (pp (m1, m2, base))^) (ap f loop)).
        apply ((ap (transport P (pp (m1, m2, base))^))^-1 X).
        
        refine ((ap (transport P (pp (m1, m2, base))^))^-1 _).
        


        assert ((fun x : S1 => transport P (pp (m1, m2, x))^ (f x)) ==
               B1_ind (fun a : B1 M => P (push (inl a))) bp
                        (fun m : M =>
                           transport_compose P (fun x0 : B1 M => push (inl x0)) 
                                             (B_loop1 m) bp @ l m) o (looptofill M m1 m2)).
          { intro x.
            unfold f. refine ((transport_pp P _ _ _)^ @ _).
            refine (transport2 P (q := idpath) (concat_pV _) _ @ _).
            exact (transport_1 P _ ). }
          
        
        
          
        transitivity ((transport_const _ _)^ @ (apD f loop)).
        * apply moveL_Vp.
          refine (concat_p1 _ @ _).
          apply inverse.
          unfold looptofill_curried in f. unfold prod_curry in f. simpl in f.
          refine ((concat_1p _)^ @ _).
          refine (whiskerR  (concat_Vp (transport_compose _ _ _ _))^ (apD f loop) @ _). Unshelve.

          @ (concat_1p _)).
          

          
          
          
          enough (transporttoright : forall x : S1, P (pushl (m1, m2, x)) -> P (pushr (m1, m2, x))).

          apD_compose
          (*rewrite B1_beta?*)
          enought (forall x : S1, P (pushr (m1, m2, x))

                                    
          
          
          admit.
            intro x. exact (transport P (pp (m1, m2, x))).
          unfold pushr in f. unfold collapseS1 in f. 
          
          
          
        * apply moveR_Vp.
          srapply @apD_const.





          
        refine (_ @ (moveR_Vp _ _ _ (apD_const _ _))).
        

        
        apply inverse.
        
        set (Pl := (fun a : B1 M => P (push (inl a))) ).
        change (fun a : B1 M => P (push (inl a))) with Pl.
        set (lm := (fun m : M =>
                    transport_compose P (fun x0 : B1 M => push (inl x0)) (B_loop1 m) bp @ l m) ).
        change (fun m : M =>
                    transport_compose P (fun x0 : B1 M => push (inl x0)) (B_loop1 m) bp @ l m) with lm.
        unfold looptofill_curried.
        unfold prod_curry.
        unfold looptofill.
        simpl.
        
        
        
        refine (concat
                  (ap_compose
                     (S1_rec (B1 M) (point (B1 M))
                             ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (m1 + m2))^) )
                      _ loop
                  )
                  _ ).
        
        
        
        refine (ap_compose _ (transport P (pp (m1, m2, x))) loop @ _).
        
        
          
    
    refine (pushout_ind _ _ _ _ _).
    - apply sum_ind.
      + refine (B1_ind _ _ _).
        * exact bp.
        * intro m.
          refine (concat
                    (transport_compose P (push o inl)
                                       (B_loop1 m)
                                       bp )
                    _
                 ).
          apply ident.
      + intros [m1 m2].
        exact (transport P (pp (m1, m2, base)) bp).
    - intros [[m1 m2]].
      refine (S1_ind _ _ _).
      + exact idpath.
      + cbn.
        refine (concat
                  (transport_paths_Fl loop idpath)
                  _
               ).
        apply moveR_Vp.
        refine (concat _ (concat_p1 _)^).
        apply inverse.
        unfold looptofill.
        

          
        unfold B_loop1.

        refine (concat
                  (ap_compose
                     (S1_rec (B1 M) (point (B1 M))
                             ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (multM m1 m2))^) )
                      _ loop
                  )
                  _ ).
        
               
                  
        unfold B1_ind.
        
        

   Admitted.


(*TODO: Use ap11. ap_apply_FlFr ap_to_conjp transport2
*)

(*TODO*) (*
  Global Instance ispointed_S1 : IsPointed S1 := base.
  Definition pS1 := Build_pType S1 _.
  Definition pB1 (M : Monoid) := Build_pType (B1 M) _.
  Definition pB2 (M : Monoid) := Build_pType (B2 M) _.
  Definition pS1toB1 {M : Monoid} (m1 m2 : M) :=
    Build_pMap pS1 (pB1 M) (S1toB1 m1 m2) idpath.
  Definition pB1toB2 {M : Monoid} (m1 m2 : M) : pB1 M ->* pB2 M :=
    Build_pMap (pB1 M) (pB2 M) (B1toB2) idpath.
 
  Lemma pconst_S1toB2 `{Funext} (M : Monoid) (m1 m2 : M) :
    (pB1toB2 m1 m2) o* (pS1toB1 m1 m2) = pconst pS1 (pB2 M).
  Proof.
    apply path_pmap.
    refine (Build_pHomotopy _ _).
    intro x.
    simpl.
    unfold const. unfold point. unfold ispointed_B2. unfold B1toB2. unfold ispointed_B1.
    refine (concat _ (pp ispointed_MMS1)^).
    apply (constant_S1toB2 x).
    - cbn.
      unfold constant_S1toB2.
      hott_simpl.
      apply moveR_pV.
      hott_simpl.
      unfold ispointed_MMS1.
      unfold ispointed_S1.
      
      apply (concat (concat_p1 _) (concat_1p _)^ ).
  Defined.

  Definition pmap_to_loops {A B : pType} (l : loops A) :
    (A ->* B) -> loops B :=
    fun f => (point_eq f)^ @ (ap f l) @ (point_eq f).

  (*TODO: Use this to make the proof below simpler?*)
*)
  
  Definition monid_to_idpath2 `{Funext} {M : Monoid} : B_loop2 (mon_id M) = idpath.
    apply (cancelL (B_loop2 (mon_id M)) _ _).
    refine (concat (isHom_MtoB2 _ _)^ _).
    refine (concat _ (concat_p1 _)^).
    apply (ap B_loop2).
    apply mon_lid.
  Defined.

  Definition B (M : Monoid) := Tr 1 (B2 M).

  Global Instance ispointed_B {M : Monoid} : IsPointed (B M) := tr (point (B2 M)).

  Definition B_loop {M : Monoid} (m : M) : point (B M) = point (B M) := ap tr (B_loop2 m).
  Definition isHom_MtoB `{Funext} {M : Monoid} (m1 m2: M) :
    (B_loop (multM m1 m2)) = ((B_loop m1) @ (B_loop m2)).
    refine (concat _ (ap_pp tr _ _)).
    apply (ap (ap tr)).
    apply isHom_MtoB2.
  Defined.

  Definition monid_to_idpath `{Funext} {M : Monoid} : B_loop (mon_id M) = idpath.
    unfold B_loop.
    refine (concat _ (ap_1 _ tr)).
    apply (ap (ap tr)).
    apply monid_to_idpath2.
  Defined.

  Definition B_rec {M : Monoid}
             (P : Type) (istrunc : IsTrunc 1 P)
             (bp : P)
             (loop' : forall m : M, bp = bp)
             (ishom : forall m1 m2 : M, loop' (multM m1 m2) = loop' m1 @ loop' m2) : B M -> P.
  Proof.
    apply Trunc_rec.
    refine (pushout_rec _ _ _).
    - apply sum_rect.
      + (*What B1 is mapped to*)
        refine (Coeq_rec _ _ _).
        * exact (unit_name bp).
        * exact loop'.
      + exact (unit_name bp). (*
        apply Unit_rec.
        exact bp.*)
    - (*This corresponds to showing that we have a homomorphism*)
      intros [[m1 m2]].
      refine (S1_ind _ idpath _).
      refine (concat (transport_paths_Fl loop idpath) _).
      apply moveR_Vp.
      refine (concat _ (concat_p1 _)^).
      refine (concat _
              (ap_compose
               (S1_rec (B1 M) (point (B1 M)) ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (multM m1 m2))^))
               (Coeq_rec P (unit_name bp) loop')
               loop )^
             ).
      refine (concat _
                     (ap
                        (ap (Coeq_rec P (unit_name bp) loop'))
                        (S1_rec_beta_loop _ _ _)^
                      )).
      refine (concat _ (ap_pp _ _ _)^).
      apply moveL_pM.
      refine (concat (concat_1p _) _).
      refine (concat (ap_V _ _)^ _).
      refine (concat (ap
                        (ap (Coeq_rec P (unit_name bp) loop'))
                        (inv_V (B_loop1 (multM m1 m2)))
                      ) _ ).      
      refine (concat (Coeq_rec_beta_cp P (unit_name bp) loop' (multM m1 m2)) _).
      refine (concat _ (ap_pp _ _ _)^).
      refine (concat (ishom m1 m2) _).
      apply concat2.
      + exact (Coeq_rec_beta_cp P (unit_name bp) loop' m1)^.
      + exact (Coeq_rec_beta_cp P (unit_name bp) loop' m2)^.
  Defined.

  Definition B_ind {M : Monoid}
             (P : B M -> Type) (istrunc : forall (a : B M), IsTrunc 1 (P a))
             (bp : P (point (B M)))
             (loop' : forall (m : M), transport P (B_loop m) bp = bp)
             
             : forall a : B M, P a.
    apply Trunc_ind.
    exact istrunc.
    refine (pushout_ind _ _ _ _ _).
    - apply sum_ind.
      + refine (B1_ind _ _ _).
        * exact (transport (P o tr) (pp ispointed_MMS1)^ bp).
        * intro m.
          refine (concat
                    (transport_compose (P o tr) (push o inl)
                                       (B_loop1 m)
                                       (transport (P o tr) (pp ispointed_MMS1)^ bp) )
                    _
                 ).

          refine (concat (transport_pp _ _ _ _)^ _).
          refine (moveL_transport_V (P o tr) _ _ _ _).
          refine (concat (transport_pp _ _ _ _)^ _).
          refine (concat
                    (transport_compose P tr _ _)
                    _ ).
          apply loop'.
      + intros []. exact bp.
    - simpl.
      intros [[m1 m2]].
      refine (S1_ind _ _ _).
      + simpl.
        change (pushout looptofill (const tt)) with (B2 M).
        refine (moveR_transport_p (P o tr) _ _ _ _).
        refine (concat
                  (transport_compose P tr _ _)
                  _ ).
        refine (concat
                  _
                  (transport_compose P tr _ _)^ ).
        apply transport2.
        apply (ap (ap tr)).

  Admitted.        
        

    
  
End Classifying_Space.



Section B2_coeq.
  Definition l12 {M : Monoid} : M * M * S1 -> B1 M.
    intros [[m1 m2]].
    refine (S1_rec (B1 M) (point _) _).
    exact (B_loop1 (multM m1 m2)).
  Defined.

  Definition l1l2 {M : Monoid} : M * M * S1 -> B1 M.
    intros [[m1 m2]].
    refine (S1_rec (B1 M) (point _) _).
    exact ((B_loop1 m1) @ (B_loop1 m2)).
  Defined.

  Definition l12_beta {M : Monoid} (m1 m2 : M) :
    ap (fun x : S1 => l12 (m1, m2, x)) loop = B_loop1 (multM m1 m2) := S1_rec_beta_loop _ _ _.

  Definition l1l2_beta {M : Monoid} (m1 m2 : M) :
    ap (fun x : S1 => l1l2 (m1, m2, x)) loop = ((B_loop1 m1) @ (B_loop1 m2)) := S1_rec_beta_loop _ _ _.
  
  Definition B2' (M : Monoid) := Coeq (@l12 M) l1l2.

  Definition B1toB2' {M : Monoid} : B1 M -> B2' M := coeq.
  Global Instance ispointed_B2' {M : Monoid} : IsPointed (B2' M) := B1toB2' (point (B1 M)).
    
  (*TODO: Bruke transport i stedet?*)
  Definition B_loop2' {M : Monoid} (m : M) : point (B2' M) = point (B2' M) :=  ap B1toB2' (B_loop1 m).

  Definition isHom_MtoB2' `{Funext} {M : Monoid} (m1 m2: M) :
    (B_loop2' (multM m1 m2)) = ((B_loop2' m1) @ (B_loop2' m2)).
  Proof.
    unfold B_loop2'.
    refine (concat _ (ap_pp B1toB2' _ _) ).
    rewrite <- (l12_beta m1 m2).
    rewrite <- (l1l2_beta m1 m2).
    refine (concat (ap_compose (fun x : S1 => l12 (m1, m2, x)) B1toB2' loop)^ _ ).
    refine (concat  _ (ap_compose (fun x : S1 => l1l2 (m1, m2, x)) B1toB2' loop)).
    
    change (B_loop1 (multM m1 m2)) with 
    unfold B_loop1.
    
    unfold B1toB2'.
    

    

(*Prove that B nat <~> Int*)
Section Classifying_Space_Nat.
  Definition BN := B (nat_monoid).

  (*Bruke equiv_loopsS1_int ?*)

  Definition lBN_to_Z : loops (Build_pType BN _) -> Int.
Abort.
(*    Sn_trunctype:
  Univalence -> forall n : trunc_index, IsTrunc n.+1 {x : _ & IsTrunc n x}
   path_sigma_uncurried
   hprop_trunc
   trunc_arrow
 *)

    refine (paths_rec (point (BN)) (fun _ => Int) Int.zero _). (*This is constant. P must be a bit more refined. loop => +1 : Z=Z*)























    (fun m1 => forall m2 : Trunc 0 (Coeq (as_bs S) fst),
                                       Trunc_rec
                                         (Coeq_rec (mon_set (grp_mon (grp A)))
                                                   (fun m12 : mon_set (mon S) * mon_set (mon S) =>
                                                      mon_map f (fst m12) + grp_inv (mon_map f (snd m12)))
                                                   (fun b : mon_set (mon S) * mon_set (mon S) * mon_set (mon S) =>
                                                      ap
                                                        (fun c : mon_set (grp_mon (grp A)) =>
                                                           c +
                                                           grp_inv
                                                             (mon_map f
                                                                      ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                       (let (_, snd) := b in snd))))
                                                        (preserve_mult f (let (fst, _) := let (fst, _) := b in fst in fst)
                                                                       (let (_, snd) := b in snd)) @
                                                        ((mon_assoc
                                                            (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst))
                                                            (mon_map f (let (_, snd) := b in snd))
                                                            (grp_inv
                                                               (mon_map f
                                                                        ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                         (let (_, snd) := b in snd)))))^ @
                                                                                                           ap
                                                                                                           (mon_mult
                                                                                                              (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst)))
                                                                                                           (grp_moveR_gV
                                                                                                              (grp_moveL_Vg
                                                                                                                 (preserve_mult f
                                                                                                                                (let (_, snd) := let (fst, _) := b in fst in snd)
                                                                                                                                (let (_, snd) := b in snd))^)))))
                                         (grp_compl_mult S m1 m2) =
                                       Trunc_rec
                                         (Coeq_rec (mon_set (grp_mon (grp A)))
                                                   (fun m12 : mon_set (mon S) * mon_set (mon S) =>
                                                      mon_map f (fst m12) + grp_inv (mon_map f (snd m12)))
                                                   (fun b : mon_set (mon S) * mon_set (mon S) * mon_set (mon S) =>
                                                      ap
                                                        (fun c : mon_set (grp_mon (grp A)) =>
                                                           c +
                                                           grp_inv
                                                             (mon_map f
                                                                      ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                       (let (_, snd) := b in snd))))
                                                        (preserve_mult f (let (fst, _) := let (fst, _) := b in fst in fst)
                                                                       (let (_, snd) := b in snd)) @
                                                        ((mon_assoc
                                                            (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst))
                                                            (mon_map f (let (_, snd) := b in snd))
                                                            (grp_inv
                                                               (mon_map f
                                                                        ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                         (let (_, snd) := b in snd)))))^ @
                                                                                                           ap
                                                                                                           (mon_mult
                                                                                                              (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst)))
                                                                                                           (grp_moveR_gV
                                                                                                              (grp_moveL_Vg
                                                                                                                 (preserve_mult f
                                                                                                                                (let (_, snd) := let (fst, _) := b in fst in snd)
                                                                                                                                (let (_, snd) := b in snd))^))))) m1 +
                                       Trunc_rec
                                         (Coeq_rec (mon_set (grp_mon (grp A)))
                                                   (fun m12 : mon_set (mon S) * mon_set (mon S) =>
                                                      mon_map f (fst m12) + grp_inv (mon_map f (snd m12)))
                                                   (fun b : mon_set (mon S) * mon_set (mon S) * mon_set (mon S) =>
                                                      ap
                                                        (fun c : mon_set (grp_mon (grp A)) =>
                                                           c +
                                                           grp_inv
                                                             (mon_map f
                                                                      ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                       (let (_, snd) := b in snd))))
                                                        (preserve_mult f (let (fst, _) := let (fst, _) := b in fst in fst)
                                                                       (let (_, snd) := b in snd)) @
                                                        ((mon_assoc
                                                            (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst))
                                                            (mon_map f (let (_, snd) := b in snd))
                                                            (grp_inv
                                                               (mon_map f
                                                                        ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                         (let (_, snd) := b in snd)))))^ @
                                                                                                           ap
                                                                                                           (mon_mult
                                                                                                              (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst)))
                                                                                                           (grp_moveR_gV
                                                                                                              (grp_moveL_Vg
                                                                                                                 (preserve_mult f
                                                                                                                                (let (_, snd) := let (fst, _) := b in fst in snd)
                                                                                                                                (let (_, snd) := b in snd))^))))) m2
                          )