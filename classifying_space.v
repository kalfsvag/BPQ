Load group_completion.
(* Load monoids_and_groups. *)

(*TODO: Make M not implicit. Use 1%nat_scope*)
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

  Definition B1_rec_beta_l {M : Monoid}
             (P : Type)
             (bp : P)
             (l : forall m : M, bp = bp)
             (m : M):
    ap (B1_rec P bp l) (B_loop1 m) = l m :=
    Coeq_rec_beta_cp P (const bp) l m.

  Definition B1_ind {M : Monoid}
             (P : B1 M -> Type) (bp : P (point (B1 M)))
             (loop' : forall (m : M), transport P (B_loop1 m) bp = bp)
             : forall a : B1 M, P a.
  Proof.
    srapply @Coeq_ind.
    - intros []. exact bp.
    - exact loop'.
  Defined.


  Definition B1_ind_beta_l {M : Monoid}
             (P : B1 M -> Type) (bp : P (point (B1 M)))
             (loop' : forall (m : M), transport P (B_loop1 m) bp = bp)
             (m : M) :
    apD (B1_ind P bp loop') (B_loop1 m) = loop' m
    :=
      Coeq_ind_beta_cp P _ loop' m.

  
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

  Definition B2_rec_beta_l {M : Monoid}
             (P : Type)
             (bp : P)
             (l : M -> bp = bp)
             (h : forall m1 m2 : M, l m1 @ l m2 = l (m1 + m2) )
             (m : M):
    ap (B2_rec P bp l h) (B_loop2 m) = l m.
  Proof.
    unfold B2_rec. unfold B_loop2. unfold B1toB2.
    Admitted.
  

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
    (*Weird try : go via sigma types*)
    (* apply section_to_depfun. *)
    (* esplit. *)
    (* Unshelve. *)
    (* admit. *)
    (* srapply @B2_rec. *)
    (*   -(*The basepoint goes to. . .*) *)
    (*     exists (point (B2 M)). exact bp. *)
    (*   - (*B_loop goes to. . .*) *)
    (*     intro m. *)
    (*     srapply @path_sigma. *)
    (*       exact (B_loop2 m). *)
    (*       exact (l m). *)
    (*   - intros m1 m2. simpl. *)
    (*     refine ((path_sigma_pp_pp P _ _ _ _)^ @ _). *)
    (*     srapply @path2_sigma. *)
    (*      + apply ishom_MtoB2. *)
    (*      + simpl. *)
    (*        refine (transport_paths_Fl (ishom_MtoB2 m1 m2)  _  @ _). *)
    (*        apply moveR_Vp. *)
    (*        apply inverse. *)
    (*        apply moveR_pM. *)
    (*        admit. *)
    (*        Unshelve. *)

    (*     refine (_ @ inv_V _). *)
    (*     refine (_ @ (ap inverse (path_sigma_V ) *)
        

    (*     (*Todo: path_sigma_V*) *)
        
    (*     apply moveL_1M. *)
    (*     refine ((path_sigma_pp_pp P _ _ _ _)^ @ _). *)
          
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
        set (restriction_to_B1 := (B1_ind
                                     (fun a : B1 M => P (push (inl a))) bp
                                     (fun m : M =>
                                        transport_compose P (fun x0 : B1 M => push (inl x0)) 
                                                          (B_loop1 m) bp @ l m))).
        (*Try to simplify now, didn't become simpler. . .
        refine (transport_PequivQ
                  (fun x => equiv_moveL_transport_V
                              P (pp (m1, m2, x))
                              (restriction_to_B1 (looptofill_curried M (m1, m2, x)))
                              _)
                  loop idpath @ _).
        apply moveR_equiv_V.
        cbn. unfold equiv_inv.
        apply moveL_Vp.
        *)
                                         

        (* refine (transport_paths_FlFr_D *)
        (*           (f := fun x => transport P (pp (m1, m2, x)) *)
        (*                                    (restriction_to_B1 (looptofill M m1 m2 x))) *)
        (*           (g := const (transport P (pp (m1, m2, base)) bp)) *)
        (*           loop idpath @ _). *)
        (* apply moveR_pM. *)
        (* refine (_ @ (concat_1p _)^). *)
        
        
        (* apply moveR_Vp. *)
        (* transitivity (idpath (transport P (pp (m1, m2, base)) bp)). *)



        
        (* refine (transport_paths_FlFr_D loop idpath @ _). *)

        (* dpath_path_FlFr *)
        (* transport_paths_FlFr_D *)
        
        simpl in restriction_to_B1. unfold looptofill_curried. unfold prod_curry. simpl.


        (* moveR_transport_p *)
        (*   ap01D1 *)
          
        (* refine (transport_composeD *)
        (*           (fun x : S1 => (restriction_to_B1 (looptofill M m1 m2 x)) = *)
        (*                          transport P (pp (m1, m2, x))^ *)
        (*                                    (transport P (pp (m1, m2, base)) bp)) *)
                  
        (*           (fun x => moveR_transport_p P (pp (m1, m2, x)) *)
        (*                                       (restriction_to_B1 (looptofill M m1 m2 x)) *)
        (*                                       (transport P (pp (m1, m2, base)) bp) ) *)
                                 
                                 
                                 
                                 
        (*           (fun x b => transport P (pp (m1, m2, x)) *)
        (*                                 (restriction_to_B1 b) = *)
        (*                       transport P (pp (m1, m2, base)) bp) *)
        (*           (fun x => looptofill M m1 m2 x) *)
        (*           loop idpath *)
        (*           @ _). *)
        (* Unshelve. *)
        (* Focus 2. *)
        (*   intros x b. *)
        (*   exact (transport P (pp (m1, m2, x))  *)
        (*                    (restriction_to_B1 b) = *)
        (*          transport P (pp (m1, m2, base)) bp) . *)
          
                  
                  
        refine (transport_paths_Fl loop idpath  @ _).
        (*apD_const?*)
        apply moveR_Vp.
        refine (_ @ (concat_p1 _)^).
        
        
        
        change (fun x : S1 =>
                  transport
                    P (pp (m1, m2, x))
                    (restriction_to_B1 (looptofill M m1 m2 x)))
               with
               (composeDD (fun x => transport P (pp (m1, m2, x)))
                          (composeD restriction_to_B1 (looptofill M m1 m2))) .
        
        (* enough (ap_S1 : *)
        (*           ap (looptofill M m1 m2) loop = ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (m1 + m2))^)). *)
        (* enough (ap_B1 : *)
        (*           apD (restriction_to_B1 oD looptofill M m1 m2) loop = *)
        (*           transport_compose _ _ _ _ @ *)
        (*              apD restriction_to_B1 ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (m1 + m2))^)). *)


        (* admit. *)
        (* apply S1_rec_beta_loop. *)
        
        
        
        (* refine (_ @ moveR_Vp (apD_const (composeDD (fun x : S1 => transport P (pp (m1, m2, x))) *)
        (*                                            (restriction_to_B1 oD looptofill M m1 m2)) loop)). *)
        
        
          
        transitivity ((transport_const _ _)^ @
                      (apD (composeDD (fun x : S1 => transport P (pp (m1, m2, x)))
                           (restriction_to_B1 oD looptofill M m1 m2)) loop)).
        * apply moveL_Vp.
          refine (concat_p1 _ @ _).
          apply inverse.
          

          
          refine (apD_composeDD _ _ loop @ _).
          apply moveR_Mp.

          (* transitivity (apD011 (fun x : S1 => transport P (pp (m1, m2, x))) loop *)
          (*                 (apD restriction_to_B1 ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (m1 + m2))^)) *)
          (*                 ). *)
          (* apD_compose *)
          (*rewrite B1_beta?*)
          
          admit.
        * apply moveR_Vp.
          srapply @apD_const.
  Admitted.

  




(*Alternative way to write g:*)                             
                          (* (fun x => *)
                          (*    B1_ind *)
                          (*    (fun a : B1 M => P (push (inl a))) bp *)
                          (*    (fun m : M => *)
                          (*       transport_compose P (fun x0 : B1 M => push (inl x0))  *)
                          (*                         (B_loop1 m) bp @ l m) (looptofill M m1 m2 x))). *)
                                      
                                           
        (* set (Pl := fun a : B1 M => P (push (inl a))). *)
        

        (* set (f := *)
        (*        (fun x : S1 => *)
        (*           transport *)
        (*             P (pp (m1, m2, x)) *)
        (*             (B1_ind *)
        (*                Pl bp *)
        (*                (fun m : M => *)
        (*                   transport_compose P (fun x0 : B1 M => push (inl x0))  *)
        (*                                     (B_loop1 m) bp @ l m) (looptofill_curried M (m1, m2, x))))). *)
        (* change (fun x : S1 => *)
        (*           transport *)
        (*             P (pp (m1, m2, x)) *)
        (*             (B1_ind *)
        (*                Pl bp *)
        (*                (fun m : M => *)
        (*                   transport_compose P (fun x0 : B1 M => push (inl x0))  *)
        (*                                     (B_loop1 m) bp @ l m) (looptofill_curried M (m1, m2, x)))) *)
        (*        with f. *)
        (* unfold pushr in f. unfold collapseS1 in f. *)
        (* apply (cancelL (transport_const loop (f base)) _ _). *)
        (* refine (concat_p1 _ @ _). *)
        (* refine (_ @ apD_const f loop). *)
        (* apply inverse. *)
        
        








        
        
        (* Eval compute in (f base). *)
        

        

        (* assert (forall x : S1, P (pushr (m1, m2, x)) -> P (pushl (m1, m2, base))). *)
        (* { intro x. refine (_ o transport P (pp (m1, m2, x))^ ). *)
        (*   revert x. *)
        (*   srapply @S1_ind. *)
        (*     exact idmap. *)
        (*     apply path_forall. intro. *)
        (*     refine ((transport_arrow *)
        (*                (B := fun x => P (pushl (m1, m2, x))) *)
        (*                (C := fun _ => P (pushl (m1, m2, base))) loop idmap _ )@ _). *)
            
        
        
        (* unfold pushr in f. unfold collapseS1 in f. *)
        (* enough *)
        (*   (ap (transport P (pp (m1, m2, base))^) 1 = ap (transport P (pp (m1, m2, base))^) (ap f loop)). *)
        (* apply ((ap (transport P (pp (m1, m2, base))^))^-1 X). *)
        
        (* refine ((ap (transport P (pp (m1, m2, base))^))^-1 _). *)
        


        (* assert ((fun x : S1 => transport P (pp (m1, m2, x))^ (f x)) == *)
        (*        B1_ind (fun a : B1 M => P (push (inl a))) bp *)
        (*                 (fun m : M => *)
        (*                    transport_compose P (fun x0 : B1 M => push (inl x0))  *)
        (*                                      (B_loop1 m) bp @ l m) o (looptofill M m1 m2)). *)
        (*   { intro x. *)
        (*     unfold f. refine ((transport_pp P _ _ _)^ @ _). *)
        (*     refine (transport2 P (q := idpath) (concat_pV _) _ @ _). *)
        (*     exact (transport_1 P _ ). } *)
          
        
          
   (*      refine (_ @ (moveR_Vp _ _ _ (apD_const _ _))). *)
        

        
   (*      apply inverse. *)
        
   (*      set (Pl := (fun a : B1 M => P (push (inl a))) ). *)
   (*      change (fun a : B1 M => P (push (inl a))) with Pl. *)
   (*      set (lm := (fun m : M => *)
   (*                  transport_compose P (fun x0 : B1 M => push (inl x0)) (B_loop1 m) bp @ l m) ). *)
   (*      change (fun m : M => *)
   (*                  transport_compose P (fun x0 : B1 M => push (inl x0)) (B_loop1 m) bp @ l m) with lm. *)
   (*      unfold looptofill_curried. *)
   (*      unfold prod_curry. *)
   (*      unfold looptofill. *)
   (*      simpl. *)
        
        
        
   (*      refine (concat *)
   (*                (ap_compose *)
   (*                   (S1_rec (B1 M) (point (B1 M)) *)
   (*                           ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (m1 + m2))^) ) *)
   (*                    _ loop *)
   (*                ) *)
   (*                _ ). *)
        
        
        
   (*      refine (ap_compose _ (transport P (pp (m1, m2, x))) loop @ _). *)
        
        
          
    
   (*  refine (pushout_ind _ _ _ _ _). *)
   (*  - apply sum_ind. *)
   (*    + refine (B1_ind _ _ _). *)
   (*      * exact bp. *)
   (*      * intro m. *)
   (*        refine (concat *)
   (*                  (transport_compose P (push o inl) *)
   (*                                     (B_loop1 m) *)
   (*                                     bp ) *)
   (*                  _ *)
   (*               ). *)
   (*        apply ident. *)
   (*    + intros [m1 m2]. *)
   (*      exact (transport P (pp (m1, m2, base)) bp). *)
   (*  - intros [[m1 m2]]. *)
   (*    refine (S1_ind _ _ _). *)
   (*    + exact idpath. *)
   (*    + cbn. *)
   (*      refine (concat *)
   (*                (transport_paths_Fl loop idpath) *)
   (*                _ *)
   (*             ). *)
   (*      apply moveR_Vp. *)
   (*      refine (concat _ (concat_p1 _)^). *)
   (*      apply inverse. *)
   (*      unfold looptofill. *)
        

          
   (*      unfold B_loop1. *)

   (*      refine (concat *)
   (*                (ap_compose *)
   (*                   (S1_rec (B1 M) (point (B1 M)) *)
   (*                           ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (multM m1 m2))^) ) *)
   (*                    _ loop *)
   (*                ) *)
   (*                _ ). *)
        
               
                  
   (*      unfold B1_ind. *)
        
        

   (* Admitted. *)


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
    refine (concat (ishom_MtoB2 _ _) _).
    refine (concat _ (concat_p1 _)^).
    apply (ap B_loop2).
    apply mon_lid.
  Defined.

  Definition B (M : Monoid) := Tr 1 (B2 M).

  Global Instance ispointed_B {M : Monoid} : IsPointed (B M) := tr (point (B2 M)).

  Definition B_loop {M : Monoid} (m : M) : point (B M) = point (B M) := ap tr (B_loop2 m).
  Definition ishom_MtoB `{Funext} {M : Monoid} (m1 m2: M) :
    (B_loop m1) @ (B_loop m2) = B_loop (m1 + m2).
    refine (concat (ap_pp tr _ _)^ _).
    apply (ap (ap tr)).
    apply ishom_MtoB2.
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
             (ishom : forall m1 m2 : M, loop' m1 @ loop' m2 = loop' (m1 + m2) )
              : B M -> P.
  Proof.
    apply Trunc_rec.
    exact (B2_rec P bp loop' ishom).
  Defined.

  Definition B_rec_beta_l {M : Monoid}
             (P : Type) (istrunc : IsTrunc 1 P)
             (bp : P)
             (loop' : forall m : M, bp = bp)
             (ishom : forall m1 m2 : M, loop' m1 @ loop' m2 = loop' (m1 + m2) )
             (m : M) :
    ap (B_rec P istrunc bp loop' ishom) (B_loop m) = loop' m.
  Proof.
    unfold B_rec.
    (*TODO: Trunc_rec_beta something exists?*)
  Admitted.

  Definition B_ind {M : Monoid}
             (P : B M -> Type) (istrunc : forall (a : B M), IsTrunc 1 (P a))
             (bp : P (point (B M)))
             (l : forall (m : M), transport P (B_loop m) bp = bp)
             (h : forall (m1 m2 : M),
                    transport
                      (fun pth => transport P pth bp = bp)
                      (ishom_MtoB m1 m2)
                      (transport_pp P (B_loop m1) (B_loop m2) bp @
                                    ap (transport P (B_loop m2)) (l m1) @ (l m2))
                    = l (m1 + m2))
             : forall a : B M, P a.
    apply Trunc_ind.
    exact istrunc.
    srapply @B2_ind.
    - exact bp.
    - intro m.
      refine (_ @ l m).
      unfold B_loop2.
      refine ((transport_compose _ B1toB2 (B_loop1 m) bp)^ @ _).
      unfold B_loop1.
      unfold B_loop.
      admit.
    - admit.
  Admitted.

  (*Computation rule that becomes unessecary when B_rec is properly defined.*)
  Definition B_rec_beta_bp {M : Monoid}
             (P : Type) (istrunc : IsTrunc 1 P)
             (bp : P)
             (loop' : forall m : M, bp = bp)
             (ishom : forall m1 m2 : M, loop' m1 @ loop' m2 = loop' (m1 + m2) ) :
    B_rec P istrunc bp loop' ishom (point (B M)) = bp.
  Admitted.

  Definition B_ind_beta_bp {M : Monoid}
             (P : B M -> Type) (istrunc : forall (a : B M), IsTrunc 1 (P a))
             (bp : P (point (B M)))
             (l : forall (m : M), transport P (B_loop m) bp = bp)
             (h : forall (m1 m2 : M),
                    transport
                      (fun pth => transport P pth bp = bp)
                      (ishom_MtoB m1 m2)
                      (transport_pp P (B_loop m1) (B_loop m2) bp @
                                    ap (transport P (B_loop m2)) (l m1) @ (l m2))
                    = l (m1 + m2)) :
    B_ind P istrunc bp l h (point (B M)) = bp.
  Admitted.
    
End Classifying_Space.



Section loopBM_is_groupcompletion.
  Open Scope monoid_scope.
  Fixpoint iterloop (n : nat) :=
    match n with
      | O => idpath
      | S n => loop @ (iterloop n)
    end.

  (*A simple case first. . .*)
  Lemma BN_is_S1 : S1 <~> B nat_monoid.
  Proof.
    srapply @equiv_adjointify.
    - (*Map from S1 to BN*)
      srapply @S1_rec.
        exact (point _).
      refine (B_loop _). exact 1.
    - (*Map from BN to S1*)
      srapply @B_rec.
      + exact base.
      + exact iterloop.
      + induction m1; intro m2.
        { apply concat_1p. }
        { simpl.
          refine (concat_pp_p _ _ _ @ _).
          apply whiskerL.
          apply IHm1. }
    - (*Composition is identity on BN*)
      srapply @B_ind.
      simpl. exact idpath.
      +  simpl.
         intro m.
         refine
           (transport_paths_FlFr
              (f := fun a =>
                    S1_rec (B nat_monoid) (point (B nat_monoid)) 
                         (B_loop (M := nat_monoid) (S O))
                         (B_rec (M := nat_monoid) S1 is1type_S1 base iterloop
                                (fun m1 : nat =>
                                   nat_rect
                                     (fun m0 : nat =>
                                        forall m2 : nat, iterloop m0 @ iterloop m2 = iterloop (m0 + m2))
                                     (fun m2 : nat => concat_1p (iterloop m2))
                                     (fun (m0 : nat)
                                          (IHm1 : forall m2 : nat,
                                                    iterloop m0 @ iterloop m2 = iterloop (m0 + m2))
                                          (m2 : nat) =>
                                        concat_pp_p loop (iterloop m0) (iterloop m2) @
                                                    whiskerL loop (IHm1 m2)) m1) a))
            (B_loop (M := nat_monoid) m) idpath @ _).
         simpl.
         apply moveR_pM.
         refine (concat_p1 _ @ _ @ (concat_1p _)^).
         apply inverse2.
         refine (ap_compose
                   (B_rec (M := nat_monoid) S1 is1type_S1 base iterloop
                          (fun m1 : nat =>
                             nat_rect
                               (fun m0 : nat =>
                                  forall m2 : nat, iterloop m0 @ iterloop m2 = iterloop (m0 + m2))
                               (fun m2 : nat => concat_1p (iterloop m2))
                               (fun (m0 : nat)
                                    (IHm1 : forall m2 : nat,
                                              iterloop m0 @ iterloop m2 = iterloop (m0 + m2))
                                    (m2 : nat) =>
                                  concat_pp_p loop (iterloop m0) (iterloop m2) @
                                              whiskerL loop (IHm1 m2)) m1))
                   (S1_rec (B nat_monoid) (point (B (nat_monoid))) (B_loop (M := nat_monoid) (S O)))
                   (B_loop (M := nat_monoid) m) @ _).
         transitivity
           (ap
              (S1_rec (B nat_monoid) (point (B nat_monoid)) (B_loop (M := nat_monoid) 1)) (iterloop m)).
         apply (ap (ap (S1_rec (B nat_monoid) (point (B nat_monoid)) (B_loop (M := nat_monoid) 1)))).
         apply B_rec_beta_l.
         (*Something transport_const?*)
         Check (fun f : B nat_monoid -> B nat_monoid => ap f (B_loop (M := nat_monoid) m)).


         induction m.
         { apply inverse. simpl.
           hott_simpl. apply (monid_to_idpath (M := nat_monoid)). }
         simpl. hott_simpl.
         refine (ap_pp (S1_rec (B nat_monoid) (point (B nat_monoid)) (B_loop (M := nat_monoid) (S O)))
                       loop (iterloop m) @ _).
         rewrite IHm.
         rewrite S1_rec_beta_loop.
         srapply @ishom_MtoB.
      + intros m1 m2.
        apply (istrunc_truncation 1).
    - (*Composition is identity on S1*)
      srapply @S1_ind.
      + exact idpath.
      + simpl.
        refine (transport_paths_FlFr
                  (f :=
                     fun x : S1 =>
                       B_rec
                         (M := nat_monoid) S1 is1type_S1 base iterloop
                         (fun m1 : nat =>
                            nat_rect
                              (fun m0 : nat =>
                                 forall m2 : nat, iterloop m0 @ iterloop m2 = iterloop (m0 + m2))
                              (fun m2 : nat => concat_1p (iterloop m2))
                              (fun (m0 : nat)
                                   (IHm1 : forall m2 : nat,
                                             iterloop m0 @ iterloop m2 = iterloop (m0 + m2))
                                   (m2 : nat) =>
                                 concat_pp_p loop (iterloop m0) (iterloop m2) @
                                             whiskerL loop (IHm1 m2)) m1)
                         (S1_rec
                            (B nat_monoid) (point (B nat_monoid)) (B_loop (M := nat_monoid) (S O)) x))
                  loop idpath @ _).
        apply moveR_pM.
        refine (concat_p1 _ @ _ @ (concat_1p _)^).
        apply inverse2.
        refine (_ @ (ap_idmap loop)^).
        refine (ap_compose
                  (S1_rec (B nat_monoid) (point (B (nat_monoid))) (B_loop (M := nat_monoid) (S O)))
                  (B_rec (M := nat_monoid) S1 _ base iterloop _)
                  loop @ _).
        transitivity (ap
                        (B_rec (M := nat_monoid) S1 is1type_S1 base iterloop
                               (fun m1 : nat =>
                                  nat_rect
                                    (fun m0 : nat =>
                                       forall m2 : nat, iterloop m0 @ iterloop m2 = iterloop (m0 + m2))
                                    (fun m2 : nat => concat_1p (iterloop m2))
                                    (fun (m0 : nat)
                                         (IHm1 : forall m2 : nat,
                                                   iterloop m0 @ iterloop m2 = iterloop (m0 + m2))
                                         (m2 : nat) =>
                                       concat_pp_p loop (iterloop m0) (iterloop m2) @
                                                   whiskerL loop (IHm1 m2)) m1))
                        (B_loop (M := nat_monoid) (S O))).
        { apply (ap _).
          apply S1_rec_beta_loop. }
        refine (B_rec_beta_l (M := nat_monoid) S1 _ base iterloop _ (S O) @ _).
        unfold iterloop. apply concat_p1.
  Defined.

(*   Definition path_trunctype_compose {n : trunc_index} {A B C : TruncType n} *)
(*              (f : A <~> B) (g : B <~> C)  : *)
(*     path_trunctype (g oE f) = path_trunctype f @ path_trunctype g. *)
(*   Proof. *)
(*     (* destruct f as [f Hf]. *) *)
(*     (* destruct g as [g Hg]. *) unfold equiv_compose'. unfold equiv_compose. *)
(*     unfold path_trunctype. *)
(*     unfold equiv_path_trunctype. *)
(*     simpl. hott_simpl. *)
(*     destruct A as [A hA]. destruct B as [B hB]. destruct C as [C hC]. simpl. *)
(*     refine (_ @ ap_pp *)
(*               (fun u : {X : Type & IsTrunc n X} => *)
(*                  {| trunctype_type := u.1; istrunc_trunctype_type := u.2 |}) *)
(*               (path_sigma_hprop (A; hA) *)
(*                                 (B; hB) *)
(*                                 (path_universe_uncurried f)) *)
(*               (path_sigma_hprop (B; hB) *)
(*                                 (C; hC) *)
(*                                 (path_universe_uncurried g)) *)
(*            ). *)
(*     apply (ap (ap *)
(*                  (fun u : {X : Type & IsTrunc n X} => *)
(*                     {| trunctype_type := u.1; istrunc_trunctype_type := u.2 |}))). *)
(*     unfold path_sigma_hprop. *)
(*     refine (_ @ path_sigma_pp_pp _ _ _ _ _ ). *)
(*     unfold path_sigma. *)
(*     apply (ap (path_sigma_uncurried (IsTrunc n) (A; hA) (C; hC))). *)
(*     unfold equiv_inv.  *)
(*     apply path_universe_compose. *)
(*     unfold path_universe_uncurried. *)
(*     unfold equiv_inv. destruct (isequiv_equiv_path A C) as [ua w e r]. *)
    
(*     path_sigma_pp_pp *)

(*     unfold equiv_composeR'. unfold equiv_compose'. unfold equiv_compose. *)
(*     unfold equiv_inverse. simpl. hott_simpl. *)

  
(* path_universe_compose *)

  (*Lage alternativ til apD?*)

    
  (*Classifying space as a pointed type*)
  Definition pB (M : Monoid) := Build_pType (B M) _.

  (*B S is an abelian group*)
  Definition loopB_abGrp (S : Symmetric_Monoid) : Abelian_Group.
  Proof.
    refine (Build_Abelian_Group (loopGroup (pB S)) _).
    unfold symmetric. unfold loopGroup. simpl.
    unfold mon_mult.
    unfold symmetric.
  Admitted.
  
  Definition grpcplS_to_loopsB {S : Symmetric_Monoid} : Hom (group_completion S) (loopGroup (pB S)) :=
    extend_to_inv 
      (Build_Homomorphism S (loopGroup (pB S)) B_loop monid_to_idpath
                          (fun m1 m2 => (ishom_MtoB m1 m2)^)).
  
  (*Fibration over B S with fiber groupcompletion S*)
  Definition B_code (S : Symmetric_Monoid) : B S -> hSet.
  Proof.
    srapply @B_rec.
        - exact (BuildTruncType 0 (group_completion S)).
        - intro a.
          apply (ap trunctype_type)^-1.
          exact (path_universe (grp_mult_equiv (to_groupcompletion a))).
        - intros m1 m2.
          apply (equiv_inj (ap trunctype_type)).
          refine (ap_pp trunctype_type _ _ @ _).
          refine (_ @ (eisretr (ap trunctype_type) _)^).
          refine (concat2 (eisretr (ap trunctype_type) _)
                          (eisretr (ap trunctype_type) _)
                          @ _).
          
          refine ((path_universe_compose _ _)^ @ _).
          refine (equiv_path2_universe
                    (grp_mult_equiv (to_groupcompletion m2) oE
                                    grp_mult_equiv (to_groupcompletion m1))                    
                    (grp_mult_equiv (to_groupcompletion (m1 + m2)))
                    (fun m => (grp_whiskerL (preserve_mult to_groupcompletion) @ grp_assoc)^) ).
  Defined.

  Definition B_code_beta {S : Symmetric_Monoid} (m : S) :
    ap (B_code S) (B_loop m) =
    (ap trunctype_type)^-1 (path_universe (grp_mult_equiv (to_groupcompletion m))).
  Proof.
    srapply @B_rec_beta_l.
  Defined.

  Definition transport_code_is_mult {S : Symmetric_Monoid} (m : S) :
    transport (B_code S) (B_loop m) == fun g : (group_completion S) => g + (to_groupcompletion m).
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Variable is fixed*)
      intros [a b].
      refine (transport_compose trunctype_type (B_code S) (B_loop m) (tr (coeq (a, b))) @ _).
      

      Check (fun p : B_code S (point (B S)) = B_code S (point (B S)) =>
               transport (fun X : hSet => trunctype_type X) p (tr (coeq (a, b)))).
      refine (transport_compose idmap (trunctype_type)
                                (ap (B_code S) (B_loop m)) (tr (coeq (a, b))) @ _).
      assert (B_code_beta' : ap trunctype_type (ap (B_code S) (B_loop m))  =
                             path_universe (grp_mult_equiv (to_groupcompletion m))).
      { refine (ap (ap trunctype_type) (B_code_beta m) @ _).
        apply (eisretr (ap trunctype_type)). }
      
      
      refine (ap (fun p : trunctype_type (B_code S (point (B S))) =
                          trunctype_type (B_code S (point (B S))) =>
                    transport (fun X : Type => X) p (tr (coeq (a, b)))) B_code_beta' @ _).
      refine (ap10 (transport_idmap_path_universe (grp_mult_equiv (to_groupcompletion m))) _).
    - (*Variable runs along cp*)
      intro abs.
      apply (istrunc_truncation 0).
  Defined.

  Definition transport_code_is_mult_V {S : Symmetric_Monoid} (m : S) :
    transport (B_code S) (B_loop m)^ == fun g : (group_completion S) => g - (to_groupcompletion m).
  Proof.
    intro x.
    refine (moveR_transport_V (B_code S) (B_loop m) x _ _).
    apply inverse.
    refine (transport_code_is_mult m _ @ _).
    refine (_ @ grp_rid x).
    refine (grp_assoc^ @ _).
    refine (grp_whiskerL _).
    apply grp_linv.
  Defined.

  Definition B_encode {S : Symmetric_Monoid} (x : B S) :
    (point _ = x) -> B_code S x := fun p => transport (B_code S) p (point _).

  (*I hope this is useful for proving truncations
   Something like this is probably already implemented. . .*)
  Definition generalize_paths {X : Type} {x1 x2 : X} {p1 p2 : x1 = x2} :
    (IsTrunc 0 X) -> p1 = p2.
  Proof.
    intro H. apply H.
  Defined.

  Definition B_decode {S : Symmetric_Monoid} (x : B S) :
    B_code S x -> (point _ = x).
  Proof.
    revert x.
    srapply @B_ind.
    - (*x is point*)
      simpl.
      apply grpcplS_to_loopsB.
    - (*x is B_loop m*)
      intro m.
      apply path_arrow. intro x.
      refine (transport_arrow (B_loop m) _ x @ _).
      (*This is more readable, but then it protests when writing x - m*)
      (*unfold B_code in x. simpl in x.  *)
      refine (transport_paths_r (B_loop m) _ @ _).      
      apply moveR_pM.
      refine (ap (fun g : group_completion S => grpcplS_to_loopsB g)
                 (transport_code_is_mult_V m x) @ _).
      refine (preserve_mult grpcplS_to_loopsB @ _).
      refine (whiskerL (grpcplS_to_loopsB x) _).
      refine (whiskerR monid_to_idpath (B_loop m)^ @ _).
      apply concat_1p.
    - (*x is ishom m1 m2*)
      intros m1 m2.
      srapply @generalize_paths.
  Defined.

  Definition B_decode_beta_bp {S : Symmetric_Monoid} :
    B_decode (point (B S)) = grpcplS_to_loopsB .
  Proof.
    srapply @B_ind_beta_bp.
  Defined.

  Definition B_encodeisretr {S : Symmetric_Monoid} (x : B S):
    Sect (B_encode x) (B_decode x).
  Proof.
    intro p.
    destruct p. simpl.
    (*This should be automatic if B_ind was properly defined:*)
    refine (ap10 B_decode_beta_bp (point (group_completion S)) @ _). 
    unfold grpcplS_to_loopsB. simpl.
    apply concat_pV.
  Defined.

  Definition B_encodeissect {S : Symmetric_Monoid} (x : B S) :
    Sect (B_decode x) (B_encode x).
  Proof.
    revert x.
    srapply @B_ind.
    - intro m.
      rewrite (ap10 B_decode_beta_bp m).
      revert m.
      srapply @Trunc_ind.
      srapply @Coeq_ind.
      + intros [a b].
        unfold B_encode.
        simpl.
        refine (transport_pp (B_code S) (B_loop a) (B_loop b)^ (point (group_completion S)) @ _).
        apply (moveR_transport_V (B_code S)).
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

  Definition equiv_pathsB_code {S : Symmetric_Monoid} (x : B S) :
    point (B S) = x <~> B_code S x :=
    equiv_adjointify (B_encode x) (B_decode x) (B_encodeissect x) (B_encodeisretr x).
  
  Definition equiv_loopsB_group_completion (S : Symmetric_Monoid):
       loops (pB S) <~> group_completion S:=
    equiv_pathsB_code (point (B S)).        
        
      
    
        
        
        
        
        
        




