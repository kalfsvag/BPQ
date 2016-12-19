Require Import HoTT.
Require Import UnivalenceAxiom.
Load pType_basics.
Load Coequalizer.

(*This section should be elsewhere *)
Section Misc.
  Lemma ap12 {A B : Type} (*Correct name?*)
        {a b : A} (p : a = b) {f g : A->B} (h : f=g)  :
    (ap10 h a)^ @ ap f p @ ap10 h b= ap g p.
  Proof.
    refine (concat _ (apD (fun f : A -> B => ap f p) h)).
    exact (transport_paths_FlFr _ _)^.
  Defined.

(*  Definition prod_uncurryD {A B : Type} {P : A -> B -> Type} :
    (forall p : A*B, P (fst p) (snd p)) -> forall a : A, forall b : B, P a b :=
    (equiv_prod_ind _)^-1 . *)
(*
  Definition precomposeD {A B : Type} {P : B -> Type} (f : A->B) :
    (forall a : A, P (f a)) -> forall b : B, P b.
  Proof.
    intro g.
    intro b.
    exact 
  *)  
    
  
End Misc.




Section Monoid.
  (*Is it necessary to say that A is a set?*)
  Definition associative {A : Type}  (m : A->A->A) := forall a b c : A, m a (m b c) = m (m a b) c.
  Definition left_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m e a = a.
  Definition right_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a.
  (*
Definition IsMonoid (A : Type) {isset : IsHSet A} (m : A->A->A) (e : A) :=
  (associative m) * (left_identity m e) * (right_identity m e). *)
  (*TODO: isGroup *)
  Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a.

  Record Monoid : Type := { mon_set : Type;
                            mon_isset : IsHSet mon_set;
                            mon_mult  : mon_set->mon_set->mon_set;
                            mon_id : mon_set;
                            mon_assoc : associative mon_mult;
                            mon_lid : left_identity mon_mult mon_id ;
                            mon_rid : right_identity mon_mult mon_id
                          }.

  (*Makes mon_isset an implicit argument*)
  Arguments Build_Monoid mon_set {mon_isset} mon_mult mon_id mon_assoc mon_lid mon_rid.


  Coercion mon_set : Monoid >-> Sortclass.
  Definition multM {M:Monoid} : M->M->M := mon_mult M.


  Global Instance ispointed_M {M : Monoid} : IsPointed M := (mon_id M).

  (* (*Symmetric monoid*) *)
  (* Definition Symm_Monoid : Type := {S : Monoid & symmetric (mon_mult S)}. *)
  (* (*Might be cleaner to define this as a new record, I don't know. . .*) *)
  (* Definition sym_mon_set (S : Symm_Monoid) : Type := mon_set (S.1). *)
  (* Coercion sym_mon_set : Symm_Monoid >-> Sortclass. *)

  (*Formulate the cancellation law for a monoid*)
  Definition right_cancellation_law (M : Monoid) :=
    forall a b s : M, multM a s = multM b s -> a = b.

  
  
  (*Strangely, I cannot find any proofs of nat being associative*)
  Local Open Scope nat_scope.
  Definition plus_assoc : associative Peano.plus.
    intros j k l.
    induction j, k, l.
    - exact idpath.
    - exact idpath.
    - exact idpath.
    - exact idpath.
    - exact (ap S IHj).
    - exact (ap S IHj).
    - exact (ap S IHj).
    - exact (ap S IHj).
  Defined.
  
  Definition nat_monoid : Monoid :=
    Build_Monoid
      nat Peano.plus O
      plus_assoc (fun _ => idpath) (fun n => (nat_plus_n_O n)^).


End Monoid.

Section Group.

  Definition left_inverse {M : Monoid} (inv : M->M) :=
    forall m : M, multM (inv m) m = mon_id M.

  Definition right_inverse {M : Monoid} (inv : M->M) :=
    forall m : M, multM m (inv m) = mon_id M.

  Record Group : Type := {grp_mon : Monoid;
                          grp_inv : grp_mon -> grp_mon;
                          grp_linv : left_inverse (grp_inv);
                          grp_rinv : right_inverse (grp_inv)
                         }.
  (*Rename maps that come from monoid structure*)
  Definition grp_set (G : Group) := mon_set (grp_mon G).
  Coercion grp_set : Group >-> Sortclass.
  Definition multG {G : Group} : G->G->G := mon_mult (grp_mon G).

  (*The Grothendieck group completion*)
  (*The group completion of a symmetric monoid M is M*M/~ where m~s+m *)
  (*Assume S is a symmetric monoid with cancellation. (Group completion is nicer then.)*)
  Variable S : Monoid.
  Variable mon_sym : symmetric (mon_mult S).
  Variable rc : right_cancellation_law S.

  Notation "a + b" := (multM a b) : monoid_scope.
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
    revert g1.
    refine (Coeq_rec _ _ _).
    - (*Fix first variable*)
      intros [m1 m2].
      refine (Coeq_rec _ _ _).
      + (*Fix second variable*)
        intros [n1 n2].
        exact (tr (coeq (m1 + n1, m2 + n2))).
      + (*Second variable runs along cp*)
        intros [[a b] s].
        apply (ap (tr)).
        simpl.
        refine (_ @ cp (m1+a,m2+b,s)).
        apply (ap coeq). unfold as_bs.
        apply path_prod.
        apply mon_assoc. apply mon_assoc.
    - (*First variable runst along cp*)
      intros [[a b] s].
      apply path_forall.
      refine (Coeq_ind _ _ _).
      + (*Fix second variable*)
        intros [m1 m2].
        simpl.
        apply (ap tr).
        refine (_ @ cp (a+m1,b+m2,s)).
        apply (ap coeq). unfold as_bs.
        apply path_prod.
        { simpl.
          refine ((mon_assoc S a s m1)^ @ _ @ (mon_assoc S a m1 s)).
          apply (ap (mon_mult S a)).
          apply mon_sym. }
        { refine ((mon_assoc S b s m2)^ @ _ @ (mon_assoc S b m2 s)).
          apply (ap (mon_mult S b)).
          apply mon_sym. }
      + (*Both variables runs along cp*)
        (*This is a 2-path so we just kill it*)
        intro abs'.
        apply (istrunc_truncation 0).
  Defined.
        
(*  Unset Printing Notations.
  Set Printing Implicit. *)
  Definition grp_compl_assoc : associative grp_compl_mult.
    Proof.
      unfold associative.
      refine (Trunc_ind _ _).
      intro a.
      refine (Trunc_ind _ _).
      intro b.
      refine (Trunc_ind _ _).
      intro c.
      revert b c. (*Change from here. . .*)


      refine (changebase _ _ _). (*This is not actually proved yet. . .*)
      - apply path_prod. apply mon_lid. apply mon_lid.
      - revert a.
        refine (changebase _ _ _).
        + apply path_prod. apply mon_lid. apply mon_lid.
        + refine (Coeq_ind _ _ _).
        * intros [[l1 l2] [[m1 m2] [n1 n2]]].
          simpl.
          apply (ap tr).
          apply (ap coeq).
          (*Easy right now, at least. . .*)
          unfold point. unfold ispointed_M.
          apply path_prod.
          simpl.
          
          rewrite (mon_lid S (n1)).
          
          refine (Coeq_ind _ _ _).
          * intros [n1 n2].
            apply (ap tr).
            apply (ap coeq).
            simpl.
            apply (path_prod).
              simpl. unfold point. unfold ispointed_M.
              apply (ap (fun x => mon_id S + mon_id S + x)).
              refine (_ @ mon_lid S n1).
              apply (ap (fun x => x + n1)).
              apply (mon_lid S).

              simpl. unfold point. unfold ispointed_M.
              apply (ap (fun x => mon_id S + mon_id S + x)).
              refine (_ @ mon_lid S n2).
              apply (ap (fun x => x + n2)).
              apply (mon_lid S).
          * intro.
            apply (istrunc_truncation 0).            
        + intro b.
          destruct b as [[[a b] s][[a' b'] s']].
          refine (transport_compose _ _ _ _ @ _).
          
          

              
            
        
        intro.
        apply path_universe.
        refine (univalence_axiom _).
        refine (_ @ cp ).
        unfold pullback_pc_to_cp.
      
(*      refine (prod_uncurryD _). refine (prod_uncurryD _).
      refine (functor_forall (prod_coeq_to_coeq_prod2  _ _ _ _) _ _).
      
      intro p.        
      refine ((_ o (prod_coeq_to_coeq_prod2  _ _ _ _) ) p). (*Should be possible to generalize this. . . composeD?*)
      - (*Have reduced it to a map from a single coequalizer*)
        refine (Coeq_rec _ _ _).
        + (*Proce associativity on the underlying set*)
          intros [[[l1 l2] [m1 m2]] [n1 n2]].
          
      
      
      + refine (Coeq_ind _ _ _).
        intro l1l2.
        refine (Coeq_ind _ _ _).
        * intro m1m2.
          refine (Coeq_ind _ _ _).
          { intro n1n2.
            simpl.
            apply (ap tr).
            apply (ap coeq).
            apply path_prod.
              apply mon_assoc. apply mon_assoc.
          }
          intro.
          apply (istrunc_truncation 0).
        * intro abs.
          apply path_forall.
          refine (Coeq_ind _ _ _).
          {intro m1m2. apply (istrunc_truncation 0). }
          intro abs'.
          assert (istr1 : IsTrunc 1 (grp_compl_set S)).
            apply trunc_succ.
          apply istr1. 
        * intros [[a b] s]. simpl.
          Unset Printing Notations.
  Set Printing Implicit.
  *)        
            
            
              
            
                
          
          
            
      
      

    Admitted. (*TODO*)
  
  Definition grp_compl_id : grp_compl_set S := tr (coeq (mon_id S, mon_id S)).
  
  Definition grp_compl_lid : left_identity grp_compl_mult grp_compl_id.
  Proof.
    unfold left_identity.
    apply Trunc_ind.
    - (*This is trivial*) exact (fun _ => _).
    - refine (Coeq_ind _ _ _).
      + intros [m1 m2].
        simpl.
        apply (ap tr).
        apply (ap coeq).
        apply path_prod.
        * apply mon_lid.
        * apply mon_lid.
      + intro x.
        apply (istrunc_truncation 0).
  Defined.
  
  Definition grp_compl_rid : right_identity grp_compl_mult grp_compl_id.
  Proof.
    unfold right_identity.
    apply Trunc_ind.
    - (*This is trivial*) exact (fun _ => _).
    - refine (Coeq_ind _ _ _).
      + intros [m1 m2].
        simpl.
        apply (ap tr).
        apply (ap coeq).
        apply path_prod.
        * apply mon_rid.
        * apply mon_rid.
      + intro x.
        apply (istrunc_truncation 0).
  Defined.

  

  
        
        
    
  
          
          
           
           
           
        
    
    
    
  
  
  
  Definition group_completion
             (S : Monoid)
             (mon_sym : symmetric (mon_mult S))
             (lc : left_cancellation_law (S)) : Group.
    refine (Build_Group _ _ _ _).
    
             
  
  
  Definition grp_compl_rel {S : Symm_Monoid} : relation (S*S).
    unfold relation.
    intros [a b] [c d].
    
  
  Definition group_completion (S : Symm_Monoid) : Group.
    
    
  
End Group.


(*Defining the monoidal type of finite sets and isomorphisms*)
Section FinIso.
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Definition iFin := { S : Type & Finite S }.
  (*ishprop_finite*)

  (*The cardinal of the finite set*)
  Definition cardinal (S : iFin) : nat := @fcard S.1 S.2.

  (*Canonical objects in iFin*)
  Definition fin (n : nat) : iFin := ( Fin n ; finite_fin n ).

  (*Every object is canonical*)
  Lemma canonical_iFin (S : iFin) : merely (S = fin (cardinal S)).
  Proof.
    refine (Trunc_rec (n:=-1) (A := (S.1 <~> Fin (fcard S.1))) _ _).
    - exact S.2.
    - intro e.
      apply tr.
      refine (path_sigma_hprop _ _ _).
      refine (path_universe _).
        apply e. exact _.
    - apply merely_equiv_fin.
  Defined.
  (*Should be possible to choose an isomorphism? *)

  (*The monoidal structure on iFin*)
  Definition FinPlus : iFin-> iFin -> iFin.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (S1 + S2 ; finite_sum _ _).
  Defined.

  (*I feel it should be possible to make a tactic *)
  Definition FinPlus_assoc : associative FinPlus.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2] [S3 fin_S3].
    refine (path_sigma_hprop _ _ _).
    refine (path_universe _).
    apply equiv_sum_assoc. exact _.
  Defined.
  
  Definition FinPlus_leftid : left_identity FinPlus (fin 0).
  Proof.
    intros [S fin_S].
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_l S)).
  Defined.

  Definition FinPlus_rightid : right_identity FinPlus (fin 0).
  Proof.
    intros [S fin_S].
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_r S)).
  Defined.

  Definition FinPlus_symmetric : symmetric FinPlus. 
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (equiv_sum_symm S1 S2)).
  Defined.

  

  

  
  

End FinIso.
    


      
Section Classifying_Space.
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
    refine (Coeq_rec P _ _).
    - exact (const bp). (*intros []. exact bp.*)
    - exact l.
  Defined.

  Definition B1_ind {M : Monoid}
             (P : B1 M -> Type) (bp : P (point (B1 M)))
             (loop' : forall (m : M), transport P (B_loop1 m) bp = bp)
             : forall a : B1 M, P a.
  Proof.
    refine (Coeq_ind _ _ _).
    - intros []. exact bp.
    - exact loop'.
  Defined.
  
  Definition looptofill (M : Monoid) (m1 m2 : M) : S1 -> B1 M.
    refine (S1_rec (B1 M) (point (B1 M)) _).
    exact ((B_loop1 m1) @ (B_loop1 m2) @ (B_loop1 (multM m1 m2))^).
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

  

  Definition isHom_MtoB2 `{Funext} {M : Monoid} (m1 m2: M) :
     B_loop2 m1 @ B_loop2 m2 = B_loop2 (multM m1 m2).
  Proof.
    unfold B_loop2.
    apply moveL_1M.
    path_via (ap B1toB2 (ap (S1toB1 m1 m2) loop)).
    - path_via (ap B1toB2 ( (B_loop1 m1) @ (B_loop1 m2) @ (B_loop1 (multM m1 m2))^)).
      + refine (concat _ (ap_pp _ _ _)^).
        apply concat2.
        * refine (ap_pp _ _ _)^.
        * refine (ap_V B1toB2 _)^ .
      + 
        apply ap.
        unfold S1toB1.
        refine (S1_rec_beta_loop _ _ _)^. 
    - refine (concat (ap_compose _ _ _)^ _).
      refine (concat _ (ap_const loop _)). 
      refine (concat _ (ap12 loop (const_S1toB2 m1 m2))).
      rewrite ap_compose.
      rewrite concat_pp_p.
      apply moveL_Vp.
      unfold S1toB1.
      unfold looptofill.
      rewrite S1_rec_beta_loop.      
      unfold const_S1toB2.
      rewrite (path_forall _ _ (ap10_path_forall _ _ _)).
      unfold nullhom_S1toB2.
      hott_simpl.
  Qed.
                          

  Definition B2_rec {M : Monoid}
             (P : Type)
             (bp : P)
             (l : M -> bp = bp)
             (h : forall m1 m2 : M, l m1 @ l m2 = l (multM m1 m2) ) :
    B2 M -> P.
    (*B2 is the pushout of B1 M and M*M*S1*)
    refine (pushout_rec P _ _).
    - apply sum_rect.      
      + (*The map defined on B1 is given by l*)
        refine (B1_rec _ bp _).
        exact l.
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
      refine (S1_ind _ _ _ ).
      + exact idpath.
      + refine (concat (transport_paths_Fl loop idpath) _).
        hott_simpl.        (*TODO: Make this transparent?*)
        unfold B1_rec.
        rewrite ap_compose.
        rewrite S1_rec_beta_loop.
        rewrite <- (inv_V idpath).
        apply inverse2.
        rewrite ap_pp.
        rewrite ap_pp.
        unfold B_loop1.
        (*Somehow, rewrite Coeq_rec_beta_cp doesn't work here. . .*)
        rewrite ap_V.
        apply moveR_pV.
        refine (concat (y := l (multM m1 m2)) _ _).
        refine (concat (y := l m1 @ l m2) _ _).
        apply concat2.
        exact (Coeq_rec_beta_cp P (const bp) l m1).
        exact (Coeq_rec_beta_cp P (const bp) l m2).
        exact (h m1 m2).        
        hott_simpl.
        exact (Coeq_rec_beta_cp P (const bp) l (multM m1 m2))^.
  Qed.
        
        
      

   
  
   Definition B2_ind {M : Monoid}
             (P : B2 M -> Type)
             (bp : P (point (B2 M)))
             (l : forall (m : M), transport P (B_loop2 m) bp = bp)
             (h : forall (m1 m2 : M),
                    ap (transport P (B_loop2 m2)) (l m1) @ (l m2) = l (multM m1 m2) )
                        (* transport P (B_loop2 m1) (transport P (B_loop2 m2) bp) *)
                        (* = transport P (B_loop2 (multM m1 m2)) bp ) (*Not right*) *)
             : forall a : B2 M, P a.
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





