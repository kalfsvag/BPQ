Require Import HoTT.
Load pType_basics.

(*This section should be elsewhere *)
Section ap12.
  Lemma ap12 {A B : Type} (*Correct name?*)
        {a b : A} (p : a = b) {f g : A->B} (h : f=g)  :
    (ap10 h a)^ @ ap f p @ ap10 h b= ap g p.
  Proof.
    refine (concat _ (apD (fun f : A -> B => ap f p) h)).
    exact (transport_paths_FlFr _ _)^.
  Defined.
End ap12.

(*Defining the monoidal type of finite sets and isomorphisms*)
Section FinIso.
  Require Import UnivalenceAxiom.
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Record iFin :=
    { fType : Type;
      isFin : Finite fType
      }.
  (*ishprop_finite*)

  Definition cardinal (A : iFin) : nat.
    refine (fcard (fType A) ).
    exact (isFin A).
  Defined.

  (*Canonical objects in iFin*)
  Definition fin (n : nat) : iFin :=
    Build_iFin (Fin n) _.

  (*Every object is canonical*)
  Definition canonical_iFin (A : iFin) : A = fin (cardinal A).
    (*TODO*)
  Admitted.
  
  
  

End Section.
    
  


Section Monoid.
  (*Is it necessary to say that A is a set?*)
  Definition associative {A : Type}  (m : A->A->A) := forall a b c : A, m a (m b c) = m (m a b) c.
  Definition left_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m e a = a.
  Definition right_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a.
  (*
Definition IsMonoid (A : Type) {isset : IsHSet A} (m : A->A->A) (e : A) :=
  (associative m) * (left_identity m e) * (right_identity m e). *)
  (*TODO: isGroup *)

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

(*A simple result on coequalizers*)
Lemma Coeq_precompose `{Funext} {B A : Type} {f : B -> A} {g : B -> A} :
  (@coeq B A f g) o f = coeq o g.
Proof.
  apply path_forall.
  intro b.
  apply cp.
Defined.

      
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





