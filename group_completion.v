Require Import HoTT.
Load pType_basics.
Local Open Scope nat_scope.

Section Disc.
  Fixpoint Disc (n:nat) : pType :=
    match n with
        | O => Build_pType Unit _
        | S n => psusp (Disc n)
    end.
  
  Definition Sphere_to_Disc (n : nat) : pSphere n ->* Disc n.+1.
  Proof.
    induction n.
    - (*Map S0 to the boundary of the interval*)
      rapply Build_pMap.
      + apply (Susp_rec North South). apply Empty_rec.
      + exact idpath.
    - apply (psusp_functor IHn).
  Defined.    
End Disc.


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
(*
(*In this section I will try to define classifying space of a monoid directly as an inductive type*)
Section B.
  (*First define the 2-skeleton of the classifying space.*)
  Private Inductive B2 (M : Monoid) :=
    pt_B2 : B2 M.

  Arguments pt_B2 {M}.
  
  Axiom mon_loop : forall (M : Monoid) (m : M) , @pt_B2 M = pt_B2.
  Arguments mon_loop {M} m.

  Axiom mon_hom : forall (M : Monoid) (m1 m2 : M),
                    (mon_loop m1) @ (mon_loop m2) = mon_loop (multM m1 m2).
  Arguments mon_hom {M} m1 m2.
    
    
  

  Definition B2_rec {M : Monoid} (P : Type) (pt : P)
             (loop_P : forall m : M, pt = pt)
             (hom_P : forall m1 m2 : M
 
End B.
*)

(*A simple result on coequalizers*)
Lemma Coeq_precompose `{Funext} {B A : Type} {f : B -> A} {g : B -> A} :
  (@coeq B A f g) o f = coeq o g.
Proof.
  apply path_forall.
  intro b.
  apply cp.
Defined.

(*
Section Classifying_Space.
  (*Try a simpler construction of B M than below. *)
  
  (*The 1-skeleton of B.*)
  Definition B1 (M : Monoid)  := @Coeq M Unit (const tt) (const tt).
  
  (*B1 has one point:*)
  Global Instance ispointed_B1 {M : Monoid} : IsPointed (B1 M) := coeq tt.
  
  (*B1 has one loop for every m : M*)
  Definition mon_loop1 {M : Monoid} : M -> point (B1 M) = point (B1 M) := cp.

  Definition pm1_pm2 {M : Monoid} : M * M * S1 -> B1 M.
    intros [[m1 m2]].
    refine (S1_rec (B1 M) (point _) _).
    exact ((mon_loop1 m1) @ (mon_loop1 m2)).
  Defined.

  Definition pS1 := Build_pType S1 base.
  Definition pB1 (M : Monoid) := Build_pType (B1 M) _.
  
  Definition S1_to_B1_1 {M : Monoid} (m1 m2 : M) : pS1 ->* pB1 M :=
    Build_pMap pS1 (pB1 M)
      (fun x : pS1 => pm1_pm2 (m1, m2, x))
      idpath.

  Definition p_m1m2 {M : Monoid} : M * M * S1 -> B1 M.
    intros [[m1 m2]].
    refine (S1_rec (B1 M) (point _) _).
    exact (mon_loop1 (multM m1 m2)).
  Defined.

  Definition S1_to_B1_2 {M : Monoid} (m1 m2 : M) : pS1 ->* pB1 M :=
    Build_pMap pS1 (pB1 M)
      (fun x : pS1 => p_m1m2 (m1, m2, x))
      idpath.
  Definition pm1_pm2 {M : Monoid} : M * M * S1 -> B1 M.
    intros [[m1 m2]].
    refine (S1_rec (B1 M) (point _) _).
    exact ((mon_loop1 m1) @ (mon_loop1 m2)).
  Defined.

  Definition pS1 := Build_pType S1 base.
  Definition pB1 (M : Monoid) := Build_pType (B1 M) _.
  
  Definition S1_to_B1_1 {M : Monoid} (m1 m2 : M) : pS1 ->* pB1 M :=
    Build_pMap pS1 (pB1 M)
      (fun x : pS1 => pm1_pm2 (m1, m2, x))
      idpath.

  Definition p_m1m2 {M : Monoid} : M * M * S1 -> B1 M.
    intros [[m1 m2]].
    refine (S1_rec (B1 M) (point _) _).
    exact (mon_loop1 (multM m1 m2)).
  Defined.

  Definition S1_to_B1_2 {M : Monoid} (m1 m2 : M) : pS1 ->* pB1 M :=
    Build_pMap pS1 (pB1 M)
      (fun x : pS1 => p_m1m2 (m1, m2, x))
      idpath.


  (*The 2-skeleton of B*)
  Definition B2 (M : Monoid) := @Coeq (M * M * S1) (B1 M)
                                      pm1_pm2
                                      p_m1m2.
  Global Instance ispointed_B2 {M : Monoid} : IsPointed (B2 M) := coeq (point (B1 M)).
  Definition pB2 (M : Monoid) := Build_pType (B2 M) _.

  Definition B1toB2 {M : Monoid} : pB1 M ->* pB2 M :=
    Build_pMap (pB1 M) (pB2 M) coeq idpath.

  Definition mon_loop2 {M : Monoid} (m : M) : point (B2 M) = point (B2 M) := ap B1toB2 (mon_loop1 m).

  Definition comesFromS1_1 {M : Monoid} (m1 m2 : M) :
    ap (B1toB2 o (S1_to_B1_1 m1 m2)) loop = (mon_loop2 m1) @ (mon_loop2 m2).
  Proof.
    refine (concat _ _). exact (ap B1toB2 ((mon_loop1 m1)@(mon_loop1 m2))).
    refine (concat _ _). exact (ap B1toB2 (ap (S1_to_B1_1 m1 m2) loop)).
    { apply ap_compose. }
    { apply ap.
      apply S1_rec_beta_loop. }
    apply (ap_pp B1toB2).
  Defined.

  Definition comesFromS1_2 {M : Monoid} (m1 m2 : M) :
    ap (B1toB2 o (S1_to_B1_2 m1 m2)) loop = mon_loop2 (multM m1 m2).
  Proof.
    refine (concat _ _). exact (ap B1toB2 (ap (S1_to_B1_2 m1 m2) loop)).
    { apply ap_compose. }
    unfold mon_loop2.
    apply ap.
    apply S1_rec_beta_loop.    
  Defined.

  (*This one could be done in more generality:*)
  Definition restriction_is_equal `{Funext} {M : Monoid} (m1 m2 : M) :
    B1toB2 o (S1_to_B1_1 m1 m2) = B1toB2 o (S1_to_B1_2 m1 m2).
  Proof.
    apply path_forall.
    intro x.
    cbn.
    apply cp.
    (*
    apply path_pmap.
    refine (Build_pHomotopy _ _ ).
    - cbn.
      refine (S1_ind _ _ _).
      + exact idpath.
      + refine (concat (transport_paths_FlFr _ _) _).
        hott_simpl. (*Opaquely for now. . .*)
        apply moveR_Vp.
        rewrite concat_p1.

        rewrite (ap_compose _ _ _) .
        refine (concat _ (ap_compose (fun x : S1 => pm1_pm2 (m1, m2, x)) coeq loop)^) .
        unfold p_m1m2.
        unfold pm1_pm2.

        rewrite S1_rec_beta_loop.
        rewrite S1_rec_beta_loop.
        unfold mon_loop1.
        
        admit.
    - exact idpath. 

        
     *)      
  Defined.

  Definition mon_hom `{Funext} {M : Monoid} (m1 m2 : M) :
    ((mon_loop2 m1) @ (mon_loop2 m2)) = (mon_loop2 (multM m1 m2)).
  Proof.
    refine (concat _ _). exact (ap (B1toB2 o (S1_to_B1_1 m1 m2)) loop).
    { apply inverse.
      apply comesFromS1_1. }
    refine (concat _ _). exact (ap (B1toB2 o (S1_to_B1_2 m1 m2)) loop).
    { change (fun x : pS1 => B1toB2 (S1_to_B1_1 m1 m2 x)) with (B1toB2 o (S1_to_B1_1 m1 m2)).
      
      refine (concat _
                     (apD (fun (f : S1 -> B2 M) => ap f loop) (restriction_is_equal m1 m2))).
      refine (concat _
                     (transport_paths_FlFr
                        (restriction_is_equal m1 m2)
                        (ap (fun x : S1 => B1toB2 (S1_to_B1_1 m1 m2 x)) loop))^
             ).
      cbn.
      rewrite ap_apply_l.
      unfold restriction_is_equal.
      rewrite ap10_path_forall.
      
      simpl.
      


                     refine (concat _ _).
      exact (transport (fun (f : interval -> B2 M) => f Interval.zero = f Interval.one) (restriction_is_equal m1 m2) _).
      
          rewrite (restriction_is_equal m1 m2). (*Y U NO WORK*)
      
      apply (apD (fun (f : interval -> B2 M) => ap f seg)). } 
    apply comesFromInt_2.
    
    
    unfold mon_loop2.
    refine (concat _ _). exact (ap B1toB2 ((mon_loop1 m1)@(mon_loop1 m2))).
    { refine (ap_pp B1toB2 _ _)^ . }
    (*Must use interval_rec_beta_seg. . .*)
    refine (concat _ _). exact (ap B1toB2 (ap (intToB1_1 m1 m2) seg)).
    { apply inverse.
      apply ap.
      apply interval_rec_beta_seg. }
    refine (concat _ _). exact (ap B1toB2 (ap (intToB1_2 m1 m2) seg)).
       { rewrite <- ap_compose.  }
    apply ap.
    apply interval_rec_beta_seg.
*)     
    
      
Section Classifying_Space_Pushout.
  (*Define the classifying space of a monoid as a cell complex*)

  (*The 1-skeleton of B.*)
  Definition B1 (M : Monoid)  := @Coeq M Unit (const tt) (const tt).
  
  (*B1 has one point:*)
  Global Instance ispointed_B1 {M : Monoid} : IsPointed (B1 M) := coeq tt.
  
  (*B1 has one loop for every m : M*)
  Definition mon_loop1 {M : Monoid} : M -> point (B1 M) = point (B1 M) := cp.


  
  Definition looptofill {M : Monoid} : M * M * S1 -> B1 M.
    intros [[m1 m2]].
    refine (S1_rec (B1 M) (point _) _).
    exact ((mon_loop1 m1) @ (mon_loop1 m2) @ (mon_loop1 (multM m1 m2))^).
  Defined.
  
  Definition S1toB1 {M : Monoid} (m1 m2 : M) : S1 -> B1 M :=
    fun x : S1 => looptofill (m1, m2, x).

  (*Construct 2-cells*)
  Definition B2 (M : Monoid) := pushout
                                  (@looptofill M)
                                  (@const (M * M * S1) Unit tt).
  
  Global Instance ispointed_B2 {M : Monoid} : IsPointed (B2 M) := push (inr tt).

  Definition ispointed_MMS1 {M : Monoid} : IsPointed (M * M * S1) := (mon_id M, mon_id M, base).

  (*Not sure if this is needed. . .*)
  Definition path_to_pt_B2 {M : Monoid} (x : M * M * S1) : pushl x = point (B2 M) := pp x.

  Definition B1toB2 {M : Monoid} : B1 M -> B2 M := (push o inl).
  (*TODO: Bruke transport i stedet?*)
  Definition mon_loop2 {M : Monoid} (m : M) : point (B2 M) = point (B2 M).
  Proof.
    refine (concat _ (pp (ispointed_MMS1))).
    refine (concat (pp (ispointed_MMS1))^ _).
    exact (ap (push o inl) (mon_loop1 m)).
  Defined.

  Definition constant_S1toB2 `{Funext} {M : Monoid} (m1 m2 : M) :
    B1toB2 o (S1toB1 m1 m2) = const (point (B2 M)).
  Proof.
    apply path_forall.
    intro x.
    apply (path_to_pt_B2 (m1, m2, x)).
  Defined.
  (*Plan: apD this to get something. . .*)

(*TODO: Use ap11. ap_apply_FlFr ap_to_conjp transport2
*)

(*TODO*)
  Global Instance ispointed_S1 : IsPointed S1 := base.
  Definition pS1 := Build_pType S1 _.
  Definition pB1 (M : Monoid) := Build_pType (B1 M) _.
  Definition pB2 (M : Monoid) := Build_pType (B2 M) _.
  Definition pS1toB1 {M : Monoid} (m1 m2 : M) := Build_pMap pS1 (pB1 M) (S1toB1 m1 m2) idpath.
  Definition pB1toB2 {M : Monoid} (m1 m2 : M) : pB1 M ->* pB2 M.
    refine (Build_pMap (pB1 M) (pB2 M) (B1toB2) _).
    refine (pp (m1, m2, base) ).
  Defined.

  (*TODO : pS1toB2 ==* const*)
  Lemma const_S1toB2 `{Funext} (M : Monoid) (m1 m2 : M) :
    (pB1toB2 m1 m2) o* (pS1toB1 m1 m2) = pconst pS1 (pB2 M).
  Proof.
    apply path_pmap.
    refine (Build_pHomotopy _ _).
    - intro x.
      refine (pp (m1, m2, x)).
    - cbn.
      apply (concat (concat_p1 _) (concat_1p _)^ ).
  Defined.

  Definition pmap_to_loops {A B : pType} (l : loops A) :
    (A ->* B) -> loops B :=
    fun f => (point_eq f)^ @ (ap f l) @ (point_eq f).

  (*TODO: Use this to make the result below simpler*)


  
  Definition isHom_MtoB2 `{Funext} {M : Monoid} (m1 m2: M) :
    (mon_loop2 (multM m1 m2)) = ((mon_loop2 m1) @ (mon_loop2 m2)).
  Proof.
    unfold mon_loop2. hott_simpl.
    refine (whiskerR _ _).
    apply moveR_Vp.
    hott_simpl.
(*    change (fun x : B1 M => push (inl x)) with (@B1toB2 M). *)
    apply moveR_1M.
    path_via (ap B1toB2 (ap (S1toB1 m1 m2) loop)).
    - refine (concat _ (ap_compose _ _ _)).
      refine (concat (ap_const loop (point (B2 M)))^ _).
      refine (concat _
                     (apD (fun f : S1 -> B2 M => ap f loop) (constant_S1toB2 m1 m2)^)).
      refine (concat _
                     (transport_paths_FlFr
                     (constant_S1toB2 m1 m2)^ (ap (const (point (B2 M))) loop))^ ).
      unfold const.
      rewrite ap_const.
      rewrite ap_const.
      hott_simpl.

    - path_via (ap B1toB2 ( (mon_loop1 m1) @ (mon_loop1 m2) @ (mon_loop1 (multM m1 m2))^)).
      + apply ap.
        apply S1_rec_beta_loop.
      + 
        change (fun x : B1 M => push (inl x)) with (@B1toB2 M).
        refine (concat (ap_pp _ _ _) _).
        apply concat2.
        * refine (ap_pp _ _ _).
        * refine (ap_V _ _) .
  Qed.
  

  Definition B (M : Monoid) := Tr 1 (B2 M).
  (*TODO: Give names to loops and homotopies in B.*)

  Definition BN := B (nat_monoid).

  Definition lBN_to_Z : loops (Build_pType BN _) -> Int.
Abort.
(*    Sn_trunctype:
  Univalence -> forall n : trunc_index, IsTrunc n.+1 {x : _ & IsTrunc n x} *)

    refine (paths_rec (point (BN)) (fun _ => Int) Int.zero _). (*This is constant. P must be a bit more refined. loop => +1 : Z=Z*)
        
  
  
  

(*
(*For now, define classifying space in a naive (and wrong) way.*)

Inductive B' (M : Monoid)  : Type := pt : B' M.
Axiom monoid_loop : forall M : Monoid,
               (monoid_set M) -> pt M = pt M.
Axiom isHom_B : forall M : Monoid, 
  forall a b : monoid_set M, monoid_loop M ((mult M) a b) = monoid_loop M a @ monoid_loop M b.
Definition B (M : Monoid) : Type := Trunc 2 (B' M).
*)

(*First define a one-point space with one path for every element in M. This should be the 1-skeleton of B M.*)
Definition B1 (M : Monoid) := Coeq (const (A:=monoid_set M) tt) (const (A:=monoid_set M) tt).
(*The two-skeleton is the same as demanding that concat respects multiplication in M.*)

(*TODO: Make this general for a map M*M -> M. It might also be that I am really showing that B is functorial. . .*)
Definition loop_o_mult `{Funext} {M : Monoid} : B1 M *B1 M -> B1 M.
  apply prod_rect.
  refine (Coeq_rec (B1 M -> B1 M) _ _).
  - (*First argument is pt *)
    intros [].
    refine (Coeq_rec (B1 M) _ _).
    + (*Second argument is pt *)
      exact coeq. (*This corresponds to (pt,pt) => pt*)
    + (*Second argument is monoid_loop a *)
      apply cp. (*This corresponds to (pt, loop) => loop*)
  - (*First argument is monoid_loop a *)
    intro a.
    apply path_arrow.
    refine (Coeq_ind _ _ _).
    + (*Second argument is pt *)
      intros [].
      exact (cp a). (*This corresponds to (loop, pt) => loop*)
    + (*Second argument is monoid_loop b*)
      (*The solution here should correspond to loop(ab)*)
      intro b.
      simpl. (*Use transport_paths_FlFr, og Coeq_rec_beta_cp*)
      path_via
        (((ap (Coeq_rec (B1 M) coeq cp) (cp b))^ @ (cp a)) @ ap (Coeq_rec (B1 M) coeq cp) (cp b)).
      { refine (transport_paths_FlFr _ _). }
(*      rewrite Coeq_rec_beta_cp. (*Want to do this transparently.*)*)
      path_via
      (((cp b)^ @ cp (f:=(const (A:=monoid_set M) tt)) (g:=(const (A:=monoid_set M) tt)) a) @ cp b).
      * apply concat2.
        { apply whiskerR.
          apply inverse2.
          apply Coeq_rec_beta_cp.
        }
        refine (Coeq_rec_beta_cp _ _ _ _).
      * 
    
    
      

Definition B_rec {M : Monoid}
           (P : Type) (p : P)
           (loop' : (monoid_set M) -> p = p)
           (ishom : (forall a b : monoid_set M, loop' ((mult M) a b) = loop' a @ loop' b))
            : B M -> P.
  Coeq_rec P (unit_name p) loop. 

  
                          