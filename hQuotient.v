Require Import HoTT.
Require Import UnivalenceAxiom.
Notation "X ->* Y" := (pMap (Build_pType X _) (Build_pType Y _)).
Infix "o*" := pmap_compose.
Load stuff.
Definition pconst (X Y : pType) : X ->* Y :=
  Build_pMap X Y (const (point Y)) idpath.

Section Homotopy_Quotient.

  Definition hQuotient {X Y : Type} (i : X -> Y) :=
    pushout i (const tt).

  Definition to_quotient {X Y : Type} (i : X -> Y) :
    Y -> hQuotient i :=
    fun y => push (inl y).

  Definition functor_quotient {X Y X' Y'} {i : X -> Y} {i' : X' -> Y'}
             (f : X -> X') (g : Y -> Y') :
             g o i == i' o f -> hQuotient i -> hQuotient i'.
  Proof.
    intro square.
    unfold hQuotient. unfold pushout.
    srapply @functor_coeq.
    exact f. exact (functor_sum g idmap).
    - intro x.
      cbn. apply (ap inl). apply square.
    - intro x. reflexivity.
  Defined.
End Homotopy_Quotient.

Section Pointed_Homotopy_Quotient.
  Global Instance ispointed_quotient {X Y : pType} (i : X ->* Y) : IsPointed (hQuotient i) := push (inr tt).
  Definition pQuotient {X Y : pType} (i : X ->* Y) : pType :=
    Build_pType (hQuotient i) _.

  Definition to_quotient_pt {X Y : pType} (i : X ->* Y) : Y ->* hQuotient i.
  Proof.
    apply (Build_pMap Y (pQuotient i) (to_quotient i)).
    unfold to_quotient.
    cbn. unfold ispointed_quotient.
    refine (_ @ (pp (point X))). apply (ap (push o inl)). exact (point_eq i)^.
  Defined.

  Definition pt_functor_quotient {X Y X' Y' : pType} {i : X ->* Y} {i' : X' ->* Y'}
             (f : X ->* X') (g : Y ->* Y') :
             pHomotopy (g o* i) (i' o* f) -> (hQuotient i ->* hQuotient i').
  Proof.
    intro square.
    srapply @Build_pMap; cbn.
    - apply (functor_quotient f g). cbn. apply square.
    - reflexivity.
  Defined.

  Definition composition_is_null {X Y : pType} (i : X ->* Y) :
    pHomotopy ((to_quotient_pt i) o* i) (pconst X (pQuotient i)).
  Proof.
    srapply @Build_pHomotopy.
    - intro x. exact (pp x).
    - cbn. unfold to_quotient.
      refine (concat_p1 _ @ _).
      refine ((concat_1p _)^ @ _).
      refine (_ @ concat_pp_p _ _ _).
      apply whiskerR.
      refine (_ @ ap_pp (push o inl) _ _).
      apply inverse.
      refine (_ @ ap_1 _ (push o inl)).
      apply (ap (ap (push o inl))). apply concat_pV.
  Defined.    
  
  (* Loops in the quotient coming from X are killed *)
  Definition kill_loop {X Y : pType} (i : X ->* Y) (alpha : loops X) :
    (loops_functor (to_quotient_pt i) o* (loops_functor i)) alpha = idpath.
  Proof.
    refine ((pointed_htpy (loops_functor_compose (to_quotient_pt i) i) alpha)^ @ _).
    refine (ap (fun f => loops_functor f alpha) (path_pmap (composition_is_null i)) @ _).
    unfold loops_functor. cbn.
    refine (concat_1p _ @ _). refine (concat_p1 _ @ _).
    apply ap_const.
  Defined.

  Definition natural_kill_loop_top {X Y X' Y': pType} {i : X ->* Y} {i' : X' ->* Y'}
             (f : X ->* X') (g : Y ->* Y') (square : pHomotopy (g o* i) (i' o* f)) (alpha : loops X) :
    (loops_functor (pt_functor_quotient f g square)) ((loops_functor (to_quotient_pt i) o* loops_functor i) alpha) =
    (loops_functor (to_quotient_pt i') o* (loops_functor i')) (loops_functor f alpha).
  Proof.
    transitivity ((loops_functor ((to_quotient_pt i') o* i' o* f)) alpha).
    transitivity ((loops_functor ((pt_functor_quotient f g square) o* (to_quotient_pt i) o* i)) alpha).
    - apply inverse.
      refine ((pointed_htpy (loops_functor_compose (pt_functor_quotient f g square o* to_quotient_pt i) i)) alpha @ _).
      refine ((pointed_htpy (loops_functor_compose (pt_functor_quotient f g square) (to_quotient_pt i)))
                ((loops_functor i) alpha)).
    - apply (ap (fun fn => loops_functor fn alpha)).
      transitivity ((to_quotient_pt i') o* (i' o* f)).
      

      
      apply inverse.
      refine ((pointed_htpy (loops_functor_compose (to_quotient_pt i' o* i') f) alpha @ _)).
      refine ((pointed_htpy (loops_functor_compose (to_quotient_pt i') i')) ((loops_functor f) alpha) @ _).
      
      
      cbn.
    
    refine ((loops_functor_compose    )^
    
    cbn. rewrite concat_1p. rewrite concat_p1.
    
    repeat rewrite ap_pp. unfold to_quotient. unfold functor_quotient. unfold functor_coeq. unfold pp.
    path_induction_hammer.
    
    rewrite Coeq_rec_beta_cp.
    repeat rewrite <- ap_compose. repeat rewrite ap_pp.
    
  

  (* Now the difficult thing *)
  Definition natural_kill_loop {X Y X' Y' : pType} {i : X ->* Y} {i' : X' ->* Y'}
             (f : X ->* X') (g : Y ->* Y') (square : pHomotopy (g o* i) (i' o* f) )
    (alpha : loops X) : Type.
    ap (loops_functor (pt_functor_quotient f g square)) (kill_loop i alpha) =
    kill_loop i' (loops_functor f alpha).



    (loops_functor (pt_functor_quotient f g square)) ((loops_functor (to_quotient_pt i) o* loops_functor i) alpha) =
       (loops_functor (pt_functor_quotient f g square)) 1
    

    

