Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import trunc_lemmas.
Load monoids_and_groups.
Require Import set_quotient.



(* Defining sets with a monoid action (see MacLane, p5) *)
Section Monoid_action.
  Open Scope monoid_scope.

  Record Monoid_Action (M : Monoid) (X : hSet) := {function_of : M -> (X -> X);
                                                   assoc_function_of : forall (m1 m2 : M) (x : X),
                                                       function_of (m1 + m2) x = function_of m1 (function_of m2 x);
                                                   preserve_id_function_of : forall x : X,
                                                       function_of (mon_id) x = x
                                                  }.
  Global Arguments function_of {M} {X} _ _ _.

    (* [S X] *)
  (* The quotient X/~, where x ~ y if there is a s : S s.t. s + x = y *)
  Definition grp_compl_relation {M : Monoid} (X : hSet) (a : Monoid_Action M X) : relation X
    := (fun x y => {m : M | function_of a m x = y}).

  Lemma relation_is_mere {M : Monoid} (X : hSet)
           (a : Monoid_Action M X)
           (isfree_a : forall (m1 m2 : M) (x : X), (function_of a m1 x = function_of a m2 x -> m1 = m2))
    : is_mere_relation X (grp_compl_relation X a).
  Proof.
    intros.
    unfold grp_compl_relation.
    apply (trunc_sigma' _).
    - intros [m1 p1] [m2 p2]. simpl.
      apply (contr_inhabited_hprop _).
      exact (isfree_a m1 m2 x (p1 @ p2^)).
  Qed.

End Monoid_action.

Section Group_Completion_Quotient.
  Open Scope monoid_scope.
  Variable M : Symmetric_Monoid.
  Variable right_cancellation_M : forall l m n : M, m + l = n + l -> m = n.
  
  Definition product_action : Monoid_Action M (BuildhSet (M*M)).
  Proof.
    srapply (@Build_Monoid_Action).
    (* The action *)
    - intro m.
      intros [a b].
      exact (m + a, m + b).
    - intros m1 m2 [x1 x2].
      apply path_prod; apply mon_assoc.
    - intros [x1 x2]. apply path_prod; apply mon_lid.
  Defined.
  
  Definition right_cancel_action : forall (m1 m2 : M) (x : M*M),
      function_of product_action m1 x = function_of product_action m2 x -> m1 = m2.
  Proof.
    intros m1 m2 [x1 x2]. simpl.
    intro p.
    apply (right_cancellation_M x1).
    exact (ap fst p).
  Defined.

  Instance product_action_is_mere : is_mere_relation (M*M) (grp_compl_relation (BuildhSet (M*M)) product_action) :=
    relation_is_mere (BuildhSet (M*M)) (product_action) right_cancel_action.

  Definition group_completion  :=
    set_quotient (grp_compl_relation (BuildhSet (M*M)) product_action).

  Definition grp_compl_mult : group_completion -> group_completion -> group_completion.
  Proof.
    srapply @set_quotient_rec2; simpl.
    intros [a1 a2] [b1 b2].
    apply class_of.
    exact (a1 + b1, a2 + b2).
    - intros [a1 a2] [b1 b2] [c1 c2].
      intros [s p]. simpl in p.
      apply related_classes_eq. red.
      exists s. simpl.
      apply path_prod; simpl; refine (mon_assoc^ @ _).
      + apply (ap (fun x => x + c1)). apply (ap fst p).
      + apply (ap (fun x => x + c2)). apply (ap snd p).
    - intros [a1 a2] [b1 b2] [c1 c2].
      intros [s p]. simpl in p.
      apply related_classes_eq. red.
      exists s. simpl.
      apply path_prod; simpl;
      refine (mon_assoc^ @ _).
      + refine (ap (fun x => x + b1) mon_sym @ _).
        refine (mon_assoc @ _).
        apply (ap (mon_mult a1)). apply (ap fst p).
      + refine (ap (fun x => x + b2) mon_sym @ _).
        refine (mon_assoc @ _).
        apply (ap (mon_mult a2)). apply (ap snd p).
  Defined.

  Definition grp_compl_inv : group_completion -> group_completion.
  Proof.
    srapply @set_quotient_functor.
    - intros [a1 a2]. exact (a2,a1).
    - intros [a1 a2] [b1 b2].
      intros [s p]. 
      exists s. simpl in p. simpl.
      apply path_prod.
      + apply (ap snd p). + apply (ap fst p).
  Defined.

  Definition grp_compl_linv :
    forall x : group_completion,
      grp_compl_mult (grp_compl_inv x) x = class_of _ (mon_id,  mon_id).
  Proof.
    apply set_quotient_ind_prop.
    - intro x.
      apply (set_quotient_set _ _).
    - intros [a1 a2]. simpl.
      apply inverse.
      apply related_classes_eq. red.
      exists (a1 + a2). simpl.
      apply path_prod; simpl.
      + refine (mon_rid _ @ _). apply mon_sym.
      + apply mon_rid.
  Defined.

  Definition grp_compl_rinv :
    forall x : group_completion,
      grp_compl_mult x (grp_compl_inv x) = class_of _ (mon_id,  mon_id).
  Proof.
    apply set_quotient_ind_prop.
    - intro x.
      apply (set_quotient_set _ _).
    - intros [a1 a2]. simpl.
      apply inverse.
      apply related_classes_eq. red.
      exists (a1 + a2). simpl.
      apply path_prod; simpl.
      + apply mon_rid.
      + refine (mon_rid _ @ _). apply mon_sym.
  Defined.

  (* Is group *)
      
        

      
    
    

  
      
      
      
End Group_Completion_Quotient.









    
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

  Definition grp_compl_set := Trunc 0 (Coeq as_bs fst).
  Definition grp_compl  (a b : S) : grp_compl_set
    := tr (coeq (a, b)).
  Definition grp_compl_mult : grp_compl_set -> grp_compl_set -> grp_compl_set.
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
        exact (grp_compl (m1 + n1) (m2 + n2)).
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
          
  Definition grp_compl_id : grp_compl_set := grp_compl (mon_id S) (mon_id S).
  
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

  Definition grp_compl_inv : grp_compl_set -> grp_compl_set.
  Proof.
    apply Trunc_rec.
    srapply @Coeq_rec.
    - intros [m1 m2].
      exact (grp_compl m2 m1).
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
            grp_compl_set
            grp_compl_mult grp_compl_id grp_compl_assoc grp_compl_lid grp_compl_rid )
         grp_compl_inv grp_compl_linv grp_compl_rinv)
      grp_compl_sym.

  
  (*Defining the (monoid) homomorphism from a monoid to its group completion*)
  Definition to_groupcompletion : Homomorphism S group_completion.
    srapply @Build_Homomorphism.
    - (*The map on set level*)
      intro m.
      exact (grp_compl m (mon_id S)).
    - (*The map preserves identity*)
      exact idpath.
    - (*The map is an isomorphism*)
      intros m1 m2.
      apply (ap tr); apply (ap coeq).
      apply path_prod.
      exact idpath.
      exact (mon_lid (mon_id S))^.
  Defined.

  (* Definition eta_group_completion : forall g : group_completion, *)
  (*   exists ab : S*S, g = grp_compl (fst ab) (snd ab). *)
  (* Proof. *)
  (*   srapply @Trunc_ind. intro aa.  *)

  Definition gcp : forall a b : S,
                     grp_compl a b = to_groupcompletion a - to_groupcompletion b.
  Proof.
    intros a b.
    unfold to_groupcompletion. simpl. unfold grp_compl. apply (ap tr).
    refine ((cp (a, b, mon_id S))^ @ _). apply (ap coeq). unfold as_bs.
    apply (ap (fun c : S => (a + mon_id S, c))).
    exact (mon_rid b @ (mon_lid b)^).
  Defined.

  (* Definition badname : forall a b : S, *)
  (*                        to_groupcompletion a = to_groupcompletion b -> exists s : S, a + s = b + s. *)
  (* Proof. *)
  (*   intros a b p. *)
  (*   assert (grp_compl a b = grp_id (group_completion)). *)
  (*   { refine (gcp a b @ _). *)
  (*     apply (grp_moveR_gV (G := group_completion)). *)
  (*     exact (p @ (grp_lid (to_groupcompletion b))^). } *)
  (*   unfold group_completion in X. simpl in X. unfold grp_compl_id in X. unfold grp_compl in X. *)
  (* Admitted. *)


  (*    (* Check (equiv_path_Tr (n := -1) (coeq (a, b)) (coeq (mon_id S, mon_id S)))^-1 X. *) *)
  (* (*   (* `Arguments foo ... : simpl nomatch` *) *) *)
  

  (* Definition injective_to_groupcompletion (right_cancel : forall a b s : S, a + s = b + s -> a = b) : *)
  (*   forall a b : S, to_groupcompletion a = to_groupcompletion b -> a = b. *)
  (* Proof. *)
  (*   (* assert (retract : group_completion -> S). *) *)
  (*   (* { srapply @Trunc_rec. exact (mon_isset S). *) *)
  (*   (*   srapply @Coeq_rec. *) *)
  (*   (*   - exact fst. *) *)
  (*   (*   - intros [[a b] s]. simpl. *) *)
  (*   (*     refine (mon_assoc^ @ _). *) *)
  (*   (*     refine (grp_whiskerL  *) *)
  (*   (*     apply (ap (fun c => a + c)). *) *)
  (*   (*     refine (mon_assoc @ _). *) *)
        
    
  (*   intros a b. *)
  (*   unfold to_groupcompletion. simpl. unfold grp_compl. *)
  (*   intro p. *)
  (*   (* Check grp_moveR_gV (p @ (grp_lid (to_groupcompletion b))^). *) *)
  (*   (* apply grp_moveL_1M. *) *)
  (*   assert (to_groupcompletion a - to_groupcompletion b = grp_id _). *)
  (*   { apply grp_moveR_gV. *)
  (*     refine (p @ _). *)
  (*     exact (grp_lid (to_groupcompletion b))^. } *)
  (*   unfold to_groupcompletion in p. simpl in p. *)

  (*   (* apply (grp_whiskerR (c := grp_id _)) in p. *) *)
  (*   (* apply grp_moveL_Vg in p. *) *)
  (*   (* unfold grp_inv in p.  *) *)
  (*   (* unfold to_groupcompletion in p. simpl in p. *) *)
  (*   (* set (p' := ((equiv_path_Tr (coeq (a , mon_id S)) (coeq (b, mon_id S)))^-1 p)). (*This takes long *) time to run. . .*) *)
  (*   Admitted. *)
    

  
    
End Group_completion.

Arguments to_groupcompletion {S}.
(* Arguments grp_compl {S}. *)

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
        exact (tr (coeq (f m, f n))).
      + (*The map is well defined.*)
        intros [[a b] s].
        apply (ap tr).
        refine (_ @ cp (f a, f b, f s)).
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
        
  Definition natural_to_groupcompletion {S S' : Symmetric_Monoid} (h : Hom S' S):
    to_groupcompletion oH h = (functor_group_completion h) oH to_groupcompletion.
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
  
  Definition hom_map_extend_to_inv {S : Symmetric_Monoid} {G : Group} :
    Homomorphism S G -> ((group_completion S) -> G).
  Proof.
    intro f.
    refine (Trunc_rec (H:=grp_isset _) _).
    srapply @Coeq_rec.
    + (*The variable is fixed*)
      intro m12.
      exact ((f (fst m12)) - (f (snd m12))).
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

  Definition extend_to_inv {S : Symmetric_Monoid} {G : Group} :
    Homomorphism S G -> Homomorphism (group_completion S) G.
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
        refine (grp_whiskerL (ap grp_inv (ap f (mon_sym))) @ _).
        refine (path_group2 (preserve_mult f) ((ap grp_inv (preserve_mult f))) @ _).
        refine (grp_assoc^ @ _ @ grp_assoc).
        apply grp_whiskerL.
        refine (grp_whiskerL grp_inv_distr @ _).
        refine (grp_assoc @ _ @ grp_assoc^).
        apply grp_whiskerR.
        apply grp_moveR_gV.
        refine (_ @ grp_assoc).
        apply grp_moveL_Vg.
        refine ((preserve_mult f)^ @ _ @ preserve_mult f).
        apply (ap f). apply mon_sym.
      + (*First variable runs along cp*)
        intro abs. apply (grp_isset G).
    - (*Second variable runs along cp*)
      intro abs. apply (grp_isset G).
  Defined.

  
  Theorem grp_compl_adjoint (S : Symmetric_Monoid) (G : Group) :
    Homomorphism S G <~> Homomorphism (group_completion S) G.
  Proof.
    refine (equiv_adjointify extend_to_inv (fun f => f oH to_groupcompletion) _ _).
    (*Prove that the maps are inverses*)
    - intro f.
      refine (path_hom _ _ _) ; simpl.
      apply path_forall.
      (*Trunc_ind uses about 5 minutes to find a proof of this, faster to prove it manually.*)
      assert (Pt : forall m : (group_completion S),
                   IsTrunc 0
                           (hom_map_extend_to_inv (f oH to_groupcompletion) m = f m)).
      { intro m. exact (@trunc_succ -1 _ (mon_isset _ _ _)). }
      refine (@Trunc_ind 0 (Coeq (as_bs S) fst) _ Pt _ ).
      srapply @Coeq_ind. 
      + (*Variable fixed*)
        intros [m1 m2].
        simpl.
        apply grp_moveR_gV.
        refine (_ @ preserve_mult f).
        apply (ap f); apply (ap tr).
        refine ((cp (m1, mon_id S, m2))^ @ _); unfold as_bs.
        apply (ap coeq).
        apply (ap (fun s : S => (m1 + m2, s))).
        exact (mon_lid m2 @ (mon_rid m2)^).
      + (*Variable runs along cp*)
        intro abs.
        apply (grp_isset G).
    - intro f.
      refine (path_hom _ _ _) ; simpl.
      apply path_forall.
      intro m.
      apply grp_moveR_gV.
      refine ((grp_rid _)^ @ _).
      exact (grp_whiskerL (preserve_id f)^ ).
  Defined.

  (*Naturality follows from [natural_to_groupcompletion], since the map [Hom (group_completion S) A -> Hom S A is exactly precomposing with [to_groupcompletion].*)

  Definition grp_compl_unit (S : Symmetric_Monoid) : Hom S (group_completion S) :=
    (grp_compl_adjoint S (group_completion S))^-1 idhom.
  Definition grp_compl_counit (A : Abelian_Group) : Hom (group_completion A) A :=
    grp_compl_adjoint A A idhom.
  

End Adjointness.

Section Group_complete_nat.
  (* Definition int_group : Group. *)
  (* Proof. *)
  (*   srapply @Build_Group. *)
  (*   - srapply (@Build_Monoid Int). *)
    
  
  Definition grpcpl_nat_is_int : group_completion nat_symm_monoid <~> Int.
  Proof.
    srapply @equiv_adjointify.
    - apply Trunc_rec.
      srapply @Coeq_rec.
      + intros [m n]. exact (Int_sum (nat_to_int m) (Int_minus (nat_to_int n))).
      + intros [[l m] n]. simpl.
