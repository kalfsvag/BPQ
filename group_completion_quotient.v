Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import trunc_lemmas.
Load monoids_and_groups.
Require Import set_quotient.



(* Defining sets with a monoid action (see MacLane, p5) *)
Section Monoid_action.
  Open Scope monoid_scope.


  (* (* move this closer to definition *) *)
  (* Global Instance isset_hom {M N : Monoid} : IsHSet (Hom M N). *)
  (* Proof. *)
  (*   apply (trunc_equiv' _ (issig_hom M N)). *)
  (* Defined.   *)

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
  Definition group_completion_group : Group.
  Proof.
    srapply @Build_Group.
    srapply @Build_Monoid.
    - exact (BuildTruncType 0 group_completion).
    - simpl.
      apply grp_compl_mult.
    - simpl.
      apply class_of.
      exact (mon_id, mon_id).
    - unfold associative. simpl.
      apply (set_quotient_ind_prop _
                (fun a : group_completion  => forall b c : group_completion,
                     grp_compl_mult (grp_compl_mult a b) c = grp_compl_mult a (grp_compl_mult b c))).
      intro a.
      apply (set_quotient_ind_prop _
             (fun b : group_completion => forall c : group_completion,
                  grp_compl_mult (grp_compl_mult (class_of (grp_compl_relation (BuildhSet (M * M))
                                                                               product_action) a) b) c
                  =
                  grp_compl_mult (class_of (grp_compl_relation (BuildhSet (M * M)) product_action) a)
                                                       (grp_compl_mult b c))).
      intro b.
      apply (set_quotient_ind_prop _ _).
      intro c.
      revert a b c.
      intros [a1 a2] [b1 b2] [c1 c2]. simpl.
      apply (ap (class_of (grp_compl_relation (BuildhSet (M * M)) product_action))).
      apply path_prod; apply mon_assoc.
    - unfold left_identity.
      apply (set_quotient_ind_prop _ _).
      intros [a1 a2]. simpl.
      apply (ap (class_of (grp_compl_relation (BuildhSet (M * M)) product_action))).
      apply path_prod; apply mon_lid.
    - unfold right_identity.
      apply (set_quotient_ind_prop _ _).
      intros [a1 a2]. simpl.
      apply (ap (class_of (grp_compl_relation (BuildhSet (M * M)) product_action))).
      apply path_prod; apply mon_rid.
    - simpl.
      apply grp_compl_inv.
    - unfold left_inverse. simpl.
      apply grp_compl_linv.
    - unfold right_inverse. simpl.
      apply grp_compl_rinv.
  Defined.

  Definition to_groupcompletion : Hom M (group_completion_group).
  Proof.
    srapply @Build_Homomorphism.
    - intro a.
      apply class_of.
      exact (a, mon_id).
    - simpl. reflexivity.
    - simpl. intros.
      apply (ap (class_of (grp_compl_relation (BuildhSet (M * M)) product_action))).
      apply path_prod. reflexivity. simpl.
      apply inverse. apply mon_lid.
  Defined.


  (* (* move this *) *)
  (* Definition antihom_inv {G : Group} : *)
  (*   forall (g1 g2 : G), *)
  (*     grp_inv (g1 + g2) = grp_inv g2 + grp_inv g1. *)
  (* Proof. *)
  (*   intros. *)
  (*   apply grp_moveL_Vg. *)
  (*   apply grp_moveL_V1. *)
  (*   refine (mon_assoc^ @ _). *)
  (*   apply (grp_rinv (g1 + g2)). *)
  (* Defined. *)

  Definition inverse_precompose_groupcompletion (G : Abelian_Group) :
    Hom M G -> Hom group_completion_group G.
  Proof.
    intro g.
    srapply @Build_Homomorphism.
    srapply @set_quotient_rec.
    + intros [m1 m2].
      exact (g m1 - g m2).
    + intros [m1 m2] [n1 n2].
      intros [s p]. simpl in p.
      set (p1 := ap fst p). simpl in p1. destruct p1.
      set (p2 := ap snd p). simpl in p2. destruct p2.
      rewrite preserve_mult. rewrite preserve_mult.
      rewrite grp_inv_distr.
      rewrite (grp_sym (a := g s) (b := g m1)).
      rewrite (grp_sym (a := - g m2) (b := - g s)).
      refine (_ @ mon_assoc^).
      refine (_ @ (ap (fun x => g m1 + x) mon_assoc)).
      rewrite grp_rinv. rewrite mon_lid.
      reflexivity.
    + simpl.
      apply grp_rinv.
    + intro m.
      apply (set_quotient_ind_prop _ _). intros [n1 n2].
      revert m.
      apply (set_quotient_ind_prop _ _).
      intros [m1 m2]. simpl.
      rewrite preserve_mult. rewrite preserve_mult.
      refine (mon_assoc @ _ @ mon_assoc^).
      apply (ap (fun x => g m1 + x)).
      rewrite grp_inv_distr.
      refine (mon_assoc^ @ _ @ mon_assoc).
      refine (grp_sym @ _).
      apply (mon_assoc^).
  Defined.

  

  Definition universal_groupcompletion (G : Abelian_Group) :
    IsEquiv (fun f : Hom group_completion_group G => compose_hom f to_groupcompletion).
  Proof.
    srapply @isequiv_adjointify.
    - apply inverse_precompose_groupcompletion.
    - unfold Sect. intro f.
      apply path_hom. apply path_arrow. intro x. simpl.
      rewrite preserve_id.
      rewrite inv_id.
      apply mon_rid.
    - unfold Sect.
      intro g. apply path_hom. apply path_arrow. intro x.  revert x.
      apply (set_quotient_ind_prop _ _).
      intros [m1 m2]. simpl.
      rewrite <- preserve_inv.
      rewrite <- preserve_mult. simpl.
      set (cl := class_of (grp_compl_relation (BuildhSet (M * M)) product_action)).
      apply (ap (g o cl)). clear cl.
      apply path_prod.
      apply mon_rid. apply mon_lid.
  Defined.
      
    
  (* This is more in line with the proof in the thesis *)
  Definition universal_groupcompletion' (G : Abelian_Group) :
    IsEquiv (fun f : Hom group_completion_group G => compose_hom f to_groupcompletion).
  Proof.
    apply (isequiv_isepi_ismono
             (BuildhSet (Hom group_completion_group G))
             (BuildhSet (Hom M G))).
    - apply issurj_isepi.
      apply BuildIsSurjection. intro f.
      apply tr. unfold hfiber.
      exists (inverse_precompose_groupcompletion G f).
      apply path_hom. apply path_arrow.
      intro x. simpl.
      rewrite preserve_id. rewrite inv_id. apply mon_rid.
    - apply isinj_ismono.
      unfold isinj.
      intros f g.
      intro H.
      apply path_hom. apply path_arrow.
      intro x. revert x.
      apply (set_quotient_ind_prop _ _).
      intros [x1 x2].
      set (cl := class_of (grp_compl_relation (BuildhSet (M * M)) product_action)).
      cut (f (cl (x1, mon_id)) - f (cl (x2, mon_id)) = g (cl (x1, mon_id)) - g (cl (x2, mon_id))).
      { intro p. refine (_ @ p @ _).
        - rewrite <- preserve_inv.
          rewrite <- preserve_mult.
          apply (ap (f o cl)).
          apply path_prod; apply inverse.
           apply mon_rid. apply mon_lid.
        - rewrite <- preserve_inv.
          rewrite <- preserve_mult.
          apply (ap (g o cl)).
          apply path_prod.
            apply mon_rid. apply mon_lid. }
      apply (ap011 (@mon_mult G)).
      apply (ap10 (equiv_inverse (path_hom (f oH to_groupcompletion) (g oH to_groupcompletion)) H) x1).
      apply (ap grp_inv).
      apply (ap10 (equiv_inverse (path_hom (f oH to_groupcompletion) (g oH to_groupcompletion)) H) x2).
  Defined. 
       
End Group_Completion_Quotient.





