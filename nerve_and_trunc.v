Require Import HoTT.

(* Require Import finite_lemmas path_lemmas pointed_lemmas delooping *)
(*                permutations BSigma group_complete_1type. *)
Require Import Categories.Functor Category.Morphisms.
Require Import Category.Core. 
Require Import set_quotient.
Add Rec LoadPath "~/Coq-projects/groupoids" as GR.
From GR Require Import cquot cquot_principles.

Definition cat_isomorphic_compose {C D E : PreCategory}
           (G : cat.isomorphic D E) (F : cat.isomorphic C D)
  : cat.isomorphic C E.
Proof.
  destruct G as [G iso_G]. destruct F as [F iso_F].
  exists (G o F)%functor.
  destruct iso_G as [ff_G equiv_G].
  destruct iso_F as [ff_F equiv_F].
  srefine (_ , isequiv_compose).
  unfold cat.fullyfaithful in *.
  intros s d. 
  unfold Functor.Composition.Core.compose. simpl.
  apply isequiv_compose.
Defined.



Definition double_transport {A B : Type} (P : A -> B -> Type)
           {a a' : A} {b b' : B}
           (p : a = a') (q : b = b') :
  P a b -> P a' b'.
Proof.
  destruct p. destruct q. exact idmap.
Defined.



Definition double_transport_compose {A B : Type} (P : A -> B -> Type)
           {a a' a'' : A} {b b' b'' : B}
           (p : a = a') (p' : a' = a'')
           (q : b = b') (q' : b' = b'')
  : double_transport P (p @ p') (q @ q') ==
    double_transport P p' q' o double_transport P p q.
Proof.
  intro x.
  destruct q'. destruct q.
  destruct p'. destruct p. reflexivity.
Defined.


Definition path_functor' {C D : PreCategory} (F G : Functor C D)
           (p0 : forall c : C, F c = G c)
           (p1 : forall (c d : C) (f : morphism C c d),
               double_transport (morphism D) (p0 c) (p0 d) (morphism_of F f )
               = morphism_of G f)
  : F = G.
Proof.
  srapply @path_functor.
  - apply path_forall. exact p0.
  - apply path_forall. intro s. apply path_forall. intro d.
    apply path_arrow. intro f.
    refine (_ @ p1 _ _ f).
    rewrite <- (apD10_path_forall (object_of F) (object_of G) p0 s).
    rewrite <- (apD10_path_forall (object_of F) (object_of G) p0 d).
    change (path_forall (Core.object_of F) (Core.object_of G) p0) with
    (path_forall F G p0).
    destruct (path_forall F G p0). simpl.
    reflexivity.
Defined.




Section Pi_0.
Definition pi0_cat (C : PreCategory) : Type
  := set_quotient (morphism C).

Definition class_of_pi0cat {C : PreCategory} : C -> pi0_cat C :=
  class_of (morphism C).

Definition path_pi0_cat {C : PreCategory} {c d : C} (f : morphism C c d)
  : class_of_pi0cat c = class_of_pi0cat d.
Proof.
  apply related_classes_eq. exact f.
Defined.  

Definition pi0_cat_cquot (C : PreCategory) :
  pi0_cat C <~> Trunc 0 (cquot C).
Proof.
  srapply @equiv_adjointify.
  - srapply @set_quotient_rec.
    + intro c. apply tr. apply (ccl C c).
    + simpl. intros x y f.
      apply (ap tr).
      apply ccleq. exact f.
  - srapply @Trunc_rec.
    srapply @cquot_rec.
    + apply class_of.
    + intros c d f.
      apply related_classes_eq. exact f.
    + simpl. intro c.
      apply set_quotient_set.
    + simpl. intros.
      apply set_quotient_set.
  - intro x. revert x.
    srefine (Trunc_ind _ _).
    srefine (cquot_ind_prop _ _ _).
    simpl. reflexivity.
  - intro x. revert x.
    srefine (set_quotient_ind_prop _ _ _).
    simpl. reflexivity.
Defined.
End Pi_0.

Section Cat_sum.


(* Given a family of categories over a type, we can define the sum *)
Definition cat_sum_obj (X : Type) (C : X -> PreCategory) :=
  {x : X & object (C x)}.

Definition morphism_over {X : Type} (C : X -> PreCategory)
           {x0 x1 : X} (p : x0 = x1) (c0 : C x0) (c1 : C x1) : Type.
Proof.
  destruct p.
  exact (morphism (C x0) c0 c1).
Defined.

Global Instance isset_morphism_over {X : Type} (C : X -> PreCategory)
       {x0 x1 : X} (p : x0 = x1) (c0 : C x0) (c1 : C x1)
  : IsHSet (morphism_over C p c0 c1).
Proof.
  destruct p. simpl. exact _.
Defined.

Definition morphism_over_compose {X : Type} (C : X -> PreCategory)
           {x0 x1 x2 : X} {p1 : x0 = x1} {p2 : x1 = x2}
           {c0 : C x0} {c1 : C x1} {c2 : C x2}
  : morphism_over C p2 c1 c2 ->  morphism_over C p1 c0 c1
    -> morphism_over C (p1 @ p2) c0 c2.
Proof.
  intros f g.
  destruct p2. destruct p1.
  simpl. exact (f o g)%morphism.
Defined.

Definition cat_sum_morph (X : Type) (C : X -> PreCategory)
  : cat_sum_obj X C -> cat_sum_obj X C -> Type.
Proof.
  intros [x a] [y b].
  exact {p : x = y & morphism_over C p a b}.
Defined.

Definition cat_sum (X : Type) {istrunc_X : IsTrunc 1 X}
           (C : X -> PreCategory) : PreCategory.
Proof.
  srapply (Build_PreCategory (cat_sum_morph X C)).
  (* identity *)
  - intros [x a]. exists idpath. apply identity.
  - intros [x a] [y b] [z c].
    intros [p f] [q g].
    exists (q @ p).
    apply (morphism_over_compose C f g).
  - intros [x a] [y b] [z c] [w d].
    intros [p f] [q g] [r h].
    destruct r. destruct q. destruct p. simpl in *.
    srapply (@path_sigma).
    { reflexivity. } apply associativity.
  - intros [x a] [y b]. intros [p f].
    destruct p.
    srapply (@path_sigma).
    { reflexivity. } simpl.
    apply left_identity.
  - intros [x a] [y b]. intros [p f].
    destruct p.
    srapply (@path_sigma).
    { reflexivity. } simpl.
    apply right_identity.
Defined.



Definition include_summand (X : Type) {istrunc_X : IsTrunc 1 X}
           (C : X -> PreCategory) (x : X)
  : Functor (C x) (cat_sum X C).
Proof.
  srapply @Build_Functor.
  - intro c. exact (x; c).
  - intros s d f. simpl.
    exists idpath. exact f.
  - intros a b c f g. simpl. reflexivity.
  - reflexivity.
Defined.

Definition univ_cat_sum (X : Type) {istrunc_X : IsTrunc 1 X}
           (C : X -> PreCategory) (D : PreCategory)
  :  Functor (cat_sum X C) D <~> (forall x : X, Functor (C x) D).
Proof.
  srapply @equiv_adjointify.
  - intro F. intro x.
    refine (F o _)%functor.
    apply include_summand.
  - intro F.
    srapply @Build_Functor.
    + intros [x c]. exact (F x c).
    + intros [x1 c1] [x2 c2]. simpl.
      intros [p f]. simpl. destruct p. simpl in *.
      apply (morphism_of (F x1)). exact f.
    + intros [x1 c1] [x2 c2] [x3 c3].
      intros [p f] [q g]. simpl.
      destruct q. destruct p. simpl.
      apply composition_of.
    + simpl. intro x.
      apply identity_of.
  - simpl. intro F. apply path_forall.
    intro x. srapply @path_functor'.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. intro F.
    srapply @path_functor'.
    + simpl. intros [x c]. reflexivity.
    + simpl. intros [x1 c1] [x2 c2] [p f].
      destruct p. reflexivity.
Defined.

Definition cat_sum_to_groupoid (X : Type) (Y : X -> Type)
           {istrunc_X : IsTrunc 1 X} {istrunc_Y : forall x : X, IsTrunc 1 (Y x)}
  : Functor (cat_sum X (fun x => Core.groupoid_category (Y x)))
            (Core.groupoid_category {x : X & Y x}).
Proof.
  srapply @Build_Functor.
  - exact idmap.
  - intros [x1 y1] [x2 y2]. simpl.
    intros [p f]. destruct p. simpl in f. destruct f. reflexivity.
  - intros [x1 y1] [x2 y2] [x3 y3]. simpl.
    intros [p1 f1] [p2 f2]. destruct p2. destruct p1. simpl.
    destruct f2. destruct f1. reflexivity.
  - simpl. reflexivity.
Defined.

(* show that the above functor is an isomorphism instead...*)
(* the path groupoid of a sigma type is equivalent to such a type *)
Definition iso_path_groupoid_cat_sum (X : Type) (Y : X -> Type)
           {istrunc_X : IsTrunc 1 X} {istrunc_Y : forall x : X, IsTrunc 1 (Y x)}
  : cat.isomorphic (Core.groupoid_category {x : X & Y x})
                   (cat_sum X (fun x => Core.groupoid_category (Y x))).
Proof.
  unfold cat.isomorphic.
  srapply @exist.
  - srapply @Build_Functor.
    + simpl. exact idmap.
    + simpl. intros a b p.
      unfold cat_sum_morph. destruct p.
      exists idpath. reflexivity.
    + simpl. intros a b c p q. destruct q. destruct p. simpl.
      reflexivity.
    + simpl. reflexivity.
  - apply Datatypes.pair.
    + intros a b. simpl.
      srapply @isequiv_adjointify.
      * intros [p f]. destruct a as [x1 y1]. destruct b as [x2 y2].
        destruct p. simpl in f. destruct f. reflexivity.
      * intros [p f].
        destruct a as [x1 y1]. destruct b as [x2 y2].
        destruct p. simpl in f. destruct f. reflexivity.
      * simpl. intro p. destruct p. reflexivity.
    + simpl. exact _.
Defined.
End Cat_sum.    
           

Section Component.
Definition component (X : Type) (x0 : Trunc 0 X) :=
  {x : X & tr x = x0}.

(* full subcategory given by a family of propositions on the type of objects *)
Definition full_subcategory
           (C : PreCategory) (P : C -> Type) : PreCategory.
Proof.
  srapply (Build_PreCategory
           (object := {c : C & P c})
           (fun c d => morphism C (c.1) (d.1))).
  - intros. simpl.
    apply identity.
  - simpl. intros a b c f g.
    apply (compose f g).
  - simpl. intros a b c d. intros f g h.
    apply (associativity).
  - simpl. intros a b f.
    apply left_identity.
  - simpl. intros a b f.
    apply right_identity.
Defined.

Definition include_full_subcategory (C : PreCategory) (P : C -> Type)
  : Functor (full_subcategory C P) C.
Proof.
  srapply @Build_Functor.
  - exact pr1.
  - intros [c1 p1] [c2 p2]. exact idmap.
  - intros [c1 p1] [c2 p2] [c3 p3]. reflexivity.
  - simpl. reflexivity.
Defined. 

Definition component_cat (C : PreCategory) (c0 : pi0_cat C) :=
  full_subcategory C (fun c => class_of _ c = c0).

End Component.

Section Decompose_cat.

Definition transport_morph_component {C : PreCategory} {c d : C}
           (f : morphism C c d) :
  transport (component_cat C) (path_pi0_cat f) (c; idpath) =
  (c; path_pi0_cat f).
Proof.
  destruct (path_pi0_cat f). reflexivity.
Defined.

Definition decompose_cat_obj {C : PreCategory}
  : C -> cat_sum (pi0_cat C) (component_cat C).
Proof.
  intro c. exists (class_of_pi0cat c).
  exists c. reflexivity.
Defined.

Definition morphism_over_decomp {C : PreCategory} {c1 c2 : C}
           {x1 x2 : pi0_cat C}
           (p1 : class_of_pi0cat c1 = x1)
           (p2 : class_of_pi0cat c2 = x2)
           (q : x1 = x2)
  : morphism (component_cat C x2) (c1; p1 @ q) (c2 ; p2) ->
    morphism_over (component_cat C) q (c1; p1) (c2; p2).
Proof.
  destruct q. simpl. exact idmap.
Defined.

Definition morphism_to_morphism_over_comp {C : PreCategory} {c1 c2 c3 : C}
           {x1 x2 x3 : pi0_cat C}
           (p1 : class_of_pi0cat c1 = x1)
           (p2 : class_of_pi0cat c2 = x2)
           (p3 : class_of_pi0cat c3 = x3)
           (q1 : x1 = x2) (q2 : x2 = x3)
           (f : morphism C c2 c3) (g : morphism C c1 c2)
  : morphism_over_compose _
      (morphism_over_decomp p2 p3 q2 f) (morphism_over_decomp p1 p2 q1 g) =
    morphism_over_decomp p1 p3 (q1 @ q2) (f o g)%morphism.
Proof.
  destruct q2. destruct q1. reflexivity.
Defined.    

(* Definition morphism_over_decomp {C : PreCategory} {c1 c2 : C} *)
(*            (f : morphism C c1 c2) *)
(*   : morphism_over (component_cat C) (path_pi0_cat f) (c1; idpath) (c2; idpath). *)
(* Proof. *)
(*   apply morphism_to_morphism_over. exact f. *)
(* Defined.   *)

Definition decompose_cat (C : PreCategory)
  : cat.isomorphic C (cat_sum (pi0_cat C) (component_cat C)).
Proof.
  refine
    (cat_isomorphic_compose
       (D := full_subcategory C (fun c => {x : pi0_cat C & class_of_pi0cat c = x}))
       _ _).
  - srapply @exist.
    + srapply @Build_Functor.
      * intros [c [x p]].
        exact (x; (c; p)).
      * intros [c1 [x1 p1]] [c2 [x2 p2]].
        simpl. intro f.
        srapply @exist.
        { simpl. exact (p1^ @ (path_pi0_cat f) @ p2). }
        simpl.
          
        (* destruct p1. destruct p2. *)
        (* exists (path_pi0_cat f). *)
        apply morphism_over_decomp. simpl.
        exact f.
      * intros [c1 [x1 p1]] [c2 [x2 p2]] [c3 [x3 p3]].
        destruct p3. destruct p2. destruct p1.
        intros f1 f2. simpl in f1. simpl in f2.
        simpl. rewrite morphism_to_morphism_over_comp.
        repeat rewrite concat_1p. repeat rewrite concat_p1.
        simpl. unfold morphism_over_decomp.
        assert (p : path_pi0_cat (f2 o f1) =
                    path_pi0_cat f1 @ path_pi0_cat f2).
        { apply set_quotient_set. }
        
        destruct p. reflexivity.
      * simpl.
        intros [c [x p]]. destruct p.
        unfold morphism_over_decomp.
        rewrite concat_1p. rewrite concat_p1. 
        assert (p :path_pi0_cat (identity c) = idpath).
        { apply set_quotient_set. } rewrite p.
        reflexivity.
    + simpl. unfold cat.is_isomorphism.
      unfold cat.fullyfaithful. simpl.
      apply Datatypes.pair.
      { intros [c1 [x1 p1]] [c2 [x2 p2]].
        srapply @isequiv_adjointify.
        - simpl.
          intros [p f]. destruct p. simpl in f. exact f.
        - intros [p f].          
          destruct p. simpl. simpl in f.
          assert (p : (p1^ @ path_pi0_cat f) @ p2 = idpath).
          { apply set_quotient_set. }
          rewrite p.
          reflexivity.
        - intro f. simpl in f.
          generalize ((p1^ @ path_pi0_cat f) @ p2).
          intro p. destruct p. reflexivity. }
      { srapply @isequiv_adjointify.
        - intros [x [c p]].
          exact (c; (x; p)).
        - intros [x [c p]]. reflexivity.
        - intros [c [x p]]. reflexivity. }
  - srapply @exist.
    + srapply @Build_Functor.
      * intro c. exists c. exists (class_of_pi0cat c). reflexivity.
      * intros s d f. simpl. exact f.
      * intros a b c f g. simpl. reflexivity.
      * reflexivity.
    + simpl. apply Datatypes.pair.
      * intros c d. simpl. exact _.
      * simpl.
        srapply @isequiv_adjointify.
        { apply pr1. }
        { intros [c [x p]]. simpl.
          destruct p. reflexivity. }
        intro c. reflexivity.
Defined.

End Decompose_cat.


(* Record IsIso_Cat {C D : PreCategory} (F : Functor C D) := *)
(*   {isequiv_obj : IsEquiv (object_of F); *)
(*    isequiv_morphism : forall a b : C, IsEquiv (@morphism_of _ _ F a b) *)
(*   }. *)


(* Definition Iso_Cat_inv {C D : PreCategory} (F : Functor C D) *)
(*   : (IsIso_Cat F) -> Functor D C. *)
(* Proof. *)
(*   intros [iseq_0 iseq_1]. *)
(*   srapply @Build_Functor. *)
(*   - exact (F^-1). *)
(*   - intros c d f. *)
(*     apply (morphism_of F (s := F^-1 c) (d := F^-1 d))^-1. *)
(*     srefine (double_transport (morphism D) _ _ f). *)
(*     { apply (eisretr F c)^. } *)
(*     { apply (eisretr F d)^. } *)
(*   - intros a b c f g. *)
(*     simpl. *)
(*     apply (equiv_inj (morphism_of F (d:=F^-1 c))). *)
(*     refine (eisretr (morphism_of F (d:=F^-1 c)) _ @ _). *)
(*     refine (_ @ (composition_of F _ _ _ _ _)^). *)
(*     rewrite (eisretr (morphism_of F (d:=F^-1 c))). *)
(*     rewrite (eisretr (morphism_of F (d:=F^-1 b))). *)
(*     destruct (eisretr F b)^. *)
(*     destruct (eisretr F c)^. *)
(*     destruct (eisretr F a)^. reflexivity. *)
(*   - simpl. intro d. *)
(*     apply (equiv_inj (morphism_of F (d:=F^-1 d))). *)
(*     refine (eisretr (morphism_of F (d:=F^-1 d)) _ @ _). *)
(*     refine (_ @ (identity_of F _)^). *)
(*     destruct (eisretr F d)^. reflexivity. *)
(* Defined. *)



(* Definition path_functor_uncurried' {C D : PreCategory} (F G : Functor C D) *)
(*   : {p0 : forall c : C, F c = G c & *)
(*       forall (c d : C) (f : morphism C c d), *)
(*                double_transport (morphism D) (p0 c) (p0 d) (morphism_of F f ) *)
(*                = morphism_of G f} -> F = G. *)
(* Proof. *)
(*   intros [p0 p1]. exact (path_functor' F G p0 p1). *)
(* Defined. *)


(* Definition equiv_path_functor' {C D : PreCategory} (F G : Functor C D) *)
(*   : {p0 : forall c : C, F c = G c & *)
(*       forall (c d : C) (f : morphism C c d), *)
(*                double_transport (morphism D) (p0 c) (p0 d) (morphism_of F f ) *)
(*                = morphism_of G f} <~> F = G. *)
(* Proof. *)
(*   refine (equiv_path_functor_uncurried F G oE _). *)
(*   srapply @equiv_functor_sigma'. *)
(*   - apply equiv_path_forall. *)
(*   - intro p. simpl. *)
(*     transitivity *)
(*       (forall (c d : C) (f : morphism C c d), *)
(*           double_transport (morphism D) *)
(*                            ((apD10 (path_forall F G p)) c) *)
(*                            ((apD10 (path_forall F G p)) d) *)
(*                            (F _1 f)%morphism = *)
(*           (G _1 f)%morphism). *)
(*     { apply equiv_functor_forall_id. intro a. *)
(*       apply equiv_functor_forall_id. intro b. *)
(*       apply equiv_functor_forall_id. intro f. *)
(*       rewrite <- (apD10_path_forall (object_of F) (object_of G) p a). *)
(*       rewrite <- (apD10_path_forall (object_of F) (object_of G) p b). *)
(*       reflexivity. } *)
(*     generalize (path_forall F G p). clear p. intro p. *)
(*     srapply @equiv_adjointify. *)
(*     + intro q. *)
(*       destruct (path_arrow _ _ (path_forall _ _ (path_forall _ _ q))). *)
(*       apply path_forall. intro a. *)
(*       apply path_forall. intro b. *)
(*       apply path_arrow. intro f. *)
(*       refine (_ @ q a b f). *)
(*       change  *)
      
    
(*     change (path_forall (Core.object_of F) (Core.object_of G) p) with *)
(*     .     *)
(*     destruct (path_forall F G p). *)
      
  
(*   unfold path_functor_uncurried'. unfold path_functor'. *)
(*   srapply @isequiv_adjointify. *)
(*   - intros []. *)
(*     srapply @exist. *)
(*     + intro c. reflexivity. *)
(*     + simpl. reflexivity. *)
(*   - intro p. destruct p. *)
(*     unfold path_functor_uncurried'. *)
(*     unfold path_functor'. simpl. *)
    
    
    
                 

(* Definition linv_iso_cat_inv {C D : PreCategory} (F : Functor C D) *)
(*            {isiso_F : IsIso_Cat F} *)
(*   : Functor.compose (Iso_Cat_inv F isiso_F) F = (Functor.identity C). *)
(* Proof. *)
(*   srapply @path_functor'. *)
(*   - simpl. intro c. *)
(*     apply eissect. *)
(*   - simpl. intros c d f. *)
(*     rewrite eisadj. *)
(*     rewrite eisadj. *)
    
(*     (* refine (_ @ eissect (morphism_of F (s := c) (d := d)) f). *) *)
(*     (* generalize (F _1 f)%morphism. intro g. clear f. *) *)
(*     destruct isiso_F as [iseq_0 iseq_1]. *)
(*     rewrite <- ap_V. rewrite <- ap_V. *)
(*     change (eissect (Core.object_of F) c) with (eissect F c). *)
(*     change (eissect (Core.object_of F) d) with (eissect F d). *)
(*     assert (H : double_transport (morphism C) (eissect F c) (eissect F d) *)
(*                              o (morphism_of F (d:=F^-1 (F _0 d)%object))^-1 *)
(*             == *)
(*             (morphism_of F (d := d))^-1 o *)
(*                  double_transport (morphism D) (ap F (eissect F c)) *)
(*                                                (ap F (eissect F d))). *)
(*     { destruct (eissect F c). destruct (eissect F d). intro g. *)
(*       simpl. reflexivity. } *)
(*     rewrite H. *)
(*     rewrite <- double_transport_compose. *)
(*     rewrite <- ap_pp. rewrite <- ap_pp. *)
(*     rewrite concat_Vp. rewrite concat_Vp. simpl. *)
(*     apply eissect. *)
(* Defined. *)

(* Definition rinv_iso_cat_inv {C D : PreCategory} (F : Functor C D) *)
(*            {isiso_F : IsIso_Cat F} *)
(*   : Functor.compose F (Iso_Cat_inv F isiso_F) = (Functor.identity D). *)
(* Proof. *)
(*   srapply @path_functor'. *)
(*   - simpl. intro d. *)
(*     apply eisretr. *)
(*   - simpl. intros c d f. *)
(*     destruct isiso_F as [iseq_0 iseq_1]. *)
(*     rewrite (eisretr ((morphism_of F (d:=F^-1 d)))). *)
(*     refine ((double_transport_compose _ _ _ _ _ _)^ @ _). *)
(*     rewrite concat_Vp. rewrite concat_Vp. *)
(*     reflexivity. *)
(* Defined. *)

(* Definition cat_inv_to_iso {C D : PreCategory} *)
(*            (F : Functor C D) *)
(*            (G : Functor D C) *)
(*            : (F o G = 1)%functor -> (G o F = 1)%functor -> *)
(*              IsIso_Cat F. *)
(* Proof. *)
(*   intros rinv linv. *)
(*   assert (linv_obj : forall c : C, G (F c) = c). *)
(*   {intro c. change (G _0 (F _0 c))%object with ((G o F)%functor c). *)
(*    rewrite linv. reflexivity. } *)
(*   assert (rinv_obj : forall d : D, F (G d) = d). *)
(*   {intro d. change (F _0 (G _0 d))%object with ((F o G)%functor d). *)
(*    rewrite rinv. reflexivity. } *)

(*   assert (isequiv_F0 : IsEquiv F). *)
(*   {srapply @isequiv_adjointify. *)
(*    - exact G. *)
(*    - intro d. apply rinv_obj. *)
(*    - intro c. apply linv_obj. *)
(*   }  *)
(*   assert (isequiv_F1 : forall (a b : C), IsEquiv (morphism_of F (s := a) (d := b))). *)
(*   {intros a b. *)
(*    srapply @isequiv_adjointify. *)
(*    - intro f. *)
(*      apply (double_transport (morphism C) (linv_obj a) (linv_obj b)). *)
(*      apply (morphism_of G f). *)
(*    - intro f. *)
(*      transitivity (double_transport (morphism D) (morphism_of (F o G)%functor f). *)
     
     
  
(* srefine (@Build_IsIso_Cat C D F isequiv_f _). *)
  


(* srapply @ *)

    

(* (* A category is the sum of its components *) *)
(* Definition decompose_cat (C : PreCategory) : *)
(*   C  *)
           

(* Definition inclution_comp_cat (C : PreCategory) (c0 : pi0_cat C) : *)
(*            Functor (component_cat C c0) C. *)
(* Proof. *)
(*   srapply @Build_Functor. *)
(*   - exact pr1. *)
(*   - intros c d. exact idmap. *)
(*   - reflexivity. *)
(*   - reflexivity. *)
(* Defined. *)

(* Definition functor_cquot (C D : PreCategory) (F : Functor C D) *)
(*   : cquot C -> cquot D. *)
(* Proof. *)
(*   srapply @cquot_rec. *)
(*   - intro x. apply ccl. exact (F x). *)
(*   - intros a b f. simpl. *)
(*     apply ccleq. *)
(*     apply (morphism_of F f). *)
(*   - intro a. simpl. *)
(*     refine (_ @ ce D _). *)
(*     apply (ap (ccleq D)). *)
(*     apply identity_of. *)
(*   - intros a b c f g. simpl. *)
(*     refine (_ @ cconcat D _ _). *)
(*     apply (ap (ccleq D)). *)
(*     apply composition_of. *)
(* Defined. *)

Section Cquot_sum.
  (* move *)

  (* The functor given by the constructors of cquot *)
  Definition include_in_cquot (C : PreCategory)
  : Functor C (Core.groupoid_category (cquot C)).
  Proof.
    srapply @Build_Functor.
    - apply ccl.
    - apply ccleq.
    - apply cconcat.
    - apply ce.
  Defined.

  Definition functor_groupoid_category
             (X Y : Type) {istrunc_X : IsTrunc 1 X} {istrunc_Y : IsTrunc 1 Y}
    : (X -> Y) -> Functor (Core.groupoid_category X) (Core.groupoid_category Y).
  Proof.
    intro f.
    srapply @Build_Functor.
    + exact f.
    + intros x1 x2. simpl. exact (ap f).
    + intros x1 x2 x3 p1 p2. simpl in *.
      apply ap_pp.
    + reflexivity.
  Defined.

      
      

  
  Definition univ_cquot (C : PreCategory) (Y : Type) {istrunc_Y : IsTrunc 1 Y}
    : (cquot C -> Y) <~> Functor C (Core.groupoid_category Y).
  Proof.
    srapply @equiv_adjointify.
    - intro f.
      refine (_ o (include_in_cquot C))%functor.
      apply functor_groupoid_category. exact f.
    - intro F.
      srapply @cquot_rec.
      + exact (object_of F).
      + apply (morphism_of F). 
      + apply (identity_of F).
      + apply (composition_of F).
    - intro F.
      srapply @path_functor'.
      + reflexivity.
      + intros a b f. simpl.
        apply cquot_rec_beta_ccleq.
    - intro F. apply path_arrow. intro x. revert x.
      srapply @cquot_ind_set.
      + intro c. simpl. reflexivity.
      + intros c1 c2 f. simpl.
        apply path_to_path_over.
        refine (transport_paths_FlFr _ _ @ _).
        simpl. rewrite concat_p1.
        apply moveR_Vp. rewrite concat_p1.
        apply inverse.
        refine (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _).
  Defined.

  (* move *)
  Definition functor_cquot {C D : PreCategory}
    : Functor C D -> (cquot C -> cquot D).
  Proof.
    intro F.
    apply (univ_cquot _ _)^-1.
    refine (include_in_cquot _ o F)%functor.
    (* srapply @cquot_rec. *)
    (* - intro c. apply ccl. exact (F c). *)
    (* - intros c1 c2 f. simpl. *)
    (*   apply ccleq. apply (morphism_of F). exact f. *)
    (* - intro c. simpl. *)
    (*   rewrite identity_of. apply ce. *)
    (* - intros c1 c2 c3 f g. simpl. *)
    (*   rewrite composition_of. apply cconcat. *)
  Defined.

  Definition cat_sum_pr1 (X : Type) {istrunc_X : IsTrunc 1 X} (C : X -> PreCategory)
    : Functor (cat_sum X C) (Core.groupoid_category X).
  Proof.
    srapply @Build_Functor.
    - exact pr1.
    - intros s d. exact pr1.
    - intros a b c f g. simpl. reflexivity.
    - intro c. simpl. reflexivity.
  Defined.

  Definition sum_grpd_to_grpd (
      

Definition cquot_sum (X : Type) {istrunc_X : IsTrunc 1 X} (C : X -> PreCategory)
  :  cquot (cat_sum X C) <~> {x : X & (cquot (C x))}.
Proof.
  srapply @equiv_adjointify.
  - apply (univ_cquot _ _)^-1.
    
    
    srapply @exist.
    + revert c.
      apply (univ_cquot _ _)^-1.
      apply cat_sum_pr1.
    + simpl.
      revert c.
      srapply @cquot_ind.
      *  simpl. intros [x c]. exact (ccl _ c).
      * simpl. intros [x1 c1] [x2 c2]. intros [p f]. destruct p. simpl in f.
        simpl.
      
      
    
    apply (univ_cat_sum _ _ _)^-1.
    
    
    intro x. refine (cat.inv_iso_map (iso_path_groupoid_cat_sum _ _) o _)%functor.
    refine (include_summand _ _ x o _)%functor.
    apply include_in_cquot.
  (* -  *)
  (*   srapply @cquot_rec. *)
  (*   + intros [x c]. exists x. *)
  (*     exact (ccl _ c). *)
  (*   + intros [x1 c1] [x2 c2]. intros [p f]. *)
  (*     srapply @path_sigma. *)
  (*     { exact p. } *)
  (*     destruct p. simpl. simpl in f. *)
  (*     apply ccleq. exact f. *)
  (*   + simpl. intros [x c]. *)
  (*     rewrite ce. reflexivity. *)
  (*   + intros [x1 c1] [x2 c2] [x3 c3]. simpl. *)
  (*     intros [p1 f1] [p2 f2]. destruct p2. destruct p1. simpl. *)
  (*     rewrite cconcat. destruct (ccleq (C x1) f2). *)
  (*     destruct (ccleq (C x1) f1). reflexivity. *)
  - intros [x c]. revert c.
    apply functor_cquot. apply include_summand.
  - intros [x c].
    
    revert c. apply apD10. apply (equiv_inj (univ_cquot _ {x0 : X & cquot (C x0)})).
    
    apply (equiv
    
    revert c. unfold functor_cquot.

    srapply @cquot_ind_set.
    + simpl. reflexivity.
    + simpl. intros c1 c2 f.      
      srapply @path_to_path_over.
      

    
    apply (univ_cquot _ _)^-1.
    apply (univ_cat_sum _ _ _)^-1.
    intro x.
    refine (cat.inv_iso_map (iso_path_groupoid_cat_sum _ _) o _)%functor.
    refine (include_summand _ _ x o _)%functor.
    apply include_in_cquot.
  (* -  *)
  (*   srapply @Build_Functor. *)
  (*   + intro c. exists x. *)
  (*     apply ccl. exact c. *)
  (*   + intros c1 c2 f. simpl. *)
  (*     srapply @path_sigma. *)
  (*     { reflexivity. } *)
  (*     simpl. *)
  (*     apply ccleq. exact f. *)
  (*   + intros a b c f g. simpl. *)
  (*     refine (_ @ path_sigma_pp_pp _ _ _ _ _). simpl. *)
  (*     rewrite concat_1p. *)
  (*     apply (ap (path_sigma _ _ _ _)). *)
  (*     rewrite ap_idmap. *)
  (*     apply cconcat. *)
  (*   + intro c. simpl. rewrite ce. reflexivity. *)
  - intros [x c]. revert c.
    apply (univ_cquot _ _)^-1.
    refine (include_in_cquot _ o _)%functor.
    apply include_summand.
  - intros [x c].
    
    
    revert c. apply apD10. apply (equiv_inj (univ_cquot _ {x0 : X & cquot (C x0)})).
    
    

    
    srapply @cquot_ind_set.
    + intro c. simpl. reflexivity.
    + intros c1 c2 f. apply path_to_path_over.
      
      refine (transport_paths_FlFr (ccleq (C x) f) idpath @ _).
    
    
                                            
    unfold univ_cquot. 
simpl.
    
    
simpl.
    apply (apD10 (A := X) (B := fun x => forall c : cquot (C x), ).
    srapply @path_sigma. { simpl.
    revert c.
    apply
      (equiv_inj (univ_cat_sum X C (Core.groupoid_category {x1 : X & cquot (C x1)}))).
    apply (equiv_inj (univ_cquot (cat_sum X C) {x1 : X & cquot (C x1)})).
    srapply @cquot_ind_set.
    + intro c. simpl. reflexivity.
    + intros c1 c2 f.
      apply path_to_path_over.
      refine 
      
    
      
      
                           

    srapply @cquot_rec.
    + simpl.
      intros [x c].
      exists x. exact (ccl (C x) c).
    + intros [x1 c1] [x2 c2].
      simpl. unfold cat_sum_morph.
      intros [p f]. destruct p. simpl in f.
      srapply @path_sigma. {reflexivity. }
      simpl. apply ccleq. exact f.
    + intros [x1 c1]. simpl.
      rewrite ce. reflexivity.
    + intros [x1 c1] [x2 c2] [x3 c3].
      intros [
      
    


Definition cquot_comp_to_comp_cquot (C : PreCategory) (c0 : pi0_cat C)
  : cquot (component_cat C c0) -> component (cquot C) (pi0_cat_cquot C c0).
Proof.
  intro x.
  srapply @exist.
  + revert x.
    apply functor_cquot.
    apply inclution_comp_cat.
  + simpl. revert x.
    srapply @cquot_ind_prop. intros [a p]. simpl.
    destruct p. reflexivity.
Defined.

Definition isequiv_cquot_comp_to_comp_cquot (C : PreCategory) (c0 : pi0_cat C)
           (* (c0 : Trunc 0 (cquot C)) *)
  : IsEquiv (cquot_comp_to_comp_cquot C c0). (* ((pi0_cat_cquot _)^-1 c0)). *)
Proof.
  revert c0.
  srefine (equiv_functor_forall_pf (pi0_cat_cquot C) _).
  intro c0.
  (* srefine (set_quotient_ind_prop _ _ _). *)

  (* (* srefine (Trunc_ind _ _). simpl. *) *)
  (* (* srefine (cquot_ind_prop _ _ _). simpl. *) *)
  (* intro c0. *)
  srapply @isequiv_adjointify.
  - unfold component.
    cut (
        {x : cquot C & tr x = c0} ->
        cquot (component_cat C ((pi0_cat_cquot C)^-1 c0))).
    { intro f. intros [x p]. apply f.
      exists x. refine (p @ _).
      apply eisretr. }
    intros [x p].  destruct p.
    revert x.
    srapply @cquot_ind.
    + intro c. simpl. 
      apply ccl. exists c. reflexivity.
    + intros a b f. admit.
    + admit.
    + admit.
      simpl in p.
    
    
    destruct (eisretr (pi0_cat_cquot C) c0) in p.
    

  
  apply isequiv_fcontr.
  intros [x p].  revert p. revert x.
  srefine (cquot_ind_prop _ _ _). simpl.
  intros c p.  
  srapply @BuildContr.
  - srapply @exist.
    + apply ccl. simpl. exists c.
      apply (equiv_inj (pi0_cat_cquot C)). exact p.
    + simpl.
      apply path_sigma_hprop. reflexivity.
  - intros [x q]. simpl in q.
    srapply @path_sigma.
    + simpl.
                  
  revert p.
  apply
    (equiv_functor_forall_pf (equiv_moveR_equiv_V (f := pi0_cat_cquot C) (tr x) c0)).
  intros [].
  
          
  rewrite <- (eissect (equiv_moveR_equiv_V (f := pi0_cat_cquot C) (tr x) c0) p).
  destruct (equiv_moveR_equiv_V (f := pi0_cat_cquot C) (tr x) c0 p).
  clear p.
  unfold equiv_inv. 
simpl.

                                                                                
Definition component_cquot (C : PreCategory) (c0 : pi0_cat C)
  : cquot (component_cat C c0) <~> component (cquot C) (pi0_cat_cquot C c0).
Proof.
  srapply @equiv_adjointify.
  - intro x.
    srapply @exist.
    + revert x.
      apply functor_cquot.
      apply inclution_comp_cat.
    + simpl. revert x.
      srapply @cquot_ind_prop. intros [a p]. simpl.
      destruct p. reflexivity.
  - intros [x p]. revert p.
    cut (((pi0_cat_cquot C)^-1 (tr x) = c0) -> cquot (component_cat C c0)).
    { intro f. intro p. apply f.
      refine (ap ((pi0_cat_cquot C)^-1) p @ _).
      apply eissect. }
    intros [].
    revert x.
    srapply @cquot_ind.
    + intro a. simpl. apply ccl.
      exists a. reflexivity.
    + intros a b f. simpl.
      
    
    

    srapply @cquot_rec.
    + simpl. intros [c p].
      exists (ccl C c).
      apply (ap
               (set_quotient_rec (morphism C)
                                 (fun c1 : C => tr (ccl C c1))
                                 (fun (x y : C)
                                      (f : morphism C x y) => ap tr (ccleq C f)))
               p).
    + simpl. intros [c p] [d q].
      simpl. intro f.
      apply (path_sigma _ (_;_) (_;_) (ccleq C f)).
      simpl.
      
    
      
    
      
    
  