Load monoidal_1type.

Section Type_to_Cat.
  Require Import HoTT.Categories Category.Morphisms.
  
  Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
  Definition Type_to_Cat : 1-Type -> PreCategory.
  Proof.
    intro X.
    srapply (Build_PreCategory (fun x y : X => x = y)).
    - reflexivity.
    - cbn. intros x y z p q.
      exact (q @ p).
    - intros x1 x2 x3 x4 p q r. simpl. apply concat_p_pp.
    - cbn. intros x1 x2 p. apply concat_p1.
    - intros x y p. simpl. apply concat_1p.
  Defined.

  Global Instance isgroupoid_type_to_cat (X : 1-Type) (x1 x2 : (Type_to_Cat X)) (f : x1 --> x2) :
    IsIsomorphism f.
  Proof.
    srapply @Build_IsIsomorphism.
    - exact f^.
    - apply concat_pV.
    - apply concat_Vp.
  Defined.
    

  Definition arrow_to_functor {X Y : 1-Type} (F : X -> Y) :
    Functor (Type_to_Cat X) (Type_to_Cat Y).
  Proof.
    srapply @Build_Functor. exact F.
    - intros x1 x2. simpl.
      exact (ap F).
    - simpl. intros x1 x2 x3 p q.
      apply ap_pp.
    - simpl. reflexivity.
  Defined.

  Definition cat_of_arrow (X Y : 1-Type) :
    Functor (Type_to_Cat (BuildTruncType 1 (X -> Y))) (functor_category (Type_to_Cat X) (Type_to_Cat Y)).
  Proof.
    srapply @Build_Functor; simpl.
    apply arrow_to_functor.
    - intros f g p.
      srapply @Build_NaturalTransformation; simpl.
      + apply (ap10 p).
      + intros x1 x2 q.
        destruct p, q. reflexivity.        
    - intros f g h p q. simpl.
      unfold NaturalTransformation.Composition.Core.compose. simpl. destruct p, q. simpl.
      apply NaturalTransformation.path_natural_transformation. simpl. intro x. reflexivity.
    - intro f. simpl.
      apply NaturalTransformation.path_natural_transformation. simpl. intro x. reflexivity.
  Defined.
End Type_to_Cat.

    
Section Localize.
  Require Import HoTT.Categories.
  (* if we have a monoidal action with left_cancellation, we can build a category with objects X and arrows*)
  (* {m : M & m ⊗ x = m ⊗ y} *)
  Definition monoidal_action_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) :
    (X -> X -> Type) := fun x y => {s : M & a s x = y}.

  Instance isset_mon_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) (x1 x2 : X)
           (left_cancel : left_faithful a)
    (* (left_cancel : forall (s t : M) (p q : s = t) (x : X), *)
    (*              action_on_path a x p = action_on_path a x q -> p = q)  *):
    IsHSet (monoidal_action_morphism M X a x1 x2).
  Proof.
    unfold monoidal_action_morphism.
    intros [s1 p1] [s2 p2].
    apply (trunc_equiv' {q : s1 = s2 & transport (fun s => a s x1 = x2) q p1 = p2}).
    { apply (equiv_path_sigma (fun s : M => a s x1 = x2) (s1; p1) (s2; p2) ). }
    (* apply (trunc_equiv' {q : s1 = s2 & p1 = (ap (fun s => a s x1) q) @ p2}). *)
    apply (trunc_equiv' {q : s1 = s2 & p1 = action_on_path a x1 q @ p2}).
    { apply equiv_functor_sigma_id. intro q. destruct q. simpl. destruct p2. apply equiv_idmap. }
    apply trunc_sigma'.
    + intro p. exact _.
    + simpl.
      intros [q1 r1] [q2 r2]. simpl.
      apply contr_inhabited_hprop. exact _.
      apply (left_cancel _ _ q1 q2 x1).
      transitivity (p1 @ p2^).
      { apply moveL_pV. apply r1^. }
      { apply moveR_pV. apply r2. }
  Defined.

  Definition monoidal_action_cat (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X)
             (left_cancel : left_faithful a)
             (* (left_cancel : forall (s t : M) (p q : s = t) (x : X), *)
             (*     action_on_path a x p = action_on_path a x q -> p = q) *)
    : PreCategory.
  Proof.
    srefine (Build_PreCategory (monoidal_action_morphism M X a) _ _ _ _ _ (fun x1 x2 => isset_mon_morphism M X a x1 x2 left_cancel)).
    (* identity *)
    - intro x. exists mon_id. apply mon_act_id.
    (* composition *)
    - intros x y z.
      intros [s1 p1] [s2 p2].
      exists (s1 ⊗ s2).
      exact (mon_act_mult a s1 s2 x @ ap (a s1) p2 @ p1).
    (* associativity *)
    - intros x1 x2 x3 x4 [s1 []] [s2 []] [s3 []]. repeat rewrite ap_1. repeat rewrite concat_p1.
      srapply @path_sigma. apply mon_assoc. cbn.
      refine (transport_paths_Fl (mon_assoc s3 s2 s1) _ @ _).
      rewrite mon_act_pentagon. repeat rewrite inv_pp. repeat rewrite inv_V.
      apply moveR_pM.
      repeat rewrite concat_pp_p. apply whiskerL. apply whiskerL.
      apply inverse. apply inv_pp.
    (* left identity *)
    - simpl.
      intros x1 x2 [s []]. simpl. rewrite concat_p1.
      srapply @path_sigma. apply mon_lid. simpl. 
      refine (transport_paths_Fl (mon_lid s) _ @ _).
      apply moveR_Vp. refine (_ @ (concat_p1 _)^). apply inverse.
      apply mon_act_triangle1.
    (* right identity *)
    - simpl.
      intros x1 x2 [s []]. simpl. rewrite concat_p1.
      srapply @path_sigma. apply mon_rid. simpl. 
      refine (transport_paths_Fl (mon_rid s) _ @ _).
      apply moveR_Vp. refine (_ @ (concat_p1 _)^). apply inverse.
      apply mon_act_triangle2.
  Defined.

  Definition localize_action (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X)
             (left_cancel : left_faithful (@mon_mult M))
             (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q)  *): PreCategory.
  Proof.
    apply (monoidal_action_cat M (BuildTruncType 1 (M*X)) (act_on_prod M M X (act_on_self M) act)). simpl.
    intros s t p q [a x].
    unfold action_on_path. simpl.
    intro H. apply (left_cancel s t p q a). 
    refine ((ap_fst_path_prod (z := (s ⊗ a, act s x )) (z' := (t ⊗ a, act t x ))
                (ap (fun m : M => m ⊗ a) p) (ap (fun m : M => act m x) p))^ @ _ @
             ap_fst_path_prod (z := (s ⊗ a, act s x )) (z' := (t ⊗ a, act t x ))
                (ap (fun m : M => m ⊗ a) q) (ap (fun m : M => act m x) q)). 
    apply (ap (ap fst)).
    refine (_ @ H @ _).
    - destruct p. reflexivity.
    - destruct q. reflexivity.
  Defined.    

  Definition group_completion (M : Monoidal_1Type)
             (left_cancel : left_faithful (@mon_mult M))
             (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *) : PreCategory :=
    localize_action M M (act_on_self M) left_cancel.

  Definition contr_self_category (M : Monoidal_1Type)
             (left_cancel : left_faithful (@mon_mult M))
             (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *)
    : forall x : object (monoidal_action_cat M M (act_on_self M) left_cancel),
      Contr (morphism (monoidal_action_cat M M (act_on_self M) left_cancel) mon_id x).
  Proof.
    simpl. intro a. unfold monoidal_action_morphism. unfold act_on_self. simpl.
    apply (contr_equiv' {s : M & s = a}).
    - srapply @equiv_functor_sigma'. exact equiv_idmap.
      intro m. simpl.
      apply equiv_concat_l. apply mon_rid.
    - apply contr_basedpaths'.
  Defined.

  Definition ap_homotopy_idmap {A : Type} (f : A -> A) (h : f == idmap) (a : A):
    ap f (h a) = h (f a).
  Proof.
    cut (forall p : f a = a,
              ap f p = h (f a) @ p @ (h a)^).
    - intro H. refine (H (h a) @ _).
      refine (concat_pp_p _ _ _ @ _). 
      refine (whiskerL _ (concat_pV _) @ _). apply concat_p1.
    - intros []. destruct (h (f a)). reflexivity.
  Defined.    
  
  (* Definition ap_homotopic_idmap {A : Type} (f : A -> A) (h : f == idmap) {a b : A} (p : a = b) : *)
  (*   ap f p = (h a) @ p @ (h b)^. *)
  (* Proof. *)
  (*   destruct p. destruct (h a). reflexivity. *)
  (* Defined. *)

  Definition prod_to_groupcompletion (S : Monoidal_1Type)
             (left_cancel : left_faithful (@mon_mult S))
             (* (left_cancel : forall (s t : S) (p q : s = t) (a : S), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *):
    Functor ((Type_to_Cat S)*(Type_to_Cat S))%category (group_completion S left_cancel).
  Proof.
    srapply @Build_Functor; simpl. exact idmap.
    - intros a b [p q].
      unfold monoidal_action_morphism.
      exists mon_id. apply path_prod. apply (mon_lid _ @ p). apply (mon_lid _ @ q).
    - intros [a1 a2] [b1 b2] [c1 c2] [p1 p2] [q1 q2]. simpl in *.
      destruct q2, q1, p2, p1. simpl. repeat rewrite concat_p1.
      srapply @path_sigma;simpl. apply inverse. apply mon_lid. 
      refine (transport_paths_Fl (mon_lid mon_id)^
              (path_prod (functor_prod (mon_mult mon_id) (mon_mult mon_id) (a1, a2)) (a1, a2) (mon_lid a1) (mon_lid a2)) @ _).
      rewrite ap_V. rewrite inv_V.
      apply whiskerR.
      transitivity (path_prod ((mon_id ⊗ mon_id) ⊗ a1, (mon_id ⊗ mon_id) ⊗ a2) (_,_)

                              (ap (fun x : S => mon_mult x a1) (mon_lid mon_id)) (ap (fun x : S => mon_mult x a2) (mon_lid mon_id))).
      { destruct (mon_lid mon_id). reflexivity. }
      rewrite ap_functor_prod.
      rewrite <- path_prod_pp.
      apply (ap011 (path_prod _ _));
      refine (mon_triangle1 S mon_id _ @ _); apply whiskerL;
      apply inverse; simpl; apply ap_homotopy_idmap.
    - intro x. simpl. rewrite concat_p1. rewrite concat_p1. reflexivity.
  Defined.

  Definition to_prod (C : PreCategory) :
    Functor C (C*C)%category.
  Proof.
    apply Functor.prod; apply Functor.identity.
  Defined.
  
  Definition to_groupcompletion (S : Monoidal_1Type)
             (left_cancel : left_faithful (@mon_mult S))
           (* (left_cancel : forall (s t : S) (p q : s = t) (a : S), *)
           (*       ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *):
  Functor (Type_to_Cat S) (group_completion S left_cancel) :=
    Functor.compose (prod_to_groupcompletion S left_cancel) (to_prod _).

End Localize.
     

Section Monoidal_Category.
  Require Import Category.Morphisms.
  Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
  Open Scope morphism.

  Definition BiFunctor (A B C : PreCategory) :=
    Functor A (functor_category B C).

  Definition morphism_of_1 {A B C : PreCategory} (F : BiFunctor A B C)
             {a a' : A} (f : a --> a') (b : B)  :
    F a b --> F a' b :=
    morphism_of F f b.

  Definition morphism_of_2 {A B C : PreCategory} (F : BiFunctor A B C)
             (a : A) {b b' : B} (g : b --> b') :
    F a b --> F a b' :=
    morphism_of (F a) g.

  Definition morphism_of_12 {A B C : PreCategory} (F : BiFunctor A B C)
             {a a' : A} (f : a --> a') {b b' : B} (g : b --> b') :
    F a b --> F a' b' :=
    (morphism_of_2 F a' g) o (morphism_of_1 F f b).
  (* Could define it the other way as well. . . *)    
    

  Record Monoidal_Category :=
    {moncat : PreCategory;
     moncat_mult : BiFunctor moncat moncat moncat;
     moncat_id : moncat;
     
     moncat_assoc : forall a b c : moncat,
          (moncat_mult (moncat_mult a b) c) --> (moncat_mult a (moncat_mult b c));
     natl_assoc : forall (a b c a' b' c' : moncat)
                         (f : a --> a') (g : b --> b') (h : c --> c'),
         morphism_of_12 moncat_mult f (morphism_of_12 moncat_mult g h) o moncat_assoc a b c =
         moncat_assoc a' b' c' o morphism_of_12 moncat_mult (morphism_of_12 moncat_mult f g) h;
     iso_assoc : forall a b c : moncat,
         IsIsomorphism (moncat_assoc a b c);
     
     moncat_lid : forall a : moncat,
         (moncat_mult moncat_id a) --> a;
     natl_lid : forall (a a' : moncat) (f : a --> a'),
         f o (moncat_lid a) = (moncat_lid a') o (morphism_of_2 moncat_mult moncat_id f);
     iso_lid : forall a : moncat,
         IsIsomorphism (moncat_lid a);
     
     moncat_rid : forall a : moncat,
         (moncat_mult a moncat_id) -->  a;
     natl_rid : forall (a a' : moncat) (f : a --> a'),
         f o (moncat_rid a) = (moncat_rid a') o (morphism_of_1 moncat_mult f moncat_id);
     iso_rid : forall a : moncat,
         IsIsomorphism (moncat_rid a);

     moncat_triangle1 : forall (a b : moncat),
         morphism_of_1 moncat_mult (moncat_lid a) b = moncat_lid (moncat_mult a b) o moncat_assoc moncat_id a b;
     moncat_triangle2 : forall (a b : moncat),
         morphism_of_1 moncat_mult (moncat_rid a) b = morphism_of_2 moncat_mult a (moncat_lid b) o moncat_assoc a moncat_id b;

     moncat_pentagon : forall (a b c d : moncat),
         morphism_of_1 moncat_mult (moncat_assoc a b c) d =
         (moncat_assoc a (moncat_mult b c) d)^-1 o ((morphism_of_2 moncat_mult a (moncat_assoc b c d))^-1 o
         (moncat_assoc a b (moncat_mult c d) o moncat_assoc (moncat_mult a b) c d))

    }.

    
  Infix "⊗" := smon_mult (at level 50,no associativity).
  Definition moncat_of_montype : Monoidal_1Type -> Monoidal_Category.
  Proof.
    
    intros [S m e assoc lid rid triangle1 triangle2 pentagon].
    refine
      (Build_Monoidal_Category (Type_to_Cat S) (cat_of_arrow S S o (arrow_to_functor m))%functor e assoc _ _ lid _ _ rid _ _ _ _ _); simpl.
    - intros a b c a' b' c' [] [] []. simpl. destruct (assoc a b c). reflexivity.
    - intros a a' []. destruct (lid a). reflexivity.
    - intros a a' []. destruct (rid a). reflexivity.
    - intros a b. refine (_ @ triangle1 a b).
      unfold morphism_of_1. simpl.
      destruct (lid a). reflexivity.
    - intros a b. refine (_ @ triangle2 a b).
      unfold morphism_of_1. simpl.
      destruct (rid a). reflexivity.
    - intros a b c d.
      unfold morphism_of_1. simpl.
      refine (_ @ pentagon a b c d @ _).
      + destruct (assoc a b c). reflexivity.
      + apply whiskerR. apply whiskerL.
        destruct (assoc b c d). reflexivity.      
  Defined.

  (* Definition moncat_action_category (S : Symmetric_Monoidal_1Type) (X : Monoidal_1Type) (F : Monoidal_Map S X) *)
  (*            (left_cancel : forall (s t : S) (p q : s = t) (a : S), *)
  (*                ap (fun x => smon_mult x a) p = ap (fun x => smon_mult x a) q -> p = q) : Monoidal_Category. *)
  (* Proof. *)
  (*   srefine (Build_Monoidal_Category (monoidal_action_cat S X (monmap_to_action F) left_cancel) _ _ _ _ (fun a b c => Build_IsIsomorphism _ _ _ _ _ _ _) *)
  (*                                    _ _ (fun a => Build_IsIsomorphism _ _ _ _ _ _ _) _ _ (fun a => Build_IsIsomorphism _ _ _ _ _ _ _)). *)
  Lemma ap_homotopy {A B : Type} {a b : A} (p : a = b) (f g : A -> B) (H : g == f) :
    ap f p = (H a)^ @ (ap g p) @ (H b).
  Proof.
    destruct p. simpl. destruct (H a). reflexivity.
  Defined.

  Lemma grp_complete_bifun_lem1' (S : Symmetric_Monoidal_1Type) (a b s t : S) :
      (((smon_assoc (t ⊗ s) a b)^ @ ap (fun x : S => x ⊗ b) (smon_sym (t ⊗ s) a)) @ smon_assoc a (t ⊗ s) b) @
           ap (smon_mult a) (smon_assoc t s b) =
      (smon_assoc t s (a ⊗ b) @ ap (smon_mult t) (((smon_assoc s a b)^ @ ap (fun x : S => x ⊗ b) (smon_sym s a)) @ smon_assoc a s b))
        @ (((smon_assoc t a (s ⊗ b))^ @ ap (fun x : S => x ⊗ (s ⊗ b)) (smon_sym t a)) @ smon_assoc a t (s ⊗ b)).
  Proof.
    repeat rewrite ap_pp. rewrite ap_V.
    assert (p : ap (smon_mult t) (ap (fun x : S => x ⊗ b) (smon_sym s a)) =
                (smon_assoc t (s ⊗ a) b)^ @ ap (fun x : S => x ⊗ b) (ap (fun x : S => t ⊗ x) (smon_sym s a)) @ smon_assoc t (a ⊗ s) b).
    destruct (smon_sym s a). simpl.
    destruct (smon_assoc t (s ⊗ a) b). simpl.  reflexivity.
    rewrite p. clear p. repeat rewrite concat_pp_p.
    assert (p : ap (fun x : S => x ⊗ (s ⊗ b)) (smon_sym t a) =
                (smon_assoc (t ⊗ a) s b)^ @ ap (fun x : S => x ⊗ b) (ap (fun x : S => x ⊗ s) (smon_sym t a)) @ smon_assoc (a ⊗ t) s b).
    destruct (smon_sym t a). simpl.
    destruct (smon_assoc (t ⊗ a) s b). simpl. reflexivity.
    rewrite p. clear p.
    rewrite (smon_sym_inv S t a). repeat rewrite ap_V.
    rewrite (smon_hexagon S a t s).
    repeat rewrite ap_pp. repeat rewrite ap_V.
    repeat rewrite concat_pp_p.
    repeat rewrite (smon_pentagon).
    repeat rewrite inv_pp. repeat rewrite inv_V.
    repeat rewrite concat_pp_p.
    repeat rewrite concat_V_pp. rewrite concat_Vp. rewrite concat_p1.
    rewrite concat_p_Vp. rewrite concat_p_Vp.
    rewrite (smon_sym_inv S a (t ⊗ s)). rewrite ap_V. rewrite inv_V.
    rewrite (smon_sym_inv S s a). rewrite ap_V. rewrite ap_V.
    repeat rewrite concat_V_pp. 
    repeat rewrite concat_p_pp. repeat apply whiskerR. rewrite concat_pV.
    apply inverse. apply concat_1p.
  Qed.

  Lemma grp_complete_bifun_lem1 
        (S : Symmetric_Monoidal_1Type)
        (a1 a2 b1 b2 : S) (c d : S * S) (s : S)
        (p : functor_prod (smon_mult s) (smon_mult s) (b1, b2) = c) (t : S)
        (q : functor_prod (smon_mult t) (smon_mult t) c = d) : 
    path_prod ((t ⊗ s) ⊗ (a1 ⊗ b1), (t ⊗ s) ⊗ (a2 ⊗ b2)) (a1 ⊗ ((t ⊗ s) ⊗ b1), a2 ⊗ ((t ⊗ s) ⊗ b2))
              (((smon_assoc (t ⊗ s) a1 b1)^ @ ap (fun x : S => x ⊗ b1) (smon_sym (t ⊗ s) a1)) @ smon_assoc a1 (t ⊗ s) b1)
              (((smon_assoc (t ⊗ s) a2 b2)^ @ ap (fun x : S => x ⊗ b2) (smon_sym (t ⊗ s) a2)) @ smon_assoc a2 (t ⊗ s) b2) @
              ap (functor_prod (smon_mult a1) (smon_mult a2))
              ((path_prod (functor_prod (smon_mult (t ⊗ s)) (smon_mult (t ⊗ s)) (b1, b2))
                          (functor_prod (smon_mult t) (smon_mult t) (functor_prod (smon_mult s) (smon_mult s) (b1, b2)))
                          (smon_assoc t s b1) (smon_assoc t s b2) @ ap (functor_prod (smon_mult t) (smon_mult t)) p) @ q) =
    (path_prod (functor_prod (smon_mult (t ⊗ s)) (smon_mult (t ⊗ s)) (functor_prod (smon_mult a1) (smon_mult a2) (b1, b2)))
               (functor_prod (smon_mult t) (smon_mult t)
                             (functor_prod (smon_mult s) (smon_mult s) (functor_prod (smon_mult a1) (smon_mult a2) (b1, b2))))
               (smon_assoc t s (a1 ⊗ b1)) (smon_assoc t s (a2 ⊗ b2)) @
               ap (functor_prod (smon_mult t) (smon_mult t))
               (path_prod (s ⊗ (a1 ⊗ b1), s ⊗ (a2 ⊗ b2)) (a1 ⊗ (s ⊗ b1), a2 ⊗ (s ⊗ b2))
                          (((smon_assoc s a1 b1)^ @ ap (fun x : S => x ⊗ b1) (smon_sym s a1)) @ smon_assoc a1 s b1)
                          (((smon_assoc s a2 b2)^ @ ap (fun x : S => x ⊗ b2) (smon_sym s a2)) @ smon_assoc a2 s b2) @
                          ap (functor_prod (smon_mult a1) (smon_mult a2)) p))
      @ (path_prod (t ⊗ (a1 ⊗ fst c), t ⊗ (a2 ⊗ snd c)) (a1 ⊗ (t ⊗ fst c), a2 ⊗ (t ⊗ snd c))
                   (((smon_assoc t a1 (fst c))^ @ ap (fun x : S => x ⊗ (let (fst, _) := c in fst))
                                                  (smon_sym t a1)) @ smon_assoc a1 t (fst c))
                   (((smon_assoc t a2 (snd c))^ @ ap (fun x : S => x ⊗ (let (_, snd) := c in snd)) (smon_sym t a2))
                      @ smon_assoc a2 t (snd c))
                   @ ap (functor_prod (smon_mult a1) (smon_mult a2)) q).
  Proof.
    destruct p,q.    
    repeat rewrite ap_pp.
    repeat rewrite ap_functor_prod. simpl. repeat rewrite concat_p1. 
    repeat rewrite <- path_prod_pp.
    apply (ap011 (path_prod _ _)); apply grp_complete_bifun_lem1'.
  Qed.

  Lemma grp_complete_bifun_lem2 (S : Symmetric_Monoidal_1Type) (a b : S) :
            (((smon_assoc smon_id a b)^ @ ap (fun x : S => x ⊗ b) (smon_sym smon_id a)) @ smon_assoc a smon_id b)
              @ ap (smon_mult a) (smon_lid b) = smon_lid (a ⊗ b).
  Proof.
    rewrite smon_sym_inv. rewrite ap_V.
    rewrite smon_hexagon.
    rewrite inv_pp. rewrite inv_pp. rewrite inv_pp. rewrite inv_pp.
    rewrite inv_V. rewrite inv_V.
    repeat rewrite concat_pp_p.
    rewrite concat_V_pp. rewrite concat_V_pp.
    assert (natl : ap (smon_mult smon_id) (smon_sym a b) =
                       smon_lid (a ⊗ b) @ smon_sym a b @ (smon_lid (b ⊗ a))^).
    { destruct (smon_sym a b). destruct (smon_lid (a ⊗ b)). reflexivity. }
    rewrite natl. clear natl.
    assert (natl : smon_sym a (smon_id ⊗ b) =
                   ap (smon_mult a) (smon_lid b) @ smon_sym a b @ (ap (fun x => x ⊗ a) (smon_lid b))^).
    { destruct (smon_lid b). simpl.
      destruct (smon_sym a (smon_id ⊗ b)). reflexivity. }
    rewrite natl. clear natl.
    rewrite smon_triangle1.
    rewrite inv_pp. rewrite inv_pp. rewrite inv_pp. rewrite inv_pp. rewrite inv_V. rewrite inv_V. 
    repeat rewrite concat_pp_p.

    repeat rewrite concat_V_pp. rewrite concat_p_Vp. rewrite concat_Vp.
    apply concat_p1.
  Qed.

  Lemma grp_complete_bifun_lem3' (S : Symmetric_Monoidal_1Type) (a s c t : S):
    (ap (fun x : S => x ⊗ (a ⊗ c)) (smon_sym s t))^
    @ ((smon_assoc s t (a ⊗ c) @ (((ap (smon_mult s) (smon_assoc t a c))^
       @ ap (smon_mult s) (ap (fun x : S => x ⊗ c) (smon_sym t a)))
       @ ap (smon_mult s) (smon_assoc a t c))) @ (smon_assoc s a (t ⊗ c))^) =
          (smon_assoc t s (a ⊗ c) @ (ap (smon_mult t) (smon_assoc s a c))^)
            @ (((smon_assoc t (s ⊗ a) c)^ @ ap (fun x : S => x ⊗ c) (smon_sym t (s ⊗ a))) @ smon_assoc (s ⊗ a) t c).
  Proof.
    assert (p : (ap (fun x : S => x ⊗ (a ⊗ c)) (smon_sym s t)) =
                (smon_assoc (s ⊗ t) a c)^ @ ap (fun x : S => x ⊗ c) (ap (fun x : S => x ⊗ a) (smon_sym t s))^ @
                                                                                                                    (smon_assoc (t ⊗ s) a c)).
    { rewrite (smon_sym_inv S t s). destruct (smon_sym s t). simpl.
      destruct (smon_assoc (s ⊗ t) a c). reflexivity. }
    rewrite p. clear p.
    assert (p : ap (smon_mult s) (ap (fun x : S => x ⊗ c) (smon_sym t a)) =
                (smon_assoc s (t ⊗ a) c)^ @ ap (fun x => x ⊗ c) (ap (fun x => s ⊗ x) (smon_sym t a)) @
                                              smon_assoc s (a ⊗ t) c).
    { destruct (smon_sym t a). simpl.
      destruct (smon_assoc s (t ⊗ a) c). reflexivity. }
    rewrite p. clear p.                  
    repeat rewrite inv_pp. rewrite ap_V. repeat rewrite inv_V.
    rewrite (smon_hexagon S t s).
    repeat rewrite ap_pp. repeat rewrite ap_V. 
    repeat rewrite concat_pp_p.
    repeat rewrite smon_pentagon.
    repeat rewrite inv_pp. repeat rewrite inv_V.
    change (fun x : S => s ⊗ x) with (smon_mult s).
    repeat rewrite concat_pp_p.
    repeat rewrite concat_V_pp.
    repeat rewrite concat_p_Vp.
    repeat rewrite concat_V_pp.
    repeat apply whiskerL. rewrite concat_pV. apply concat_p1.
  Qed.

  Lemma grp_complete_bifun_lem3
        (S : Symmetric_Monoidal_1Type) (left_cancel : left_faithful mon_mult) (a1 a2 : S) (b : S * S) (s : S)
        (p : functor_prod (smon_mult s) (smon_mult s) (a1, a2) = b) (c1 c2 : S) (d : Core.object (group_completion S left_cancel)) 
        (t : S) (q : functor_prod (smon_mult t) (smon_mult t) (c1, c2) = d): 
    (ap (fun x : S => functor_prod (smon_mult x) (smon_mult x) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2))) (smon_sym s t))^
    @ ((path_prod (functor_prod (smon_mult (s ⊗ t)) (smon_mult (s ⊗ t)) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2)))
                  (functor_prod (smon_mult s) (smon_mult s)
                                (functor_prod (smon_mult t) (smon_mult t) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2))))
                  (smon_assoc s t (a1 ⊗ c1)) (smon_assoc s t (a2 ⊗ c2))
                  @ ap (functor_prod (smon_mult s) (smon_mult s)) (path_prod (t ⊗ (a1 ⊗ c1), t ⊗ (a2 ⊗ c2)) (a1 ⊗ (t ⊗ c1), a2 ⊗ (t ⊗ c2))
                    (((smon_assoc t a1 c1)^ @ ap (fun x : S => x ⊗ c1) (smon_sym t a1)) @ smon_assoc a1 t c1)
                    (((smon_assoc t a2 c2)^ @ ap (fun x : S => x ⊗ c2) (smon_sym t a2)) @ smon_assoc a2 t c2) @
                    ap (functor_prod (smon_mult a1) (smon_mult a2)) q))
         @ (path_prod (s ⊗ (a1 ⊗ fst d), s ⊗ (a2 ⊗ snd d)) ((s ⊗ a1) ⊗ fst d, (s ⊗ a2) ⊗ snd d) (smon_assoc s a1 (fst d))^
            (smon_assoc s a2 (snd d))^ @ ap (fun b0 : S * S => functor_prod (smon_mult (fst b0)) (smon_mult (snd b0)) d) p)) =
    (path_prod (functor_prod (smon_mult (t ⊗ s)) (smon_mult (t ⊗ s)) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2)))
               (functor_prod (smon_mult t) (smon_mult t)
                             (functor_prod (smon_mult s) (smon_mult s) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2))))
               (smon_assoc t s (a1 ⊗ c1)) (smon_assoc t s (a2 ⊗ c2)) @ ap (functor_prod (smon_mult t) (smon_mult t))
               (path_prod (s ⊗ (a1 ⊗ c1), s ⊗ (a2 ⊗ c2)) ((s ⊗ a1) ⊗ c1, (s ⊗ a2) ⊗ c2) (smon_assoc s a1 c1)^ (smon_assoc s a2 c2)^
                @ ap (fun b0 : S * S => functor_prod (smon_mult (fst b0)) (smon_mult (snd b0)) (c1, c2)) p))
      @ (path_prod (t ⊗ (fst b ⊗ c1), t ⊗ (snd b ⊗ c2)) (fst b ⊗ (t ⊗ c1), snd b ⊗ (t ⊗ c2))
                   (((smon_assoc t (fst b) c1)^ @ ap (fun x : S => x ⊗ c1) (smon_sym t (let (fst, _) := b in fst)))
                      @ smon_assoc (fst b) t c1)
                   (((smon_assoc t (snd b) c2)^ @ ap (fun x : S => x ⊗ c2) (smon_sym t (let (_, snd) := b in snd)))
                      @ smon_assoc (snd b) t c2) @ ap (functor_prod (smon_mult (fst b)) (smon_mult (snd b))) q).
  Proof.
    destruct p,q. simpl.
    repeat rewrite concat_p1.
    repeat rewrite ap_functor_prod.
    assert (p :
              (ap (fun x : S => functor_prod (smon_mult x) (smon_mult x) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2)))
                  (smon_sym s t) =
               path_prod (_,_) (_,_)
                         (ap (fun x => x ⊗ (a1 ⊗ c1)) (smon_sym s t)) (ap (fun x => x ⊗ (a2 ⊗ c2)) (smon_sym s t)))).
    { destruct (smon_sym s t). simpl. reflexivity. }
    rewrite p. clear p.
    rewrite <- path_prod_VV.
    repeat rewrite <- path_prod_pp. repeat rewrite ap_pp. repeat rewrite ap_V. 
    apply (ap011 (path_prod _ _)); apply grp_complete_bifun_lem3'.
  Qed.  

  Definition mult_group_completion_fix_fst (S : Symmetric_Monoidal_1Type) (left_cancel : left_faithful (@mon_mult S))
             (a : group_completion S left_cancel) :
    Functor (group_completion S left_cancel) (group_completion S left_cancel).
  Proof.
    srapply @Build_Functor.
    + simpl.
      exact (functor_prod (smon_mult (fst a)) (smon_mult (snd a))).
    + simpl. intros b c.
      unfold monoidal_action_morphism. simpl. unfold functor_prod. simpl.

      intros [s p].
      exists s.
      refine (_ @ ap (functor_prod (smon_mult (fst a)) (smon_mult (snd a))) p).
      unfold functor_prod. simpl. apply path_prod; simpl; refine ((smon_assoc _ _ _)^ @ _ @ smon_assoc _ _ _);
                                    apply (ap (fun x => x ⊗ _ b) (smon_sym s (_ a))).
    + intros b c d. simpl in b,c,d.        
      intros [s p] [t q]. simpl in p,q.  simpl.
      destruct a as [a1 a2]; destruct b as [b1 b2]; simpl.
      srapply @path_sigma. reflexivity. simpl.
      apply grp_complete_bifun_lem1.
    + simpl. intro b.
      srapply @path_sigma. simpl. reflexivity. simpl.
      refine (whiskerL _ (ap_functor_prod _ _ _ _ _ _) @ _).
      destruct a as [a1 a2]. destruct b as [b1 b2]. simpl.
      refine ((path_prod_pp _ _ _ _ _ _ _)^ @ _).
      apply (ap011 (path_prod _ _)); apply grp_complete_bifun_lem2.
  Defined.
  
  Definition mult_group_completion (S : Symmetric_Monoidal_1Type) (left_cancel : left_faithful (@mon_mult S)) :
    BiFunctor (group_completion S left_cancel) (group_completion S left_cancel) (group_completion S left_cancel).
  Proof.
    unfold BiFunctor.
    srapply (Build_Functor (group_completion S left_cancel) (group_completion S left_cancel -> group_completion S left_cancel)
                         (fun (a : (group_completion S left_cancel)) => (mult_group_completion_fix_fst S left_cancel a))).
    - intros a b. simpl in a, b. simpl.
      intros [s p]. simpl in p. 
      srapply @Build_NaturalTransformation.
      + simpl. intro c.
        unfold monoidal_action_morphism. simpl.
        exists s.
        refine (_ @ ap (fun b => functor_prod (smon_mult (fst b)) (smon_mult (snd b)) c) p).
        unfold functor_prod. simpl.
        apply path_prod;
          apply ((smon_assoc _ _ _)^).
      + destruct a as [a1 a2]. intros [c1 c2] d.
        intros [t q]. simpl in q.
        srapply @path_sigma. apply smon_sym.
        refine (transport_paths_Fl (smon_sym s t) _ @ _). cbn.
        apply grp_complete_bifun_lem3.
    - intros a b c [s p] [t q].
      apply NaturalTransformation.path_natural_transformation. simpl.
      intro d. destruct p, q.
      srapply @path_sigma. reflexivity. simpl.
      abstract (
          repeat rewrite concat_p1;
          destruct d as [d1 d2]; simpl;
          change (fun b : S * S => functor_prod (smon_mult (fst b)) (smon_mult (snd b)) (d1, d2)) with
          (functor_prod (fun b : S =>  b ⊗ d1) (fun b : S => b ⊗ d2));
          repeat rewrite ap_functor_prod;
          repeat rewrite <- path_prod_pp;

          apply (ap011 (path_prod _ _));
          rewrite smon_pentagon;
          repeat rewrite concat_p_pp;
          apply whiskerR;
          apply concat2;
          try rewrite concat_Vp; try apply concat_1p;
          try apply inverse; apply ap_V).
    - intros [a1 a2].
      apply NaturalTransformation.path_natural_transformation. simpl.
      intros [b1 b2]. simpl.
      srapply @path_sigma. reflexivity.
      simpl.
      change (fun b : S * S => functor_prod (smon_mult (fst b)) (smon_mult (snd b)) (b1, b2))
             with
             (functor_prod (fun c : S => c ⊗ b1) (fun c : S => c ⊗ b2)).
      abstract (
          rewrite ap_functor_prod;
          rewrite <- path_prod_pp;
          apply (ap011 (path_prod _ _));
          rewrite smon_triangle1;
          rewrite concat_V_pp; reflexivity).
  Defined.
    
    
   Lemma ap_pair_path_prod {A B : Type} (f g : A -> B) {a b : A} (p : a = b) :
     ap (fun a : A => (f a, g a)) p = path_prod (f a, g a) (f b, g b) (ap f p) (ap g p).
   Proof.
     destruct p. reflexivity.
   Defined.
  
  Definition moncat_group_completion (S : Symmetric_Monoidal_1Type)
             (left_cancel : forall (s t : S) (p q : s = t) (a : S),
                 ap (fun x => smon_mult x a) p = ap (fun x => smon_mult x a) q -> p = q) : Monoidal_Category.
  Proof.
    srefine (Build_Monoidal_Category
               (group_completion S left_cancel) (mult_group_completion S left_cancel)
               (smon_id, smon_id)
               _ _ (fun a b c => Build_IsIsomorphism _ _ _ _ _ _ _)
               _ _ (fun a => Build_IsIsomorphism _ _ _ _ _ _ _)
               _ _ (fun a => Build_IsIsomorphism _ _ _ _ _ _ _) _ _ _).
    (* associative *)
    - intros a b c. simpl.
      unfold monoidal_action_morphism. simpl.
      destruct a as [a1 a2]. destruct b as [b1 b2]. destruct c as [c1 c2].
      unfold functor_prod. simpl.
      exists smon_id.
      apply path_prod; refine (smon_lid _ @ _); apply smon_assoc.
    (* asssociativity is natural *)
    - intros [a1 a2] [b1 b2] [c1 c2] a' b' c' [s p] [t q] [u r]. destruct p,q,r. simpl.
      srapply @path_sigma. simpl.
      { refine (smon_rid _ @ (smon_assoc _ _ _) @ (smon_lid _)^). }
      simpl.
      refine (transport_paths_Fl
                ((smon_rid ((u ⊗ t) ⊗ s) @ smon_assoc u t s) @ (smon_lid (u ⊗ (t ⊗ s)))^) _ @ _).
      repeat rewrite ap_pp.       repeat rewrite concat_p1.
      repeat rewrite ap_V. repeat rewrite inv_V.
      repeat rewrite ap_pair_path_prod. simpl.
      repeat rewrite <- path_prod_pp.
      rewrite <- path_prod_VV.
      rewrite <- path_prod_pp. rewrite <- path_prod_VV.
      rewrite <- path_prod_pp.
      apply (ap011 (path_prod _ _)).
      rewrite inv_pp. rewrite inv_pp. rewrite inv_V.
      repeat rewrite concat_p_pp. admit. admit.
    (* inverse associative *)
    - simpl. unfold monoidal_action_morphism. simpl. unfold functor_prod. simpl.
      destruct a as [a1 a2]. destruct b as [b1 b2]. destruct c as [c1 c2]. simpl.
      exists smon_id.
      apply path_prod; refine (smon_lid _ @ _); apply inverse; apply smon_assoc.
    - destruct a as [a1 a2]. destruct b as [b1 b2]. destruct c as [c1 c2]. simpl.
      rewrite ap_functor_prod. rewrite <- path_prod_pp. rewrite <- path_prod_pp. unfold functor_prod.
      srapply @path_sigma.
      apply smon_lid.           (* smon_rid works as well *)
      simpl.
      refine (transport_paths_Fl (smon_lid smon_id) _ @ _).
      admit.
    - simpl. admit.
    (* Left identity *)
    - intros [a1 a2]. simpl.
      unfold monoidal_action_morphism. simpl. unfold functor_prod. simpl.
      exists smon_id.
      apply path_prod; refine (smon_lid _ @ smon_lid _).
    - intros [a1 a2] a' [s p]. simpl in p. unfold functor_prod in p. simpl in p. destruct p.
      simpl. admit.
    - admit.
    - admit.
    - admit.
    (* right identity *)
    - intros [a1 a2]. simpl. unfold monoidal_action_morphism. simpl. unfold functor_prod. simpl.
      exists smon_id. apply path_prod; refine (smon_lid _ @ smon_rid _).
    - admit.
    - admit.
    - admit.
    - admit.
    (* Coherence diagrams *)
    - simpl. admit.
    - admit.
    - admit.
  Admitted.    

             
End Monoidal_Category.


  