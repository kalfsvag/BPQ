Require Import HoTT.
Require Import FunextAxiom.

Add Rec LoadPath "~/Coq-projects/groupoids" as GR.
From GR Require Import path_over.

Require Import Functor Categories Category Morphisms(* Category.Core *) .


(* move *)
Definition path_sigma' {A : Type} {B : A -> Type} {ab ab' : {a : A & B a}}
           (p : ab.1 = ab'.1) (q : path_over B p (ab.2) (ab'.2))
  : ab = ab'.
Proof.
  destruct ab as [a b]. destruct ab' as [a' b']. simpl in *.
  destruct q. reflexivity.
Defined.

Definition path_sigma_concat' {A : Type} {B : A -> Type} {x y z : {a : A & B a}}
           (p : x.1 = y.1) (q : path_over B p (x.2) (y.2))
           (p' : y.1 = z.1) (q' : path_over B p' (y.2) (z.2))
  : path_sigma' p q @ path_sigma' p' q' =
    path_sigma' (p @ p') (path_over_concat q q').
Proof.
  destruct x as [x1 x2]. destruct y as [y1 y2]. destruct z as [z1 z2]. simpl in *.
  destruct q'. destruct q. reflexivity.
Defined.


Definition equiv_path_sigma' {A : Type} {B : A -> Type} (ab ab' : {a : A & B a}) :
  {p : ab.1 = ab'.1 & path_over B p (ab.2) (ab'.2)} <~> ab = ab'.
Proof.
  srapply @equiv_adjointify.
  - intros [p q]. exact (path_sigma' p q).
  - intros []. exists idpath. apply path_over_id.
  - intros []. reflexivity.
  - intros [p q].
    destruct ab as [a b]. destruct ab' as [a' b']. simpl in *.
    destruct p. destruct q. reflexivity.
Defined.

  Lemma equiv_path_over_id {A : Type} {B : A -> Type} (a : A) (b1 b2 : B a)
    : path_over B (idpath a) b1 b2 <~> b1 = b2.
  Proof.
    srapply @equiv_adjointify.
    - apply (path_over_to_path (p := idpath a)).
    - apply (path_to_path_over (p := idpath a)).
    - simpl. intros []. reflexivity.
    - intro q. destruct q. reflexivity.
  Defined.      

  Definition isequiv_path_over_concat {A : Type} {B : A -> Type}
             {a1 a2 a3: A} {p1 : a1 = a2} (p2 : a2 = a3)
             {b1 : B a1} {b2 : B a2} (q : path_over B p1 b1 b2)
             (b3 : B a3) 
    : IsEquiv (path_over_concat (p₂ := p2) (c₃ := b3) q).
  Proof.
    srapply @isequiv_adjointify.
    - destruct p2. destruct q. exact idmap.
    - destruct q. destruct p2. 
      intro q. simpl in q. revert q.
      apply (equiv_functor_forall_pf (equiv_path_over_id a c b3)).
      intros []. reflexivity.
    - destruct q. destruct p2. simpl.
      apply (equiv_functor_forall_pf (equiv_path_over_id a c b3)).
      intros []. reflexivity.
  Defined.
  



(* Making an induction principle for pointed connected 1-types, based on notes by Thierry Coquand *)


Section rezk_ind_set.
  Context (X : Type) (* `{IsTrunc_X : IsTrunc 1 X} *). (* the latter variable not strictly necessary *)
  (* Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *) *)
  (*         `{isconn_X : forall (x : X), merely (x0 = x)}. *)

  Context (C : PreCategory)
          (* (H : Functor C (groupoid_category X)) *)
          (* (isfullyfaithful_H : IsFullyFaithful H) *)
          (* (isessentiallysurjective_H : IsEssentiallySurjective H). *)
          (* The following is uncurrying a weak equivalence from C to X *)
          (H_0 : C -> X)
          `{merely_surj_H : forall (x : X), merely {c : C & H_0 c = x}}
          (H_1 : forall {c1 c2 : C},
              morphism C c1 c2 -> H_0 c1 = H_0 c2)
          `{isequiv_H1 : forall (c1 c2 : C), IsEquiv (@H_1 c1 c2)}
          (H_idhom : forall (c : C), H_1 (identity c) = idpath)
          (H_2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3),
              H_1 (h o g)%morphism = H_1 g @ H_1 h).
  Arguments H_1 {c1 c2}.
  Arguments H_2 {c1 c2 c3}.

  (* Lemma H_idhom (c : C) : H_1 (identity c) = idpath. *)
  (* Proof. *)
  (*   apply (equiv_inj (concat (H_1 1))). *)
  (*   refine (ap H_1 (identity_identity C c)^ @ _). *)
  (*   refine (H_2 (identity c) (identity c) @ _). *)
  (*   ap H_1 (identity_identity C c)^ @ H_2 (identity c) (identity c) *)

  (* Instance istrunc_X : IsTrunc 1 X. *)
  (* Proof. *)
  (*   intros x1 x2. *)
  (*   generalize (merely_surj_H x1). apply Trunc_rec. intros [c1 p]. destruct p. *)
  (*   generalize (merely_surj_H x2). apply Trunc_rec. intros [c2 p]. destruct p. *)
  (*   apply (trunc_equiv _ H_1). *)
  (* Defined. *)

  Context (Y : X -> Type)
          `{istrunc_Y : forall (x : X), IsHSet (Y x)}
          (f0 : forall (c : C), Y (H_0 c))
          (f1 : forall {c1 c2 : C} (g : morphism C c1 c2),
              path_over Y (H_1 g) (f0 c1) (f0 c2)).
  Arguments f1 {c1 c2} g.
  (* Arguments f2 {c1 c2 c3} g h. *)

  (* Definition sect_of_rezk_ind : X -> {x : X & Y x}. *)
  (* Proof. *)
  (*   srapply (@rezk_rec X C (@H_0) (merely_surj_H) (@H_1) _ (@H_2)). *)
  (*   - intro c. exists (H_0 c). exact (f0 c). *)
  (*   - intros c1 c2 g. simpl. *)
  (*     srapply @path_sigma'. *)
  (*     + simpl. apply H_1. exact g. *)
  (*     + simpl. apply f1. *)
  (*   - simpl. intros. *)
  (*     refine (_ @ (path_sigma_concat' _ _ _ _)^). *)
  (*     change (path_sigma' ?p ?q) with (equiv_path_sigma' (_ ; _) (_;_) (p; q)). *)
  (*     apply (ap (equiv_path_sigma' _ _)). *)
  (*     srapply @path_sigma'. *)
  (*     + simpl. apply H_2. *)
  (*     + simpl. apply f2. *)
  (* Defined. *)
      
  (* Definition issect_sect_of_rezk_ind (x : X) : (sect_of_rezk_ind x).1 = x. *)
  (* Proof. *)
  (*   simpl. Abort. *)
    Definition B_set (x : X) (y : Y x) :=
      (forall (c : C) (p : H_0 c = x), path_over Y p (f0 c) y).
                                              
    (* {q : forall (c : C) (p : H_0 c = x), (f0 c) = y & *)
    (*  forall (c1 c2 : C) (g : morphism C c1 c2) (p : H_0 c2 = x), *)
    (*    q c1 (H_1 g @ p) = *)
    (*    (f1 g) @ (q c2 p)}. *)

  (* Lemma q_is_f1 (c1 c2 : C) (y : Y) (q : B (H_0 c2) y) (h : morphism C c1 c2) : *)
  (*   q.1 c1 (H_1 h) = *)
  (*   (f1 h) @ (q.1 c2 idpath). *)
  (* Proof. *)
  (*   destruct q as [q b]. simpl. *)
  (*   refine (ap (q c1) (concat_p1 (H_1 h))^ @ _). *)
  (*   apply b. *)
  (* Qed. *)
  
  Definition B_set_base : forall (c : C) (y : Y (H_0 c)),
        (B_set (H_0 c) y) <~> (f0 c = y).
  Proof.
    intros c y. unfold B_set.
    transitivity
      (forall (c0 : C) (g : morphism C c0 c), path_over Y (H_1 g) (f0 c0) y).
    { apply equiv_functor_forall_id. intro c1.
      refine (equiv_functor_forall_pb (BuildEquiv _ _ (@H_1 c1 c) _)). }
    apply equiv_iff_hprop.
    - intro q.
      refine (_ @ path_over_to_path (q c (identity c))).
      apply inverse.
      refine (ap (fun p => transport Y p (f0 c)) (H_idhom c)).
    - intro p. destruct p.
      intros c1 g. apply f1.
  Defined.

  Instance contr_B_set :
    forall (x : X), Contr {y : Y x & B_set x y}.
  Proof.
    intro x.
    cut (merely ({c : C & H_0 c = x}) -> Contr {y : Y x & B_set x y}).
    { intro hyp. apply hyp.
      apply merely_surj_H. }
    apply Trunc_rec. intros [c []].
    apply (contr_equiv' {y : Y (H_0 c) & (f0 c = y)}).
    { apply equiv_functor_sigma_id. intro y.
      apply equiv_inverse.
      apply B_set_base. }
    apply contr_basedpaths.
  Defined.

  Definition rezk_ind_set : forall (x : X), Y x
    := fun x => (center _ (contr_B_set x)).1 .

  (* Definition deloop_ind : forall (x : X), Y x *)
  (*   := fun x => pr1 (center _ (contr_C x)) *)

  Definition rezk_ind_set_q (x : X) (c : C):
    forall (p : H_0 c = x), path_over Y p (f0 c) (rezk_ind_set x)
    := ((center {y : Y x & B_set x y}).2 c).  

  (* Definition deloop_ind_p (x : X) : forall ω : (point X) = x, transport Y ω y0 = deloop_ind x *)
  (*   := pr1 (pr2 (center {y : Y x & C x y} )). *)
  
  (* Lemma q_is_ap_rezk_rec : *)
  (*   forall (x x': X) (c : C) (p : H_0 c = x) (q : x = x'), *)
  (*     rezk_rec_q x' c (p @ q) = *)
  (*     rezk_rec_q x c p @ ap rezk_rec q. *)
  (*     (* transport_pp Y α β _ @ ap (transport Y β) (deloop_ind_p x α) @ apD deloop_ind β. *) *)
  (* Proof. *)
  (*   intros. destruct q. destruct p. simpl. *)
  (*   apply inverse. apply concat_p1. *)
  (* Qed. *)

  Definition rezk_ind_set_beta_obj (c : C) : (rezk_ind_set (H_0 c)) = f0 c.
  Proof.
    apply inverse.
    apply equiv_path_over_id. 
    apply (rezk_ind_set_q).
  Defined.


  (* Definition rezk_rec_beta_morphism : forall (c1 c2 : C) (g :  morphism C c1 c2), *)
  (*     ap rezk_rec (H_1 g) = (rezk_rec_beta_obj c1) @ (f1 g) @ (rezk_rec_beta_obj c2)^. *)
  (*     (* (ap (transport Y ω) deloop_ind_beta_pt)^ @ apD deloop_ind ω @ deloop_ind_beta_pt = f ω. *) *)
  (* Proof. *)
  (*   intros. unfold rezk_rec_beta_obj. *)
  (*   rewrite inv_V. refine (_ @ concat_p_pp _ _ _). apply moveL_Vp. *)
  (*   apply inverse. *)
  (*   refine (_ @ q_is_ap_rezk_rec _ _ _ _ _). rewrite concat_1p. *)
  (*   apply inverse. apply q_is_f1. *)
  (* Defined. *)

  


  (* Lemma f1_idhom (c : C) :  *)
  (*   path_over (fun p => path_over Y p (f0 c) (f0 c)) (H_idhom c) *)
  (*             (f1 (identity c)) (path_over_id (f0 c)). *)
  (* Proof. *)
  (*   assert (H_idhom c = *)
  (*           ap H_1 (identity_identity C c)^ @ H_2 (identity c) (identity c) *)
  (*   assert (q : path_over (fun p : H_0 c = H_0 c => path_over Y p (f0 c) (f0 c)) *)
  (*                         (H_2 (identity c) (identity c))  *)
  (*   apply (equiv_inj (path_over_concat _ (f2 1 1) *)
    
  (*   refine (transport_path_over *)
  (*   refine (path_over_concat _ (path_over_concat (f2 1 1) _ )). *)
  (*   apply (equiv_inj (concat (f1 1))). *)
  (*   refine (_ @ (concat_p1 _)^). *)
  (*   apply inverse. *)
  (*   refine (_ @ f2 1 1). *)
  (*   apply (ap f1). *)
  (*   apply inverse. *)
  (*   apply left_identity. *)
  (* Qed. *)

  
  (* Definition B (x : X) (y : Y) := *)
  (*   {q : forall (c : C) (p : H_0 c = x), (f0 c) = y & *)
  (*    forall (c1 c2 : C) (g : morphism C c1 c2) (p : H_0 c2 = x), *)
  (*      q c1 (H_1 g @ p) = *)
  (*      (f1 g) @ (q c2 p)}. *)

  (* Lemma q_is_f1 (c1 c2 : C) (y : Y) (q : B (H_0 c2) y) (h : morphism C c1 c2) : *)
  (*   q.1 c1 (H_1 h) = *)
  (*   (f1 h) @ (q.1 c2 idpath). *)
  (* Proof. *)
  (*   destruct q as [q b]. simpl. *)
  (*   refine (ap (q c1) (concat_p1 (H_1 h))^ @ _). *)
  (*   apply b. *)
  (* Qed. *)
  
  (* Definition B_base : forall (c : C) (y : Y), (B (H_0 c) y) <~> (f0 c = y). *)
  (* Proof. *)
  (*   intros c y. unfold B. *)
  (*   transitivity *)
  (*     {q : forall c0 : C, morphism C c0 c -> f0 c0 = y & *)
  (*        forall (c1 c2 : C) (g : morphism C c1 c2) (h : morphism C c2 c), *)
  (*          q c1 (h o g)%morphism = f1 g @ q c2 h}. *)
  (*   { srapply @equiv_functor_sigma'. *)
  (*     - apply equiv_functor_forall_id. *)
  (*       intro c1. *)
  (*       apply (equiv_precompose'). *)
  (*       exact (BuildEquiv _ _ H_1 _). *)
  (*     - intro q. simpl. *)
  (*       apply equiv_functor_forall_id. intro c1. *)
  (*       apply equiv_functor_forall_id. intro c2. *)
  (*       apply equiv_functor_forall_id. intro g. *)
  (*       srapply @equiv_functor_forall'. *)
  (*       { exact (BuildEquiv _ _ H_1 _). } *)
  (*       intro h. simpl. *)
  (*       unfold functor_forall. *)
  (*       apply equiv_concat_l. *)
  (*       apply (ap (q c1)). *)
  (*       apply H_2. } *)
            
    
  (*   srapply @equiv_adjointify. *)
  (*   - intros [q b]. *)
  (*     apply (q c). apply identity. *)
  (*   - intro p. (* destruct p0. *) *)
  (*     srapply @exist. *)
  (*     + intros c1 h. refine (_ @ p). *)
  (*       apply f1. exact h. *)
  (*     + hnf. intros. *)
  (*       refine (_ @ concat_pp_p _ _ _ ). apply whiskerR. *)
  (*       refine (f2 _ _). *)
  (*   - intro p. *)
  (*     refine (whiskerR (f1_idhom _) _ @ _). apply concat_1p. *)
  (*   - intros [q b].  *)
  (*     apply path_sigma_hprop. simpl. *)
  (*     apply path_forall. intro c1. *)
  (*     apply path_forall. intro g. *)
  (*     refine (_ @ ap (q c1) (left_identity _ _ _ _)). *)
  (*     apply inverse. apply b. *)
  (* Defined. *)




  (* Instance contr_B : *)
  (*   forall (x : X), Contr {y : Y & B x y}. *)
  (* Proof. *)
  (*   intro x. *)
  (*   cut (merely ({c : C & H_0 c = x}) -> Contr {y : Y & B x y}). *)
  (*   { intro hyp. apply hyp. *)
  (*     apply merely_surj_H. } *)
  (*   apply Trunc_rec. intros [c []]. *)
  (*   apply (contr_equiv' {y : Y & (f0 c = y)}). *)
  (*   { apply equiv_functor_sigma_id. intro y. *)
  (*     apply equiv_inverse. *)
  (*     apply B_base. } *)
  (*   apply contr_basedpaths. *)
  (* Defined. *)

  (* Definition rezk_rec : X -> Y *)
  (*   := fun x => (center _ (contr_B x)).1 . *)

  (* (* Definition deloop_ind : forall (x : X), Y x *) *)
  (* (*   := fun x => pr1 (center _ (contr_C x)) *) *)

  (* Definition rezk_rec_q (x : X) (c : C): *)
  (*   forall (p : H_0 c = x), f0 c = rezk_rec x *)
  (*   := ((center {y : Y & B x y}).2.1 c).   *)

  (* (* Definition deloop_ind_p (x : X) : forall ω : (point X) = x, transport Y ω y0 = deloop_ind x *) *)
  (* (*   := pr1 (pr2 (center {y : Y x & C x y} )). *) *)
  
  (* Lemma q_is_ap_rezk_rec : *)
  (*   forall (x x': X) (c : C) (p : H_0 c = x) (q : x = x'), *)
  (*     rezk_rec_q x' c (p @ q) = *)
  (*     rezk_rec_q x c p @ ap rezk_rec q. *)
  (*     (* transport_pp Y α β _ @ ap (transport Y β) (deloop_ind_p x α) @ apD deloop_ind β. *) *)
  (* Proof. *)
  (*   intros. destruct q. destruct p. simpl. *)
  (*   apply inverse. apply concat_p1. *)
  (* Qed. *)

  (* Definition rezk_rec_beta_obj (c : C) : rezk_rec (H_0 c) = f0 c:= *)
  (*   (rezk_rec_q (H_0 c) c idpath)^. *)


  (* Definition rezk_rec_beta_morphism : forall (c1 c2 : C) (g :  morphism C c1 c2), *)
  (*     ap rezk_rec (H_1 g) = (rezk_rec_beta_obj c1) @ (f1 g) @ (rezk_rec_beta_obj c2)^. *)
  (*     (* (ap (transport Y ω) deloop_ind_beta_pt)^ @ apD deloop_ind ω @ deloop_ind_beta_pt = f ω. *) *)
  (* Proof. *)
  (*   intros. unfold rezk_rec_beta_obj. *)
  (*   rewrite inv_V. refine (_ @ concat_p_pp _ _ _). apply moveL_Vp. *)
  (*   apply inverse. *)
  (*   refine (_ @ q_is_ap_rezk_rec _ _ _ _ _). rewrite concat_1p. *)
  (*   apply inverse. apply q_is_f1. *)
  (* Defined. *)
End rezk_ind_set.

Section rezk_rec.
  Context (X : Type) (* `{IsTrunc_X : IsTrunc 1 X} *). (* the latter variable not strictly necessary *)
  (* Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *) *)
  (*         `{isconn_X : forall (x : X), merely (x0 = x)}. *)

  Context (C : PreCategory)
          (* (H : Functor C (groupoid_category X)) *)
          (* (isfullyfaithful_H : IsFullyFaithful H) *)
          (* (isessentiallysurjective_H : IsEssentiallySurjective H). *)
          (* The following is uncurrying a weak equivalence from C to X *)
          (H_0 : C -> X)
          `{merely_surj_H : forall (x : X), merely {c : C & H_0 c = x}}
          (H_1 : forall {c1 c2 : C},
              morphism C c1 c2 -> H_0 c1 = H_0 c2)
          `{isequiv_H1 : forall (c1 c2 : C), IsEquiv (@H_1 c1 c2)}
          (H_idhom : forall (c : C), H_1 (identity c) = idpath)
          (H_2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3),
              H_1 (h o g)%morphism = H_1 g @ H_1 h).
  Arguments H_1 {c1 c2}.
  Arguments H_2 {c1 c2 c3}.

  Context (Y : Type)
          `{istrunc_Y : IsTrunc 1 (Y)}
          (f0 : C -> Y)
          (f1 : forall {c1 c2 : C} (g : morphism C c1 c2),
              (f0 c1) =  (f0 c2))
          (f2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3),
                        (f1 (h o g)%morphism) =
                        ((f1 g) @ (f1 h))).
  Arguments f1 {c1 c2} g.
  Arguments f2 {c1 c2 c3} g h.

  Lemma f1_idhom (c : C) : f1 (identity c) = idpath.
  Proof.
    apply (equiv_inj (concat (f1 1))).
    refine (_ @ (concat_p1 _)^).
    apply inverse.
    refine (_ @ f2 1 1).
    apply (ap f1).
    apply inverse.
    apply left_identity.
  Qed.

  
  Definition B (x : X) (y : Y) :=
    {q : forall (c : C) (p : H_0 c = x), (f0 c) = y &
     forall (c1 c2 : C) (g : morphism C c1 c2) (p : H_0 c2 = x),
       q c1 (H_1 g @ p) =
       (f1 g) @ (q c2 p)}.

  Lemma q_is_f1 (c1 c2 : C) (y : Y) (q : B (H_0 c2) y) (h : morphism C c1 c2) :
    q.1 c1 (H_1 h) =
    (f1 h) @ (q.1 c2 idpath).
  Proof.
    destruct q as [q b]. simpl.
    refine (ap (q c1) (concat_p1 (H_1 h))^ @ _).
    apply b.
  Qed.
  
  Definition B_base : forall (c : C) (y : Y), (B (H_0 c) y) <~> (f0 c = y).
  Proof.
    intros c y. unfold B.
    transitivity
      {q : forall c0 : C, morphism C c0 c -> f0 c0 = y &
         forall (c1 c2 : C) (g : morphism C c1 c2) (h : morphism C c2 c),
           q c1 (h o g)%morphism = f1 g @ q c2 h}.
    { srapply @equiv_functor_sigma'.
      - apply equiv_functor_forall_id.
        intro c1.
        apply (equiv_precompose').
        exact (BuildEquiv _ _ H_1 _).
      - intro q. simpl.
        apply equiv_functor_forall_id. intro c1.
        apply equiv_functor_forall_id. intro c2.
        apply equiv_functor_forall_id. intro g.
        srapply @equiv_functor_forall'.
        { exact (BuildEquiv _ _ H_1 _). }
        intro h. simpl.
        unfold functor_forall.
        apply equiv_concat_l.
        apply (ap (q c1)).
        apply H_2. }
            
    
    srapply @equiv_adjointify.
    - intros [q b].
      apply (q c). apply identity.
    - intro p. (* destruct p0. *)
      srapply @exist.
      + intros c1 h. refine (_ @ p).
        apply f1. exact h.
      + hnf. intros.
        refine (_ @ concat_pp_p _ _ _ ). apply whiskerR.
        refine (f2 _ _).
    - intro p.
      refine (whiskerR (f1_idhom _) _ @ _). apply concat_1p.
    - intros [q b]. 
      apply path_sigma_hprop. simpl.
      apply path_forall. intro c1.
      apply path_forall. intro g.
      refine (_ @ ap (q c1) (left_identity _ _ _ _)).
      apply inverse. apply b.
  Defined.




  Instance contr_B :
    forall (x : X), Contr {y : Y & B x y}.
  Proof.
    intro x.
    cut (merely ({c : C & H_0 c = x}) -> Contr {y : Y & B x y}).
    { intro hyp. apply hyp.
      apply merely_surj_H. }
    apply Trunc_rec. intros [c []].
    apply (contr_equiv' {y : Y & (f0 c = y)}).
    { apply equiv_functor_sigma_id. intro y.
      apply equiv_inverse.
      apply B_base. }
    apply contr_basedpaths.
  Defined.

  Definition rezk_rec : X -> Y
    := fun x => (center _ (contr_B x)).1 .

  (* Definition deloop_ind : forall (x : X), Y x *)
  (*   := fun x => pr1 (center _ (contr_C x)) *)

  Definition rezk_rec_q (x : X) (c : C):
    forall (p : H_0 c = x), f0 c = rezk_rec x
    := ((center {y : Y & B x y}).2.1 c).  

  (* Definition deloop_ind_p (x : X) : forall ω : (point X) = x, transport Y ω y0 = deloop_ind x *)
  (*   := pr1 (pr2 (center {y : Y x & C x y} )). *)
  
  Lemma q_is_ap_rezk_rec :
    forall (x x': X) (c : C) (p : H_0 c = x) (q : x = x'),
      rezk_rec_q x' c (p @ q) =
      rezk_rec_q x c p @ ap rezk_rec q.
      (* transport_pp Y α β _ @ ap (transport Y β) (deloop_ind_p x α) @ apD deloop_ind β. *)
  Proof.
    intros. destruct q. destruct p. simpl.
    apply inverse. apply concat_p1.
  Qed.

  Definition rezk_rec_beta_obj (c : C) : rezk_rec (H_0 c) = f0 c:=
    (rezk_rec_q (H_0 c) c idpath)^.


  Definition rezk_rec_beta_morphism : forall (c1 c2 : C) (g :  morphism C c1 c2),
      ap rezk_rec (H_1 g) = (rezk_rec_beta_obj c1) @ (f1 g) @ (rezk_rec_beta_obj c2)^.
      (* (ap (transport Y ω) deloop_ind_beta_pt)^ @ apD deloop_ind ω @ deloop_ind_beta_pt = f ω. *)
  Proof.
    intros. unfold rezk_rec_beta_obj.
    rewrite inv_V. refine (_ @ concat_p_pp _ _ _). apply moveL_Vp.
    apply inverse.
    refine (_ @ q_is_ap_rezk_rec _ _ _ _ _). rewrite concat_1p.
    apply inverse. apply q_is_f1.
  Defined.
End rezk_rec.


Section rezk_ind.
    Context (X : Type) (* `{IsTrunc_X : IsTrunc 1 X} *). (* the latter variable not strictly necessary *)
  (* Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *) *)
  (*         `{isconn_X : forall (x : X), merely (x0 = x)}. *)

  Context (C : PreCategory)
          (* (H : Functor C (groupoid_category X)) *)
          (* (isfullyfaithful_H : IsFullyFaithful H) *)
          (* (isessentiallysurjective_H : IsEssentiallySurjective H). *)
          (* The following is uncurrying a weak equivalence from C to X *)
          (H_0 : C -> X)
          `{merely_surj_H : forall (x : X), merely {c : C & H_0 c = x}}
          (H_1 : forall {c1 c2 : C},
              morphism C c1 c2 -> H_0 c1 = H_0 c2)
          `{isequiv_H1 : forall (c1 c2 : C), IsEquiv (@H_1 c1 c2)}
          (H_idhom : forall (c : C), H_1 (identity c) = idpath)
          (H_2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3),
              H_1 (h o g)%morphism = H_1 g @ H_1 h).
  Arguments H_1 {c1 c2}.
  Arguments H_2 {c1 c2 c3}.

  (* Lemma H_idhom (c : C) : H_1 (identity c) = idpath. *)
  (* Proof. *)
  (*   apply (equiv_inj (concat (H_1 1))). *)
  (*   refine (ap H_1 (identity_identity C c)^ @ _). *)
  (*   refine (H_2 (identity c) (identity c) @ _). *)
  (*   ap H_1 (identity_identity C c)^ @ H_2 (identity c) (identity c) *)

  Instance istrunc_X : IsTrunc 1 X.
  Proof.
    intros x1 x2.
    generalize (merely_surj_H x1). apply Trunc_rec. intros [c1 p]. destruct p.
    generalize (merely_surj_H x2). apply Trunc_rec. intros [c2 p]. destruct p.
    apply (trunc_equiv _ H_1).
  Defined.

  Context (Y : X -> Type)
          `{istrunc_Y : forall (x : X), IsHSet (Y x)}
          (f0 : forall (c : C), Y (H_0 c))
          (f1 : forall {c1 c2 : C} (g : morphism C c1 c2),
              path_over Y (H_1 g) (f0 c1) (f0 c2))
          (f2 : forall {c1 c2 c3 : C} (g : morphism C c1 c2) (h : morphism C c2 c3),
              path_over (fun p => path_over Y p (f0 c1) (f0 c3))
                        (H_2 g h)
                        (f1 (h o g)%morphism)
                        (path_over_concat (f1 g) (f1 h))).           
  Arguments f1 {c1 c2} g.
  Arguments f2 {c1 c2 c3} g h.

  

  Definition sect_of_rezk_ind : X -> {x : X & Y x}.
  Proof.
    srapply (@rezk_rec X C (@H_0) (merely_surj_H) (@H_1) _ (@H_2)).
    - intro c. exists (H_0 c). exact (f0 c).
    - intros c1 c2 g. simpl.
      srapply @path_sigma'.
      + simpl. apply H_1. exact g.
      + simpl. apply f1.
    -  simpl. intros.
       refine (_ @ (path_sigma_concat' _ _ _ _)^).
       change (path_sigma' ?p ?q) with (equiv_path_sigma' (_ ; _) (_;_) (p; q)).
       apply (ap (equiv_path_sigma' _ _)).
       srapply @path_sigma'.
      + simpl. apply H_2.
      + simpl. apply f2.
  Defined.

  Definition sect_of_rezk_ind_beta_obj (c : C) :
    sect_of_rezk_ind (H_0 c) = (H_0 c; f0 c).
  Proof.
    apply rezk_rec_beta_obj.
  Defined.  
      
  Definition issect_sect_of_rezk_ind (x : X) : (sect_of_rezk_ind x).1 = x.
  Proof.
    revert x.    
    srapply (@rezk_ind_set X C H_0 merely_surj_H (@H_1) _ (@H_idhom)).
    - intro c. simpl.
      change (H_0 c) with (H_0 c; f0 c).1.
      apply (ap (fun x => x.1)).
      apply sect_of_rezk_ind_beta_obj.
    - intros.  simpl.
      apply path_to_path_over.
      refine (transport_paths_FlFr (H_1 g) _ @ _). rewrite ap_idmap.      
      rewrite (ap_compose _ (fun x => x.1)).
      refine (concat_pp_p _ _ _ @ _).

      apply moveR_Vp.
      refine (_ @ ap_pp (fun x : {x : X & Y x} => x.1)
                (ap sect_of_rezk_ind (H_1 g)) (sect_of_rezk_ind_beta_obj c2)).
      apply moveR_Mp.      
      rewrite <- (ap_V (fun x : {x : X & Y x} => x.1) (sect_of_rezk_ind_beta_obj c1)).
      refine (_ @ ap_pp (fun x : {x : X & Y x} => x.1)
                        (sect_of_rezk_ind_beta_obj c1)^ _).

      rezk_rec_beta_morphism
                _ _).
      rewrite <- (ap_pp (fun x : {x : X & Y x} => x.1)
                        (ap sect_of_rezk_ind (H_1 g))^
                        (sect_of_rezk_ind_beta_obj c1)).

      apply moveR_Mp.
      refine (
          
          (ap_pp (fun x : {x : X & Y x} => x.1) (ap sect_of_rezk_ind (H_1 g))^ ((rezk_rec_beta_obj X C H_0 (@H_1) (@H_2) {x : X & Y x} (fun c : C => (H_0 c; f0 c))
       (fun (c0 c3 : C) (g0 : morphism C c0 c3) => path_sigma' (H_1 g0) (f1 g0))
       (fun (c0 c3 c4 : C) (g0 : morphism C c0 c3) (h : morphism C c3 c4) =>
        ap (fun X0 : {p : H_0 c0 = H_0 c4 & path_over Y p (f0 c0) (f0 c4)} => path_sigma' X0.1 X0.2)
          (path_sigma' (H_2 g0 h) (f2 g0 h)) @ (path_sigma_concat' (H_1 g0) (f1 g0) (H_1 h) (f1 h))^)
       c1)))^ @ _).

      rewrite <- 
      rewrite (ap_compose (fun x => x.1)).
      
      transitivity (H_0 c; f0 c).1.
      {  }
      
      unfold sect_of_rezk_ind.
      refine (rezk_rec_beta_obj
                X C H_0 (@H_1) (@H_2) {x : X & Y x} (fun c0 : C => (H_0 c0; f0 c0))
                (fun (c1 c2 : C) (g : morphism C c1 c2) => path_sigma' (H_1 g) (f1 g))
                (fun (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3) =>
                   ap (equiv_path_sigma' (H_0 c1; f0 c1) (H_0 c3; f0 c3))
                      (path_sigma' (H_2 g h) (f2 g h)) @
                      (path_sigma_concat' (H_1 g) (f1 g) (H_1 h) (f1 h))^))


                                _ _ _ _ _ _ _  c @ _).
      Check ( X ).
      
    
    simpl.



(* Section rezk_ind_prop. *)
(*   Context (X : Type).  *)
(*   Context (Y : X -> hProp) *)
(*           (y0 : forall (c : C), Y (H_0 c)). *)

(*   Definition deloop_ind_prop : forall x : X, Y x. *)
(*   Proof. *)
(*     intro x. *)
(*     generalize (isconn_conn_ptype X x). *)
(*     apply Trunc_ind. *)
(*     { exact _. } *)
(*     intros []. exact y0. *)
(*   Defined. *)
(* End rezk_ind_prop.     *)
    




(* Section rezk_ind_prop. *)
(*   Context (X : Type).  *)
(*   Context (Y : X -> hProp) *)
(*           (y0 : forall (c : C), Y (H_0 c)). *)

(*   Definition deloop_ind_prop : forall x : X, Y x. *)
(*   Proof. *)
(*     intro x. *)
(*     generalize (isconn_conn_ptype X x). *)
(*     apply Trunc_ind. *)
(*     { exact _. } *)
(*     intros []. exact y0. *)
(*   Defined. *)
(* End rezk_ind_prop.     *)
    

Section rezk_ind.
  Context (X : Type).
  Context (C : PreCategory)
          (* (H : Functor C (groupoid_category X)) *)
          (* (isfullyfaithful_H : IsFullyFaithful H) *)
          (* (isessentiallysurjective_H : IsEssentiallySurjective H). *)
          (* The following is uncurrying a weak equivalence from C to X *)
          (H_0 : C -> X)
          (merely_surj_H : forall (x : X), merely {c : C & H_0 c = x})
          (H_1 : forall {c1 c2 : C},
              morphism C c1 c2 -> H_0 c1 = H_0 c2)
          `{isequiv_H1 : forall (c1 c2 : C), IsEquiv (@H_1 c1 c2)}
          (H_idhom : forall (c : C), H_1 (identity c) = idpath)
          (H_2 : forall (c1 c2 c3 : C) (g : morphism C c1 c2) (h : morphism C c2 c3),
              H_1 (h o g)%morphism = H_1 g @ H_1 h).
  Arguments H_1 {c1 c2}.
  Arguments H_2 {c1 c2 c3}.  
  

  Context (Y : X -> Type)
          `{isset_y : forall x : X, IsHSet (Y x)}
          (f0 : forall c : C, Y (H_0 c))
          (f1 : forall {c1 c2 : C} (g : morphism C c1 c2),
              path_over Y (H_1 g) (f0 c1) (f0 c2)).

  Definition deloop_ind_set : forall x : X, Y x.
  Proof.
    apply (deloop_ind X Y y0 f).
    intros.
    apply isset_y.
  Defined.
End deloop_ind_set.

Section deloop_rec.
  Context (X : Conn_pType).
  Context (Y : Type)
          `{istrunc_y : IsTrunc 1 Y}
          (y0 : Y)
          (f : ((point X) = (point X)) -> (y0 = y0))
          (ishom_f : forall (α ω : (point X) = (point X)),
              f (α @ ω) = f α @ f ω).

  Lemma rec_help (α ω : (point X) = (point X)) :
    transport_const (α @ ω) y0 @ f (α @ ω) =
    (transport_pp (fun _ : X => Y) α ω y0
                  @ ap (transport (fun _ : X => Y) ω) (transport_const α y0 @ f α))
      @ (transport_const ω y0 @ f ω).
  Proof.
    rewrite ishom_f.
    destruct (f ω). destruct (f α).
    destruct ω. destruct α. reflexivity.
  Qed.

  Definition deloop_rec : X -> Y :=
    deloop_ind X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help.

  Definition deloop_rec_beta_pt : deloop_rec (point X) = y0 :=
    deloop_ind_beta_pt X _ _ _ _ .

  Definition deloop_rec_beta_loop (ω : (point X) = (point X)) :
    deloop_rec_beta_pt^ @ ap deloop_rec ω @ deloop_rec_beta_pt = f ω.
  Proof.
    apply (cancelL (transport_const ω y0)).
    refine (_ @ deloop_ind_beta_loop X (fun _ => Y) y0
              (fun ω => transport_const _ _ @ f ω) rec_help ω).
    change (deloop_ind X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help)
    with deloop_rec.
    change (deloop_ind_beta_pt X 
                               (fun _ : X => Y) y0
                               (fun ω0 : (point X) = (point X) => transport_const ω0 y0 @ f ω0) rec_help)
    with deloop_rec_beta_pt.
    generalize (deloop_rec_beta_pt). intros []. simpl.
    revert ω.
    cut (forall (x : X) (ω : point X = x),
            transport_const ω (deloop_rec (point X)) @ ((1 @ ap deloop_rec ω) @ 1) =
            (1 @ apD deloop_rec ω) @ 1).
    { intro H. apply H. }
    intros x []. reflexivity.
  Qed.

  Definition deloop_rec_beta_loop' (ω : (point X) = (point X)) :
    ap deloop_rec ω = deloop_rec_beta_pt @ f ω @ deloop_rec_beta_pt^.
  Proof.
    apply moveL_pV. apply moveL_Mp.
    refine (concat_p_pp _ _ _ @ _).
    apply deloop_rec_beta_loop.
  Qed.

End resc_rec.

Section universal.
  Context (X : Conn_pType).
  Context (Y : Type) `{istrunc_y : IsTrunc 1 Y}.

  Definition rec_of (g : X -> Y) : X -> Y.
  Proof.
    apply (deloop_rec X Y (g (point X)) (fun ω => ap g ω)).
    intros. apply ap_pp.
  Defined.

  Definition is_rec (g : X -> Y) :
    rec_of g == g.
  Proof.
    intro x. revert x.
    srapply (deloop_ind_set X); simpl.
    - simpl. apply deloop_rec_beta_pt.
    - simpl. intros.
      refine (transport_paths_FlFr ω _ @ _).
      refine (concat_pp_p _ _ _ @ _).
      apply moveR_Vp.
      apply moveR_Mp. apply inverse.
      refine (concat_p_pp _ _ _ @ _).
      refine (deloop_rec_beta_loop X Y (g (point X))
                                   (fun ω0 : (point X) = (point X) => ap g ω0)
                                   (fun α ω0 : (point X) = (point X) => ap_pp g α ω0) ω).
  Defined.

  Definition deloop_rec_uncurried :
    {y0 : Y &
          {f : ((point X) = (point X)) -> (y0 = y0) &
                forall (α ω : (point X) = (point X)), f (α @ ω) = f α @ f ω}} -> X -> Y.
  Proof.
    intros [y0 [f ishom_f]]. exact (deloop_rec X Y y0 f ishom_f).
  Defined.

  Definition isequiv_deloop_rec_uncurried : IsEquiv deloop_rec_uncurried.
  Proof.
    srapply @isequiv_adjointify.
    - intro g.
      exists (g (point X)). exists (fun ω => ap g ω). intros. apply ap_pp.
    - intro g. apply path_arrow.
      apply (is_rec g).
    - intros [y0 [f ishom_f]].
      srapply @path_sigma.
      + simpl. apply deloop_rec_beta_pt.
      + simpl. srapply @path_sigma_hprop. simpl.
        apply path_forall. intro ω.
        refine (_ @ deloop_rec_beta_loop X Y y0 f ishom_f ω).
        generalize (deloop_rec_beta_pt X Y y0 f ishom_f). intros [].
        simpl.
        rewrite concat_1p. rewrite concat_p1. reflexivity.
  Defined.

  Definition path_deloop
             (f g : X -> Y)
             (p : f (point X) = g (point X))
             (eq_ap : forall w : (point X) = (point X), ap f w = p @ ap g w @ p^)
    : f == g.
  Proof.
    intro x. revert x.
    srapply (deloop_ind_set X).
    - simpl. exact p.
    - intro. simpl.
      refine (transport_paths_FlFr _ p @ _).
      rewrite eq_ap.
      rewrite inv_pp. rewrite inv_V.
      rewrite inv_pp. rewrite concat_p_pp.
      rewrite concat_pV_p. rewrite concat_pV_p. reflexivity.
  Defined.

  Definition path_deloop_id (f : X -> Y) (x : X) : 
    path_deloop f f idpath (fun w => inverse (concat_p1 _ @ concat_1p (ap f w))) x = idpath.
  Proof.
    revert x.
    apply (deloop_ind_prop X). simpl.
    refine (deloop_ind_beta_pt X _ _ _ _ ).
  Qed.    
    
End universal.

Section pointed_rec.
  Context (X : Conn_pType).
  
  Context (Y : pType) {istrunc_y : IsTrunc 1 Y}.
  
  (* Record p1Type := *)
  (*   {onetype_of :> 1-Type ; *)
  (*    ispointed_1type_of : IsPointed onetype_of}. *)
  (* Global Instance ispointed_1type_of' (Y : p1Type) : IsPointed Y *)
  (*   := ispointed_1type_of Y. *)
  (* Definition ptype_of (Y : p1Type) := Build_pType Y _. *)
  (* Coercion ptype_of : p1Type >-> pType. *)
  (* Context (Y : p1Type). *)

  Definition equiv_deloop_prec :
    {f : loops X -> loops Y & forall α ω : loops X, f (α @ ω) = f α @ f ω} <~> pMap X Y.
  Proof.
    refine (issig_pmap X Y oE _).
    transitivity
      {a : {y : Y & {f : loops X -> y = y &
                                    forall α ω : loops X, f (α @ ω) = f α @ f ω}} & point Y = pr1 a}.
    - srapply @equiv_adjointify.
      + intros [f ishom_f].
        srapply @exist.
        *  exists (point Y).
           exists f. exact ishom_f.
        * reflexivity.
      + intros [[y [f ishom]] p].
        simpl in p.  destruct p.
        exact (f; ishom).
      + intros [[y [f ishom]] p]. simpl in p. destruct p.
        reflexivity.
      + intros [f ishom_f]. reflexivity.
    - srapply @equiv_functor_sigma'.
      + exact (BuildEquiv _ _ (deloop_rec_uncurried X  Y)
                          (isequiv_deloop_rec_uncurried X Y)).
      + simpl.
        intros [y [f ishom]].
        refine (equiv_path_inverse _ _ oE _).
        apply equiv_concat_r.
        simpl. apply inverse. unfold deloop_rec_uncurried.
        apply deloop_rec_beta_pt.
  Defined.

  Definition deloop_prec (f : loops X -> loops Y)
             (ishom_f : forall α ω : loops X, f (α @ ω) = f α @ f ω) :
    pMap X Y.
  Proof.
    apply (Build_pMap X Y (deloop_rec X Y (point Y) f ishom_f)).
    apply deloop_rec_beta_pt.
  Defined.

  Lemma deloop_prec_eq_equiv_dloop_prec (f : loops X -> loops Y)
             (ishom_f : forall α ω : loops X, f (α @ ω) = f α @ f ω) :
    deloop_prec f ishom_f = equiv_deloop_prec (f; ishom_f).
  Proof.
    simpl. rewrite concat_1p. rewrite inv_V.
    reflexivity.
  Qed.

End pointed_rec.


Require Import monoids_and_groups.
Section functor_deloop.
  Context (X : Conn_pType) `{istrunc_X : IsTrunc 1 X}.
  Context (Y : pType) `{istrunc_Y : IsTrunc 1 Y}.

  Definition equiv_functor_deloop'
    : Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)) <~> pMap X Y.
  Proof.
    refine (equiv_deloop_prec X Y oE _).
    srapply @equiv_adjointify.
    - intros [f f_id f_mult]. exact (f; f_mult).
    - intros [f f_mult].
      apply (@Build_GrpHom (loopGroup X _) (loopGroup Y _) f f_mult).
    - intro f.
      apply path_sigma_hprop. reflexivity.
    - intro f. apply path_hom. reflexivity.
  Defined.

  Definition functor_deloop : Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)) -> pMap X Y.
  Proof.
    intros [f f_1 f_mult]. simpl in f_mult.
    srapply @Build_pMap.
    - apply (deloop_rec X Y (point Y) f f_mult).
    - apply deloop_rec_beta_pt.
  Defined.      

  Definition functor_loop : pMap X Y -> Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)).
  Proof.
    intro f.
    srapply @Build_GrpHom.
    - apply (loops_functor f).
    - simpl. destruct (point_eq f).
      intros. destruct g2. destruct g1. reflexivity.
  Defined.

  Global Instance isequiv_functor_loop : IsEquiv functor_loop.
  Proof.
    apply (isequiv_adjointify functor_loop functor_deloop).
    - intro f. apply path_hom. apply path_arrow.
      intro w. simpl in w. destruct f as [f f_1 f_mult]. simpl.
      rewrite deloop_rec_beta_loop'. hott_simpl.
    - intro f. apply path_pmap.          
      srapply @Build_pHomotopy.
      + srapply (path_deloop X ).
        { refine (deloop_rec_beta_pt X _ _ _ _@ (point_eq f)^). }
        intro w.
        refine (deloop_rec_beta_loop' X Y (point Y) _ _ w @ _).
        pointed_reduce.
        reflexivity.
      + apply moveR_pM.
        refine (deloop_ind_beta_pt X  _ _ _ _ ). 
  Defined.

  Definition equiv_functor_loop
    : pMap X Y <~> Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y))
    := BuildEquiv _ _ functor_loop _.

  Definition functor_deloop_loop
             (f : Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)))
    : loops_functor (functor_deloop f) == f.
  Proof.
    intro ω. unfold loops_functor. simpl.
    refine (concat_p_pp _ _ _ @ _). apply deloop_rec_beta_loop.
  Defined.




End functor_deloop.

  Lemma functor_loop_id (X : Conn_pType) 
        `{istrunc_X : IsTrunc 1 X} :
    functor_loop X X (@pmap_idmap X) == idhom.
  Proof.
    unfold functor_loop. simpl. intros []. reflexivity.
  Defined.


  Lemma functor_loop_compose
        (X : Conn_pType)  `{istrunc_X : IsTrunc 1 X}
        (Y : Conn_pType) `{istrunc_Y : IsTrunc 1 Y}
        (Z : pType) `{istrunc_Z : IsTrunc 1 Z}
        (f : pMap X Y) (g : pMap Y Z)
    : functor_loop Y Z g oH functor_loop X Y f ==
      functor_loop X Z (pmap_compose g f).
  Proof.
    unfold functor_loop. simpl. intro p.
    pointed_reduce.
    apply inverse. apply ap_compose.
  Qed.


Section functor_deloop_id.
  Context (X : Conn_pType)  `{istrunc_X : IsTrunc 1 X}.
  Definition functor_deloop_id :
    (functor_deloop X X idhom) = @pmap_idmap X.
  Proof.
    apply (equiv_inj (functor_loop X X)).
    refine (eisretr (functor_loop X X) idhom @ _).
    apply inverse. 
    apply path_hom. apply path_arrow.
    apply functor_loop_id.
  Defined.
End functor_deloop_id.

Section functor_deloop_compose.
  Context (X : Conn_pType) `{istrunc_X : IsTrunc 1 X}.
  Context (Y : Conn_pType) `{istrunc_Y : IsTrunc 1 Y}.
  Context (Z : pType) `{istrunc_Z : IsTrunc 1 Z}.

  Open Scope monoid_scope.
  Definition functor_deloop_compose
             (f : Homomorphism (loopGroup X (point X)) (loopGroup Y (point Y)))
             (g : Homomorphism (loopGroup Y (point Y)) (loopGroup Z (point Z))) :
    (functor_deloop X Z (g oH f)) =
    (pmap_compose (functor_deloop Y Z g)
                  (functor_deloop X Y f)).
  Proof.
    apply (equiv_inj (functor_loop X Z)).
    refine (eisretr (functor_loop X Z) (g oH f) @ _).
    apply path_hom. apply path_arrow. intro x.
    refine (_ @ functor_loop_compose _ _ _ _ _ _).
    apply inverse.
    apply (ap011 (fun a b => (a oH b) x)).
    - refine (eisretr (functor_loop Y Z) g).
    - refine (eisretr (functor_loop X Y) f).
  Qed.
End functor_deloop_compose.



(* Section deloop_double_rec. *)
(*     Context (X1 : Type) (a : X1)  *)
(*           (isconn_X1 : forall (x : X1), merely (a = x)). *)
(*     Context (X2 : Type) (b : X2)  *)
(*             (isconn_X2 : forall (x : X2), merely (b = x)). *)
(*     Context (Y : 1-Type) *)
(*             (y0 : Y) *)
(*             (fl : a = a -> y0 = y0) *)
(*             (ishom_fl : forall (α ω : a = a), *)
(*                 fl (α @ ω) = fl α @ fl ω) *)
(*             (fr : b = b -> y0 = y0) *)
(*             (ishom_fr : forall (α ω : b = b), *)
(*                 fr (α @ ω) = fr α @ fr ω) *)
(*             (natl_flr : forall (α : a = a) (ω : b = b), *)
(*                 fl α @ fr ω = fr ω @ fl α). *)
    
(*     Definition deloop_double_rec : X1 -> X2 -> Y. *)
(*     Proof. *)
(*       srefine (deloop_rec X1 a isconn_X1 _ _ _ _). *)
(*       - simpl. *)
(*         exact (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr). *)
(*       - intro α. apply path_arrow. intro x2. revert x2. *)
(*         srefine (deloop_ind_set X2 b isconn_X2 _ _ _ ). *)
(*         + simpl. *)
(*           refine *)
(*             (deloop_rec_beta_x0 X2 b isconn_X2 Y y0 fr ishom_fr @ _ @ *)
(*                                 (deloop_rec_beta_x0 _ _ _ _ _ _ _ )^). *)
(*           exact (fl α). *)
(*         + intro. simpl.  *)
(*           refine (transport_paths_FlFr  _ _ @ _). *)
(*           rewrite *)
(*             (moveL_Mp _ _ _ (moveL_pV _ _ _ (deloop_rec_beta_loop X2 b isconn_X2 Y y0 fr ishom_fr ω))). *)
(*           generalize ((deloop_rec_beta_x0 X2 b isconn_X2 Y y0 fr ishom_fr)). *)
(*           intro p. *)
(*           rewrite inv_pp. rewrite inv_pp. rewrite inv_V. *)
(*           repeat rewrite concat_p_pp. *)
(*           apply whiskerR. apply moveR_pM. *)
(*           repeat rewrite concat_pp_p. apply whiskerL. *)
(*           apply moveR_Vp. *)
(*           rewrite concat_Vp. rewrite concat_p1. *)
(*           rewrite concat_V_pp. *)
(*           rewrite concat_p_pp. apply moveL_pV. apply natl_flr. *)
(*       - simpl. intros. *)
(*         apply (ap (path_arrow (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr) (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr))). *)
(*         apply (istrunc_trunctype_type Y). *)
          
(*           generalize *)
(*             ((deloop_rec_beta_x0 X2 b isconn_X2 Y y0 fr ishom_fr @ fl α) *)
(*                @ (deloop_rec_beta_x0 X2 b isconn_X2 Y y0 fr ishom_fr)^). *)
(*           generalize (ap (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr) ω ). *)
(*           repeat rewrite concat_p_pp. *)
(*           destruct ((ap (deloop_rec X2 b isconn_X2 Y y0 fr ishom_fr) ω)). *)

(*       intros x1. *)
      


(*           (y0 : Y) *)
(*           (f : (x0 = x0) -> (y0 = y0)) *)
(*           (ishom_f : forall (α ω : x0 = x0), *)
(*               f (α @ ω) = f α @ f ω). *)

(* End deloop_double_rec. *)


Section deloop_double_ind_set.
  Context (X1 : Conn_pType).
  Context (X2 : Conn_pType).

  Context (Y : X1 -> X2 -> 0-Type)
          (y0 : Y (point X1) (point X2))
          (fr : forall (ω : (point X2) = (point X2)), transport (Y (point X1)) ω y0 = y0)
          (fl : forall (ω : (point X1) = (point X1)), transport (fun x1 => Y x1 (point X2)) ω y0 = y0).
  
  Definition deloop_double_ind_set : forall (x1 : X1) (x2 : X2), Y x1 x2.
  Proof.
    intros x1.
    simple refine (deloop_ind_set X2 (fun x2 => Y x1 x2) _ _).
    - exact (deloop_ind_set X1 (fun x1 => Y x1 (point X2)) y0 fl x1).
    - simpl. intro.
      revert x1.
      apply (deloop_ind_prop X1). simpl.
      refine (_ @ fr ω @ _).
      + apply (ap (transport (fun x : X2 => Y (point X1) x) ω)).
        unfold deloop_ind_set.
        exact (deloop_ind_beta_pt X1
                   (fun x : X1 => Y x (point X2)) y0 _ _ ) .
      + apply inverse.
        unfold deloop_ind_set.
        exact (deloop_ind_beta_pt X1
                   (fun x : X1 => Y x (point X2)) y0 _ _).
  Defined.

  Definition deloop_double_ind_set_beta_pt :
    deloop_double_ind_set (point X1) (point X2) = y0.
  Proof.
    unfold deloop_double_ind_set. unfold deloop_ind_set.
    refine (deloop_ind_beta_pt X2 _ _ _ _ @ _).
    apply (deloop_ind_beta_pt X1 (fun x : X1 => Y x (point X2))).
  Defined.    
    
End deloop_double_ind_set.

Section deloop_double_ind_set'.
  Context (X1 : Conn_pType).
  Context (X2 : Conn_pType).

  Context (Y : X1 -> X2 -> 0-Type)
          (y0 : Y (point X1) (point X2))
          (fl_fr : forall (ω1 : (point X1) = (point X1)) (ω2 : (point X2) = (point X2)),
              transport (uncurry Y) (path_prod (_,_) (_,_) ω1 ω2) y0 = y0).

  
  Definition deloop_double_ind_set' : forall (x1 : X1) (x2 : X2), Y x1 x2.
  Proof.
    intros x1 x2.
    simple refine (deloop_ind_set (conn_ptype_prod X1 X2) (uncurry Y) y0 _ (x1, x2)).
    unfold point. simpl.
    apply (equiv_functor_forall_pb (equiv_path_prod (point X1, point X2) (point X1, point X2))).
    intros [ω1 ω2]. simpl in ω1, ω2.
    apply fl_fr.
  Defined.

  Definition deloop_double_ind_set_beta_pt' :
    deloop_double_ind_set' (point X1) (point X2) = y0.
  Proof.
    unfold deloop_double_ind_set'. unfold deloop_ind_set. simpl.
    change (point X1, point X2) with (point (conn_ptype_prod X1 X2)).
    apply (deloop_ind_beta_pt (conn_ptype_prod X1 X2) (uncurry Y) y0).
  Defined.

End deloop_double_ind_set'.
  

    
(* todo: replace transport with pathover above, and write out deloop_double_ind *)
(* this should replace the two above *)
(* Section deloop_double_ind. *)
  