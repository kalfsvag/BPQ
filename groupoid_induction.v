Require Import HoTT.
Require Import FunextAxiom.

(* Making an induction principle for pointed connected 1-types, based on notes by Thierry Coquand *)

Section groupoid_induction.
  Context (X : Type) (x0 : X) (istrunc_X : IsTrunc 1 X)
          (isconn_X : forall (x : X), merely (x0 = x)).

  Context (Y : X -> 1-Type)
          (y0 : Y (x0))
          (f : forall (ω : x0 = x0), transport Y ω y0 = y0)
          (ishom_f : forall (α ω : x0 = x0),
              f (α @ ω) =
              transport_pp Y  α ω _ @ ap (transport Y ω) (f α) @ (f ω)).
  Lemma ishom_f_1 :
    f idpath = idpath.
  Proof.
    apply (equiv_inj (concat (f idpath))).
    refine (_ @ (concat_p1 _)^).
    apply inverse.
    refine (ishom_f idpath idpath @ _).
    apply whiskerR. simpl.
    refine (concat_1p _ @ _).
    apply ap_idmap.
  Qed.

  Definition C (x : X) (y : Y x) :=
    {p : forall (ω : x0 = x),
        transport Y ω y0 = y &
        forall (α : x0 = x0) (ω : x0 = x),
          p (α @ ω) =
          transport_pp Y α ω _ @ ap (transport Y ω) (f α) @ p (ω)}.

  Lemma p_is_f (y : Y x0) (p : C x0 y) (α : x0 = x0) :
    p.1 α = f α @ (p.1 idpath).
  Proof.
    destruct p as [p H]. simpl.
    refine ((apD p (concat_p1 α))^ @ _).
    refine (transport_paths_Fl (concat_p1 α) (p (α @ 1)) @ _).
    apply moveR_Vp.
    refine (H α idpath @ _).
    refine (_ @ concat_pp_p _ _ _ ). apply whiskerR.
    apply concat2.
    + destruct α. reflexivity.
    + destruct (f α). reflexivity.
  Qed.    
  
  Definition C_base : forall y : Y x0, (C x0 y) <~> y0 = y.
  Proof.
    intro y.
    srapply @equiv_adjointify.
    - intros [p H].
      exact (p idpath).
    - intro p0.
      exists (fun ω => f ω @ p0).
      intros.
      refine (_ @ concat_pp_p _ _ _). apply whiskerR.
      apply ishom_f.
    - intro p0.
      refine (_ @ concat_1p _). apply whiskerR.
      apply ishom_f_1.
    - intros [p H].
      apply path_sigma_hprop. simpl.
      apply path_forall. intro α.
      apply inverse.
      apply (p_is_f y (p; H)).
  Defined.

  Instance contr_C :
    forall (x : X), Contr {y : Y x & C x y}.
  Proof.
    intro x. 
    generalize (isconn_X x).
    apply Trunc_rec. intros [].
    apply (contr_equiv' {y : Y x0 & y0 = y}).
    { apply equiv_functor_sigma_id. intro y.
      apply equiv_inverse.
      apply C_base. }
    apply contr_basedpaths.
  Defined.
  
  Definition groupoid_ind : forall (x : X), Y x
    := fun x => pr1 (center _ (contr_C x)).

  Definition groupoid_ind_p (x : X) : forall ω : x0 = x, transport Y ω y0 = groupoid_ind x
    := pr1 (pr2 (center {y : Y x & C x y} )).
  
  Lemma p_is_apD_ind :
    forall (x x': X) (α : x0 = x) (β : x = x'),
      groupoid_ind_p x' (α @ β) =
      transport_pp Y α β _ @ ap (transport Y β) (groupoid_ind_p x α) @ apD groupoid_ind β.
  Proof.
    intros. destruct β. destruct α. simpl.
    rewrite concat_1p. rewrite concat_p1.
    apply inverse. apply ap_idmap.
  Qed.

  Definition groupoid_ind_beta_x0 
    : groupoid_ind x0 = y0 :=
    (groupoid_ind_p x0 idpath)^.


  Definition groupoid_ind_beta_f : 
    forall (ω : x0 = x0),
      (ap (transport Y ω) groupoid_ind_beta_x0)^ @ apD groupoid_ind ω @ groupoid_ind_beta_x0 = f ω.
  Proof.
    intro. apply moveR_pM. unfold groupoid_ind_beta_x0.
    rewrite ap_V. rewrite inv_V. rewrite inv_V.
    refine (_ @ p_is_f _ _ ω).
    change ((center {y : Y x0 & C x0 y}).2).1 with (groupoid_ind_p x0).
    apply inverse.
    rewrite <- (concat_1p ω).    
    refine ((p_is_apD_ind x0 x0 idpath ω) @ _).
    destruct ω. simpl. destruct (groupoid_ind_p x0 idpath).
    reflexivity.
  Qed.
End groupoid_induction.

Section groupoid_rec.
  Context (X : Type) (x0 : X) (istrunc_X : IsTrunc 1 X)
          (isconn_X : forall (x : X), merely (x0 = x)).

  Context (Y : 1-Type)
          (y0 : Y)
          (f : (x0 = x0) -> (y0 = y0))
          (ishom_f : forall (α ω : x0 = x0),
              f (α @ ω) = f α @ f ω).

  Lemma rec_help (α ω : x0 = x0) :
    transport_const (α @ ω) y0 @ f (α @ ω) =
    (transport_pp (fun _ : X => Y) α ω y0
                  @ ap (transport (fun _ : X => Y) ω) (transport_const α y0 @ f α))
      @ (transport_const ω y0 @ f ω).
  Proof.
    rewrite ishom_f.
    destruct (f ω). destruct (f α).
    destruct ω. destruct α. reflexivity.
  Qed.

  Definition groupoid_rec : X -> Y :=
    groupoid_ind X x0 isconn_X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help.

  Definition groupoid_rec_beta_x0 : groupoid_rec x0 = y0 :=
    groupoid_ind_beta_x0 X x0 _ _ _ _ _.

  Definition groupoid_rec_beta_f (ω : x0 = x0) :
    groupoid_rec_beta_x0^ @ ap groupoid_rec ω @ groupoid_rec_beta_x0 = f ω.
  Proof.
    apply (cancelL (transport_const ω y0)).
    refine (_ @ groupoid_ind_beta_f X x0 isconn_X (fun _ => Y) y0
              (fun ω => transport_const _ _ @ f ω) rec_help ω).
    change (groupoid_ind X x0 isconn_X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help)
    with groupoid_rec.
    change (groupoid_ind_beta_x0 X x0 isconn_X (fun _ : X => Y) y0
                                 (fun ω0 : x0 = x0 => transport_const ω0 y0 @ f ω0) rec_help)
    with groupoid_rec_beta_x0.
    generalize (groupoid_rec_beta_x0). intros []. simpl.
    destruct ω. reflexivity.
  Qed.
End groupoid_rec.

Section universal.
  Context (X : pType) (x0 : X) (istrunc_X : IsTrunc 1 X)
          (isconn_X : forall (x : X), merely (x0 = x)).
  Context (Y : 1-Type)
          (y0 : Y).

  Definition groupoid_rec_uncurried :
    {f : x0 = x0 -> y0 = y0 & forall α ω : x0 = x0, f (α @ ω) = f α @ f ω} ->
    pMap (Build_pType X x0) (Build_pType Y y0).
  Proof.
    intros [f ishom].
    apply (Build_pMap (Build_pType X x0) (Build_pType Y y0)
                      (groupoid_rec X x0 isconn_X (BuildTruncType 1 Y) y0 f ishom)).
    apply (groupoid_rec_beta_x0 X x0 isconn_X (BuildTruncType 1 Y)).
  Defined.

  Definition isequiv_groupoid_rec_uncurried :
    IsEquiv groupoid_rec_uncurried.
  Proof.
    srapply @isequiv_adjointify.
    - intros [g pointed_g]. simpl in g. simpl in pointed_g.
      exists (fun ω => pointed_g^ @ ap g ω @ pointed_g).      
      intros. rewrite ap_pp. hott_simpl.
    - intros [g pointed_g]. apply path_pmap.
      srapply @Build_pHomotopy.
      + simpl. intro x. revert x.
        srapply (@groupoid_ind X x0 isconn_X).  simpl.
        * refine (groupoid_rec_beta_x0 X x0 isconn_X _ y0 _ _ @ _). apply inverse. apply pointed_g.
        * intro ω. admit.
        * intros. apply (istrunc_trunctype_type Y).
      + 
        
      
  


