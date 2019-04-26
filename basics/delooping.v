Require Import HoTT.
Require Import FunextAxiom.

(* Making an induction principle for pointed connected 1-types, based on notes by Thierry Coquand *)

Section deloop_induction.
  Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *)
          (isconn_X : forall (x : X), merely (x0 = x)).

  Context (Y : X -> 1-Type)
          (y0 : Y (x0))
          (f : forall (ω : x0 = x0), transport Y ω y0 = y0)
          (ishom_f : forall (α ω : x0 = x0),
              f (α @ ω) =
              transport_pp Y  α ω y0 @ ap (transport Y ω) (f α) @ (f ω)).
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
    (* Being contractible is a proposition, so we can assume that X is a single point *)
    apply Trunc_rec. intros [].
    apply (contr_equiv' {y : Y x0 & y0 = y}).
    { apply equiv_functor_sigma_id. intro y.
      apply equiv_inverse.
      apply C_base. }
    apply contr_basedpaths.
  Defined.

  Definition deloop_ind : forall (x : X), Y x
    := fun x => pr1 (center _ (contr_C x)).

  Definition deloop_ind_p (x : X) : forall ω : x0 = x, transport Y ω y0 = deloop_ind x
    := pr1 (pr2 (center {y : Y x & C x y} )).
  
  Lemma p_is_apD_ind :
    forall (x x': X) (α : x0 = x) (β : x = x'),
      deloop_ind_p x' (α @ β) =
      transport_pp Y α β _ @ ap (transport Y β) (deloop_ind_p x α) @ apD deloop_ind β.
  Proof.
    intros. destruct β. destruct α. simpl.
    destruct (deloop_ind_p x0 idpath). reflexivity.
  Qed.

  Definition deloop_ind_beta_x0 : deloop_ind x0 = y0 :=
    (deloop_ind_p x0 idpath)^.


  Definition deloop_ind_beta_f : forall (ω : x0 = x0),
      (ap (transport Y ω) deloop_ind_beta_x0)^ @ apD deloop_ind ω @ deloop_ind_beta_x0 = f ω.
  Proof.
    intro. apply moveR_pM. unfold deloop_ind_beta_x0.
    rewrite ap_V. rewrite inv_V. rewrite inv_V.
    refine (_ @ p_is_f _ _ ω).
    change ((center {y : Y x0 & C x0 y}).2).1 with (deloop_ind_p x0).
    apply inverse.
    rewrite <- (concat_1p ω).    
    refine ((p_is_apD_ind x0 x0 idpath ω) @ _).
    destruct ω. simpl. destruct (deloop_ind_p x0 idpath).
    reflexivity.
  Qed.
End deloop_induction.

Section deloop_ind_prop.
  Context (X : Type) (x0 : X) 
          (isconn_X : forall (x : X), merely (x0 = x)).
  Context (Y : X -> hProp)
          (y0 : Y (x0)).

  Definition deloop_ind_prop : forall x : X, Y x.
  Proof.
    intro x.
    generalize (isconn_X x).
    apply Trunc_ind.
    { exact _. }
    intros []. exact y0.
  Defined.
End deloop_ind_prop.
                     
    
    

Section deloop_ind_set.
  Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *)
          (isconn_X : forall (x : X), merely (x0 = x)).

  Context (Y : X -> 0-Type)
          (y0 : Y (x0))
          (f : forall (ω : x0 = x0), transport Y ω y0 = y0).

  Definition deloop_ind_set : forall x : X, Y x.
  Proof.
    apply (deloop_ind X x0 isconn_X (fun x => BuildTruncType 1 (Y x)) y0 f).
    intros.
    apply (istrunc_trunctype_type (Y x0)).
  Defined.
End deloop_ind_set.

Section deloop_rec.
  Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *)
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

  Definition deloop_rec : X -> Y :=
    deloop_ind X x0 isconn_X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help.

  Definition deloop_rec_beta_x0 : deloop_rec x0 = y0 :=
    deloop_ind_beta_x0 X x0 _ _ _ _ _.

  Definition deloop_rec_beta_f (ω : x0 = x0) :
    deloop_rec_beta_x0^ @ ap deloop_rec ω @ deloop_rec_beta_x0 = f ω.
  Proof.
    apply (cancelL (transport_const ω y0)).
    refine (_ @ deloop_ind_beta_f X x0 isconn_X (fun _ => Y) y0
              (fun ω => transport_const _ _ @ f ω) rec_help ω).
    change (deloop_ind X x0 isconn_X (fun _ => Y) y0 (fun ω => transport_const ω y0 @ f ω) rec_help)
    with deloop_rec.
    change (deloop_ind_beta_x0 X x0 isconn_X (fun _ : X => Y) y0
                                 (fun ω0 : x0 = x0 => transport_const ω0 y0 @ f ω0) rec_help)
    with deloop_rec_beta_x0.
    generalize (deloop_rec_beta_x0). intros []. simpl.
    destruct ω. reflexivity.
  Qed.
End deloop_rec.

Section universal.
  Context (X : Type) (x0 : X) (* (istrunc_X : IsTrunc 1 X) *)
          (isconn_X : forall (x : X), merely (x0 = x)).

  Context (Y : 1-Type).

  Definition rec_of (g : X -> Y) : X -> Y.
  Proof.
    apply (deloop_rec X x0 isconn_X Y (g x0) (fun ω => ap g ω)).
    intros. apply ap_pp.
  Defined.

  Definition is_rec (g : X -> Y) :
    rec_of g == g.
  Proof.
    intro x. revert x.
    srapply (deloop_ind_set X x0 isconn_X); simpl.
    - simpl. apply deloop_rec_beta_x0.
    - simpl. intros.
      refine (transport_paths_FlFr ω _ @ _).
      refine (concat_pp_p _ _ _ @ _).
      apply moveR_Vp.
      apply moveR_Mp. apply inverse.
      refine (concat_p_pp _ _ _ @ _).
      apply (deloop_rec_beta_f X x0 isconn_X Y (g x0) (fun ω0 : x0 = x0 => ap g ω0)
                                 (fun α ω0 : x0 = x0 => ap_pp g α ω0) ω ).
  Defined.

  Definition deloop_rec_uncurried :
    {y0 : Y & {f : (x0 = x0) -> (y0 = y0) & forall (α ω : x0 = x0), f (α @ ω) = f α @ f ω}} ->
    X -> Y.
  Proof.
    intros [y0 [f ishom_f]]. exact (deloop_rec X x0 isconn_X Y y0 f ishom_f).
  Defined.

  Definition isequiv_deloop_rec_uncurried : IsEquiv deloop_rec_uncurried.
  Proof.
    srapply @isequiv_adjointify.
    - intro g.
      exists (g x0). exists (fun ω => ap g ω). intros. apply ap_pp.
    - intro g. apply path_arrow.
      apply (is_rec g).
    - intros [y0 [f ishom_f]].
      srapply @path_sigma.
      + simpl. apply deloop_rec_beta_x0.
      + simpl. srapply @path_sigma_hprop. simpl.
        apply path_forall. intro ω.
        refine (_ @ deloop_rec_beta_f X x0 isconn_X Y y0 f ishom_f ω).
        generalize (deloop_rec_beta_x0 X x0 isconn_X Y y0 f ishom_f). intros [].
        simpl. destruct ω. reflexivity.
  Defined.
      
      
  
End universal.


Section deloop_double_ind_set.
  Context (X1 : Type) (a : X1) 
          (isconn_X1 : forall (x : X1), merely (a = x)).
  Context (X2 : Type) (b : X2) 
          (isconn_X2 : forall (x : X2), merely (b = x)).

  Context (Y : X1 -> X2 -> 0-Type)
          (y0 : Y a b)
          (fr : forall (ω : b = b), transport (Y a) ω y0 = y0)
          (fl : forall (ω : a = a), transport (fun x1 => Y x1 b) ω y0 = y0).
  
  Definition deloop_double_ind_set : forall (x1 : X1) (x2 : X2), Y x1 x2.
  Proof.
    intros x1.
    simple refine (deloop_ind_set X2 b isconn_X2 (fun x2 => Y x1 x2) _ _).
    - exact (deloop_ind_set X1 a isconn_X1 (fun x1 => Y x1 b) y0 fl x1).
    - simpl. intro.
      revert x1.
      apply (deloop_ind_prop X1 a isconn_X1). simpl.
      refine (_ @ fr ω @ _).
      + apply (ap (transport (fun x : X2 => Y a x) ω)).
        unfold deloop_ind_set.
        exact (deloop_ind_beta_x0 X1 a isconn_X1
                   (fun x : X1 =>
                      {| trunctype_type := Y x b; istrunc_trunctype_type := trunc_hset |}) y0 _ _ ) .
      + apply inverse.
        unfold deloop_ind_set.
        exact (deloop_ind_beta_x0 X1 a isconn_X1
                   (fun x : X1 =>
                      {| trunctype_type := Y x b; istrunc_trunctype_type := trunc_hset |}) y0 _ _).
  Defined.
End deloop_double_ind_set.

    


