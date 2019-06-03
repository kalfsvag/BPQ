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

  Definition deloop_rec_beta_f' (ω : x0 = x0) :
    ap deloop_rec ω = deloop_rec_beta_x0 @ f ω @ deloop_rec_beta_x0^.
  Proof.
    apply moveL_pV. apply moveL_Mp.
    refine (concat_p_pp _ _ _ @ _).
    apply deloop_rec_beta_f.
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

  Definition path_deloop
             (f g : X -> Y)
             (p : f x0 = g x0)
             (eq_ap : forall w : x0 = x0, ap f w = p @ ap g w @ p^)
    : f == g.
  Proof.
    intro x. revert x.
    srapply (deloop_ind_set X x0 isconn_X).
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
    apply (deloop_ind_prop X x0 isconn_X). simpl.
    refine (deloop_ind_beta_x0 X x0 isconn_X _ _ _ _ ).
  Qed.    
    
End universal.

Section pointed_rec.
  Context (X : pType) (isconn_X : forall (x : X), merely (point (X) = x)).
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
      + exact (BuildEquiv _ _ (deloop_rec_uncurried X (point X) (isconn_X) (BuildTruncType 1 Y))
                          (isequiv_deloop_rec_uncurried X (point X) (isconn_X) (BuildTruncType 1 Y))).
      + simpl.
        intros [y [f ishom]].
        refine (equiv_path_inverse _ _ oE _).
        apply equiv_concat_r.
        simpl. apply inverse. unfold deloop_rec_uncurried.
        apply deloop_rec_beta_x0.
  Defined.

  Definition deloop_prec (f : loops X -> loops Y)
             (ishom_f : forall α ω : loops X, f (α @ ω) = f α @ f ω) :
    pMap X Y.
  Proof.
    apply (Build_pMap X Y (deloop_rec X (point X) (isconn_X) (BuildTruncType 1 Y) (point Y) f ishom_f)).
    apply deloop_rec_beta_x0.
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
  Context (X : pType) `{istrunc_X : IsTrunc 1 X} `{isconn_X : forall (x : X), merely (point (X) = x)}.
  Context (Y : pType) `{istrunc_Y : IsTrunc 1 Y} `{isconn_Y : forall (y : Y), merely (point (Y) = y)}.

  Definition equiv_functor_deloop' : Homomorphism (loopGroup X) (loopGroup Y) <~> pMap X Y.
  Proof.
    refine (equiv_deloop_prec X isconn_X Y oE _).
    srapply @equiv_adjointify.
    - intros [f f_id f_mult]. exact (f; f_mult).
    - intros [f f_mult].
      apply (@Build_GrpHom (loopGroup X) (loopGroup Y) f f_mult).
    - intro f.
      apply path_sigma_hprop. reflexivity.
    - intro f. apply path_hom. reflexivity.
  Defined.

  Definition functor_deloop : Homomorphism (loopGroup X) (loopGroup Y) -> pMap X Y.
  Proof.
    intros [f f_1 f_mult]. simpl in f_mult.
    srapply @Build_pMap.
    - apply (deloop_rec X (point X) isconn_X _ (point Y) f f_mult).
    - apply deloop_rec_beta_x0.
  Defined.      

  Definition functor_loop : pMap X Y -> Homomorphism (loopGroup X) (loopGroup Y).
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
      rewrite deloop_rec_beta_f'. hott_simpl.
    - intro f. apply path_pmap.
          
      srapply @Build_pHomotopy.
      + srapply (path_deloop X (point X) isconn_X).
        { refine (deloop_rec_beta_x0 X (point X) (isconn_X) _ _ _ _@ (point_eq f)^). }

        intro w.
        refine (deloop_rec_beta_f' X (point X) (isconn_X) _ (point Y) _ _ w @ _).
        pointed_reduce.
        apply concat2.
        * apply whiskerR. reflexivity.
        * reflexivity.
      + apply moveR_pM.
        refine (deloop_ind_beta_x0 X (point X) isconn_X _ _ _ _ @ _).
        apply whiskerR.
        reflexivity.
  Defined.
  
End functor_deloop.

Section functor_deloop_id.
  Context (X : pType) `{istrunc_X : IsTrunc 1 X} `{isconn_X : forall (x : X), merely (point (X) = x)}.
  Definition functor_deloop_id :
    (functor_deloop (isconn_X := isconn_X) X X idhom) = pmap_idmap X.
  Proof.
    apply (equiv_inj (functor_loop X (isconn_X := isconn_X) X (isconn_Y := isconn_X))).
    refine (eisretr (functor_loop X X) idhom @ _).
    apply inverse.
    apply path_hom. apply path_arrow. intro w. simpl.
    refine ((concat_1p _) @ (concat_p1 _) @ _).
    apply ap_idmap.
  Defined.

End functor_deloop_id.

Section functor_deloop_compose.
  Context (X : pType) `{istrunc_X : IsTrunc 1 X} `{isconn_X : forall (x : X), merely (point (X) = x)}.
  Context (Y : pType) `{istrunc_Y : IsTrunc 1 Y} `{isconn_Y : forall (y : Y), merely (point (Y) = y)}.
  Context (Z : pType) `{istrunc_Z : IsTrunc 1 Z} `{isconn_Z : forall (z : Z), merely (point (Z) = z)}.

  Open Scope monoid_scope.
  Definition functor_deloop_compose
             (f : Homomorphism (loopGroup X) (loopGroup Y))
             (g : Homomorphism (loopGroup Y) (loopGroup Z)) :
    (functor_deloop X Z (isconn_X := isconn_X) (g oH f)) =
    (pmap_compose
       (functor_deloop (isconn_X := isconn_Y) Y Z g)
       (functor_deloop (isconn_X := isconn_X) X Y f)
    ).
  Proof.
    apply (equiv_inj (functor_loop X (isconn_X := isconn_X) Z (isconn_Y := isconn_Z))).
    refine (eisretr (functor_loop X Z) (g oH f) @ _).
    apply inverse.
    apply path_hom. apply path_arrow. intro x.
    transitivity (((functor_loop Y (isconn_X := isconn_Y) Z (isconn_Y := isconn_Z)
                                 (functor_deloop Y (isconn_X := isconn_Y) Z  g))
                     oH
                     (functor_loop X (isconn_X := isconn_X) Y (isconn_Y := isconn_Y)
                                 (functor_deloop X (isconn_X := isconn_X) Y  f))) x).
    - generalize (functor_deloop Y (isconn_X := isconn_Y) Z  g). clear g. intro g.
      generalize (functor_deloop X (isconn_X := isconn_X) Y  f). clear f. intro f.
      simpl. destruct (point_eq g). destruct (point_eq f). simpl.
      repeat rewrite concat_1p. repeat rewrite concat_p1.
      apply ap_compose.
    - apply (ap011 (fun a b => (a oH b) x)). 
      + refine (eisretr (functor_loop Y Z) g).
      + refine (eisretr (functor_loop X Y) f).
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
(*             (moveL_Mp _ _ _ (moveL_pV _ _ _ (deloop_rec_beta_f X2 b isconn_X2 Y y0 fr ishom_fr ω))). *)
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

  Definition deloop_double_ind_set_beta_x0 :
    deloop_double_ind_set a b = y0.
  Proof.
    unfold deloop_double_ind_set. unfold deloop_ind_set.
    refine (deloop_ind_beta_x0 X2 b isconn_X2
           (fun x : X2 => {| trunctype_type := Y a x; istrunc_trunctype_type := trunc_hset |})
           _ _ _ @ _).
    apply (deloop_ind_beta_x0 X1 a isconn_X1
          (fun x : X1 => {| trunctype_type := Y x b; istrunc_trunctype_type := trunc_hset |})).
  Defined.
    
    
End deloop_double_ind_set.

    


