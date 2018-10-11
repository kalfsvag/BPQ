Require Import HoTT.
Require Import UnivalenceAxiom.

Definition push_fl {A B C : Type} (f : A -> B) (g : A -> C):
  B -> pushout f g := push o inl.
Definition push_fr {A B C : Type} (f : A -> B) (g : A -> C):
  C -> pushout f g := push o inr.


Definition pushout_ind' {A B C : Type} (f : A -> B) (g : A -> C)
           (P : pushout f g -> Type)
           (push_fl' : forall b : B, P (push_fl f g b))
           (push_fr' : forall c : C, P (push_fr f g c))
           (pp' : forall a : A, transport P (pp a) (push_fl' (f a)) = push_fr' (g a))
  : forall x : pushout f g, P x.
Proof.
  srapply @pushout_ind. intros [b|c]. apply push_fl'. apply push_fr'. apply pp'.
Defined.

Definition pushout_rec' {A B C : Type} (f : A -> B) (g : A -> C)
           (P : Type)
           (push_fl' : B -> P)
           (push_fr' : C -> P)
           (pp' : forall a : A, push_fl' (f a) = push_fr' (g a))
  : pushout f g -> P.
Proof.
  srapply @pushout_rec. intros [b|c]. exact (push_fl' b). exact (push_fr' c). apply pp'.
Defined.
  

Definition pushout_ind_beta_pp' {A B C} {f : A -> B} {g : A -> C}
           (P : pushout f g -> Type)
           (push_fl' : forall b : B, P (push_fl f g b))
           (push_fr' : forall c : C, P (push_fr f g c))
           (pp' : forall a : A, transport P (pp a) (push_fl' (f a)) = push_fr' (g a))
           (a : A)
  : apD (pushout_ind' f g P push_fl' push_fr' pp') (pp a) = pp' a.
Proof.
  apply pushout_ind_beta_pp.
Defined.                        (* perhaps not necessary. . . *)

Definition pushout_eta_homot {A B C : Type} {f : A -> B} {g : A -> C}
           {P : pushout f g -> Type} (h : forall x, P x)
  : h == pushout_ind' f g P (h o push_fl f g) (h o push_fr f g) (fun a => apD h (pp a)).
Proof.
  unfold pointwise_paths. srapply @pushout_ind'; try reflexivity.
  intro a.
  refine (transport_paths_FlFr_D
            (f := h)
            (g := pushout_ind' f g P (fun x0 : B => h (push_fl  f g x0)) (fun x0 : C => h (push_fr  f g x0))
                               (fun a0 : A => apD h (pp a0)))
            (pp a) ((fun b : B => 1) (f a)) @ _). simpl.
  apply moveR_Mp. refine (pushout_ind_beta_pp P _ _ _ @ _).
  cut (forall q : transport P (pp a) (h (pushl a)) = h (pushr a), q = ((q^@1)^@1)).
  - intro H. apply H.
  - intros []. reflexivity.
Defined.

Definition pushout_rec_eta_homot {A B C : Type} {f : A -> B} {g : A -> C}
           {P : Type} (h : pushout f g -> P)
  : h == pushout_rec' f g P (h o push_fl  f g) (h o push_fr  f g) (fun a => ap h (pp a)).
Proof.
  unfold pointwise_paths.
  srapply @pushout_ind'; try reflexivity.
  intro a.
  refine (transport_paths_FlFr
            (f := h)
            (g := pushout_rec' f g P (fun x0 : B => h (push_fl  f g x0)) (fun x0 : C => h (push_fr f g x0))
                               (fun a0 : A => ap h (pp a0)))
            (pp a) ((fun b : B => 1) (f a)) @ _).
  apply moveR_Mp. refine (pushout_rec_beta_pp P _ _ _ @ _).
  cut (forall q : h (pushl a) = h (pushr a), q = ((q^ @ 1)^ @ 1)).
  intro H. apply H. intros []. reflexivity.
Defined.

Definition path_pushout_rec' {A B C : Type} {f : A -> B} {g : A -> C}
           (P : Type)
           (push_fl' : B -> P)
           (push_fr' : C -> P)
           (pp1 pp2: forall a : A, push_fl' (f a) = push_fr' (g a)) :
  pp1 = pp2 -> pushout_rec' f g P push_fl' push_fr' pp1 == pushout_rec' f g P push_fl' push_fr' pp2 :=
  fun q x => (ap (fun pp' : forall a : A, push_fl' (f a) = push_fr' (g a) =>
                    pushout_rec' f g P push_fl' push_fr' pp' x) q).


Definition functor_pushout {A1 B1 C1 A2 B2 C2}
           {f1 : A1 -> B1} {g1 : A1 -> C1} {f2 : A2 -> B2} {g2 : A2 -> C2}
           (hA : A1 -> A2) (hB : B1 -> B2) (hC : C1 -> C2) :
  (hB o f1 == f2 o hA) -> (hC o g1 == g2 o hA ) ->  pushout f1 g1 -> pushout f2 g2.
Proof.
  intros nat_f nat_g. srapply @pushout_rec'.
  - exact (fun b => push_fl  f2 g2 (hB b)).
  - exact (fun c => push_fr f2 g2 (hC c)).
  - exact (fun a => (ap (push_fl f2 g2) (nat_f a) @ pp (hA a)) @ (ap (push_fr f2 g2) (nat_g a)^)).
Defined.

Definition functor_pushout_beta_pp {A1 B1 C1 A2 B2 C2}
           {f1 : A1 -> B1} {g1 : A1 -> C1} {f2 : A2 -> B2} {g2 : A2 -> C2}
           (hA : A1 -> A2) (hB : B1 -> B2) (hC : C1 -> C2)
           (nat_f : hB o f1 == f2 o hA) (nat_g : hC o g1 == g2 o hA )
           (a : A1)
  : ap (functor_pushout hA hB hC nat_f nat_g) (pp a) =
    (ap (push_fl f2 g2) (nat_f a) @ pp (hA a)) @ (ap (push_fr f2 g2) (nat_g a)^).
Proof.
  unfold functor_pushout. unfold pushout_rec'. refine (pushout_rec_beta_pp (pushout f2 g2) _ _ a ).
Defined.

Definition functor_pushout_compose {A1 B1 C1 A2 B2 C2 A3 B3 C3}
           {f1 : A1 -> B1} {g1 : A1 -> C1} {f2 : A2 -> B2} {g2 : A2 -> C2} {f3 : A3 -> B3} {g3 : A3 -> C3}
           (hA1 : A1 -> A2) (hB1 : B1 -> B2) (hC1 : C1 -> C2)
           (hA2 : A2 -> A3) (hB2 : B2 -> B3) (hC2 : C2 -> C3)
           (nat_f1 : hB1 o f1 == f2 o hA1) (nat_g1 : hC1 o g1 == g2 o hA1 )
           (nat_f2 : hB2 o f2 == f3 o hA2) (nat_g2 : hC2 o g2 == g3 o hA2 )
  : functor_pushout (hA2 o hA1) (hB2 o hB1) (hC2 o hC1)
                    (fun a : A1 => ap (hB2) (nat_f1 a) @ (nat_f2 (hA1 a)))
                    (fun a : A1 => ap (hC2) (nat_g1 a) @ (nat_g2 (hA1 a))) ==
    (functor_pushout hA2 hB2 hC2 nat_f2 nat_g2) o (functor_pushout hA1 hB1 hC1 nat_f1 nat_g1).
Proof.
  intro x. apply inverse.
  refine ((pushout_rec_eta_homot
            ((functor_pushout hA2 hB2 hC2 nat_f2 nat_g2) o (functor_pushout hA1 hB1 hC1 nat_f1 nat_g1)) x) @ _).
  srapply @path_pushout_rec'. cbn.
  apply path_forall. intro a.
  refine (ap_compose _ _ _ @ _).
  refine (ap (fun q : functor_pushout hA1 hB1 hC1 nat_f1 nat_g1 (pushl a) = functor_pushout hA1 hB1 hC1 nat_f1 nat_g1 (pushr a)
              => ap (functor_pushout hA2 hB2 hC2 nat_f2 nat_g2) q) (functor_pushout_beta_pp hA1 hB1 hC1 nat_f1 nat_g1 a) @ _).
  refine (ap_pp _ _ _ @ _).
  refine (whiskerR (ap_pp _ _ _) _ @ _).
  refine (whiskerR (whiskerL (ap (functor_pushout hA2 hB2 hC2 nat_f2 nat_g2) (ap (push_fl f2 g2) (nat_f1 a))) (functor_pushout_beta_pp hA2 hB2 hC2 nat_f2 nat_g2 (hA1 a)))
                    (ap (functor_pushout hA2 hB2 hC2 nat_f2 nat_g2) (ap (push_fr f2 g2) (nat_g1 a)^)) @ _).
  repeat rewrite ap_V. rewrite <- !ap_compose. simpl.
  repeat rewrite ap_pp. rewrite <- ap_compose.
  repeat rewrite concat_pp_p.
  apply whiskerL. apply whiskerL. apply whiskerL.
  rewrite inv_pp. apply whiskerL. apply (ap inverse).
  apply ap_compose.
Qed.                            (* that was a mess. . . *)


           
           
