Require Import HoTT.
(*Some results on coequalizers*)

(*This should be somewhere else. . .*)
Definition prod_uncurryD {A B : Type} {P : A -> B -> Type} :
  (forall p : A*B, P (fst p) (snd p)) -> forall a : A, forall b : B, P a b :=
  (equiv_prod_ind _)^-1 .



Lemma Coeq_precompose `{Funext} {B A : Type} {f : B -> A} {g : B -> A} :
  (@coeq B A f g) o f = coeq o g.
Proof.
  apply path_forall.
  intro b.
  apply cp.
Defined.



(* (*Want to show that Coequ commutes with product: *)
(*    Coeq f g * Coeq f' g' <~> Coeq (functor_prod f f') (functor_prod g g') *)
(*    Then, using equiv_prod_ind, iterated Coequalizers will perhaps be easier to define. *)
(*  *) *)
(* Section Coeq_prod_commute. *)

(*   (*Can generalize this to having *)
(*      r : A -> A' *)
(*      s : B -> B' *)
(*    such that sf = f'r and sg = g'r *)
   
(*    The case proved is r = const (point A'), s = const (f (point A')) *)

(*    *) *)

(*   Definition prod_coeq_to_coeq_prod *)
(*              {A B A' B' : Type} *)
(*              {a0 : IsPointed A} *)
(*              {f g : A -> B} {f' g' : A'-> B'} *)
(*              {pointed_f : f a0 = g a0} : *)
(*     Coeq f g * Coeq f' g' -> Coeq (functor_prod f f') (functor_prod g g'). *)
(*   Proof. *)
(*     apply prod_curry. *)
(*     refine (Coeq_rec _ _ _). *)
(*     - intro b. *)
(*       refine (functor_coeq _ _ _ _). *)
(*       + exact (fun a' => (point A, a')). *)
(*       + exact (fun b' => (f (point A) , b')). *)
(*       + intro a'. exact idpath. *)
(*       + intro a'. unfold functor_prod. simpl. *)
(*         apply (ap (fun b => (b, g' a'))). *)
(*         exact (pointed_f). *)
(*     - intro a. *)
(*       exact idpath. *)
(*   Defined. *)

(*   Definition prod_coeq_to_coeq_prod2 *)
(*              {A B A' B' A'' B'' : Type} *)
(*              {a0 : IsPointed A} *)
(*              {a0' : IsPointed A'} *)
(*              {f g : A -> B} {f' g' : A'-> B'} {f'' g'' : A''-> B''} *)
(*              {pointed_f : f a0 = g a0} *)
(*              {pointed_f' : f' a0' = g' a0'}: *)
    
(*     Coeq f g * Coeq f' g' * Coeq f'' g'' -> *)
(*     Coeq (functor_prod (functor_prod f f') f'') (functor_prod (functor_prod g g') g''). *)
(*   Proof. *)
(*     refine (prod_coeq_to_coeq_prod o _). *)
(*     - apply path_prod. exact pointed_f. exact pointed_f'. *)
(*     - refine (functor_prod _ idmap). *)
(*       refine (prod_coeq_to_coeq_prod). exact pointed_f. *)
(*   Defined. *)

(*   Definition coeq_prod_to_prod_coeq *)
(*              {A B A' B' : Type} *)
(*              {f g : A -> B} {f' g' : A'-> B'} : *)
(*     Coeq (functor_prod f f') (functor_prod g g') -> Coeq f g * Coeq f' g'. *)
(*   Proof. *)
(*     refine (Coeq_rec _ _ _). *)
(*     - exact (functor_prod coeq coeq). *)
(*     - intros [a a']. *)
(*       unfold functor_prod. *)
(*       simpl. *)
(*       apply path_prod. apply cp. apply cp. *)
(*   Defined. *)


(* (* (equiv_prod_ind _) *) *)
(*   (*Try to show stuff so that I can use prod_coeq_to_coeq_prod in functor_forall*) *)
(*   Definition pullback_pc_to_cp (*TODO: Better name*) *)
(*              {A B A' B' : Type} *)
(*              {f g : A -> B} {f' g' : A'-> B'} *)
(*              (P : Coeq f g -> Coeq f' g' -> Type) : *)
(*     Coeq (functor_prod f f') (functor_prod g g') -> Type. *)
(*   Proof. *)
(*     refine (Coeq_rec _ _ _). *)
(*     - intros [b b']. *)
(*       exact (P (coeq b) (coeq b')). *)
(*     - intros [a a']. *)
(*       simpl. *)
(*       refine (concat (y:= P (coeq (g a)) (coeq (f' a'))) _ _). *)
(*       + apply (ap (fun c => P c (coeq (f' a')))). *)
(*         apply cp. *)
(*       + apply (ap (fun c => P (coeq (g a)) c)). *)
(*         apply cp. *)
(*   Defined. *)

(*   (*TODO: Prove and give better name*) *)
(*   Definition badbadname *)
(*              {A B A' B' : Type} *)
(*              {a0 : IsPointed A} *)
(*              {f g : A -> B} {f' g' : A'-> B'} *)
(*              {pointed_f : f a0 = g a0} *)
(*              (P : Coeq f g -> Coeq f' g' -> Type) : *)
(*     forall c : Coeq f g, forall c' : Coeq f' g', *)
(*       (pullback_pc_to_cp P (prod_coeq_to_coeq_prod (pointed_f := pointed_f) (c, c'))) -> P c c'. *)
(*     Proof. *)
(*       refine (Coeq_ind _ _ _). *)
(*         intro b. *)
(*         refine (Coeq_ind _ _ _). *)
(*           intro b'. *)
(*           simpl. *)
(*           rewrite pointed_f. *)
(*           Admitted. *)


(*     Definition changebase *)
(*              {A B A' B' : Type} *)
(*              {a0 : IsPointed A} *)
(*              {f g : A -> B} {f' g' : A'-> B'} *)
(*              (pointed_f : f a0 = g a0) *)
(*              (P : Coeq f g -> Coeq f' g' -> Type) *)
(*     : (forall p : Coeq (functor_prod f f') (functor_prod g g'), pullback_pc_to_cp P p) *)
(*       -> (forall c : Coeq f g, forall c' : Coeq f' g', P c c'). *)
(*       intro x. *)
(*       apply prod_uncurryD. *)
(*       revert x. *)
(*       refine (functor_forall _ _). *)
(*       - exact (prod_coeq_to_coeq_prod (pointed_f := pointed_f)). *)
(*       - refine (prod_ind _ _). *)
(*         refine (badbadname  P). *)
(*     Defined. *)
        
          
      
      

  
  
(* (* *)

(*   Lemma Coeq_prod_commute  (f g : A->B) (f' g' : A'->B'): *)
(*     Coeq f g * Coeq f' g' <~> Coeq (functor_prod f f') (functor_prod g g'). *)
(*   Abort. *)

(* *) *)