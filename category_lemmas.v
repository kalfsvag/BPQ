Require Import HoTT.
Require Import HoTT.Categories Category.Morphisms.
Require Import finite_lemmas.


Section Type_to_Cat.
  
  
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
    srapply (Build_Functor (Type_to_Cat X) (Type_to_Cat Y) F).
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
    - apply arrow_to_functor.
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




Section FinCat.
  Require Import finite_lemmas.
  Definition fin_1type : 1-Type.
    srapply (@BuildTruncType 1 {n : nat & Finite_Types n}).
    red.
    intros A B.
    apply (trunc_equiv' (A.2 <~> B.2) (path_finite_types A B)).
  Defined.

  (* Check (fundamental_pregroupoid_category fin_1type). *)
  (* Definition fincat : PreCategory. *)
  (* Proof. *)
  (*   srapply (Build_PreCategory (fun m n : nat => Fin m = Fin n)); simpl. *)
  (*   - intro m. reflexivity. *)
  (*   - intros l m n. *)
  (*     intros p q. exact (q @ p). *)
  (*   - intros. simpl. *)
  (*     apply concat_p_pp. *)
  (*   - simpl. intros. *)
  (*     apply concat_p1. *)
  (*   - simpl. intros. *)
  (*     apply concat_1p. *)
  (* Defined. *)

  Definition fincat : PreCategory.
  Proof.
    srapply (Build_PreCategory (fun m n : nat => Fin m <~> Fin n)); simpl.
    - intro m. apply equiv_idmap.
    - intros l m n.
      apply equiv_compose'.
    - intros. simpl.
      apply path_equiv. reflexivity.
    - simpl. intros.
      apply path_equiv. reflexivity.
    - simpl. intros. apply path_equiv. reflexivity.
  Defined.

    
  
  (* Trying to show that these are equivalent *)
  Definition F : Functor fincat (Type_to_Cat (fin_1type)).
  Proof.
    srapply @Build_Functor; simpl.
    - intro m. exact (m; canon m).
    - intros m n e. simpl. 
      apply path_finite_types.
      apply e.
    - intros a b c e1 e2.
      hnf. 
      apply (path_finite_types_compose (a; canon a) (b; canon b) (c; canon c)).
    - hnf.
      intro n.
      apply path_finite_types_1.
  Defined.

  Definition G : Functor (Type_to_Cat (fin_1type)) fincat.
  Proof.
    srapply @Build_Functor; simpl.
    - apply pr1.
    - intros A B []. exact equiv_idmap.
    - intros a b c [] []. simpl.
      apply path_equiv. reflexivity.
    - reflexivity.
  Defined.
    
  (* F is a weak equivalence (def 9.4.6) *)
  Arguments path_finite_types : simpl never.
  
  Definition fullyfaithful_F :
    forall (a b : _), IsEquiv (@morphism_of _ _ F a b).  
  Proof.
    intros a b. simpl in a, b.
    unfold F. cbn.
    apply equiv_isequiv.
  Defined.

  Definition essentially_surj_F :
    Attributes.IsEssentiallySurjective F.
  Proof.
    unfold Attributes.IsEssentiallySurjective. simpl.
    intros [m [A fA]]. strip_truncations.
    apply tr.
    exists m.
    srapply @Build_Isomorphic. simpl.
    apply path_finite_types.
    simpl. apply equiv_inverse.
    apply fA.
  Defined. 
    

    
End FinCat.