Require Import HoTT.
Require Import HoTT.Categories Category.Morphisms.
Require Import FunextAxiom.
(* Require Import finite_lemmas. *)


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
    Functor (Type_to_Cat (BuildTruncType 1 (X -> Y)))
            (functor_category (Type_to_Cat X) (Type_to_Cat Y)).
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



