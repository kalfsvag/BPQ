Require Import HoTT.
Require Import finite_lemmas.
Require Import Category.


Section FinCat.
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
