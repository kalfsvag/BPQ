Require Import HoTT.
Require Import pointed_lemmas.

Section Smash.
  (* Define smash product *)
  Private Inductive smash (A B : pType) : Type :=
    |pair_smash (a : A) (b : B) : (smash A B)
    |hub_l : smash A B
    |hub_r : smash A B.

  Arguments pair_smash {A} {B} a b.
  Arguments hub_l {A} {B}.
  Arguments hub_r {A} {B}.

  Axiom ispointed_pairs_l : forall (A B : pType) (b : B), pair_smash (point A) b = hub_l.
  Axiom ispointed_pairs_r : forall (A B : pType) (a : A), pair_smash a (point B) = hub_r.

  Definition smash_ind (A B : pType)
             (P : smash A B -> Type)
             (pair_smash' : forall (a : A) (b : B), P (pair_smash a b))
             (hub_l' : P (hub_l))
             (hub_r' : P (hub_r))
             (ispointed_pairs_l' : forall (b : B), transport P (ispointed_pairs_l A B b) (pair_smash' (point A) b) = hub_l')
             (ispointed_pairs_r' : forall (a : A), transport P (ispointed_pairs_r A B a) (pair_smash' a (point B)) = hub_r')
                                                   :forall x : smash A B, P x.
  Proof.
    intro x. destruct x.
    - exact (pair_smash' a b).
    - exact hub_l'.
    - exact hub_r'.
  Defined.

  Axiom smash_ind_beta_ispointed_pairs_l :
    forall (A B : pType)
           (P : smash A B -> Type)
           (pair_smash' : forall (a : A) (b : B), P (pair_smash a b))
           (hub_l' : P (hub_l))
           (hub_r' : P (hub_r))
           (ispointed_pairs_l' : forall (b : B), transport P (ispointed_pairs_l A B b) (pair_smash' (point A) b) = hub_l')
           (ispointed_pairs_r' : forall (a : A), transport P (ispointed_pairs_r A B a) (pair_smash' a (point B)) = hub_r')
           (b : B),
      apD (smash_ind A B P pair_smash' hub_l' hub_r' ispointed_pairs_l' ispointed_pairs_r') (ispointed_pairs_l A B b) = ispointed_pairs_l' b.


  Axiom smash_ind_beta_ispointed_pairs_r :
    forall (A B : pType)
           (P : smash A B -> Type)
           (pair_smash' : forall (a : A) (b : B), P (pair_smash a b))
           (hub_l' : P (hub_l))
           (hub_r' : P (hub_r))
           (ispointed_pairs_l' : forall (b : B), transport P (ispointed_pairs_l A B b) (pair_smash' (point A) b) = hub_l')
           (ispointed_pairs_r' : forall (a : A), transport P (ispointed_pairs_r A B a) (pair_smash' a (point B)) = hub_r')
           (a : A),
      apD (smash_ind A B P pair_smash' hub_l' hub_r' ispointed_pairs_l' ispointed_pairs_r') (ispointed_pairs_r A B a) = ispointed_pairs_r' a.
End Smash.

Definition smash_rec (A B : pType)
           (P : Type)
           (pair_smash' : A  -> B -> P)
           (hub_l' : P)
           (hub_r' : P)
           (ispointed_pairs_l' : forall (b : B), pair_smash' (point A) b = hub_l')
           (ispointed_pairs_r' : forall (a : A), pair_smash' a (point B) = hub_r')
  : smash A B -> P.
Proof.
  apply (smash_ind A B (fun _ => P) pair_smash' hub_l' hub_r'); intros;
    refine (transport_const _ _ @ _).
  exact (ispointed_pairs_l' b).
  exact (ispointed_pairs_r' a).
Defined.

Definition smash_rec_beta_ispointed_pairs_l (A B : pType)
           (P : Type)
           (pair_smash' : A  -> B -> P)
           (hub_l' : P)
           (hub_r' : P)
           (ispointed_pairs_l' : forall (b : B), pair_smash' (point A) b = hub_l')
           (ispointed_pairs_r' : forall (a : A), pair_smash' a (point B) = hub_r')
           (b : B) :
  ap (smash_rec A B P pair_smash' hub_l' hub_r' ispointed_pairs_l' ispointed_pairs_r')
     (ispointed_pairs_l A B b)
  = ispointed_pairs_l' b.
Proof.
  apply (cancelL (transport_const (ispointed_pairs_l A B b) (pair_smash' (point A) b))).
  transitivity (apD (smash_rec A B P pair_smash' hub_l' hub_r' ispointed_pairs_l' ispointed_pairs_r')
               (ispointed_pairs_l A B b)).
  symmetry; refine (apD_const
                      (smash_rec A B P pair_smash' hub_l' hub_r' ispointed_pairs_l' ispointed_pairs_r') _).
  refine (smash_ind_beta_ispointed_pairs_l A B _ _ _ _ _ _ b).
Defined.
  
                                   
Global Instance ispointed_smash {A B : pType} : IsPointed (smash A B) := (hub_l A B).


Definition functor_smash {A B A' B' : pType} (f : A ->* A') (g : B ->* B')
           : smash A B ->* smash A' B'.
Proof.
  srapply @Build_pMap.
  - cbn.
    srapply @smash_rec.
    + intros a b.
      apply pair_smash. exact (f a). exact (g b).
    + apply hub_l.
    + apply hub_r.
    + intros. cbn.
      transitivity (pair_smash A' B' (point A') (g b)).
      { apply (ap (fun a' => pair_smash A' B' a' (g b))). exact (point_eq f). }
      { apply (ispointed_pairs_l A' B'). }
    + intros. cbn.
      transitivity (pair_smash A' B' (f a) (point B')).
      { apply (ap (pair_smash A' B' (f a))). exact (point_eq g). }
      { apply (ispointed_pairs_r A' B'). }
  - cbn. reflexivity.
Defined.
    
        
        





