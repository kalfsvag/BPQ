Require Import HoTT.

Section Smash.
  (* Define smash product *)
  Private Inductive Smash (A B : pType) : Type :=
    |pair_smash (a : A) (b : B) : (Smash A B)
    |hub_l : Smash A B
    |hub_r : Smash A B.

  Arguments pair_smash {A} {B} a b.
  Arguments hub_l {A} {B}.
  Arguments hub_r {A} {B}.

  Axiom ispointed_pairs_l : forall (A B : pType) (b : B), pair_smash (point A) b = hub_l.
  Axiom ispointed_pairs_r : forall (A B : pType) (a : A), pair_smash a (point B) = hub_r.

  Definition Smash_ind (A B : pType)
             (P : Smash A B -> Type)
             (pair_smash' : forall (a : A) (b : B), P (pair_smash a b))
             (hub_l' : P (hub_l))
             (hub_r' : P (hub_r))
             (ispointed_pairs_l' : forall (b : B), transport P (ispointed_pairs_l A B b) (pair_smash' (point A) b) = hub_l')
             (ispointed_pairs_r' : forall (a : A), transport P (ispointed_pairs_r A B a) (pair_smash' a (point B)) = hub_r')
                                                   :forall x : Smash A B, P x.
  Proof.
    intro x. destruct x.
    - exact (pair_smash' a b).
    - exact hub_l'.
    - exact hub_r'.
  Defined.

  Axiom Smash_ind_beta_ispointed_pairs_l :
    forall (A B : pType)
           (P : Smash A B -> Type)
           (pair_smash' : forall (a : A) (b : B), P (pair_smash a b))
           (hub_l' : P (hub_l))
           (hub_r' : P (hub_r))
           (ispointed_pairs_l' : forall (b : B), transport P (ispointed_pairs_l A B b) (pair_smash' (point A) b) = hub_l')
           (ispointed_pairs_r' : forall (a : A), transport P (ispointed_pairs_r A B a) (pair_smash' a (point B)) = hub_r')
           (b : B),
      apD (Smash_ind A B P pair_smash' hub_l' hub_r' ispointed_pairs_l' ispointed_pairs_r') (ispointed_pairs_l A B b) = ispointed_pairs_l' b.


  Axiom Smash_ind_beta_ispointed_pairs_r :
    forall (A B : pType)
           (P : Smash A B -> Type)
           (pair_smash' : forall (a : A) (b : B), P (pair_smash a b))
           (hub_l' : P (hub_l))
           (hub_r' : P (hub_r))
           (ispointed_pairs_l' : forall (b : B), transport P (ispointed_pairs_l A B b) (pair_smash' (point A) b) = hub_l')
           (ispointed_pairs_r' : forall (a : A), transport P (ispointed_pairs_r A B a) (pair_smash' a (point B)) = hub_r')
           (a : A),
      apD (Smash_ind A B P pair_smash' hub_l' hub_r' ispointed_pairs_l' ispointed_pairs_r') (ispointed_pairs_r A B a) = ispointed_pairs_r' a.
End Smash.

Definition Smash_rec (A B : pType)
           (P : Type)
           (pair_smash' : A  -> B -> P)
           (hub_l' : P)
           (hub_r' : P)
           (ispointed_pairs_l' : forall (b : B), pair_smash' (point A) b = hub_l')
           (ispointed_pairs_r' : forall (a : A), pair_smash' a (point B) = hub_r')
  : Smash A B -> P.
Proof.
  apply (Smash_ind A B (fun _ => P) pair_smash' hub_l' hub_r'); intros;
    refine (transport_const _ _ @ _).
  exact (ispointed_pairs_l' b).
  exact (ispointed_pairs_r' a).
Defined.

Definition Smash_rec_beta_ispointed_pairs_l (A B : pType)
           (P : Type)
           (pair_smash' : A  -> B -> P)
           (hub_l' : P)
           (hub_r' : P)
           (ispointed_pairs_l' : forall (b : B), pair_smash' (point A) b = hub_l')
           (ispointed_pairs_r' : forall (a : A), pair_smash' a (point B) = hub_r')
           (b : B) :
  ap (Smash_rec A B P pair_smash' hub_l' hub_r' ispointed_pairs_l' ispointed_pairs_r')
     (ispointed_pairs_l A B b)
  = ispointed_pairs_l' b.
Proof.
  
  
                                   

