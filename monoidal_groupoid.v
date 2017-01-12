Require Import HoTT.
Require Import UnivalenceAxiom.
Load pType_basics.


(*Defining the monoidal type of finite sets and isomorphisms*)
Section FinIso.
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Definition iFin := { S : Type & Finite S }.
  (*ishprop_finite*)

  (*The cardinal of the finite set*)
  Definition cardinal (S : iFin) : nat := @fcard S.1 S.2.

  (*Canonical objects in iFin*)
  Definition fin (n : nat) : iFin := ( Fin n ; finite_fin n ).

  (*Every object is canonical*)
  Lemma canonical_iFin (S : iFin) : merely (S = fin (cardinal S)).
  Proof.
    refine (Trunc_rec (n:=-1) (A := (S.1 <~> Fin (fcard S.1))) _ _).
    - intro e.
      apply tr.
      apply path_sigma_hprop.
      exact (path_universe e). 
    - apply merely_equiv_fin.
  Defined.
  (*Should be possible to choose an isomorphism? *)

  (*The monoidal structure on iFin*)
  Definition FinPlus : iFin-> iFin -> iFin.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (S1 + S2 ; finite_sum _ _).
  Defined.

  (*I feel it should be possible to make a tactic *)
  Definition FinPlus_assoc : associative FinPlus.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2] [S3 fin_S3].
    refine (path_sigma_hprop _ _ _).
    srapply @path_universe.
    apply equiv_sum_assoc. exact _.
  Defined.
  
  Definition FinPlus_leftid : left_identity FinPlus (fin 0).
  Proof.
    intros [S fin_S].
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_l S)).
  Defined.

  Definition FinPlus_rightid : right_identity FinPlus (fin 0).
  Proof.
    intros [S fin_S].
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_r S)).
  Defined.

  Definition FinPlus_symmetric : symmetric FinPlus. 
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (equiv_sum_symm S1 S2)).
  Defined.

End FinIso.