Require Import HoTT.
Require Import UnivalenceAxiom.

Section B_Aut.
  Context (X : Type).
  Definition B_Aut  :=
    {A : Type & merely (A <~> X)}.

  Definition type_of_BAut : B_Aut -> Type := pr1.
    
  Coercion type_of_BAut : B_Aut >-> Sortclass .

  Global Instance ispointed_BAut : IsPointed B_Aut := (X; tr (equiv_idmap X)).

  Global Instance trunc_B_Aut (n : trunc_index) `{IsTrunc n.+1 X} :
    IsTrunc n.+2 (B_Aut).
  Proof.
    intros [A eA] [B eB].
    change (IsTrunc_internal n.+1) with (IsTrunc n.+1).
    strip_truncations.
    apply (trunc_equiv' (A <~> X)).
    - refine (equiv_path_sigma_hprop (_;_) (_;_) oE _). simpl.
      refine (equiv_path_universe A B oE _).
      apply (equiv_functor_equiv (equiv_idmap A) (equiv_inverse eB)).
    - apply istrunc_equiv.
  Qed.
End B_Aut.
