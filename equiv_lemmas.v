Require Import HoTT.

Definition equiv_emoveR_fV `{Funext} {A B C : Type} (e : A <~> B) (f : B -> C) (g : A -> C) : 
  g = f o e <~> g o e^-1 = f.
Proof.
  transitivity (g == f o e).
  apply equiv_inverse.
  apply equiv_path_arrow.
  transitivity (g o e^-1 == f).
  unfold pointwise_paths.
  apply equiv_inverse.
  apply (equiv_functor_forall' e).
  intro b.
  apply (equiv_concat_l).
  apply (ap g).
  change (e^-1 (e b)) with ((e^-1 o e) b).
  apply (ap10 (f:= idmap)).
  apply path_arrow.
  intro x. apply inverse. apply (eissect e).
  apply equiv_path_arrow.
Defined.
