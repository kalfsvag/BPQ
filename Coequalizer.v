Require Import HoTT.
(*Some results on coequalizers*)


Lemma Coeq_precompose `{Funext} {B A : Type} {f : B -> A} {g : B -> A} :
  (@coeq B A f g) o f = coeq o g.
Proof.
  apply path_forall.
  intro b.
  apply cp.
Defined.



(*Want to show that Coequ commutes with product:
   Coeq f g * Coeq f' g' <~> Coeq (functor_prod f f') (functor_prod g g')
   Then, using equiv_prod_ind, iterated Coequalizers will perhaps be easier to define.
 *)


(*Assume it first to see if things get easier*)

Lemma Coeq_prod_commute {A B A' B' : Type} (f g : A->B) (f' g' : A'->B'):
   Coeq f g * Coeq f' g' <~> Coeq (functor_prod f f') (functor_prod g g').
  Admitted.


