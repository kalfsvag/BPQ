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
Section Coeq_prod_commute.
  Open Scope pointed_scope.
  Variables A B A' B' : pType.

  Definition prod_coeq_to_coeq_prod (f g : A ->* B) (f' g' : A'->* B') :
    Coeq f g * Coeq f' g' -> Coeq (functor_prod f f') (functor_prod g g').
  Proof.
    apply prod_curry.
    refine (Coeq_rec _ _ _).
    - intro b.
      refine (functor_coeq _ _ _ _).
      + exact (fun a' => (point A, a')).
      + exact (fun b' => (point B , b')).
      + intro a'.
        apply path_prod.
        * exact (point_eq f)^ .
        * exact idpath.
      + 
              
        
      
      refine (Coeq_rec _ _ _).
      + intro b'.
        apply coeq.
        exact (b,b').
      + intro a'.
        simpl.
        
      



  Lemma Coeq_prod_commute  (f g : A->B) (f' g' : A'->B'):
    Coeq f g * Coeq f' g' <~> Coeq (functor_prod f f') (functor_prod g g').
  Admitted.


