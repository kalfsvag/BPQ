Require Import HoTT.


(*A tactic for rewriting truncated equalities. I.e. [p : Trunc n (a=b)].
 Only works when the goal is truncated.
 Not very foolproof. *)
Ltac trunc_rewrite p :=
  pose proof p as truncated_path;
  revert truncated_path; apply Trunc_rec; intro truncated_path; rewrite truncated_path; clear truncated_path.



(*A more general version of trunc_sigma that only requires A to be "locally truncated" wherever there is a [b : Ba] *)
Definition trunc_sigma' {A : Type} {B : A -> Type} {n : trunc_index} :
           (forall a : A, IsTrunc (n.+1) (B a)) ->
           (forall p q : {a : A & B a}, IsTrunc n (p.1 = q.1)) ->
           IsTrunc (n.+1) {a : A & B a}.
Proof.
  intros H_B H_pq.
  intros ab ab'.
  cut (IsTrunc n ({p : ab.1 = ab'.1 & p# ab.2 = ab'.2})).
  apply trunc_equiv'.
  exact (BuildEquiv _ _ (path_sigma_uncurried B ab ab') _).

  apply trunc_sigma.
Defined.

(*Transport along truncated paths*)
Definition truncated_transport (n : trunc_index) {A : Type} (B : A -> Type)
           {HB : forall a : A, IsTrunc n (B a)}
           {a a' : A} (p : Trunc n (a = a')) :
  B a -> B a'.
Proof.
  intro b. revert p. apply Trunc_rec. intro p.
  exact (transport B p b).
Defined.
