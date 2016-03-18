Require Import HoTT.
(*Require Import Coq.Program.Tactics.*)


Section Book_1_4.
Variable C:Type.

(*Defining the iterator.*)
Fixpoint iter (C:Type) (c0:C) (cs:C->C) (n:nat) : C := 
	match n with
		|O=>c0
		|S p => cs (iter C c0 cs p)
end.


(*Make an iterative step function N*C->N*C from the recursive step function cs.*)
Definition iter_step (c0:C) (cs : nat->C->C) (p:nat*C) : nat*C :=
	match p with
		|(n,c) => (S n, cs n c)
end.

(*Define recursion in terms of the iterator.*)
Definition Rec (c0:C) (cs : nat->C->C) (n:nat) : C :=
	snd (iter (nat*C) (O,c0)  (iter_step c0 cs) n).

Lemma iter_formula : forall (n:nat) (c0:C) (cs : nat->C->C), 
  iter (nat*C) (O,c0) (iter_step c0 cs) n = (n, Rec c0 cs n).
Proof.
  intros n c0 cs.
  apply equiv_path_prod.
  simpl.
  split.
  * (* First projection *)
		induction n.
		** (*Base case*)
			reflexivity.
		** (*Induction step*)
			simpl.
			rewrite IHn.
			reflexivity.
		
  * (*Second projection*)
		induction n.
		** (*Base case*)
			reflexivity.
		** (*Induction step*)
			unfold Rec.
			reflexivity.
Qed.

(* 
	induction n.
	* (*base case*) reflexivity.
	 
	* (*step case*)
	unfold Rec.
	simpl.
	rewrite IHn.
	simpl.
	unfold iter_step.
	reflexivity.
Qed.
 *) 
Proposition Rec_equals_natrec : forall (c0:C)(cs : nat->C->C)(n:nat), 
  	Rec c0 cs n = nat_rec C c0 cs n.
	intros c0 cs.
	intro n.
	
	induction n.
	* reflexivity.
	
	*
	simpl.
	rewrite <- IHn.
	unfold Rec at 1.
	simpl.
	rewrite iter_formula.
	simpl.
	reflexivity.
Qed.


(*Alternative way to do it:*)
Lemma step_equation_satisfied : forall (c0:C)(cs : nat->C->C)(n:nat),
	Rec c0 cs (n.+1) = cs n (Rec c0 cs n).
	intros c0 cs n.
	unfold Rec at 1.
	
	simpl.
	rewrite (iter_formula).
	simpl.
	reflexivity.
Qed.

Proposition Rec_equals_natrec2 : forall (c0:C)(cs : nat->C->C)(n:nat), 
  	Rec c0 cs n = nat_rec C c0 cs n.
  	intros c0 cs n.
  	induction n.
  	* reflexivity.
  	* 
  	rewrite step_equation_satisfied.
  	rewrite IHn.
  	reflexivity.
Qed.

End Book_1_4.