Require Import HoTT.Basics.

Section Definitions.
	Variable A:Set.
	Definition prod A := A->A->A.
	Definition associative {A} (m : prod A) :=
		forall a b c : A, m (m a b) c = m a (m b c).
	Definition commutative {A} (m : prod A) :=
		forall a b : A, m a b = m b a.
	Definition neutral {A} (e:A) (m:prod A) :=
		forall a:A, (m e a = a) /\ (m a e = a).
	Definition exists_inverse {A} (m:prod A) (e:A) :=
		forall a:A, exists a', m a a' = e /\ m a' a = e.
	
	Definition isMonoid A (m : prod A) (e:A) :=
		associative m /\ neutral e m.
	Definition isCommutative_Monoid A (m : prod A) (e:A) :=
		associative m /\ neutral e m /\ commutative m.
	Definition isGroup A (m:prod A) (e:A) :=
		associative m /\ neutral e m /\ exists_inverse m e.
	Definition isAbelian_Group A (m:prod A) (e:A) :=
		associative m /\ neutral e m /\ exists_inverse m e /\ commutative m.
End Definitions.

Section Nat.
	Fixpoint add (m:nat) : nat->nat :=
		match m with
			| O => (fun n:nat => n)
			| S m => (fun n:nat => S (add m n) )
		end.
		
	
	(*Addition is defined recursively on the first variable.
	It also decreases on second variable: *)
	Lemma pred_second : forall m n : nat, add m (S n) = S (add m n).
	Proof.
		intros m n.
		induction m.
		(*Base case*) * reflexivity.
		(*Induction step*) *
			simpl.
			rewrite IHm. reflexivity.
	Defined.
	
	Lemma addzero : forall n : nat, add n 0 = n.
	Proof.
	induction n. reflexivity. (*Base case done*)
	(*Induction step:*)
	simpl. rewrite IHn. reflexivity.
	Defined.

	Lemma zeroadd : forall n : nat, add 0 n = n.
	Proof. reflexivity. Defined.	

	Lemma add_associative : forall l m n:nat, add (add l m) n = add l (add m n).
		induction l.
			induction m.
				induction n.
					(*l m n = 0*) * reflexivity.
					(*l = m = 0, Step n*)* reflexivity.
					(*l = 0, Step m *)* reflexivity.
					(*Step l*)*
						intros m n.
						simpl.
						apply (ap S).
						apply IHl.
	Defined.
	
	Lemma add_commutative : forall n m:nat, add n m = add m n.
		induction n.
		(*Base case*) *
			intro m.
			rewrite addzero. reflexivity.
		(*Induction step*) *
			intro m.
			simpl.
			rewrite IHn.
			symmetry.
			apply pred_second.
	Defined.
	
	Proposition nat_comm_monoid : isCommutative_Monoid nat add O.
		unfold isCommutative_Monoid.
		split.
			(*Associativity*) *
					unfold associative.
					apply add_associative.
				* split.
				(*Neutral element*) **
					unfold neutral.
					intro n.
					split.
							***apply zeroadd. ***apply addzero.
			(*Commutativity*) **
				unfold commutative.
				apply add_commutative.
	Defined.
			


	(*Define addition by recursion on the second variable.*)
	Fixpoint add' (m n : nat) : nat :=
		match n with
		|O => m
		|S n1 => S (add' m n1)
	end.
	
	
	Proposition equaladditions : forall m n:nat, add m n = add' m n.
		induction n.
		(*Base case*) * simpl. rewrite addzero. reflexivity.
		(*Induction step*) *
			simpl.
			rewrite pred_second.
			rewrite IHn.
			reflexivity.
	Defined.

			
	(*Slightly different proof showing that the two additions are equal (doesn't use lemmas)*)
	Proposition equaladditions2 : forall m n:nat, add m n = add' m n.
		induction m.
		(*Base case m*) *
			induction n.
				(*Base case n*) ** reflexivity.
				(*Induction step n*) ** 
					simpl.
					rewrite <- IHn. 
					reflexivity.
		(*Induction step m*) *
 			intro n.
			simpl.
			rewrite IHm.
				induction n.
					(*Base case n*) ** reflexivity.
					(*Induction step n*) **
						simpl.
						rewrite IHn. reflexivity.
	Defined.

End Nat.

Section Bad_Idea.
	Inductive Z' : Set :=
		|minus (n0 n1:nat) : Z'
	.
	
	Axiom eq_Z : forall m1 m2 n1 n2 : nat, 
		add m1 n2 = add n1 m2 <-> minus m1 m2 = minus n1 n2.
	
	Definition f (n : Z') : nat :=
		match n with
			minus n1 n2 => n1
		end.
	
	Lemma eq1 : minus 1 1 = minus 0 0.
		apply eq_Z. reflexivity.
	Qed.
	
	Theorem wrong : 1=0.
		apply ((ap f) eq1).
	Qed.

End Bad_Idea.



Section Integers.	

	Inductive Z : Set :=
		|subt (n0 n1:nat) : Z
	.
	
	Definition EqZ (m n : Z) : Type :=
		match m,n with
			| subt m1 m2, subt n1 n2 =>
				add m1 n2 = add m2 n1
		end.
	
	Lemma refl_Z : Reflexive EqZ.
		unfold Reflexive. Abort.
	
	(*TODO: This is equiv relation*)
	
	
	Definition WellDefined_Z {A:Type} (f:Z->A) : Type.
		(*TODO*) exact A. Defined.
(* 	Axiom eq_Z_1 : forall m1 m2 n1 n2 : nat, 
		add m1 n2 = add n1 m2 -> subt m1 m2 = subt n1 n2.
	
	Axiom eq_Z_2 : forall m1 m2 n1 n2 : nat, 
		subt m1 m2 = subt n1 n2 -> add m1 n2 = add n1 m2. *)
	
	Definition inj (n: nat) : Z := subt n O.
	
	Definition neg (m:Z) :=
		match m with
		|subt m1 m2 => subt m2 m1
	end.
	
(* 	Definition add_Z (m n : Z) : Z :=
		match m with
		| subt m1 m2 => match n with
			|subt n1 n2 => subt (add m1 n1) (add m2 n2)
		end
	end.
 *)	
	Definition add_Z (m n : Z) : Z :=
		match m,n with
		|subt m1 m2, subt n1 n2 => subt (add m1 n1) (add m2 n2)
	end.
	
	Definition subt_Z (m n: Z) : Z :=
		add_Z m (neg n).
		
	Proposition injection : forall m n:nat, inj m = inj n -> m = n.
	Proof.
		unfold inj.
		intros m n p.
 		rewrite <- (addzero m). rewrite <- (addzero n).
		apply eq_Z_2.
		assumption.
	Defined.
	
	(*Abelian group axioms*)
	Lemma add_Z_associative : forall l m n : Z, 
		add_Z (add_Z l m) n = add_Z l (add_Z m n).
	Proof.
		induction l.
		induction m.
		induction n.
		unfold add_Z.
		rewrite add_associative. rewrite add_associative. reflexivity.
	Defined.
	
	Lemma add_Z_commutative : forall m n : Z,
		add_Z m n = add_Z n m.
		induction m.
		induction n.
		simpl.
		rewrite (add_commutative n2 n0). rewrite (add_commutative n3 n1). reflexivity.
	Defined.
		
	Definition O_Z := subt O O.
	
	Lemma addzero_Z : forall n : Z, add_Z n O_Z = n.
	Proof.
		induction n.
		unfold O_Z.
		unfold add_Z.
		rewrite addzero. rewrite addzero. reflexivity.
	Defined.
	Lemma zeroadd_Z : forall n : Z, add_Z O_Z n = n.
		induction n.
		unfold O_Z.
		unfold add_Z.
		rewrite zeroadd. rewrite zeroadd. reflexivity.
	Defined.
	
	Lemma inverse_neg : forall n : Z, add_Z n (neg n) = O_Z /\ add_Z (neg n) n = O_Z.
	Proof.
		induction n.
		unfold neg.
		unfold add_Z.
		unfold O_Z.
		split.
		*apply eq_Z_1.
		rewrite addzero. rewrite zeroadd. 
		apply add_commutative.
		*apply eq_Z_1.
		rewrite addzero. rewrite zeroadd. 
		apply add_commutative.
	Defined.
	
	Proposition Z_abelian : isAbelian_Group Z add_Z O_Z.
		unfold isAbelian_Group.
		
		split.
		(*Associativity*) *
			unfold associative. apply add_Z_associative.
		* split.
		(*Neutral element*) **
			unfold neutral. intro n. split.
				***apply zeroadd_Z. ***apply addzero_Z.
		** split.
		(*Exists inverse*) ***
			unfold exists_inverse.
				intro n.
				exists (neg n). apply inverse_neg.
		(*Commutativity*) ***
			unfold commutative.
			apply add_Z_commutative.
	Defined.

End Integers.

Section Problem.
	Definition f (n : Z) : nat :=
		match n with
			subt n1 n2 => n1
		end.
	
	Lemma eq1 : subt 1 1 = subt 0 0.
		apply eq_Z_1. reflexivity.
	Qed.
	
	Theorem wrong : 1=0.
		apply ((ap f) eq1).
	Qed.