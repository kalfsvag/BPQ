Require Import HoTT.
Load stuff.

(* The nonempty finite sets of n+1 elements *)
Inductive pFin : forall (n : nat), Type :=
  | fin_zero {n : nat} : pFin n
  | fin_succ {n : nat} : pFin n -> pFin n.+1.

Definition fin_include {n : nat} : pFin n -> pFin n.+1.
Proof.
  intro i. induction i.
  (* zero goes to zero *)
  exact fin_zero.
  (* i+1 goes to i+1 *)
  exact (fin_succ IHi).
Defined.

(* pFin is equivalent to Fin *)
Lemma equiv_pFin_Fin (n : nat) : pFin n <~> Fin n.+1.
Proof.
  srapply @equiv_adjointify.
  - intro i. induction i.
    (* i=0 *) exact (inr tt).
    (* i+1 *) exact (inl IHi).
  - induction n.
    intro i. exact fin_zero.    (* n=0 *)
    intros [i |].
    exact (fin_succ (IHn i)). (* i+1 *)
    intro t. exact fin_zero.  (* i=0 *)
  - intro i. simpl.
    induction n. simpl. destruct i. contradiction. destruct u. reflexivity.
    destruct i.
    { simpl. exact (ap inl (IHn f)). } destruct u. reflexivity.
  - intro i. induction i.
    + simpl. induction n. reflexivity. reflexivity.
    + simpl. simpl in IHi. exact (ap fin_succ IHi).
Defined.


(* (* Use my own definition of minus. . . *) *)
(* Notation "n - m" := (nat_minus m n). *)

(* (* The finite pointed set {0, 1, ..., n} *) *)
(* Notation "[ n ]" := (Fin (S n)). *)

(* (* I order [Fin n] so that zero is the "outmost" element. *) *)
(* (*In that way, recursion over [Fin n] is as close as possible as recursion over [nat]. *) *)
(* Definition fin_zero {n} : [n] := inr tt. *)

(* Instance ispointed_fin {n : nat} : IsPointed [n] := fin_zero. *)

(* (* Then the inclusion [inl : [n] -> [n+1]] becomes the successor function *) *)
(* Definition fin_succ {n : nat} : Fin n -> [n] := inl. *)

(* (* Recursion over finite sets *) *)
(* Definition fin_rec {n : nat} (A : Type) (a0 : A) (aS : (Fin n) -> A) : [n] -> A. *)
(* Proof. *)
(*   intros [|]. exact aS. exact (const a0). *)
(* Defined. *)

(* Definition fin_ind {n : nat} (P : [n] -> Type) (p0 : P fin_zero) (pS : forall i : (Fin n), P (fin_succ i)) : *)
(*   forall i : [n], P i. *)
(* Proof. *)
(*   intros [|[]]. exact pS. exact p0. *)
(* Defined. *)

(* (* The inclution [Fin n -> Fin (n+1) *) *)
(* Definition include_1 {n : nat} : Fin n -> [n]. *)
(* Proof. *)
(*   induction n. *)
(*   (* Trivial when n is zero *) *)
(*   contradiction. *)
(*   srapply @fin_rec. *)
(*   (* 0 goes to 0 *) exact fin_zero. *)
(*   intro i. simpl. apply (@fin_succ (n.+1)). exact (IHn i). *)
(* Defined. *)
  
  
(*   (* apply fin_rec. *) *)
(*   (* (* Zero goes to zero *) *) *)
(*   (* - exact fin_zero. *) *)
(*   (* (* [i+1] goes to [fin_succ i] *) *) *)
(*   (* - refine (fin_succ o IHn). *) *)
(* (* Defined. *) *)



(* (* I think I order Fin the other way than in the HoTT library. . . *) *)
(* Fixpoint nat_fin' {n : nat} : Fin n -> nat. *)
(* Proof. induction n. contradiction. *)
(*   apply (fin_rec nat O). *)
(*   exact (S o (nat_fin' n)). *)
(* Defined. *)

(* (* Check that the order is right *) *)
(* Definition zerotozero {n : nat} : nat_fin' (@fin_zero n) = O := idpath. *)
(* Lemma i_to_i {n : nat} (i : Fin n) : @nat_fin' (n.+1) (include_1 i) = @nat_fin' n i. *)
(* Proof. *)
(*   induction n. contradiction. *)
(*   revert i. apply fin_ind. *)
(*   - reflexivity. *)
(*   - intro i. simpl. rewrite <- IHn. reflexivity. *)
(* Qed. *)


(* (* The order is reverse from nat_fin defined in the HoTT library *) *)
(* Definition zerotozero2 {n : nat} : not (nat_fin' (@fin_zero (n.+1)) = nat_fin (n.+2) fin_zero). *)
(*   simpl. unfold const. Abort. *)


(* Definition Fin_resp_sum (m n : nat) : Fin (m + n) <~> (Fin m) + (Fin n). *)
(* Proof. *)
(*   induction m. *)
(*   - (*m is 0*) *)
(*     apply equiv_inverse. *)
(*     apply (sum_empty_l (Fin n)). *)
(*   - simpl. *)
(*     refine (_ oE (equiv_functor_sum_r IHm)). *)
(*     refine ((equiv_sum_assoc (Fin m) Unit (Fin n))^-1 oE _ oE equiv_sum_assoc (Fin m) (Fin n) Unit). *)
(*     apply equiv_functor_sum_l. *)
(*     apply equiv_sum_symm. *)
(* Defined. *)

(* Definition decompose_fin {n : nat} (i : Fin n) : *)
(*   Fin n <~>  Fin (nat_minus (nat_fin' i).+1 n) + Unit + Fin (nat_fin' i). *)
(* Proof. *)
(*   induction n. contradiction. *)
(*   revert i. *)
(*   srapply @fin_ind. *)
(*   - apply equiv_inverse. apply sum_empty_r.     *)
(*   - intro i. simpl. simpl in IHn. *)
(*     refine (_ oE equiv_functor_sum_r (IHn i)). *)
(*     apply equiv_sum_assoc. *)
(* Defined. *)

(* Definition iterated_prod (A : Type) (n : nat) : Type. *)
(* Proof. *)
(*   induction n. *)
(*   (* A^0 is Unit *) *)
(*   - exact Unit. *)
(*   (* A^(n+1) is A*(A^n) *) *)
(*   - exact (prod A IHn). *)
(* Defined. *)

(* Notation "A *^ n" := (iterated_prod A n) (at level 20). *)

(* (* Decompose the iterated product, isolating the i'th component. *) *)
(* Definition decompose_iterated_prod {A : Type} {n : nat} (i : Fin n) : *)
(*   (A *^ n) <~> (A*^(nat_fin' i) * A * A*^(nat_minus (nat_fin' i).+1) n). *)
(* Proof. *)
(*   induction n. contradiction. *)
(*   revert i. srapply @fin_ind; simpl. *)
(*   - transitivity (Unit * (A * A *^ n)). *)
(*       apply equiv_inverse. apply prod_unit_l. *)
(*       apply equiv_prod_assoc. *)
(*   - intro i. *)
(*     refine (_ oE equiv_functor_prod_l (IHn i)). *)
(*     refine (_ oE equiv_prod_assoc A _ _). *)
(*     apply equiv_functor_prod_r. *)
(*     apply equiv_prod_assoc. *)
(* Defined. *)

(* (* Project down to the i'th component *) *)
(* Definition projection_iterated_prod {A : Type} {n : nat} (i : Fin n) : A*^n -> A. *)
(* Proof. *)
(*   refine (_ o (@decompose_iterated_prod A n i)). *)
(*   intros [[a0 a] a1]. exact a. *)
(* Defined. *)

(* (* Project away from the i'th component *) *)
(* Fixpoint face_iterated_prod {A: Type} {n : nat} (i : [n]) : A*^(n.+1) -> A*^n. *)
(* Proof. *)
(* (*   revert i. srapply @fin_rec. *) *)
(* (*   (* i=0 *) *) *)
(* (*   - intros [a0 a]. exact a. *) *)
(* (*   (* i+1 *) *) *)
(* (*   - induction n. contradiction. *) *)
(* (*     intro i. *) *)
(* (*     intros [a0 a]. exact (a0, face_iterated_prod A n i a). *) *)
(* (* Defined. *) *)
    
(*   induction n. *)
(*   (* n=0 *) *)
(*   - exact (const tt). *)
(*   - simpl. simpl in IHn. *)
(*   revert i. srapply @fin_ind; simpl. *)
(*   (* i=0 *) *)
(*   + apply snd. *)
(*   (* i+1 *) *)
(*   + intro i. *)
(*     intros [a0 a]. *)
(*     exact (a0, IHn i a). *)
(* Defined. *)

(* (* (* The 0'th face projects away from the 0'th component *) *) *)
(* (* Definition face_iterated_prod_0 {A:Type} {n : nat} (a0 : A) (a : A*^n) : *) *)
(* (*   face_iterated_prod fin_zero (a0, a) = a. *) *)
(* (* Proof. *) *)
(* (*   induction n. *) *)
(* (*   (* n=0 *) *) *)
(* (*   - apply contr_unit. *) *)
(* (*   (* n+1 *) *) *)
(* (*   - reflexivity. *) *)
(* (* Defined. *) *)

(* (* (* I can't manage to make simpl do this reduction alone. . . *) *) *)
(* (* Definition face_iterated_prod_Si {A : Type} {n : nat} (a0 : A) (a : A*^n.+1) (i : [n]) : *) *)
(* (*   face_iterated_prod (fin_succ i) (a0, a) = (a0, face_iterated_prod i a) := idpath. *) *)

(* (* Definition a_simplicial_identity_prod {A : Type} {n : nat} (i : [n]) (a : A*^n.+2): *) *)
(* (*   (face_iterated_prod i o face_iterated_prod (fin_succ i)) a = *) *)
(* (*   (face_iterated_prod i o face_iterated_prod (include_1 i)) a. *) *)
(* (* Proof. *) *)
(* (*   destruct a as [a0 [a1 a]]. *) *)
(* (*   induction n. *) *)
(* (*   (* n=0 *) *) *)
(* (*   - reflexivity. *) *)
(* (*   (* n+1 *) *) *)
(* (*   - revert i. srapply @fin_ind. *) *)
(* (*     (* i=0 *) *) *)
(* (*     + reflexivity. *) *)
(* (*     + srapply @fin_ind. *) *)
(* (*       simpl. *) *)
(* (*     +  *) *)
(* (*     + induction n. simpl. *) *)

(* (*     induction n. *) *)
(* (*     (* n=1 *) *) *)
(* (*     + revert i. srapply @fin_ind.  *) *)
(* (*     (* i=0 *) *) *)
(* (*       * reflexivity. *) *)
(* (*       (* i+1 *) *) *)
(* (*       * reflexivity. *) *)
(* (*     (* n+2 *) *) *)
(* (*     + revert i. *) *)
(* (*       srapply @fin_ind. *) *)
(* (*     (* i=0 *) reflexivity. *) *)
(* (*     (* i+1 *) srapply @fin_ind. *) *)
(* (*     (* i=1 *) reflexivity. *) *)
(* (*     (* i+2 *) destruct a as [a2 [a3 a]]. simpl. *) *)
      
      
(* (*     + srapply @fin_ind. *) *)
(* (*       (* i=1 *) *) *)
(* (*       * simpl. apply path_prod. reflexivity. simpl. rewrite face_iterated_prod_0. reflexivity. *) *)
(* (*       *  *) *)
(* (*         unfold face_iterated_prod. simpl. *) *)

(* (*       intro i. destruct a as [a2 a]. *) *)
(* (*       repeat rewrite face_iterated_prod_Si. simpl. simpl in IHn. *) *)
(* (*       apply path_prod. reflexivity. *) *)
      
      
      
      
(* (*       simpl. *) *)
      
(* (*       unfold face_iterated_prod. simpl. *) *)

  
  
  
    
  



