Require Import HoTT.

(*Strangely, I cannot find any proofs of nat being associative*)
Local Open Scope nat_scope.
Definition plus_assoc : forall j k l : nat, j + (k + l) = (j + k) + l. 
  intros j k l.
  induction j.
  - exact idpath.
  - exact (ap S IHj).
Defined.


(*Cancellation in nat*)
Open Scope nat_scope.
(* Subtraction of natural numbers. *)
  (* Is given by [m,n => -m + n] *)
(* This is the same as the already defined [minus], but the below lemma is much easier to prove *)
Fixpoint nat_minus (m n : nat) : nat :=
  match m with
      |0 => n (*-0 + m := m*)
      |m.+1 => match n with
                  |0 => 0 (*-(m+1)+0 = 0*)
                  |n.+1 => nat_minus m n (*- m+1 + n+1= -m + n*)
              end
  end.

(* Just to show that this is the same as the old minus. *)
Lemma nat_minus_is_minus (m n : nat) : nat_minus m n = minus n m.
Proof.
  revert n.
  induction m.
  - induction n; reflexivity.
  - induction n. reflexivity.
    simpl. apply IHm.
Defined.

Definition nat_plus_minus (m n : nat) : nat_minus m (m + n) = n.
Proof.
  induction m. 
  - reflexivity.
  - exact IHm.
Defined.

Definition nat_plus_cancelL (l m n : nat) : l + m = l + n -> m = n.
Proof.
  intro p.
  refine ((nat_plus_minus l m)^ @ _ @ nat_plus_minus l n).
  apply (ap (nat_minus l) p).
Defined.

(* Definition not_leq_is_gt (i j : nat) : not (i <= j) <~> i > j. *)
(* Proof. *)
(*   unfold not. unfold leq. unfold gt. *)
(*   simpl. *)
(*   induction i. simpl. *)

(* Definition split_nat (i : nat) : *)
(*   nat <~> {j : nat & j <= i} + {j : nat & j > i}. *)
(* Proof. *)
(*   srapply @equiv_adjointify. *)
(*   - intro k. induction k. *)
(*     (* k = 0 *) *)
(*     + apply inl. *)
(*       exists 0. *)
(*       apply leq0n. *)
(*     (* k+1 *) *)
(*     +  *)

Close Scope nat_scope.
