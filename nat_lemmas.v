Require Import HoTT.

(*Strangely, I cannot find any proofs of nat being associative*)
Local Open Scope nat_scope.
Definition plus_assoc : forall j k l : nat, (j + k) + l = j + (k + l). 
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

(* Comparing not_leq to gt *)
Section Inequalities.
  Local Open Scope nat.
  (* For two natural numbers, one is either less than or equal the other, or it is greater. *)
  Definition leq_or_gt (i j : nat) : (i <= j) + (i > j).
  Proof.
    revert j. induction i; intro j.
    (* 0 <= j *)
    - exact (inl tt).
    - destruct j.
      (* 0 < i+1 *)
      + exact (inr tt).
      (* (i < j+1) + (j.+1 < i + 1) <-> (i <= j) + (j < i) *)
      + apply IHi.
  Defined.
 

  Definition leq_succ (n : nat) : n <= n.+1.
  Proof.
    induction n. reflexivity. apply IHn.
  Defined.

  (* Lemma leq_refl_code (i j : nat) : i =n j -> i <= j. *)
  (* Proof. *)
  (*   intro H. *)
  (*   destruct (path_nat H). apply leq_refl. *)
  (* Qed. *)
  
  Definition neq_succ (n : nat) : not (n =n n.+1).
  Proof.
    induction n.
    - exact idmap.
    - exact IHn.
  Defined.

  Definition leq0 {n : nat} : n <= 0 -> n =n 0.
  Proof.
    induction n; exact idmap.
  Defined.

  (* if both i<=j and j<=i, then they are equal *)
  Definition leq_geq_to_eq (i j : nat) : (i <= j) -> (j <= i) -> i =n j.
  Proof.
    revert i.
    induction j; intros i i_leq_j j_leq_i.
    - exact (leq0 i_leq_j).
    - destruct i.
      + intros. destruct j_leq_i.
      + simpl. intros.
        apply (IHj _ i_leq_j j_leq_i).
  Defined.

  (* If i <= n, then i < n or i = n+1 *)
  Definition lt_or_eq (i n : nat) : i <= n -> (i < n) + (i = n).
  Proof.
    intro i_leq_n.
    destruct (leq_or_gt n i) as [n_leq_i | n_gt_i].
    - apply inr. apply path_nat. exact (leq_geq_to_eq _  _ i_leq_n n_leq_i).
    - exact (inl n_gt_i).
  Defined.

  Definition lt_or_eq_or_gt (i n : nat) :
    (i < n) + (i = n) + (i > n).
  Proof.
    destruct (leq_or_gt i n) as [leq | gt].
    - apply inl. apply (lt_or_eq i n leq).
    - exact (inr gt).
  Defined.
    

  (* Definition leq_to_lt_plus_eq (i j : nat) : i <= j -> (i < j) + (i = j). *)
  (* Proof. *)
  (*   intro i_leq_j. *)
  (*   destruct (dec (i = j)). *)
  (*   - exact (inr p). *)
  (*   - apply inl. *)
  (*     induction j. *)
  (*     + simpl. rewrite (path_nat (leq0 i i_leq_j)) in n. apply n. reflexivity. *)
  (*     + destruct i. exact tt. *)
  (*       srapply (@leq_transd i.+2 j j.+1). *)
  (*       * apply IHj. *)
  (*         admit. *)
           
        
  (*       simpl. *)

        
  (*       i. *)
  (*     + simpl. *)
    
  (*   destruct j. *)
  (*   apply inr. apply path_nat. apply (leq0  i (i_leq_j)). *)
  (*   destruct i. *)
  (*   - simpl. *)
    
  (*   apply inl. change (i < j.+1) with (i <= j). *)
  (*   apply (leq_transd *)
    
    

  (* Definition nlt_n0 (n : nat) : ~(n < 0) := idmap. *)
  
  Definition gt_to_notleq (i j : nat) : j > i -> ~(j <= i).
  Proof.
    intro i_lt_j.
    intro j_leq_i.
    apply (neq_succ i).
    apply (leq_antisymd (leq_succ i)).
    apply (leq_transd i_lt_j j_leq_i).
    (* set (Si_leq_i := leq_transd i_lt_j j_leq_i). *)
    (* set (Si_eq_i := leq_antisymd (leq_succ i) Si_leq_i). *)
    (* apply (neq_succ i Si_eq_i). *)
    (* induction i. *)
    (* exact Si_eq_i. *)
  Defined.

  Definition not_i_lt_i (i : nat) : ~(i < i).
  Proof.
    unfold not.
    induction i. exact idmap.
    exact IHi.
  Defined.
  
  (* Lemma notleq_to_gt (i j : nat) : ~(j <= i) -> j > i. *)
  (* Proof. *)
  (*   intro j_nleq_i. *)
  (*   induction j. *)
  (*   - apply j_nleq_i. *)
  (*     apply leq0n. *)
  (*   - change (i < j.+1) with (i <= j). *)
  (*     destruct (dec (i =n j)). *)
  (*     (* i = j *) *)
  (*     + destruct (path_nat t). apply leq_refl. *)
  (*     +  *)

  (*     induction i. *)
  (*     + exact tt. *)
  (*     +  *)
    
  (*   induction i, j. *)
  (*   - apply j_nleq_i. exact tt. *)
  (*   - exact tt. *)
  (*   - simpl. simpl in IHi. simpl in j_nleq_i. apply IHi. exact j_nleq_i. *)
  (*   - change (i.+1 < j.+1) with (i < j). *)
  (*     change (j < i.+1) with (j <= i) in j_nleq_i. *)
  (*     change (i < j.+1) with (i <= j) in IHi. *)
      
    
  (*   destruct (dec (~ (j <= i))). *)
  (*   - set (f := j_nleq_i t). destruct f. *)
  (*   -  *)
  
  (* If i <= j, then j is the sum of i and some natural number *)
  Definition leq_to_sum {i j : nat} : i <= j -> {k : nat | j = i + k}%nat.
  Proof.
    revert j. induction i; intro j.
    - intro. 
      exists j. reflexivity.
    - destruct j. intros [].
      simpl. change (i < j.+1) with (i <= j).
      intro i_leq_j.
      apply (functor_sigma (A := nat) idmap (fun _ => ap S)).
      apply (IHi j i_leq_j).
      (* exists (IHi j i_leq_j).1. *)
      (* apply (ap S). *)
      (* apply (IHi j i_leq_j).2. *)
  Defined.

  (* If j > i, then j is a successor *)
  Definition gt_is_succ {i j : nat} : i < j -> {k : nat | j = k.+1}.
  Proof.
    intro i_lt_j.
    destruct (leq_to_sum i_lt_j) as [k H].
    exact (i+k; H)%nat.
  Defined.
    
End Inequalities.


