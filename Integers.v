Load monoids_and_groups.
Open Scope nat_scope.

(* The inclusion of natural numbers in integers *)
Definition nat_to_int : nat -> Int.
Proof.
  intro n.
  destruct n.
  - exact Int.zero.
  - apply pos.
    induction n.
    + exact Int.one.
    + exact (Int.succ_pos IHn).
Defined.

(* The inclusion preserves sum *)
Definition nat_to_int_succ : forall m : nat, nat_to_int (m.+1) = succ_int (nat_to_int m).
Proof.
  destruct m; reflexivity.
Defined.

(* succ_int and pred_int are inverses *)
Definition Int_succ_pred : forall a : Int, succ_int (pred_int a) = a.
Proof.
  induction a; try induction p; try reflexivity.
Defined.

Definition Int_pred_succ : forall a : Int, pred_int (succ_int a) = a.
Proof.
  destruct a; try destruct p; try reflexivity.
Defined.

(* Multiplying with -1 *)
Definition Int_minus (a : Int) : Int :=
  match a with
  |neg p => pos p
  |Int.zero => Int.zero
  |pos p => neg p
  end.

(* Int_minus is its own inverse *)
Definition Int_minus_minus (a : Int) : Int_minus (Int_minus a) = a.
Proof.
  destruct a; reflexivity.
Defined.

(* Successor of minus is minus of predecessor *)
Definition Int_succ_minus (a : Int) : succ_int (Int_minus a) = Int_minus (pred_int a).
Proof.
  destruct a; try destruct p; try reflexivity.
Defined.

(* (* Add a positive integer to an integer *) *)
(* Fixpoint Int_sum_pos (p : Pos) : Int -> Int. *)
(*   destruct p. *)
(*   - exact succ_int. *)
(*   - exact (succ_int o (Int_sum_pos p)). *)
(* Defined. *)

(* Sum of two integers *)
Definition Int_sum (a : Int) : Int -> Int.
Proof.
  destruct a.
  (* a is negative *)
  - induction p.
    + exact pred_int.           (* -1 + n *)
    + exact (pred_int o IHp). (* (-1-p) + n = -1 + (-p + n) *)
  (* a is zero *)
  - exact idmap.
  (* a is positive *)
  - induction p.
    + exact succ_int.           (* 1+n *)
    + exact (succ_int o IHp). (* (1+p) + n = 1 + (p+n) *)
Defined.

(* Sum of two positive integers *)
Fixpoint pos_sum (p : Pos) : Pos -> Pos.
Proof.
  destruct p.
  + exact succ_pos.
  + exact (succ_pos o (pos_sum p)).
Defined.

(* Sum of positives is positive *)
Lemma Int_sum_pos (p q : Pos) : Int_sum (pos p) (pos q) = pos (pos_sum p q).
Proof.
  induction p.
  - reflexivity.
  - change (Int_sum (pos (succ_pos p)) (pos q)) with (succ_int (Int_sum (pos p) (pos q))).
    rewrite IHp. reflexivity.
Qed.

(* Sum of negatives are negative *)
Lemma int_sum_neg (p q : Pos) : Int_sum (neg p) (neg q) = neg (pos_sum p q).
Proof.
  induction p.
  - reflexivity.
  - change (Int_sum (neg (succ_pos p)) (neg q)) with (pred_int (Int_sum (neg p) (neg q))).
    rewrite IHp. reflexivity.
Qed.  

(* Sum preserves mines *)
Lemma Int_sum_minus (a b: Int) : Int_sum (Int_minus a) (Int_minus b) = Int_minus (Int_sum a b).
Proof.
  destruct a; destruct b; try reflexivity.
  - rewrite int_sum_neg. apply Int_sum_pos.
  - 
    + apply Int_succ_minus.
    + intro b. admit. 
  - reflexivity.
  - 
  
  simpl.
  
  unfold Int_minus. simpl.

  simpl.
  destruct a,b; try reflexivity. simpl.
  

(* Sum preserves successor (in first variable) *)
Definition Int_sum_succ : forall a b : Int, Int_sum (succ_int a) b = succ_int (Int_sum a b).
Proof. 
  intros a b.
  destruct a.
  (* a is negative *)
  - destruct p.
    + simpl. apply inverse. apply Int_succ_pred.
    + (* change (neg (succ_pos p)) with (pred_int (neg p)). *)
      rewrite (Int_succ_pred (neg p)).
      

    (* rewrite Int_succ_minus. rewrite Int_pred_succ. rewrite Int_minus_minus. reflexivity. *)
    (* simpl. rewrite Int_succ_minus. rewrite Int_pred_succ. reflexivity. *) admit.
  (* a is zero *)
  - reflexivity.
  - reflexivity.
Qed.

(* The inclusion [nat -> Integer] preserves sum *)
Definition ishom_nat_to_int : forall m n : nat, nat_to_int (m + n) = Int_sum (nat_to_int m) (nat_to_int n).
Proof.
  intros m n.
  induction m; try reflexivity.
  rewrite nat_to_int_succ. transitivity (succ_int (nat_to_int (m+n))).
  { apply nat_to_int_succ. }
  rewrite Int_sum_succ. exact (ap succ_int IHm).
Qed.

(* Sum of integers is associative *)
Definition Int_sum_assoc : associative Int_sum.
Proof.
  intros a b c.
  destruct a.
  - simpl. admit.               (* a is negative *)
  - reflexivity.                (* a is zero *)
  - simpl. induction p.
    simpl. apply inverse. apply Int_sum_succ.
    simpl.
    

    induction a.
  (* a is negative *)
  - admit. (* induction p. *)
  (* (* a is -1 *) *)
  (* + simpl. *)
  (*   induction b as [q | q | q]; try reflexivity. *)
  (*   (* b is positive *) *)
  (*   * induction q. *)
  (*     (* b is 1 *) *)
  (*     { simpl. induction c; try reflexivity. induction p; reflexivity. } *)
  (*     (* b is q+1 *) *)
  (*     { simpl.  } *)
    
    
  (* a is zero *)
  - reflexivity.
  (* a is positive *)
  - induction p.
    simpl.  Admitted.




