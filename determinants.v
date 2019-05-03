Require Import HoTT.


(* Example test ( A : Type) (H : Decidable A) : ~ ~ A -> A. *)
(* intros. unfold not in X. *)
(* destruct (dec A). *)
(* exact a. *)
(* destruct (X n). *)
Require Import finite_lemmas.
Require Import monoids_and_groups.
  

Section Determinant.
  Open Scope monoid_scope.
  (* the determinant of the map swapping k and the last element of Fin n *)
  Definition det_twist (n : nat) (k : Fin n) : group_2.
  Proof.
    induction n.
    - exact ι.
    - destruct k as [k | []].
      + exact (twist_2 (IHn k)).
      + exact ι.
  Defined.

  (* Arguments det_twist !n k. *)
  
  Definition determinant (n : nat) :
    (Fin n <~> Fin n) -> group_2.
  Proof.
    intro e.
    (* For n = 0, the determinant is trivial *)
    induction n. { exact ι. }
    
    exact (mon_mult (det_twist n.+1 (e (inr tt))) (IHn (equiv_restrict e))).
  Defined.

Definition det_plus_1 {n : nat} (e : Fin n <~> Fin n) :
  determinant n.+1 (e +E 1) = determinant n e.
Proof.
  simpl. refine (id_2_is_id _ @ _).
  apply (ap (determinant n)).
  apply path_equiv. apply path_arrow.
  apply equiv_restrict_plus1.
Defined. 


(* Putting this instead fails. . .   *)
(*     determinant n.+1 (e +E 1) = determinant n e. *)
  


  (* Definition fin_equiv_inv_plus1 {m n : nat} (e : Fin m <~> Fin n) : *)
  (*   (equiv_fin_equiv m n)^-1 (e +E 1) = (inr tt, e). *)
  (* Proof. *)
  (*   apply (equiv_inj (fin_equiv' m n)). *)
  (*   refine (eisretr (fin_equiv' m n) (e +E 1) @ _). *)
  (*   unfold fin_equiv'. unfold fin_equiv. simpl. *)
  (*   destruct n; apply inverse; *)
  (*     apply ecompose_1e. *)
  (* Defined. *)

  Definition det_compose (n : nat) (e1 e2 : Fin n <~> Fin n) :
    determinant n (e2 oE e1) = mon_mult (determinant n e2)(determinant n e1).
  Proof.
    induction n.
    - simpl. reflexivity.
    - hnf. simpl.
      destruct (e1 (inr tt)) as [y | []].
      + admit.
      + simpl. rewrite id_2_is_id.
        destruct (e2 (inr tt)) as [y | []].
        * 

  (*     admit. *)
  (*     Admitted. *)
    
    

  (* Lemma fin_sum (m n : nat) : Fin (m + n)%nat <~>  (Fin n) + (Fin m). *)
  (* Proof. *)
  (*   induction m; simpl. *)
  (*   - apply equiv_inverse. apply sum_empty_r. *)
  (*   - refine (equiv_sum_assoc _ _ _ oE (IHm +E 1)). *)
  (* Defined. *)

  Definition block_sum_lid (m : nat) {n : nat} (e : Fin n <~> Fin n) :
    Fin (m + n) <~> Fin (m + n).
  Proof.
    induction m; simpl.
    - exact e.
    - exact (equiv_functor_sum' IHm 1).
  Defined.

  (* Definition block_sum_lid_1 (m : nat) {n : nat} (e : Fin n <~> Fin n) : *)
  (*   block_sum_lid m.+1 e = (block_sum_lid m e) +E 1 := idpath.     *)

  Definition det_plus_id {m n : nat} (e : Fin n <~> Fin n) :
    determinant (m+n) (block_sum_lid m e) = determinant n e.
  Proof.
    revert n e.
    induction m.
    - intros n e. reflexivity.
    - intros n e. simpl.
      refine (id_2_is_id _ @ _).
      refine (_ @ IHm _ _).
      apply (ap (determinant (m + n))).
      apply path_equiv. apply path_arrow.
      apply equiv_restrict_plus1.  
  Qed.

  

(* I think the following is in finite_lemmas...*)


(* (* Comparing not_leq to gt *) *)
(* Section Inequalities. *)
  
(*   (* For two natural numbers, one is either less than or equal the other, or it is greater. *) *)
(*   Definition leq_or_gt (i j : nat) : (i <= j) + (i > j). *)
(*   Proof. *)
(*     revert j. induction i; intro j. *)
(*     (* 0 <= j *) *)
(*     - exact (inl tt). *)
(*     - destruct j. *)
(*       (* 0 < i+1 *) *)
(*       + exact (inr tt). *)
(*       (* (i < j+1) + (j.+1 < i + 1) <-> (i <= j) + (j < i) *) *)
(*       + apply IHi. *)
(*   Defined. *)
 

(*   Definition leq_succ (n : nat) : n <= n.+1. *)
(*   Proof. *)
(*     induction n. reflexivity. apply IHn. *)
(*   Defined. *)

(*   (* Lemma leq_refl_code (i j : nat) : i =n j -> i <= j. *) *)
(*   (* Proof. *) *)
(*   (*   intro H. *) *)
(*   (*   destruct (path_nat H). apply leq_refl. *) *)
(*   (* Qed. *) *)
  
(*   Definition neq_succ (n : nat) : not (n =n n.+1). *)
(*   Proof. *)
(*     induction n. *)
(*     - exact idmap. *)
(*     - exact IHn. *)
(*   Defined. *)

(*   Definition leq0 {n : nat} : n <= 0 -> n =n 0. *)
(*   Proof. *)
(*     induction n; exact idmap. *)
(*   Defined. *)

(*     (*  *) *)
(*   Definition leq_geq_to_eq (i j : nat) : (i <= j) * (j <= i) -> i =n j. *)
(*   Proof. *)
(*     intros [i_lt_j  j_lt_i]. *)
(*     revert j_lt_i. revert i_lt_j. revert i. *)
(*     induction j. *)
(*     - intros. exact (leq0 i_lt_j). *)
(*     - destruct i. *)
(*       + intros. destruct j_lt_i. *)
(*       + simpl. intros. *)
(*         apply (IHj _ i_lt_j j_lt_i). *)
(*   Defined. *)

(*   (* Definition leq_to_lt_plus_eq (i j : nat) : i <= j -> (i < j) + (i = j). *) *)
(*   (* Proof. *) *)
(*   (*   intro i_leq_j. *) *)
(*   (*   destruct (dec (i = j)). *) *)
(*   (*   - exact (inr p). *) *)
(*   (*   - apply inl. *) *)
(*   (*     induction j. *) *)
(*   (*     + simpl. rewrite (path_nat (leq0 i i_leq_j)) in n. apply n. reflexivity. *) *)
(*   (*     + destruct i. exact tt. *) *)
(*   (*       srapply (@leq_transd i.+2 j j.+1). *) *)
(*   (*       * apply IHj. *) *)
(*   (*         admit. *) *)
           
        
(*   (*       simpl. *) *)

        
(*   (*       i. *) *)
(*   (*     + simpl. *) *)
    
(*   (*   destruct j. *) *)
(*   (*   apply inr. apply path_nat. apply (leq0  i (i_leq_j)). *) *)
(*   (*   destruct i. *) *)
(*   (*   - simpl. *) *)
    
(*   (*   apply inl. change (i < j.+1) with (i <= j). *) *)
(*   (*   apply (leq_transd *) *)
    
    

(*   (* Definition nlt_n0 (n : nat) : ~(n < 0) := idmap. *) *)
  
(*   Definition gt_to_notleq (i j : nat) : j > i -> ~(j <= i). *)
(*   Proof. *)
(*     intro i_lt_j. *)
(*     intro j_leq_i. *)
(*     apply (neq_succ i). *)
(*     apply (leq_antisymd (leq_succ i)). *)
(*     apply (leq_transd i_lt_j j_leq_i). *)
(*     (* set (Si_leq_i := leq_transd i_lt_j j_leq_i). *) *)
(*     (* set (Si_eq_i := leq_antisymd (leq_succ i) Si_leq_i). *) *)
(*     (* apply (neq_succ i Si_eq_i). *) *)
(*     (* induction i. *) *)
(*     (* exact Si_eq_i. *) *)
(*   Defined. *)

(*   (* Lemma notleq_to_gt (i j : nat) : ~(j <= i) -> j > i. *) *)
(*   (* Proof. *) *)
(*   (*   intro j_nleq_i. *) *)
(*   (*   induction j. *) *)
(*   (*   - apply j_nleq_i. *) *)
(*   (*     apply leq0n. *) *)
(*   (*   - change (i < j.+1) with (i <= j). *) *)
(*   (*     destruct (dec (i =n j)). *) *)
(*   (*     (* i = j *) *) *)
(*   (*     + destruct (path_nat t). apply leq_refl. *) *)
(*   (*     +  *) *)

(*   (*     induction i. *) *)
(*   (*     + exact tt. *) *)
(*   (*     +  *) *)
    
(*   (*   induction i, j. *) *)
(*   (*   - apply j_nleq_i. exact tt. *) *)
(*   (*   - exact tt. *) *)
(*   (*   - simpl. simpl in IHi. simpl in j_nleq_i. apply IHi. exact j_nleq_i. *) *)
(*   (*   - change (i.+1 < j.+1) with (i < j). *) *)
(*   (*     change (j < i.+1) with (j <= i) in j_nleq_i. *) *)
(*   (*     change (i < j.+1) with (i <= j) in IHi. *) *)
      
    
(*   (*   destruct (dec (~ (j <= i))). *) *)
(*   (*   - set (f := j_nleq_i t). destruct f. *) *)
(*   (*   -  *) *)
  
(*   (* If i <= j, then j is the sum of i and some natural number *) *)
(*   Definition leq_to_sum {i j : nat} : i <= j -> {k : nat | j = i + k}%nat. *)
(*   Proof. *)
(*     revert j. induction i; intro j. *)
(*     - intro.  *)
(*       exists j. reflexivity. *)
(*     - destruct j. intros []. *)
(*       simpl. change (i < j.+1) with (i <= j). *)
(*       intro i_leq_j. *)
(*       apply (functor_sigma (A := nat) idmap (fun _ => ap S)). *)
(*       apply (IHi j i_leq_j). *)
(*       (* exists (IHi j i_leq_j).1. *) *)
(*       (* apply (ap S). *) *)
(*       (* apply (IHi j i_leq_j).2. *) *)
(*   Defined. *)

(*   (* If j > i, then j is a successor *) *)
(*   Definition gt_is_succ {i j : nat} : i < j -> {k : nat | j = k.+1}. *)
(*   Proof. *)
(*     intro i_lt_j. *)
(*     destruct (leq_to_sum i_lt_j) as [k H]. *)
(*     exact (i+k; H)%nat. *)
(*   Defined. *)
    
(* End Inequalities. *)

(* Notation "[ n ]" := {m : nat | m <= n}. *)
(* Section Cosimplicial_maps. *)
  
(*   (* Definition pFin (n : nat) := { m : nat | m <= n }. *) *)
(*   (* Definition pFin_include {n : nat} : pFin n -> nat := pr1. *) *)
(*   (* Coercion pFin_include : pFin >-> nat. *) *)

(*   (* The i'th coface *) *)
(*   Definition coface {n : nat} (i : nat) (i_leq_n : i <= n) : [n] -> [n.+1]. *)
(*   Proof. *)
(*     intros [j j_leq_n]. *)
(*     destruct (leq_or_gt i j).   (* destruct (dec (i <= j)).      *) *)
(*     (* i <= j *) *)
(*     - exists j. *)
(*       apply (leq_trans _ n _ j_leq_n). apply leq_succ. *)
(*     (* j > i *) *)
(*     - exists j.+1. *)
(*       apply j_leq_n. *)
(*   Defined. *)

(*   (* The i'th codegeneracy *) *)
(*   (* s_i j = *)
(*           j, if j <= i *)
(*           j-1, if j > i  *) *)
(*   Definition codegen {n : nat} (i : nat) (i_leq_n : i <= n) : [n.+1] -> [n]. *)
(*   Proof. *)
(*     intros [j j_leq_Sn]. *)
(*     destruct (leq_or_gt j i). *)
(*     (* j <= i *) *)
(*     - exists j. *)
(*       apply (leq_trans _ i _ t i_leq_n). *)
(*     (* j > i *) *)
(*     - destruct (gt_is_succ t) as [k H]. (* j is a successor *) *)
(*       exists k. *)
(*       change (k <= n) with (k.+1 <= n.+1). *)
(*       apply (@leq_transd k.+1 j n.+1)%nat. *)
(*       rewrite H. apply leq_refl. *)
(*       apply j_leq_Sn. *)
(*   Defined. *)

(* End Cosimplicial_maps. *)


    





    
  
  