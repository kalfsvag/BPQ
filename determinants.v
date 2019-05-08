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

  (* Fixpoint det_twist {n : nat} (k : Fin n) {struct n} : group_2. *)
  (* Proof. *)
  (*   destruct n. {destruct k. } *)
  (*   destruct k as [k | []]. *)
  (*   - exact (twist_2 (det_twist n k)). *)
  (*   - exact ι. *)
  (* Defined. *)

  Definition swap_last {n : nat} (e : Fin n.+1 <~> Fin n.+1) := fin_transpose (e (inr tt)) (inr tt).

  Arguments equiv_sum_assoc : simpl nomatch.
  
  Definition swap_last_blocksum {m n : nat}
             (e1 : Fin m.+1 <~> Fin m.+1)
             (e2 : Fin n <~> Fin n) :
    swap_last (block_sum e1 e2) ==
    block_sum (swap_last e1) equiv_idmap.
  Proof.
    unfold swap_last.
    change
      ((block_sum e1 e2) (inr tt))
      with
      ((fin_resp_sum m.+1 n)^-1 (inr (e1 (inr tt)))).
    apply fin_transpose_eta.
    - unfold block_sum.
      ev_equiv.
      rewrite (eisretr (fin_resp_sum m.+1 n)).
      change
        ((1 +E fin_transpose (e1 (inr tt)) (inr tt)) (inr (e1 (inr tt))))
      with 
        (inr (Fin n) (fin_transpose (e1 (inr tt)) (inr tt) (e1 (inr tt)))).
      rewrite (fin_transpose_beta_l).
      reflexivity.
    - unfold block_sum. ev_equiv.
      apply (ap (fin_resp_sum m.+1 n)^-1).
      change
        ((fin_resp_sum m.+1 n) (inr tt))
        with
        (inr (Fin n) (inr (Fin m) tt)).
      change
        ((1 +E fin_transpose (e1 (inr tt)) (inr tt)) (inr (inr tt)))
        with
        (inr (Fin n) (fin_transpose (e1 (inr tt)) (inr tt) (inr tt))).
      apply (ap inr).
      apply (fin_transpose_beta_r).
    - intros i neq_x neq_y.
      unfold block_sum.
      (* change (inr (Fin (m+n)) tt) *)
      (*        with *)
      (*        ((fin_resp_sum m.+1 n)^-1 (inr tt)) in neq_y. *)
      ev_equiv.
      apply (equiv_inj (fin_resp_sum m.+1 n)).
      refine (eisretr (fin_resp_sum m.+1 n) _ @ _).
      recall ((fin_resp_sum m.+1 n) i) as j eqn:p.
      rewrite p.
      destruct j as [j | j].
      + reflexivity.
      + apply (ap inr).
        apply fin_transpose_other.
        * intro q.
          apply neq_x.
          apply (equiv_inj (fin_resp_sum m.+1 n)).
          refine (_ @ ((eisretr (fin_resp_sum m.+1 n)) _)^).
          refine (p @ _).
          exact (ap inr q).
        * intro q.
          apply neq_y.
          apply (equiv_inj (fin_resp_sum m.+1 n)).
          refine (p @ _). simpl.
          apply (ap inr q).
  Qed.


  

  Lemma swap_fix_last {n : nat} (e : Fin n.+1 <~> Fin n.+1) :
    (swap_last e oE e) (inr tt) = inr tt.
  Proof.
    apply fin_transpose_last_with_with.
  Qed.
  
  (* Definition det_twist {n : nat} (k : Fin n) : group_2. *)
  (* Proof. *)
  (*   induction n. *)
  (*   - exact ι. *)
  (*   - destruct k as [k | []]. *)
  (*     + exact (@mon_mult group_2 τ (IHn k)). *)
  (*     + exact ι. *)
  (* Defined. *)

  (* Arguments det_twist  !n !k. *)

  Definition transpose_and_restrict {n : nat} (e : Fin n.+1 <~> Fin n.+1)  :
    Fin n <~> Fin n :=
    (equiv_restrict (swap_last e oE e) (swap_fix_last e)).

  Definition transpose_and_restrict_block_sum {m n : nat}
             (e1 : Fin m.+1 <~> Fin m.+1)
             (e2 : Fin n <~> Fin n) :
    transpose_and_restrict (block_sum e1 e2) == block_sum (transpose_and_restrict e1) e2.
  Proof.
    apply inj_equiv_plus1.
    intro x.
    refine (equiv_restrict_eta _ _ _ @ _).
    refine (swap_last_blocksum e1 e2 _ @ _).
    refine ((block_sum_compose (swap_last e1) e1 equiv_idmap e2 x)^ @ _).
    rewrite (ecompose_1e).
    refine (_ @ (block_sum_plus1 _ _ x)).
    apply (ap (fun g => (block_sum (m := m.+1) g e2) x)).
    apply path_equiv. apply path_arrow.
    intro y.
    apply inverse.
    apply equiv_restrict_eta.
  Defined.
    
    

  (* First determinant of transpositions with the last element *)
  Definition det_transpose {n : nat} (i : Fin n.+1) : group_2.
  Proof.
    destruct i as [i | []].
    (* i is a nontrivial transposition, and has determinant τ *)
    - exact τ.
    (* i is the trivial transposition and has determinent ι *)
    - exact ι.
  Defined.
    
  Fixpoint determinant (n : nat) :
    (Fin n <~> Fin n) -> group_2.
  Proof.
    intro e.
    (* For n = 0, the determinant is trivial *)
    destruct n. { exact ι. }
    exact (det_transpose (e (inr tt)) + determinant n (transpose_and_restrict e)).
  Defined.
 

  
  (* Definition Decidable_fixlast {n : nat} (e : Fin n.+1 <~> Fin n.+1) : Type:= *)
  (*   (e (inr tt) = inr tt) + {x : Fin n & e (inr tt) = inl x}. *)
  
  (* Definition decidable_fixlast {n : nat} (e : Fin n.+1 <~> Fin n.+1) : *)
  (*   (e (inr tt) = inr tt) + {x : Fin n & e (inr tt) = inl x}. *)
  (* Proof. *)
  (*   recall (e (inr tt)) as x eqn:p. *)
  (*   destruct x as [x | []]. *)
  (*   - exact (inr (x; p)). *)
  (*   - exact (inl p). *)
  (* Defined. *)

  (* Definition decidable_fixlast_blocksum {m n : nat} *)
  (*            (e1 : Fin m.+1 <~> Fin m.+1) (e2 : Fin n <~> Fin n) : *)
  (*   Decidable_fixlast e1 -> Decidable_fixlast (block_sum m.+1 n e1 e2). *)
  (* Proof. *)
  (*   apply functor_sum. *)
  (*   - apply (block_sum_fixlast m n e1 e2)^-1. *)
  (*   - srapply @functor_sigma. *)
  (*     + intro i. *)
  (*       apply (fin_resp_sum m n)^-1. exact (inr i). *)
  (*     + intro i. simpl. *)
  (*       intro p. *)
  (*       rewrite p. reflexivity. *)
  (* Defined. *)

  (* Definition decidable_fixlast_blocksum_is_decidable_fixlast {m n : nat} *)
  (*            (e1 : Fin m.+1 <~> Fin m.+1) (e2 : Fin n <~> Fin n) : *)
  (*   decidable_fixlast_blocksum e1 e2 (decidable_fixlast e1) = *)
  (*   decidable_fixlast (block_sum m.+1 n e1 e2). *)
  (* Proof. *)
  (*   destruct (decidable_fixlast e1). *)
  (*   - simpl. *)
      

  (*     destruct (decidable_fixlast (block_sum m.+1 n e1 e2)). *)
  (*     + apply (ap inl). *)
  (*       apply (istrunc_trunctype_type (BuildTruncType 0 (Fin (m.+1 + n)))). *)
  (*     + simpl in p. *)
  (*     apply path_sum.  *)
  (*   -  *)
    
      
      
  (*   decidable_fixlast (block_sum m.+1 n e1 e2) = *)
  (*   functor_sum (block_sum_fixlast m.+1 n e1 e2)^-1 *)
  (*               ( *)

  (* Fixpoint determinant (n : nat) : *)
  (*   (Fin n <~> Fin n) -> group_2. *)
  (* Proof. *)
  (*   intro e. *)
  (*   (* For n = 0, the determinant is trivial *) *)
  (*   destruct n. { exact ι. } *)
  (*   destruct (decidable_fixlast e) as [p | [x p]]. *)
  (*   - exact (determinant n (equiv_restrict e p)). *)
  (*   - exact (τ + determinant n (transpose_and_restrict e)). *)
  (*   (* recall (e (inr tt)) as x eqn:p. *) *)
  (*   (* destruct x as [x | []]. *) *)
  (*   (* (* e does not preserve the last point *) *) *)
  (*   (* - exact (τ + determinant n (transpose_and_restrict e)). *) *)
  (*   (* (* e preserves the last point *) *) *)
  (*   (* - exact (determinant n (equiv_restrict e p)). *) *)
  (* Defined. *)

  (* Definition det_plus_1 {n : nat} (e : Fin n <~> Fin n) : *)
  (*   determinant (n := n.+1) (e +E 1) = determinant e. *)
  (* Proof. *)
  (*   simpl. (* refine (id_2_is_id _ @ _). *)
    apply (ap (determinant (n := n))). *)
  (*   apply path_equiv. apply path_arrow. *)
  (*   apply equiv_restrict_plus1. *)
  (* Defined. *)

  Arguments block_sum : simpl never.
  
  Definition det_block_sum {m n : nat} (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n) :
    determinant (m+n) (block_sum e1 e2) = determinant m e1 + determinant n e2.
  Proof.
    induction m.
    - simpl.
      (* assert (e1 = equiv_idmap). *)
      (* { apply path_equiv. apply path_arrow. intros []. } *)
      (* rewrite X. clear X. *)
      refine (_ @ (id_2_is_id _)^).
      apply (ap (determinant n)). 
      apply path_equiv. reflexivity.
    - change
        (determinant ?k.+1 ?e)
        with
        (det_transpose (e (inr tt)) + determinant k (transpose_and_restrict e)).
      change
        (determinant (?k.+1 + n) ?e)
        with
        (det_transpose (e (inr tt)) + determinant (k+n) (transpose_and_restrict e)).
      rewrite (path_equiv (path_forall _ _ (transpose_and_restrict_block_sum e1 e2))).
      rewrite (IHm (transpose_and_restrict e1)).
      refine (mon_assoc^ @ _).
      apply (ap (fun g => g + determinant m (transpose_and_restrict e1) + determinant n e2)).
      change ((block_sum e1 e2) (inr tt))
             with
             ((fin_resp_sum m.+1 n)^-1 (inr (e1 (inr tt)))).
      destruct (e1 (inr tt)) as [x | []].
      + reflexivity.
      + reflexivity.
  Defined.

  Fixpoint block_sum_lid (m : nat) (n : nat) (e : Fin n <~> Fin n) :
    Fin (m + n) <~> Fin (m + n).
  Proof.
    induction m; simpl.
    - exact e.
    - exact (equiv_functor_sum' (block_sum_lid m n e) 1).
  Defined.

  (* Definition block_sum_lid_1 (m : nat) {n : nat} (e : Fin n <~> Fin n) : *)
  (*   block_sum_lid m.+1 e = (block_sum_lid m e) +E 1 := idpath.     *)

  Definition det_id (m : nat) :
    determinant m (equiv_idmap) = ι.
  Proof.
    induction m.
    - reflexivity.
    - simpl. refine (_ @ IHm).
      apply (ap (determinant m)).
      unfold equiv_restrict.
      apply path_equiv. apply path_arrow.
      intro x.  reflexivity.
  Qed.


  (* Definition det_plus_id {m n : nat} (e : Fin n <~> Fin n) : *)
  (*   determinant (m+n) (block_sum_lid m n e) = determinant n e. *)
  (* Proof. *)
  (*   revert n e. *)
  (*   induction m. *)
  (*   - intros n e. reflexivity. *)
  (*   - intros n e. simpl. *)
  (*     rewrite (path_equiv (path_arrow _ _ (equiv_restrict_plus1 (block_sum_lid m n e)))). *)
  (*     apply IHm. *)
  (*  Qed. *)
      
  (*     refine (id_2_is_id _ @ _). *)
  (*     refine (_ @ IHm _ _). *)
  (*     apply (ap (determinant)). *)
  (*     apply path_equiv. apply path_arrow. *)
  (*     apply equiv_restrict_plus1.   *)
  Qed.

    

  (* Definition block_sum_lid_is_block_sum {m : nat} {n : nat} (e : Fin n <~> Fin n) : *)
  (*   block_sum m n (equiv_idmap (Fin m)) e = block_sum_lid m n e. *)
  (* Proof. *)
  (*   induction m. *)
  (*   - apply path_equiv. apply path_arrow. *)
  (*     intro x. reflexivity. *)
  (*   - change (block_sum_lid m.+1 n e) with ((block_sum_lid m n e) +E (equiv_idmap Unit)). *)
  (*     refine (_ @ (ap (fun f => f +E equiv_idmap) IHm)). *)
  (*     clear IHm. *)
  (*     unfold block_sum. *)
  (*     apply path_equiv. apply path_arrow. *)
  (*     induction n. *)
  (*     + intros [x | []]. *)
  (*       * simpl. *)
  (*     +  *)
  (*     + reflexivity. *)
  (*     + unfold block_sum_lid. simpl. *)
  (*       refine (_ @ IHm x). *)
    
    

  (* Definition det_plus {m n : nat} (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n) : *)
  (*   determinant (block_sum m n e1 e2) = (determinant e1) + (determinant e2). *)
  (* Proof. *)
  (*   revert n e2. *)
  (*   induction m. *)
  (*   - intros.       *)
  (*     transitivity (determinant e2). *)
  (*     + apply (ap determinant). apply path_equiv. reflexivity. *)
  (*     + apply inverse. apply id_2_is_id. *)
  (*   - intros. *)
      

  

  (* Fixpoint det_twist_compose {n : nat} (e : Fin n.+1 <~> Fin n.+1) (x : Fin n.+1) {struct n}: *)
  (*   det_twist (e x) = mon_mult (det_twist (e (inr tt))) (det_twist x). *)
  (* Proof. *)
  (*   destruct x as [x | []]. *)
  (*   -  *)
    
    
  (* Definition det_twist_compose {n : nat} (e1 e2 : Fin n.+1 <~> Fin n.+1) : *)
  (*   det_twist (e2 (e1 (inr tt))) = mon_mult (det_twist (e2 (inr tt))) (det_twist (e1 (inr tt))). *)
  (* Proof.     *)
  (*   generalize (e1 (inr tt)) as x. clear e1. *)
  (*   destruct x as [x | []]. *)
  (*   - recall (e2 (inr tt)) as y eqn:p. rewrite p. *)
  (*     recall (e2 (inl x)) as z eqn:q. rewrite q. *)
  (*     assert (neq : y <> z). *)
  (*     { intro r. *)
  (*       apply (inl_ne_inr x tt). *)
  (*       apply (equiv_inj e2). exact (q @ r^ @ p^). } *)
  (*     clear q. clear p. clear e2. *)
      
  (*     destruct y as [y | []]. *)
  (*     +  *)
      
      
  (*     + destruc *)
    
  (*   recall (e1 (inr tt)) as x eqn:p. rewrite p. *)
  (*   destruct x as [x | []]. *)
  (*   - recall (e2 (inr tt)) as y eqn:q. rewrite q. *)
  (*     destruct y as [y | []]. *)
  (*     + rewrite <- p. rewrite <- q. *)


  (*     destruct (e1 (inr tt)) as [y | []]. *)
  (*     + simpl. *)
  (*   - simpl. *)
  (*     apply inverse. apply (@mon_rid group_2). *)
    

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
    determinant (e2 oE e1) = mon_mult (determinant e2)(determinant e1).
  Proof.
    induction n.
    - simpl. reflexivity.
    - rewrite (@mon_assoc _
                          (det_twist (e2 (inr tt)))
                          (determinant (equiv_restrict e2))
                          (det_twist (e1 (inr tt)) + determinant (equiv_restrict e1))).
      rewrite <- (@mon_assoc _
                             (determinant (equiv_restrict e2))
                             (det_twist (e1 (inr tt)))
                             (determinant (equiv_restrict e1))).
      rewrite (symm_group_2
                 (determinant (equiv_restrict e2))
                 (det_twist (e1 (inr tt)))).
      rewrite (@mon_assoc _
                          (det_twist (e1 (inr tt)))
                          (determinant (equiv_restrict e2))
                          (determinant (equiv_restrict e1))).
      (* refine (_ @ *)
      (*           @mon_assoc _ *)
      (*           (det_twist (e2 (inr tt))) *)
      (*           (det_twist (e1 (inr tt))) *)
      (*           (determinant (equiv_restrict e2) + determinant (equiv_restrict e1))). *)
      (* rewrite <- (IHn (equiv_restrict e1) (equiv_restrict e2)). simpl. *)
      simpl. change mult_2 with (mon_mult (M := group_2)).
      recall (e1 (inr tt)) as x eqn:p. 
      destruct x as [x | []].
      + recall (e2 (e1 (inr tt))) as y eqn:q.
        destruct y as [y | []].
        * admit. (* r(e2 o e1)  = swap (e1 (inr tt), e2 (e1 (inr tt)) o r(e2) o r(e1) *)
        * rewrite q.
          refine (id_2_is_id _ @ _).
          (* ? *) admit.
      + rewrite p. 
        apply (ap (fun g => det_twist (e2 (inr tt)) + g)).
        simpl. refine (_ @ (id_2_is_id _)^).
        refine (_ @ IHn _ _).
        apply (ap determinant). (* should work *)
         
          
          


      simpl.

      rewrite (@mon_assoc _
                          (det_twist (e2 (inr tt)))
                          (determinant (equiv_restrict e2))
                          (det_twist (e1 (inr tt)) + determinant (equiv_restrict e1))).
      rewrite <- (@mon_assoc _
                             (determinant (equiv_restrict e2))
                             (det_twist (e1 (inr tt)))
                             (determinant (equiv_restrict e1))).
      rewrite (symm_group_2
                 (determinant (equiv_restrict e2))
                 (det_twist (e1 (inr tt)))).
      rewrite (@mon_assoc _
                          (det_twist (e1 (inr tt)))
                          (determinant (equiv_restrict e2))
                          (determinant (equiv_restrict e1))).
      refine (_ @
                @mon_assoc _
                           (det_twist (e2 (inr tt)))
                           (det_twist (e1 (inr tt)))
                           (determinant (equiv_restrict e2) + determinant (equiv_restrict e1))).
      recall (e1 (inr tt)) as x eqn:p. rewrite p.
      destruct x as [x | []].
      + rewrite <- p.
        
                
      rewrite <- (IHn (equiv_restrict e1) (equiv_restrict e2)).
      recall (e1 (inr tt)) as x eqn:p. rewrite p.
      destruct x as [x | []].
      + rewrite <- p.
        destruct ( (e1 (inr tt


        admit.
      + apply (ap (fun g => det_twist (e2 (inr tt)) + g)).
        simpl. refine (_ @ (id_2_is_id _)^).
        apply (ap determinant).
        refine (_ @ (path_equiv (path_forall _ _ (equiv_restrict_plus1 (_))))).
        cut ((equiv_restrict e2 oE equiv_restrict e1 +E (equiv_idmap Unit)) =
              (equiv_restrict e2 +E 1) oE (equiv_restrict e1 +E 1)).
        { intro H. rewrite H. 
          rewrite (equiv_restrict_fixlast e1 p).         
          apply (ap (equiv_restrict)).
          apply path_equiv. apply path_arrow. intro x. ev_equiv.
          refine ((equiv_restrict_plus1 e2 (e1 x))^ @ _).

          
          rewrite (path_equiv (path_forall _ _ )).
        
        
        
        
        
        
        unfold equiv_restrict. 
        apply path_equiv. apply path_arrow. intro x.
        
        
        rewrite <- (equiv_restrict_fixlast e1 p).
        

      
      rewrite (symm_group_2
                 (determinant (equiv_restrict e2 oE equiv_restrict e1))
                 (determinant (equiv_restrict e1))).

      hnf. simpl.
      destruct (e1 (inr tt)) as [y | []].
      + simpl.
        
        rewrite (symm_group_2 (twist_2 (det_twist y)) (determinant (equiv_restrict e1))).
        rewrite (@mon_assoc _
                            (det_twist (e2 (inr tt)))
                            (determinant (equiv_restrict e2))
                            (determinant (equiv_restrict e1) + twist_2 (det_twist y))).
        rewrite <- (@mon_assoc _
                               (determinant (equiv_restrict e2))
                               (determinant (equiv_restrict e1))
                               (twist_2 (det_twist y))).
        rewrite <- (IHn (equiv_restrict e1) (equiv_restrict e2)).
        rewrite (symm_group_2
                   (determinant (equiv_restrict e2 oE equiv_restrict e1))
                   (twist_2 (det_twist y))).
        
        
        
        transitivity
          (mult_2 (mult_2 (determinant (equiv_restrict e2)) (det_twist (e2 (inr tt))))
                  (mult_2 (twist_2 (det_twist y)) (determinant (equiv_restrict e1)))).
        { 
        
        

        admit.
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


    





    
  
  