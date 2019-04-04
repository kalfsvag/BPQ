Require Import HoTT.


(* Example test ( A : Type) (H : Decidable A) : ~ ~ A -> A. *)
(* intros. unfold not in X. *)
(* destruct (dec A). *)
(* exact a. *)
(* destruct (X n). *)
Require Import finite_lemmas.

Definition twist2 : Fin 2 -> Fin 2.
Proof.
  unfold Fin.
    intros [[[] |[]] | [] ].
    + apply inr. exact tt.
    + apply inl. apply inr. exact tt.
Defined.

Definition twist2_squared : twist2 o twist2 == idmap.
Proof.
  intros [[[] |[]] | [] ]; reflexivity.
Defined.  

Definition isequiv_twist2 : IsEquiv twist2.
  apply (isequiv_adjointify twist2 twist2); apply twist2_squared.
Defined.

Definition equiv_twist2 : Fin 2 <~> Fin 2 :=
  BuildEquiv _ _ twist2 isequiv_twist2.

Fixpoint endpoint_minus {n : nat} (k : Fin n.+1) : nat.
Proof.
  simpl in k.
  destruct k as [k | endpoint].
  destruct n. destruct k.
  (* (n+1)-(k+1) := n - k  *)
  - exact (endpoint_minus n k).
  (* (n+1)-(n+1) = 0 *)
  - exact 0.
Defined.

Fixpoint iterated_composition {A : Type} (n : nat) (f : A <~> A) : A <~> A.
Proof.
  destruct n.
  - exact equiv_idmap.
  - exact (f oE (iterated_composition A n f)).
Defined.

Section Determinant.
  Fixpoint determinant (n : nat) :
    (Fin n <~> Fin n) -> (Fin 2 <~> Fin 2).
  Proof.
    intro e.

    (* refine (_ oE determinant n e_restr). *)
    
    destruct n.
    (*  *)
    - exact equiv_idmap.
    - (** the determinant of e is the determinant of the restriction times the determinant of the twist.
          the determinant of the twist is tw : 2 <~> 2 to the power of the number of transpositions *)
      (* destruct ((equiv_fin_equiv n n)^-1 e) as [twist_to e_restr]. *)
      
      refine (_ oE determinant n (snd ((equiv_fin_equiv n n)^-1 e))).
      exact (iterated_composition (endpoint_minus (fst ((equiv_fin_equiv n n)^-1 e))) equiv_twist2).
  Defined.

  Definition det_plus_1 {n : nat} (e : Fin n <~> Fin n) :
    determinant n.+1 (equiv_functor_sum' e (equiv_idmap Unit)) = determinant n e.
  Proof.
    induction n.
    - apply path_equiv. apply path_arrow.
      intro t. simpl. unfold equiv_inv.
      destruct isequiv_fin_equiv. simpl.
      + simpl.
      
      
  
    
  
  
  Definition determinant (n : nat) :
    Finite_Types n -> Finite_Types 2.
  Proof.
    intros [A H]. unfold Finite_Types.
    

    
    exists [2].
    
    strip_truncations.
    
    apply tr.


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


    





    
  
  