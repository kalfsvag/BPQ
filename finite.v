Require Import HoTT.
Load stuff.
Context `{Funext}.

(* A few results I didn't find *)
Lemma dprop_equiv_unit (A : Type) (isprop_A : IsHProp A) (dec_A : Decidable A) : (A + ~A) <~> Unit.
Proof.
  srapply @equiv_adjointify.
  - exact (const tt).
  - intro t. exact (dec_A).
  - intros []. reflexivity.
  - intros [a | na].
    destruct (dec_A) as [a' | na'].
    apply (ap inl). apply (isprop_A a' a).
    destruct (na' a).
    destruct (dec_A) as [a' | na'].
    destruct (na a').
    apply (ap inr). apply path_arrow. intro a. destruct (na a).
Defined.

Lemma equiv_sigma_sum' (A : Type) (B C : A -> Type) :
   {a : A & B a} + {a : A & C a} <~> {a : A & B a + C a}.
Proof.
  srapply @equiv_adjointify.
  - intros [[a b] | [a c]].
    + exact (a; inl b).
    + exact (a; inr c).
  - intros [a [b | c]].
    + exact (inl (a; b)).
    + exact (inr (a; c)).
  - intros [a [b | c]]; reflexivity.
  - intros [[a b] | [a c]]; reflexivity.
Defined.
    
  

(* This is also in monoidal_1type.v *)
(*Finite types are sets *)
Definition isset_Fin (n : nat) : IsHSet (Fin n).
Proof.
  induction n.
  - exact _.
  - apply hset_sum.
Defined.

Definition isset_Finite (A : Type) :
  Finite A -> IsHSet A.
Proof.
  intros [m finA]. strip_truncations.
  apply (trunc_equiv' (Fin m) finA^-1).
Defined.


Section Factorize_Monomorphism.
  Context (A B : Type).
  Context {finite_A : Finite A}.
  Context {finite_B : Finite B}.
  Context (f : A-> B).
  Context {ismono_f : forall a1 a2 : A, f a1 = f a2 -> a1 = a2}.

  (* First a lemma that the hfiber is a proposition *)
  Lemma ishprop_hfiber (b : B) : IsHProp (hfiber f b).
  Proof.
    apply trunc_sigma'.
    - intro a. srapply @isset_Finite.
    - intros [a1 p1] [a2 p2]. simpl.
      apply contr_inhabited_hprop.
      + srapply @isset_Finite.
      + apply ismono_f.
        exact (p1 @ p2^).
  Defined.

  (* Since A is a set, the himage is the sum of the hfibers *)
  Lemma himage_hfiber : (himage f) <~> {b : B & hfiber f b}.
  Proof.
    unfold himage. unfold TrM.image. simpl.
    apply equiv_functor_sigma_id. intro a.
    apply equiv_inverse. 
    exists tr.
    apply isequiv_tr.
    apply ishprop_hfiber.
  Defined.

  (* Then a lemma that the the hfiber is decidable. *)
  Global Instance decidable_hfiber (b : B) : Decidable (hfiber f b).
  Proof.
    apply detachable_finite_subset.
    - apply ishprop_hfiber.
    - apply (finite_equiv' (himage f) himage_hfiber).
      apply finite_image.
  Defined.

  (* Now we can start factorizing *)
  Theorem split_range : {b : B & hfiber f b} + {b : B & not (hfiber f b)} <~> B.
  Proof.
    transitivity (B*Unit).
    transitivity {b : B & Unit}.
    transitivity {b : B & hfiber f b + ~ hfiber f b}.
    - apply equiv_sigma_sum'.
    - apply equiv_functor_sigma_id.
      intro b.
      apply (dprop_equiv_unit _ (ishprop_hfiber b) (decidable_hfiber b)).
    - apply equiv_sigma_prod0.
    - apply prod_unit_r.
  Defined.

  (* Could perhaps be simplified using isequiv_fcontr *)
  Theorem equiv_A_image : A <~> {b : B & hfiber f b}.
  Proof.
    transitivity {a : A & {b : B & f a =b}}.
    transitivity {a : A & Unit}.
    transitivity (A*Unit).
    - apply equiv_inverse. apply prod_unit_r.
    - apply equiv_inverse. apply equiv_sigma_prod0.
    - apply equiv_functor_sigma_id.
      intro a.
      srapply @equiv_adjointify.
      + intro t. exact (f a; idpath).
      + exact (const tt).
      + intros [b p].
        srapply @path_sigma.
        * exact p.
        * transitivity (1@p).
          apply transport_paths_r.
          apply concat_1p.
      + intros []. reflexivity.
    - unfold hfiber.
      apply equiv_sigma_symm.
  Defined.
End Factorize_Monomorphism.



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



  



Section Pointed_Finite.
  Local Open Scope nat.
  (* Canonical pointed finite sets as subsets of N *)
  Definition pFin (n : nat) := {i : nat | i <= n}.
  Global Instance ispointed_pFin {n : nat} : IsPointed (pFin n) := (0;tt).

  (* The map sending 0 to [inl tt] *)
  Definition equiv_pFin_succ (n : nat) : pFin (n.+1) <~> Unit + pFin n.
  Proof.
    srapply @equiv_adjointify.
    - intros [i Hi].
      destruct i.
      + exact (inl tt).
      + exact (inr (i; Hi)).
    - intros [[] | i].
      + exact (0; tt).
      + destruct i as [i Hi].
        exact (i.+1; Hi).
    - unfold Sect.
      intros [[] | [i Hi]]; reflexivity.
    - unfold Sect.
      intros [i Hi]. simpl.
      induction i. simpl in Hi. destruct Hi. reflexivity.
      reflexivity.
  Defined.

  (* The map sending n+1 to [inr tt] *)
  Definition equiv_pFin_incl (n : nat) : pFin (n.+1) <~> pFin n + Unit.
  Proof.
    srapply @equiv_adjointify.
    - intros [i i_leq_Sn].
      destruct (lt_or_eq i (n.+1) i_leq_Sn) as [i_lt_Sn | eq_i_n].
      (* Case when i<n+1 *)
      + exact (inl (i; i_lt_Sn)).
      (* Case when i=n *)
      + exact (inr tt).
    - intros [[i i_leq_n] | []].
      + exists i.
        apply (leq_transd i_leq_n). apply leq_succ.
      + exists n.+1. apply leq_refl.
    - unfold Sect.
      (* I fell there should be a better way to do this. . . *)
      intros [[i i_lt_n] |].      
      + destruct (lt_or_eq i n.+1 (leq_transd i_lt_n (leq_succ n))) as [i_lt_Sn | i_eq_Sn].
        * apply (ap inl).
          apply path_sigma_hprop. reflexivity.
          (* apply (ap (fun a : i <= n => (i; a))). *)
          (* apply (istrunc_trunctype_type (i<=n)). *)
        * assert (false : n.+1 <= n).
          {rewrite <- i_eq_Sn. apply i_lt_n. }
          destruct (not_i_lt_i n false).
      + intros []. simpl.
        destruct (lt_or_eq n.+1 n.+1 (leq_refl n)) as [i_lt_Sn | i_eq_Sn].
        * destruct (not_i_lt_i n.+1 i_lt_Sn).
        * exact idpath.
    - unfold Sect.
      intros [i i_leq_Sn].
      destruct (lt_or_eq i n.+1 i_leq_Sn) as [i_lt_sn | i_eq_sn]; simpl.
      + apply (path_sigma_hprop). reflexivity.
      + apply (path_sigma_hprop). exact i_eq_sn^.
  Defined.

  (* (* Give better name if this works *) *)
  (* Definition decidable_path_Sn : forall (n : trunc_index) (x : Sphere n.+2), Decidable (merely (x = North)). *)
  (* Proof. *)
  (*   intros n x. unfold Decidable. *)
  (*   induction n. *)
  (*   revert x. srapply @Susp_ind; simpl. *)
  (*   + apply inl. apply tr. exact idpath. *)
  (*   +                           (* Trenger at merid er en ekvivalens? *) *)
    
    
    
  (*     (* Do this for n-spheres directly? *) *)
  (* (* I want a map (pFin n -> X) -> (pFin n -> X) moving all basepoints to the end, and else keeping the order *) *)
  (* Definition movebptoend {n : nat} (X : Type) : (pFin n -> X + Unit) -> (pFin n -> X + Unit). *)
  (* Proof. *)
  (*   induction n. *)
  (*   - exact idmap. *)
  (*   -  *)
  (*     intro x. *)
  (*     destruct (x (0;tt)).  *)
      
  (*     destruct (merely (x (0; tt) = x0)) as [fst_is_bp | fst_is_not_bp]. *)


  (* General pointed finite sets of cardinality n *)
  Definition Pointed_Finite (n : nat) := {A : Type & merely (A <~> pFin n)}.

  (* Definition Canonical_Pointed_Finite (n : nat) : Pointed_Finite n:= *)
  (*   (pFin n; tr 1%equiv). *)


End Pointed_Finite.


Section Cosimplicial_maps.
  Local Open Scope nat.
   Notation "[ n ]" := {m : nat | m <= n}.
  (* Definition pFin (n : nat) := { m : nat | m <= n }. *)
  (* Definition pFin_include {n : nat} : pFin n -> nat := pr1. *)
  (* Coercion pFin_include : pFin >-> nat. *)

  (* The i'th coface *)
  Definition coface {n : nat} (i : nat) (i_leq_n : i <= n) : [n] -> [n.+1].
  Proof.
    intros [j j_leq_n].
    destruct (leq_or_gt i j).   (* destruct (dec (i <= j)).      *)
    (* i <= j *)
    - exists j.
      apply (leq_transd j_leq_n)%nat. apply leq_succ.
    (* j > i *)
    - exists j.+1.
      apply j_leq_n.
  Defined.

  (* The i'th codegeneracy *)
  (* s_i j =
          j, if j <= i
          j-1, if j > i  *)
  Definition codegen {n : nat} (i : nat) (i_leq_n : i <= n) : [n.+1] -> [n].
  Proof.
    intros [j j_leq_Sn].
    destruct (leq_or_gt j i).
    (* j <= i *)
    - exists j.
      apply (leq_trans _ i _ t i_leq_n).
    (* j > i *)
    - destruct (gt_is_succ t) as [k H]. (* j is a successor *)
      exists k.
      change (k <= n) with (k.+1 <= n.+1).
      apply (@leq_transd k.+1 j n.+1)%nat.
      rewrite H. apply leq_refl.
      apply j_leq_Sn.
  Defined.

End Cosimplicial_maps.














(* Older definition of pointed finite sets: *)
(* (* The nonempty finite sets of n+1 elements *) *)
(* Inductive pFin : forall (n : nat), Type := *)
(*   | fin_zero {n : nat} : pFin n *)
(*   | fin_succ {n : nat} : pFin n -> pFin n.+1. *)

(* Definition fin_include {n : nat} : pFin n -> pFin n.+1. *)
(* Proof. *)
(*   intro i. induction i. *)
(*   (* zero goes to zero *) *)
(*   exact fin_zero. *)
(*   (* i+1 goes to i+1 *) *)
(*   exact (fin_succ IHi). *)
(* Defined. *)

(* (* pFin is equivalent to Fin *) *)
(* Lemma equiv_pFin_Fin (n : nat) : pFin n <~> Fin n.+1. *)
(* Proof. *)
(*   srapply @equiv_adjointify. *)
(*   - intro i. induction i. *)
(*     (* i=0 *) exact (inr tt). *)
(*     (* i+1 *) exact (inl IHi). *)
(*   - induction n. *)
(*     intro i. exact fin_zero.    (* n=0 *) *)
(*     intros [i |]. *)
(*     exact (fin_succ (IHn i)). (* i+1 *) *)
(*     intro t. exact fin_zero.  (* i=0 *) *)
(*   - intro i. simpl. *)
(*     induction n. simpl. destruct i. contradiction. destruct u. reflexivity. *)
(*     destruct i. *)
(*     { simpl. exact (ap inl (IHn f)). } destruct u. reflexivity. *)
(*   - intro i. induction i. *)
(*     + simpl. induction n. reflexivity. reflexivity. *)
(*     + simpl. simpl in IHi. exact (ap fin_succ IHi). *)
(* Defined. *)


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

  
  
  
    
  




