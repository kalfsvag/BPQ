Require Import HoTT.
Require Import trunc_lemmas.
Require Import sigma_lemmas.
Require Import equiv_lemmas.
Require Import UnivalenceAxiom.


(* The type of decidable propositions is finite *)
Global Instance finite_dprop : Finite DProp.
Proof.
  refine (finite_equiv' (Fin 2) _ _).
  transitivity Bool.
  + unfold Fin.
    srapply @equiv_adjointify.
    { intros [[[] | []] | []]. exact true. exact false. }
    { intros  [ | ]. exact (inl (inr tt)). exact (inr tt). }
    * intros [ | ] ;reflexivity.
    * intros [[[] | []] | []]; reflexivity.
  + apply equiv_inverse. apply equiv_dprop_to_bool.
Qed.
    

Section Finite_Types.
  Definition Finite_Types  :=
    {A : Type & Finite A}.

  Definition type_of (A : Finite_Types) := pr1 A.
  Global Coercion type_of : Finite_Types >-> Sortclass.
  Global Instance finite_finite_type (A : Finite_Types) : Finite A := A.2.

  (* Canonical finite types *)
  Definition canon (n : nat) : Finite_Types :=
    (* Build_Finite_Types (Fin n) (Build_Finite (Fin n) n (tr 1%equiv)). *)
    (Fin n; Build_Finite (Fin n) n (tr 1%equiv)).

  (* A detachable subset of a finite set has smaller cardinal *)
  Definition leq_card_subset (A : Finite_Types) (P : A -> Type)
             (isprop_P : forall a : A, IsHProp (P a)) (isdec_P : forall a : A, Decidable (P a)) :
    (fcard {a : A & P a} <= fcard A)%nat.
  Proof.  
    destruct A as [A fA]. simpl in P, isprop_P, isdec_P. simpl.
    apply (leq_inj_finite pr1).
    unfold IsEmbedding. intro a.
    apply (trunc_equiv' (P a) ).
    apply hfiber_fibration. apply isprop_P.
  Qed.

  (* Plus one for finite types *)
  Definition add_one : Finite_Types -> Finite_Types.
  Proof.
    intros [A [n H]].
    exists (A + Unit).
    (* apply (Build_Finite_Types (A + Unit)). *)
    strip_truncations.
    apply (Build_Finite _ (n.+1)).
    apply tr. (* apply path_universe_uncurried. *)
    (* exact (equiv_functor_sum' ((equiv_path_universe A (Fin n))^-1 H) equiv_idmap). *)
    exact (equiv_functor_sum' H equiv_idmap).
  Defined.

  Definition path_finite_types  (s t : Finite_Types):
    (s <~> t) <~> s = t :=
    equiv_path_sigma_hprop _ _ oE equiv_path_universe _ _.

  Definition transport_exp_finite {X : Type} {A B : Finite_Types} (e : A <~> B) (x : A -> X) :
    transport (fun I : Finite_Types => I -> X) (path_finite_types A B e) x = x o e^-1.
  Proof.
    refine (ap10 (transport_pr1_path_sigma_uncurried (pr1^-1 (path_universe_uncurried e))
                                                     (fun A : Type => A -> X)) x @ _).
    exact (transport_exp X A B e x).
  Defined.

  (* This should more or less follow from baut_ind_hset (except that is only for P: Type -> Type*)
  Definition BSigma_ind_hSet (P : Finite_Types -> Type)
             {isset_P : forall s : Finite_Types, IsHSet (P s)}
             (pt : forall n : nat, P (canon n))
             (wd : forall (n : nat) (e : Fin n <~> Fin n),
                 transport P (path_finite_types (canon n) (canon n) e) (pt n) = pt n) :
    forall s : Finite_Types, P s.
  Proof.
    intro s.
    apply (@pr1 (P s) (fun p : P s => forall e' : Fin (fcard s) <~> s,
                           transport P (path_finite_types (canon (fcard s)) s e') (pt (fcard s)) = p)).
    assert (isprop_goal : forall s' : Finite_Types, IsHProp
                                                      {p : P s' &
                                                           forall e' : Fin (fcard s') <~> s',
                                                             transport P (path_sigma_hprop (canon (fcard s')) s' (path_universe_uncurried e'))
                                                                       (pt (fcard s')) = p}).
    { destruct s' as [A [m eA]].
      strip_truncations. apply trunc_sigma'.
      - intro p. apply trunc_forall.
      - intros p q.
        apply (contr_inhabited_hprop _).
        destruct p as [p fp]. destruct q as [q fq]. simpl. simpl in fp. simpl in fq.      
        exact ((fp (equiv_inverse eA))^ @ (fq (equiv_inverse eA))). }
    destruct s as [A [m eA]]. strip_truncations.
    destruct (path_finite_types (canon m) (A; Build_Finite A m (tr eA)) (equiv_inverse eA)).
    change (fcard (canon m)) with m.
    exact (pt m; wd m).
  Defined.

End Finite_Types.
  




(* A term in Magma A is a decomposition of A into a sum of Empty and Unit *)
Section Magma.
  Inductive Magma : Type -> Type :=
    |m0 : Magma Empty
    |m1 : Magma Unit
    |m_sum {A B : Type} : Magma A -> Magma B -> Magma (A+B).

  Definition magma_to_finite (A : Type) : Magma A -> Finite A.
  Proof.
    intro m.
    induction m.
    - exact finite_empty.
    - exact finite_unit.
    - apply finite_sum. exact IHm1. exact IHm2.
  Defined.

  (* Definition contr_magma0 : Contr (Magma Empty). *)
  (* Proof. *)
  (*   apply (BuildContr _ m0). *)
  (*   recall Empty as A eqn:e. *)
  (*   apply (transport (fun B => Contr (Magma B)) e^). *)
  (*   srapply @BuildContr. *)
  (*   - destruct e. exact m0. *)
  (*   - intro m. induction m. *)
      

      
  (*   recall Empty as A eqn:e. *)
  (*   apply (transport (fun B => Contr (Magma B)) e^). *)

  (*   -  *)
    
End Magma.

  

(* This is also in monoidal_1type.v *)
(*Finite types are sets *)
Definition isset_Fin (n : nat) : IsHSet (Fin n).
Proof.
  induction n.
  - exact _.
  - apply hset_sum.
Defined.

Definition isset_Finite `{Funext} (A : Type) :
  Finite A -> IsHSet A.
Proof.
  intros [m finA]. strip_truncations.
  apply (trunc_equiv' (Fin m) finA^-1).
Defined.

Section Restrict_Equivalence.
  (* This is just copied from fin_equiv_hfiber, but I wanted it as its own result *)

  (* My doing: One of the Fin n's is generalized. *)
  Local Lemma is_inl_restrict_equiv_notfixlast {n : nat} {A : Type}
        (e : A+Unit <~> Fin n.+1) (y : Fin n) (p : e (inr tt) = inl y) :
    forall a : A, is_inl ((fin_transpose_last_with n (inl y) oE e) (inl a)).
  Proof.
    intro a. ev_equiv.
    assert (q : inl y <> e (inl a))
      by exact (fun z => inl_ne_inr _ _ (equiv_inj e (z^ @ p^))).
    set (z := e (inl a)) in *.
    destruct z as [z|[]].
    - rewrite fin_transpose_last_with_rest;
        try exact tt; try assumption.
    - rewrite fin_transpose_last_with_last; exact tt.
  Qed.

  Local Lemma is_inr_restrict_equiv_notfixlast {n : nat} {A : Type}
        (e : A + Unit <~> Fin n.+1) (y : Fin n) (p : e (inr tt) = inl y) :
    forall b : Unit, is_inr ((fin_transpose_last_with n (inl y) oE e) (inr b)).
  Proof.
    intros []. ev_equiv.
    rewrite p.
    rewrite fin_transpose_last_with_with; exact tt.
  Qed.

  Local Lemma is_inl_restrict_equiv_last_fixed {A B: Type} (e : A + Unit <~> B + Unit) (p : e (inr tt) = inr tt)
    : forall a : A, is_inl (e (inl a)).
  Proof.
    intro a.
    destruct (is_inl_or_is_inr (e (inl a))) as [l|r].
    - exact l.
    - assert (q := inr_un_inr (e (inl a)) r).
      apply moveR_equiv_V in q.
      assert (s := q^ @ ap (e^-1 o inr) (path_unit _ _) @ (moveL_equiv_V _ _ p)^).
      elim (inl_ne_inr _ _ s).
  Qed.

  Local Lemma is_inr_restrict_equiv_last_fixed {A B : Type} (e : A+Unit <~> B+Unit) (p : e (inr tt) = inr tt) :
    forall b : Unit, is_inr (e (inr b)).
  Proof.
    intros []; exact (p^ # tt).
  Defined.

  Definition equiv_restrict {n : nat} {A : Type} (e : A+Unit <~> Fin n.+1) :  A<~> Fin n.
  Proof.
    simpl in e.
    recall (e (inr tt)) as y eqn:p.
    assert (p' := (moveL_equiv_V _ _ p)^).
    destruct y as [y | []].
    (*  *)
    - apply (equiv_unfunctor_sum_l (fin_transpose_last_with n (inl y) oE e)).
      + apply is_inl_restrict_equiv_notfixlast. exact p.
      + apply is_inr_restrict_equiv_notfixlast. exact p.
    - apply (equiv_unfunctor_sum_l e (is_inl_restrict_equiv_last_fixed e p) (is_inr_restrict_equiv_last_fixed e p)).
  Defined.
End Restrict_Equivalence.


Section Factorize_Monomorphism.
  Context (A B : Type).
  Context {finite_A : Finite A}.
  Context {finite_B : Finite B}.
  Context (f : A-> B).
  (* Context (ismono_f : forall a1 a2 : A, f a1 = f a2 -> a1 = a2). *)
  Context (isemb_f : IsEmbedding f).
  Context `{Funext}.
  
  (* If f is an embedding and A has a point, then f has a retract *)
  Definition retract_of_embedding (a0 : A) : B -> A.
  Proof.
    intro b.
    destruct (detachable_image_finite f b) as [[a p] |]. 
    - exact a.
    - exact a0.
  Defined.  

  
  Definition issect_embedding (a0 : A) : (retract_of_embedding a0) o f == idmap.
  Proof.
    cbn. intro a. unfold retract_of_embedding.
    destruct (detachable_image_finite f (f a)) as [[a' p] |].
    - apply (isinj_embedding f _ _ _ p).
    - apply Empty_rec. apply n. exact (a; idpath).
  Defined.

  (* (* First a lemma that the hfiber is a proposition *) *)
  (* Lemma ishprop_hfiber (b : B) : IsHProp (hfiber f b). *)
  (* Proof. *)
  (*   apply trunc_sigma'. *)
  (*   - intro a. srapply @isset_Finite. *)
  (*   - intros [a1 p1] [a2 p2]. simpl. *)
  (*     apply contr_inhabited_hprop. *)
  (*     + srapply @isset_Finite. *)
  (*     + apply ismono_f. *)
  (*       exact (p1 @ p2^). *)
  (* Defined. *)

  (* (* Since A is a set, the himage is the sum of the hfibers *) *)
  (* Lemma himage_hfiber : (himage f) <~> {b : B & hfiber f b}. *)
  (* Proof. *)
  (*   unfold himage. unfold TrM.image. simpl. *)
  (*   apply equiv_functor_sigma_id. intro a. *)
  (*   apply equiv_inverse.  *)
  (*   exists tr. *)
  (*   apply isequiv_tr. *)
  (*   apply ishprop_hfiber. *)
  (* Defined. *)

  (* (* Then a lemma that the the hfiber is decidable. *)
  (*    This is almost the same as decidable_image_finite *) *)
  (* Global Instance decidable_hfiber (b : B) : Decidable (hfiber f b). *)
  (* Proof. *)
  (*   apply detachable_finite_subset. *)
  (*   - apply ishprop_hfiber. *)
  (*   - apply (finite_equiv' (himage f) himage_hfiber). *)
  (*     apply finite_image. *)
  (* Defined. *)

  (* Now we can start factorizing *)
  Theorem split_range : B <~> {b : B & hfiber f b} + {b : B & not (hfiber f b)}.
  Proof.
    srapply @equiv_adjointify.
    { intro b.
      destruct (detachable_image_finite f b) as [fib | nfib].
      exact (inl (b; fib)). exact (inr (b; nfib)). }
    { intros [[b fib] | [b nfib]] ;exact b. }
    - intros [[b fib] | [b nfib]];
        destruct (detachable_image_finite f b) as [fib' | nfib']; cbn.
      + apply (ap inl). apply path_sigma_hprop. reflexivity.
      + destruct (nfib' fib).
      + destruct (nfib fib').
      + apply (ap inr). apply path_sigma_hprop. reflexivity.
    - intro b.
      destruct (detachable_image_finite f b) as [fib | nfib]; reflexivity.      
  Defined.    
    (* transitivity (B*Unit). *)
    (* transitivity {b : B & Unit}. *)
    (* transitivity {b : B & hfiber f b + ~ hfiber f b}. *)
    (* - apply equiv_sigma_sum'. *)
    (* - apply equiv_functor_sigma_id. *)
    (*   intro b. *)
    (*   apply (dprop_equiv_unit _ (isemb_f b) (detachable_image_finite f b)). *)
    (* - apply equiv_sigma_prod0. *)
    (* - apply prod_unit_r. *)
  (* Defined. *)

  (* Could perhaps be simplified using isequiv_fcontr *)
  Theorem equiv_A_image : A <~> {b : B & hfiber f b}.
  Proof.
    srapply @equiv_adjointify.
    { intro a. exists (f a). exists a. reflexivity. }
    { intros [b [a p]]. exact a. }
    - intros [b [a p]]. srapply @path_sigma. exact p.
      apply isemb_f.
    - intro a. reflexivity.
  Defined.
    
  (*   transitivity {a : A & {b : B & f a =b}}. *)
  (*   transitivity {a : A & Unit}. *)
  (*   transitivity (A*Unit). *)
  (*   - apply equiv_inverse. apply prod_unit_r. *)
  (*   - apply equiv_inverse. apply equiv_sigma_prod0. *)
  (*   - apply equiv_functor_sigma_id. *)
  (*     intro a. *)
  (*     srapply @equiv_adjointify. *)
  (*     + intro t. exact (f a; idpath). *)
  (*     + exact (const tt). *)
  (*     + intros [b p]. *)
  (*       srapply @path_sigma. *)
  (*       * exact p. *)
  (*       * transitivity (1@p). *)
  (*         apply transport_paths_r. *)
  (*         apply concat_1p. *)
  (*     + intros []. reflexivity. *)
  (*   - unfold hfiber. *)
  (*     apply equiv_sigma_symm. *)
  (* Defined. *)
  
End Factorize_Monomorphism.

Section Finite_Subsets.
  (* Lemma finite_fibers_to_finite_sigma *)
  (*       (A : Type) (a0 : A) (B : A -> Type) (finite_B0 : Finite (B a0)) *)
        
  (*       (connected_A : merely (forall a : A, a0 = a)) *)
  (*       (only_basepoint_inhabited : merely (forall (a : A) (b0 : B a0) (b : B a), (a = a0))) *)
  (* : Finite {a : A & B a}. *)
  (* Proof.     *)
  (*   destruct finite_B0 as [m e]. *)
  (*   apply (Build_Finite _ m). strip_truncations. apply tr. *)
  (*   refine (e oE _). *)
  (*   set (iscontr_A := BuildContr A (point A) connected_A : Contr A). *)
  (*   apply (@equiv_contr_sigma A B iscontr_A). *)
  (* Defined.  *)

  Definition Finite_Subsets (A : Finite_Types) :=
    {B : Finite_Types & {f : B -> A & IsEmbedding f}}.
  Definition fintype_of_subset (A : Finite_Types) : Finite_Subsets A -> Finite_Types := pr1.  
  Global Coercion fintype_of_subset : Finite_Subsets >-> Finite_Types.

  Definition path_finite_subsets {A : Finite_Types} (B1 B2 : Finite_Subsets A)
             (e : B1 <~> B2) (h : B1.2.1 o e^-1 = B2.2.1) :
    B1 = B2.
  Proof.
    srapply @path_sigma.
    - apply path_finite_types. exact e.
    - apply path_sigma_hprop. refine (_ @ h). destruct B1 as [B1 [f1 emb1]]. destruct B2 as [B2 [f2 emb2]]. cbn in *.
      refine (_ @ transport_exp_finite e f1). cbn.
      apply (ap pr1 (transport_sigma (A := Finite_Types) (B := fun B => B -> A) (C := fun B f => IsEmbedding f)
                                     (path_sigma_hprop B1 B2 (path_universe_uncurried e)) (f1; emb1))).
  Defined.
             

  Local Definition project_to_dprop (X Y : Type) : X + Y -> DProp :=
    fun xy => if xy then True else False.

  (* Giving a finite subset is the same as giving a map A -> DProp *)
  Definition equiv_detachable_finite_subset {A : Finite_Types} :
    (A -> DProp) <~> Finite_Subsets A.
  Proof.
    srapply @equiv_adjointify.
    { intro B.
      srapply @existT.
      exists {a : A & B a}. exact _.
      cbn. exists pr1. intro a.
      apply (trunc_equiv' (B a)).
      apply (hfiber_fibration a B). exact _. }
    { intros [B [f isemb_f]].
      exact ((project_to_dprop _ _) o (split_range B A f isemb_f)). }
    - intros [B [f isemb_f]].
      srapply @path_finite_subsets.
      + cbn.
        srapply @equiv_adjointify.
        { intros [a h].
          destruct (detachable_image_finite f a) as [fib | nfib]; cbn in *.
          - exact fib.1. - destruct h. }
        { intro b. exists (f b).
          destruct (detachable_image_finite f (f b)) as [fib | nfib]; cbn.
          - exact tt. - apply nfib. exists b. reflexivity. }
        * intro b. cbn.
          destruct (detachable_image_finite f (f b)) as [fib | nfib]. destruct fib as [b' p]; cbn.
          { apply (isinj_embedding f isemb_f). exact p. }
          apply Empty_rec. apply nfib. exists b. reflexivity.
        * cbn. intros [a h].
          apply path_sigma_hprop. cbn.          
          destruct (detachable_image_finite f a) as [fib | nfib]; cbn in *.
          { destruct fib as [a' p]. cbn. exact p. } destruct h.
      + reflexivity.
    - intro B.
      apply path_arrow. intro a. cbn.
      destruct (detachable_image_finite pr1 a) as [fib | nfib]; cbn.
      + destruct fib as [[a' b] p].
        apply path_dprop. apply path_universe_uncurried. cbn.
        apply equiv_inverse.
        srapply @equiv_contr_unit. apply contr_inhabited_hprop. exact _. exact (transport B p b).
      + apply path_dprop. apply path_universe_uncurried. apply equiv_inverse.
        apply (if_not_hprop_then_equiv_Empty). exact _. intro b. apply nfib.
        apply (hfiber_fibration a B b).
  Defined.

  (* Then we can show that the type of finite subsets is finite *)
  Global Instance finite_finite_subsets {A : Finite_Types} : Finite (Finite_Subsets A).
  Proof.
    apply (finite_equiv' (A -> DProp) equiv_detachable_finite_subset).
    apply finite_forall. exact _. intro a. exact _.
  Qed.  
  
  Definition Finite_Types_component (n : nat)
    := {B : Type & (merely (B <~> Fin n))}.
  Definition fin_to_fin (n : nat) :
    Finite_Types_component n -> Finite_Types.
    intros [B e].
    exists B. exists n. exact e.
  Defined.

  Coercion fin_to_fin : Finite_Types_component >-> Finite_Types.
  Global Instance finite_fin_ (n : nat) (B : Finite_Types_component n) : Finite B := finite_finite_type B.

  Definition fcard_is_ (n : nat) (B : Finite_Types_component n)
    : fcard B = n := idpath.

  Definition decompose_finite_types :
    Finite_Types <~> {n : nat & Finite_Types_component n}.
  Proof.
    srapply @equiv_adjointify.
    { intros [A [n e]]. exact (n; (A; e)). }
    { intros [n [A e]]. exists A. exact (Build_Finite A n e). }
    - intros [n [A e]]. reflexivity.
    - intros [A [n e]]. reflexivity.
  Defined.

  Definition component_is_subtype (n : nat):
    Finite_Types_component n <~> {B : Finite_Types & fcard B = n}.
  Proof.
    srapply @equiv_adjointify.
    { intros [B e]. exists (B; Build_Finite B n e). reflexivity. }
    { intros [[B [m e]] p]. destruct p. cbn. exact (B;e). }
    - intros [[B [m e]] p]. destruct p. reflexivity.
    - intros [B e]. reflexivity.
  Defined.  
  
  Definition finite_subset_component (A : Finite_Types) (n : nat) :=
    { B : Finite_Types_component n & {f : B -> A & IsEmbedding f}}.
  Definition subset_component_to_component (A : Finite_Types) (n : nat)
    : finite_subset_component A n -> Finite_Types_component n := pr1.
  Coercion subset_component_to_component : finite_subset_component >-> Finite_Types_component.

  Definition subset_component_to_subset (A : Finite_Types) (n : nat)
    : finite_subset_component A n -> Finite_Subsets A.
  Proof.
    intros [B e]. exists B. exact e.
  Defined.
  Coercion subset_component_to_subset : finite_subset_component >-> Finite_Subsets.    
  

  Definition decompose_finite_subsets (A : Finite_Types) :
    Finite_Subsets A <~> {n : nat & finite_subset_component A n}.
  Proof.
    unfold Finite_Subsets. unfold finite_subset_component.
    transitivity {B : {n : nat & Finite_Types_component n} & {f : B.2 -> A & IsEmbedding f}}.
    - srapply @equiv_functor_sigma'. exact decompose_finite_types. cbn.
      intro B. reflexivity.
    - apply equiv_inverse. srapply @equiv_sigma_assoc.
  Defined.

  Definition subset_component_is_subtype (A : Finite_Types) (n : nat) :
    finite_subset_component A n <~> {B : Finite_Subsets A & fcard B.1 = n}.
  Proof.
    unfold finite_subset_component. unfold Finite_Subsets.
    transitivity {B : {B : Finite_Types & fcard B = n} & {f : B.1 -> A & IsEmbedding f}}.
    { srapply @equiv_functor_sigma'. apply component_is_subtype.
      intro B. reflexivity. }
    (* Easier to do directly than using lemmas *)
    srapply @equiv_adjointify.
    { intros [[B p] h]. exact ((B; h); p). }
    { intros [[B h] p]. exact ((B; p); h). }
    - intros [[B h] p]. reflexivity.
    - intros [[B p] h]. reflexivity.
  Defined.

  Definition equiv_detachable_finite_subset_component (A : Finite_Types) (n : nat):
    finite_subset_component A n <~> {B : A -> DProp & fcard ({a : A & B a}) = n}.
  Proof.
    refine (_ oE subset_component_is_subtype A n). apply equiv_inverse.
    srapply @equiv_functor_sigma'. apply equiv_detachable_finite_subset.
    intro B. hnf. reflexivity.
  Defined.
  
End Finite_Subsets.
      



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

  
  
  
    
  




