Require Import HoTT.


Definition Embedding (A B : Type) := {f : A -> B & IsEmbedding f}.
Definition fun_of_emb (A B : Type) : Embedding A B -> (A -> B) := pr1.
Coercion fun_of_emb : Embedding >-> Funclass.


Section Factorize_Monomorphism.
  Context (A B : Type).
  Context {finite_A : Finite A}.
  Context {finite_B : Finite B}.
  Context (f : A-> B).
  Context (isemb_f : IsEmbedding f).
  (* Context `{Funext}. *)
  
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

  (* Now we can start factorizing *)
  Theorem split_range : B <~> {b : B & hfiber f b} + {b : B & not (hfiber f b)}.
  Proof.
    srapply @equiv_adjointify.
    { intro b.
      destruct (detachable_image_finite f b) as [fib | nfib].
      - exact (inl (b; fib)).
      - exact (inr (b; nfib)). }
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

  Definition compliment_to_range : {b : B & not (hfiber f b)} -> B := pr1.

  Definition embed_compliment : IsEmbedding compliment_to_range.
  Proof.
    unfold IsEmbedding. intro b.
    apply (trunc_equiv' (not (hfiber f b))).
    - unfold compliment_to_range.
      exact (hfiber_fibration b _).
    - exact _.
  Defined.
    

  (* Could perhaps be simplified using isequiv_fcontr? *)
  Theorem equiv_image : A <~> {b : B & hfiber f b}.
  Proof.
    srapply @equiv_adjointify.
    { intro a. exists (f a). exists a. reflexivity. }
    { intros [b [a p]]. exact a. }
    - intros [b [a p]]. srapply @path_sigma.
      +  exact p.
      +  apply isemb_f.
    - intro a. reflexivity.
  Defined.

  Definition fcard_sum_compliment : (fcard A + fcard {b : B & not (hfiber f b)} = fcard B)%nat.
  Proof.
    refine ((fcard_sum _ _)^ @ _).
    apply fcard_equiv'.
    refine (split_range^-1 oE _).
    apply equiv_functor_sum'.
    - exact equiv_image.
    - reflexivity.
  Qed.

  (* a lemma for minus *)
  Lemma sum_minus (k l: nat) :
    l = (k+l)%nat - k.
  Proof.
    induction k; simpl.
    - destruct l; reflexivity.
    - simpl. exact IHk.
  Qed.

  Lemma leq_0 (k : nat) : k <= 0 -> k = 0.
  Proof.
    intro p. apply path_nat.
    destruct k; exact p.
  Defined.

  (* Fixpoint minus_minus (n k : nat) : *)
  (*   (k <= n) -> n - (n - k) = k. *)
  (* Proof. *)
  (*   destruct n. simpl. intros p. apply inverse. apply (leq_0 k p). *)
  (*   destruct k. simpl. intro t. apply path_nat. apply subnn. *)
  (*   intro p. simpl. *)
  (*   refine (_ @ ap S (minus_minus n k p)). destruct (n - k).  admit. simpl. *)
  (*   destruct n. simpl. reflexivity. destruct k. simpl. *)
    
  (*   simpl. *)

  (*   unfold leq. simpl. *)
  
  Definition fcard_compliment : fcard {b : B & not (hfiber f b)} = (fcard B) - (fcard A).
  Proof.
    destruct fcard_sum_compliment. apply sum_minus.
  Qed.    
End Factorize_Monomorphism.

Section Finite_Subsets.
  Definition Finite_Subsets {n : nat} (k : nat) (A : Finite_Types n)  :=
    {B : Finite_Types k & {f : B -> A & IsEmbedding f}}.
  Definition fintype_of_subset {n k: nat} (A : Finite_Types n)  : Finite_Subsets k A -> Finite_Types k := pr1.  
  Global Coercion fintype_of_subset : Finite_Subsets >-> Finite_Types.
  Definition type_of_subset {n k: nat} (A : Finite_Types n) : Finite_Subsets k A -> Type := pr1 o pr1.
  Global Coercion type_of_subset :Finite_Subsets >-> Sortclass.

  Definition path_finite_subsets k {n : nat} {A : Finite_Types n} (B1 B2 : Finite_Subsets k A)
             (e : B1 <~> B2) (h : B1.2.1 o e^-1 = B2.2.1) :
    B1 = B2.
  Proof.
    srapply @path_sigma.
    - apply (path_finite_types_fix k). exact e.
    - apply path_sigma_hprop. refine (_ @ h). destruct B1 as [B1 [f1 emb1]]. destruct B2 as [B2 [f2 emb2]]. cbn in *.
      refine (_ @ transport_exp_finite_fix k e f1). cbn.
      apply (ap pr1 (transport_sigma (A := Finite_Types k) (B := fun B => B -> A) (C := fun B f => IsEmbedding f)
                                     (path_sigma_hprop B1 B2 (path_universe_uncurried e)) (f1; emb1))).
  Defined.

  Definition path_finite_subsets_sum {n : nat} {A : Finite_Types n}
             (B1 B2 : {B : {fB : Type & Finite fB} & {f : B.1 -> A & IsEmbedding f}})
             (e : B1.1.1 <~> B2.1.1) (h : B1.2.1 o e^-1 = B2.2.1) :
    B1 = B2.
  Proof.
    srapply @path_sigma'.
    - apply path_finite_types_sum. exact e.
    - apply path_sigma_hprop. refine (_ @ h). simpl.
      refine (_ @ transport_exp_finite_sum e (B1.2.1)).
      destruct B1 as [[B1 [n1 e1]] [f1 emb1]].
      destruct B2 as [[B2 [n2 e2]] [f2 emb2]]. simpl in *.
      apply (ap pr1
                (transport_sigma
                (A := {fB : Type & Finite fB}) (B := fun B => B.1 -> A) (C := fun B f => IsEmbedding f)
                (path_sigma_hprop (B1; {| fcard := n1; merely_equiv_fin := e1 |})
                                  (B2; {| fcard := n2; merely_equiv_fin := e2 |}) (path_universe_uncurried e)) (f1; emb1))).
  Defined.             

  Local Definition project_to_dprop (X Y : Type) : X + Y -> DProp :=
    fun xy => if xy then True else False.

  (* Giving a finite subset is the same as giving a map A -> DProp *)
  Definition equiv_detachable_finite_subset {n : nat} {A : Finite_Types n} :
    (A -> DProp) <~> {B : {fB : Type & Finite fB} & {f : B.1 -> A & IsEmbedding f}}.
  Proof.
    srapply @equiv_adjointify.
    { intro P. srapply @exist.
      - exists {a : A & P a}.  exact _.
      - simpl.
        exists pr1. intro a.
        apply (trunc_equiv' (P a)).
        + apply (hfiber_fibration a P).
        + exact _. }
    { intros [[B fB] [f isemb_f]].
      apply ((project_to_dprop _ _) o (split_range B A f isemb_f)). }
    - intros [[B fB] [f isemb_f]].
      srapply @path_finite_subsets_sum.
      + cbn.
        srapply @equiv_adjointify.
        { intros [a h]. simpl in f.
          destruct (detachable_image_finite f a) as [fib | nfib]; cbn in *.
          - exact fib.1. - destruct h. }
        { intro b. exists (f b). simpl in f.
          destruct (detachable_image_finite f (f b)) as [fib | nfib]; cbn.
          - exact tt. - apply nfib. exists b. reflexivity. }
        * intro b. cbn. simpl in f.
          destruct (detachable_image_finite f (f b)) as [fib | nfib].
          { destruct fib as [b' p]; cbn.
            apply (isinj_embedding f isemb_f). exact p. }
          apply Empty_rec. apply nfib. exists b. reflexivity.
        * cbn. intros [a h].
          apply path_sigma_hprop. cbn. simpl in f.
          destruct (detachable_image_finite f a) as [fib | nfib]; cbn in *.
          { destruct fib as [a' p]. cbn. exact p. } destruct h.
      + reflexivity.
    - intro B.
      apply path_arrow. intro a. cbn.
      destruct (detachable_image_finite pr1 a) as [fib | nfib]; cbn.
      + destruct fib as [[a' b] p].
        apply path_dprop. apply path_universe_uncurried. cbn.
        apply equiv_inverse.
        srapply @equiv_contr_unit. apply contr_inhabited_hprop.
        * exact _.
        * exact (transport B p b).
      + apply path_dprop. apply path_universe_uncurried. apply equiv_inverse.
        apply (if_not_hprop_then_equiv_Empty).
        * exact _.
        * intro b. apply nfib.
          apply (hfiber_fibration a B b).
  Defined.

  Definition equiv_finite_subset {n : nat} {A : Finite_Types n} :
    {k : nat & Finite_Subsets k A} <~> {B : {fB : Type & Finite fB} & {f : B.1 -> A & IsEmbedding f}}.
  Proof.
    srapply @equiv_adjointify.
    - intros [k [B f]]. simpl in f.
      srapply @exist.
      + exists B. exact _.
      + simpl. exact f.
    - intros [[B [k eB] f]]. simpl in f.
      exists k. exists (B; eB). exact f.
    - intros [[B [k eB] f]]. reflexivity.
    - intros [k [B f]]. reflexivity.
  Defined.
      
    

  (* Then we can show that the type of finite subsets is finite *)
  Global Instance finite_finite_subsets {n : nat} {A : Finite_Types n} : Finite {k : nat & Finite_Subsets k A}.
  Proof.
    apply (finite_equiv' (A -> DProp)).
    - exact ((equiv_finite_subset)^-1 oE equiv_detachable_finite_subset).
    - apply finite_forall.
      + exact _.
      + intro a. exact _.
  Qed.
  
  Definition equiv_detachable_finite_fix (k : nat) {n : nat} {A : Finite_Types n} :
    Finite_Subsets k A <~> {B : A -> DProp & fcard ({a : A & B a}) = k}.
  Proof.
    transitivity
      {B : {B : {fB : Type & Finite fB} & {f : B.1 -> A & IsEmbedding f}} & @fcard _ B.1.2 = k}.
    { 
      transitivity {B : {k' : nat & Finite_Subsets k' A} & B.1 = k}.
      - srapply @equiv_adjointify.
        { intro B. exists (k; B). reflexivity. }
        { intros [[k' B] []]. exact B. }
        { intros [[k' B] []]. reflexivity. }
        { intro B. reflexivity. }
      - apply (equiv_functor_sigma' equiv_finite_subset).
        intros [k' B]. reflexivity. }
    - apply equiv_inverse.
      apply (equiv_functor_sigma' equiv_detachable_finite_subset).
      intro B. reflexivity.
  Defined.

  (* Now we get that the parts of finite subsets are finite *)
  Definition finite_finite_subset_fix (k : nat) {n : nat} {A : Finite_Types n} :
    Finite (Finite_Subsets k A).
  Proof.
    apply (finite_equiv' {B : A -> DProp & fcard ({a : A & B a}) = k}).
    - apply equiv_inverse. simpl. apply equiv_detachable_finite_fix.
    - apply (finite_detachable_subset); intro B; exact _.
  Defined.

  (* This result is perhaps belonging somewhere else. . . *)
  Definition compose_embedding {X Y Z : Type} (f : X -> Y) (g : Y -> Z) :
     IsEmbedding f -> IsEmbedding g -> IsEmbedding (g o f).
  Proof.
    unfold IsEmbedding. intros embf embg. intro z.
    apply (trunc_equiv' _ (hfiber_compose f g z)^-1).
  Qed.

  
  Definition include_subset {n k: nat} {A : Finite_Types n} {B : Finite_Subsets k A} {l : nat}
             : Finite_Subsets l B -> Finite_Subsets l A.
  Proof.
    unfold Finite_Subsets.
    intros [I [b emb_b]]. destruct B as [B [a emb_a]]. simpl in b.
    exists I. exists (a o b). apply compose_embedding.
    - exact emb_b.
    - exact emb_a.
  Defined.

  (* Definition include_subset_in_last {n k : nat} {A : Finite_Types n} {B : Finite_Subsets k A} : *)
  (*   B -> A. *)
  (* Proof. *)
  (*   exact B.2.1. *)
  (* Defined. *)

  Definition incl {n k : nat} {A : Finite_Types n} (B : Finite_Subsets k A) :
    Embedding B A := B.2.

  (* Coercion include_subset_in_last : Finite_Subsets >-> Funclass. *)

  (* Definition check (n k: nat) (A : Finite_Types n) (B : Finite_Subsets k A): B -> A. apply B. *)
  

  

  Definition compliment {n k : nat} (A : Finite_Types n) :
    Finite_Subsets k A -> Finite_Subsets (n - k) A.
  Proof.
    intros [B [f embf]].
    srapply @exist.
    - exists ({a : A & not (hfiber f a)}).
      srapply @finite_eq_fcard. 
      apply fcard_compliment. exact embf.
    - simpl.
      exists pr1.
      apply embed_compliment.
  Defined.

  Definition equiv_sum_compliment {n k : nat} {A : Finite_Types n} (B : Finite_Subsets k A) :
    B + (compliment A B) <~> A.
  Proof.
    destruct B as [B [f embf]]. simpl.
    refine ((split_range B A f embf)^-1 oE _).
    srapply @equiv_functor_sum'.
    - apply equiv_image. exact embf.
    - reflexivity.
  Defined.

  Definition sum_compliment_subset {n k : nat} {A : Finite_Types n} (B : Finite_Subsets k A) :
      Finite_Subsets n A.
  Proof.
    srapply @exist.
    - exists (B + (compliment A B)). srapply @finite_eq_fcard.
      change (fcard (Fin n)) with (fcard A).
      apply fcard_equiv'. apply equiv_sum_compliment.
    - exists (equiv_sum_compliment B).
      apply equiv_is_embedding. exact _.
  Defined.

  (* A as a subset of itself *)
  Definition last_subset {n : nat} (A : Finite_Types n) :
    Finite_Subsets n A.
  Proof.
    exists A. exists idmap. apply equiv_is_embedding. exact _.
  Defined.
  
  Definition eq_sum_compliment {n k : nat} {A : Finite_Types n} (B : Finite_Subsets k A) :
    sum_compliment_subset B = last_subset A.
  Proof.
    srapply @path_finite_subsets.
    - apply equiv_sum_compliment.
    - apply path_arrow. intro a. simpl.
      destruct B as [B [f embf]]. simpl.
      destruct (detachable_image_finite f a) as [[a' p] |].
      + exact p.
      + simpl. reflexivity.
  Defined.

  
End Finite_Subsets.


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
    - apply finite_sum.
      + exact IHm1.
      + exact IHm2.
  Defined.

  Definition magma_canon (n : nat)
    : Magma (Fin n).
  Proof.
    induction n.
    - exact m0.
    - apply m_sum.
      + apply IHn.
      + exact m1.
  Defined.
End Magma.


Require Import nat_lemmas.

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
      induction i.
      + simpl in Hi. destruct Hi. reflexivity.
      + reflexivity.
  Defined.

  
  Open Scope nat.

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

  (* General pointed finite sets of cardinality n *)
  Definition Pointed_Finite (n : nat) := {A : Type & merely (A <~> pFin n)}.

End Pointed_Finite.


Section Cosimplicial_maps.
  Local Open Scope nat.
   Notation "[ n ]" := {m : nat | m <= n}.
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
      + rewrite H. apply leq_refl.
      + apply j_leq_Sn.
  Defined.

End Cosimplicial_maps.






  
    
  
