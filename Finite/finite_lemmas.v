Require Import HoTT.
Require Import trunc_lemmas.
Require Import sigma_lemmas.
Require Import equiv_lemmas.
Require Import category_lemmas.
Require Import UnivalenceAxiom.







Definition Embedding (A B : Type) := {f : A -> B & IsEmbedding f}.
Definition fun_of_emb (A B : Type) : Embedding A B -> (A -> B) := pr1.
Coercion fun_of_emb : Embedding >-> Funclass.


Definition equiv_fin2_bool : Fin 2 <~> Bool.
Proof.
  srapply @equiv_adjointify.
  { intros [[[] | []] | []].
    - exact true.
    - exact false. }
  { intros  [ | ].
    - exact (inl (inr tt)).
    - exact (inr tt). }
  - intros [ | ] ;reflexivity.
  - intros [[[] | []] | []]; reflexivity.
Defined.


(* The type of decidable propositions is finite *)
Global Instance finite_dprop : Finite DProp.
Proof.
  refine (finite_equiv' (Fin 2) _ _).
  refine (_ oE equiv_fin2_bool).
  apply equiv_inverse. apply equiv_dprop_to_bool.
Qed.


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

Lemma finite_eq_fcard (A B : Type) {fA : Finite A} {fB : Finite B} :
  fcard A = fcard B -> merely (A <~> B).
Proof.
  destruct fA as [m eA]. destruct fB as [n eB].
  strip_truncations. intro p. apply tr. simpl in p. destruct p.
  exact (eB^-1 oE eA).
Qed.

Section Sum_Finite.
  Definition finl (m n : nat) : Fin m -> Fin (n + m).
  Proof.
    induction n.
    - exact idmap.
    - simpl.
      exact (inl o IHn).
  Defined.

  Definition finr (m n : nat) : Fin n -> Fin (n + m).
  Proof.
    induction n.
    - apply Empty_rec.
    - simpl.
      exact (functor_sum IHn idmap).
  Defined.

  Definition finsum (m n : nat) : Fin m + Fin n -> Fin (n+m).
  Proof.
    intros [i | j].
    - exact (finl _ _ i).
    - exact (finr _ _ j).
  Defined.

  Global Instance isequiv_finsum {m n : nat} : IsEquiv (finsum m n).
  Proof.
    induction n.
    - simpl.
      assert (h : finsum m 0 = (sum_empty_r (Fin m))).
      { apply path_arrow.
        intros [x | []]; reflexivity. }
      rewrite h.  exact _.
    - assert (h : finsum m n.+1 =
                  (functor_sum (finsum m n) idmap) o (equiv_sum_assoc (Fin m) (Fin n) Unit)^-1).
      { apply path_arrow.
        intros [i | [i | []]]; reflexivity. }
      rewrite h.
      apply (isequiv_compose (g := (functor_sum (B := Unit) (finsum m n) (idmap)))).
  Qed.

  (* TODO: rename to equiv_finsum *)
  Definition fin_resp_sum (m n : nat) : (Fin m) + (Fin n) <~> Fin (n + m) :=
    BuildEquiv _ _ (finsum m n) isequiv_finsum.

  (* Definition fin_resp_sum_last (m n : nat) : *)
  (*   fin_resp_sum m n.+1 (inr (inr tt)) = (inr tt) := idpath. *)
End Sum_Finite.

Require Import B_Aut.
Section Finite_Types.
  Definition Finite_Types  (n : nat) := B_Aut (Fin n).

  Definition type_of {n : nat} (A : Finite_Types n) := pr1 A.
  Global Coercion type_of : Finite_Types >-> Sortclass.
  Global Instance finite_finite_type {n : nat} (A : Finite_Types n) : Finite A := 
    Build_Finite A.1 n A.2.

  Definition fin_decompose :
    {n : nat & Finite_Types n} <~> {A : Type & Finite A}.
  Proof.
    srapply @equiv_adjointify.
    - intros [n A]. exists A. exact _.
    - intros [A [n e]]. exact (n; (A; e)).
    - intros [A [n e]]. simpl.
      apply path_sigma_hprop. reflexivity.
    - intros [n A]. simpl. reflexivity.
  Defined.
    
  

  (* Canonical finite types *)
  Definition canon (n : nat) : Finite_Types n := point _.    

  (* A detachable subset of a finite set has smaller cardinal *)
  Definition leq_card_subset {n : nat} (A : Finite_Types n) (P : A -> Type)
             (isprop_P : forall a : A, IsHProp (P a)) (isdec_P : forall a : A, Decidable (P a)) :
    (fcard {a : A & P a} <= fcard A)%nat.
  Proof.  
    destruct A as [A eA]. simpl in P, isprop_P, isdec_P. 
    apply (leq_inj_finite pr1).
    unfold IsEmbedding. simpl. intro a.
    apply (trunc_equiv' (P a) ).
    - apply hfiber_fibration.
    - apply isprop_P.
  Qed.

  (* Plus one for finite types *)
  Definition add_one {n : nat} : Finite_Types n -> Finite_Types n.+1.
  Proof.
    intros [A H].
    exists (A + Unit).
    (* apply (Build_Finite_Types (A + Unit)). *)
    strip_truncations.
    apply tr. (* apply path_universe_uncurried. *)
    (* exact (equiv_functor_sum' ((equiv_path_universe A (Fin n))^-1 H) equiv_idmap). *)
    exact (equiv_functor_sum' H equiv_idmap).
  Defined.

  (* Path types in various "types of finite types" *)
  Definition path_finite_types_fix (n : nat) (s t : Finite_Types n):
    (s <~> t) <~> s = t :=
    equiv_path_sigma_hprop _ _ oE equiv_path_universe _ _.

  Definition path_finite_types_sum (s t : {A : Type & Finite A}) :
    (s.1 <~> t.1) <~> s = t :=
    equiv_path_sigma_hprop _ _ oE equiv_path_universe _ _.

  Definition path_finite_types (s t : {n : nat & Finite_Types n}) :
    (s.2 <~> t.2) <~> s = t.
  Proof.  
    refine ((equiv_ap fin_decompose s t)^-1 oE _).
    destruct s as [m [A eA]]. destruct t as [n [B eB]]. simpl.
    exact (path_finite_types_sum (A; finite_finite_type (A; eA)) (B; finite_finite_type (B; eB))).
  Defined.
  
  Definition transport_exp_finite_fix (n : nat) {X : Type} {A B : Finite_Types n} (e : A <~> B) (x : A -> X):
    transport (fun I : Finite_Types n => I -> X) (path_finite_types_fix n A B e) x = x o e^-1.
  Proof.
    refine (ap10 (transport_pr1_path_sigma_uncurried (pr1^-1 (path_universe_uncurried e))
                                                     (fun A : Type => A -> X)) x @ _).
    exact (transport_exp X A B e x).
  Defined.

  Definition transport_exp_finite_sum {X : Type} {A B : {A : Type & Finite A}} (e : A.1 <~> B.1) (x : A.1 -> X) :
    transport (fun I : {A : Type & Finite A} => I.1 -> X) (path_finite_types_sum A B e) x = x o e^-1.
  Proof.
    refine (ap10 (transport_pr1_path_sigma_uncurried (pr1^-1 (path_universe_uncurried e))
                                                     (fun A : Type => A -> X)) x @ _).
    exact (transport_exp X A.1 B.1 e x).
  Defined.

    Lemma path_sigma_hprop_compose {A : Type} {P : A -> Type} {isprop : forall a : A, IsHProp (P a)}
        (x y z: { a : A & P a}) (p : x.1 = y.1) (q : y.1 = z.1) :
    path_sigma_hprop _ _ (p @ q) = (path_sigma_hprop _ _ p) @ (path_sigma_hprop _ _ q).
  Proof.
    destruct x as [x1 x2]. destruct y as [y1 y2]. destruct z as [z1 z2]. simpl in p,q.
    destruct q. destruct p. cbn.
    destruct (center _ (isprop x1 x2 z2)).
    destruct (center _ (isprop x1 x2 y2)).    
    refine (path_sigma_hprop_1 _ @ _).
    apply inverse.
    apply (concat2 (path_sigma_hprop_1 (x1; x2)) (path_sigma_hprop_1 (x1; x2))).
  Defined.

  Lemma path_finite_types_fix_compose (m : nat) (A B C : Finite_Types m)
        (e1 : A <~> B) (e2 : B <~> C) :
    path_finite_types_fix m _ _ (e2 oE e1) =
    (path_finite_types_fix m _ _ e1) @ (path_finite_types_fix m _ _ e2).
  Proof.
    unfold path_finite_types_fix. simpl.
    refine (ap (path_sigma_hprop A C) (path_universe_compose e1 e2) @ _).
    apply path_sigma_hprop_compose.
  Defined.                  

  (* This is more complicated, not sure if it is needed? *)
  Lemma path_finite_types_compose (A B C : {n : nat & Finite_Types n})
        (e1 : A.2 <~> B.2) (e2 : B.2 <~> C.2) :
    path_finite_types _ _ (e2 oE e1) = (path_finite_types _ _ e1) @ (path_finite_types _ _ e2).
  Proof.
    destruct A as [l [A fA]].
    destruct B as [m [B fB]].
    destruct C as [n [C fC]].
    simpl in e1, e2.
    unfold path_finite_types.
    unfold path_finite_types_sum.
    unfold pr1.

    change
      (((equiv_ap fin_decompose (?x; (?a; ?fa)) (?y; (?b; ?fb)))^-1
       oE (equiv_path_sigma_hprop (?a; finite_finite_type (?a; ?fa)) (?b; finite_finite_type (?b; ?fb))
       oE equiv_path_universe ?a ?b)) ?e)
    with
    ((equiv_ap fin_decompose (x; (a; fa)) (y; (b; fb)))^-1
      (path_sigma_hprop (a; finite_finite_type (a; fa)) (b; finite_finite_type (b; fb))
      (path_universe e))).
    refine (ap ( (equiv_ap fin_decompose (l; (A; fA)) (n; (C; fC)))^-1               
                 o (path_sigma_hprop (A; finite_finite_type (A; fA)) (C; finite_finite_type (C; fC))))
               (path_universe_compose e1 e2) @ _).
    refine (ap (equiv_ap fin_decompose (l; (A; fA)) (n; (C; fC)))^-1
               (path_sigma_hprop_compose
                  (A; finite_finite_type (A; fA))
                  (B; finite_finite_type (B; fB))
                  (C; finite_finite_type (C; fC))
                  (path_universe e1) (path_universe e2)) @ _).
    cut (forall (a b c: {n : nat & Finite_Types n})
                (p : fin_decompose a = fin_decompose b) (q : fin_decompose b = fin_decompose c),
            (equiv_ap fin_decompose a c)^-1 (p @ q) =
            ((equiv_ap fin_decompose a b)^-1 p) @ ((equiv_ap fin_decompose b c)^-1 q)).
    { intro H. apply H. }
    clear l A fA m B fB n C fC e1 e2.
    intros A B C p q.
    (* unfold equiv_ap. *)
    change ((equiv_ap fin_decompose ?x ?y)^-1)
           with
           (fun q : fin_decompose x = fin_decompose y =>
              ((eissect fin_decompose x)^ @ ap fin_decompose^-1 q) @ eissect fin_decompose y).
    hnf.
    destruct (eissect fin_decompose C).
    destruct (eissect fin_decompose A).
    destruct (eissect fin_decompose B). hott_simpl.
    apply ap_pp.
  Qed.

  Definition path_finite_types_1 (A : {n : nat & Finite_Types n}) :
      path_finite_types A A equiv_idmap = idpath.
  Proof.
    destruct A as [n [A fA]].
    unfold path_finite_types.
    unfold path_finite_types_sum.
    unfold pr1.
    change
      (((equiv_ap fin_decompose (n; (A; fA)) (n; (A; fA)))^-1
        oE (equiv_path_sigma_hprop (A; finite_finite_type (A; fA)) (A; finite_finite_type (A; fA))
        oE equiv_path_universe A A))
         equiv_idmap)
      with
      ((equiv_ap fin_decompose (n; (A; fA)) (n; (A; fA)))^-1
          (path_sigma_hprop (A; finite_finite_type (A; fA)) (A; finite_finite_type (A; fA))
             (@path_universe _ A A equiv_idmap _))).
    refine (ap ((equiv_ap fin_decompose (n; (A; fA)) (n; (A; fA)))^-1 o
               (path_sigma_hprop (A; finite_finite_type (A; fA)) (A; finite_finite_type (A; fA))))
               (path_universe_1) @ _).
    refine (ap ((equiv_ap fin_decompose (n; (A; fA)) (n; (A; fA)))^-1)
               (path_sigma_hprop_1 _) @ _).
    change ((equiv_ap fin_decompose ?x ?y)^-1)
           with
           (fun q : fin_decompose x = fin_decompose y =>
              ((eissect fin_decompose x)^ @ ap fin_decompose^-1 q) @ eissect fin_decompose y).
    hnf.
    destruct (eissect fin_decompose (n; (A; fA))). reflexivity.
  Qed.     
 

  (* This should more or less follow from baut_ind_hset (except that is only for P: Type -> Type*)
  Definition BSigma_ind_hSet (P : forall n : nat, Finite_Types n -> Type)
             {isset_P : forall (n : nat) (s : Finite_Types n), IsHSet (P n s)}
             (pt : forall n : nat, P  n (canon n))
             (wd : forall (n : nat) (e : Fin n <~> Fin n),
                 transport (P n) (path_finite_types_fix n (canon n) (canon n) e) (pt n) = pt n) :
    forall (n : nat) (s : Finite_Types n), P n s.
  Proof.
    intros n s.
    apply (@pr1 (P n s) (fun p : P n s => forall e' : Fin n <~> s,
                           transport (P n) (path_finite_types_fix n (canon n) s e') (pt n) = p)).
    assert (isprop_goal : forall s' : Finite_Types n, IsHProp
                                                      {p : P n s' &
                                                           forall e' : Fin n <~> s',
                                                             transport (P n) (path_sigma_hprop (canon n) s' (path_universe_uncurried e'))
                                                                       (pt n) = p}).
    { destruct s' as [A eA].
      strip_truncations. apply trunc_sigma'.
      - intro p. apply trunc_forall.
      - intros p q.
        apply (contr_inhabited_hprop _).
        destruct p as [p fp]. destruct q as [q fq]. simpl. simpl in fp. simpl in fq.      
        exact ((fp (equiv_inverse eA))^ @ (fq (equiv_inverse eA))). }
    destruct s as [A eA]. strip_truncations.
    destruct (path_finite_types_fix n (canon n) (A; (tr eA)) (equiv_inverse eA)). simpl.
    exact (pt n; wd n).
  Defined.


End Finite_Types.


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


Section Fin_Transpose.
  Definition fin_transpose {n : nat} (x y : Fin n)
  : Fin n <~> Fin n.
  Proof.
    induction n.
    - destruct x.
    - destruct y as [y | []].
      + destruct x as [x | []].
        * exact (IHn x y +E 1).
        * exact (fin_transpose_last_with n (inl y)).
      + exact (fin_transpose_last_with n x).
  Defined.

  (* Definition fin_transpose_is_withlast_r {n : nat} (x : Fin n.+1) : *)
  (*   fin_transpose x (inr tt) = fin_transpose_last_with n x := idpath. *)

  (* Definition fin_transpose_is_withlast_l {n : nat} (y : Fin n.+1) : *)
  (*   fin_transpose (n := n.+1) (inr tt) y = fin_transpose_last_with n y. *)
  (* Proof. *)
  (*   destruct y as [y | []]; reflexivity. *)
  (* Defined. *)

  Definition fin_transpose_same_is_id {n : nat} (x : Fin n) :
    fin_transpose x x == idmap.
  Proof.
    intro i.
    induction n.
    { destruct x. }
    destruct x as [x | []].
    - simpl. destruct i as [i | []].
      + apply (ap inl). apply IHn.
      + reflexivity.
    - simpl. apply fin_transpose_last_with_last_other.
  Defined.

  Definition fin_transpose_invol {n : nat} (x y : Fin n) :
    fin_transpose x y o fin_transpose x y == idmap.
  Proof.
    induction n.
    {destruct x. }
    intro i. ev_equiv.
    destruct y as [y | []].
    - destruct x as [x | []].
      + simpl. destruct i as [i | []].
        { simpl. apply (ap inl). apply IHn. }
        reflexivity.
      + simpl. apply fin_transpose_last_with_invol.
    - simpl. apply fin_transpose_last_with_invol.
  Defined.

  Definition fin_transpose_sym {n : nat} (x y : Fin n) :
    fin_transpose x y == fin_transpose y x.
  Proof.
    induction n.
    { destruct x. }
    intro i.
    destruct y as [y | []]; destruct x as [x | []]; try reflexivity.
    - simpl. destruct i as [i | []].
      + apply (ap inl). apply IHn.
      + reflexivity.
  Defined.

  Definition fin_transpose_beta_r {n : nat} (x y : Fin n) :
    fin_transpose x y y = x.
  Proof.
    induction n.
    { destruct x. }
    destruct y as [y | []]; destruct x as [x | []]; try (apply fin_transpose_last_with_last).
    - simpl. apply (ap inl). apply IHn.
    - simpl. apply fin_transpose_last_with_with.
  Defined.

  Definition fin_transpose_beta_l {n : nat} (x y : Fin n) :
    fin_transpose x y x = y.
  Proof.
    refine (fin_transpose_sym x y x @ _).
    apply fin_transpose_beta_r.
  Defined.

  Definition fin_transpose_other {n : nat} (x y : Fin n) (i : Fin n):
    (i <> x) -> (i <> y) -> fin_transpose x y i = i.
  Proof.
    intros n_x n_y.
    induction n.
    { destruct x.  }
    destruct y as [y | []].
    - destruct x as [x | []].
      + simpl. destruct i as [i | []].
        * apply (ap inl). apply IHn.
          { intro p. apply n_x. exact (ap inl p). }
          { intro p. apply n_y. exact (ap inl p). }
        * reflexivity.
      + simpl. destruct i as [i | []].
        * apply fin_transpose_last_with_rest.
          intro p. apply n_y. exact p^.
        * destruct (n_x idpath).
    - simpl. destruct i as [i | []].
      + apply fin_transpose_last_with_rest.
        intro p. apply n_x. exact p^.
      + destruct (n_y idpath).
  Defined.

  (* either i = x, i = y, or equal to neither *)
  Definition decompose_fin_n {n : nat} (x y : Fin n) (i : Fin n) :
    (i = x) + (i = y) + ((i <> x) * (i <> y)).
  Proof.
    destruct (decidablepaths_fin n i x).
    - exact (inl (inl p)).
    - destruct (decidablepaths_fin n i y).
      + apply inl. exact (inr p).
      + apply inr. exact (n0, n1).
  Qed.    

  Definition natural_fin_transpose {n : nat} (x y : Fin n) (e : Fin n <~> Fin n) :
    e o (fin_transpose x y) == fin_transpose (e x) (e y) o e.
  Proof.
    intro i. ev_equiv.
    destruct (decompose_fin_n x y i) as [[p | p] |[n_x n_y] ].
    - rewrite p.
      rewrite fin_transpose_beta_l.
      apply inverse. apply fin_transpose_beta_l.
    - rewrite p.
      rewrite fin_transpose_beta_r.
      apply inverse. apply fin_transpose_beta_r.
    - rewrite (fin_transpose_other x y i n_x n_y).
      apply inverse. apply fin_transpose_other.
      + intro p. apply n_x. apply (equiv_inj e p).
      + intro p. apply n_y. apply (equiv_inj e p).
  Qed.

  Definition fin_transpose_eta {n : nat} (x y : Fin n) (e : Fin n -> Fin n) :
    (e x = y) -> (e y = x) -> (forall i : Fin n, i <> x -> i <> y -> e i = i) ->
    fin_transpose x y == e.
  Proof.
    intros p q neq.
    intro i.
    destruct (decidablepaths_fin n i x) as [eq_x | neq_x].
    - rewrite eq_x.
      rewrite p.
      apply fin_transpose_beta_l.
    - destruct (decidablepaths_fin n i y) as [eq_y | neq_y].
      + rewrite eq_y.  rewrite q.
        apply fin_transpose_beta_r.
      + rewrite (neq i neq_x neq_y).
        apply (fin_transpose_other _ _ _ neq_x neq_y).
  Qed.
      
    
End Fin_Transpose.

Section Sigma2.
  Definition sigma2_fixlast (σ : Fin 2 <~> Fin 2) :
    (σ (inr tt) = inr tt) -> σ == equiv_idmap.
  Proof.
    intro p.
    intros [[[] | []] | []]; simpl.
    - recall (σ ((inl (inr tt)))) as x eqn:q.
      rewrite q.
      destruct x as [[[] | []] | []].
      + reflexivity.
      + destruct (inr_ne_inl tt (inr tt) (equiv_inj σ (p @ q^))). (* absurd case *)
    - exact p.
  Qed.

  Definition twist2 : Fin 2 <~> Fin 2 :=
    fin_transpose (n := 2) (inl (inr tt)) (inr tt).

  Definition twist2_inv : equiv_inverse twist2 = twist2.
  Proof.
    apply path_equiv. reflexivity.
  Qed.

  Definition sigma2_notfixlast (σ : Fin 2 <~> Fin 2) :
    (σ (inr tt) = inl (inr tt)) -> σ == twist2.
  Proof.
    intro p.
    intros [[[] | []] | []]; simpl.
    - recall (σ ((inl (inr tt)))) as x eqn:q.
      rewrite q.
      destruct x as [[[] | []] | []].
      + destruct (inr_ne_inl tt (inr tt) (equiv_inj σ (p @ q^))). (* absurd case *)
      + reflexivity.
    - exact p.
  Qed.

  Definition symm_sigma2 (σ1 σ2 : Fin 2 <~> Fin 2) :
    σ1 oE σ2 = σ2 oE σ1.
  Proof.
    recall (σ1 (inr tt)) as x eqn:p.
    destruct x as [[[] | []] | []].
    - rewrite (path_equiv (path_forall _ _ (sigma2_notfixlast σ1 p))).
      recall (σ2 (inr tt)) as y eqn:q.
      destruct y as [[[] | []] | []].
      + rewrite (path_equiv (path_forall _ _ (sigma2_notfixlast σ2 q))).
        reflexivity.
      + rewrite (path_equiv (path_forall _ _ (sigma2_fixlast σ2 q))).
        rewrite ecompose_e1. rewrite ecompose_1e. reflexivity.
    - rewrite (path_equiv (path_forall _ _ (sigma2_fixlast σ1 p))).
      rewrite ecompose_e1. rewrite ecompose_1e. reflexivity.
  Qed.    

End Sigma2.

Section Restrict_Equivalence.
  Context {n : nat}
          {A : Type}
          (e : A + Unit <~> Fin n.+1)
          (fixlast : e (inr tt) = inr tt).

  Lemma not_inr_is_inl {X Y : Type}
        (x :  X + Y)
        (not_inr : forall y : Y, x <> inr y)
    : is_inl x.
  Proof.
    destruct x as [x | y'].
    - exact tt.
    - destruct (not_inr y' idpath).
  Qed.
  
  Lemma fix_last_is_inr :
    forall u : Unit, is_inr (e (inr u)).
  Proof.
    intros []. rewrite fixlast.
    exact tt.
  Qed.

  Lemma fix_last_is_inl :
    forall a : A, is_inl (e (inl a)).
  Proof.
    intro a. apply not_inr_is_inl.
    intros []. rewrite <- fixlast.
    intro q. apply (inl_ne_inr a tt).
    exact (equiv_inj e q).
  Qed.

  Definition equiv_restrict :=
    equiv_unfunctor_sum_l e fix_last_is_inl fix_last_is_inr.

  Definition swap_last := fin_transpose (e (inr tt)) (inr tt).

  Lemma swap_fix_last :
    (swap_last oE e) (inr tt) = inr tt.
  Proof.
    unfold swap_last. ev_equiv. apply fin_transpose_last_with_with.
  Qed.

 
  Definition equiv_restrict_eta :
    equiv_restrict +E equiv_idmap == e.
  Proof.
    intro x.
    refine (_ @ unfunctor_sum_eta _ fix_last_is_inl fix_last_is_inr x).
    destruct x as [x | []]; try reflexivity.   
    simpl.
    destruct (unfunctor_sum_r e fix_last_is_inr tt).
    reflexivity.
  Qed.      
End Restrict_Equivalence.

  Definition equiv_restrict_plus1 {n : nat} {A : Type} (e : A <~> Fin n) :
    equiv_restrict (e +E equiv_idmap) idpath == e.
  Proof.
    intro a.
    apply (path_sum_inl Unit).
    refine (unfunctor_sum_l_beta _ _ a ).
  Qed.

  Definition inj_equiv_plus1 {n : nat} {A : Type} (e1 e2 : A <~> Fin n) :
    (e1 +E (equiv_idmap Unit)) == (e2 +E (equiv_idmap Unit)) -> e1 == e2.
  Proof.
    intro H.
    intro x.
    apply (path_sum_inl Unit). apply (H (inl x)).
  Qed.

  Definition fin_decompose_ind {m n : nat} (P : Fin (n+m) -> Type)
             (Pl : forall i : Fin m, P (finl _ _ i))
             (Pr : forall i : Fin n, P (finr _ _ i))
    : forall i : Fin (n+m), P i.
  Proof.
    cut (forall j : (Fin m)+(Fin n), P (finsum m n j)).
    - intro f.
      intro i.
      apply (transport P (eisretr (finsum m n) i)).
      exact (f ((finsum m n)^-1 i)).
    - intros [j | j].
      + exact (Pl j).
      + exact (Pr j).
  Defined.


  Definition block_sum {m n: nat} (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n) :
    Fin (n+m)%nat <~> Fin (n+m)%nat :=
    (fin_resp_sum m n) oE (e1 +E e2) oE (equiv_inverse (fin_resp_sum m n)).

  Definition block_sum_beta_finl {m n : nat} (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n)
             (i : Fin m) :
    block_sum e1 e2 (finl _ _ i) = finl _ _ (e1 i).
  Proof.
    unfold block_sum. ev_equiv.
    rewrite (eissect (fin_resp_sum m n) (inl i)). reflexivity.
  Qed.

  Definition block_sum_beta_finr {m n : nat} (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n)
             (i : Fin n) :
    block_sum e1 e2 (finr _ _ i) = finr _ _ (e2 i).
  Proof.
    unfold block_sum. ev_equiv.
    rewrite (eissect (fin_resp_sum m n) (inr i)). reflexivity.
  Qed.

  Definition block_sum_eta {m n : nat} 
             (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n)
             (g : Fin (n + m) <~> Fin (n + m))
             (eq_l : forall i : Fin m,
                 finl _ _(e1 i)
                 = g (finl _ _ i))
             (eq_r : forall i : Fin n,
                 (finr _ _ (e2 i)
                 = g (finr _ _ i)))
    : block_sum e1 e2 == g .
  Proof.
    unfold block_sum. intro j. revert j.
    apply fin_decompose_ind.
    - simpl. intro i. rewrite (eissect (fin_resp_sum m n) (inl i)).
      apply eq_l.
    - simpl. intro i. rewrite (eissect (fin_resp_sum m n) (inr i)).
      apply eq_r.
  Qed.

  Definition block_sum_compose {m n : nat}
             (e1 g1 : Fin m <~> Fin m)
             (e2 g2 : Fin n <~> Fin n) :
    block_sum (e1 oE g1) (e2 oE g2) ==
    (block_sum e1 e2) oE (block_sum g1 g2).
  Proof.
    apply block_sum_eta.
    - intro i. ev_equiv.
      rewrite block_sum_beta_finl.
      rewrite block_sum_beta_finl.
      reflexivity.
    - intro i. ev_equiv.
      rewrite block_sum_beta_finr.
      rewrite block_sum_beta_finr.
      reflexivity.
  Qed.

  Definition block_sum_plus1 {m n : nat}
             (e1 : Fin m <~> Fin m)
             (e2 : Fin n <~> Fin n) :
    block_sum (n := n.+1) e1 (e2 +E (equiv_idmap Unit)) == (block_sum e1 e2) +E (equiv_idmap Unit).
  Proof.
    
    apply block_sum_eta.
    - simpl.
      intro i. apply (ap inl).
      rewrite (eissect (finsum m n) (inl i)). reflexivity.
    - simpl. intros [i | []].
      + simpl. rewrite (eissect (finsum m n) (inr i)). reflexivity.
      + reflexivity.
  Qed.
  

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






  
    
  




