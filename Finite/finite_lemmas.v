Require Import HoTT.
Require Import trunc_lemmas.
Require Import sigma_lemmas.
Require Import equiv_lemmas.
Require Import category_lemmas.
Require Import UnivalenceAxiom.





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
  Definition Finite_Types  (n : nat) :=
    {A : Type & merely (A <~> Fin n)}.

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
  Definition canon (n : nat) : IsPointed (Finite_Types n) := (Fin n; tr equiv_idmap).    

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
  Definition path_finite_types_fix (n : nat) (s t : Finite_Types n)
    : (s <~> t) -> s = t
    :=  path_sigma_hprop _ _ o path_universe_uncurried.

  Global Instance isequiv_path_finite_types_fix (n : nat) (s t : Finite_Types n)
    : IsEquiv (path_finite_types_fix n s t)
    := isequiv_compose (f := path_universe_uncurried) (g := path_sigma_hprop _ _).

  Definition equiv_path_finite_types_fix (n : nat) (s t : Finite_Types n)
    : (s <~> t) <~> (s = t)
    := BuildEquiv _ _ (path_finite_types_fix n s t) (isequiv_path_finite_types_fix n s t).    

  Definition equiv_path_finite_types (s t : {A : Type & Finite A}) :
    (s.1 <~> t.1) <~> s = t :=
    equiv_path_sigma_hprop _ _ oE equiv_path_universe _ _.

  Definition equiv_path_BSigma (s t : {n : nat & Finite_Types n}) :
    (s.2 <~> t.2) <~> s = t.
  Proof.  
    refine ((equiv_ap fin_decompose s t)^-1 oE _).
    destruct s as [m [A eA]]. destruct t as [n [B eB]]. simpl.
    exact (equiv_path_finite_types (A; finite_finite_type (A; eA)) (B; finite_finite_type (B; eB))).
  Defined.
  
  Definition transport_exp_finite_fix (n : nat) {X : Type} {A B : Finite_Types n}
             (e : A <~> B) (x : A -> X)
    : transport (fun I : Finite_Types n => I -> X) (path_finite_types_fix n A B e) x = x o e^-1.
  Proof.
    refine (ap10 (transport_pr1_path_sigma_uncurried (pr1^-1 (path_universe_uncurried e))
                                                     (fun A : Type => A -> X)) x @ _).
    exact (transport_exp X A B e x).
  Defined.

  Definition transport_exp_finite_sum {X : Type} {A B : {A : Type & Finite A}}
             (e : A.1 <~> B.1) (x : A.1 -> X)
    : transport (fun I : {A : Type & Finite A} => I.1 -> X)
                (equiv_path_finite_types A B e) x = x o e^-1.
  Proof.
    refine (ap10 (transport_pr1_path_sigma_uncurried (pr1^-1 (path_universe_uncurried e))
                                                     (fun A : Type => A -> X)) x @ _).
    exact (transport_exp X A.1 B.1 e x).
  Defined.

  (* move *)
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

  Lemma path_finite_types_fix_id (m : nat) (A : Finite_Types m) :
    path_finite_types_fix m A A equiv_idmap = idpath.
  Proof.
    unfold path_finite_types_fix. apply moveR_equiv_M.
    simpl. unfold path_universe_uncurried.
    apply moveR_equiv_V.
    apply path_equiv. reflexivity.
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
  (* better proof in BSigma.v *)
  (* Lemma path_BSigma_compose (A B C : {n : nat & Finite_Types n}) *)
  (*       (e1 : A.2 <~> B.2) (e2 : B.2 <~> C.2) : *)
  (*   equiv_path_BSigma _ _ (e2 oE e1) *)
  (*   = (equiv_path_BSigma _ _ e1) @ (equiv_path_BSigma _ _ e2). *)
  (* Proof. *)
  (*   destruct A as [l [A fA]]. *)
  (*   destruct B as [m [B fB]]. *)
  (*   destruct C as [n [C fC]]. *)
  (*   simpl in e1, e2.  *)
  (*   unfold equiv_path_BSigma. *)
  (*   unfold equiv_path_finite_types. *)
  (*   unfold pr1. *)

  (*   change *)
  (*     (((equiv_ap fin_decompose (?x; (?a; ?fa)) (?y; (?b; ?fb)))^-1 *)
  (*      oE (equiv_path_sigma_hprop (?a; finite_finite_type (?a; ?fa)) (?b; finite_finite_type (?b; ?fb)) *)
  (*      oE equiv_path_universe ?a ?b)) ?e) *)
  (*   with *)
  (*   ((equiv_ap fin_decompose (x; (a; fa)) (y; (b; fb)))^-1 *)
  (*     (path_sigma_hprop (a; finite_finite_type (a; fa)) (b; finite_finite_type (b; fb)) *)
  (*     (path_universe e))). *)
  (*   refine (ap ( (equiv_ap fin_decompose (l; (A; fA)) (n; (C; fC)))^-1                *)
  (*                o (path_sigma_hprop (A; finite_finite_type (A; fA)) (C; finite_finite_type (C; fC)))) *)
  (*              (path_universe_compose e1 e2) @ _). *)
  (*   refine (ap (equiv_ap fin_decompose (l; (A; fA)) (n; (C; fC)))^-1 *)
  (*              (path_sigma_hprop_compose *)
  (*                 (A; finite_finite_type (A; fA)) *)
  (*                 (B; finite_finite_type (B; fB)) *)
  (*                 (C; finite_finite_type (C; fC)) *)
  (*                 (path_universe e1) (path_universe e2)) @ _). *)
  (*   cut (forall (a b c: {n : nat & Finite_Types n}) *)
  (*               (p : fin_decompose a = fin_decompose b) (q : fin_decompose b = fin_decompose c), *)
  (*           (equiv_ap fin_decompose a c)^-1 (p @ q) = *)
  (*           ((equiv_ap fin_decompose a b)^-1 p) @ ((equiv_ap fin_decompose b c)^-1 q)). *)
  (*   { intro H. apply H. } *)
  (*   clear l A fA m B fB n C fC e1 e2. *)
  (*   intros A B C p q. *)
  (*   (* unfold equiv_ap. *) *)
  (*   change ((equiv_ap fin_decompose ?x ?y)^-1) *)
  (*          with *)
  (*          (fun q : fin_decompose x = fin_decompose y => *)
  (*             ((eissect fin_decompose x)^ @ ap fin_decompose^-1 q) @ eissect fin_decompose y). *)
  (*   hnf. *)
  (*   destruct (eissect fin_decompose C). *)
  (*   destruct (eissect fin_decompose A). *)
  (*   destruct (eissect fin_decompose B). hott_simpl. *)
  (*   apply ap_pp. *)
  (* Qed. *)

  (* Definition path_finite_types_1 (A : {n : nat & Finite_Types n}) : *)
  (*     equiv_path_BSigma A A equiv_idmap = idpath. *)
  (* Proof. *)
  (*   destruct A as [n [A fA]]. *)
  (*   unfold equiv_path_BSigma. *)
  (*   unfold equiv_path_finite_types. *)
  (*   unfold pr1. *)
  (*   change *)
  (*     (((equiv_ap fin_decompose (n; (A; fA)) (n; (A; fA)))^-1 *)
  (*       oE (equiv_path_sigma_hprop (A; finite_finite_type (A; fA)) (A; finite_finite_type (A; fA)) *)
  (*       oE equiv_path_universe A A)) *)
  (*        equiv_idmap) *)
  (*     with *)
  (*     ((equiv_ap fin_decompose (n; (A; fA)) (n; (A; fA)))^-1 *)
  (*         (path_sigma_hprop (A; finite_finite_type (A; fA)) (A; finite_finite_type (A; fA)) *)
  (*            (@path_universe _ A A equiv_idmap _))). *)
  (*   refine (ap ((equiv_ap fin_decompose (n; (A; fA)) (n; (A; fA)))^-1 o *)
  (*              (path_sigma_hprop (A; finite_finite_type (A; fA)) (A; finite_finite_type (A; fA)))) *)
  (*              (path_universe_1) @ _). *)
  (*   refine (ap ((equiv_ap fin_decompose (n; (A; fA)) (n; (A; fA)))^-1) *)
  (*              (path_sigma_hprop_1 _) @ _). *)
  (*   change ((equiv_ap fin_decompose ?x ?y)^-1) *)
  (*          with *)
  (*          (fun q : fin_decompose x = fin_decompose y => *)
  (*             ((eissect fin_decompose x)^ @ ap fin_decompose^-1 q) @ eissect fin_decompose y). *)
  (*   hnf. *)
  (*   destruct (eissect fin_decompose (n; (A; fA))). reflexivity. *)
  (* Qed.      *)
 

  (* This should more or less follow from baut_ind_hset (except that is only for P: Type -> Type*)
  (* made redundant by deloop.v *)
  (* Definition BSigma_ind_hSet (P : forall n : nat, Finite_Types n -> Type) *)
  (*            {isset_P : forall (n : nat) (s : Finite_Types n), IsHSet (P n s)} *)
  (*            (pt : forall n : nat, P  n (canon n)) *)
  (*            (wd : forall (n : nat) (e : Fin n <~> Fin n), *)
  (*                transport (P n) (path_finite_types_fix n (canon n) (canon n) e) (pt n) = pt n) : *)
  (*   forall (n : nat) (s : Finite_Types n), P n s. *)
  (* Proof. *)
  (*   intros n s. *)
  (*   apply (@pr1 (P n s) (fun p : P n s => forall e' : Fin n <~> s, *)
  (*                          transport (P n) (path_finite_types_fix n (canon n) s e') (pt n) = p)). *)
  (*   assert (isprop_goal : forall s' : Finite_Types n, IsHProp *)
  (*                                                     {p : P n s' & *)
  (*                                                          forall e' : Fin n <~> s', *)
  (*                                                            transport (P n) (path_sigma_hprop (canon n) s' (path_universe_uncurried e')) *)
  (*                                                                      (pt n) = p}). *)
  (*   { destruct s' as [A eA]. *)
  (*     strip_truncations. apply trunc_sigma'. *)
  (*     - intro p. apply trunc_forall. *)
  (*     - intros p q. *)
  (*       apply (contr_inhabited_hprop _). *)
  (*       destruct p as [p fp]. destruct q as [q fq]. simpl. simpl in fp. simpl in fq.       *)
  (*       exact ((fp (equiv_inverse eA))^ @ (fq (equiv_inverse eA))). } *)
  (*   destruct s as [A eA]. strip_truncations. *)
  (*   destruct (path_finite_types_fix n (canon n) (A; (tr eA)) (equiv_inverse eA)). simpl. *)
  (*   exact (pt n; wd n). *)
  (* Defined. *)


End Finite_Types.










