Require Import HoTT.
Require Import trunc_lemmas.
Require Import sigma_lemmas.
Require Import equiv_lemmas.
Require Import category_lemmas.
Require Import UnivalenceAxiom.







Definition Embedding (A B : Type) := {f : A -> B & IsEmbedding f}.
Definition fun_of_emb (A B : Type) : Embedding A B -> (A -> B) := pr1.
Coercion fun_of_emb : Embedding >-> Funclass.

Definition τ : Fin 2 -> Fin 2.
Proof.
  unfold Fin.
    intros [[[] |[]] | [] ].
    + apply inr. exact tt.
    + apply inl. apply inr. exact tt.
Defined.

Definition τ_squared : τ o τ == idmap.
Proof.
  intros [[[] |[]] | [] ]; reflexivity.
Defined.  

Definition isequiv_τ : IsEquiv τ.
  apply (isequiv_adjointify τ τ); apply τ_squared.
Defined.

Definition equiv_τ : Fin 2 <~> Fin 2 :=
  BuildEquiv _ _ τ isequiv_τ.

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

(* Definition equiv_bool_autFin2 : *)
(*   Bool <~> (Fin 2 <~> Fin 2). *)
(* Proof. *)
(*   srapply @equiv_adjointify. *)
(*   - intros [ | ]. *)
(*     + exact equiv_idmap. *)
(*     + exact equiv_τ. *)
(*   - intro e. recall (e (inr tt)) as x eqn:p. *)
(*     destruct x as [[[] | []] |[] ]. *)
(*     + exact false. *)
(*     + exact true. *)
(*   - intro e.  *)
(*     destruct (e (inr tt)) as [[[] | []] |[] ]; simpl. *)
    
    


(* Definition equiv_Fin2_τ_or_id (e : Fin 2 <~> Fin 2) : *)
(*   (e = equiv_τ) + (e = 1%equiv). *)
(* Proof. *)
(*   recall (e (inr tt)) as x eqn:p. *)
(*   destruct x as [x | []]. *)
(*   - apply inl. *)
    
(*     equiv_bool_aut_bool *)

(* Definition comm_equiv_Fin2 (e1 e2 : Fin 2 <~> Fin 2) : *)



(* The type of decidable propositions is finite *)
Global Instance finite_dprop : Finite DProp.
Proof.
  refine (finite_equiv' (Fin 2) _ _).
  refine (_ oE equiv_fin2_bool).
  apply equiv_inverse. apply equiv_dprop_to_bool.
Qed.

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

Lemma finite_eq_fcard (A B : Type) {fA : Finite A} {fB : Finite B} :
  fcard A = fcard B -> merely (A <~> B).
Proof.
  destruct fA as [m eA]. destruct fB as [n eB].
  strip_truncations. intro p. apply tr. simpl in p. destruct p.
  exact (eB^-1 oE eA).
Qed.


Definition Fin_resp_sum (m n : nat) : Fin (m + n) <~> (Fin m) + (Fin n).
Proof.
  induction m.
  - (*m is 0*)
    apply equiv_inverse.
    apply (sum_empty_l (Fin n)).
  - simpl.
    refine (_ oE (equiv_functor_sum_r IHm)).
    refine ((equiv_sum_assoc (Fin m) Unit (Fin n))^-1 oE _ oE equiv_sum_assoc (Fin m) (Fin n) Unit).
    apply equiv_functor_sum_l.
    apply equiv_sum_symm.
Defined.



Section Finite_Types.
  Definition Finite_Types  (n : nat) :=
    {A : Type & merely (A <~> Fin n) }.

  Definition type_of {n : nat} (A : Finite_Types n) := pr1 A.
  Global Coercion type_of : Finite_Types >-> Sortclass.
  Global Instance finite_finite_type {n : nat} (A : Finite_Types n) : Finite A :=
    Build_Finite A.1 n A.2.

  Definition sum_finite :
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
  Definition canon (n : nat) : Finite_Types n := (Fin n; (tr 1%equiv)).    

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
    refine ((equiv_ap sum_finite s t)^-1 oE _).
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
      (((equiv_ap sum_finite (?x; (?a; ?fa)) (?y; (?b; ?fb)))^-1
       oE (equiv_path_sigma_hprop (?a; finite_finite_type (?a; ?fa)) (?b; finite_finite_type (?b; ?fb))
       oE equiv_path_universe ?a ?b)) ?e)
    with
    ((equiv_ap sum_finite (x; (a; fa)) (y; (b; fb)))^-1
      (path_sigma_hprop (a; finite_finite_type (a; fa)) (b; finite_finite_type (b; fb))
      (path_universe e))).
    refine (ap ( (equiv_ap sum_finite (l; (A; fA)) (n; (C; fC)))^-1               
                 o (path_sigma_hprop (A; finite_finite_type (A; fA)) (C; finite_finite_type (C; fC))))
               (path_universe_compose e1 e2) @ _).
    refine (ap (equiv_ap sum_finite (l; (A; fA)) (n; (C; fC)))^-1
               (path_sigma_hprop_compose
                  (A; finite_finite_type (A; fA))
                  (B; finite_finite_type (B; fB))
                  (C; finite_finite_type (C; fC))
                  (path_universe e1) (path_universe e2)) @ _).
    cut (forall (a b c: {n : nat & Finite_Types n})
                (p : sum_finite a = sum_finite b) (q : sum_finite b = sum_finite c),
            (equiv_ap sum_finite a c)^-1 (p @ q) =
            ((equiv_ap sum_finite a b)^-1 p) @ ((equiv_ap sum_finite b c)^-1 q)).
    { intro H. apply H. }
    clear l A fA m B fB n C fC e1 e2.
    intros A B C p q.
    (* unfold equiv_ap. *)
    change ((equiv_ap sum_finite ?x ?y)^-1)
           with
           (fun q : sum_finite x = sum_finite y =>
              ((eissect sum_finite x)^ @ ap sum_finite^-1 q) @ eissect sum_finite y).
    hnf.
    destruct (eissect sum_finite C).
    destruct (eissect sum_finite A).
    destruct (eissect sum_finite B). hott_simpl.
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
      (((equiv_ap sum_finite (n; (A; fA)) (n; (A; fA)))^-1
        oE (equiv_path_sigma_hprop (A; finite_finite_type (A; fA)) (A; finite_finite_type (A; fA))
        oE equiv_path_universe A A))
         equiv_idmap)
      with
      ((equiv_ap sum_finite (n; (A; fA)) (n; (A; fA)))^-1
          (path_sigma_hprop (A; finite_finite_type (A; fA)) (A; finite_finite_type (A; fA))
             (@path_universe _ A A equiv_idmap _))).
    refine (ap ((equiv_ap sum_finite (n; (A; fA)) (n; (A; fA)))^-1 o
               (path_sigma_hprop (A; finite_finite_type (A; fA)) (A; finite_finite_type (A; fA))))
               (path_universe_1) @ _).
    refine (ap ((equiv_ap sum_finite (n; (A; fA)) (n; (A; fA)))^-1)
               (path_sigma_hprop_1 _) @ _).
    change ((equiv_ap sum_finite ?x ?y)^-1)
           with
           (fun q : sum_finite x = sum_finite y =>
              ((eissect sum_finite x)^ @ ap sum_finite^-1 q) @ eissect sum_finite y).
    hnf.
    destruct (eissect sum_finite (n; (A; fA))). reflexivity.
  Qed.     
 

  (* Definition transport_exp_finite {X : Type} {A B : {n : nat & Finite_Types n}} (e : A.2 <~> B.2) (x : A.2 -> X) : *)
  (*   transport (fun I : {n : nat & Finite_Types n} => I.2 -> X) (path_finite_types A B e) x = x o e^-1. *)
  (* Proof.     *)

  (*   destruct A as [m [A eA]]. destruct B as [n [B eB]]. simpl in e. simpl in x. *)
  (*   refine (_ @ transport_exp_finite_sum (A := (A; Build_Finite A m eA)) (B := (B; Build_Finite B n eB)) e x). *)
  (*   refine (_ @ (transport_compose (fun I : {n0 : nat & Finite_Types n0} => I.2 -> X) *)
  (*                             (sum_finite )^-1 *)
  (*                             (path_finite_types_sum (A; finite_finite_type (A; eA)) (B; finite_finite_type (B; eB)) e) x)^ ). *)
  (*   unfold path_finite_types. *)
  (*   apply (ap (fun f : sum_finite (m; (A; eA)) = sum_finite (n; (B; eB)) -> (m; (A; eA)) = (n; (B; eB)) => *)
  (*                transport (fun I : {n0 : nat & Finite_Types n0} => I.2 -> X) *)
  (*                          (f ((path_finite_types_sum (A; finite_finite_type (A; eA)) (B; finite_finite_type (B; eB))) e)) x)). *)
  (*   transitivity  *)
  (*   (fun q : sum_finite (m; (A; eA)) = sum_finite (n; (B; eB)) => *)
  (*                      ((eissect sum_finite (m; (A; eA)))^ @ ap sum_finite^-1 q) @ eissect sum_finite (n; (B; eB))). reflexivity. *)
  (*   Abort. *)

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


  (* Definition BSigma_rec_1Type (n : nat) (X : Type) (istrunc_P : IsTrunc 1 X) *)
  (*            (x0 : X) *)
  (*            (wd : (Fin n <~> Fin n) -> x0 = x0) *)
  (*            (wd_comp : forall (e1 e2 : Fin n <~> Fin n), *)
  (*                wd e1 @ wd e2 = wd (e2 oE e1)) : *)
  (*   Finite_Types n -> X. *)
  (* Proof. *)
  (*   intro s. *)
    
  (*   apply (@pr1 X (fun x : X => {wd' : (forall e :Fin n <~> s, x = x0) & *)
  (*                            forall (e1 e2 : Fin n <~> Fin n), wd' e1 @ wd' e2 = wd' (e2 oE e1)})). *)
  (*   assert (isprop_goal : IsHProp *)
  (*                           {x : X & *)
  (*                                {wd' : Fin n <~> Fin n -> x = x & *)
  (*                                      forall e1 e2 : Fin n <~> Fin n, *)
  (*                                        wd' e1 @ wd' e2 = wd' (e2 oE e1)}}). *)
  (*   { unfold IsHProp. simpl. *)
  (*     intros x y. *)
  (*     refine (contr_equiv' _ (equiv_path_sigma _ x y)^-1). *)
  (*     destruct x as [x1 x2]. destruct y as [y1 y2]. simpl. *)
      
    

    

End Finite_Types.



(* Section FinCat. *)
(*   Definition fin_1type : 1-Type. *)
(*     srapply (@BuildTruncType 1 {n : nat & Finite_Types n}). *)
(*     red. *)
(*     intros A B. *)
(*     apply (trunc_equiv' (A.2 <~> B.2) (path_finite_types A B)). *)
(*   Defined. *)

(*   (* Check (fundamental_pregroupoid_category fin_1type). *) *)
(*   (* Definition fincat : PreCategory. *) *)
(*   (* Proof. *) *)
(*   (*   srapply (Build_PreCategory (fun m n : nat => Fin m = Fin n)); simpl. *) *)
(*   (*   - intro m. reflexivity. *) *)
(*   (*   - intros l m n. *) *)
(*   (*     intros p q. exact (q @ p). *) *)
(*   (*   - intros. simpl. *) *)
(*   (*     apply concat_p_pp. *) *)
(*   (*   - simpl. intros. *) *)
(*   (*     apply concat_p1. *) *)
(*   (*   - simpl. intros. *) *)
(*   (*     apply concat_1p. *) *)
(*   (* Defined. *) *)

(*   Definition fincat : PreCategory. *)
(*   Proof. *)
(*     srapply (Build_PreCategory (fun m n : nat => Fin m <~> Fin n)); simpl. *)
(*     - intro m. apply equiv_idmap. *)
(*     - intros l m n. *)
(*       apply equiv_compose'. *)
(*     - intros. simpl. *)
(*       apply path_equiv. reflexivity. *)
(*     - simpl. intros. *)
(*       apply path_equiv. reflexivity. *)
(*     - simpl. intros. apply path_equiv. reflexivity. *)
(*   Defined. *)

    
  
(*   (* Trying to show that these are equivalent *) *)
(*   Definition F : Functor fincat (Type_to_Cat (fin_1type)). *)
(*   Proof. *)
(*     srapply @Build_Functor; simpl. *)
(*     - intro m. exact (m; canon m). *)
(*     - intros m n e. simpl.  *)
(*       apply path_finite_types. *)
(*       apply e. *)
(*     - intros a b c e1 e2. *)
(*       hnf.  *)
(*       apply (path_finite_types_compose (a; canon a) (b; canon b) (c; canon c)). *)
(*     - hnf. *)
(*       intro n. *)
(*       apply path_finite_types_1. *)
(*   Defined. *)

(*   Definition G : Functor (Type_to_Cat (fin_1type)) fincat. *)
(*   Proof. *)
(*     srapply @Build_Functor; simpl. *)
(*     - apply pr1. *)
(*     - intros A B []. exact equiv_idmap. *)
(*     - intros a b c [] []. simpl. *)
(*       apply path_equiv. reflexivity. *)
(*     - reflexivity. *)
(*   Defined. *)
    
(*   (* F is a weak equivalence (def 9.4.6) *) *)
(*   Arguments path_finite_types : simpl never. *)
  
(*   Definition fullyfaithful_F : *)
(*     forall (a b : _), IsEquiv (@morphism_of _ _ F a b).   *)
(*   Proof. *)
(*     intros a b. simpl in a, b. *)
(*     unfold F. cbn. *)
(*     apply equiv_isequiv. *)
(*   Defined. *)

(*   Definition essentially_surj_F : *)
(*     Attributes.IsEssentiallySurjective F. *)
(*   Proof. *)
(*     unfold Attributes.IsEssentiallySurjective. simpl. *)
(*     intros [m [A fA]]. strip_truncations. *)
(*     apply tr. *)
(*     exists m. *)
(*     srapply @Build_Isomorphic. simpl. *)
(*     apply path_finite_types. *)
(*     simpl. apply equiv_inverse. *)
(*     apply fA. *)
(*   Defined.  *)
    

    
(* End FinCat. *)




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

  (* Definition equiv_compliment {n k : nat} {A : Finite_Types n} : *)
  (*     IsEquiv (@compliment n k A). *)
  (* Proof. *)
  (*   srapply @isequiv_adjointify. *)
    
    




  (* (* I want to show that P n A is contractible, but I don't think I need it. . . *) *)
  (* Definition contr_last_subset {n : nat} (A : Finite_Types n) : *)
  (*   Contr (Finite_Subsets n A). *)
  (* Proof. *)
  (*   srapply @BuildContr. *)
  (*   - srapply @exist. *)
  (*     exists A. exact A.2. *)
  (*     exists idmap. apply equiv_is_embedding. exact _. *)
  (*   - intro B. srapply @path_finite_subsets. *)
  (*     + simpl. apply equiv_inverse. *)
  (*       destruct B as [B [f embf]]. simpl. *)
  (*       transitivity {ab : A * B & f (snd ab) = fst ab}. *)
  (*       *  srapply @equiv_adjointify. *)
  (*          { intro b. exists (f b, b). reflexivity. } *)
  (*          { exact (snd o pr1). } *)
  (*          { intros [[a b] p]. simpl in *. admit. } *)
  (*          { intro b. reflexivity. } *)
  (*       * srapply @equiv_adjointify. *)
  (*         { intros [[a b] p]. exact a. } *)
  (*         { intro a. *)
        
  (*       srapply @BuildEquiv. *)
  (*       exact B.2.1. *)
  (*       apply isequiv_fcontr. intro a. *)
  (*       apply contr_inhabited_hprop. apply (B.2.2). *)

        
        
    


    

    
  
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
End Magma.

  


Section Restrict_Equivalence.
  Context {n : nat}
          {A : Type}
          (e : A + Unit <~> Fin n.+1).

  Definition swap_last := fin_transpose_last_with n (e (inr tt)).

  Lemma swap_fix_last :
    (swap_last oE e) (inr tt) = inr tt.
  Proof.
    unfold swap_last. ev_equiv. apply fin_transpose_last_with_with.
  Qed.

  Lemma is_inr_restrict_equiv :
    forall u : Unit,
      is_inr ((swap_last oE e) (inr u)).
  Proof.
    intros []. rewrite swap_fix_last. exact tt.
  Qed.

  Lemma not_inr_is_inl {X Y : Type}
        (x :  X + Y)
        (not_inr : forall y : Y, x <> inr y)
    : is_inl x.
  Proof.
    destruct x as [x | y'].
    - exact tt.
    - destruct (not_inr y' idpath).
  Qed.
        
  
  Lemma is_inl_restrict_equiv :
    forall a : A,
      is_inl ((swap_last oE e) (inl a)).
  Proof.
    intro a.
    apply not_inr_is_inl.
    intros [].
    rewrite <- swap_fix_last.
    intro p. apply (inl_ne_inr a tt).
    exact (equiv_inj (swap_last oE e) p).
  Qed.
    
    
  (*   intro a. unfold swap_last. ev_equiv. *)
  (*   (* two cases: e (inl a) is the last element, or it isn't *) *)
  (*   assert (neq : (e (inr tt) <> e (inl a))) *)
  (*       by exact (fun z => inl_ne_inr _ _ (equiv_inj e (z^))). *)
  (*   recall (e (inl a)) as y eqn:p. *)
  (*   destruct y as [y | []]. *)
  (*   - rewrite p. *)
  (*     rewrite fin_transpose_last_with_rest. *)
  (*     { exact tt. } *)
  (*     destruct p. exact neq. *)
  (*   - rewrite p. *)
  (*     rewrite fin_transpose_last_with_last. *)
  (*     (* two cases: e (inr tt) is inl(z) or inr(tt), the latter wich is absurd *) *)
  (*     recall (e (inr tt)) as z eqn:q. *)
  (*     destruct z as [z | []]. *)
  (*     + rewrite q. exact tt. *)
  (*     + destruct q^. exact (neq p^). *)
  (* Qed. *)

  Definition equiv_restrict :=
    equiv_unfunctor_sum_l (swap_last oE e)
                          is_inl_restrict_equiv
                          is_inr_restrict_equiv.

  Definition equiv_restrict_eta :
    equiv_restrict +E equiv_idmap == swap_last oE e.
  Proof.
    intro x.
    refine (_ @ unfunctor_sum_eta _ is_inl_restrict_equiv is_inr_restrict_equiv x).
    destruct x as [x | []]; try reflexivity.    
    simpl.
    destruct (unfunctor_sum_r (fun x : A + Unit => swap_last (e x)) is_inr_restrict_equiv tt).
    reflexivity.
  Qed.

  (* Definition equiv_restrict_fixlast : *)
  (*   (e (inr tt) = inr tt) -> equiv_restrict +E equiv_idmap = e. *)
  (* Proof. *)
  (*   intro p. *)
  (*   cut (swap = equiv_idmap). *)
  (*   { intro q. unfold equiv_restrict. *)
  (*     apply path_equiv. simpl. *)
  (*     apply path_arrow. intros [a | []]; simpl. *)
  (*     -  *)
      
End Restrict_Equivalence.

Definition equiv_restrict_plus1 {n : nat} {A : Type} (e : A <~> Fin n) :
  equiv_restrict (e +E equiv_idmap) == e.
Proof.
  intro a.
  apply (path_sum_inl Unit).
  refine (unfunctor_sum_l_beta _ _ a @ _).
  simpl. destruct n; reflexivity.      (* for some reason I have to destruct n *)
Qed.

(* Definition swap_last_compose {n : nat} (e1 e2 : Fin n.+1 <~> Fin n.+1) : *)
(*   swap_last (e2 oE e1) == (swap_last e2) oE (swap_last e1). *)
(* Proof. *)
(*   intro x. unfold swap_last. *)
  
(* Definition swap_compose {n : nat} (e1 e2 : Fin n.+1 <~> Fin n.+1) : *)
(*   e2 oE swap_last e1 oE e1 == e2 oE e1. *)
(* Proof. *)
(*   hnf. intro x. *)
  

(* Definition equiv_restrict_compose {n : nat} (e1 e2 : Fin n.+1 <~> Fin n.+1) : *)
(*   equiv_restrict (e2 oE e1) == (equiv_restrict e2) oE (equiv_restrict e1). *)
(* Proof. *)
(*   destruct n. { intros []. } *)
(*   intro x. *)
(*   apply (path_sum_inl Unit). *)
(*   refine (_ @ (unfunctor_sum_l_beta _ _ (equiv_restrict e1 x))^). *)
(*   refine (_ @ (ap (swap_last e2 oE e2) (unfunctor_sum_l_beta _ _ x)^)). *)
(*   refine (unfunctor_sum_l_beta _ _ x @ _). *)
(*   assert (comm_sigma2 : forall g1 g2 : Fin 2 <~> Fin 2, g1 oE g2 == g2 oE g1). *)
(*   { admit. } *)
(*   transitivity ((swap_last e2 oE swap_last e1 oE (e2 oE e1)) (inl x)). *)
(*   { simpl. generalize (e2 (e1 (inl x))). (* not true. . . *) admit. } *)
(*   apply (ap (swap_last e2)). *)
(*   apply (comm_sigma2 (swap_last e1) e2 (e1 (inl x))). *)
  
  

(*   (* Fin 2 <~> Fin 2 commutative, and swap functorial *) *)
(* Admitted. *)


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
      + rewrite H. apply leq_refl.
      + apply j_leq_Sn.
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

  
  
  
    
  




