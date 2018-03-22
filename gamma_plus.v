(* Trying to define \Gammma^+ as in Jardines "The Barratt-Priddy-Quillen Theorem" from 2009 *)
(* There it is defined as the homotopy colimit over all monomorphisms of a certain functor.*)
(* Monomorphisms can be factored into permutations and the inclusions n->n+1 not hitting the last point. *)
(* This we take advantage of to define the colimit in HoTT. The permutations come from univalence, and the rest is a normal HIT *)

Require Import HoTT.
Require Import UnivalenceAxiom.
(* Load finite. *)
Load stuff.

(* Definition Finite_Types (n : nat) := *)
(*   BAut (Fin n). *)
(* Use BAut instead? *)
Definition Finite_Types  :=
  {A : Type & Finite A}.

Definition type_of (A : Finite_Types) := pr1 A.
Coercion type_of : Finite_Types >-> Sortclass.

Definition card_of (A : Finite_Types) := @fcard (A.1) (A.2) : nat.

(* Canonical finite types *)
Definition canon (n : nat) : Finite_Types :=
  (Fin n; Build_Finite (Fin n) n (tr 1%equiv)).

(* This is also in monoidal_1type.v *)
(*Finite types are sets *)
Definition isset_Fin (n : nat) : IsHSet (Fin n).
Proof.
  induction n.
  - exact _.
  - apply hset_sum.
Defined.

Definition isset_Finite (A : Type) {n : nat}:
  merely (A <~> Fin n) -> IsHSet A.
Proof.
  intro finA. strip_truncations.
  apply (trunc_equiv' (Fin n) finA^-1).
Defined.

(* A detachable subset of a finite set has smaller cardinal *)
Definition leq_card_subset (A : Finite_Types) (P : A -> Type)
           (isprop_P : forall a : A, IsHProp (P a)) (isdec_P : forall a : A, Decidable (P a)) :
  (card_of ({a : A & P a}; (@finite_detachable_subset A.1 A.2 P isprop_P isdec_P)) <= card_of A)%nat.
Proof.
  
  
  destruct A as [A fA]. simpl in P, isprop_P, isdec_P. simpl.
  (* set (i := (card_of ({a : A & P a}; finite_detachable_subset P))). *)
  unfold card_of. simpl.
  apply (leq_inj_finite pr1).
  unfold IsEmbedding. intro a.
  unfold hfiber.
  assert (equiv_P : {x : {x : A & P x} & x.1 = a} <~> P a).
  { srapply @BuildEquiv.
    intros [[a1 p] q]. exact (transport P q p).
    srapply @BuildIsEquiv.
    - intro p. exact ((a; p); idpath).
    - unfold Sect. apply transport_1.
    - unfold Sect. intros [[a1 p] q].
      srapply @path_sigma.
      srapply @path_sigma.
      + exact q^.
      + apply transport_Vp.
      + destruct q. reflexivity.
        (* simpl. simpl in q. change (fun x : A => P x) with P. *)
        (* destruct q. simpl. *)
        (* refine (ap10 (transport_pr1_path_sigma *)
        (*                 (A := A) (P := P) *)
        (*                 (u := (a; transport P q p)) *)
        (*                 (v := (a1; p)) *)
        (*                 q^ (transport_Vp (fun x : A => P x) q p) (fun a' => a' = a)) 1 @ _). *)
        (* refine (transport_paths_l _ _ @ _). *)
    - intros [[a1 p] q]. destruct q. reflexivity. }
  apply (trunc_equiv' (P a) (equiv_P^-1)).
Qed.

(* Plus one for finite types *)
Definition add_one : Finite_Types -> Finite_Types.
Proof.
  intros [A [n H]].
  exists (A + Unit).
  strip_truncations.
  apply (Build_Finite _ (n.+1)).
  apply tr. (* apply path_universe_uncurried. *)
  (* exact (equiv_functor_sum' ((equiv_path_universe A (Fin n))^-1 H) equiv_idmap). *)
  exact (equiv_functor_sum' H equiv_idmap).
Defined.

Definition path_finite_types  (s t : Finite_Types):
  (s.1 <~> t.1) <~> s = t :=
  equiv_path_sigma_hprop _ _ oE equiv_path_universe _ _.
  

(* This should more or less follow from baut_ind_hset (except that is only for P: Type -> Type*)
Definition BSigma_ind_hSet (P : Finite_Types -> Type)
           {isset_P : forall s : Finite_Types, IsHSet (P s)}
           (pt : forall n : nat, P (canon n))
           (wd : forall (n : nat) (e : Fin n <~> Fin n),
               transport P (path_finite_types (canon n) (canon n) e) (pt n) = pt n) :
  forall s : Finite_Types, P s.
Proof.
  intro s.
  apply (@pr1 (P s) (fun p : P s => forall e' : Fin (card_of s) <~> s,
                         transport P (path_finite_types (canon (card_of s)) s e') (pt (card_of s)) = p)).
  assert (isprop_goal : forall s' : Finite_Types, IsHProp
                          {p : P s' &
                               forall e' : Fin (card_of s') <~> s',
                                 transport P (path_sigma_hprop (canon (card_of s')) s' (path_universe_uncurried e'))
                                           (pt (card_of s')) = p}).
  { destruct s' as [A [m eA]].
    strip_truncations. apply trunc_sigma'.
    - intro p. apply trunc_forall.
    - intros p q.
      apply (contr_inhabited_hprop _).
      destruct p as [p fp]. destruct q as [q fq]. simpl. simpl in fp. simpl in fq.      
      exact ((fp (equiv_inverse eA))^ @ (fq (equiv_inverse eA))). }
  destruct s as [A [m eA]]. strip_truncations.
  destruct (path_finite_types (canon m) (A; Build_Finite A m (tr eA)) (equiv_inverse eA)).
  change (card_of (canon m)) with m.
  exact (pt m; wd m).
Defined.
  
  

(* (* Not sure if this needs a point in A, but it is enouch for my purposes *) *)
(* Definition forall_merely_to_merely_forall {A : Type} (P : A -> Type) (a : A): *)
(*   (forall a : A, merely (P a)) -> merely (forall a : A, P a). *)
(* Proof. *)
(*   intro f. *)
(*   set (fa := f a). generalize fa. intro. strip_truncations. apply tr. *)
(*   intro a0. exact fa0. *)
(*   apply functor_trunc.  *)

  
  

(* This is just copied from fin_equiv_hfiber, but I wanted it as its own result *)

(* TODO : One of the Fin n's should be generalized. *)
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

(* Definition equiv_restrict {n : nat} {A B: Type} (e : A+Unit <~> B+1) :  <~> Fin n. *)
(* Proof. *)
(*   simpl in e. *)
(*   recall (e (inr tt)) as y eqn:p. *)
(*   assert (p' := (moveL_equiv_V _ _ p)^). *)
(*   destruct y as [y | []]. *)
(*   (*  *) *)
(*   - apply (equiv_unfunctor_sum_l (fin_transpose_last_with n (inl y) oE e) *)
(*                                  (is_inl_transpose1 e y p) (is_inr_transpose1 e y p)). *)
(*   - apply (equiv_unfunctor_sum_l e (is_inl_transpose2 e p) (is_inr_transpose2 e p)). *)
(* Defined. *)

(* Definition almost_natural {n : nat} (e : Fin n.+1 <~> Fin n.+1) : *)
(*   inl o equiv_restrict e == (fin_transpose_last_with n (e (inr tt)) oE e) o inl. *)
(* Proof. *)
(*   intro a. simpl. *)
(*   recall (e (inl a)) as x eqn:px. *)
(*   recall (e (inr tt)) as y eqn:py. destruct y as [y | []]. *)
(*   - rewrite p. simpl.  *)
(*     assert (q : inl y <> e (inl a)) *)
(*       by exact (fun z => inl_ne_inr _ _ (equiv_inj e (z^ @ p^))). *)
(*     rewrite fin_transpose_last_with_rest. *)
(*   destruct (e (inr tt)) as [y | []]. *)

(*   refine (unfunctor_sum_l_beta _ _ a @ _).  *)
(*   intro a. simpl in e. *)
(*   unfunctor_sum_l_beta *)
(*   recall (e (inr tt)) as y eqn:p. *)
(*   assert (p' := (moveL_equiv_V _ _ p)^). rewrite p. *)
(*   destruct y as [y | []]. *)
(*   - assert (q : inl y <> e (inl a)) *)
(*         by exact (fun z => inl_ne_inr _ _ (equiv_inj e (z^ @ p^))). *)
(*     ev_equiv. recall (e (inl a)) as z eqn:pz. *)
(*     (* set (z := e (inl a)) in *. *) *)
(*     destruct z as [z | z[]]. *)
(*     (* { rewrite pz. rewrite fin_transpose_last_with_rest. apply (ap inl). *)
 (*      *) *)
(*     Admitted. *)


Definition equiv_restrict_last_fixed {A B : Type} (e : A+Unit <~> B+Unit) (p : e (inr tt) = inr tt):
  A <~> B.   (* {e' : Fin n <~> Fin n & e o inl = inl o e'}. *)
Proof.
  exact (equiv_unfunctor_sum_l e (is_inl_restrict_equiv_last_fixed e p) (is_inr_restrict_equiv_last_fixed e p)).  
Defined.

(* Definition equiv_restrict_notfixlast {n : nat} {A : Type}  *)
(*            (e : A + Unit <~> Fin n.+1) (y : Fin n) (p : e (inr tt) = inl y) : *)
(*   A <~> Fin n. *)
(* Proof. *)
(*   exact (equiv_unfunctor_sum_l e (is_inl_restrict_equiv_notfixlast e y p) (is_inr_restrict_equiv_last_fixed e y p)). *)

(* Definition equiv_restrict_not_fix_last {n : nat} (e : Fin n.+1 <~> Fin n.+1) (ne : e (inr tt) <> inr tt) : *)
(*   Fin n <~> Fin n. *)
(* Proof. *)
(*   set (k := e^-1 (inr tt)). *)
(*   assert (k <> inr tt). *)
(*   { intro q. apply ne. *)
(*     refine (ap e q^ @ _). unfold k. apply eisretr. } *)


(*   apply (equiv_unfunctor_sum  *)


(*   apply (equiv_unfunctor_sum_l e). *)
(*   - apply (is_inl_transpose2 e p). *)
(*     intro a. *)
(*     destruct (is_inl_or_is_inr (e (inl a))) as [l|r]. *)
(*     + exact l. *)
(*     + assert (q := inr_un_inr (e (inl a)) r). *)
(*       apply moveR_equiv_V in q. *)
(*       assert (s := q^ @ ap (e^-1 o inr) (path_unit _ _) @ (moveL_equiv_V _ _ p)^). *)
(*       elim (inl_ne_inr _ _ s). *)
(*   - intros []. rewrite p. exact tt. *)
(* Defined. *)

Definition natural_equiv_restrict {A B : Type} (e : A+Unit <~> B+Unit) (p : e (inr tt) = inr tt) :
  inl o (equiv_restrict_last_fixed e p) == e o inl.
Proof.
  intro x. apply unfunctor_sum_l_beta.
Defined.

(* Definition swap_const {n : nat} (k : Fin n.+1) (x : Fin n.+1 -> X) (p : x k = x (inr tt)) : *)
(*   x o (fin_transpose_last_with n k) == x. *)
(* Proof. *)
(*   intro i. *)
(*   destruct i as [i | []]. *)
(*   - destruct (dec (k = inl i)). *)
(*     + rewrite <- p0. exact (ap x (fin_transpose_last_with_with n k) @ p^). *)
(*     + exact (ap x (fin_transpose_last_with_rest n k i n0)). *)
(*   - exact (ap x (fin_transpose_last_with_last n k) @ p). *)
(* Defined. *)










  

(* Open Scope nat. *)
Section Homotopy_Symmetric_Product.
  (* The symmetric product (I think) *)
  Definition hSymmetric_Product (X : Type) :=
    {A : Finite_Types & (A -> X)}.

  (* To get a function out of hSP n into a set, you need a function out of the product which does not depend on  *)
  (* permutations n <~> n *)
  Definition hSP_rec_hset {X : pType} (P : Type)
             {isset_P : IsHSet P}
             (f : forall n: nat, (Fin n -> X) -> P)
             (welldef : forall (n : nat) (x : Fin n -> X) (e : Fin n <~> Fin n), f n (x o e) = f n x)
    : hSymmetric_Product X -> P .
  Proof.
    intros [s x]. revert s x.
    srapply @BSigma_ind_hSet.
    - simpl. exact f.
    - intros n e. apply path_arrow. intro.
      change (fun s : Finite_Types => (s -> X) -> P) with
      (fun s : {A : Type  & Finite A} => (s.1 -> X)-> P).
      refine (transport_arrow_toconst (path_sigma_hprop (canon n) (canon n) (path_universe_uncurried e)) (f n) x @ _).
      (* transitivity (f (x o e)). *)
      (* transitivity *)
      (*   (p (transport (fun x0 : {A : Type & merely (A <~> Fin n)} => x0.1 -> X) *)
      (*                 (path_sigma_hprop (canon n) (canon n) (path_universe_uncurried e))^ (x o e))). *)
      refine (_ @ welldef n x e).
      apply (ap (f n)).
      unfold path_sigma_hprop.
      
      apply (moveR_transport_V (fun x0 : {A : Type & Finite A} => x0.1 -> X)
            (path_sigma_uncurried (fun A : Type => Finite A) (canon n) (canon n)
                                  (pr1^-1 (path_universe_uncurried e)))).
      apply inverse.
      transitivity (transport (fun A : Type => A -> X)
                              (pr1^-1 (path_universe_uncurried e)).1 (x o e)).
      + apply ap10. refine (@transport_pr1_path_sigma_uncurried
                              (Type)
                              (fun A => Finite A)
                              (canon n) (canon n)
                              (pr1^-1 (path_universe_uncurried e))
                              (fun A => A -> X)).
      + simpl. (* change (path_universe_uncurried e) with (path_universe e). *)
        refine (transport_exp X (Fin n) (Fin n) e (x o e) @ _).
        apply path_arrow. intro i. apply (ap x). apply (eisretr e).
  Defined.

  Definition hSP_ind_hprop {X : pType} (P : hSymmetric_Product X -> Type)
             {isprop_Pn : forall (n : nat) (x : Fin n -> X), IsHProp (P (canon n; x))}
             (* {isset_P : IsHSet (P (canon n; const (point X)))} *)
             (f : forall (n : nat) (x : Fin n -> X), P (canon n; x))
    : forall x : hSymmetric_Product X, P x.
  Proof.
    intros [s x]. revert s x.
    assert (p : forall (n : nat) (e : Fin n <~> Fin n), tr (n:=-1) e = tr (1%equiv)).
    { intros n e. apply (istrunc_truncation -1). }
    assert (isprop_P : forall x : hSymmetric_Product X, IsHProp (P x)).    
    { intros [[A [n eA]] x]. revert x. strip_truncations. destruct (path_universe eA)^.
      simpl.
      destruct (p n eA)^. exact (isprop_Pn n).
    }
    intros [A [n eA]]. strip_truncations.
    destruct (path_universe eA)^. destruct (p n eA)^. exact (f n).
  Defined.

  Definition transport_exp_finite {X : Type} {A B : Finite_Types} (e : A <~> B) (x : A -> X) :
    transport (fun I : Finite_Types => I -> X) (path_finite_types A B e) x = x o e^-1.
  Proof.
    refine (ap10 (transport_pr1_path_sigma_uncurried (pr1^-1 (path_universe_uncurried e))
                                                     (fun A : Type => A -> X)) x @ _).
    exact (transport_exp X A B e x).
  Defined.
  
  (* transport_arrow_toconst *)

  (* Another way of defining the symmetric product *)
  Definition equiv_other_SP {X : Type} :
    hSymmetric_Product X <~> {A : Type & (Finite A) * (A -> X)%type}.
  Proof.
    unfold hSymmetric_Product. unfold Finite_Types.
    apply equiv_inverse.
    refine (equiv_sigma_assoc _ _ oE _).
    apply equiv_functor_sigma_id. intro A.
    simpl. apply equiv_inverse.
    apply equiv_sigma_prod0.
  Defined.

  Definition prod_to_SP {X : Type} {n : nat} : (Fin n -> X) -> hSymmetric_Product X :=
    fun x => (canon n; x).

  Definition path_hSP {X : Type} (x y : hSymmetric_Product X) :
    {e : x.1 <~> y.1 & x.2 o e^-1 = y.2} -> x = y.
  Proof.
    intros [e p].
    srapply @path_sigma.
    - exact (path_finite_types x.1 y.1 e).
    - refine (transport_exp_finite e x.2 @ p).
      (* apply equiv_emoveR_fV. exact p. *)
  Defined.

    

  (* Given elements (A,x) (B,y) in the symmetric product, the identity type (A,x) = (B,y) should be the type
 {f : A<~>B & x = y o f}.*)
  Definition equiv_path_hSP {X : Type} (x y : hSymmetric_Product X)  :
    x = y <~> {e : x.1 <~> y.1 & x.2 o e^-1 = y.2}.
  Proof.
    (* refine (_ oE (equiv_ap equiv_other_SP x y)). *)
    refine (_ oE equiv_path_sigma _ _ _).
    destruct x as [A x]. simpl in x.
    destruct y as [B y]. simpl in y. simpl.
    transitivity {p : A.1 = B.1 & transport (fun A : Type => A -> X) p x = y}.
    { srapply @equiv_functor_sigma'.
      - apply equiv_inverse. apply equiv_path_sigma_hprop.
      - intro p.
        destruct p. reflexivity. }
    apply equiv_inverse.
    refine (equiv_functor_sigma'(equiv_path_universe A B) _).
    intro e. simpl. apply equiv_concat_l.
    apply transport_exp.
  Defined.

  (* Not sure if this is needed *)
  Definition transport_equiv_plus1 {A B1 B2: Type} (e : B1 <~> B2) (f : B1 + Unit <~> A) :
    transport (fun B => B + Unit <~> A) (path_universe_uncurried e) f = f oE
                                                                  (equiv_inverse (equiv_functor_sum' e 1%equiv)).
  Proof.
    transitivity (f oE (((equiv_inverse (equiv_path_universe _ _)) (path_universe_uncurried e)) +E 1)^-1).
    { destruct (path_universe_uncurried e). simpl.
      apply emoveL_eV. 
      apply path_equiv. apply path_arrow. intro b. simpl.
      destruct b as [b | []]; reflexivity. }
    apply path_equiv.
    apply (ap (fun g => f o g)). simpl.
    apply path_arrow. intros [b | []]. simpl.
    { apply (ap inl).
      apply (moveR_transport_V idmap (path_universe e) b _). apply inverse.
      refine (ap10 (transport_idmap_path_universe e) (e^-1 b) @ _).
      apply eisretr. }
    reflexivity.
  Defined.

  (* The normalized form of a tuple *)
  Definition norm {X : pType} {dec_ne : forall x : X, Decidable (~ x = point X)}  :
    hSymmetric_Product X -> hSymmetric_Product X.
  Proof.
    intros [[A fA] x]. 
    set (B := {a : A & x a <> point X}).
    exists (B; (@finite_detachable_subset A fA (fun a => x a <> point X) _ _)).
    exact (x o pr1).
  Defined.


  (* (* Perhaps nicer to generalize *) *)
  (* Definition incl_sigma {A : Type} (P : A -> Type) : {a : A & P a} -> A := pr1. *)
  
  (* The inclusion of the underlying set of ther normalized tuple *)
  Definition inclusion_from_norm {X : pType} {A : Type} (x : A -> X) :
    {a : A & x a <> point X} -> A := pr1.

  Definition isfunctor_sum_incl {X : pType} {A : Type} (x : A + Unit -> X) :
    inclusion_from_norm x == functor_sum (inclusion_from_norm (x o inl)) (fun t => tt)
                                         o equiv_sigma_sum A Unit (fun a => x a <> point X).
  Proof. 
    intros [[a | []] ne]; reflexivity.
  Defined.


  (* The length of a tuple *)
  Definition len {X : pType} : hSymmetric_Product X -> nat := fun x => card_of x.1.


      
      (* isequiv_compose *)
  (* A lemma that should be elsewhere *)
  Definition ap_pred {m n : nat} : S m = S n -> m = n := ap pred.

        
  (* If the length of x and norm x are equal, then the inclusion is an equivalence *)
  (* This can be generalized to all decidable propositions over hSP X *)
  Definition eq_len_isequiv {X : pType} {dec_ne : forall x : X, Decidable (~ x = point X)}
             (x : hSymmetric_Product X) :
    len x = len (norm x) -> IsEquiv (inclusion_from_norm x.2).
  Proof.
    (* destruct x as [A x]. *)
    (* destruct A as [A [n eA]]. revert x. strip_truncations. intros x p.     *)
    (* induction n. *)
    (* -       unfold len. unfold card_of. simpl. destruct (path_universe eA)^. *)
    (*   apply all_to_empty_isequiv. *)
    (* - simpl in x. unfold len in p. *)

    (*   revert x. strip_truncations. intros x p. destruct (path_universe eA)^. simpl in IHn. *)
    (*   intro x. *)
    
    destruct x as [[A fA] x]. simpl. unfold len. simpl in x. simpl.
    destruct fA as [n eA]. strip_truncations.
    assert (frompath_eA : eA = equiv_inverse (equiv_path _ _ (path_universe_uncurried eA)^)).
    { apply inverse.
      refine ((equiv_path_V _ _ (path_universe_uncurried eA)^)^ @ _).
      refine (_ @ equiv_path_path_universe_uncurried eA).
      apply (ap (equiv_path A (Fin n))). apply inv_V. }
    destruct (frompath_eA)^.
    destruct (path_universe_uncurried eA)^. clear frompath_eA. clear eA.
    induction n.
    - intro p. apply all_to_empty_isequiv.      
    - intro p. rewrite (path_arrow _ _ (isfunctor_sum_incl x)).
      change (fun x0 : {x0 : Fin n + Unit & x x0 <> point X} =>
     functor_sum (inclusion_from_norm (fun x1 : Fin n => x (inl x1)))
       (fun _ : {b : Unit & x (inr b) <> point X} => tt)
       ((equiv_sigma_sum (Fin n) Unit (fun a : Fin n + Unit => x a <> point X)) x0)) with
            (functor_sum (inclusion_from_norm (x o inl)) (fun t => tt)
                         o equiv_sigma_sum (Fin n) Unit (fun a => x a <> point X)).
      apply (isequiv_compose' (equiv_sigma_sum (Fin n) Unit (fun a : Fin n + Unit => x a <> point X)) _).
      destruct (dec (x (inr tt) <> point X)).
      (* If the last term is not the base point then*)
      (* {a : Fin n+1 & x a <> x0} <~> {a : Fin n & x (inl a) <> x0} + Unit   *)
      + assert (isequiv_const : IsEquiv (fun t : {b : Unit & x (inr b) <> point X} => tt)).
        { srapply @isequiv_adjointify.
          - intros []. exact (tt ; n0).
          - intros[]; reflexivity.
          - intros [[] ne]. simpl.
            apply (path_sigma_hprop _ _). reflexivity. }
        assert (p' :
                  card_of (Fin n; {| fcard := n; merely_equiv_fin := tr ((equiv_path (Fin n) (Fin n) 1)^-1)%equiv |})
                  =
                  card_of ({a : Fin n & x (inl a) <> point X};
                           finite_detachable_subset (fun a : Fin n => x (inl a) <> point X))).
        { apply ap_pred.
          refine (p @ _).
          transitivity
            (((card_of
                 ({a : Fin n & x (inl a) <> point X};
                  finite_detachable_subset (fun a : Fin n => x (inl a) <> point X)))
              +
              card_of ({b : Unit & x (inr b) <> point X};
                       finite_equiv Unit (fun _ : {b : Unit & x (inr b) <> point X} => tt)^-1 finite_unit)
             )%nat).
          - refine (_ @ fcard_sum _ _).
            apply fcard_equiv'.
            apply equiv_sigma_sum.
          - apply nat_plus_comm. }
        srapply @isequiv_functor_sum.
        apply IHn. exact p'.
      + assert (isempty : {b : Unit & x (inr b) <> point X} <~> Empty).
        { srapply @BuildEquiv. intros [[] ne]. apply n0. exact ne. }
        assert (n.+1 = (card_of
                          ({a : Fin n & x (inl a) <> point X};
                           finite_detachable_subset (fun a : Fin n => x (inl a) <> point X))))%nat.
        { refine (p @ _).
          unfold card_of. simpl.
          apply fcard_equiv'.
          transitivity ({a : Fin n & x (inl a) <> point X} + Empty).
          { apply (@equiv_functor_sum {a : Fin n & x (inl a) <> point X} _ idmap _ _ Empty isempty _). }
          apply uiv_sum_empty.
            srapply (@equiv_functor_sum 1%equiv).
          
          transitivity
            (card_of
                 ({a : Fin n & x (inl a) <> point X};
                  finite_detachable_subset (fun a : Fin n => x (inl a) <> point X))).
          { admit. }
          unfold card_of.
              

            

        
        apply ap_pred.
        refine (p @ _).
        transitivity
          (((card_of
               ({a : Fin n & x (inl a) <> point X};
                finite_detachable_subset (fun a : Fin n => x (inl a) <> point X)))
            +
            card_of ({b : Unit & x (inr b) <> point X};
                     finite_equiv Unit (fun _ : {b : Unit & x (inr b) <> point X} => tt)^-1 finite_unit)
           )%nat).
        { refine (_ @ fcard_sum _ _).
          apply fcard_equiv'.
          apply equiv_sigma_sum. } 
        apply nat_plus_comm.
      + 

        
            refine (_ @ nat_plus_comm _ 1). reflexivity.
            unfold card_of. simpl.
            change {x0 : Fin (fcard (Fin n)) & x (inl (1%equiv^-1 x0)) <> point X} with
            {x0 : Fin (fcard n) & x (inl x0) <> point X}.
            apply (ap (fun m : nat => fcard {a : Fin (n) & x (inl a) <> point X})%nat).
            simpl.

          apply
            (ap pred
                (x := S (card_of (Fin n; {| fcard := n;
                                            merely_equiv_fin := tr ((equiv_path (Fin n) (Fin n) 1)^-1)%equiv |})))
                (y := S (card_of ({a : Fin n & x (inl a) <> point X}; finite_detachable_subset (fun a : Fin n => x (inl a) <> point X))))).
                    
                ).

        
        (* Speeds things a little up below *)
        set (finite_a :=
               finite_detachable_subset (fun x0 : Fin n => x (inl x0) <> point X)
               : Finite {a : Fin n & x (inl a) <> point X}).
        set (finite_b :=
               (finite_detachable_subset (fun x0 : Unit => x (inr x0) <> point X) :
                  Finite {b : Unit & x (inr b) <> point X})).
        set (m := fcard {b : Unit & x (inr b) <> point X}).
        assert (p' : m = 1%nat).
        { refine (fcard_equiv (fun _ : {b : Unit & x (inr b) <> point X} => tt) @ _). reflexivity. }
        set (n' := fcard {a : Fin n & x (inl a) <> point X}).
        assert (p'' : fcard ({a : Fin n & x (inl a) <> point X} + {b : Unit & x (inr b) <> point X}) =
               (n'.+1)%nat).
        { refine (_ @ nat_plus_comm n' 1).
          refine (fcard_sum _ _ @ _).
          change (fcard {a : Fin n & x (inl a) <> point X}) with n'.
          apply (ap (fun i => n' + i)%nat p'). }
        
        Check (ap pred (p @ p'')).
        assert 
          
          transitivity ((fcard {a : Fin n & x (inl a) <> point X}) + 1)%nat.
          { apply (ap (fun m => (fcard {a : Fin n & x (inl a) <> point X}) + m)%nat).

                  fcard_sum
          apply path_nat.
          change 

        
        rewrite (path_universe (fun t : {b : Unit & x (inr b) <> point X} => tt)) in p.
        

            apply path_sigma_1.

            
        srapply @isequiv_functor_sum (H := IHn (x o inl)
        srapply @isequiv_functor_sum. (* For some reason this takes ages. . . *)
      
      unfold inclusion_of_norm.
      simpl in IHn.
      
    
    
    unfold inclusion_of_norm.

    
  (* (* Trying to be able to choose an equivalence A <~> B + Unit *) *)
  (* Definition isprop_choice_minus1 {n : nat} (A : Finite_Types n.+1) (a : A) : *)
  (*   (* IsHProp {B : (hSymmetric_Product n A) & IsEquiv (* (functor_sum B.2 (fun t : Unit => a))}. *) *) *)
  (*   (*                                           (A := B.1+Unit) (B:=A) *) *)
  (*   (*                                           (fun b => match b with *) *)
  (*   (*                                                     |(inl b) => B.2 b *) *)
  (*   (*                                                     |(inr tt) => a end)} . *) *)
  (*   IsHProp {B : Finite_Types n & {e : B+Unit <~> A & e (inr tt) = a}}. *)
  (* Proof. *)
  (*   srefine (trunc_equiv' {B : (hSymmetric_Product n A) & IsEquiv  *)
  (*                                             (A := B.1+Unit) (B:=A) *)
  (*                                             (fun b => match b with *)
  (*                                                       |(inl b) => B.2 b *)
  (*                                                       |(inr tt) => a end)} _ (H:= _)). *)
  (*   { transitivity {B : Finite_Types n & {f : B -> A & IsEquiv (A := B+Unit) (B:=A) *)
  (*                                                              (fun b => match b with *)
  (*                                                                        |(inl b) => f b *)
  (*                                                                        |(inr tt) => a end)}}. *)
  (*     { apply equiv_inverse. srapply @equiv_sigma_assoc. } *)
  (*     apply equiv_functor_sigma_id. intro B. *)
  (*     transitivity {f : B + Unit -> A & IsEquiv f & f (inr tt) = a}. *)
  (*     { srefine (equiv_functor_sigma _ _). *)

  (*     _ (H:= _) *)
  (*                                                                                             admit. *)
  (*   destruct A as [A eA]. simpl. revert a. (* strip_truncations. destruct (path_universe eA)^. *) intro a. *)
  (*   apply trunc_sigma'. *)
  (*   - intro b. *)
  (*     apply hprop_isequiv. *)
  (*   - intros [B1 equiv_1] [B2 equiv_2]. simpl. *)
  (*     srapply (@contr_equiv'  _ _ (equiv_path_hSP B1 B2)^-1). *)
  (*     destruct B1 as [B1 f1]. destruct B2 as [B2 f2]. simpl. simpl in a. *)
  (*     simpl in equiv_1. simpl in equiv_2. *)
  (*     set (e1 := BuildEquiv _ _ (fun b : B1 + Unit => match b with *)
  (*                                                     | inl b0 => f1 b0 *)
  (*                                                     | inr tt => a *)
  (*                                                     end) *)
  (*                           equiv_1). *)
  (*     set (e2 := BuildEquiv _ _ (fun b : B2 + Unit => match b with *)
  (*                                                     | inl b0 => f2 b0 *)
  (*                                                     | inr tt => a *)
  (*                                                     end) *)
  (*                           equiv_2). *)
  (*     change f1 with (e1 o inl). change f2 with (e2 o inl). *)
  (*     set (e := e2^-1 oE e1). *)
  (*     assert (p : e (inr tt) = inr tt). { unfold e. apply moveR_equiv_V. reflexivity. } *)
                                        
  (*                                       srapply @BuildContr. *)
  (*     + exists (equiv_restrict_last_fixed e p). *)
  (*       apply path_arrow. intro b. *)
  (*       transitivity (e2 (e (inl b))). unfold e. apply inverse. apply (eisretr e2). *)
  (*       apply (ap e2). apply inverse. apply (natural_equiv_restrict). *)
  (*     + intros [e' wd]. *)
  (*       assert (i_t : IsHSet (B1 -> A)). *)
  (*       { srefine (trunc_arrow (H0 := _)). *)
  (*         apply (isset_Finite A eA). } *)
  (*       srefine (path_sigma_hprop (H := fun _ => i_t _ _) _ _ _). simpl. *)
  (*       apply path_equiv. apply path_arrow. intro b. *)
  (*       apply (path_sum_inl  (Unit)). *)
  (*       refine (natural_equiv_restrict e p b @ _). unfold e. apply moveR_equiv_V. *)
  (*       exact (ap10 wd b). *)
  (* Defined. *)


  
  (* (* Given a point in X, we can add it to the end of the symmetric product *) *)
  (* Definition hSP_cons {X : Type} (x0 : X) (x : Fin n -> X) : hSymmetric_Product X. *)
  (* Proof. *)
  (*   exists (canon n.+1). *)
  (*   exact (sum_rect _ x (fun _ => x0)). *)
  (* Defined. *)
End Homotopy_Symmetric_Product.


Module Export Gamma_Plus.
  Context (X : pType).
  Context {dec_ne_bp : forall x : X, Decidable (x <> point X)}.
  (* Defining Gamma_Plus as a HIT*)
  (* This is shamelessly copied from the definition of Coeq. *)
  Private Inductive Gamma_Plus :=
    t : hSymmetric_Product X -> Gamma_Plus.

  Definition x0 := (point X).

  (* A tuple should be equal to its normalization, i.e. removing all instances of the basepoint. *)
  (* We need an argument that the length of x and its normalized form are not equal to ensure that we don't   *)
  (* add paths that are already there. *)
  Axiom d : forall (x : hSymmetric_Product X), len x <> len (norm x) -> t x = t (norm x).

  (* (* If a tuple is already equal its normalized form, then we should kill the extra path *) *)
  (* Axiom x : forall {n} (x : hSymmetric_Product n X), IsEquiv (inclusion_of_norm x) *)

  

  (* The induction principle for Gamma_Plus *)
  Definition Gamma_Plus_ind (P : Gamma_Plus -> Type)
                                  (t' : forall (x : hSymmetric_Product X), P (t x))
                                  (d' : forall (x : hSymmetric_Product X) (ne : len x <> len (norm x)),
                                      transport P (d x ne) (t' x) = t' (norm x)) :
      forall g : Gamma_Plus, P g :=
    fun g => (match g with | t x => t' x end).
    


  Axiom Gamma_Plus_ind_beta_d : forall (P : Gamma_Plus -> Type)
                                       (t' : forall (x : hSymmetric_Product X), P (t x))
                                       (d' : forall (x : hSymmetric_Product X)
                                                    (ne : len x <> len (norm x)),
                                           transport P (d x ne) (t' x) = t' (norm x))
                                       (x : hSymmetric_Product X) (ne : len x <> len (norm x)),
      apD (Gamma_Plus_ind P t' d') (d x ne) = d' x ne.

  Definition Gamma_Plus_rec (P : Type)
             (t' : hSymmetric_Product X -> P)
             (d' : forall (x : hSymmetric_Product X),
                          (len x <> len (norm x)) -> t' x = t' (norm x))
    := Gamma_Plus_ind (fun _ => P) t' (fun  (x : hSymmetric_Product X) (ne : len x <> len (norm x))
                                       => transport_const (d x ne) _ @ d' x ne).

  Definition Gamma_rec_beta_d (P : Type)
             (t' : hSymmetric_Product X -> P)
             (d' : forall (x : hSymmetric_Product X),
                          (len x <> len (norm x)) -> t' x = t' (norm x))
             (x : hSymmetric_Product X) (ne : len x <> len (norm x))
    : ap (Gamma_Plus_rec P t' d') (d x ne) = d' x ne.
  Proof.
    unfold Gamma_Plus_rec.
    eapply (cancelL (transport_const (d x ne) _)).
    refine ((apD_const (@Gamma_Plus_ind (fun _ => P) t' _) (d x ne))^ @ _).
    refine (Gamma_Plus_ind_beta_d (fun _ => P) _ _ _ _).
  Defined.


    
  
  (* Definition canon_const {X : pType} {n : nat} : *)
  (*   t (canon n; const x0) = t (canon 0; const x0) :> Gamma_Plus X. *)
  (* Proof. *)
  (*   induction n. *)
  (*   - reflexivity. *)
  (*   - refine (_ @ IHn). *)
  (*     refine (_ @ d (canon n; const x0)). *)
  (*     apply (ap t). *)
  (*     apply path_SP. *)
  (*     exists 1%equiv. *)
  (*     apply path_arrow. intros [x |]; reflexivity. *)
  (* Defined. *)
  
  (* Definition contr_const {X : pType} {n : nat}: *)
  (*   forall B : Finite_Types n, Contr (t (B; const x0) = t (canon n; const x0) :> Gamma_Plus X). *)
  (* Proof. *)
  (*   intros [B e]. strip_truncations. *)
  (*   assert (t ((B; tr e); const x0) = t(canon n; const x0):>Gamma_Plus X). *)
  (*   apply (ap t). *)
  (*   apply path_hSP. simpl. *)
  (*   exists e. reflexivity. *)
  (*   refine (trunc_equiv (t (canon n; const x0) = (t (canon n; const x0))) (fun p => X0  @ p)). *)
  (*   clear X0. *)
  (*   refine (trunc_equiv (t (canon 0; const x0) = (t (canon 0; const x0))) (fun p => (canon_const @ p @ canon_const^))). *)
  (*   srapply @BuildContr. *)
  (*   - reflexivity. *)
  (*   -                           (* TODO *) *)

  (* The basepoint of Gamma Plus is the point coming from the empty set *)
  Definition ispointed_gamma_plus {X : pType} : IsPointed (Gamma_Plus X) :=
    t (canon 0; const x0).      (* Any function would suffice, but const x0 is the shortest to write. *)

  (* When proving a proposition we only need to prove it for the symmetric products. *)
  Definition Gamma_Plus_ind_hProp {X : pType} (P : Gamma_Plus X -> Type)
             {isprop_P : forall g : Gamma_Plus X, IsHProp (P g)}
             (t' : forall {n : nat} (x : hSymmetric_Product n X), P (t x)) :
    forall g : Gamma_Plus X, P g.
  Proof.
    apply (Gamma_Plus_ind P t').
    intros n A. apply isprop_P.
  Defined.  
End Gamma_Plus.

(* I want to prove that Gamma_Plus S0 <~> {n : nat & Finite_Sets} *)
Section Gamma_Plus_S0.
  Context (X : pType).
  Notation "'x0'" := (point X).
  Context (isdprop_basedpath : forall x : X, IsHProp (x = x0)).
  Context (isdec_basedpath : forall x : X, Decidable (x = x0)).

  Definition swap_const {n : nat} (k : Fin n.+1) (x : Fin n.+1 -> X) (p : x k = x (inr tt)) :
    x o (fin_transpose_last_with n k) == x.
  Proof.
    intro i.
    destruct i as [i | []].
    - destruct (dec (k = inl i)).
      + rewrite <- p0. exact (ap x (fin_transpose_last_with_with n k) @ p^).
      + exact (ap x (fin_transpose_last_with_rest n k i n0)).
    - exact (ap x (fin_transpose_last_with_last n k) @ p).
  Defined.

  Definition code_tuple {n : nat} : (Fin n -> X + Unit) -> hProp.
  Proof.
    intro x.
    induction n.
    - exact True.
    - destruct (x (inr tt)).
      (* x (n+1) is not basepoint *)
      + exact False.
      + exact (IHn (x o inl)).
  Defined.

  
  TODO(* Better for X_+ ?*) 
  
  (* Define code on functions Fin n -> X first *)
  Definition code_tuple {n : nat} : (Fin n -> X) -> hProp.
  Proof.
    intro x.
    induction n.
    - exact True.
    - exact (if (dec (x (inr tt) = x0)) then (IHn (x o inl)) else False).
  Defined.



  (* Now we want to prove that forall g : Gamma_Plus X, g = point Gamma_Plus X is a proposition.  *)
  (* This proposition is True if x only hits x0, else it is false *)
  Definition code_Gamma_Plus : Gamma_Plus X -> hProp.
  Proof.
    srapply @Gamma_Plus_rec.
    - intro n.
      apply (hSP_rec_hset hProp code_tuple).
      intros x e.
      induction n; try reflexivity.
      (* Different cases depending on if e(n+1) is n+1 *)
      destruct (dec (e (inr tt) = inr tt)).
      (* e(n+1) is (n+1) *)
      + simpl. rewrite p. destruct (dec (x (inr tt) = x0)).
        (* both are x0 *)
        { refine (_ @ IHn (x o inl) (equiv_restrict_fix_last e p)).
          apply (ap (code_tuple)).
          apply path_arrow. intro i. apply (ap x). apply inverse.
          apply (natural_equiv_restrict e p i). }
        { reflexivity. }
      (* recall (e (inr tt)) as e_Sn  eqn: p. *)
      (* destruct e_Sn as [a | []]. *)
      (* e(n+1) is not n+1 *)
      + (* set (k := e (inr tt)). *)
        set (swap := (fin_transpose_last_with n (e (inr tt)) oE e)).
        assert (p : swap (inr tt) = inr tt).
        { unfold swap. simpl.
          apply fin_transpose_last_with_with. }
        simpl.
        destruct (dec (x (inr tt) = x0)).
        destruct (dec (x (e (inr tt)) = x0)).
        (* Both are x0 *)
        * transitivity (code_tuple (x o swap)).
          { 
            apply (ap code_tuple). unfold swap. simpl.
            apply (ap (fun y : Fin n.+1 -> X => y o e) (x := x) (y := x o (fin_transpose_last_with n (e (inr tt))))).
            apply path_arrow. intro i. apply inverse. apply swap_const.
            exact (p1 @ p0^). }
          unfold code_tuple.
            refine (_ @ IHn (x o inl) (equiv_restrict_fix_last swap p)).

        (* assert (p' : inr tt = e^-1 (inl a)). *)
        (* { apply (moveL_equiv_V _ _ p). } *)
        (* set (k := e^-1 (inr tt)). *)
        (* assert (p'' : e k = (inr tt)). *)
        (* { unfold k. apply eisretr. } *)
        (* assert (k <> inr tt). *)
        (* { unfold k.  *)
        (*   intro q. set (p''' := q @ p'). *)
        (*   rewrite q in p''. exact  *)
        
        (* assert (is_inl_k : is_inl k). *)
        admit.
      
    - simpl.
          
          
        
        
        
      { refine (_ @ IHn (x o inl)
      
      destruct (is_inl_or_is_inr (e (inr tt))). simpl in i.
      destruct (dec (x (e (inr tt)) = point X)); destruct (dec (x (inr tt) = point X)).
      (* Both endpoints are x0 *)
      +                         (* need Fin n <~> Fin n from Fin n+1 <~> Fin n+1 *)
        refine (_ @ IHn (x o inl) (equiv_restrict e)).
        apply (ap code_tuple). apply path_arrow. intro a.
        

        unfold fin_equiv_hfiber.
        simpl.
        
        (* refine (IHn (x o inl) pred e *)
        (* equiv_fin_equiv *)

        
        admit.
      + admit.
      + admit.
      
      
      
      srapply @hSP_rec_hset.
      + induction n.
        * intro f. exact True.    (* the basepoint is equal to the basepoint *)
        * intro x.
          (* Now there are different cases depending on the last point of x *)
          exact (if (dec (x (inr tt) = x0)) then 
          destruct (dec (x (inr tt) = x0)).
          (* If x (n+1) = x0, we go further, checking the rest of the values of x *)
          { exact (IHn (x o inl)). }
          (* If not x (n+1) = x0, stop and return False  *)
          { exact False. }
      (* Now we show that the definition is well defined up to equivalences *)
      + intros x e. induction n; try reflexivity.
        destruct (dec (x (inr tt) = x0)). destruct (dec (x (e (inr tt)) = x0)).
        (* both endpoints are x0. should use IHn somehow *)
        * admit.
        * simpl.
        simpl.

      intros [A x].
      revert x. revert A.
      srapply @BSigma_ind_hSet. simpl.
      induction n.
      + intro f. exact True.    (* the basepoint is equal to the basepoint *)
      + intro x.
        (* Now there are different cases depending on the last point of x *)
        destruct (dec (x (inr tt) = x0)).
        (* If x (n+1) = x0, we go further, checking the rest of the values of x *)
        * exact (IHn (x o inl)).
        (* If not x (n+1) = x0, stop and return False  *)
        * exact False.
      (* Now we show that the definition is well defined on Gamma Plus *)
      +                         (* Find out what
transport (fun s : Finite_Types n => (s -> X) -> hProp) ((path_finite_types (canon n) (canon n)) e)
is
     *)
        intro e. simpl.
        induction n.
        * simpl.
        assert (e = 1%equiv).
        { apply path_equiv. apply path_arrow. intros []. }
        rewrite X0. unfold path_universe_uncurried.
        (* rewrite path_universe_1. *)
        (* destruct Unit_hp. apply istrunc_trunctype_type. *)
        admit.                  (* This should be provable. . . *)
        * simpl.
        
      


      exact (forall a : A, x a = x0).
    - intro n. intros [A x]. simpl. destruct A as [A eA].
      apply path_universe_uncurried.
      refine (_ oE (equiv_sum_ind _)^-1). simpl.
      refine (prod_unit_r _ oE _).
      apply (equiv_functor_prod' 1%equiv).
      apply (@equiv_contr_unit (Unit -> x0 = x0)).
      apply (@contr_arrow _ Unit).
      apply (@contr_inhabited_hprop _ (isprop_basedpath x0)). exact idpath.
  Defined.

  Definition isprop_code : forall g : Gamma_Plus X, IsHProp (code_Gamma_Plus g).
  Proof.
    apply Gamma_Plus_ind_hProp.
    - intros. apply hprop_trunc.
    - intros n [A x]. simpl.
      apply trunc_forall.
  Defined.

  Definition encode_Gamma_Plus :
    forall g : Gamma_Plus X, (g = t(canon 0; const x0)) -> code_Gamma_Plus g.
  Proof.
    intro g. intro p. destruct p^. unfold code_Gamma_Plus. simpl. intros [].
  Defined.
    (* assert (isprop_P : forall g : Gamma_Plus X, IsHProp ((g = t(canon 0; const x0)) -> code_Gamma_Plus g)). *)
    (* - intro g. *)
    (*   apply (trunc_arrow (H0:=(isprop_code g))). *)
    (* - srapply (@Gamma_Plus_ind_hProp X _ isprop_P). *)
    (*   intros n [[A eA] x]. *)
    (*   revert x. revert eA. srapply @Trunc_ind. simpl. *)
    (*   intros eA x. intro p. *)
      
    (* srapply (@Gamma_Plus_ind_hProp X). *)
    (* - intro g. *)
    (*   assert (isprop_stuff : forall g : Gamma_Plus X, IsHProp (g = t (canon 0; const x0) -> code_Gamma_Plus g)). *)
    (*   { intro g0. apply (trunc_arrow (H0 := isprop_code g0)). } *)
    (*   apply (trunc_forall (H0 := isprop_stuff)). *)
    (* - intros n [[A eA] x]. *)
    (*   apply (@Gamma_Plus_ind_hProp X). *)
    (*   + intro g. apply (trunc *)
        
        
    (*   refine (@trunc_forall _ (Gamma_Plus X) _ _ _). *)
    (*   apply (@trunc_arrow _ (. *)


  decode????

  Definition isequiv_encode_Gamma_Plus :
    forall g : Gamma_Plus X, IsEquiv (encode_Gamma_Plus g).
  Proof.
    (* srapply (@Gamma_Plus_ind_hProp X (fun g => IsEquiv (encode_Gamma_Plus g))). simpl. *)
    intro g.
    srapply @isequiv_adjointify.
    - revert g.
      srapply (@Gamma_Plus_ind X (fun g => code_Gamma_Plus g -> g = t (canon 0; const x0))).
      intros n [[A eA] x]. simpl in x. simpl.
      intro isconst_x.
      apply center.
      revert eA. srapply @Trunc_ind. intro eA.
      simpl. 

      revert eA x.
      srapply @Gamma_Plus_ind.
      
    srapply (@Gamma_Plus_ind X (fun g => IsEquiv (encode_Gamma_Plus g))).
    (* Must do inverse before destructing x? *)
    intros n A. simpl.
    srapply @isequiv_adjointify.
    - 

    
    intros n [[A eA] x]. revert eA x.
    srapply @Trunc_ind. intros eA x. simpl in x.
    srapply @isequiv_adjointify.
    (* Inverse *)
    - simpl. intro const_x.
      transitivity (t (X := X) (canon n; const x0)).
      + apply (ap t). srapply @path_hSP; simpl.
        * exact eA.
        * apply path_arrow. intro a. apply const_x.
      + clear eA.
        induction n. reflexivity.
        refine (_ @ IHn).
        refine (_ @ d (canon n; const x0)).
        unfold hhSP_cons. apply (ap t).
        srapply @path_hSP. exact 1%equiv.
        apply path_arrow. intros [i | t]; reflexivity.

    - intro xxx. simpl in xxx.
      assert (isprop_this : IsHProp (forall a : A, x a = x0)).
      + apply trunc_forall.
      + apply isprop_this.        
    - intro p.
      induction n.
      

      apply isprop_code
    - intro p.
        * reflexivity. * simpl.
        simpl.
        simpl.
        apply (path_hSP 1%equiv).
        simpl.
        Check (
        p
        srapply @d.
        check
        apply d.
        
        exact (d (canon n; const x0) @ IHn).
      refine ((path_hSP eA _ @ _)).
    

  Definition decode_Gamma_plus :
    forall g : Gamma_Plus X, code_Gamma_Plus g -> g = t (canon 0; const x0).
  Proof.
    

  Definition based_path_Gamma_Plus :
    forall g : Gamma_Plus X,
      (g = t (canon 0; const x0)) <~> code_Gamma_Plus g.
  Proof.
    apply Gamma_Plus_ind_hProp.
    - intro g.
      srapply @istrunc_equiv.
      apply isprop_code.
    - intros n [[A eA] x].
      revert x. revert eA.
      srapply @Trunc_ind.
      intro eA. simpl. intro x.
      transitivity (t (canon n; x o eA^-1) = t (canon 0; const x0)).
      + apply equiv_concat_l.
        apply (ap t). apply inverse.
        srapply @path_hSP.
        * simpl. exact eA.
        * simpl. apply path_arrow. intro a. apply (ap x).
          apply inverse. apply (eissect eA).
      + induction n.
        * transitivity (t (canon 0; const x0) = t (canon 0; const x0) :> Gamma_Plus X).
          {apply equiv_concat_l. apply (ap t).
           srapply @path_hSP.
           - exact 1%equiv.
           - simpl. apply path_arrow. intros [].
          }
          transitivity Unit.
          { srapply @equiv_contr_unit.
            apply contr_inhabited_hprop.
            - 
          
           
          refine (_ oE (equiv_concat_l _ _)).
          admit.
        * simpl.
      

End Gamma_Plus_S0.