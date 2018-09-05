(* Trying to define \Gammma^+ as in Jardines "The Barratt-Priddy-Quillen Theorem" from 2009 *)
(* There it is defined as the homotopy colimit over all monomorphisms of a certain functor.*)
(* Monomorphisms can be factored into permutations and the inclusions n->n+1 not hitting the last point. *)
(* This we take advantage of to define the colimit in HoTT. The permutations come from univalence, and the rest is a normal HIT *)

Require Import HoTT.
Require Import UnivalenceAxiom.
Load finite.
(* Load stuff. *)

(* An equivalence I need for Gamma plus *)
Definition equiv_emoveR_fV `{Funext} {A B C : Type} (e : A <~> B) (f : B -> C) (g : A -> C) : 
  g = f o e <~> g o e^-1 = f.
Proof.
  transitivity (g == f o e).
  apply equiv_inverse.
  apply equiv_path_arrow.
  transitivity (g o e^-1 == f).
  unfold pointwise_paths.
  apply equiv_inverse.
  apply (equiv_functor_forall' e).
  intro b.
  apply (equiv_concat_l).
  apply (ap g).
  change (e^-1 (e b)) with ((e^-1 o e) b).
  apply (ap10 (f:= idmap)).
  apply path_arrow.
  intro x. apply inverse. apply (eissect e).
  apply equiv_path_arrow.
Defined.




(* Definition Finite_Types (n : nat) := *)
(*   BAut (Fin n). *)
(* Use BAut instead? *)
Definition Finite_Types  :=
  {A : Type & Finite A}.

(* Record Finite_Types := *)
(*   {finite_type :> Type; finite_finite_type : Finite finite_type}. *)

(* Definition issig_Finite_Types : *)
(*   { A : Type & Finite A } <~> Finite_Types. *)
(* Proof. *)
(*   issig Build_Finite_Types finite_type finite_finite_type. *)
(* Defined. *)

Definition type_of (A : Finite_Types) := pr1 A.
Coercion type_of : Finite_Types >-> Sortclass.
Global Instance finite_finite_type (A : Finite_Types) : Finite A := A.2.
(* Variable A : Finite_Types. Check fcard A. *)

(* Definition type_of (A : Finite_Types) := pr1 A. *)
(* Coercion type_of : Finite_Types >-> Sortclass. *)

(* Definition card_of (A : Finite_Types) := @fcard (A) (finite_finite_type A) : nat. *)

(* Canonical finite types *)
Definition canon (n : nat) : Finite_Types :=
  (* Build_Finite_Types (Fin n) (Build_Finite (Fin n) n (tr 1%equiv)). *)
  (Fin n; Build_Finite (Fin n) n (tr 1%equiv)).

(* This is also in monoidal_1type.v *)
(*Finite types are sets *)
(* Definition isset_Fin (n : nat) : IsHSet (Fin n). *)
(* Proof. *)
(*   induction n. *)
(*   - exact _. *)
(*   - apply hset_sum. *)
(* Defined. *)

(* Definition isset_Finite (A : Type) {n : nat}: *)
(*   merely (A <~> Fin n) -> IsHSet A. *)
(* Proof. *)
(*   intro finA. strip_truncations. *)
(*   apply (trunc_equiv' (Fin n) finA^-1). *)
(* Defined. *)

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

(* Proof. *)
(*   refine (_ oE equiv_path_universe _ _).  *)
(*   refine (_ oE equiv_path_sigma_hprop  *)
(*             (finite_type s; finite_finite_type s) (finite_type t; finite_finite_type t)). *)
(*   apply (equiv_ap' issig_Finite_Types (finite_type s; finite_finite_type s) (finite_type t; finite_finite_type t)). *)
(* Defined. *)
  

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

(* (* See if we can take things one step further *) *)
(* (* Do recursion first, but induction should be doable as well *) *)
(* Definition BSigma_rec_1type (P : Type) *)
(*            {is1Type_P : IsTrunc 1 P} *)
(*            (pt : nat -> P) *)
(*            (wd1 : forall {n : nat}, (Fin n <~> Fin n) -> pt n = pt n) *)
(*            (wd2 : forall {n : nat} (e1 e2 : Fin n <~> Fin n), *)
(*                wd1 (e2 oE e1) = wd1 e1 @ wd1 e2) : *)
(*   Finite_Types -> P. *)
(* Proof. *)
(*   intro s. *)
(*   apply (@pr1 P (fun p : P => forall n : nat, *)
(*                      {q : Fin n <~> Fin n -> p = p *)
(*                                              & forall e1 e2 : Fin n <~> Fin n, q (e2 oE e1) = q e1 @ q e2} *)
(*                 )). *)
(*   assert (isset_goal : IsHSet {p : P & *)
(*                                     forall n : nat, Fin n <~> Fin n -> p = p}). *)
(*   { srapply @trunc_sigma'. *)
(*     intros [p1 q1] [p2 q2]. simpl. apply (is1Type_P p1 p2). *)

    
(*   assert (isprop_goal : IsHProp *)
(*                           {p : P & *)
(*                                forall n : nat, *)
(*                                  {q : Fin n <~> Fin n -> p = p *)
(*                                   & forall e1 e2 : Fin n <~> Fin n, q (e2 oE e1) = q e1 @ q e2}}). *)
(*   { apply trunc_sigma'. *)
(*     - intro p. *)
(*       srefine (trunc_forall (n:=-1) (H0 := _)). intro n. simpl. *)
(*       apply trunc_sigma'. *)
(*       + intro q. apply trunc_forall. *)
(*       + intros q1 q2. *)
(*         apply (contr_inhabited_hprop _). apply path_arrow. intro e. *)
         

        
(*       apply trunc_forall. *)

  
  
  
(*   apply (@pr1 nat (fun n : nat => *)
(*                      {wd1 : Fin n <~> Fin n -> pt n = pt n & *)
(*                                                forall (e1 e2 : Fin n <~> Fin n), wd1 (e2 oE e1) = wd1 e1 @ wd1 e2 *)
(*                               })). *)
  
(*   apply (@pr1 (P s) (fun p : P s => forall e' : Fin (fcard s) <~> s, *)
(*                          transport P (path_finite_types (canon (fcard s)) s e') (pt (fcard s)) = p)). *)
(*   assert (isprop_goal : forall s' : Finite_Types, IsHProp *)
(*                           {p : P s' & *)
(*                                forall e' : Fin (fcard s') <~> s', *)
(*                                  transport P (path_sigma_hprop (canon (fcard s')) s' (path_universe_uncurried e')) *)
(*                                            (pt (fcard s')) = p}). *)
(*   { destruct s' as [A [m eA]]. *)
(*     strip_truncations. apply trunc_sigma'. *)
(*     - intro p. apply trunc_forall. *)
(*     - intros p q. *)
(*       apply (contr_inhabited_hprop _). *)
(*       destruct p as [p fp]. destruct q as [q fq]. simpl. simpl in fp. simpl in fq.       *)
(*       exact ((fp (equiv_inverse eA))^ @ (fq (equiv_inverse eA))). } *)
(*   destruct s as [A [m eA]]. strip_truncations. *)
(*   destruct (path_finite_types (canon m) (A; Build_Finite A m (tr eA)) (equiv_inverse eA)). *)
(*   change (fcard (canon m)) with m. *)
(*   exact (pt m; wd m). *)
(* Defined. *)
  
  

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
      (fun s : {A : Type  & Finite A} => (pr1 s -> X)-> P).
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

  (* (* Another way of defining the symmetric product *) *)
  (* Definition equiv_other_SP {X : Type} : *)
  (*   hSymmetric_Product X <~> {A : Type & (Finite A) * (A -> X)%type}. *)
  (* Proof. *)
  (*   unfold hSymmetric_Product. unfold Finite_Types. *)
  (*   apply equiv_inverse. *)
  (*   refine (equiv_sigma_assoc _ _ oE _). *)
  (*   apply equiv_functor_sigma_id. intro A. *)
  (*   simpl. apply equiv_inverse. *)
  (*   apply equiv_sigma_prod0. *)
  (* Defined. *)

  Definition prod_to_SP {X : Type} {n : nat} : (Fin n -> X) -> hSymmetric_Product X :=
    fun x => (canon n; x).

  (* This definition is nicer, I guess, but it is easier to just define the equivalence directly *)
  (* Definition path_hSP {X : Type} (x y : hSymmetric_Product X) : *)
  (*   {e : pr1 x <~> pr1 y & pr2 x o e^-1 = pr2 y} -> x = y. *)
  (* Proof. *)
  (*   intros [e p]. *)
  (*   srapply @path_sigma. *)
  (*   - exact (path_finite_types x.1 y.1 e). *)
  (*   - refine (transport_exp_finite e x.2 @ p). *)
  (*     (* apply equiv_emoveR_fV. exact p. *) *)
  (* Defined. *)


  (* Given elements (A,x) (B,y) in the symmetric product, the identity type (A,x) = (B,y) should be the type
 {f : A<~>B & x = y o f}.*)
  Definition equiv_path_hSP {X : Type} (x y : hSymmetric_Product X)  :
    {e : x.1 <~> y.1 & x.2 o e^-1 = y.2} <~> x = y.
  Proof.
    refine ((equiv_path_sigma _ _ _)^-1 oE _).
    destruct x as [A x]. 
    destruct y as [B y]. simpl.
    apply (equiv_functor_sigma' (path_finite_types A B)). intro e.
    apply equiv_concat_l.
    apply transport_exp_finite.
  Defined.

  Definition path_hSP {X : Type} (x y : hSymmetric_Product X)
             (e : x.1 <~> y.1) (p : x.2 o e^-1 = y.2) :
    x = y := (equiv_path_hSP x y (e; p)).

  (* Lemma stuff {X : Type} (x y : hSymmetric_Product X) *)
  (*       (e : x.1 <~> y.1) (p : x.2 o e^-1 = y.2) :  *)
  (*   path_hSP x y (equiv_path x.1 y.1 (path_universe_uncurried e)) *)
  (*            (ap (fun e' : x.1 <~> y.1  => x.2 o (e')^-1) (eisretr  (equiv_path x.1 y.1) e) @ p) *)
  (*   = *)
  (*   path_hSP x y e p. *)
  (* Proof. *)
  (*   refine (_ @ apD011 (path_hSP x y) _ _). simpl. *)
    
  (*   destruct x as [A x]. destruct y as [B y]. simpl in e,p. simpl. *)
  (*   destruct A as [A fA]. destruct B as [B fB]. destruct p. rewrite concat_p1. simpl. *)
  (*   unfold path_hSP. simpl. *)

  (*   refine (_ @ apD011 (path_sigma (fun a : Finite_Types => a.1 -> X) ((A; fA); x) ((B; fB); fun x0 : B => x (e^-1 x0))) _ _). *)
    
  (*   simpl. *)

  (*              (ecompose_eV (equiv_equiv_path x.1 y.1)) *)


  (*              (path_equiv (path_arrow _ _ (eisretr  (equiv_path x.1 y.1)) )) *)
  (*              @ p) *)


  (* Definition path_hSP_1 {X : Type} (x : hSymmetric_Product X) :  *)
  (*   path_hSP x x 1 1 = 1. *)
  (* Proof. *)
  (*   destruct x as [A x]. *)
  (*   unfold path_hSP. simpl. *)
  (*   assert (transport_exp_finite 1 x  *)
    
  (*   assert (h : 1 = path_universe_uncurried (A := A) 1). apply inverse.  apply path_universe_1.  destruct h. *)

  Definition path_hSP_compose {X : pType} (x y z : hSymmetric_Product X)
             (e1 : x.1.1 <~> y.1.1) (p1 : x.2 o e1^-1 = y.2)
             (e2 : y.1.1 <~> z.1.1) (p2 : y.2 o e2^-1 = z.2)
    : path_hSP x y e1 p1 @ path_hSP y z e2 p2 = path_hSP x z (e2 oE e1) (ap (fun x => x o e2^-1) p1 @ p2).
  Proof.
    Abort.
  (*   destruct x as [[A fA] x]. destruct y as [[B fB] y]. destruct z as [[C fC] z]. simpl. *)
  (*   simpl in x, y, z, e1, p1, e2, p2.  simpl. destruct p1. destruct p2. *)
  (*   repeat rewrite concat_p1.  *)
  (*   (* refine ((path_sigma_pp_pp _ _ _ _ _)^ @ _). *) *)
  (*   (* assert ((path_sigma_hprop (A; fA) (B; fB) (path_universe_uncurried e1) @ *) *)
  (*   (*  path_sigma_hprop (B; fB) (C; fC) (path_universe_uncurried e2)) = *) *)
  (*   (*         (path_sigma_hprop (A; fA) (C; fC) (path_universe_uncurried (e2 oE e1)))). *) *)
  (*   (* { change (path_universe_uncurried (e2 oE e1)) with (path_universe (e2 o e1)). *) *)
  (*   (*   change (path_universe_uncurried e2) with (path_universe e2). *) *)
  (*   (*   change (path_universe_uncurried e1) with (path_universe e1). *) *)
      
      
      
  (*   (*   rewrite (path_universe_compose e1 e2). *) *)
      
    
  (*   (* srefine (_ @ *) *)
  (*   (*           apD011 *) *)
  (*   (*           (path_sigma *) *)
  (*   (*              (fun A0 : Finite_Types => A0 -> X) ((A; fA); x) ((C; fC); x o (e1^-1 o e2^-1)) *) *)
  (*   (*                                                               ) *) *)
  (*   (*           _ _). *) *)
    

    
  (*   (* assert (equiv_path _ _ (path_universe_uncurried e1) = e1). apply eisretr. destruct X0. *) *)
    
    

    
  (*   (* revert p1 p2.  *)(* revert x y z. revert fA fB fC. *) *)
  (*   (* revert e2. *) *)
  (*   (* generalize (path_universe_uncurried e1). *) *)
  (*   revert x. revert fA fB fC. *)
  (*   revert e2 e1. revert B C. *)
  (*   srapply @equiv_induction'. intro B. simpl. revert A B. *)
  (*   srapply @equiv_induction'. intro A. simpl. *)
  (*   intros. *)
  (*   assert (h : fA = fB). apply ishprop_finite. destruct h. *)
  (*   assert (h : fA = fC). apply ishprop_finite. destruct h. *)
  (*   change (fun x0 : A => x x0) with x. *)
  (*   unfold path_hSP. simpl. *)
  (*   assert ((path_sigma_hprop (A; fA) (A; fA) (path_universe_uncurried 1)) = 1). *)
  (*   { change (path_universe_uncurried 1) with (path_universe (A:=A) idmap). *)
  (*     rewrite path_universe_1. *)
  (*     apply path_sigma_hprop_1. } *)
  (*   refine ((path_sigma_pp_pp _ _ _ _ _)^ @ _). simpl.  *)
  (*   assert (path_sigma (fun a : Finite_Types => a -> X) ((A; fA); x) ((A; fA); x) *)
  (*                      (path_sigma_hprop (A; fA) (A; fA) (path_universe_uncurried 1)) = *)
  (*           path_sigma (fun a : Finite_Types => a -> X) ((A; fA); x) ((A; fA); x) 1). *)
                       
  (*                       = 1). *)
  (*   {  *)
  (*   { change (path_universe_uncurried 1) with (path_universe (A:=A) idmap). *)
  (*     assert (path_sigma (fun a : Finite_Types => a -> X) ((A; fA); x) ((A; fA); x) *)
  (*   (path_sigma_hprop (A; fA) (A; fA) (path_universe idmap)) = *)
  (*             (path_sigma (fun a : Finite_Types => a -> X) ((A; fA); x) ((A; fA); x) *)
  (*   (path_sigma_hprop (A; fA) (A; fA) 1))). *)
      
  (*     apply inverse. unfold transport_exp_finite. *)
  (*     srefine (_ @ apD011 (path_sigma (fun a : Finite_Types => a -> X) ((A; fA); x) ((A; fA); x)) *)
  (*               (ap (path_sigma_hprop (A; fA) (A; fA)) path_universe_1)^ *)
  (*                  _). admit. admit. admit. *)
  (*     rewrite path_universe_1. *)

  (*     transitivity *)
  (*       (path_sigma (fun a : Finite_Types => a -> X) ((A; fA); x) ((A; fA); x) *)
  (*       (path_sigma_hprop (A; fA) (A; fA) 1) (transport_exp_finite (A := (A;fA)) 1 x)). *)
    
  (*   repeat rewrite concat_p1. *)
  (*   unfold transport_exp_finite. *)
  (*   assert (path_universe_uncurried (A := A ) 1 = 1). apply path_universe_1. rewrite X0. *)

    
  (*   simpl. *)
  (*   rewrite ( *)
    
  (*   unfold path_hSP. simpl. *)
  (*   destruct p1. destruct p2. simpl. repeat rewrite concat_p1. *)
  (*   assert (path_sigma (fun a : Finite_Types => a -> X) ((A; fA); x) ((A; fA); fun x0 : A => x x0) *)
  (*   (path_sigma_hprop (A; fA) (A; fA) (path_universe_uncurried 1)) (transport_exp_finite 1 x) = 1). *)
  (*   assert (h : path_universe_uncurried (A := A) 1 = 1). *)
  (*   { apply path_universe_1. } destruct h. *)
    
  (*   destruct (path_universe_1 (A := A)). *)
  (*   assert (h : 1 = (path_sigma_hprop (A; fA) (A; fA) (path_universe_uncurried 1))). *)

  (*   { apply inverse. *)
  (*     transitivity *)
  (*       (path_sigma_hprop (A; fA) (A; fA) 1). *)
  (*     -  apply (ap (path_sigma_hprop (A; fA) (A; fA))). *)
  (*        apply path_universe_1. *)
  (*     - apply path_sigma_hprop_1. }  *)
  (*   destruct h. *)
    
         
    
  (*   unfold transport_exp_finite. *)

    
  (*   transitivity idpath. *)
  (*   refine ((path_sigma_pp_pp _ _ _ _ _)^ @ _). simpl. *)
  (*    (@ecompose_e1 _ A A 1). *)

    
  (*   apply (equiv_induction' *)
  (*            (fun A B e1 => *)
  (*               forall (e2 : B <~> C) (fA : Finite A) (fB : Finite B) (x : A -> X)  *)
  (*   (y : B -> X) (z : C -> X) (p1 : (fun x0 : B => x (e1^-1 x0)) = y) (p2 : (fun x0 : C => y (e2^-1 x0)) = z), *)
  (* path_hSP ((A; fA); x) ((B; fB); y) e1 p1 @ path_hSP ((B; fB); y) ((C; fC); z) e2 p2 = *)
  (* path_hSP ((A; fA); x) ((C; fC); z) (e2 oE e1) (ap (fun (x0 : B -> X) (x1 : C) => x0 (e2^-1 x1)) p1 @ p2))). *)
  (*   simpl. *)

                
                  
  (*   apply (equiv_induction'  e1). *)
    
  (*   unfold path_hSP. *)
    
  (*   refine ((path_sigma_pp_pp _ _ _ _ _)^ @ _). *)
  (*   apply (ap (path_sigma (fun A0 : Finite_Types => A0 -> X) (A; x) (C; z))). *)

  (* (* Not sure if this is needed *) *)
  (* Definition transport_equiv_plus1 {A B1 B2: Type} (e : B1 <~> B2) (f : B1 + Unit <~> A) : *)
  (*   transport (fun B => B + Unit <~> A) (path_universe_uncurried e) f = f oE *)
  (*                                                                 (equiv_inverse (equiv_functor_sum' e 1%equiv)). *)
  (* Proof. *)
  (*   transitivity (f oE (((equiv_inverse (equiv_path_universe _ _)) (path_universe_uncurried e)) +E 1)^-1). *)
  (*   { destruct (path_universe_uncurried e). simpl. *)
  (*     apply emoveL_eV.  *)
  (*     apply path_equiv. apply path_arrow. intro b. simpl. *)
  (*     destruct b as [b | []]; reflexivity. } *)
  (*   apply path_equiv. *)
  (*   apply (ap (fun g => f o g)). simpl. *)
  (*   apply path_arrow. intros [b | []]. simpl. *)
  (*   { apply (ap inl). *)
  (*     apply (moveR_transport_V idmap (path_universe e) b _). apply inverse. *)
  (*     refine (ap10 (transport_idmap_path_universe e) (e^-1 b) @ _). *)
  (*     apply eisretr. } *)
  (*   reflexivity. *)
  (* Defined. *)

  (* Sum in hSP *)
  Definition hSP_sum {X : Type} :
    hSymmetric_Product X -> hSymmetric_Product X -> hSymmetric_Product X.
  Proof.
    intros [[A fA] x] [[B fB] y]. simpl in x,y.
    srapply @exist.
    {exists (A + B). exact _. }
    simpl. intros ab. 
    exact (match ab with
             |inl a => x a
             |inr b => y b
           end).
  Defined.

  End Homotopy_Symmetric_Product.



Section Normalize.
  Context {X : pType}.
  Context {dec_ne : forall x : X, Decidable (~ x = point X)}.
          

  (* The normalized form of a tuple *)
  Definition norm :
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
  Definition inclusion_from_norm  {A : Type} (x : A -> X) :
    {a : A & x a <> point X} -> A := pr1.

  (* Definition isfunctor_sum_incl {X : pType} {A : Type} (x : A + Unit -> X) : *)
  (*   inclusion_from_norm x == functor_sum (inclusion_from_norm (x o inl)) (fun t => tt) *)
  (*                                        o equiv_sigma_sum A Unit (fun a => x a <> point X). *)
  (* Proof.  *)
  (*   intros [[a | []] ne]; reflexivity. *)
  (* Defined. *)


  (* The length of a tuple *)
  Definition len  : hSymmetric_Product X -> nat := fun x => fcard x.1.

  (* The length of the normalization is less than the length *)
  Definition len_norm_leq (x : hSymmetric_Product X) :
    (len (norm x) <= len x)%nat.
  Proof.
    apply leq_card_subset.
  Defined.

  (* The lenght of the norm is either equal or less than the length *)
  Definition len_norm_lt_or_eq (x : hSymmetric_Product X) :
    (len (norm x) < len x)%nat + (len (norm x) = len x).
  Proof.
    apply lt_or_eq. apply len_norm_leq.
  Defined.
  
  (* isequiv_compose *)
  (* (* A lemma that should be elsewhere *) *)
  (* Definition ap_pred {m n : nat} : S m = S n -> m = n := ap pred. *)

  (* If the length of x and norm x are equal, then none of the points of x are x0 *)
  Definition eq_len_no_basept (x : hSymmetric_Product X) :
    len (norm x) = len x -> forall a : x.1, x.2 a <> point X.
  Proof.
    revert x.
    srapply @hSP_ind_hprop.
    intros n x. simpl.    
    intro p.
    (* Now we can do induction on n *)    
    induction n.
    - intros [].                (* The base case is trivial *)
    - assert (equiv_sum :
                {a : Fin n.+1 & x a <> point X} <~> {a : Fin n & x (inl a) <> point X} + (x (inr tt) <> point X)).
      { refine (_ oE equiv_sigma_sum _ _ _).
        srapply @equiv_functor_sum'.
        - exact equiv_idmap.
        - apply equiv_iff_hprop_uncurried.
          apply pair.
          + intros [[] ne]. exact ne.
          + intro ne. exact (tt; ne). }
      destruct (dec_ne (x (inr tt))).
      (* If (x (inr tt)) <> x0, then norm (Fin n+1, x) <~> norm (Fin n, x o inl) + 1 *)
      (* and the result follows from induction *)
      + intros [a | []].
        * apply (IHn (x o inl)).
          (set (ap_pred := (fun m n => @ap nat nat pred (S m) (S n) ): forall {m n : nat}, S m = S n -> m = n)).
          apply (ap_pred). clear ap_pred. simpl in p.
          refine (_ @ p).
          assert (equiv_sum' : {a : Fin n.+1 & x a <> point X} <~> {a : Fin n & x (inl a) <> point X} + Unit).
          { refine (_ oE equiv_sum).
            apply equiv_functor_sum_l.
            apply if_hprop_then_equiv_Unit. exact _. exact n0. }
          unfold len.
          refine (fcard_equiv' equiv_sum'^-1). (* inverse because I am doing ad hoc changes *)
        * exact n0.
      (* If not (x (inr tt)) <> x0, then norm (Fin n+1, x) <~> norm (Fin n, x o inl) *)
      (* But then len (norm (Fin n, x o inl)) = n+1 > n by assumption, so we get a contradiction *)
      + apply Empty_rec.
        assert (equiv_sum' : {a : Fin n.+1 & x a <> point X} <~> {a : Fin n & x (inl a) <> point X}).
        { refine (_ oE equiv_sum).
          refine (sum_empty_r _ oE _).
          apply equiv_functor_sum_l.
          apply if_not_hprop_then_equiv_Empty. exact _. exact n0. }
        assert (p' : (n.+1%nat = fcard {a : Fin n & x (inl a) <> point X})).
        { refine (p^ @ _).
          exact (fcard_equiv' equiv_sum'). }
        assert (leq : (fcard {a : Fin n & x (inl a) <> point X} <= n)%nat).
        { change n with (fcard (canon n)). apply (leq_card_subset (canon n)). }
        apply (not_nltn n). destruct p'. exact leq.
  Defined.

        
  (* If the length of x and norm x are equal, then the inclusion is an equivalence *)
  (* This can be generalized to all decidable propositions over hSP X *)
  Definition eq_len_isequiv_incl (x : hSymmetric_Product X) :
    len (norm x) = len x -> IsEquiv (inclusion_from_norm x.2).
  Proof.
    intro p.
    srapply @isequiv_pr1_contr. intro a.
    apply contr_inhabited_hprop. exact _.
    apply (eq_len_no_basept x p).
  Defined.

  Definition equiv_eq_len_isequiv_incl (x : hSymmetric_Product X) :
    len (norm x) = len x <~> IsEquiv (inclusion_from_norm x.2).
  Proof.
    apply equiv_iff_hprop_uncurried.
    unfold iff.
    apply pair.
    - apply eq_len_isequiv_incl.
    - intro isequiv. apply (ap len).
      srapply @path_hSP.
      apply (BuildEquiv _ _ (inclusion_from_norm x.2) isequiv).
      apply equiv_emoveR_fV. apply path_arrow. intro a.  reflexivity.
  Defined.

  Definition isequiv_norm  (x : hSymmetric_Product X) : DHProp.
  Proof.
    apply (Build_DHProp (BuildTruncType -1 (IsEquiv (inclusion_from_norm x.2)))).
    apply (decidable_equiv' (len (norm x) = len x) (equiv_eq_len_isequiv_incl x)).
    apply decidable_paths_nat.
  Defined.

  Definition isequiv_norm_to_id 
             (x : hSymmetric_Product X) :
    isequiv_norm x -> norm x = x.
  Proof.
    unfold isequiv_norm. simpl.
    intro H.
    srapply @path_hSP.
    apply (BuildEquiv _ _ (inclusion_from_norm x.2) H).
    apply equiv_emoveR_fV. apply path_arrow. intro a. reflexivity.
  Defined.

  Definition isequiv_norm_norm (x : hSymmetric_Product X) :
    isequiv_norm (norm x).
  Proof.
    srapply @isequiv_pr1_contr. intros [a ne]. apply contr_inhabited_hprop. exact _. exact ne.
  Defined.

  (* Just put this here because i want it to have this name  *)
  Definition eq_len_isequiv_norm (x : hSymmetric_Product X) :
    len (norm x) = len x -> isequiv_norm x := (eq_len_isequiv_incl x).


End Normalize.


Module Export Gamma_Plus.
  Context (X : pType).
  Context {dec_me_bp : forall x : X, Decidable (merely (x = point X))}.

  Definition me_or_ne_bp : forall x : X, merely (x = point X) + (x <> point X).
  Proof.
    intro x.
    destruct (dec_me_bp x).
    - exact (inl t).
    - apply inr. intro p. apply n. exact (tr p).
  Defined.

  Definition contr_me_or_ne_bp : forall x : X, Contr (merely (x = point X) + (x <> point X)).
  Proof.
    intro x.
    apply (BuildContr _ (me_or_ne_bp x)).
    intros [meq1 | neq1]; destruct (me_or_ne_bp x) as [meq2 | neq2].
    - apply (ap inl). apply (istrunc_truncation -1).
    - apply Empty_rec. strip_truncations. exact (neq2 meq1).
    - apply Empty_rec. strip_truncations. exact (neq1 meq2).
    - apply (ap inr). apply (trunc_arrow (n:= -1)).
  Qed.
    
  Instance dec_ne_bp : forall x : X, Decidable (x <> point X).
  Proof.
    intro x.
    destruct (dec_me_bp x).
    - apply inr. strip_truncations. intro ne. exact (ne t).
    - apply inl. intro p. apply n. exact (tr p).
  Defined.
    
  (* Should perhabs be Decidable (merely (x = point X))? *)
  (* Context {dec_me_bp : forall x : X, Decidable (merely (x = point X)) *)

  Definition x0 := (point X).

  (* Given a choice of  *)
  Definition normplus
             (A : Finite_Types)
             (x : A -> X)
             (path_choice : forall a : A, merely (x a = x0) -> x a = x0) :
    (A; x) = hSP_sum
               (norm (A; x))
               ((({a : A & merely (x a = x0)};
                    finite_detachable_subset (fun a : A => merely (x a = x0)));
                   const x0)).
  Proof.
    srapply @path_hSP.
    - simpl. refine (equiv_sum_symm _ _ oE _).
      refine (_ oE (equiv_sigma_contr (fun a : A => merely (x a = x0) + (x a <> x0)))^-1).
      + exact (equiv_inverse (equiv_sigma_sum' A (fun a => Trunc (-1) (x a = x0)) (fun a => x a <> x0))).
      + intro a. apply contr_me_or_ne_bp.
    - simpl.
      destruct A as [A fA]. simpl.
      apply path_arrow. 
      intros [[a neq] | [a meq]].
      + reflexivity.
      + apply (path_choice a meq).
  Defined.

  

  

  (* Defining Gamma_Plus as a HIT*)
  (* This is shamelessly copied from the definition of Coeq. *)
  Private Inductive Gamma_Plus :=
    v : hSymmetric_Product X -> Gamma_Plus.

  (* To get a path [v x = v y] in Gamma_Plus, all you need is a path in [v N x = v N y]*)
  Axiom l : forall (x y : hSymmetric_Product X) (len_lt : (len x < len y)%nat),
                   norm x = norm y -> v x = v y.

  (* From this we get a path v x = v N x for all x *)
  Definition n {x : hSymmetric_Product X} :
    v (norm x) = v x.
  Proof.
    destruct (len_norm_lt_or_eq x).
    - apply (l _ _ t).
      apply (isequiv_norm_to_id _ (isequiv_norm_norm x)).
    - apply (ap v).
      apply isequiv_norm_to_id.
      apply eq_len_isequiv_norm. exact p.
  Defined.

  (* The induction principle for Gamma_Plus *)
  Definition Gamma_Plus_ind (P : Gamma_Plus -> Type)
                                  (v' : forall (x : hSymmetric_Product X), P (v x))
                                  (l' : forall (x y : hSymmetric_Product X)
                                               (len_lt: (len x < len y)%nat)
                                               (p : norm x = norm y),
                                               transport P (l x y len_lt p) (v' x) = v' y) :
      forall g : Gamma_Plus, P g :=
    fun g => (match g with | v x => v' x end).

  Axiom Gamma_Plus_ind_beta_d : forall (P : Gamma_Plus -> Type)
                                       (v' : forall (x : hSymmetric_Product X), P (v x))
                                       (l' : forall (x y : hSymmetric_Product X)
                                                    (len_lt: (len x < len y)%nat)
                                                    (p : norm x = norm y),
                                           transport P (l x y len_lt p) (v' x) = v' y)
                                       (x y : hSymmetric_Product X)
                                       (len_lt: (len x < len y)%nat)
                                       (p : norm x = norm y),
      apD (Gamma_Plus_ind P v' l') (l x y len_lt p) = l' x y len_lt p.

  Definition Gamma_Plus_rec (P : Type)
             (v' : hSymmetric_Product X -> P)
             (l' : forall (x y : hSymmetric_Product X),
                          (len x < len y)%nat -> (norm x = norm y) -> v' x = v' y)
    := Gamma_Plus_ind (fun _ => P) v' (fun  (x y : hSymmetric_Product X)
                                            (len_lt: (len x < len y)%nat)
                                            (p : norm x = norm y)
                                       => transport_const (l x y len_lt p) _ @ l' x y len_lt p).

  Definition Gamma_rec_beta_d (P : Type)
             (v' : hSymmetric_Product X -> P)
             (l' : forall (x y : hSymmetric_Product X),
                          (len x < len y)%nat -> (norm x = norm y) -> v' x = v' y)
             (x y: hSymmetric_Product X)
             (len_lt: (len x < len y)%nat)
             (p : norm x = norm y)
    : ap (Gamma_Plus_rec P v' l') (l x y len_lt p) = l' x y len_lt p.
  Proof.
    unfold Gamma_Plus_rec.
    eapply (cancelL (transport_const (l x y len_lt p) _)).
    refine ((apD_const (@Gamma_Plus_ind (fun _ => P) v' _) (l x y len_lt p))^ @ _).
    refine (Gamma_Plus_ind_beta_d (fun _ => P) _ _ _ _ _ _).
  Defined.

  (* Norm is well defined om Gamma_Plus *)
  Definition N : Gamma_Plus -> Gamma_Plus.
  Proof.
    srapply @Gamma_Plus_rec.
    - exact (v o norm).
    - intros x y len_lt p.
      exact (ap v p).
  Defined.


  (* If I can do this, then the definition is wrong *)
  Definition shouldbewrong (x : Gamma_Plus) : N x = x.
  Proof.
    revert x. srapply @Gamma_Plus_ind.
    - intro x. simpl.
      apply n.
    - intros. simpl.
      refine (transport_paths_FlFr (l x y len_lt p) n @ _).
      rewrite ap_idmap. unfold n.
      destruct (len_norm_lt_or_eq x) as [lt_norm_x | eq_norm_x];
        destruct (len_norm_lt_or_eq y) as [lt_norm_y | eq_norm_y]; admit.
      Abort.
  (* Can't manage to to this (luckily) *)

  (* If X is connected, it should still not be contractible *)
  Definition shouldbewrong2
             (normisempty : forall (x : hSymmetric_Product X), norm x = (canon 0; Empty_rec)) :
    forall x : Gamma_Plus, x = v (canon 0; Empty_rec).
  Proof.
    srapply @Gamma_Plus_ind.
    - intro x. simpl.
      refine (n^ @ _). apply (ap v). apply normisempty.
    - intros.
      refine (transport_paths_l _ _ @ _).
      apply moveR_Vp.
      
      apply l.
             

  

  
  
  










  (* 9/4: Below here is old definition. *)
  
  (* Defining Gamma_Plus as a HIT*)
  (* This is shamelessly copied from the definition of Coeq. *)
  Private Inductive Gamma_Plus :=
    t : hSymmetric_Product X -> Gamma_Plus.

  Definition x0 := (point X).

  
  (* A tuple should be equal to its normalization, i.e. removing all instances of the basepoint. *)
  (* We need an argument that the length of x and its normalized form are not equal to ensure that we don't   *)
  (* add paths that are already there. *)
  (* Also we want this to depend on a choice of path x a = x0 wherever this is possible, or else we end up killing *)
  (* paths in X. *)
  Axiom d : forall (x : hSymmetric_Product X),
      (forall a : x.1, merely (x.2 a = x0) -> x.2 a = x0) -> ~(isequiv_norm x) -> t x = t (norm x).

  (* (* If a tuple is already equal its normalized form, then we should kill the extra path *) *)
  (* Axiom x : forall {n} (x : hSymmetric_Product n X), IsEquiv (inclusion_of_norm x) *)

  

  (* The induction principle for Gamma_Plus *)
  Definition Gamma_Plus_ind (P : Gamma_Plus -> Type)
                                  (t' : forall (x : hSymmetric_Product X), P (t x))
                                  (d' : forall (x : hSymmetric_Product X)
                                               (c : forall a : pr1 x, merely (pr2 x a = x0) -> pr2 x a = x0)
                                               (ne : ~(isequiv_norm x)),
                                      transport P (d x c ne) (t' x) = t' (norm x)) :
      forall g : Gamma_Plus, P g :=
    fun g => (match g with | t x => t' x end).
    


  Axiom Gamma_Plus_ind_beta_d : forall (P : Gamma_Plus -> Type)
                                       (t' : forall (x : hSymmetric_Product X), P (t x))
                                       (d' : forall (x : hSymmetric_Product X)
                                                    (c : forall a : pr1 x, merely (pr2 x a = x0) -> pr2 x a = x0)
                                                    (ne : ~(isequiv_norm x)),
                                           transport P (d x c ne) (t' x) = t' (norm x))
                                       (x : hSymmetric_Product X)
                                       (c : forall a : pr1 x, merely (pr2 x a = x0) -> pr2 x a = x0)
                                       (ne : ~(isequiv_norm x)),
      apD (Gamma_Plus_ind P t' d') (d x c ne) = d' x c ne.

  Definition Gamma_Plus_rec (P : Type)
             (t' : hSymmetric_Product X -> P)
             (d' : forall (x : hSymmetric_Product X),
                          (forall a : pr1 x, merely (pr2 x a = x0) -> pr2 x a = x0) ->
                          (~(isequiv_norm x)) -> t' x = t' (norm x))
    := Gamma_Plus_ind (fun _ => P) t' (fun  (x : hSymmetric_Product X)
                                            (c : forall a : pr1 x, merely (pr2 x a = x0) -> pr2 x a = x0)
                                            (ne : ~(isequiv_norm x))
                                       => transport_const (d x c ne) _ @ d' x c ne).

  Definition Gamma_rec_beta_d (P : Type)
             (t' : hSymmetric_Product X -> P)
             (d' : forall (x : hSymmetric_Product X),
                 (forall a : pr1 x, merely (pr2 x a = x0) -> pr2 x a = x0) ->
                 (~(isequiv_norm x)) -> t' x = t' (norm x))
             (x : hSymmetric_Product X)
             (c : forall a : pr1 x, merely (pr2 x a = x0) -> pr2 x a = x0)
             (ne : ~(isequiv_norm x))
    : ap (Gamma_Plus_rec P t' d') (d x c ne) = d' x c ne.
  Proof.
    unfold Gamma_Plus_rec.
    eapply (cancelL (transport_const (d x c ne) _)).
    refine ((apD_const (@Gamma_Plus_ind (fun _ => P) t' _) (d x c ne))^ @ _).
    refine (Gamma_Plus_ind_beta_d (fun _ => P) _ _ _ _ _).
  Defined.

  (* Norm is well defined om Gamma_Plus *)
  Definition N : Gamma_Plus -> Gamma_Plus.
  Proof.
    srapply @Gamma_Plus_rec.
    - exact (t o norm).
    - intro x.
      (* intros [[A fA] x]. simpl in x. *)
      intros c ne.
      apply (ap t). apply inverse.
      apply isequiv_norm_to_id. exact (isequiv_norm_norm x).
  Defined.

  Arguments proj1_sig _ _  _ : simpl nomatch.
  Arguments proj2_sig _ _  _ : simpl nomatch.

  (* (* Being constantly x0 is well defined *) *)
  (* Definition isconst : Gamma_Plus -> Type. *)
  (* Proof. *)
  (*   srapply @Gamma_Plus_rec. *)
  (*   - intros [A x]. exact (forall a : A, x a = x0). *)
  (*   - intros [[A fA] x]. simpl.  intros c ne. simpl in x. *)
  (*     srapply @path_universe. *)
  (*     + intro eq. *)
  (*       intros [a neq]. destruct (neq (eq a)). *)
  (*     + srapply @BuildIsEquiv. *)
  (*       * intro eq. apply Empty_rec. apply ne. *)
  (*         apply (eq_len_isequiv_incl ((A;fA);x)). *)
  (*         unfold len. unfold fcard. simpl. *)
  (*         revert eq. *)

  (*         eq_len_no_basept *)
  (*         bruk hProp_ind over. . . *)
    
  
  (* If all x a are x0. then N x is empty *)

  (* An easier to use variant of d *)
  Definition d' : forall (x : hSymmetric_Product X),
      (forall a : x.1, merely (x.2 a = x0) -> x.2 a = x0) -> t x = t (norm x).
  Proof.
    intros x eq.
    destruct (dec (isequiv_norm x)) as [isequiv | notequiv].
    - apply (ap t). apply inverse.
      apply isequiv_norm_to_id. exact isequiv.
    - apply (d _ eq notequiv).
  Defined.


  (* Showing that monomorphisms give equalities in Gamma_Plus *)
  Definition path_Gamma_Plus {A B : Finite_Types} {x : A -> X} {y : B -> X}
             (f : A -> B)
             {ismono_f : forall a1 a2 : A, f a1 = f a2 -> a1 = a2}
             (y_extends_x : forall b : B,
                 match (dec (hfiber f b)) with
                   |inl in_image => y b = x in_image.1
                   |inr f => y b = x0
                 end)
    : t (A; x) = t (B; y).      (* load finite *)
  Proof.
  
  (* Now we want a proof that everything in Gamma_Plus is equal to its norm if x = x0 is a proposition*)
  Definition eq_to_norm {isprop_eq : forall x : X, IsHProp (x = x0)} : forall x : Gamma_Plus, x = N x.
  Proof.
    srapply @Gamma_Plus_ind.
    - intro x. simpl.
      apply (d' x).
      intro a. apply Trunc_rec. exact idmap.
    (* -  *)
    (*   destruct (dec (isequiv_norm x)) as [isequiv | notequiv]. *)
    (*   + apply (ap t). apply inverse. apply (isequiv_norm_to_id x isequiv). *)
    (*   + apply (d x). *)
    (*     { intro a. apply Trunc_rec. exact idmap. } exact notequiv. *)
    - intros.
      refine (transport_paths_FlFr _ _ @ _).
      unfold d'.
      (* Now to get the correct cases. *)
      assert (p : (inr ne) = dec (isequiv_norm x)). 
      { apply ishprop_decidable_hprop. apply hprop_isequiv. }
      destruct p.
      assert (p : (inl (isequiv_norm_norm x)) = dec (isequiv_norm (norm x))).
      { apply ishprop_decidable_hprop. apply hprop_isequiv. } destruct p. 
      assert (p : c = (fun a : x.1 => Trunc_rec idmap)).
      { apply (trunc_forall (n := -1)). }
      destruct p.
      rewrite ap_idmap. rewrite concat_Vp. rewrite concat_1p.
      refine (Gamma_rec_beta_d _ _ _ _ _ _ ).
  Qed.

  (* Constant terms are equal to the empty term *)
  Definition const_bp_is_bp : forall A : Finite_Types,
      t (A; const x0) = t (canon 0; Empty_rec).
  Proof.
    intro A.
    refine (d' _ _ @ _).
    - simpl. intro a. intro. reflexivity.
    - apply (ap t).
      apply path_hSP.
      destruct A as [A fA]. simpl.
      srapply @exist.
      + srapply @BuildEquiv.
        intros [a ne]. apply ne. reflexivity.
      + apply path_arrow. intros [].
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
  Definition ispointed_gamma_plus {X : pType} : IsPointed (Gamma_Plus) :=
    t (canon 0; Empty_rec).

  (* When proving a proposition we only need to prove it for the symmetric products. *)
  Definition Gamma_Plus_ind_hProp (P : Gamma_Plus -> Type)
             {isprop_P : forall g : Gamma_Plus, IsHProp (P g)}
             (t' : forall (x : hSymmetric_Product X), P (t x)) :
    forall g : Gamma_Plus, P g.
  Proof.
    apply (Gamma_Plus_ind P t').
    intros. apply isprop_P.
  Defined.

  (* Sum on Gamma_Plus *)
  Definition Gamma_Plus_sum : Gamma_Plus -> Gamma_Plus -> Gamma_Plus.
  Proof.
    intro x. srapply @Gamma_Plus_rec.
    revert x. srapply @Gamma_Plus_rec.
    (* Both variables are tuples *)
    - intros x y. apply t.
      exact (hSP_sum x y).
    (* x runs along d *)
    - intros x choice_path_x neqiv. simpl. apply path_arrow. intro y. simpl in choice_path_x.
      (* Should go via the norm of both, but so that it doesn't depend on the equalities in y *)
      transitivity (t (norm ((hSP_sum (norm x) y)))).
      transitivity (t (norm (hSP_sum x y))).
      + apply d'. destruct x as [[A fA] x]. destruct y as [[B fB] y]. simpl. simpl in x, eq, y.
        intros [a | b]. simpl in eq. apply eq. admit.
      + apply (ap t). admit.
      + apply inverse. apply d'. intros [a | b]. apply eq. admit.
    - intros y eq nequiv. simpl. admit.
  
  
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