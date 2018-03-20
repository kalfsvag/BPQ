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


(* Record Finite_Types (n : nat) := *)
(*   {finite_type : Type ; isfinite_finite_type : merely (finite_type <~> Fin n)}. *)
(* Coercion finite_type : Finite_Types >-> Sortclass. *)

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
  


      



  
           

(* Definition functor_trunc {n : trunc_index} {A B : Type} (f : A -> B) : Trunc n A -> Trunc n B := *)
(*   Trunc_rec (tr o f). *)

(* Definition trunc_inv {n : trunc_index} (A : Type) : Trunc n (Trunc n A -> A). *)
(* Proof. *)
  

(* (* Not sure if this needs a point in A, but it is enouch for my purposes *) *)
(* Definition forall_merely_to_merely_forall {A : Type} (P : A -> Type) (a : A): *)
(*   (forall a : A, merely (P a)) -> merely (forall a : A, P a). *)
(* Proof. *)
(*   intro f. *)
(*   set (fa := f a). generalize fa. intro. strip_truncations. apply tr. *)
(*   intro a0. exact fa0. *)
(*   apply functor_trunc.  *)
  

(* The proposition that all finite types are equivalent to canonical finite types *)
(* Definition merely_canonical `{Funext} {n : nat} : merely (forall A : Finite_Types n, A = (Fin n; tr 1%equiv)). *)
(* Proof. *)
(*   unfold merely. simpl. *)
(*   IsTrunc_internal *)

  
  
(*   set (f := pr2 : (forall A : (Finite_Types n), merely (A <~> Fin n))). *)
(*   assert (forall A : (Finite_Types n), merely (A = (Fin n; tr 1%equiv))). *)
(*   { intro A. generalize (f A). apply Trunc_rec. intro e. apply tr. apply (path_sigma_hprop). exact (path_universe e). } *)
  
  
(*   set (x :=  *)
(*   set (f1 := functor_sigma idmap (fun _ => tr) : {A : Type & A <~> Fin n} -> Finite_Types n). *)
(*   set (f2 := (fun f  : =>  *)
(*   apply (functor_trunc (functor_forall f1 idmap)). *)
  
(*   set (x := pr2 : (forall A : (Finite_Types n), merely (A <~> Fin n))). *)
(*   set (H2 := trunc_forall  *)
(*   revert H. intro. *)
(*   apply (@functor_forall  *)





  
  

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
  (* (* Perhaps not right to call this induction, but. . . *) *)
  (* Definition hSP_ind_hset {n : nat} {X : pType} (P : Type) *)
  (*            {isset_P : IsHSet P} *)
  (*            (f : ((Fin n -> X) -> P)) *)
  (*            (welldef : forall (x : Fin n -> X) (e : Fin n <~> Fin n), f (x o e) = f x) *)
  (*            : forall s : Finite_Types n,  (s -> X) -> P . *)
  (* Proof. *)


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

  (* Definition isequiv_path_SP {X : Type} {x y : hSymmetric_Product X} : *)
  (*   IsEquiv (path_SP x y). *)
  (* Proof. *)
  (*   srapply @isequiv_adjointify. *)
  (*   - refine (_ o (path_sigma_uncurried _ x y)^-1). *)
  (*     srapply @functor_sigma. *)
  (*     + apply (path_finite_types x.1 y.1)^-1. *)
  (*     + simpl. intros p q. *)


  (*       Check transport_exp_finite (path_universe (equiv_path x.1 y.1 p)). *)
  (*       refine (_ @ q). *)
  (*       apply path_arrow. intro. *)
  (*       refine (transport_exp_finite *)

        
  (*       apply (equiv_path x.1 y.1). *)
      
  (*     intro p. *)
  (*     exists ((path_finite_types x.1 y.1)^-1 p..1). *)
  (*     destruct p. reflexivity. *)
  (*   - intro.  unfold path_SP. rewrite (eisretr (path_finite_types x.1 y.1)). *)
  (*     simpl. destruct x as [A x]. destruct y as [B y]. simpl. *)
      
  (*     apply path_arrow. intro b. *)
  (*     refine (_ @ transport_exp_finite *)

  (*     destruct p. *)
  (*     exists (1%equiv). reflexivity. *)
  (*   - intro p. destruct p. *)
  (*     unfold path_SP. rewrite concat_p1. *)
  (*     change (path_sigma *)
  (*               (fun A : Finite_Types => A -> X) x x *)
  (*               ((path_finite_types x.1 x.1) 1%equiv) (transport_exp_finite 1 x.2)) with *)
  (*     (path_sigma_uncurried *)
  (*        (fun A : Finite_Types => A -> X) x x *)
  (*        ((path_finite_types x.1 x.1) 1%equiv; transport_exp_finite 1 x.2)).         *)
  (*     apply (moveR_equiv_M). simpl. *)
  (*     srapply @path_sigma. *)
  (*     + simpl. *)
  (*       unfold path_universe_uncurried. *)
  (*       refine (_ @ path_sigma_hprop_1 _). *)
  (*       apply (ap (path_sigma_hprop x.1 x.1)). *)
  (*       apply moveR_equiv_V. reflexivity. *)
  (*     + simpl. *)

      
  (*     change  *)
      
  (*     refine (_ @ eta_path_sigma idpath). simpl. *)


  (*     isequiv_path_sigma *)

  (*     simpl. unfold path_finite_types. *)
  (*     destruct p.  *)
  (*     unfold path_SP. *)
  (*     unfold path_finite_types. simpl. unfold path_universe_uncurried. *)
  (*     destruct x as [A x]. simpl. *)
  (*     rewrite concat_p1. *)

  (*     simpl. *)
  (*     assert (forall A : Type, ((equiv_path A A)^-1 1%equiv) = idpath). *)
  (*     { intro A'. apply moveR_equiv_V. reflexivity. } *)
  (*     apply (apD010 (path_sigma (fun A0 : Finite_Types => A0 -> X) (A; x) (A; x))). *)
  (*     rewrite X0. *)
      
      
      
  (*     change (equiv_path A.1 A.1)^-1 with (@path_universe_uncurried _ A.1 A.1). *)
  (*     rewrite concat_p1. unfold path_universe_uncurried. *)
  (*     change (path_universe_uncurried 1) with (@path_universe _ A.1 A.1 idmap). *)
  (*     rewrite path_universe_1. *)
      
      
  (*     rewrite <- equiv_path_V. *)
      
  (*     transitivity *)
  (*       (path_sigma (fun A : Finite_Types => A -> X) x x idpath (transport_exp_finite 1 x.2 @ 1)). *)
      
  (*     unfold transport_exp_finite. simpl. *)

  (*     destruct x as [A x]. destruct y as [B y]. simpl. *)
  (*     intro p. *)
  (*     recall ((path_sigma_uncurried _ _ _)^-1 p) as p' eqn:h. *)
  (*     destruct p' as [p1 p2]. *)
  (*     destruct ((path_sigma_uncurried _ _ _)^-1 p) as [p1 p2]. simpl. clear p. *)


      
  (*     exists ((path_finite_types _ _)^-1 p1). *)
      
  (*     simpl. *)
  (*     refine (_ @ p2). *)
  (*     refine (_ @ (transport_exp_finite *)
  (*     simpl. *)

  (*     transitivity *)

  (*     destruct x as [A x]. destruct y as [B y]. simpl. *)
  (*     intro p. destruct *)
  (*     unfold hSymmetric_Product in x, y. *)
    
    

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

  (* (* Sanity check *) *)
  (* Definition check {X : Type} (x y : hSymmetric_Product X) : *)
  (*   (path_hSP x y) = (equiv_path_hSP x y)^-1. *)
  (* Proof. *)
  (*   apply path_arrow. intros [e p]. *)
  (*   apply moveL_equiv_V. destruct x as [A x]. destruct y as [B y]. simpl in p. destruct p. simpl. *)
  (*   unfold path_hSP. *)


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

  (* The inclusion of the underlying set of ther normalized tuple *)
  Definition inclusion_of_norm {X : pType} {dec_ne : forall x : X, Decidable (~ x = point X)}
             (x : hSymmetric_Product X) := pr1 :
                                               (norm x).1 -> x.1.



  
  (* Definition prop_choice_minus1 {n : nat} (A : Finite_Types n.+1) : *)
  (*   IsHProp {B : Type & B + Unit <~> A}. *)
  (* Proof. *)
  (*   intros [B1 f1] [B2 f2]. *)
  (*   srapply @BuildContr. *)
  (*   srapply @path_sigma. *)
  (*   - simpl. apply path_universe_uncurried. *)
  (*     admit. *)
  (*   - simpl. *)
  (*     refine (transport_equiv_plus1 _ f1 @ _). *)

  (*   simpl. *)
  (*   intros a b. *)

  (* Definition contr_choice_minus1 {n : nat} (A : Finite_Types n.+1) : *)
  (*   Contr {B : Type & B + Unit <~> A}. *)
  (* Proof. *)
  (*   destruct A as [A eA]. strip_truncations. destruct (path_universe eA)^. simpl. *)
  (*   srapply @BuildContr. *)
  (*   - exists (canon n). *)
  (*     exact 1%equiv. *)
  (*   - intros [B e]. *)
  (*     (* two cases: e (inr tt) is (inr tt) or not *) *)
  (*     recall (e (inr tt)) as i eqn:p. *)
  (*     destruct i as [i | []]. *)
  (*     (* e (inr tt) is inl i *) *)
  (*     + srapply @path_sigma. *)
  (*       * simpl. srapply @path_universe_uncurried.  *)
  (*         (* want an equivalence that fixes the endpoint *) *)
  (*         srapply @equiv_restrict_last_fixed. *)
  (*         { exact (equiv_inverse (fin_transpose_last_with n (e (inr tt)) oE e)). } *)
  (*         simpl. *)
  (*         apply moveR_equiv_V. apply moveR_equiv_V. apply inverse. *)
  (*         apply (fin_transpose_last_with_with). *)
  (*       * refine (transport_equiv_plus1 _ 1 @ _). simpl. *)
  (*         apply path_equiv. apply path_arrow. *)
  (*         intros [b | []]. *)
  (*         { simpl. *)
  (*           refine (unfunctor_sum_l_beta _ _ b @ _). *)
  (*           admit. } *)
  (*         simpl.                (* argh *) *)
          
  (*         admit. *)

  (*     + (srapply @path_sigma). simpl. *)
  (*       srapply @path_universe_uncurried. *)
  (*       { apply equiv_inverse. exact (equiv_restrict_last_fixed e p). } *)
  (*       simpl. *)
  (*       refine (transport_equiv_plus1 _ 1 @ _). *)
  (*       apply path_equiv. apply path_arrow. *)
  (*       intros [b | []]. *)
  (*       * simpl. *)
  (*         apply (unfunctor_sum_l_beta e _ b). *)
  (*       * simpl. exact p^. *)
        
        
        
          
  (*         destruct (path_universe e)^. *)
        
      
  (*     destruct (e (inr tt)). *)
  (*     srapply @path_sigma. *)
      
  (*     + simpl. destruct B as [B eB]. *)
  (*       apply path_finite_types.  simpl. *)
        
  (*       apply equiv_unfunctor_sum_l *)
        
  (*     apply path_finite_types. *)
  (*     apply (path_finite_types _ _). *)
  
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

  (* Definition finite_minus1 {n : nat} {A : Finite_Types n.+1} (a : A) : {B : Finite_Types n & B + Unit <~> A}. *)
  (* Proof. *)
  (*   apply (equiv_functor_sigma_id (fun B : (Finite_Types n) => issig_equiv (B + Unit) A)). *)
  (*   apply (functor_sigma idmap  *)
  (*    *)
    
  (*   ikke helt. . . *)
    
  (*   equiv_sigma_assoc *)

  (*   issig_equiv *)
          
    


  
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
  Axiom d : forall (x : hSymmetric_Product X), card_of x.1 <> card_of (norm x).1 -> t x = t (norm x).

  (* (* If a tuple is already equal its normalized form, then we should kill the extra path *) *)
  (* Axiom x : forall {n} (x : hSymmetric_Product n X), IsEquiv (inclusion_of_norm x) *)

  

  (* The induction principle for Gamma_Plus *)
  Definition Gamma_Plus_ind (P : Gamma_Plus -> Type)
                                  (t' : forall (x : hSymmetric_Product X), P (t x))
                                  (d' : forall (x : hSymmetric_Product X) (ne : card_of x.1 <> card_of (norm x).1),
                                      transport P (d x ne) (t' x) = t' (norm x)) :
      forall g : Gamma_Plus, P g :=
    fun g => (match g with | t x => t' x end).
    

    (* Definition Gamma_Plus_ind_beta_d_test : forall {X} {P : Gamma_Plus X -> Type} *)
    (*                                    (t' : forall (n : nat) (x : hSymmetric_Product n X), P (t x)) *)
    (*                                    (d' : forall (n : nat) (x : hSymmetric_Product n X), *)
    (*                                        transport P (d x) (t' n.+1 (hSP_cons (point X) x)) = t' n x) *)
    (*                                    {n} (x : hSymmetric_Product n X), Type. *)
    (*   intros. *)
    (*   Check (Gamma_Plus_ind P t' d'). *)
    (*   Check (apD (Gamma_Plus_ind P t' d') (d x)). *)
      
    (*   apD (Gamma_Plus_ind P t' d') (d x) = d' n x. *)


  
  Axiom Gamma_Plus_ind_beta_d : forall {X} (P : Gamma_Plus X -> Type)
                                       (t' : forall (n : nat) (x : hSymmetric_Product n X), P (t x))
                                       (d' : forall (n : nat) (x : Fin n -> X),
                                           transport P (d x) (t' (S n) (hSP_cons x0 x)) = t' n (canon n; x))
                                       {n} (x : Fin n -> X),
      apD (Gamma_Plus_ind P t' d') (d x) = d' n x.

  Definition Gamma_Plus_rec {X : pType} (P : Type)
             (t' : forall n : nat, hSymmetric_Product n X -> P)
             (d' : forall (n : nat) (x : Fin n -> X), t' (S n) (hSP_cons x0 x) = t' n (canon n; x))
    := Gamma_Plus_ind (fun _ => P) t' (fun  n (x : Fin n ->  X) => transport_const (d x) _ @ d' n x).

  Definition Gamma_rec_beta_d {X : pType} (P : Type)
             (t' : forall n : nat, hSymmetric_Product n X -> P)
             (d' : forall (n : nat) (x : Fin n -> X), t' (S n) (hSP_cons x0 x) = t' n (canon n; x))
             {n : nat} (x : Fin n -> X)
    : ap (Gamma_Plus_rec P t' d') (d x) = d' n x.
  Proof.
    unfold Gamma_Plus_rec.
    eapply (cancelL (transport_const (d x) _)).
    refine ((apD_const (@Gamma_Plus_ind X (fun _ => P) t' _) (d x))^ @ _).
    refine (Gamma_Plus_ind_beta_d (fun _ => P) _ _ _).
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