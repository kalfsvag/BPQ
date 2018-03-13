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
Definition Finite_Types (n : nat) :=
  {A : Type & merely (A <~> Fin n)}.

Definition type_of {n : nat} (A : Finite_Types n) := pr1 A.
Coercion type_of : Finite_Types >-> Sortclass.

(* Canonical finite types *)
Definition canon (n : nat) : Finite_Types n :=
  (* (Fin n; tr idpath). *)
  (Fin n; tr 1%equiv).

(* Record Finite_Types (n : nat) := *)
(*   {finite_type : Type ; isfinite_finite_type : merely (finite_type <~> Fin n)}. *)
(* Coercion finite_type : Finite_Types >-> Sortclass. *)

(* Plus one for finite types *)
Definition add_one {n : nat} : Finite_Types n -> Finite_Types n.+1.
Proof.
  intros [A H].
  exists (A + Unit).
  strip_truncations.
  apply tr. (* apply path_universe_uncurried. *)
  (* exact (equiv_functor_sum' ((equiv_path_universe A (Fin n))^-1 H) equiv_idmap). *)
  exact (equiv_functor_sum' H equiv_idmap).
Defined.

Definition path_finite_types {n : nat} (s t : Finite_Types n):
  (s.1 <~> t.1) <~> s = t :=
  equiv_path_sigma_hprop _ _ oE equiv_path_universe _ _.
  

(* This should more or less follow from baut_ind_hset (except that is only for P: Type -> Type*)
Definition BSigma_ind_hSet (n : nat) (P : Finite_Types n -> Type)
           {isset_P : forall s : Finite_Types n, IsHSet (P s)}
           (pt : P (canon n))
           (wd : forall e : Fin n <~> Fin n, transport P (path_finite_types (canon n) (canon n) e) pt = pt) :
  forall s : Finite_Types n, P s.
Proof.
  intro s.
  apply (@pr1 (P s) (fun p => forall e' : canon n <~> s, transport P (path_finite_types (canon n) s e') pt = p)).
  assert (isprop_goal : forall s' : Finite_Types n,
            IsHProp {p : P s' & forall e' : canon n <~> s', transport P ((path_finite_types (canon n) s') e') pt = p}).
  { destruct s' as [A eA]. strip_truncations.
    apply trunc_sigma'.
    - intro p. apply trunc_forall.
    - intros p q.
      apply (contr_inhabited_hprop _).
      destruct p as [p fp]. destruct q as [q fq]. simpl. simpl in fp. simpl in fq.
      exact ((fp (equiv_inverse eA))^ @ (fq (equiv_inverse eA))). }
  destruct s as [A eA]. strip_truncations.
  destruct (path_finite_types (canon n) (A; tr eA) (equiv_inverse eA)).
  exact (pt; wd).
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
  

(* Open Scope nat. *)
Section Homotopy_Symmetric_Product.
  (* The symmetric product (I think) *)
  Definition hSymmetric_Product (n : nat) (X : Type) :=
    {A : Finite_Types n & (A -> X)}.

  (* To get a function out of hSP n into a set, you need a function out of the product which does not depend on  *)
  (* permutations n <~> n *)
  Definition hSP_rec_hset {n : nat} {X : pType} (P : Type)
             {isset_P : IsHSet P}
             (f : ((Fin n -> X) -> P))
             (welldef : forall (x : Fin n -> X) (e : Fin n <~> Fin n), f (x o e) = f x)
    : hSymmetric_Product n X -> P .
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
    - intro e. apply path_arrow. intro.
      change (fun s : Finite_Types n => (s -> X) -> P) with
      (fun s : {A : Type  & merely (A <~> Fin n)} => (s.1 -> X)-> P).
      refine (transport_arrow_toconst (path_sigma_hprop (canon n) (canon n) (path_universe_uncurried e)) f x @ _).
      (* transitivity (f (x o e)). *)
      (* transitivity *)
      (*   (p (transport (fun x0 : {A : Type & merely (A <~> Fin n)} => x0.1 -> X) *)
      (*                 (path_sigma_hprop (canon n) (canon n) (path_universe_uncurried e))^ (x o e))). *)
      refine (_ @ welldef x e).
      apply (ap f).
      unfold path_sigma_hprop.
      
      apply (moveR_transport_V (fun x0 : {A : Type & Trunc (-1) (A <~> Fin n)} => x0.1 -> X)
            (path_sigma_uncurried (fun A : Type => merely (A <~> Fin n)) (canon n) (canon n)
                                  (pr1^-1 (path_universe_uncurried e)))).
      apply inverse.
      transitivity (transport (fun A : Type => A -> X)
                              (pr1^-1 (path_universe_uncurried e)).1 (x o e)).
      + apply ap10. refine (@transport_pr1_path_sigma_uncurried
                              (Type)
                              (fun A => Trunc (-1) (A <~> Fin n))
                              (canon n) (canon n)
                              (pr1^-1 (path_universe_uncurried e))
                              (fun A => A -> X)).
      + simpl. (* change (path_universe_uncurried e) with (path_universe e). *)
        refine (transport_exp X (Fin n) (Fin n) e (x o e) @ _).
        apply path_arrow. intro i. apply (ap x). apply (eisretr e).
  Defined.
      

    
  (* transport_arrow_toconst *)

  (* Another way of defining the symmetric product *)
  (* I feel I have done this before, but I cannot find it. . . *)
  Definition equiv_other_SP {n : nat} {X : Type} :
    hSymmetric_Product n X <~> {A : Type & ((merely (A <~> Fin n)) * (A -> X))%type}.
  Proof.
    unfold hSymmetric_Product.
    srapply @equiv_adjointify.
    - intros [[A Hx] x]. exists A. exact (Hx, x).
    - intros [A [Hx x]].
      exact ((A; Hx) ; x).
    - unfold Sect. intros [A [Hx x]]. reflexivity.
    - unfold Sect. intros [[A Hx] x]. reflexivity.
  Defined.

  Definition prod_to_SP {n : nat} {X : Type} : (Fin n -> X) -> hSymmetric_Product n X :=
    fun x => ((Fin n; (tr 1%equiv)); x).

  (* Definition path_SP {n : nat} {X : Type} {x y : hSymmetric_Product n X} : *)
  (*   {f : x.1 <~> y.1 & x.2 = y.2 o f} -> x = y. *)
  (* Proof. *)
  (*   destruct x as [[A eA] x]. destruct y as [[B eB] y]. simpl. *)
  (*   intros [f p]. *)
  (*   srapply @path_sigma; simpl. *)
  (*   - apply path_sigma_hprop. exact (path_universe_uncurried f). *)
  (*   - refine (transport_exp _ _ _ f _ @ _). *)
    
    

  (* Given elements (A,x) (B,y) in the symmetric product, the identity type (A,x) = (B,y) should be the type
 {f : A<~>B & x = y o f}.*)
  Definition equiv_path_hSP {n : nat} {X : Type} (x y : hSymmetric_Product n X) :
    x = y <~> {f : x.1 <~> y.1 & x.2 = y.2 o f}.
  Proof.
    refine (_ oE (equiv_ap equiv_other_SP x y)).
    refine (_ oE equiv_path_sigma _ _ _).
    destruct x as [[A Hx] x]. simpl in x.
    destruct y as [[B Hy] y]. simpl in y.
    simpl.
    transitivity {p : A = B & transport (fun a : Type => a -> X) p x = y}.
    - apply equiv_functor_sigma_id. intro p.
      transitivity ((transport (fun a : Type => merely (a <~> Fin n)) p Hx = Hy)*
                    (transport (fun a : Type => a -> X) p x = y))%type.
      + refine (_ oE (equiv_concat_l (transport_prod p _) _)^-1).
        apply equiv_inverse.
        (* For some reason, [apply equiv_path_prod] doesn't work here *)
        exact (equiv_path_prod
                 (transport (fun a : Type => Trunc (-1) (a <~> Fin n)) p Hx,
                  transport (fun a : Type => a -> X) p x) (Hy, y)).
      + refine ((prod_unit_l _) oE _).
        refine (equiv_functor_prod' _ 1%equiv).
        apply equiv_contr_unit.
    - apply equiv_inverse.
      refine (equiv_functor_sigma'(equiv_path_universe A B) _).
      intro e. simpl.
      change (fun x0 : A => y (e x0)) with (y o e).
      transitivity (x o e^-1 = y).
      + apply equiv_emoveR_fV.
      + apply equiv_concat_l.
        apply transport_exp.
  Defined.

  Definition path_hSP {n : nat} {X : Type} {x y : hSymmetric_Product n X} (f : x.1 <~> y.1) (p : x.2 = y.2 o f) :
    x=y.
  Proof.
    exact ((@equiv_path_hSP n X x y)^-1 (f; p)).
  Defined.
  

  (* Given a point in X, we can add it to the end of the symmetric product *)
  Definition hSP_cons {n : nat} {X : Type} (x0 : X) (x : Fin n -> X) : hSymmetric_Product n.+1 X.
  Proof.
    exists (canon n.+1).
    exact (sum_rect _ x (fun _ => x0)).
  Defined.
End Homotopy_Symmetric_Product.


Module Export Gamma_Plus.
  (* Defining Gamma_Plus as a HIT*)
  (* This is shamelessly copied from the definition of Coeq. *)
  Private Inductive Gamma_Plus (X : pType) :=
    t (n : nat) : hSymmetric_Product n X -> Gamma_Plus X.

  Arguments t {X} {n} _.
  (* This is perhaps stupid, but from here, x0 is always the basepoint of something. *)
  Local Notation "'x0'" := (point _).

  (* We want a path (A,x) = (A+1, (x,x0)) *)
  (* Axiom d : forall {X : pType} {n} (x : hSymmetric_Product n X), t (hSP_cons x0 x) = t x. *)
  Axiom d : forall {X : pType} {n} (x : Fin n -> X), t (hSP_cons (point X) x) = t (canon n; x).

  (* The induction principle for Gamma_Plus *)
  Definition Gamma_Plus_ind {X} (P : Gamma_Plus X -> Type)
                                  (t' : forall {n : nat} (x : hSymmetric_Product n X), P (t x))
                                  (d' : forall {n : nat} (x : Fin n -> X),
                                      transport P (d x) (t' (hSP_cons x0 x)) = t' (canon n; x)) :
      forall g : Gamma_Plus X, P g :=
    fun g => (match g with | @t _ n x => t' x end).
    

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

  
  
  (* A result needed for showing that this is well defined *)
  (* This is just copied from fin_equiv_hfiber, but I wanted it as its own result *)
  Local Lemma is_inl_transpose1 {n : nat} (e : Fin n.+1 <~> Fin n.+1) (y : Fin n) (p : e (inr tt) = inl y) :
        forall a : Fin n, is_inl ((fin_transpose_last_with n (inl y) oE e) (inl a)).
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

  Local Lemma is_inr_transpose1 {n : nat} (e : Fin n.+1 <~> Fin n.+1) (y : Fin n) (p : e (inr tt) = inl y) :
    forall b : Unit, is_inr ((fin_transpose_last_with n (inl y) oE e) (inr b)).
  Proof.
    intros []. ev_equiv.
    rewrite p.
    rewrite fin_transpose_last_with_with; exact tt.
  Qed.

  Local Lemma is_inl_transpose2 {n : nat} (e : Fin n.+1 <~> Fin n.+1) (p : e (inr tt) = inr tt)
    : forall a : Fin n, is_inl (e (inl a)).
  Proof.
    intro a.
    destruct (is_inl_or_is_inr (e (inl a))) as [l|r].
    - exact l.
    - assert (q := inr_un_inr (e (inl a)) r).
      apply moveR_equiv_V in q.
      assert (s := q^ @ ap (e^-1 o inr) (path_unit _ _) @ (moveL_equiv_V _ _ p)^).
      elim (inl_ne_inr _ _ s).
  Qed.

  Local Lemma is_inr_transpose2 {n : nat} (e : Fin n.+1 <~> Fin n.+1) (p : e (inr tt) = inr tt) :
    forall b : Unit, is_inr (e (inr b)).
  Proof.
    intros []; exact (p^ # tt).
  Defined.
  
  Definition equiv_restrict {n : nat} (e : Fin n.+1 <~> Fin n.+1) : Fin n <~> Fin n.
  Proof.
    simpl in e.
    recall (e (inr tt)) as y eqn:p.
    assert (p' := (moveL_equiv_V _ _ p)^).
    destruct y as [y | []].
    (*  *)
    - apply (equiv_unfunctor_sum_l (fin_transpose_last_with n (inl y) oE e)
                                   (is_inl_transpose1 e y p) (is_inr_transpose1 e y p)).
    - apply (equiv_unfunctor_sum_l e (is_inl_transpose2 e p) (is_inr_transpose2 e p)).
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
        

  Definition equiv_restrict_fix_last {n : nat} (e : Fin n.+1 <~> Fin n.+1) (p : e (inr tt) = inr tt):
    Fin n <~> Fin n.   (* {e' : Fin n <~> Fin n & e o inl = inl o e'}. *)
  Proof.
    exact (equiv_unfunctor_sum_l e (is_inl_transpose2 e p) (is_inr_transpose2 e p)).
    
  Defined.
    
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

  Definition natural_equiv_restrict {n : nat} (e : Fin n.+1 <~> Fin n.+1) (p : e (inr tt) = inr tt) :
    inl o (equiv_restrict_fix_last e p) == e o inl.
  Proof.
    intro x. apply unfunctor_sum_l_beta.
  Defined.

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