(* Trying to define \Gammma^+ as in Jardines "The Barratt-Priddy-Quillen Theorem" from 2009 *)
(* There it is defined as the homotopy colimit over all monomorphisms of a certain functor.*)
(* Monomorphisms can be factored into permutations and the inclusions n->n+1 not hitting the last point. *)
(* This we take advantage of to define the colimit in HoTT. The permutations come from univalence, and the rest is a normal HIT *)

Require Import HoTT.
Require Import UnivalenceAxiom.
(* Load finite. *)
Load stuff.

Definition Finite_Types (n : nat) :=
  {A : Type & merely (A <~> Fin n)}.

Definition type_of {n : nat} (A : Finite_Types n) := pr1 A.
Coercion type_of : Finite_Types >-> Sortclass.

(* Canonical finite types *)
Definition canon (n : nat) : Finite_Types n := (Fin n; tr 1%equiv).

(* Record Finite_Types (n : nat) := *)
(*   {finite_type : Type ; isfinite_finite_type : merely (finite_type <~> Fin n)}. *)
(* Coercion finite_type : Finite_Types >-> Sortclass. *)

(* Plus one for finite types *)
Definition add_one {n : nat} : Finite_Types n -> Finite_Types n.+1.
Proof.
  intros [A H].
  exists (A + Unit).
  strip_truncations.
  apply tr.
  exact (equiv_functor_sum' H equiv_idmap).
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

  (* Given elements (A,x) (B,y) in the symmetric product, the identity type (A,x) = (B,y) should be the type
 {f : A<~>B & x = y o f}.*)
  Definition path_SP {n : nat} {X : Type} (x y : hSymmetric_Product n X) :
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

  (* Given a point in X, we can add it to the end of the symmetric product *)
  Definition hSP_cons {n : nat} {X : Type} (x0 : X) : hSymmetric_Product n X -> hSymmetric_Product n.+1 X.
  Proof.
    intros [A x].    
    exists (add_one A).
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
  Notation "'x0'" := (point _).

  (* We want a path (A,x) = (A+1, (x,x0)) *)
  Axiom d : forall {X : pType} {n} (x : hSymmetric_Product n X), t (hSP_cons x0 x) = t x.

  (* The induction principle for Gamma_Plus *)
  Definition Gamma_Plus_ind {X} (P : Gamma_Plus X -> Type)
                                  (t' : forall {n : nat} (x : hSymmetric_Product n X), P (t x))
                                  (d' : forall {n : nat} (x : hSymmetric_Product n X),
                                      transport P (d x) (t' (hSP_cons x0 x)) = t' x) :
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
                                       (d' : forall (n : nat) (x : hSymmetric_Product n X),
                                           transport P (d x) (t' (S n) (hSP_cons x0 x)) = t' n x)
                                       {n} (x : hSymmetric_Product n X),
      apD (Gamma_Plus_ind P t' d') (d x) = d' n x.

  Definition Gamma_Plus_rec {X : pType} (P : Type)
             (t' : forall n : nat, hSymmetric_Product n X -> P)
             (d' : forall (n : nat) (x : hSymmetric_Product n X), t' (S n) (hSP_cons x0 x) = t' n x)
    := Gamma_Plus_ind (fun _ => P) t' (fun  n (x : hSymmetric_Product n X) => transport_const (d x) _ @ d' n x).

  Definition Gamma_rec_beta_d {X : pType} (P : Type)
             (t' : forall n : nat, hSymmetric_Product n X -> P)
             (d' : forall (n : nat) (x : hSymmetric_Product n X), t' (S n) (hSP_cons x0 x) = t' n x)
             {n : nat} (x : hSymmetric_Product n X)
    : ap (Gamma_Plus_rec P t' d') (d x) = d' n x.
  Proof.
    unfold Gamma_Plus_rec.
    eapply (cancelL (transport_const (d x) _)).
    refine ((apD_const (@Gamma_Plus_ind X (fun _ => P) t' _) (d x))^ @ _).
    refine (Gamma_Plus_ind_beta_d (fun _ => P) _ _ _).
  Defined.

  Definition canon_const {X : pType} {n : nat} :
    t (canon n; const x0) = t (canon 0; const x0) :> Gamma_Plus X.
  Proof.
    induction n.
    - reflexivity.
    - refine (_ @ IHn).
      refine (_ @ d (canon n; const x0)).
      apply (ap t).
      apply path_SP.
      exists 1%equiv.
      apply path_arrow. intros [x |]; reflexivity.
  Defined.
  
  Definition contr_const {X : pType} {n : nat}:
    forall B : Finite_Types n, Contr (t (B; const x0) = t (canon n; const x0) :> Gamma_Plus X).
  Proof.
    intros [B e]. strip_truncations.
    assert (t ((B; tr e); const x0) = t(canon n; const x0):>Gamma_Plus X).
    apply (ap t).
    apply path_SP. simpl.
    exists e. reflexivity.
    refine (trunc_equiv (t (canon n; const x0) = (t (canon n; const x0))) (fun p => X0  @ p)).
    clear X0.
    refine (trunc_equiv (t (canon 0; const x0) = (t (canon 0; const x0))) (fun p => (canon_const @ p @ canon_const^))).
    srapply @BuildContr.
    - reflexivity.
    -                           (* TODO *)
    

  
End Gamma_Plus.
