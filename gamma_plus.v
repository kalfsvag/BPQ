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
  Definition equiv_path_SP {n : nat} {X : Type} (x y : hSymmetric_Product n X) :
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

  Definition path_SP {n : nat} {X : Type} {x y : hSymmetric_Product n X} (f : x.1 <~> y.1) (p : x.2 = y.2 o f) :
    x=y.
  Proof.
    exact ((@equiv_path_SP n X x y)^-1 (f; p)).
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
  (*   apply path_SP. simpl. *)
  (*   exists e. reflexivity. *)
  (*   refine (trunc_equiv (t (canon n; const x0) = (t (canon n; const x0))) (fun p => X0  @ p)). *)
  (*   clear X0. *)
  (*   refine (trunc_equiv (t (canon 0; const x0) = (t (canon 0; const x0))) (fun p => (canon_const @ p @ canon_const^))). *)
  (*   srapply @BuildContr. *)
  (*   - reflexivity. *)
  (*   -                           (* TODO *) *)


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
  Context (isprop_basedpath : forall x : X, IsHProp (x = x0)).

  Definition code_Gamma_Plus : Gamma_Plus X -> Type.
  Proof.
    srapply @Gamma_Plus_rec.
    - intro n. intros [A x].
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

  Definition isequiv_encode_Gamma_Plus :
    forall g : Gamma_Plus X, IsEquiv (encode_Gamma_Plus g).
  Proof.
    (* srapply (@Gamma_Plus_ind_hProp X (fun g => IsEquiv (encode_Gamma_Plus g))). simpl. *)
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
      + apply (ap t). srapply @path_SP; simpl.
        * exact eA.
        * apply path_arrow. intro a. apply const_x.
      + clear eA.
        induction n. reflexivity.
        refine (_ @ IHn).
        refine (_ @ d (canon n; const x0)).
        unfold hSP_cons. apply (ap t).
        srapply @path_SP. exact 1%equiv.
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
        apply (path_SP 1%equiv).
        simpl.
        Check (
        p
        srapply @d.
        check
        apply d.
        
        exact (d (canon n; const x0) @ IHn).
      refine ((path_SP eA _ @ _)).
    

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
        srapply @path_SP.
        * simpl. exact eA.
        * simpl. apply path_arrow. intro a. apply (ap x).
          apply inverse. apply (eissect eA).
      + induction n.
        * transitivity (t (canon 0; const x0) = t (canon 0; const x0) :> Gamma_Plus X).
          {apply equiv_concat_l. apply (ap t).
           srapply @path_SP.
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