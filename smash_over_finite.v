Require Import HoTT.
Require Import type_over.
Require Import finite_lemmas.
Require Import pointed_lemmas.
Require Import type_over.
Require Import pushout_lemmas.



Definition embedding (X Y : Type) := {f : X -> Y & IsEmbedding f}.
Definition embedding_to_arrow {X Y : Type} :
  embedding X Y -> (X -> Y) := pr1.
Coercion embedding_to_arrow : embedding >-> Funclass.

Section Functor_prod.
  Definition functor_prod_fin {A B : Finite_Types} {X : A -> pType} (f : embedding B A) :
    (forall b : B, X (f b)) -> (forall a : A, X a).
  Proof.
    intro x. intro a.
    destruct f as [f emb].
    destruct (detachable_image_finite f a) as [[b p] | nhitA].
    - exact (transport X p (x b)). 
    - exact (point (X a)).
  Defined.
  
  (* Definition functor_exp {X : pType} {A B : Finite_Types} (f : embedding B A)  : *)
  (*   (B -> X) -> (A -> X). *)
  (* Proof. *)
  (*   intro x. intro a. *)
  (*   destruct f as [f emb]. *)
  (*   destruct (detachable_image_finite f a) as [[b p] | nhitA]. *)
  (*   - exact (x b). *)
  (*   - exact (point X). *)
  (* Defined. *)

  Definition issect_functor_prod_fin {A B : Finite_Types} {X : A -> pType} (f : embedding B A) (x : forall b : B, X (f b)) :
    forall b : B, (functor_prod_fin f x (f b) = x b).
  Proof.
    intro b. unfold functor_prod_fin. destruct f as [f emb]. cbn.    
    destruct (detachable_image_finite f (f b)) as [[b' p] | ].
    -  

      refine (_ @ apD x (isinj_embedding f emb b' b p)). simpl.
      refine (_ @ (transport_compose X f (isinj_embedding f emb b' b p) (x b'))^).
      cut (p = (ap f (isinj_embedding f emb b' b p))). intro q. destruct q. reflexivity.
      unfold isinj_embedding.
      refine (_ @ ap_compose pr1 f (path_ishprop (b'; p) (b; 1))).
      unfold path_ishprop.
      transitivity (ap pr1 (path_sigma (fun b' : B => f b' = f b)
      
      
      
      destruct (isinj_embedding f emb b' b p).

      apply (ap x).
      apply (isinj_embedding f emb b' b p).
    - apply Empty_rec. apply n. exists b. reflexivity.
  Defined.
End Exponentials.



Definition base_to_sum (A : Type) (X : A -> pType) : A -> {a : A & X a} := fun a => (a; point (X a)).


Definition Wedge {A : Type} (X : A -> pType) : Type
  := pushout (const tt) (base_to_sum A X).

(* uncurry constructors *)
Definition pt {A : Type} {X : A -> pType} : Wedge X := push_fl tt.
Definition wsummand {A : Type} {X : A -> pType} (a : A)
  : X a -> Wedge X
  := fun x => push_fr (a;x).
Definition wp {A : Type} {X : A -> pType} (a : A)
  : pt = (wsummand a (point (X a)))
  := pp (f:= const tt) (g := base_to_sum A X) a.

Definition wedge_ind {A : Type} (X : A -> pType)
           (P : Wedge X -> Type)
           (pt' : P pt)
           (wsummand' : forall (a : A) (x : X a), P (wsummand a x))
           (wp' : forall (a : A), transport P (wp a) pt' = wsummand' a (point (X a)))
  : forall x : Wedge X, P x.
Proof.
  srapply @pushout_ind'. intros []. exact pt'.
  intros [a x]. exact (wsummand' a x).
  exact wp'.
Defined.

Definition wedge_rec {A : Type} (X : A -> pType)
           (P : Type)
           (pt' : P)
           (wsummand' : forall (a : A), X a -> P)
           (wp' : forall (a : A), pt' = wsummand' a (point (X a)))
  : Wedge X -> P.
Proof.
  srapply @pushout_rec'. intros []. exact pt'.
  intros [a x]. exact (wsummand' a x).
  exact wp'.
Defined.

Definition functor_wedge {A : Type} (X : A -> pType) (B : Type) (f : B -> A) :
           Wedge (fun b : B => X (f b)) -> Wedge X.
Proof.
  srapply @functor_pushout. exact f. exact idmap.
  cbn. intros [b x]. exact (f b; x).
  intro b. reflexivity.
  simpl. intro b. reflexivity.
Defined.

Definition functor_wedge_compose {A : Type} (X : A -> pType) (B : Type) (f : B -> A) (C : Type) (g : C -> B) :
  functor_wedge X C (f o g) == functor_wedge X B f o functor_wedge (fun b : B => X (f b)) C g.
Proof.
  intro x. 
  refine (_ @ functor_pushout_compose _ _ _ _ _ _ _ _ _ _ x). reflexivity.
Defined.

Definition wedge_to_prod {A : Finite_Types} (X : A -> pType)
  : Wedge X -> (forall a : A, X a).
Proof.
  srapply @wedge_rec.
  - intro a. exact (point (X a)).
  - intros a x. intro a'.
    destruct (decidablepaths_finite A a a').
    + destruct p. exact x.
    + exact (point (X a')).
  - intro a. apply path_forall. intro a'.
    destruct (decidablepaths_finite A a a').
    + cbn. destruct p. reflexivity.
    + reflexivity.
Defined.

Definition natural_wedge_to_prod {A : Finite_Types} (X : A -> pType)


(* The set {1,...,n} *)
Definition one_to (n : nat) := Fin n.
(* Definition pred_one_to {n : nat} : one_to n -> Unit + one_to n. *)
(* Proof. *)
(*   intro k.  *)

Context (X : pType).
Context (n : nat).
Context (U : one_to n -> Finite_Types -> pType).
Context (i : forall (k : one_to n) (A: Finite_Types),
            U k A -> (A -> X)).
Context (l : forall (k : one_to n) {A B : Finite_Types} (f : embedding B A),
            U k B -> U k A).
Context (natl : forall (k : one_to n) {A B : Finite_Types} (f : embedding B A),
            (i k A) o (l k A B f) = (functor_exp f) o (i k B)).

(* l_compose, U k is pushout, i, l, natl given by pushout induction *)

                    







(* -------------------------------------------------------------- *)

Context (X : pType).

(* Want to define the union over all (B -> X) where B are finite subtypes of A *)
(* Filter finite subtypes of A by cardinality *)

Definition functor_exp (A : Finite_Types) (B : Finite_Subsets A)  :
  (B -> X) -> (A -> X).
Proof.
  destruct B as [B [f emb]]. cbn.
  intro x. intro a.
  destruct (detachable_image_finite f a) as [[b p] | nhitA].
  - exact (x b).
  - exact (point X).
Defined.

Definition type_over_of_subset {A : Finite_Types} : (Finite_Subsets A) -> Type_Over (A -> X).
Proof.
  intro B.
  apply (Build_Type_Over (B -> X)). apply functor_exp.
Defined.


(* The intersection between a type over X^A and X^B *)
Definition intersect_with_power {A : Finite_Types} (B : Finite_Subsets A) (Y : Type_Over (A -> X)) : Type
  := { xy : (B -> X) * Y &
               forall b : B, (fst xy) b = arrow_of_over Y (snd xy) (B.2.1 b) }.

Definition intersection_to_left {A : Finite_Types} (n : nat) (Y : Type_Over (A -> X)) :
  {B : finite_subset_component A n & intersect_with_power B Y} -> {B : finite_subset_component A n & (B -> X)}.
Proof.
  intros [B [[x y] p]]. exists B. exact x.
Defined.

Definition intersection_to_right {A : Finite_Types} (n : nat) (Y : Type_Over (A -> X)) :
  {B : finite_subset_component A n & intersect_with_power B Y} -> Y.
Proof.
  intros [B [[x y] p]]. exact y.
Defined.


Definition glue_prod {A : Finite_Types} (n : nat) (Y : Type_Over (A -> X)) :=
  pushout (intersection_to_left n Y) (intersection_to_right n Y).

(* Think of Y as the base that we glue products X^B to. *)

Definition prod_in {A : Finite_Types} {n : nat} (Y : Type_Over (A -> X))
           {B : finite_subset_component A n} :
  (B -> X) -> glue_prod n Y.
Proof.
  intro x. apply (push o inl). exact (B; x).
Defined.

Definition base {A : Finite_Types} (n : nat) {Y : Type_Over (A -> X)}
  : Y -> glue_prod n Y
  := push o inr.

Definition gp {A : Finite_Types} {n : nat} {Y : Type_Over (A -> X)}
           {B : finite_subset_component A n}
           (x : B -> X) (y : Y)
           (eq_under_B : forall b : B, x b = arrow_of_over Y y (B.2.1 b))
  : prod_in Y x = base n y
  := (pp (B; ((x,y); eq_under_B))).

Definition glue_prod_ind {A : Finite_Types} {n : nat} (Y : Type_Over (A -> X))
           (P : glue_prod n Y -> Type)
           (prod_in' : forall (B : finite_subset_component A n) (x : B -> X),
               P (prod_in Y x))
           (base' : forall y : Y, P (base n y))
           (gp' : forall (B : finite_subset_component A n) (x : B -> X) (y : Y) (eq_under_B : forall b : B, x b = arrow_of_over Y y (B.2.1 b)),
               transport P (gp x y eq_under_B) (prod_in' B x) = base' y)
  : forall x : glue_prod n Y, P x.
Proof.
  unfold glue_prod. srapply @pushout_ind.
  - intros [[B x] | y].
    + apply prod_in'.
    + apply base'.
  - intros [B [[x y] eq_over_B]]. apply gp'.
Defined.
  
Definition glue_prod_ind_beta_gp {A : Finite_Types} (n : nat) (Y : Type_Over (A -> X))
           (P : glue_prod n Y -> Type)
           (prod_in' : forall (B : finite_subset_component A n) (x : B -> X),
               P (prod_in Y x))
           (base' : forall y : Y, P (base n y))
           (gp' : forall (B : finite_subset_component A n) (x : B -> X) (y : Y) (eq_under_B : forall b : B, x b = arrow_of_over Y y (B.2.1 b)),
               transport P (gp x y eq_under_B) (prod_in' B x) = base' y)
           {B : finite_subset_component A n}
           (x : B -> X) (y : Y)
           (eq_under_B : forall b : B, x b = arrow_of_over Y y (B.2.1 b)) :
  apD (glue_prod_ind Y P prod_in' base' gp') (gp x y eq_under_B) = gp' B x y eq_under_B.
Proof.
  srapply @pushout_ind_beta_pp.
Defined.

Definition glue_prod_rec {A : Finite_Types} {n : nat} (Y : Type_Over (A -> X))
           (P : Type)
           (prod_in' : forall (B : finite_subset_component A n),
               (B -> X) -> P)
           (base' : Y -> P)
           (gp' : forall (B : finite_subset_component A n) (x : B -> X) (y : Y) (eq_under_B : forall b : B, x b = arrow_of_over Y y (B.2.1 b)),
               prod_in' B x = base' y)
  : glue_prod n Y -> P.
Proof.
  srapply @pushout_rec.
  - intros [[B x] | y].
    + exact (prod_in' B x).
    + exact (base' y).
  - intros [B [[x y] eq_over_B]]. apply gp'. cbn. apply eq_over_B.
Defined.

Definition glue_prod_rec_beta_gp {A : Finite_Types} {n : nat} (Y : Type_Over (A -> X))
           (P : Type)
           (prod_in' : forall (B : finite_subset_component A n),
               (B -> X) -> P)
           (base' : Y -> P)
           (gp' : forall (B : finite_subset_component A n) (x : B -> X) (y : Y) (eq_under_B : forall b : B, x b = arrow_of_over Y y (B.2.1 b)),
               prod_in' B x = base' y)
           {B : finite_subset_component A n}
           (x : B -> X) (y : Y)
           (eq_under_B : forall b : B, x b = arrow_of_over Y y (B.2.1 b)) :
  ap (glue_prod_rec Y P prod_in' base' gp') (gp x y eq_under_B) = gp' B x y eq_under_B.
Proof.
  srapply @pushout_rec_beta_pp.
Defined.

Definition glue_prod_to_prod {A : Finite_Types} {n : nat} (Y : Type_Over (A -> X)) :
  glue_prod n Y -> (A -> X).
Proof.
  srapply @glue_prod_rec.
  - intro B.
    apply (functor_exp A B).
  - apply (arrow_of_over Y).
  - intros B x y eq_over_B.
    cbn.
    apply path_arrow. destruct B as [B [f emb]].
    intro a. unfold functor_exp. cbn.
    recall (detachable_image_finite f a) as d eqn:q. destruct d as [[b p] | not_inb].
    + rewrite q. destruct p. apply eq_over_B.
    + rewrite q. clear q.
      
      
      
      
    destruct  as [ | ]. cbn.
    + destruct p. 
      refine (_ @ eq_over_B b). 

      admit.
    +                           (* doesn't work *)
Abort.

Definition union_of_products {A : Finite_Types} (n : nat) : Type_Over (A -> X).
Proof.
  induction n.
  (* n is 0 *)
  - apply (Build_Type_Over Unit). intro t. exact (const (point X)).
  - apply (Build_Type_Over (glue_prod n.+1 IHn)).
    
  

           
               
  





Define gp, glue_prod_ind, glue_prod_ind_beta_gp

       
  