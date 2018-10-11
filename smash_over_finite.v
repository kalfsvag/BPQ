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
    (* intro x. *)
    (* apply (equiv_ind (split_range _ _ f _)^-1 _). *)
    (* intros [[a [b []]] | [a n]]; cbn. *)
    (* - exact (x b). *)
    (* - exact (point ( X a)). *)
    destruct f as [f emb].
    intros x a.
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
    intro b.
    unfold functor_prod_fin. destruct f as [f emb]. cbn.    
    destruct (detachable_image_finite f (f b)) as [[b' p] | ].
    - set (g := retract_of_embedding B A f _ b).
      set (H := (issect_embedding B A f _ b) : g o f == idmap).
      cut ({q : b' = b & ap f q = p}).
      + intros [q h]. destruct h. destruct q. reflexivity.
      + exists ((H b')^ @ ap g p @ (H b)).
        apply (isset_Finite A). exact _.
    - apply Empty_rec. apply n. exists b. reflexivity.
  Defined.
End Functor_prod.

Definition base_to_sum (A : Type) (X : A -> pType) : A -> {a : A & X a} := fun a => (a; point (X a)).


Definition Wedge {A : Type} (X : A -> pType) : Type
  := pushout (const tt) (base_to_sum A X).

(* uncurry constructors *)
Definition pt {A : Type} {X : A -> pType} : Wedge X := push_fl _ _ tt.
Definition wsummand {A : Type} {X : A -> pType} (a : A)
  : X a -> Wedge X
  := fun x => push_fr _ _ (a;x).
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

Definition functor_wedge_summand {A : Type} (X : A -> pType) (B : Type) (f : B -> A) :
  forall b : B, X (f b) -> {a : A & X a}.
Proof.
  intros b x. exact (f b; x).
Defined.  

Definition functor_wedge {A : Type} (X : A -> pType) (B : Type) (f : B -> A) :
           Wedge (fun b : B => X (f b)) -> Wedge X.
Proof.
  srapply @functor_pushout. exact f. exact idmap.
  - simpl. intros [b x]. apply (functor_wedge_summand X B f b x).
  - intro b. reflexivity.
  - intro b. reflexivity.
Defined.

Definition functor_wedge_compose {A : Type} (X : A -> pType) (B : Type) (f : B -> A) (C : Type) (g : C -> B) :
  functor_wedge X C (f o g) == functor_wedge X B f o functor_wedge (fun b : B => X (f b)) C g.
Proof.
  intro x. 
  refine (_ @ functor_pushout_compose _ _ _ _ _ _ _ _ _ _ x). reflexivity.
Defined.

Definition wedge_eta_homot {A : Type} {X : A -> pType} {P : Wedge X -> Type}
           (f : forall x : Wedge X, P x) :
  f == wedge_ind X P (f pt) (fun (a : A) (x : (X a)) => f (wsummand a x)) (fun a : A => apD f (wp a)).
Proof.
  srapply @wedge_ind; try reflexivity.
  - intro a.
    refine (transport_paths_FlFr_D
              (f := f)
              (g := wedge_ind X P (f pt) (fun (a0 : A) (x0 : X a0) => f (wsummand a0 x0)) (fun a0 : A => apD f (wp a0)))
              (wp a) idpath @ _).    
    simpl. apply moveR_Mp.
    refine (pushout_ind_beta_pp P _ _ _ @ _).
    cut (forall q : transport P (wp a) (f pt) = f (wsummand a (point (X a))), q = ((q^@1)^@1)).
    intro H. apply H.
    intros []. reflexivity.
Defined.

Definition wedge_rec_eta_homot {A : Type} {X : A -> pType} {P : Type}
           (f : Wedge X -> P)
  : f == wedge_rec X P (f pt) (fun a => f o (wsummand a)) (fun a => ap f (wp a)).
Proof.
  unfold pointwise_paths.
  srapply @wedge_ind; try reflexivity.
  intro a.
  refine (transport_paths_FlFr
            (f := f)            
            (wp a) idpath @ _).
  apply moveR_Mp. refine (pushout_rec_beta_pp P _ _ _ @ _).
  cut (forall q : f pt = f (wsummand a (point (X a))), q = ((q^ @ 1)^ @ 1)).
  intro H. apply H. intros []. reflexivity.
Defined.

Definition path_wedge_arrow {A : Type} (X : A -> pType) (Y : Type) (f g : Wedge X -> Y)
           (eq_pt : f pt = g pt)
           (eq_summand : forall (a : A) (x : X a), f (wsummand a x) = g (wsummand a x))
           (eq_wp : forall a : A,
              eq_pt^ @ (ap f (wp a)) @ (eq_summand a (point (X a))) = ap g (wp a))
  : f = g.
Proof.
  apply path_forall. srapply @wedge_ind.
  - exact eq_pt.
  - exact eq_summand.
  - intro a.
    refine (transport_paths_FlFr (wp a) eq_pt @ _).
    refine (concat_pp_p _ _ _ @ _). apply moveR_Vp. apply moveR_Mp. apply inverse.
    refine (concat_p_pp _ _ _ @ _). exact (eq_wp a).
Defined.

Definition wedge_to_prod_summand {A : Finite_Types} (X : A -> pType)
           : forall (a : A), (X a) -> forall a : A, X a.
Proof.
  intros a x.
  intro a'.
  destruct (decidablepaths_finite A a a').
  + destruct p. exact x.
  + exact (point (X a')).
Defined.

Definition wedge_to_prod_wp  {A : Finite_Types} (X : A -> pType) (a : A) :
  ((fun a' : A => point (X a')) = wedge_to_prod_summand X a (point (X a))).
Proof.
  apply path_forall. intro a'.
  unfold wedge_to_prod_summand.
  destruct (decidablepaths_finite A a a').
  + cbn. destruct p. reflexivity.
  + reflexivity.
Defined.
  
  
Definition wedge_to_prod {A : Finite_Types} (X : A -> pType)
  : Wedge X -> (forall a : A, X a).
Proof.
  srapply @wedge_rec.
  - intro a. exact (point (X a)).
  - apply wedge_to_prod_summand.
  - apply wedge_to_prod_wp.
Defined.

(* Wedge_to_prod is natural *)
Definition natural_wedge_to_prod_summand {A : Finite_Types} (X : A -> pType) (B : Finite_Types) (f : embedding B A) :
    forall (b : B) (x : X (f b)),
      wedge_to_prod_summand (A := A) X (f b) x = functor_prod_fin f (wedge_to_prod_summand (X o f) b x).
Proof.
  intros b x. unfold wedge_to_prod_summand. unfold functor_prod_fin.
  destruct f as [f emb]. simpl in *. apply path_forall. intro a.
  destruct (detachable_image_finite f a) as [[b' p']|];
  destruct (decidablepaths_finite A (f b) a) as [p|];
  try destruct (decidablepaths_finite B b b') as [q|].
  - destruct q.
  cut (p = p').
  { intros []. reflexivity. }
  apply (isset_Finite A). exact _.
  - destruct p'. apply Empty_rec. apply n. apply (isinj_embedding f). exact _. exact p.
  - unfold transport. destruct p'. destruct q. apply Empty_rec. apply n. reflexivity.
  - destruct p'. unfold transport. reflexivity.
  - destruct p. apply Empty_rec. apply n.
    exact (b; idpath).
  - reflexivity.
Defined.

Definition natural_wedge_to_prod {A : Finite_Types} (X : A -> pType) (B : Finite_Types) (f : embedding B A)
  : wedge_to_prod X o (functor_wedge X B f) = (functor_prod_fin f) o (wedge_to_prod (fun b : B => X (f b))).
Proof.
  srapply @path_wedge_arrow.
  - apply path_forall. intro a. simpl.
    destruct f as [f emb].
    unfold functor_prod_fin.
    destruct
      (detachable_image_finite f a) as [[b p]|]. destruct p. reflexivity. reflexivity.
  - exact (natural_wedge_to_prod_summand X B f).
  - intro b. destruct f as [f emb]. simpl.
    
    
    
  
  apply path_arrow.
  (* refine ((wedge_rec_eta_homot ((wedge_to_prod X) o (functor_wedge X B f)) x) *)
  (*           @ _ @ *)
  (*         (wedge_rec_eta_homot ((functor_prod_fin f) o (wedge_to_prod (fun b : B => X (f b)))) x)^). *)
  (* simpl. *)
  
  
  (* -  *)
  
  srapply @wedge_ind.
  - apply path_forall. intro a. simpl.
    destruct f as [f emb].
    unfold functor_prod_fin.
    destruct
      (detachable_image_finite f a) as [[b p]|]. destruct p. reflexivity. reflexivity.
  - exact (natural_wedge_to_prod_summand X B f).
  - simpl. intro b.
    refine (transport_paths_FlFr (wp b) _ @ _). destruct f as [f emb]. simpl.
    cut (ap (fun x : Wedge (fun b : B => X (f b)) => wedge_to_prod X (functor_wedge X B f x)) (wp a)
         = wedge_to_prod_wp X 
    
    
    
    
    
    destruct (detachable_image_finite f a) as [[b' p']|].
    destruct (decidablepaths_finite A (f b) a) as [p|].
    destruct (decidablepaths_finite B b b') as [q|].
    

    
    destruct p.
    

    destruct p. destruct q.

    

    
    change (functor_wedge X B f (wsummand b x)) with (wsummand 
    apply path_forall. intro a. 
    (* destruct (decidablepaths_finite A (f b) a) as [[]|]. *) simpl in x.


    rewrite transport_

    reflexivity. reflexivity.
    destruct (decidablepaths_finite B b a').
    + 
    

    unfold wedge_to_prod. unfold functor_prod_fin. simpl.

  intro x.
  refine ((pushout_rec_eta_homot ((wedge_to_prod X) o (functor_wedge X B f)) x)
            @ _ @
          (pushout_rec_eta_homot ((functor_prod_fin f) o (wedge_to_prod (fun b : B => X (f b)))) x)^).
  simpl.
  revert x.
  srapply @wedge_ind.
  - simpl. apply path_forall. intro a. unfold functor_prod_fin.

    destruct
      (detachable_image_finite f a) as [[b p]|]. destruct p. reflexivity. reflexivity.
  - intros a x. simpl. unfold functor_prod_fin.
    
    

  
  
  
  apply (srapply @path_pushout_rec'.).
  
  cbn.
  
  
  


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

       
  