Require Import HoTT.
Require Import UnivalenceAxiom.
Load finite.


Require Import Functor Category.
(*This notation is defined elsewhere, but I do not know how to import it.*)
Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.

(* Open Scope category_scope.   *)
Open Scope morphism_scope.
    
(* Trying to do an inductive definition of the nerve *)
Inductive composable_arrows (C : PreCategory) : forall (n : nat) (c0 : C), Type :=
  | nil : forall c0 : C, composable_arrows C O c0
  | cons : forall (n : nat) (c0 c1 : C) (f0 : c1 --> c0),
      composable_arrows C n c1 -> composable_arrows C n.+1 c0.

Arguments nil {C} c0.
Arguments cons {C} {n} {c0 c1} f0 _.

(* Overload the list notation. . . *)
Notation "f0 :: s" := (cons f0 s) (at level 60, right associativity).

(* ca is a single point in degree 0, and a sigma type in degree n+1 *)
Definition sig_ca (C : PreCategory) (n : nat) (c0 : C) : Type.
Proof.
  destruct n. -exact Unit. -exact {c1 : C & (c1 --> c0) * composable_arrows C n c1}.
Defined.

Definition issig_ca' {C : PreCategory} {n : nat} {c0 : C} :
  composable_arrows C n c0 <~> sig_ca C n c0.
Proof.
  srapply @equiv_adjointify.
  - intro s. destruct s. exact tt. simpl.
    exact (c1; (f0, s)).
  - destruct n. intro t. exact (nil c0). simpl.
    intros [c1 [f0 s]]. exact (f0 :: s).
  - intro s. induction n. destruct s. reflexivity. reflexivity.
  - intro s. induction s. reflexivity. reflexivity.
Defined.
    
Definition issig_ca {C : PreCategory} {n : nat} {c0 : C} :
  composable_arrows C n.+1 c0 <~> {c1 : C & (c1 --> c0) * composable_arrows C n c1} := issig_ca'.    

(* Definition composable_arrows_pred (C : PreCategory) (n : nat) (c0 : C) : Type. *)
(* Proof. *)
(*   destruct n. *)
(*   - exact Unit. *)
(*   - exact (composable_arrows C n c0). *)
(* Defined. *)

(* The face maps when i>0 are defined on composable_arrows *)
Fixpoint ca_face_Si {C : PreCategory} {n : nat} {c0 : C} (i : pFin n) :
  composable_arrows C n.+1 c0 -> composable_arrows C n c0.
Proof.
  (* Do a trick since [destruct s] doesn't work here *)
  intro s'. destruct (issig_ca s') as [c1 [f0 s]]. clear s'.
  destruct i.
  (* i=1 *)
  - destruct s. exact (nil c0). exact (f0 o f1 :: s).
  (* i+2 *)
  - exact (f0 :: ca_face_Si C n c1 i s). (* d_i+2 (c0<-c1<-...) = c0 <- d_i+1 (c1<-...) *)
Defined.

(* All composable strings of length n: *)
Definition Nerve (C : PreCategory) (n : nat) :=
  {c0 : C & composable_arrows C n c0}.

(* Definition ca_to_nerve {C : PreCategory} {n : nat} {c0 : C} : composable_arrows C n c0 -> Nerve C n. *)
(* Proof. *)
(*   intro s. exact (_; s). *)
(* Defined. *)

(* Augment the definition of N by saying that N_(-1) = Unit *)
Definition Nerve_pred (C : PreCategory) (n : nat) : Type.
Proof.
  destruct n.
  - exact Unit.
  - exact (Nerve C n).
Defined.

(* (* Try to define the 0'th face (which just forgets the first morphism) *) *)
(* Definition nerve_face_0 {C : PreCategory} {n :nat}: *)
(*   Nerve C n -> Nerve_pred C n. *)
(* Proof. *)
(*     intros [c0 s]. destruct s. *)
(*     - exact tt. *)
(*     - simpl. exact (c1; s). *)
(* Defined. *)

Definition nerve_face {C : PreCategory} {n : nat} (i : pFin n) :
  Nerve C n -> Nerve_pred C n.
Proof.
  intros [c0 s]. destruct i.
  {destruct s. exact tt. exact (_;s). } (* i=0 *)
  exists c0. exact (ca_face_Si i s).    (* i>0 *)
Defined.

Open Scope function_scope.
Definition a_simplicial_identity {C : PreCategory} {n : nat} (i : pFin n)
           (c0 c1 : C) (f0 : c1 --> c0) (s : composable_arrows C n c1) :
  (nerve_face i (nerve_face (fin_succ i) (c0; f0 :: s)) =
   nerve_face i (nerve_face (fin_include i) (c0; f0 :: s))).
Proof.
  destruct i. { destruct s. reflexivity. reflexivity. } (* i=0 *)
  rewrite <- (eissect issig_ca s). destruct (issig_ca s) as [c2 [f1 s']]. simpl. clear s. rename s' into s.
  apply (ap (fun s => (c0; s))).
  revert c0 c1 c2 f0 f1 s. induction i; intros. 
  (* i=1 *) { simpl. destruct s. reflexivity.
              rewrite associativity. reflexivity. }
  (* i+2 *)
  simpl.
  rewrite <- (eissect issig_ca s). destruct (issig_ca s) as [c3 [f2 s']]. simpl. clear s. rename s' into s.
  apply (ap (cons f0)). apply IHi.
Qed.