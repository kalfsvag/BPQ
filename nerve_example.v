Require Import HoTT.
Load finite.
Require Import Functor Category.
(*This notation is defined elsewhere, but I do not know how to import it.*)
Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.

(* Open Scope category_scope.   *)
Open Scope morphism_scope.


Inductive pFin : forall (n : nat), Type :=
  | fin_zero {n : nat} : pFin n
  | fin_succ {n : nat} : pFin n -> pFin n.+1.

Definition fin_include {n : nat} : Fin n -> Fin n.+1.
Proof.
  intro i. induction i.
  exact fin_zero.


(* Trying to do an inductive definition of the nerve *)
Inductive composable_arrows (C : PreCategory) : forall (n : nat) (c0 : C), Type :=
  | nil : forall c0 : C, composable_arrows C O c0
  | cons : forall (n : nat) (c0 c1 : C) (f0 : c1 --> c0),
      composable_arrows C n c1 -> composable_arrows C n.+1 c0.

Arguments nil {C} c0.
Arguments cons {C} {n} {c0 c1} f0 _.

(* Overload the list notation. . . *)
Notation "f0 :: s" := (cons f0 s) (at level 60, right associativity).

(* Definition composable_arrows_pred (C : PreCategory) (n : nat) (c0 : C) : Type. *)
(* Proof. *)
(*   destruct n. *)
(*   - exact Unit. *)
(*   - exact (composable_arrows C n c0). *)
(* Defined. *)

(* (* Augment the definition of ca by saying that ca_-1 = Unit *) *)
(* Definition ca_face_Si {C : PreCategory} {n : nat} {c0 : C} (i : Fin n) : *)
(*   composable_arrows C n c0 -> composable_arrows_pred C n c0. *)
(* Proof. *)
(*   intro s. induction s. *)
(*   - exact tt. *)
(*   - destruct s. *)
(*     + apply nil. *)
(*     + revert i. srapply @fin_rec. *)
(*       (* i=1 *) exact ((f0 o f1) :: s). *)
(*       intro i. unfold composable_arrows_pred in IHs. *)
(*       apply (cons f0). exact (IHs i). *)
(* Defined. *)

(* All composable strings of length n: *)
Definition Nerve (C : PreCategory) (n : nat) :=
  {c0 : C & composable_arrows C n c0}.

Definition ca_to_nerve {C : PreCategory} {n : nat} {c0 : C} : composable_arrows C n c0 -> Nerve C n.
Proof.
  intro s. exact (_; s).
Defined.



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

Definition nerve_face {C : PreCategory} {n : nat} (i : [n]) :
  Nerve C n -> Nerve_pred C n.
Proof.
  intros [c s]. destruct s.  (* s is nil *) {exact tt. } simpl.
  revert i. srapply @fin_rec.
  (* i=0 *) {exact (c1; s). }
  (* i+1 *) intro i.
  exists c0. revert c0 f0. induction s; intros.
  (* The naming of c's and f's get a bit jumbled here. . . *)
  (* s is f0 *) {exact (nil c1). }
  revert i. srapply @fin_rec.
  (* i=1 *) {exact (f1 o f0 :: s). }
  (* i+2 *)
  (* d_(i+2) (c0 <- c1 <- . . .) = c0 <- d_(i+1) (c1 <- ...) *)
  intro i.
  exact (f1 :: IHs i c0 f0).
Defined.

(* Definition nerve_face {C : PreCategory} {n : nat} (i : [n]) : *)
(*   Nerve C n -> Nerve_pred C n. *)
(* Proof. *)
(*   intro s.  *)
(*   revert i. srapply @fin_rec. *)
(*   - apply (nerve_face_0 s). *)
(*   - destruct n. contradiction. *)
(*     intro i. destruct s as [c0 s]. exists c0. *)
(*     exact (ca_face_Si i s). *)
(* Defined. *)

Arguments nerve_face {C} {n} (i) _ : simpl never.

(* Formulate a simplicial identity that is trivially true when n is 0 and 1 *)
Definition augmented_simp_id {C : PreCategory} {n : nat} (i : Fin n) (s : Nerve C n) : Type.
Proof.
  destruct s as [c0 s].
  destruct s.
  (* s is nil *) exact Unit.
  destruct s.
  (* s is c0 -> c1 *) exact Unit.
  (* s is c0 -> c1 -> c2 -> ... *)
  exact (nerve_face i (nerve_face (fin_succ i) (c0; cons f0 (cons f1 s))) =
         nerve_face i (nerve_face (include_1 i) (c0; cons f0 (cons f1 s)))).
Defined.

Definition a_simplicial_identity {C : PreCategory} {n : nat} (i : [n])
           (c0 c1 : C) (f0 : c1 --> c0) (s : composable_arrows C n c1) :
  (nerve_face i (nerve_face (fin_succ i) (c0; f0 :: s)) =
   nerve_face i (nerve_face (include_1 i) (c0; f0 :: s))).
Proof.
  induction s. 
  induction n. simpl. 
  revert i. srapply @fin_ind. { destruct s. reflexivity. reflexivity. }
  intro i. simpl.
  
  destruct s.
  (* s is nil *) {revert i. srapply @fin_ind; try contradiction. reflexivity. }
  
  revert i. srapply @fin_ind.
  (* i=0 *) { reflexivity. } intro i. simpl.
  destruct s. (* s is f0 *) { simpl. destruct i. contradiction. simpl. reflexivity. }
  revert i.
  (* i=1 *) srapply @fin_ind. {simpl. unfold nerve_face. simpl. rewrite associativity. reflexivity. }
  (* i+2 *) simpl. intro i.
  apply (ap (fun s => (c0; s))). revert c0 c1 f0 f1. induction s. simpl. contradiction.
  simpl. intros. simpl. simpl in IHs. rewrite IHs.
  
  unfold nerve_face. simpl. 

                               simpl. unfold const. unfold nerve_face. simpl. unfold const.


  destruct s. { intros [|]. contradiction. unfold const. reflexivity. }
  intro i. simpl.
                        

  apply 
  destruct s. { intros [|]. contradiction. reflexivity. }
  srapply @fin_ind.
  (* i=1 *) { simpl. unfold const. unfold nerve_face. simpl. rewrite associativity. reflexivity. }
  (* i+1 *) intro i.
  (* The ordering on the c's get completely jumbled. . . *)
  rename c0 into ctemp. rename c2 into c0. rename c1 into c2. rename ctemp into c1. move c0 after c1. move c3 after f0.
  rename f0 into ftemp. rename f1 into f0. rename ftemp into f1. move f0 after f1. move f2 after n.
  simpl.
  
  transitivity
    (nerve_face (fin_succ (fin_succ i)) (nerve_face (fin_succ (fin_succ (fin_succ i))) (c0; f0 :: f1 :: f2 :: s)))
      

  
  unfold include_1. simpl.
  simpl.
  simpl in IHs. rewrite IHs.
  
  exact (IHs (fin_succ i)
  simpl.
  
  simpl. unfold const.
  
  
  simpl. simpl in IHs.
  
  

  destruct s. simpl.
  
  simpl.
  
  destruct s. reflexivity. simpl.
  
  destruct n. contradiction.
  destruct s. contradiction.
  simpl.
  
  
  simpl.
  - simpl. unfold const. simpl. unfold nerve_face_0. simpl.








Fixpoint ca (C : PreCategory) (c0 : C) (n : nat) :=
  match n with
  | O => Unit
  | S n => {c1 : C & {f0 : (c0 --> c1) & ca C c1 n}}
  end.

Definition Nerve (C : PreCategory) (n : nat) :=
  {c0 : C & ca C c0 n}.

(* d_0 just forgets the first map. *)
Definition nerve_face_0 {C : PreCategory} {n :nat}: Nerve C n.+1 -> Nerve C n.
Proof. unfold Nerve. simpl.
  intros [c0 [c1 [f s]]]. exact (c1; s).
Defined.

(* (* d_1 has two cases*) *)
(* (* n=0: project to last object *) *)
(* (* n>0: compose together first two morphisms *) *)
(* Definition ca_face_1 {C : PreCategory} {c0 : C} {n : nat}  : ca C c0 n.+1 -> ca C c0 n. *)
(* Proof. *)
(*   destruct n. *)
(*   (* n=0 *) *)
(*   - intros [c1 f]. exact tt. *)
(*   (* n>0 *) *)
(*   - intros [c1 [f0 [c2 [f1 s]]]]. *)
(*     exists c2. exists (f1 o f0). exact s. *)
(* Defined. *)

(* The face fixes the start object when i>0, so defines it first just on ca *)
(* d_(i+2)(c0 -> c1 -> ...) = (c0 -> (d_(i+1) (c1 -> c2 -> ...) *)
Definition ca_face_Si {C : PreCategory} {n : nat} (c0 : C) (i : [n]) : ca C c0 n.+1 -> ca C c0 n.
Proof.
  revert c0. induction n; intro c0.
  - intro. exact tt.
  - revert i. srapply @fin_rec.
    (* d_1 *)
    + intros [c1 [f0 [c2 [f1 s]]]].
      exists c2. exists (f1 o f0). exact s.
    (* d_(i+2)(c0 -> c1 -> ...) = (c0 -> (d_(i+1) (c1 -> c2 -> ...) *)
    + intro i. 
      intros [c1 [f0 s]].
      exists c1. exists f0.
      exact (IHn i c1 s).
Defined.
           
Definition nerve_face {C : PreCategory} {n : nat} (i : [n.+1]) :
  Nerve C n.+1 -> Nerve C n.
Proof.
  revert i. srapply @fin_rec.
  (* i=0 *) apply nerve_face_0.
  (* i+1 *) intro i.
  intros [c0 s]. exists c0.
  apply (ca_face_Si c0 i s).
Defined.

Arguments ca_face_Si {C} {n} c0 i _ : simpl never.
Arguments include_1 {n} _ : simpl never.

Ltac destruct_nerve s :=
  destruct s as [?c0 s];
  repeat destruct s as [?c0 [?f0 s]].

Definition a_simplicial_identity {C : PreCategory} {n : nat} (i : [n.+1]) (s : Nerve C n.+2)   :
  nerve_face i (nerve_face (fin_succ i) s) =
  nerve_face i (nerve_face (include_1 i) s).
Proof.
  destruct_nerve s. move c2 after f0. simpl.
  revert i. srapply @fin_ind.
  (* i=0 *)
  - reflexivity.
  (* i+1 *)
  - intro i.
    (* Now c0 is fixed *)
    apply (ap (fun x => (c0; x))).
    induction n. reflexivity.
    destruct s as [c3 [f2 s]]. move c3 after f0.
    revert i. srapply @fin_ind. simpl. unfold const. Admitted. 
    
  (*   + reflexivity. *)
  (*   srapply @fin_ind. *)
  (*   (* i=1 *) *)
  (*   + induction n. reflexivity. *)
  (*     simpl. simpl in IHn. rewrite IHn. *)
  (*     simpl. unfold const. unfold ca_face_Si. simpl. *)

  (*     destruct c as [c0 c]. *)
  (* repeat destruct c as [?c [?f c]]. simpl. *)
  (* destruct c as [c0 [c1 [f0 [c2 [f1  *)
  

  (* simpl. *)
  (* induction n. *)
  (* revert i. srapply @fin_ind. *)
  (* (* i=0 *) *)
  (* - simpl. unfold include_1. simpl. unfold const. destruct c as [c0 [c1 [f0 [c2 [f1 []]]]]]. unfold nerve_face. simpl. unfold const. unfold nerve_face_0. *)
  (*   reflexivity. *)
  (* (* i+1 *) *)
  (* - induction n. simpl. reflexivity.  simpl. *)
  (* - simpl. *)
  (*   destruct s as [c3 [f2 s]]. simpl. *)
  (*   destruct c as [c0 [c1 [f0 [c2 [f1 [c3 [f2 s]]]]]]]. *)
  (*   srapply @fin_ind. *)
  (*   (* i=1 *) *)
  (*   + simpl. unfold const. rewrite associativity. reflexivity. *)
  (*   + simpl. srapply @path_sigma. *)
  (*     destruct c as [c0 [c1 [f0 [c2 [f1 s]]]]]. unfold include_1. *)

  (*   change *)
  (*     ((fun i : [n.+1] => nerve_face i (nerve_face (fin_succ i) c) = nerve_face i (nerve_face (include_1 i) c)) fin_zero) with *)
  (*   (nerve_face fin_zero (nerve_face (fin_succ fin_zero) c) = nerve_face fin_zero (nerve_face fin_zero c)). *)
  (*   destruct c as [c0 [c1 [f0 [c2 [f1 s]]]]]. *)
  (*   reflexivity. *)












(*     destruct n. contradiction. *)
(*     srapply @fin_rec. *)
(*     (* i=1 : Compose the first two maps*) *)
(*     + unfold Nerve. simpl. *)
(*       intros [c0 [c1 [f0 [c2 [f1 s]]]]]. *)
(*       exists c0. exists c2. exact (f1 o f0, s). *)
(*     (* i+2 *) *)
(*     (* nerve_face (i+2) (c0 -> c1 -> ...) = (c0 -> (nerve_face (i+1) (c1 -> c2 -> ...) *) *)
(*     + intro i. *)
(*       intros [c0 [c1 [f s]]].  *)
(*       refine (c0 ; nerve_face C n (fin_succ i) (c1; s)). *)
      
  
       
       



(*     Sigma(d:C) Sigma(f: c --> d) (ca C n d) *)
(* end.  *)

(* Trying to do an inductive definition of the nerve *)
Inductive composable_arrows (C : PreCategory) : forall (n : nat) (c0 : C), Type :=
  | nil : forall c0 : C, composable_arrows C O c0
  | cons : forall (n : nat) (c0 c1 : C) (f0 : c0 --> c1),
      composable_arrows C n c1 -> composable_arrows C n.+1 c0.

Definition reduction_path_ca {C : PreCategory} {n : nat} {c0 : C} (x : composable_arrows C n c0) : Type.
  destruct n.
  - exact (x = nil C c0).
  - exact (exists (c1 : C) (f0 : c0 --> c1) (s : composable_arrows C n c1), x = cons C n c0 c1 f0 s).
Defined.

Definition reduce_ca {C : PreCategory} {n : nat} {c0 : C} (x : composable_arrows C n c0) : reduction_path_ca x.
Proof.
  induction x. reflexivity.
  - unfold reduction_path_ca.
    exists c1. exists f0. exists x. reflexivity.
Defined.

Definition ca_reduced (C : PreCategory) (n : nat) (c0 : C) : Type.
Proof.
  destruct n.
  (* ca 0 c0 <~> Unit  *)
  - exact Unit.
  (* ca n.+1 c0 <~> {c1 : C & {f0 : c0 --> c1 & ca n c1}} *)
  - exact {c1 : C & {f0 : c0 --> c1 & composable_arrows C n c1}}.
Defined.

(* Lemma ca_reduce {C : PreCategory} {n : nat} {c0 : C} : composable_arrows C n c0 <~> ca_reduced C n c0. *)
(* Proof. *)
(*   srapply @equiv_adjointify. *)
(*   - o s. destruct s. *)


