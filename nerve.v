Require Import HoTT.
Require Import UnivalenceAxiom.
Load finite.


Require Import Functor Category.
(*These notations are defined elsewhere, but I do not know how to import it.*)
Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Notation "F '_0' x" := (Functor.Core.object_of F x) (at level 10, no associativity, only parsing) : object_scope.
Notation "F '_1' m" := (Functor.Core.morphism_of F m) (at level 10, no associativity) : morphism_scope.
Open Scope category_scope.
Open Scope morphism_scope.

(* c_j := projection_iterated_prod (include_1 j) *)
(* c_j+1 := projection_iterated_prod (fin_succ j) *)

(* Morphisms from the j'th projection to the successor *)
Definition morphism_j_Sj {n : nat} {C : PreCategory} (j : Fin n) (c : C*^(n.+1)) :=
  (projection_iterated_prod (include_1 j) c) --> (projection_iterated_prod (fin_succ j) c).

Variable C : PreCategory. Variable n : nat. Variable c : C*^(n.+1). Variable j : Fin n.
Check projection_iterated_prod (include_1 j) c . 

Definition Nerve (n : nat) (C : PreCategory) :=
  {c : C*^(n.+1) & (forall j : Fin n, morphism_j_Sj j c)}%type.

Definition nerve_face {n : nat} {C: PreCategory} (i : [n.+1]) : Nerve n.+1 C -> Nerve n C.
Proof.
  unfold Nerve.
  apply (functor_sigma (face_iterated_prod i)).
  induction n. contradiction. rename n0 into n. rename IHn into d.
  intro c. intro f. intro k. revert k. revert f.
  destruct c as [c0 [c1 [c2 c]]].
  revert i.
  srapply @fin_ind; simpl.
  (* i = 0. Forget the first component *)
  - intro f. change (Fin n + Unit)%type with [n]. intro k.
    exact (f (fin_succ k)).
  (* i+1. Compose (f i and f i+1)*)
  - change (Fin n + Unit)%type with [n].
    change ([n] + Unit)%type with [n.+1].
    intro i.  intro f.
    revert i. srapply @fin_ind; simpl.
    (* i = 1. Compose f 0 and f 1 *)
    + srapply @fin_ind; simpl.
      (* k=0 *)
      * exact (f (fin_succ fin_zero) o f fin_zero). (* f_1 o f_0 *)
      (* k+1 *)
      * intro k. exact (f (fin_succ (fin_succ k))).
    (* i + 2 *)
    + change (Fin n + Unit)%type with [n].
      intro i.
      srapply @fin_ind; simpl.
      (* k = 0 *)
      * exact (f fin_zero).
      (* k+1 *)
      * intro k.
        (* d_(i+2) f (k+1) = d_(i+1) (fun j => f (j+1)) k *)
        exact (d (fin_succ i) (c1, (c2, c)) (fun j => f (fin_succ j)) k).
Defined.

(* Prove a simplicial identity to check if this works *)
Open Scope function_scope.
Definition a_simplicial_identity {n : nat} {C : PreCategory} (i : [n]) (c : Nerve n.+2 C)  :
  (nerve_face (fin_succ i) o nerve_face (include_1 (include_1 i))) c =
  (nerve_face (include_1 i) o nerve_face (include_1 (include_1 i))) c.
Proof.
  destruct c as [c f]. destruct c as [c0 [c1 [c2 c]]].
  revert i. srapply @fin_ind. simpl. unfold const.
  srapply @path_sigma. simpl. unfold face_iterated_prod. simpl.
  unfold nerve_face.
  
  
  simpl.