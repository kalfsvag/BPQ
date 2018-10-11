Require Import HoTT.
(* Require Import Utf8. *)
Require Import finite_lemmas.

Definition Diagram' (k : nat) :
  {D : Type & {pD : Type & {prev : D -> pD & {Ind : pD -> Type &
                                                          forall (X : D), Ind (prev X) -> Type}}}}.
Proof.
  induction k.
  - exists Type.
    exists Unit.
    exists (const tt).
    exists (const Unit).
    intro X. exact (const X).
  - destruct IHk as
        [Dk [pDk [prevk [Indk lastk]]]].
    exists ({X : Dk & {u : Indk (prevk X) & lastk X u} -> Type}).
    (* exists ({X : Dk & forall (u : Indk (prevk X)), (lastk X u) -> Type}). *)
    exists Dk.
    exists pr1.
    exists (fun X : Dk => {u : Indk (prevk X) & lastk X u}).
    intros [Xk XSk]. intros [u].
    cbn. intro X. apply XSk. exact (u; X).
    (* apply XSk. *)
Defined.

Definition Diagram k := (Diagram' k).1.
Definition pDiagram k : Type  := (Diagram' k).2.1.
Definition Ind k : pDiagram k -> Type
  := (Diagram' k).2.2.2.1.

(* Perhaps not needed, but written anyway *)
Definition pred_is_pred (k : nat) :
  pDiagram (k.+1) = Diagram k := idpath.

Definition succ_diagram (k : nat) :
  Diagram (k.+1) = {X : Diagram k & Ind (k.+1) X -> Type} := idpath.

(* This is a presheaf version of a diagram of a directed category •←•←…←• *)
(* This type should be equivalent to a "normal" type of diagrams of this *) 

Definition succ_Fin {k : nat}: Fin k -> Fin k.+1.
Proof.
  induction k.
  - exact Empty_rec.
  - exact (functor_sum IHk idmap).
Defined.

Definition nDiagram (k : nat) : Type :=
  {X : Fin k.+1 -> Type & forall i : Fin k, X (succ_Fin i) -> X (inl i)}.

Definition nDiagram_succ (k : nat) :
  nDiagram (k.+1) <~> {X : nDiagram k & {X_Sk : Type & X_Sk -> X.1 (inr tt)}}.
Proof.
  srapply @equiv_adjointify.
  - intros [X f].
    srapply @exist.
    exists (fun i => X (inl i)).
    exact (fun i => f (inl i)).
    simpl.
    exists (X (inr tt)). exact (f (inr tt)).
  - intros [[X f] [X_Sk f_Sk]].
    srapply @exist.
    + intros [i | t]. exact (X i). exact X_Sk.
    + simpl. intros [i | []]. simpl. exact (f i). simpl in *. exact f_Sk.
  - intros [[X f] [X_Sk f_Sk]]. simpl in *. reflexivity.
  - intros [X f].               (* perhaps just define the arrows for now. . . *)
    srapply @path_sigma. simpl. apply path_arrow.
    intros [i | []]; reflexivity. simpl.
    apply path_forall. intros [i | []].
    refine (transport_forall _ _ _ @ _). simpl.
    

    
    simpl.
    

    

Definition doesthiswork (k : nat) :
  (Diagram k) -> nDiagram k.
Proof.
  induction k.
  - simpl. intro X.
    exists (const X). intros [].
  - change (Diagram k.+1) with {X : Diagram k & Ind (k.+1) X -> Type}.
    intros [X x].
    srapply @exist.
    + intros [i | t]. exact ((IHk X).1 i).
      (* some sigma type *)
      
      Check (IHk X).2.

    
    unfold Diagram in *.
    destruct (Diagram' k) as
        [D_k [pD_k [prev_k [Ind_k last_k]]]].
    cbn in IHk.

    intros [X x].
    srapply @exist.
    + 
    
    unfold nDiagram.

    
    
    simpl.
    
    destruct (Diagram k.+1) as
        [D_Sk [pD_Sk [prev_Sk [Ind_Sk last_Sk]]]]. cbn. simpl in *.
    intro X.
    unfold nDiagram.
    

    
    simpl.
    

  