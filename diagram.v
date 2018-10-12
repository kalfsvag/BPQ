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
  - (* set (Dk := IHk.1). *)
    (* set (pDK := IHk.2.1). *)
    (* set (prevk := IHk.2.2.1). *)
    (* set (Indk := IHk.2.2.2.1). *)
    (* set (lastk := IHk.2.2.2.2).     *)
    destruct IHk as
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
Definition prev k : Diagram k -> pDiagram k
  := (Diagram' k).2.2.1.
Definition last k : forall (X : Diagram k), Ind k (prev k X) -> Type
  := (Diagram' k).2.2.2.2.

(* Perhaps not needed, but written anyway *)
Definition pred_is_pred (k : nat) :
  pDiagram (k.+1) = Diagram k := idpath.

Definition succ_diagram (k : nat) :
  Diagram (k.+1) = {X : Diagram k & Ind (k.+1) X -> Type} := idpath.

Definition issig_diagram (k : nat) :
  Diagram k = {X : pDiagram k & Ind k X -> Type}.
Proof.
  destruct k.
  - unfold Diagram. unfold pDiagram. simpl. srapply @path_universe_uncurried.
    srapply @equiv_adjointify.
    + intro X.
      exists tt. exact (const X).
    + intro X. exact (X.2 tt).
    + intro X. destruct X as [[] X]. unfold Ind in X. simpl in X. unfold const in X.
      srapply @path_sigma. reflexivity. simpl. apply path_arrow.  intros []. reflexivity.
    + intro X. reflexivity.
  - change (pDiagram k.+1) with (Diagram k). reflexivity.
Defined.

Definition succ_ind (k : nat) (X : Diagram k):
  Ind k.+1 X = {u : Ind k (prev k X) & last k X u} := idpath.

Check (Diagram 2).
Lemma test1 : Diagram 1 <~> {X0 : Type & X0 -> Type}.
  change (Diagram 1) with {X : Diagram 0 & Ind 1 X -> Type}.
  change (Ind 1) with (fun X => {u : Ind 0 (prev 0 X) & last 0 X u}).
  change (Diagram 0) with Type.
  change (Ind 0) with (fun X : Unit => Unit). simpl. 
  change (last 0) with (fun (X : Type) (t : Unit) => X). simpl.
  apply equiv_functor_sigma_id. 
  intro X.
  apply equiv_precompose'.
  srapply @equiv_adjointify.
  - intro x. exact (tt;x).
  - intros [t x]. exact x.
  - intros [[] x]. reflexivity.
  - intro x. reflexivity.
Defined.

(* The k'th type *)
Definition last_type_of (k : nat) (X : Diagram k) :=
  {u : Ind k (prev k X) & last k X u}.

Definition fst_type_of (k : nat) (X : Diagram k) : Type.
Proof.
  induction k.
  - exact X.
  - exact (IHk (prev k.+1 X)).
Defined.

Definition last_type_of_0 (X : Diagram 0) :
  last_type_of 0 X <~> X.
Proof.
  unfold last_type_of. change (prev 0 X) with tt. change (Ind 0 tt) with Unit.
  change (last 0 X) with (fun t : Unit => X). simpl.
    srapply @equiv_adjointify.
  - intros [t x]. exact x.
  - intro x. exact (tt;x).
  - intro x. reflexivity.
  - intros [[] x]. reflexivity.
Defined.

(* sanity check *)
Definition last_type_of_1 (X : Diagram 1)  : 
  last_type_of 1 X <~> {x0 : prev 1 X & last 1 X (tt; x0)}.
Proof.
  change (last_type_of 1 X) with {u : Ind 1 (prev 1 X) & last 1 X u}.
  change (Ind 1 (prev 1 X)) with {u : Ind 0 (prev 0 (prev 1 X)) & last 0 (prev 1 X) u}.
  change (Ind 0 (prev 0 (prev 1 X))) with Unit.
  change (last 0 (prev 1 X)) with (fun t : Unit => prev 1 X). simpl.
  change (Diagram 1) with {X : Type & {_ : Unit & X} -> Type} in X.
  change (prev 1 X) with X.1.
  change (last 1 X) with X.2.
  destruct X as [X0 X1]. simpl.
  srapply @equiv_adjointify.
  - intros [[[] x0] x1]. exact (x0; x1).
  - intros [x0 x1]. exact ((tt;x0);x1).
  - intros [x0 x1]. reflexivity.
  - intros [[[] x0] x1]. reflexivity.
Defined.

Definition last_type_of_to_pred (k : nat) (X : Diagram k.+1) :
  last_type_of k.+1 X -> last_type_of k (prev k.+1 X) := pr1.  

Fixpoint type_of (k : nat) (X : Diagram k) (i : Fin k.+1) : Type .
Proof.
  destruct k. exact X.
  destruct i as [i | t].
  - exact (type_of k (prev k.+1 X) i).
  - exact (last_type_of k.+1 X).
Defined.


Inductive chain (S : Type) : forall (T : Type), Type :=
|nil : chain S S
|cons : forall (T1 T2 : Type), (T2 -> T1) -> chain S T1 -> chain S T2.

Definition len {S T : Type} : chain S T -> nat.
Proof.
  intro c. induction c.
  - exact 0.
  - exact (IHc.+1).
Defined.

Definition dia_to_chain (k : nat) (X : Diagram k) : chain (fst_type_of k X) (last_type_of k X).
Proof.
  induction k. simpl. apply (cons _ _ _ (last_type_of_0 X)). apply nil.
  simpl.
  apply (cons _ _ _ (last_type_of_to_pred k X)).
  apply IHk.
Defined.

Definition chain_to_tia {S T : Type} (c : chain S T) :
  Diagram (len c).
Proof.
  induction c. exact S.
  simpl.
  change (Diagram (len c).+1) with {X : Diagram (len c) & Ind ((len c).+1) X -> Type}.
  exists IHc.
  change (Ind ((len c).+1)) with (fun X => {u : Ind (len c) (prev (len c) X) & last (len c) X u}). cbn.
  

    in X.
  
  
  change (Diagram (len c).+1) with 
           
  
  intro X. srapply @exist.
  apply (pair (fst (IHk (prev k.+1 X)).1)).
  
  
(*   destruct k. *)
(*   destruct i as [i | []]. *)
(*   - destruct i. *)
(*   - exact X. *)
(*   -  *)
(*   destruct k. *)
(*   - destruct i. *)
(*   - exact (type_of k (prev k.+1 X) i). *)
(*   - exact (last_type_of k X). *)
(* Defined. *)

Definition succ_Fin {k : nat}: Fin k -> Fin k.+1.
Proof.
  induction k.
  - exact Empty_rec.
  - exact (functor_sum IHk idmap).
Defined.


Definition arrow_type_of (k : nat) (X : Diagram k) (i : Fin k) :
  type_of k X (succ_Fin i) -> type_of k X (inl i).
Proof.
  induction k. exact idmap.
  destruct i as [i | tt].
  - simpl.
    destruct k. exact idmap.
    simpl. simpl in IHk.
    destruct i as [i | tt]. simpl. apply IHk.

    apply IHk.
  - simpl. 

    destruct k. unfold type_of. unfold last_type_of. 
  
  induction k.
  - destruct i.
  - change (Diagram k.+1) with {X : Diagram k & Ind (k.+1) X -> Type} in X.
    destruct i as [i | []].
    simpl. apply IHk.
    
(*     simpl. unfold type_of. simpl. *)
    
    
(*     destruct X as [X Xk]. unfold prev. simpl. *)
    
(*     simpl.  *)
(*     unfold last_type_of. intro. apply (IHk (prev k.+1 X). *)
(*     destruct k. simpl. *)
(*     cha *)


  

(* This is a presheaf version of a diagram of a directed category •←•←…←• *)
(* This type should be equivalent to a "normal" type of diagrams of this category*) 


(* Inductive iDiagram (S : Type) : forall (T : Type), Type  := *)
(*   |nil : iDiagram S S *)
(*   |cons : forall T1 T2 : Type, *)
(*       (T2 -> T1) -> iDiagram S T1 -> iDiagram S T2. *)

(* Definition len {S T : Type} : iDiagram S T-> nat. *)
(* Proof. *)
(*   intro d. induction d. *)
(*   - exact 0. *)
(*   - exact (IHd.+1). *)
(* Defined. *)

Definition nDiagram (k : nat) : Type :=
  {X : Fin k.+1 -> Type & forall i : Fin k, X (succ_Fin i) -> X (inl i)}.

(* Definition comp_dia : *)
(*   {k : nat & nDiagram k} <~> {ST : Type*Type & iDiagram (fst ST) (snd ST)}. *)
(* Proof. *)
(*   srapply @equiv_adjointify. *)
(*   - intros [k nd]. induction k. *)
(*     exists (nd.1 (inr tt), nd.1 (inr tt)). simpl. apply nil. *)
(*     destruct nd as [X f]. *)
(*     set (IHk_restr := IHk (X o inl; f o inl)). *)
(*     destruct IHk_restr as [[S T] id]. *)
(*     exists (S, X (inr tt)). simpl. *)
(*     apply (cons S T _). *)
    
(*     exists (IHk *)
(*     Check (IHk (X o inl; f o inl)). *)
    
Definition ndiag_succ_to_sig (k : nat) :
  nDiagram (k.+1) -> {X : nDiagram k & {X_Sk : Type & X_Sk -> X.1 (inr tt)}}.
Proof.
  intros [X f].
  srapply @exist.
  exists (fun i => X (inl i)).
  exact (fun i => f (inl i)).
  simpl.
  exists (X (inr tt)). exact (f (inr tt)).
Defined.

Definition ndiag_sig_to_succ (k : nat) :
  {X : nDiagram k & {X_Sk : Type & X_Sk -> X.1 (inr tt)}} -> nDiagram (k.+1).
Proof.
  intros [[X f] [X_Sk f_Sk]].
  srapply @exist.
  + intros [i | t]. exact (X i). exact X_Sk.
  + simpl. intros [i | []]. simpl. exact (f i). simpl in *. exact f_Sk.
Defined.


Definition nDiagram_succ (k : nat) :
  nDiagram (k.+1) <~> {X : nDiagram k & {X_Sk : Type & X_Sk -> X.1 (inr tt)}}.
Proof.
  srapply @equiv_adjointify.
  - exact (ndiag_succ_to_sig k).
  - exact (ndiag_sig_to_succ k).
  - intros [[X f] [X_Sk f_Sk]]. simpl in *. reflexivity.
  - intros [X f].               (* perhaps just define the arrows for now. . . *)
    srapply @path_sigma. simpl. apply path_arrow.
    intros [i | []]; reflexivity. simpl.    apply path_forall. intro i.
    Abort.
    

Fixpoint dia_to_ndia (k : nat) :
  (Diagram k) -> nDiagram k.
Proof.
  destruct k.
  - intro X. exists (const X). intros [].
  - intro X.
    srapply @exist. intros [i | tt].
    apply ((dia_to_ndia k (prev k.+1 X)).1 i).
    exact (last_type_of k.+1 X).
    simpl. intros [i | tt].
    simpl. apply ((dia_to_ndia k (prev k.+1 X)).2). simpl.
    
    
  
  intro X. srapply @exist.
  - intro i.
    induction k.
    + exact X.
    + destruct i as [i | ].
      * apply (IHk (prev (k.+1) X) i).
      * exact (last_type_of k.+1 X).
  - simpl. intro i.
    induction k. exact idmap.
    simpl in *.
    destruct i as [i | []].
    + simpl. apply IHk.
    + simpl. unfold last_type_of. 
    

        change (Diagram k.+1) with {X : Diagram k & Ind (k.+1) X -> Type} in X.
        destruct X as [X X_Sk].
        exact {x : (IHk X (inr tt)) & {u : Ind k.+1 X & X_Sk u}}.
  - simpl. induction k. simpl. intros [].
    intros [i | []]; simpl.
    apply (IHk (prev X) i).
    

        
        change (Ind (k.+1)) with (fun X => {u : Ind k (prev k X) & last k X u}) in X. cbn in X.

        exact ({x : (prev (k.+1) X) & {u : Ind k.+1 (prev (k.+1) X) & last (k.+1) X u}}).

        apply (Ind (k.+1) (prev k.+1 X)).
  - simpl. intro i.
    induction k.
    + exact idmap.
    + simpl in *.
      destruct i as [i | []]. simpl in *. apply IHk.
      simpl in *.
      change (Ind (k.+1) (prev k.+1 X)) with ({u : Ind k (prev k (prev k.+1 X)) & last k (prev k.+1 X) u}).
      

    
  induction k.
  - simpl. intro X.
    exists (const X). intros [].
  - intro X. apply (ndiag_sig_to_succ k).
    change (Diagram k.+1) with {X : Diagram k & Ind (k.+1) X -> Type} in X.
    change (Ind (k.+1)) with (fun X => {u : Ind k (prev k X) & last k X u}) in X. cbn in X.
    exists (IHk X.1).
    
    
    intros [Xk X_Sk].
    srapply @exist.
    + intros [i | t]. exact ((IHk Xk).1 i).
      exact (y : (IHk Xk).1 (inr tt) & 
      (* some sigma type *)
      exact (sigT X_Sk).
    + simpl.
      intros [i | []]; simpl.
      * apply (IHk Xk).2.
      * 
      
      
      
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
    

  