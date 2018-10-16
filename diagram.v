Require Import HoTT.
(* Require Import Utf8. *)
Require Import finite_lemmas.

(* Move to equiv_lemmas *)
Definition hfiber_compose_equiv (X Y1 Y2 : Type) (e : Y1 <~> Y2) (f : X -> Y1) (y : Y1):
  hfiber f y <~> hfiber (e o f) (e y).
Proof.
  unfold hfiber.
  apply (equiv_functor_sigma' equiv_idmap). intro x. simpl.
  apply equiv_ap'.
Defined.
  
  

Context (X0 : Type).

Definition Diagram' (k : nat) :
  {D : Type & D -> Type}.
Proof.
  induction k.
  exists Unit. exact (fun _ => X0).
  destruct IHk as [D_k Ind_k].
  exists {X : D_k & Ind_k X -> Type}.
  intros [X x].
  exact {u : Ind_k X & x u}.
Defined.

Definition Diagram k := (Diagram' k).1.
Definition Ind k := (Diagram' k).2.

Lemma diagram_1 : Diagram 1 <~> (X0 -> Type).
  change (Diagram 1) with {X : Diagram 0 & Ind 0 X -> Type}.
  change (Diagram 0) with Unit.
  change (Ind 0) with (fun _ : Unit => X0). simpl.
  srapply @equiv_adjointify.
  - intros [[] f]. exact f.
  - intro f. exact (tt; f).
  - intro f. reflexivity.
  - intros [[] f]. reflexivity.
Defined.

(* The k'th type *)
Definition last_type_of {k : nat} (X : Diagram k) :=
  Ind k X.
  (* {u : Ind k (prev X) & last X u}. *)

Definition last_type_of_0 (X : Diagram 0) :
  last_type_of X = X0 := idpath.


(* sanity check *)
Definition last_type_of_1 (X : Diagram 1)  : 
  last_type_of X = {x0 : X0 & (diagram_1 X) x0}.
Proof.
  destruct X as [[] X1]. simpl in X1.
  unfold last_type_of. reflexivity.
Defined.

Definition succ_diagram (k : nat) :
  Diagram (k.+1) = {X : Diagram k & Ind k X -> Type} := idpath.
(* Definition succ_ind (k : nat) (X : Diagram k): *)
(*   Ind k.+1 X = {u : Ind k (prev X) & last X u} := idpath. *)




(* (* Try another definition *) *)
(* Definition Diagram' (k : nat) : *)
(*   {D : Type & {pD : Type & {prev : D -> pD & {Ind : D -> Type & *)
(*                                                          forall (X : D), Ind (X) -> Type}}}}. *)
(* Proof. *)
(*   induction k. *)
(*   - exists Type. *)
(*     exists Unit. *)
(*     exists (const tt). *)
(*     exists idmap. *)
(*     intro X.  *)

(* Definition Diagram' (k : nat) : *)
(*   {D : Type & {pD : Type & {prev : D -> pD & {Ind : pD -> Type & *)
(*                                                           forall (X : D), Ind (prev X) -> Type}}}}. *)
(* Proof. *)
(*   induction k. *)
(*   - exists Type. *)
(*     exists Unit. *)
(*     exists (const tt). *)
(*     exists (const Unit). *)
(*     intro X. exact (const X). *)
(*   - (* set (Dk := IHk.1). *) *)
(*     (* set (pDK := IHk.2.1). *) *)
(*     (* set (prevk := IHk.2.2.1). *) *)
(*     (* set (Indk := IHk.2.2.2.1). *) *)
(*     (* set (lastk := IHk.2.2.2.2).     *) *)
(*     destruct IHk as *)
(*         [Dk [pDk [prevk [Indk lastk]]]]. *)
(*     exists ({X : Dk & {u : Indk (prevk X) & lastk X u} -> Type}). *)
(*     (* exists ({X : Dk & forall (u : Indk (prevk X)), (lastk X u) -> Type}). *) *)
(*     exists Dk. *)
(*     exists pr1. *)
(*     exists (fun X : Dk => {u : Indk (prevk X) & lastk X u}). *)
(*     intros [Xk XSk]. intros [u]. *)
(*     cbn. intro X. apply XSk. exact (u; X). *)
(*     (* apply XSk. *) *)
(* Defined. *)

(* Definition Diagram k := (Diagram' k).1. *)
(* Definition pDiagram k : Type  := (Diagram' k).2.1. *)
(* Definition Ind k : pDiagram k -> Type *)
(*   := (Diagram' k).2.2.2.1. *)
(* Definition prev {k} : Diagram k -> pDiagram k *)
(*   := (Diagram' k).2.2.1. *)
(* Definition last {k} : forall (X : Diagram k), Ind k (prev X) -> Type *)
(*   := (Diagram' k).2.2.2.2. *)

(* (* Perhaps not needed, but written anyway *) *)
(* Definition pred_is_pred (k : nat) : *)
(*   pDiagram (k.+1) = Diagram k := idpath. *)

(* Definition succ_diagram (k : nat) : *)
(*   Diagram (k.+1) = {X : Diagram k & Ind (k.+1) X -> Type} := idpath. *)

(* Definition issig_diagram (k : nat) : *)
(*   Diagram k = {X : pDiagram k & Ind k X -> Type}. *)
(* Proof. *)
(*   destruct k. *)
(*   - unfold Diagram. unfold pDiagram. simpl. srapply @path_universe_uncurried. *)
(*     srapply @equiv_adjointify. *)
(*     + intro X. *)
(*       exists tt. exact (const X). *)
(*     + intro X. exact (X.2 tt). *)
(*     + intro X. destruct X as [[] X]. unfold Ind in X. simpl in X. unfold const in X. *)
(*       srapply @path_sigma. reflexivity. simpl. apply path_arrow.  intros []. reflexivity. *)
(*     + intro X. reflexivity. *)
(*   - change (pDiagram k.+1) with (Diagram k). reflexivity. *)
(* Defined. *)

(* Definition issig_diagram_forall : *)
(*   Diagram = fun k => {X : pDiagram k & Ind k X -> Type}. *)
(* Proof. *)
(*   apply path_forall. exact issig_diagram. *)
(* Defined. *)

(* Definition succ_ind (k : nat) (X : Diagram k): *)
(*   Ind k.+1 X = {u : Ind k (prev X) & last X u} := idpath. *)

(* Check (Diagram 2). *)
(* Lemma test1 : Diagram 1 <~> {X0 : Type & X0 -> Type}. *)
(*   destruct issig_diagram_forall^. unfold pDiagram. simpl. *)
(*   (* change (Diagram 1) with {X : Diagram 0 & Ind 1 X -> Type}. *) *)
(*   change (Ind 1) with (fun X => {u : Ind 0 (prev X) & last X u}). *)
(*   (* change (Diagram 0) with Type. *) *)
(*   change (Ind 0) with (fun X : Unit => Unit). simpl.  *)
(*   change (last) with (fun (X : Type) (t : Unit) => X). simpl. *)
(*   apply equiv_functor_sigma_id.  *)
(*   intro X. *)
(*   apply equiv_precompose'. *)
(*   srapply @equiv_adjointify. *)
(*   - intro x. exact (tt;x). *)
(*   - intros [t x]. exact x. *)
(*   - intros [[] x]. reflexivity. *)
(*   - intro x. reflexivity. *)
(* Defined. *)

(* (* The k'th type *) *)
(* Definition last_type_of {k : nat} (X : Diagram k) := *)
(*   Ind k.+1 X. *)
(*   (* {u : Ind k (prev X) & last X u}. *) *)

(* Definition fst_type_of {k : nat} (X : Diagram k) : Type. *)
(* Proof. *)
(*   induction k. *)
(*   - exact X. *)
(*   - exact (IHk (prev X)). *)
(* Defined. *)

(* Definition last_type_of_0 (X : Diagram 0) : *)
(*   last_type_of X <~> X. *)
(* Proof. *)
(*   unfold last_type_of. change (prev X) with tt. change (Ind 0 tt) with Unit. *)
(*   change (last X) with (fun t : Unit => X). simpl. *)
(*     srapply @equiv_adjointify. *)
(*   - intros [t x]. exact x. *)
(*   - intro x. exact (tt;x). *)
(*   - intro x. reflexivity. *)
(*   - intros [[] x]. reflexivity. *)
(* Defined. *)

(* Definition eq_last_type_of_0 (X : Diagram 0) := path_universe (last_type_of_0 X). *)

(* (* sanity check *) *)
(* Definition last_type_of_1 (X : Diagram 1)  :  *)
(*   last_type_of X <~> {x0 : prev X & last X (tt; x0)}. *)
(* Proof. *)
(*   change (last_type_of X) with {u : Ind 1 (prev X) & last X u}. *)
(*   change (Ind 1 (prev X)) with {u : Ind 0 (@prev 0 (@prev 1 X)) & @last 0 (@prev 1 X) u}. *)
(*   change (Ind 0 (@prev 0 (@prev 1 X))) with Unit. *)
(*   change (@last 0 (@prev 1 X)) with (fun t : Unit => @prev 1 X). simpl. *)
(*   change (Diagram 1) with {X : Type & {_ : Unit & X} -> Type} in X. *)
(*   change (@prev 1 X) with X.1. *)
(*   change (@last 1 X) with X.2. *)
(*   destruct X as [X0 X1]. simpl. *)
(*   srapply @equiv_adjointify. *)
(*   - intros [[[] x0] x1]. exact (x0; x1). *)
(*   - intros [x0 x1]. exact ((tt;x0);x1). *)
(*   - intros [x0 x1]. reflexivity. *)
(*   - intros [[[] x0] x1]. reflexivity. *)
(* Defined. *)

(* Definition last_type_of_to_pred {k : nat} (X : Diagram k.+1) : *)
(*   last_type_of X -> last_type_of (prev X) := pr1. *)

(* Fixpoint type_of {k : nat} (X : Diagram k) (i : Fin k.+1) : Type . *)
(* Proof. *)
(*   destruct k. exact X. *)
(*   destruct i as [i | t]. *)
(*   - exact (type_of k (prev X) i). *)
(*   - exact (last_type_of X). *)
(* Defined. *)

Definition chain' (k : nat) : {Chain : Type & Chain -> Type}.
Proof.
  induction k.
  - exists Unit. intro t. exact X0.
  - destruct IHk as [C_k source].
    exists ({c : C_k & {S2 : Type & S2 -> source c}}).
    intros [c [S2 f]]. exact S2.
Defined.

Definition chain k := (pr1 (chain' k)).
Definition c_source {k} : chain k -> Type := (pr2 (chain' k)).

Definition chain_to_dia' (k : nat) :
  {e : chain k <~> Diagram k &
       (forall c : chain k,
           c_source c <~> Ind k (e c))}.
Proof.
  induction k.
  exists (equiv_idmap). simpl.
  intro t. 
  change (c_source t) with X0.  change (Ind 0) with (fun x : Unit => X0). simpl. reflexivity.


  change (chain k.+1) with {c : chain k & {S2 : Type & S2 -> c_source c}}.
  change (Diagram k.+1) with {X : Diagram k & Ind k X -> Type}.
  destruct IHk as [e1 e2].
  srapply @exist.
  - apply (equiv_functor_sigma' e1).
    intro c.
    transitivity {S2 : Type & S2 -> Ind k (e1 c)}.
    + apply (equiv_functor_sigma' equiv_idmap). intro S2. simpl.
      apply (equiv_postcompose (e2 c)).
    + generalize (Ind k (e1 c)). intro T.
      
    srapply @equiv_adjointify.
    * intros [S2 f].
      exact (fun x => hfiber f x).
    * intro X. exists {x : T & X x}. exact pr1.
    * intro X. apply path_arrow. intro x.
      apply path_universe_uncurried.
      apply equiv_inverse.
      apply (hfiber_fibration x X).
    * intros [S2 f].
      srapply @path_sigma'. apply path_universe_uncurried. apply equiv_inverse.
      apply equiv_fibration_replacement.
      apply (transport_exp T _ _ ((equiv_fibration_replacement f)^-1)).
  - simpl.
    intros [c [S2 f]]. unfold c_source. simpl.
    unfold functor_sigma. simpl.
    transitivity {u : Ind k (e1 c) & hfiber (fun x0 : S2 => (e2 c) (f x0)) u}.
    + refine (_ oE equiv_fibration_replacement f).
      apply (equiv_functor_sigma' (e2 c)).
      intro x.
      apply hfiber_compose_equiv.
    + reflexivity.
Defined.

Definition chain_to_dia (k : nat) := pr1 (chain_to_dia' k).
    
    set (x := (e1 c; fun x : Ind k (e1 c) => hfiber (fun x0 : S2 => (e2 c) (f x0)) x) : Diagram k.+1).
    change (Ind k.+1 (e1 c; fun x : Ind k (e1 c) => hfiber (fun x0 : S2 => (e2 c) (f x0)) x)) with
    {u : Ind_k (e1 c) & hfiber (fun x0 : S2 => (e2 c) (f x0)) u}.
    
    unfold Ind. 

    change (c_source (c; (S2; f))) with S2.
    
      refine (transport_exp T _ _ ((equiv_fibration_replacement f)^-1) _ @ _).
      simpl.

      
      change (fun x0 : {x0 : Ind k (e1 a) & X x0} => (e2 a)^-1 (let (proj1_sig, _) := x0 in proj1_sig))
             with ((e2 a)^-1 o pr2).

      hfiber_compose_map
      cut (
      
      simpl.

    
    transitivity ((c_source a) -> Type).
    srapply @equiv_adjointify.
    + intros [S2 f]. exact (hfiber f).
    + intro P.
      exists {x : c_source a & P x}. exact pr1.
    + intro P.
      apply inverse.
      apply path_arrow. intro x.
      apply path_universe_uncurried. apply hfiber_fibration.
    + intros [S2 f].
      srapply @path_sigma. simpl. apply path_universe_uncurried.
      
      apply (equiv_functor_sigma ()).
      
      hfiber_fibration
      exact (; pr1).
    
    apply equiv_inverse. apply .
    
    Check .
  

  
  exists (IHk c).
  

  

Inductive chain : forall (S : Type) (k : nat), Type :=
|nil : chain X0 0
|cons : forall (S1 S2 : Type) (k : nat),
    (S2 -> S1) -> chain S1 k -> chain S2 k.+1.

(* if there is something in chain S T 0, then S and T are equal *)
Definition eq_chain_0' (S : Type) (k : nat) : chain S k -> 
  match k with
    | 0 => X0 = S
    | k.+1 => Unit end.
Proof.
  intro c. destruct c.
  reflexivity.
  exact tt.
Defined.

Definition eq_chain_0 (S : Type) : chain S 0 -> X0 = S := eq_chain_0' S 0.
(* Definition isequiv_eq_chain_0 (S T : Type) : IsEquiv (eq_chain_0 S T). *)
(* Proof. *)
(*   srapply @isequiv_adjointify. *)
(*   intros []. apply nil. *)
(*   intros []. reflexivity. *)
(*   intro c. *)
(*   unfold eq_chain_0. *)
(*   eq_chain_0' S T c k = match k with *)
(*                          |O =>  *)
  
(*   destruct (eq_chain_0 S T c). destruct c. *)

Definition issig_chain (S : Type) (k : nat) :
  chain S k <~> match k with
                  |0 => X0=S
                  |k.+1 => {S' : Type & (S -> S') * chain S' k}
                  end.
Proof.
  srapply @equiv_adjointify.
  - intro c. induction c.
    reflexivity.
    exists S1. exact (s, c).
  - induction k.
    intros []. apply nil.
    intros [S' [f c]].
    apply (cons _ _  k f c).
  - intro.
    induction k.
    destruct x. reflexivity.
    simpl. destruct x as [S' [f c]]. reflexivity.
  - intro c. induction c.
    + reflexivity.
    + reflexivity.
Defined.

Definition dia_to_chain (k : nat) (X : Diagram k) : chain (last_type_of X) k.
Proof.
  induction k.
  - exact nil.
  - srapply @cons.
    exact (last_type_of X.1). exact pr1. apply IHk.
Defined.


(* Definition dia_to_chain (k : nat) (X : Diagram k) : chain (fst_type_of X) (last_type_of X) k. *)
(* Proof. *)
(*   induction k. simpl. destruct (eq_last_type_of_0 X)^. apply nil. *)
(*   simpl. apply (cons _ _ _ _ (last_type_of_to_pred X)). apply IHk. *)
(* Defined. *)



(* Inductive chain (T : Type) : forall (S : Type), Type := *)
(* |nil : chain T T *)
(* |cons : forall (S1 S2 : Type), (S2 -> S1) -> chain T S1 -> chain T S2. *)

(* Definition len {T S : Type} : chain T S -> nat. *)
(* Proof. *)
(*   intro c. induction c. *)
(*   - exact 0. *)
(*   - exact (IHc.+1). *)
(* Defined. *)

(* Definition dia_to_chain (k : nat) (X : Diagram k) : chain (fst_type_of X) (last_type_of X). *)
(* Proof. *)
(*   induction k. simpl. (* apply (cons _ _ _ (last_type_of_0 X)). apply nil. *) *)
(*   destruct (eq_last_type_of_0 X)^. apply nil. *)
(*   (* exact (transport (chain X) (path_universe (last_type_of_0 X))^ (nil X)). *) *)
(*   simpl. *)
(*   apply (cons _ _ _ (last_type_of_to_pred X)). *)
(*   apply IHk. *)
(* Defined. *)

(* Definition len_dia_to_chain (k : nat) (X : Diagram k) : *)
(*   len (dia_to_chain k X) = k. *)
(* Proof. *)
(*   induction k. *)
(*   - unfold dia_to_chain. simpl.   *)
(*     destruct (eq_last_type_of_0 X)^. reflexivity. *)
(*   - simpl. apply (ap S). apply IHk. *)
(* Defined. *)

Definition chain_to_dia' {S : Type} {k : nat} (c : chain S k) :
  (* {X : Diagram k & ((fst_type_of X) <~> T)* ((last_type_of X) <~> S)}. *)
  {X : Diagram k & (last_type_of X) <~> S}.
Proof.
  induction c as [ | S1 S2 k f c IHc].
  - exists tt. reflexivity.
  - srapply @exist.
    + change (Diagram k.+1) with {X : Diagram k & Ind k X -> Type}.
      (* change (Ind (len c).+1) with (fun X => {u : Ind (len c) (prev X) & last X u}). simpl. *)
      destruct IHc as [X e].
      exists X. 
      intro x.
      exact (hfiber f (e x)).
    + destruct IHc as [X e]. simpl.
      unfold last_type_of.
      (* simpl. *)
      
      (* change (Ind k.+1 (X; fun x : Ind k X => hfiber f (e x))) with *)
      (* (n X => {u : Ind k (prev X) & last X u}). simpl. *)
      (* unfold last_type_of in e. *)
      (* change (@prev k.+1 (X; fun x : Ind k.+1 X => hfiber f (e x))) with X. *)
      (* change (@last k.+1 (X; fun x : Ind k.+1 X => hfiber f (e x))) with *)
      (* (fun x => hfiber f (e x)). *)
      refine ((equiv_fibration_replacement f)^-1 oE _).
      apply (equiv_functor_sigma' e).
      intro a. reflexivity.
Defined.

Definition technical_lemma {S : Type} {k : nat}
  : {X : Diagram k & (last_type_of X) <~> S} <~> {X : Diagram k & (last_type_of X) = S}.
Proof.
  apply (equiv_functor_sigma' equiv_idmap).
  intro a. apply equiv_path_universe.
Defined.

Definition chain_to_dia {S : Type} {k : nat} :
  chain S k -> Diagram k :=
  pr1 o (chain_to_dia').

(* Definition fst_type_chain_to_dia {T S : Type} {k : nat} (c : chain T S k) : *)
(*   fst_type_of (chain_to_dia c) = T. *)
(* Proof. *)
(*   induction c. reflexivity. apply IHc. *)
(* Defined. *)

(* Definition last_type_chain_to_dia {T S : Type} {k : nat} (c : chain T S k) *)
(*   : last_type_of (chain_to_dia c) <~> S := *)
(*   (pr2 (chain_to_dia' c)). *)

(* Definition equiv_dia_chain k (T S : Type): *)
(*   chain T S k <~> {X : Diagram k & (fst_type_of X = T)*(last_type_of X = S)}. *)
(* Proof. *)
(*   refine (_ oE issig_chain T S k).   *)
(*   induction k. *)
(*   - simpl. change (Diagram 0) with Type. *)
(*     srapply @equiv_adjointify. intros []. exists T. *)
(*     exact (idpath, eq_last_type_of_0 T). *)
(*     intros [X [p q]]. *)
(*     exact (p^ @ (eq_last_type_of_0 X)^ @ q). *)
(*     intros [X [[] []]]. simpl. *)
(*     destruct (eq_last_type_of_0 X). reflexivity. *)
(*     intros []. simpl. *)
(*     destruct (eq_last_type_of_0 T). reflexivity. *)
(*   - change (Diagram k.+1) with {X : Diagram k & Ind k.+1 X -> Type}. *)
(*     srapply @equiv_adjointify. *)
(*     + intros [S' [f c]]. *)
(*       srapply @exist. *)

(* Definition chain_uncurried (k : nat) (TS : Type*Type) *)
(*   := chain (fst TS) (snd TS) k. *)

(* Definition equiv_dia_chain k (S : Type) : *)
(*   {X : Diagram k & (last_type_of X) <~> S} <~> {T : Type & chain T S k}. *)
(* Proof. *)
(*   srapply @equiv_adjointify. *)
(*   - intros [X e]. *)
(*     exists (fst_type_of X). destruct (path_universe e). *)
(*     apply dia_to_chain. *)
(*   - intros [T c]. apply (chain_to_dia' c). *)
(*   - intros [T c]. *)
(*     destruct (chain_to_dia' c) as [X e]. simpl. destruct (path_universe e). clear e. *)
    

    
(*     simpl. induction c. *)
(*     + destruct (path_universe *)
(*       (let (proj1_sig, proj2_sig) as s return ((fun X : Diagram 0 => last_type_of X <~> T) s.1) := *)
(*          chain_to_dia' (nil T) in *)
(*        proj2_sig)). *)

Definition equiv_dia_chain k :
  Diagram k <~> chain (

          match k with
                  |0 => Unit
                  |k.+1 => {S : Type & chain S k.+1} end.
Proof.
  induction k. reflexivity.  
  change (Diagram k.+1) with {X : Diagram k & Ind k X -> Type}.
  transitivity {S2 : Type & {S1 : Type & (S2 -> S1) * chain S1 k}}.
  - srapply @equiv_adjointify.
    intros [Xk X_Sk].
    exists {xk : Ind k Xk & X_Sk xk}.
    exists (Ind k Xk).
    
    
    + intros [[] X1]. unfold Ind in X1. simpl in X1.
        exists {x0 : X0 & X1 x0}. exists X0.
        exact (pr1, nil).
      * intros 

    
  - apply (equiv_functor_sigma' equiv_idmap). intro S2. simpl.
    apply equiv_inverse.
    apply issig_chain.
    
  
  induction k.
  - change (Diagram 0) with Unit.
    apply equiv_inverse.
    srapply @equiv_contr_unit.
    


Definition equiv_dia_chain k (S : Type) :
  {X : Diagram k & (last_type_of X) <~> S} <~> chain S k.
Proof.
  srapply @equiv_adjointify.
  - intros [X e].
    apply (transport (fun Y => chain Y k) (path_universe e)).
    apply (dia_to_chain k X).
  - intro c. (* apply (technical_lemma). *)
    apply (chain_to_dia' c).
  - intro c.
    induction c.
    + simpl.
      change nil with (transport (fun Y : Type => chain Y 0) idpath nil).
      apply (ap (fun p => transport (fun Y : Type => chain Y 0) p nil)).
      apply path_universe_1.
    + 
    simpl. 
    destruct IHc. 
    transport_compose

    simpl.
    reflexivity.
    unfold path_universe.  simpl.
    
    destruct (path_universe_1).
    
    unfold path_universe_uncurried. 
    unfold equiv_inverse.

    unfold equiv_path.
    destruct 


    destruct (path_universe e).
    exists (last_type_of X). destruct p.
    apply (dia_to_chain k X).
  - intros [S c].
    exists (chain_to_dia c). apply (fst_type_chain_to_dia c).
  - intros [S c].
    unfold chain_to_dia. srapply @path_sigma. simpl.
    destruct (chain_to_dia' c) as [X e]. apply (path_universe e).
    simpl.
    

    destruct (chain_to_dia' c) as [X e].
    apply (ap (fun x => (last_type_of X; x))).
    
    
    unfold chain_uncurried in c. simpl in c.
    
    
    
    srapply @path_sigma.
    simpl. exact (path_prod (fst_type_of (chain_to_dia c), last_type_of (chain_to_dia c))
                            (T, S)
                            (fst_type_chain_to_dia c) (path_universe (last_type_chain_to_dia c))).
    simpl.
    refine (transport_path_prod (chain_uncurried k) _ _ _ @ _).
    simpl.
    unfold chain_uncurried in *. simpl in *.
    induction c.
    + destruct (fst_type_chain_to_dia (nil T)).
    
    
    destruct (fst_type_chain_to_dia c)^.
    destruct (path_universe (last_type_chain_to_dia c)).

    
    induction c. simpl.
    
    refine (transport_compose (chain_uncurried k)
    

    
    induction c.
    + simpl.  destruct (eq_last_type_of_0 T)^. reflexivity.
    + simpl.

      
      destruct ((equiv_path_sigma _ _ _)^-1 IHc) as [pq r]. clear IHc.
      simpl in r. simpl in pq.
      destruct ((equiv_path_prod _ _)^-1 pq) as [p q]. simpl in p,q.
      srapply @path_sigma.
      srapply @path_prod.
      * simpl. refine (_ @ p).
        apply (ap fst_type_of). simpl. reflexivity.
      * simpl. 
      simpl.
      refine (ap (fst o pr1) IHc).
      simpl. refine (path_universe (chain_to_dia (cons _ _ _ s c)).2).
      
      
      apply (ap (fst_type_of)). unfold chain_to_dia.
      
      simpl. 
      srapply @path_sigma.
      * 
      
    + simpl. induction k; simpl.
      apply path_prod.
      * simpl. unfold chain_to_dia.
      
  
  


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
    

  