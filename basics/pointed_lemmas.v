Require Import HoTT.

(* Another notation for pointed maps *)
Notation "X ->* Y" := (pMap (Build_pType X _) (Build_pType Y _)).
Infix "o*" := pmap_compose.

Definition ptype_prod (X Y : pType) : pType
  := Build_pType (X * Y) (point _, point _).


Definition isconn (X : pType) := forall (x : X), merely (point X = x).
Record Conn_pType := {X :> pType ; isconn_conn_ptype : isconn X}.

Definition conn_ptype_prod (X Y : Conn_pType) : Conn_pType.
Proof.
  apply (Build_Conn_pType (ptype_prod X Y)).
  unfold isconn.
  intros [x y].
  generalize (isconn_conn_ptype X x). intro p.
  generalize (isconn_conn_ptype Y y). intro q.
  strip_truncations. apply tr. exact (path_prod (_,_) (_,_) p q).
Defined.
  





Definition add_pt : Type -> pType :=
  fun X => Build_pType (X + Unit) (inr tt).

Global Instance transitive_pmap : Transitive pMap.
Proof.
  intros A B C. intros f g.
  exact (pmap_compose g f).
Defined.

(* In Spheres, ~(X = North) is decidable *)
Fixpoint pSphere (n : nat) : Type :=
  match n with
    |O => Unit + Unit
    |S n => Susp (pSphere n)
  end.

Instance ispointed_psphere {n : nat} : IsPointed (pSphere n)  
  :=
    match n with
    |O => inl tt                (* todo: change with inl *)
    |S n => North
    end.

Lemma IsProp_not `{Funext} {A : Type}  : IsHProp (not A).
Proof.
  apply trunc_arrow.
Defined.

Import TrM.
Definition connected_psphere {n : nat} : IsConnected 0 (pSphere n.+1).
Proof.
  unfold IsConnected. srapply @BuildContr.
  - apply tr. exact North.
  - intro x.
    strip_truncations.
    revert x. srapply @Susp_ind.
    + reflexivity.
    + apply (ap tr). exact (merid (point (pSphere n))).
    + intro x. apply (istrunc_truncation 0).
Defined.

(* Should be generalized to all connected types? *)
(* Definition not_eq_bp_conn `{Funext} {X : pType} (isconn_X : IsConnected 0 X) (x : X) : *)
(*   ~ (~ x = point X). *)
(* Proof. *)
(*   destruct isconn_X. intro. *)
(* Abort. *)

(* Can this be generalized to all connected types? *)
Definition n_neq_bp_Sphere `{Funext} {X : Type} (x : X) : forall s : Susp X, ~ ~ s = North.
Proof.
  srapply @Susp_ind.
  - intro ne. exact (ne idpath).
  - intro ne. exact (ne (merid x)^).
  - intro x1. apply IsProp_not.
Defined.    

Definition decidable_ne_bp `{Funext} (n : nat) (x : pSphere n) : Decidable (~ x = point (pSphere n)).
Proof.
  unfold Decidable.
  destruct n.
  - destruct x as [[] |].
    + apply inr. unfold point. unfold ispointed_psphere. intro ne. exact (ne idpath).
    + apply inl. apply inr_ne_inl.
  - apply inr. apply (n_neq_bp_Sphere (point (pSphere n))).
Defined.

(* Global Instance ispointed_arrow (A : Type) (B : pType) : IsPointed (A -> B) := const (point B *)
       
