Require Import HoTT.

Definition sig_const (A B : Type) :
  sig (fun _ : A => B) <~> A * B :=
  (@equiv_adjointify
     (sig (fun _ : A => B)) (A * B)
     (fun ab => match ab with (a ; b) => (a, b) end)
     (fun ab => match ab with (a, b) => (a ;b) end)
     (fun _ => idpath) (fun _ => idpath)).


Definition ap12 {A B : Type} {a b : A} (p : a = b) {f g : A->B} (q : f=g)  :
  (ap10 q a)^ @ (ap f p) @ (ap10 q b) = ap g p.
Proof.
  destruct p, q. reflexivity.
Defined.

(*Needs better name, I guess. . .*)
Definition ap12' `{Funext} {A B : Type} {a b : A} (p : a = b) {f g : A->B} (q : f==g)  :
  (q a)^ @ (ap f p) @ q b = ap g p.
Proof.
  refine (_ @ ap12 p (path_arrow _ _ q)).
  apply concat2.
  apply whiskerR.
  apply inverse2. exact (inverse (ap10_path_arrow f g q _)). exact (inverse (ap10_path_arrow f g q _)).
Defined.
  
(* Definition path_over {A : Type} (B : A -> Type) {a a' : A} (p : a = a') (b : B a) (b' : B a') *)
(*   := transport B p b = b'. *)

Notation path_over B p b b' := (transport B p b = b')  (only parsing).


Definition concat_over {A : Type} (B : A -> Type) {a1 a2 a3 : A} (p : a1 = a2) (q : a2 = a3)
           {b1 : B a1} {b2 : B a2} {b3 : B a3} :
  path_over B p b1 b2 -> path_over B q b2 b3 -> path_over B (p@q) b1 b3
  := fun over_p over_q => (transport_pp B p q b1 @ ap (transport B q) over_p @ over_q).

Definition apD_pp {A : Type} {B : A -> Type} (f : forall a : A, B a)
           {a1 a2 a3 : A} (p : a1 = a2) (q : a2 = a3) : 
           apD f (p @ q) = concat_over B p q (apD f p) (apD f q).
Proof.
  unfold concat_over.
  destruct p. destruct q. reflexivity.
Qed.

(*Could formulate this more generally (f also a dependent function) but this is simpler and what I need right now. . . *)
Definition apD_compose {A : Type} {B : Type} {C : B -> Type}
           {a a' : A} (p : a = a')
           (f : A -> B) (g : forall b : B, C b) :           
  apD (g o f) p = transport_compose C f p (g (f a)) @ apD g (ap f p).
Proof.
  destruct p. reflexivity.
Defined.


(* Definition transport_PQ {A : Type} {P : A -> Type} {Q : A -> Type} (h : P == Q) *)
(*            {a b : A} (pth : a = b) *)
(*            (p : P a) *)
(* :  transport idmap (h b) (transport P pth p) = transport Q pth (transport idmap (h a) p). *)
(*   destruct pth. reflexivity. Defined. *)

Definition transport_PequivQ  {A : Type} {P : A -> Type} {Q : A -> Type} (h : forall a : A, P a <~> Q a)
           {a b : A} (pth : a = b)
           (p : P a)
:  transport P pth p = (h b)^-1 (transport Q pth (h a p)).
  destruct pth. simpl. apply moveL_equiv_V. reflexivity. Defined.


(* (*A version of transport_compose I need now*) *)
(* Definition transport_compose_mine {A B : Type} (C : forall a : A, B -> Type) (f : A -> B) *)
(*            {a a' : A} (p : a = a') (c : C a (f a)) : *)
(*              transport (fun a => C a (f a)) p c = *)
(*               ap ? @ (transport (C a) (ap f p) c). *)
(* Proof. *)
(*   destruct p. reflexivity. *)
(* Defined. *)
  
  
  
  
  