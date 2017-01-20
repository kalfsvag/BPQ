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

Section Dependent_paths.
  Definition composeDD {A : Type} {B : A -> Type} {C : forall a : A, B a -> Type}
             (f : forall a : A, forall b : B a, C a b)
             (g : forall a : A, B a) : forall a : A, C a (g a) := fun a => f a (g a).

  (* Notation "f 'oDD' g" := (composeDD f g) (at level 0): function_scope. *)
  
  Notation path_over B p b b' := (transport B p b = b')  (only parsing).

  (*. . . *)
  Definition apD_compose {A : Type} {B : A -> Type} {C : forall a : A, B a -> Type}
             (f : forall a : A, forall b : B a, C a b)
             (g : forall a : A, B a)
             {a a' : A} (p : a = a') :
    apD (composeDD f g) p =
    (transport_apD_transportD B g C p (f a (g a)))^ @ apD011 f p (apD g p).
  Proof.
    destruct p; reflexivity.
  Defined.

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
  
  
  
  
  







