Require Import HoTT.



Lemma equiv_sigma_sum' (A : Type) (B C : A -> Type) :
   {a : A & B a} + {a : A & C a} <~> {a : A & B a + C a}.
Proof.
  srapply @equiv_adjointify.
  - intros [[a b] | [a c]].
    + exact (a; inl b).
    + exact (a; inr c).
  - intros [a [b | c]].
    + exact (inl (a; b)).
    + exact (inr (a; c)).
  - intros [a [b | c]]; reflexivity.
  - intros [[a b] | [a c]]; reflexivity.
Defined.



(* This was already implemented as equiv_sigma_prod0. *)
(* Definition sig_const (A B : Type) : *)
(*   sig (fun _ : A => B) <~> A * B := *)
(*   (@equiv_adjointify *)
(*      (sig (fun _ : A => B)) (A * B) *)
(*      (fun ab => match ab with (a ; b) => (a, b) end) *)
(*      (fun ab => match ab with (a, b) => (a ;b) end) *)
(*      (fun _ => idpath) (fun _ => idpath)). *)

(*The section corresponding to a dependent function:*)
Definition section_of {A : Type} {B : A -> Type} (f : forall a : A, B a) :
  A -> {a : A & B a} := fun a => (a ; f a).

Definition ap_section {A : Type} {B : A -> Type} (f : forall a : A, B a) {a a' : A} (p : a = a'):
  ap (section_of f) p = path_sigma B (a; f a) (a'; f a') p (apD f p).
Proof.
  destruct p. reflexivity.
Defined.

Definition refl_sigma {A : Type} {B : A -> Type} (a : A) (b : B a) : (a ; b) = (a ; b) :=
  path_sigma B _ _ idpath idpath.
  

Definition section_to_depfun {A : Type} {B : A -> Type} :
  {f : A -> {a : A & B a} | (pr1 o f == idmap)} -> (forall a : A, B a).
Proof.
  intros [f sect].
  exact (fun a => transport B (sect a) (f a).2).
Defined.

Definition equiv_path_sigma {A : Type} (P : A -> Type) (u v : {a : A & P a}) :
  u = v <~> {p : u.1 = v.1 & transport P p u.2 = v.2}.
Proof.
  srapply @equiv_adjointify.
  - intro p. destruct p. exact (idpath; idpath).
  - intros [p q].
    exact (path_sigma P u v p q).
  - intros [p q].
    destruct u as [u1 u2].
    destruct v as [v1 v2]. simpl in p.
    destruct p. simpl in q. destruct q. reflexivity.
  - intro p. destruct p. reflexivity.
Defined.

Definition path2_sigma {A : Type} (P : A -> Type) (u v : {a : A & P a})
           (p p' : u.1 = v.1)
           (q : transport P p u.2 = v.2)
           (q' : transport P p' u.2 = v.2)
           (h1 : p = p')
           (h2 : transport (fun p0 : u.1=v.1 => (transport P p0 u.2 = v.2)) h1 q = q')
:

           path_sigma P u v p q = path_sigma P u v p' q'.
Proof.
  destruct u as [u1 u2].
  destruct v as [v1 v2].
  simpl in p. simpl in p'. destruct h1.
  simpl in q. simpl in q'.
  simpl in h2. destruct h2.
  destruct p. destruct q.
  reflexivity.
Defined.
  

Definition path_sigma_V {A : Type} (P : A -> Type) (u v : {a : A & P a})
           (p : u.1 = v.1) (q : transport P p u.2 = v.2)
           :
             (path_sigma P u v p q)^ =
             path_sigma P v u p^ (ap (transport P p^) q^ @ transport_Vp P p u.2).
Proof.
  destruct u as [u1 u2].
  destruct v as [v1 v2].
  simpl in p. destruct p.
  simpl in q. destruct q.
  reflexivity.
Defined.
  
(* transport P p^ v.2 = u.2. *)
(* Proof. *)
(*   transitivity (transport P p^ (transport P p u.2)). *)
(*   exact (ap (transport P p^) q^). *)
(*   apply transport_Vp. *)
(* Defined. *)

  (* transport_pV *)
  (*   transport_Vp *)

           
  
