Require Import HoTT.
Require Import UnivalenceAxiom.

(* This is also in Gamma plus *)
Definition equiv_emoveR_fV `{Funext} {A B C : Type} (e : A <~> B) (f : B -> C) (g : A -> C) : 
  g = f o e <~> g o e^-1 = f.
Proof.
  transitivity (g == f o e).
  apply equiv_inverse.
  apply equiv_path_arrow.
  transitivity (g o e^-1 == f).
  unfold pointwise_paths.
  apply equiv_inverse.
  apply (equiv_functor_forall' e).
  intro b.
  apply (equiv_concat_l).
  apply (ap g).
  change (e^-1 (e b)) with ((e^-1 o e) b).
  apply (ap10 (f:= idmap)).
  apply path_arrow.
  intro x. apply inverse. apply (eissect e).
  apply equiv_path_arrow.
Defined.

Record Type_Over (X : Type) :=
  {type_of_over : Type; arrow_of_over : type_of_over -> X}.


Coercion type_of_over : Type_Over >-> Sortclass.
Arguments Build_Type_Over {X} A f : rename.
Arguments type_of_over {X} A : rename.
Arguments arrow_of_over {X} A x : rename.
Context {X : Type}.


Definition issig_type_over {X : Type} :
  Type_Over X <~> {Y : Type & Y -> X}.
Proof.
  srapply @equiv_adjointify.
  - intros [A f]. exact (A ;f).
  - intros [A f]. exact (Build_Type_Over A f).
  - intros [A f]. reflexivity.
  - intros [A f]. reflexivity.
Defined.

Definition path_type_over (A B : Type_Over X)
           (e : A <~> B) (p : arrow_of_over A = (arrow_of_over B) o e)
  : A = B.
Proof.
  apply (equiv_ap issig_type_over A B)^-1.  
  srapply @path_sigma.
  apply path_universe_uncurried. exact e.
  refine (transport_exp X A B e (issig_type_over A).2 @ _).
  apply (equiv_emoveR_fV). exact p.
Defined.


(* Definition Type_Over (X : Type)   := *)
(*   {Y : Type & Y -> X}. *)




(* Definition type_of_over {X : Type}: (Type_Over X) -> Type := pr1. *)

(* (* Arguments type_of_over {X} x : simpl never. *) *)

(* Coercion type_of_over : Type_Over >-> Sortclass. *)

(* Context {X : Type}. *)

(* Definition path_type_over (A B : Type_Over X) (e : A <~> B) (p : A.2 = B.2 o e) *)
(*   : A = B. *)
(* Proof. *)
(*   srapply @path_sigma. *)
(*   apply path_universe_uncurried. exact e. *)
(*   refine (transport_exp X A B e A.2 @ _). *)
(*   apply (equiv_emoveR_fV). exact p. *)
(* Defined. *)
  

Definition prod_over : (Type_Over X) -> (Type_Over X) -> Type_Over X.
Proof.
  intros [A f] [B g].
  apply (Build_Type_Over { ab : A*B & f (fst ab) = g (snd ab)}).
  intros [[a b] p]. exact (f a).
Defined.

Arguments prod_over !A !B.



Definition fst_over (A B : Type_Over X)
  : prod_over A B -> A := fst o pr1.

Arguments fst_over !A !B x. (* : simpl never. *)

Definition snd_over (A B : Type_Over X)
  : prod_over A B -> B := snd o pr1.

Arguments snd_over !A !B x. (* : simpl never. *)

Definition path_prod_over (A B : Type_Over X) (a1 a2 : A) (b1 b2 : B)
           (p1 : arrow_of_over A a1 = arrow_of_over B b1)
           (p2 : arrow_of_over A a2 = arrow_of_over B b2)
           (qa : a1 = a2) (qb : b1 = b2)
           (comm : (p1 @ (ap (arrow_of_over B) qb) = ap (arrow_of_over A) qa @ p2))
  : ((a1,b1);p1) = ((a2,b2);p2) :> prod_over A B.
Proof.
  srapply @path_sigma.
  exact (path_prod (a1,b1) (a2,b2) qa qb).
  cbn.
  destruct A as [A f]. destruct B as [B g]. cbn in *.
  refine (transport_path_prod (fun ab : A * B => f (fst ab) = g (snd ab))
                              (x := (a1, b1)) (y := (a2, b2)) qa qb p1 @ _).
  cbn.
  refine (transport_paths_Fl qa (transport (fun y : B => f a1 = g y) qb p1) @ _).
  apply moveR_Vp.
  refine (transport_paths_Fr qb p1 @ _). exact comm.
Defined.


Definition sum_over : (Type_Over X) -> (Type_Over X) -> Type_Over X.
Proof.
  intros [A f] [B g]. exists (A + B). intros [a | b]. exact (f a). exact (g b).
Defined.

Definition hunion : (Type_Over X) -> (Type_Over X) -> Type_Over X.
Proof.
  intros A B.
  exists (pushout (fst_over A B) (snd_over A B)).
  srapply @pushout_rec.
  - apply sum_over.
  - destruct A as [A f]. destruct B as [B g]. cbn.
    intros [[a b] p]. cbn.
    exact p.
Defined.
Arguments hunion !A !B.

Definition pu (A B : Type_Over X) (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b) :
                  push (inl a) = push (inr b) :> hunion A B.
Proof.
  refine (pp ((a,b);p)).
Defined.

Definition hunion_ind (A B : Type_Over X) (P : hunion A B -> Type)
           (push' : forall ab : A + B, P (push ab)) :
(forall (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b),
    transport P (pu A B a b p) (push' (inl a)) = push' (inr b)) ->
forall u : hunion A B, P u.
Proof.
  intros p'.
  apply (pushout_ind _ _ P push').
  destruct A as [A f]. destruct B as [B g].
  intros [[a b] p]. cbn in *.
  unfold pu in p'. apply p'.
Defined.

Definition hunion_ind_beta_pu (A B : Type_Over X)
           (P : hunion A B -> Type)
           (push' : forall ab : A + B, P (push ab))
           (pu' : (forall (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b),
                     transport P (pu A B a b p) (push' (inl a)) = push' (inr b)))
           (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b) :
  apD (hunion_ind A B P push' pu') (pu A B a b p) = pu' a b p.
Proof.
  destruct A as [A f]. destruct B as [B g].
  unfold hunion_ind. cbn in *. unfold pu.
  apply (pushout_ind_beta_pp P push'
                              (fun abp : {ab : A*B & f (fst ab) = g (snd ab)} =>
                                 pu' (fst abp.1) (snd abp.1) (abp.2))
                              ((a, b);p)).
Defined.

Arguments hunion : simpl never.
Arguments pu : simpl never.
Arguments hunion_ind : simpl never.
Arguments hunion_ind_beta_pu : simpl never.

Definition hunion_rec (A B : Type_Over X) (P : Type)
           (push' : A+B -> P)
           (pu' : forall (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b),
               push' (inl a) = push' (inr b))
  : hunion A B -> P :=
  hunion_ind A B (fun _ => P) push' (fun a b p => transport_const _ _ @ pu' a b p).

Definition hunion_rec_beta_pu (A B : Type_Over X) (P : Type)
           (push' : A+B -> P)
           (pu' : forall (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b),
               push' (inl a) = push' (inr b))
           (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b) :
  ap (hunion_rec A B P push' pu') (pu A B a b p) = pu' a b p.
Proof.
  unfold hunion_rec.
  eapply (cancelL (transport_const (pu A B a b p) _)).
  refine ((apD_const (@hunion_ind A B (fun _ => P) push' _) (pu A B a b p))^ @ _).
  refine (hunion_ind_beta_pu A B (fun _ => P) _ _ _ _ _).
Defined.  

Definition assoc_prod_over : forall A B C : Type_Over X,
    prod_over A (prod_over B C) = prod_over (prod_over A B) C.
Proof.
  intros [A f] [B g] [C h].
  srapply @path_type_over.
  - srapply @equiv_adjointify.
    { intros [[a [[b c] p]] q]. cbn in *.
      srapply @existT.
      refine (_ , c).
      exists (a,b). cbn. exact q. 
      cbn. exact (q @ p). }
    { intros [[[[a b] p] c q]]. cbn in *.
      srapply @existT.
      apply (pair a).
      exists (b,c). cbn. exact (p^ @ q). cbn. exact p. }
    + intros [[[[a b] p] c q]]. cbn in *.
      (apply (ap (fun q' => ((((a, b); p), c); q')))).
      apply moveR_Mp. reflexivity.
    + intros [[a [[b c] p]] q]. cbn in *.
      srapply @path_sigma. cbn.
      apply (ap (fun p' => (a, ((b, c); p')))).
      apply moveR_Vp. reflexivity.
      cbn.
      refine (transport_paths_FlFr
                (ap (fun p' : g b = h c => (a, ((b, c); p'))) (moveR_Vp (q @ p) p q 1)) q @ _).
      transitivity ((idpath @ q) @ idpath).
      apply concat2. apply whiskerR.
      * apply (inverse2 (q:=idpath)).
        refine ((ap_compose _ _ _)^ @ _). cbn.
        apply ap_const.
      * refine ((ap_compose _ _ _)^ @ _). cbn.
        apply ap_const.
      * exact (concat_p1 _ @ concat_1p q).
  - cbn. reflexivity.
Defined.

Definition distribute_over_disjoint : forall A B C : Type_Over X,
    prod_over (sum_over A B) C <~> sum_over (prod_over A C) (prod_over B C).
Proof.
  intros [A f] [B g] [C h].
  srapply @equiv_adjointify. cbn.
  intros [[[a | b] c] p]; cbn in *.
  - apply inl. exists (a,c). exact p.
  - apply inr. exists (b,c). exact p.
  - intros [[[a c] p] | [[b c] p]]; cbn in *.
    + exists ((inl a),c). exact p.
    + exists ((inr b),c). exact p.
  - intros [[[a c] p] | [[b c] p]]; reflexivity.
  - intros [[[a | b] c] p]; reflexivity.
Defined.

Definition distribute_over_disjoint_commute (A B C : Type_Over X) :
  arrow_of_over (prod_over (sum_over A B) C) =
  arrow_of_over (sum_over (prod_over A C) (prod_over B C)) o (distribute_over_disjoint A B C).
Proof.
  destruct A as [A f]. destruct B as [B g]. destruct C as [C h]. cbn. 
  apply path_arrow.
  intros [[[a | b] c] p]; reflexivity.
Defined.

Definition sigma_over (A : Type) (B : A -> Type_Over X) : Type_Over X.
Proof.
  apply (Build_Type_Over {a : A & B a}).
  intros [a b]. exact (arrow_of_over (B a) b).
Defined.

Definition distribute_over_sigma (A : Type_Over X) (B : Type) (C : B -> Type_Over X) :
  prod_over A (sigma_over B C) = sigma_over B (fun b => prod_over A (C b)).
Proof.
  srapply @path_type_over.
  - srapply @equiv_adjointify.
    + cbn. intros [[a [b c]] p]. cbn in *.
      exists b. exists (a, c). cbn. apply p.
    + cbn. intros [b [[a c] p]]. cbn in *.
      exists (a, (b;c)). cbn. apply p.
    + intros [b [[a c] p]]. reflexivity.
    + intros [[a [b c]] p]. reflexivity.
  - cbn. apply path_arrow. 
    intros [[a [b c]] p]. reflexivity.
Defined.

Definition injective_over (A : Type_Over X) := forall {a1 a2 : A}, (arrow_of_over A a1) = (arrow_of_over A a2) -> a1 = a2.

Definition hunion_preserve_injection (A B : Type_Over X) (inj_A : injective_over A) (inj_B : injective_over B)
           : injective_over (hunion A B).
Proof.
  unfold injective_over. intros ab1 ab2. revert ab2.
  srapply @hunion_ind. intro ab2. revert ab1. srapply @hunion_ind.
  - intro ab1. revert ab1 ab2. intros [a1 | b1] [a2 | b2].
    + intro p.
      apply (ap (push o inl)).
      apply inj_A. apply p.
    + intro p.
      apply pu. apply p.
    + intro p. apply inverse.
      apply pu. apply p^.
    + intro p.
      apply (ap (push o inr)).
      apply inj_B. apply p.
  - intros a1 b1 p. cbn.
    apply path_arrow. intro q.
    refine (transport_arrow
              (pu A B a1 b1 p) _ _ @ _).
    refine (transport_paths_l (pu A B a1 b1 p) _ @ _).    
    destruct ab2 as [a2 | b2].
    + apply moveR_Vp.
Abort.
  

Definition has_section (A : Type_Over X) :=
  {s : X -> A & s o (arrow_of_over A) = idmap}.

(* Do over disjoint sum first? *)
Definition distribute_over : forall (A B C : Type_Over X)
                                    (has_section_A : has_section A),
    prod_over A (hunion B C) = hunion (prod_over A B) (prod_over A C).
Proof.
  (* intros [A f] [B g] [C h]. intro. *) intros.
  srapply @path_type_over.
  - srapply @equiv_adjointify.
    { intros [[a b] p]. cbn in *. revert b p.
      destruct A as [A f]. destruct B as [B g]. destruct C as [C h].
      srapply @hunion_ind.
      - intros [b  | c] p.
        + simpl in b, p.
          apply (push o inl). exists (a,b). exact p.
        + simpl in c, p.
          apply (push o inr). exists (a,c). exact p.
      - intros b c p. simpl in b,c,p. cbn.
        apply path_arrow. intro q. simpl in q.
        refine
          (transport_arrow
             (pu {| type_of_over := B; arrow_of_over := g |} {| type_of_over := C; arrow_of_over := h |} b c p)
             (fun
                 p0 : f a =
                      (let (type_of_over, arrow_of_over) as t return (t -> X) :=
                           hunion {| type_of_over := B; arrow_of_over := g |} {| type_of_over := C; arrow_of_over := h |} in
                       arrow_of_over) (push (inl b)) => push (inl ((a, b); p0))) q
             @ _).
        refine
          (transport_const
             (pu {| type_of_over := B; arrow_of_over := g |} {| type_of_over := C; arrow_of_over := h |} b c p)
             (push
                (inl
                   ((a, b);
                    transport
                      (fun x : hunion {| type_of_over := B; arrow_of_over := g |} {| type_of_over := C; arrow_of_over := h |} =>
                         f a =
                         (let (type_of_over0, arrow_of_over0) as t return (t -> X) :=
                              hunion {| type_of_over := B; arrow_of_over := g |} {| type_of_over := C; arrow_of_over := h |} in
                          arrow_of_over0) x) (pu {| type_of_over := B; arrow_of_over := g |} {| type_of_over := C; arrow_of_over := h |} b c p)^ q))) @ _).
        srapply @pu. reflexivity.
    }
    {
      srapply @hunion_ind.
      - intros [[[a b] p]|[[a c] p]].
        + simpl in p.
          exists (a, (push (inl b))). exact p.
        + cbn in p.
          exists (a, (push (inr c))). exact p.
      - intros [[a1 b] p] [[a2 c] q] r. cbn in *.
        refine
          (transport_const
             (pu (prod_over A B) (prod_over A C) ((a1, b); p) ((a2, c); q) r)
             ((a1, push (inl b)); p) @ _).
        srapply (@path_prod_over A (hunion B C)).
        + destruct A as [A f]. destruct B as [B g]. destruct C as [C h]. 
          destruct has_section_A as [s issect]. cbn in *.
          transitivity (s (f a2)). transitivity (s (f a1)).
          exact (ap10 issect a1)^.
          exact (ap s r).
          exact (ap10 issect a2).
        + destruct A as [A f]. destruct B as [B g]. destruct C as [C h].  cbn in *.
          apply pu. cbn. exact (p^ @ r @ q).
        + destruct A as [A f]. destruct B as [B g]. destruct C as [C h].  cbn in *.
          apply moveR_Mp.
          simpl. unfold pu.
          refine (pushout_rec_beta_pp X _ _ _ @ _).
          refine (concat_pp_p _ _ _ @ _).
          apply whiskerL. apply whiskerR.
          destruct has_section_A as [s issect]. cbn in *.
          apply inverse.

          set (issect_of_r := ((ap10 issect a1)^ @ ap (fun x : X => (s x)) r) @ (ap10 issect a2) : a1 = a2).
          cut (forall (f1 f2 : A -> A) (h : f1 = f2) (x y : A) (p : x = y),
                  (ap10 h x)^ @ (ap f1 p) @ (ap10 h y) = ap f2 p).
          intro H.
          (* Check (H (s o f) idmap issect a1 a2 issect_of_r). *)
Abort.



(* Todo: Associativity of intersect *)
(* Distributy law *)
(* Closed under injections *)

