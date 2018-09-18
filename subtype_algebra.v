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


Definition disjoint_sum_over : (Type_Over X) -> (Type_Over X) -> Type_Over X.
Proof.
  intros [A f] [B g]. exists (A + B). intros [a | b]. exact (f a). exact (g b).
Defined.

Definition sum_over : (Type_Over X) -> (Type_Over X) -> Type_Over X.
Proof.
  intros A B.
  exists (pushout (fst_over A B) (snd_over A B)).
  srapply @pushout_rec.
  - apply disjoint_sum_over.
  - destruct A as [A f]. destruct B as [B g]. cbn.
    intros [[a b] p]. cbn.
    exact p.
Defined.
Arguments sum_over !A !B.

Definition ps (A B : Type_Over X) (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b) :
                  push (inl a) = push (inr b) :> sum_over A B.
Proof.
  refine (pp ((a,b);p)).
Defined.

Definition sum_over_ind (A B : Type_Over X) (P : sum_over A B -> Type)
           (push' : forall ab : A + B, P (push ab)) :
(forall (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b),
    transport P (ps A B a b p) (push' (inl a)) = push' (inr b)) ->
forall u : sum_over A B, P u.
Proof.
  intros p'.
  apply (pushout_ind _ _ P push').
  destruct A as [A f]. destruct B as [B g].
  intros [[a b] p]. cbn in *.
  unfold ps in p'. apply p'.
Defined.

Definition sum_over_ind_beta_ps (A B : Type_Over X)
           (P : sum_over A B -> Type)
           (push' : forall ab : A + B, P (push ab))
           (ps' : (forall (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b),
                     transport P (ps A B a b p) (push' (inl a)) = push' (inr b)))
           (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b) :
  apD (sum_over_ind A B P push' ps') (ps A B a b p) = ps' a b p.
Proof.
  destruct A as [A f]. destruct B as [B g].
  unfold sum_over_ind. cbn in *. unfold ps.
  apply (pushout_ind_beta_pp P push'
                              (fun abp : {ab : A*B & f (fst ab) = g (snd ab)} =>
                                 ps' (fst abp.1) (snd abp.1) (abp.2))
                              ((a, b);p)).
Defined.

Definition sum_over_rec (A B : Type_Over X) (P : Type)
           (push' : A+B -> P)
           (ps' : forall (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b),
               push' (inl a) = push' (inr b))
  : sum_over A B -> P.
Proof.
  apply (pushout_rec P push').
  destruct A as [A f]. destruct B as [B g].
  intros [[a b] p]. cbn in *. apply ps'. exact p.
Defined.

Definition sum_over_rec_beta_ps (A B : Type_Over X) (P : Type)
           (push' : A+B -> P)
           (ps' : forall (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b),
               push' (inl a) = push' (inr b))
           (a : A) (b : B) (p : arrow_of_over A a = arrow_of_over B b) :
  ap (sum_over_rec A B P push' ps') (ps A B a b p) = ps' a b p.
Proof.
  destruct A as [A f]. destruct B as [B g].
  unfold sum_over_rec. cbn in *. unfold ps.
  apply (pushout_rec_beta_pp P push'
                             (fun abp : {ab : A*B & f (fst ab) = g (snd ab)} =>
                                 ps' (fst abp.1) (snd abp.1) (abp.2))
                              ((a, b);p)).
Defined.  



Definition assoc_prod_over : forall A B C : Type_Over X,
    prod_over A (prod_over B C) = prod_over (prod_over A B) C.
Proof.
  intros [A f] [B g] [C h].
  srapply @path_type_over.
  - srapply @equiv_adjointify.
    { intros [a [[b [c p]] q]]. cbn in *. 
      srapply @existT. 
      exists a. exists b. exact q.
      cbn. exists c. exact (q @ p). }
    { intros [[a [b p] [c q]]]. cbn in *.
      exists a.
      srapply @existT. exists b. exists c. exact (p^ @ q). cbn. exact p. }
    + intros [[a [b p] [c q]]]. cbn in *.
      (apply (ap (fun cq => ((a; (b; p)); cq)))).
      apply (ap (fun q' => (c;q'))).
      apply moveR_Mp. reflexivity.
    + intros [a [[b [c p]] q]]. cbn in q.
      apply (ap (fun bcpq => (a; bcpq))).
      srapply @path_sigma.  cbn.
      apply (ap (fun p => (b; (c; p)))).
      apply moveR_Vp. reflexivity.
      cbn.
      refine
        (transport_paths_Fr
           (ap (fun p0 : g b = h c => (b; (c; p0))) (moveR_Vp (q @ p) p q 1))
           q @ _).
      apply moveR_Mp.
      refine (_ @ (concat_Vp q)^).
      (* This is a detour, but I only get problems going more directly. . . *)
      refine (ap_compose pr1 g (ap (fun p0 : g b = h c => (b; (c; p0))) (moveR_Vp (q @ p) p q 1)) @ _).
      refine (_ @ ap_1 _ g).
      apply (ap (ap g)).
      transitivity (ap (fun p0 : g b = h c => (@proj1_sig B (fun b => {c : C & g b = h c})
                                                          (b ; (c; p0)))) (moveR_Vp (q @ p) p q 1)).      
      apply inverse.
      refine (_ @ ap_compose
               (fun p0 : g b = h c =>
                  exist (fun b => {c : C & g b = h c}) b (exist (fun c => g b = h c)  c p0))
               (@proj1_sig B (fun b => {c : C & g b = h c})) (moveR_Vp (q @ p) p q 1)). cbn.
      reflexivity.
      cbn. apply ap_const.
  - cbn. apply path_arrow.
    intros [a b]. reflexivity.
Defined.

Definition distribute_over_disjoint : forall A B C : Type_Over X,
    prod_over (disjoint_sum_over A B) C <~> disjoint_sum_over (prod_over A C) (prod_over B C).
Proof.
  intros [A f] [B g] [C h].
  srapply @equiv_adjointify. cbn.
  intros [[a | b]].
  - intros [c p]. apply inl.
    exists a. exists c. exact p.
  - intros [c p]. apply inr.
    exists b. exists c. exact p.
  - intros [[a [c p]] | [b [c p]]]; cbn.
    + exists (inl a).
      exists c. exact p.
    + exists (inr b).
      exists c. exact p.
  - cbn.
    intros [[a [c p]] | [b [c p]]]; reflexivity.
  - cbn.
    intros [[a | b]]; intros [c p]; reflexivity.
Defined.

Definition distribute_over_disjoint_commute (A B C : Type_Over X) :
  arrow_of_over (prod_over (disjoint_sum_over A B) C) =
  arrow_of_over (disjoint_sum_over (prod_over A C) (prod_over B C)) o (distribute_over_disjoint A B C).
Proof.
  destruct A as [A f]. destruct B as [B g]. destruct C as [C h].
  apply path_arrow.
  intros [[a | b]]; cbn; reflexivity.
Defined.

(* Do over disjoint sum first? *)
Definition distribute_over : forall (A B C : Type_Over X)
                                    (injective_C : forall c1 c2 : C,
                                    arrow_of_over C c1 = arrow_of_over C c2 -> c1 = c2),
    prod_over (sum_over A B) C = sum_over (prod_over A C) (prod_over B C).
Proof.
  intros [A f] [B g] [C h]. intro.
  srapply @path_type_over.
  - srapply @equiv_adjointify.
    + intros [ab]. cbn in ab.
      intros [c].  cbn.
      revert ab. srapply @pushout_ind. intros [a | b]; simpl.
      * simpl. intro p.
        apply push. apply inl.
        exists a. exists c. exact p.
      * intro p. apply push. apply inr.
        exists b. exists c. exact p.
      * cbn.
        intros [a [b p]]. cbn.
        apply path_arrow. intro q. simpl in q.
        unfold snd_over in q. simpl in q.
        refine (transport_arrow (pp (a; (b; p))) (fun p0 : f a = h c => push (inl (a; (c; p0)))) q @ _).
        refine (transport_const (pp (a; (b; p))) _ @ _).
        srapply (@ps (prod_over (Build_Type_Over A f) (Build_Type_Over C h))
                     (prod_over (Build_Type_Over B g) (Build_Type_Over C h))).
        exact p.
    + srapply @pushout_rec.
      { cbn. intros [[a [c p]] | [b [c q]]].
        - exists (push (inl a)).
          exists c. simpl. exact p.
        - exists (push (inr b)).
          exists c. simpl. exact q. }
      intros [[a [c p]] [[b [c' q] ]]]. simpl.
      intro r.
      srapply @path_sigma.
      * cbn.
        apply (ps (Build_Type_Over A f) (Build_Type_Over B g)). cbn. exact r.
      * cbn.
        refine (transport_sigma (ps (Build_Type_Over A f) (Build_Type_Over B g) a b r) (c;p) @ _).
        cbn.
        srapply @path_sigma. cbn.
        refine (transport_const
                  (ps {| type_of_over := A; arrow_of_over := f |}
                      {| type_of_over := B; arrow_of_over := g |} a b r) c @ _).
        apply (injective_C c c'). cbn. exact (p^ @ r @ q). 
        refine (transport_paths_FlFr
                   (transport_const
                      (ps {| type_of_over := A; arrow_of_over := f |} {| type_of_over := B; arrow_of_over := g |} a b r)
                      c @ @ injective_C c c' ((p^ @ r) @ q))
                   (transportD
       (fun
          _ : pushout
                (fst_over {| type_of_over := A; arrow_of_over := f |}
                   {| type_of_over := B; arrow_of_over := g |})
                (snd_over {| type_of_over := A; arrow_of_over := f |}
                   {| type_of_over := B; arrow_of_over := g |}) => C)
       (fun
          (x : pushout
                 (fst_over {| type_of_over := A; arrow_of_over := f |}
                    {| type_of_over := B; arrow_of_over := g |})
                 (snd_over {| type_of_over := A; arrow_of_over := f |}
                    {| type_of_over := B; arrow_of_over := g |})) (y : C) =>
        pushout_rec X (fun X0 : A + B => match X0 with
                                         | inl a0 => f a0
                                         | inr b0 => g b0
                                         end)
          (fun a0 : {a0 : A & {b0 : B & f a0 = g b0}} =>
           let (proj1_sig, proj2_sig) as s return ((fun b0 : B => f a0.1 = g b0) s.1) :=
             let (proj1_sig, proj2_sig) as s return ((fun a1 : A => {b0 : B & f a1 = g b0}) s.1) :=
               a0 in
             proj2_sig in
           proj2_sig) x = h y)
       (ps {| type_of_over := A; arrow_of_over := f |} {| type_of_over := B; arrow_of_over := g |} a b r)
       c p) @ _). simpl.
        rewrite ap_const. rewrite (concat_1p).
        
      cbn. simpl.
        
        simpl.
        cbn.

      



      
        cbn.
        refine
          (@ps (prod_over A C) (prod_over B C)


             (a; (c;
                   transport
                     (fun
                         x : pushout
                               (fst_over {| type_of_over := A; arrow_of_over := f |}
                                         {| type_of_over := B; arrow_of_over := g |})
                               (snd_over {| type_of_over := A; arrow_of_over := f |}
                                         {| type_of_over := B; arrow_of_over := g |}) =>
                         pushout_rec X (fun X0 : A + B => match X0 with
                                                          | inl a0 => f a0
                                                          | inr b0 => g b0
                                                          end)
                                     (fun a0 : {a0 : A & {b0 : B & f a0 = g b0}} =>
                                        let (proj1_sig, proj2_sig) as s return ((fun b0 : B => f a0.1 = g b0) s.1) :=
                                            let (proj1_sig, proj2_sig) as s return ((fun a1 : A => {b0 : B & f a1 = g b0}) s.1) :=
                                                a0 in
                                            proj2_sig in
                                        proj2_sig) x = h c) (pp (a; (b; p)))^ q))
              (b; (c; q))).
        refine (_ @ ps (
        
        simpl.
        cbn.

        cbn.
    
    



(* Todo: Associativity of intersect *)
(* Distributy law *)
(* Closed under injections *)

