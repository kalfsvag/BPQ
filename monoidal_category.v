Require Import HoTT.
Require Import UnivalenceAxiom.
Load sigma_lemmas.
Load trunc_lemmas.
  
(* Load stuff. *)


Require Import Functor Category.
(*These notations are defined elsewhere, but I do not know how to import it.*)
Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Notation "F '_0' x" := (Functor.Core.object_of F x) (at level 10, no associativity, only parsing) : object_scope.
Notation "F '_1' m" := (Functor.Core.morphism_of F m) (at level 10, no associativity) : morphism_scope.
Open Scope category_scope.
Open Scope morphism_scope.

(* Definition diagonal_functor {C : PreCategory} : Functor C (C*C). *)
(* Proof.   *)
(*   srapply @Build_Functor. *)
(*   (* Map on objects *) *)
(*   - exact (fun c => (c,c)). *)
(*   (* Map on morphisms *) *)
(*   - exact (fun c d f => (f, f)). *)
(*   (* Respect composition *) *)
(*   - exact (fun c d e f g => idpath). *)
(*   (* Respect identity *) *)
(*   - exact (fun c => idpath). *)
(* Defined. *)

Definition pair_1 {C D : PreCategory} {c c' : C} {d d' : D} (f : c --> c') (g : d --> d') :
  morphism (C*D) (c, d) (c', d') := (f,g).


(* Definition transport_morphism_Fl {C D : PreCategory} (F : Functor C D) {c1 c2 : C} {d : D} (p : c1 = c2) (f : F c1 --> d): *)
(*            transport (fun c : C => F c --> d) p f = f o (F _1 (idtoiso C p))^-1. (* (idtoiso D (ap F p))^-1. *) *)
(* Proof. *)
(*   induction p. simpl. *)
(*   apply inverse. *)
(*   refine (_ @ right_identity D _ _ f). *)
(*   apply (ap (fun g => f o g)). *)
(*   apply identity_of. *)
(* Defined. *)

(* (* Another version that doesn't use the inverse. *)
(*    Definitionally the inverse isn't given uniquely, and that gives some problems later. . . *)
(*  *) *)
(* Definition transport_morphism_Fl' {C D : PreCategory} (F : Functor C D) *)
(*            {c1 c2 : C} {d : D} (p : c1 = c2) (f : F c1 --> d): *)
(*   f = transport (fun c : C => F c --> d) p f o (F _1 (idtoiso C p)). *)
(* Proof. *)
(*   induction p. simpl. *)
(*   apply inverse. *)
(*   refine (_ @ right_identity D _ _ f). *)
(*   apply (ap (fun g => f o g)). *)
(*   apply identity_of. *)
(* Defined.   *)


Record Magma : Type :=
  { magma_cat :> PreCategory; binary_op : Functor (magma_cat*magma_cat) magma_cat }.
Arguments binary_op {m}.

Definition binary_op_0 {M : Magma} : ((object M) * (object M) -> object M )%type :=
  object_of binary_op.


Local Notation "a + b" := (Core.object_of binary_op (a, b)). (* Just for printing. *)
Local Notation "a + b" := (binary_op (a, b)).

(* Definition binary_op_1 {M : Magma} {s1 s2 d1 d2 : object M} : *)
(*   ((s1 --> d1) * (s2 --> d2))%type -> ((s1 + s2) --> (d1 + d2)). *)
(* Proof. *)
(*   intro m. apply (morphism_of binary_op). exact m. *)
(* Defined. *)

Local Notation "f +^ g" := (binary_op _1 (f, g)) (at level 40). (* This is just for printing *)
Local Notation "f +^ g" := (binary_op _1 (pair_1 f g)) (at level 40).



(* Sum of idmaps is the idmap *)
Definition sum_idmap {M : Magma} {m n : M} : (identity m +^ identity n) = identity (m + n) :=
  identity_of binary_op (m, n).

(* Translation from right *)
Definition translate_fr {M : Magma} (a : M) : Functor M M.
Proof.
  refine (Functor.compose (D := M*M) binary_op _).
  srapply @Build_Functor.
  (* Objects *)
  - exact (fun m => (m, a)).
  (* Morphisms *)
  - intros m n f. exact (f,identity a).
  (* Respect composition *)
  - intros l m n.
    intros f g.
    apply path_prod. exact idpath. apply inverse. apply left_identity.
  (* Respect identity *)
  - exact (fun _ => idpath).
Defined.

(* Translation from left *)
Definition translate_fl {M : Magma} (a : M) : Functor M M.
Proof.
  refine (Functor.compose (D := M*M) binary_op _).
  srapply @Build_Functor.
  (* Objects *)
  - exact (fun m => (a, m)).
  (* Morphisms *)
  - intros m n f. exact (identity a, f).
  (* Respect composition *)
  - intros l m n.
    intros f g.
    apply path_prod. apply inverse. apply left_identity. exact idpath. 
  (* Respect identity *)
  - exact (fun _ => idpath).
Defined.
  


Section Monoidal_Category.
  (* Require cancellation law, even if that is not reflected in the name. *)
  Record Symmetric_Monoidal_Category : Type :=
    {smon_magma :> Magma ;
     (* isgroupoid_smon_magma : forall (a b : smon_magma) (f : a --> b), IsIsomorphism f; *)
     e : smon_magma ;
     assoc : forall a b c : smon_magma, (a + b) + c --> a + (b + c);
     iso_assoc : forall a b c : smon_magma, IsIsomorphism (assoc a b c);
     natural_assoc : forall (a b c a' b' c': smon_magma) (f : a-->a') (g : b --> b') (h : c --> c'),
       assoc a' b' c' o ((f +^ g) +^ h) = (f +^ (g +^ h)) o assoc a b c;
     lid : forall a : smon_magma, e + a --> a;
     iso_lid : forall a : smon_magma, IsIsomorphism (lid a);
     natural_lid : forall (a a' : smon_magma) (f : a --> a'),
       lid a' o (1 +^ f) = f o lid a;
     rid : forall a : smon_magma, a + e --> a;
     iso_rid : forall a : smon_magma, IsIsomorphism (rid a);
     natural_rid : forall (a a' : smon_magma) (f : a --> a'),
       rid a' o (f +^ 1) = f o rid a;
     symm : forall a b : smon_magma, a + b -->  b + a;
     natural_sym : forall (a b a' b' : smon_magma) (f : a --> a') (g : b --> b'),
         symm a' b' o (f +^ g) = (g +^ f) o symm a b;
     symm_inv : forall a b : smon_magma, symm a b o symm b a = 1;
     coh_tri : forall a b : smon_magma,
         (1 +^ lid b) o (assoc a e b) = (rid a +^ 1) ;
     coh_pent : forall a b c d : smon_magma,
         (assoc a b (c+d)) o (assoc (a+b) c d)  =
         (1 +^ assoc b c d) o (assoc a (b+c) d) o (assoc a b c +^ 1);
     coh_hex : forall a b c : smon_magma,
         (assoc b c a) o (symm a (b + c)) o (assoc a b c) =
         (1 +^ symm a c) o (assoc b a c) o (symm a b +^ 1)
         
         (* (assoc c a b) o (symm (a+b) c) o assoc a b c = *)
         (* (symm a c +^ 1) o (assoc a c b) o (1 +^ symm b c); (*I am guessing that this is correct*) *)
     (* cancellation : forall (s t a : smon_magma) (f g : s --> t), (f +^ identity a) = (g +^ identity a) -> f = g *)
    }.

  (* Coherence results that are true given the above, but whose proofs are omitted (for now) *)
  Lemma coh_lid_assoc_lid (M : Symmetric_Monoidal_Category) : forall a b : M,
      lid M (a + b) o assoc M (e M) a b = (lid M a +^ 1).
  Admitted.

  

  (*Want to define the category [Sigma] of finite sets and isomorphisms. *)
  Definition isset_Finite (A : Type) :
    Finite A -> IsHSet A.
  Proof.
    intros [m finA]. strip_truncations.
    apply (trunc_equiv' (Fin m) finA^-1).
  Defined.
  
  (*obj Sigma := {A : Type & Finite A}
    morph A B := Equiv (Fin (card A)) (Fin (card B))*)

  (*Definition Sigma_morphism (m n : nat) := Equiv (Fin m) (Fin n).*)

  Definition Sigma_precat : PreCategory.
  Proof.
    srapply (@Build_PreCategory {A : Type & Finite A}
                                (fun A B => Equiv A.1 B.1)).
                                (* (fun A B => Equiv (Fin (@fcard A.1 A.2)) (Fin (@fcard B.1 B.2)))). *)
    - (*Identity*)
      intro m.
      apply equiv_idmap.
    - (*Compose*)
      intros A B C.
      apply equiv_compose'.
    - (*Associativity*)
      intros A B C D.
      intros e f g.
      apply ecompose_ee_e.
    - (*Composing with identity from left*)
      intros D E. intro f.
      apply ecompose_1e.
    - (*Composing with identity from right*)
      intros D E. intro f.
      apply ecompose_e1.
    - intros A B. simpl.
      srapply @istrunc_equiv. apply isset_Finite. exact B.2.
  Defined.

  Instance isgroupoid_preSigma (a b : Sigma_precat) (f : a --> b) : IsIsomorphism f.
  Proof.
    srapply @Build_IsIsomorphism.
    - exact (f^-1%equiv).
    - apply ecompose_Ve.
    - apply ecompose_eV.
  Defined.


  (* This category is univalent *)
  (* Prove this by reducing to univalence in types *)
  (*First: An isomorphism is the same as an equivalence on the underlying type *)
  Definition equiv_isomorphic_Sigma (A B : Sigma_precat) : (A.1 <~> B.1) <~> Isomorphic A B.
  Proof.
    srapply @equiv_adjointify.
    - (*Inverse*)
      intro f. apply (@Build_Isomorphic _ A B f _).
    - (*Underlying map*)
      exact (@morphism_isomorphic _ A B).
    - intro g. apply path_isomorphic. exact idpath.
    - exact (fun _ => idpath).
  Defined.

  Definition idtoiso_is_path_equiv {A B : Sigma_precat} :
    @idtoiso Sigma_precat A B =
    (equiv_isomorphic_Sigma A B) oE (equiv_equiv_path A.1 B.1) oE (equiv_path_sigma_hprop A B)^-1.
  Proof.
    apply path_arrow. 
    intros []. apply path_isomorphic. exact idpath.
  Defined.

  
  Lemma iscategory_Sigma : IsCategory Sigma_precat.
    intros A B.
    rewrite idtoiso_is_path_equiv. exact _.
  Qed.

  Definition Sigma_cat := Build_Category iscategory_Sigma.

  Definition Sigma_coprod : Functor (Sigma_cat*Sigma_cat) Sigma_cat.
  Proof.
    srapply @Build_Functor.
    - (*Map on objects is sum of types*)
      intros [A B].
      exists (A.1 + B.1)%type. apply finite_sum; exact _.2.
    - (*Map on morphisms.*)
      (*Fin respects sum*)
      intros [A B] [C D].
      unfold morphism. simpl.
      intros [f g]. apply (equiv_functor_sum' f g).
    - (*Respects composition*)
      intros [i1 i2] [j1 j2] [k1 k2].
      intros [f1 f2] [g1 g2]. simpl.
      apply path_equiv. apply path_arrow. 
      intros [m | n]; exact idpath.
    - (*Respects identity*)
      intros [i j]. simpl.
      apply path_equiv. apply path_arrow. intros [m | n]; exact idpath.
  Defined.

  (* Ltac reduce_sigma_morphism := intros; apply path_equiv; apply path_arrow; repeat (intros [?m | ]); intros. *)
  
  Definition Sigma : Symmetric_Monoidal_Category.
  Proof.
    srapply (@Build_Symmetric_Monoidal_Category (Build_Magma Sigma_cat Sigma_coprod) 
                                                ( Fin 0 ; finite_fin 0 )).
    - (*Associativity*)
      intros A B C.
      apply equiv_sum_assoc.
    - (* Associativity is natural *)
      intros A B C A' B' C' f g h. apply path_equiv. apply path_arrow.
      intros [[l | m] | n]; exact idpath.
    - (*Left identity*)
      intro a. apply sum_empty_l.
    - (*Left identity is natural*)
      intros A A' f.      
      apply path_equiv. apply path_arrow. intros [[] | n]. exact idpath.
    - (*Right identity*)
      intro a. apply sum_empty_r.
    - (*Right identity is natural*)
      intros A A' f. 
      apply path_equiv. apply path_arrow. intros [n | []]. exact idpath.
    - (*Symmetry*)
      intros A A'.
      apply equiv_sum_symm.
    - (*Symmetry is natural*)
      intros A A' B B' f g.
      apply path_equiv. apply path_arrow. intros [m | n]; exact idpath.
    - (*Symmetry is its own inverse*)
      intros A B.
      apply path_equiv. apply path_arrow. intros [m | n]; exact idpath.
    - (*Coherence triangle*)
      intros A B.
      apply path_equiv. apply path_arrow. intros [[m | []] | n]; exact idpath.
    - (*Coherence pentagon*)
      intros A B C D.
      apply path_equiv. apply path_arrow. repeat (intros [ | m]); intros; exact idpath.
    - (*Coherence hexagon*)
      simpl. intros A B C.
      apply path_equiv. apply path_arrow. repeat (intros [ | m]); intros; exact idpath.
    (* - (* Translations are faithful *) *)
    (*   (* This proof is not natural in A, but this is a proposition so it doesn't matter. . .*) *)
    (*   intros S T A f g H. *)
    (*   apply path_equiv. apply path_arrow. intro s. *)
    (*   set (collapseA := fun ta : T.1 + A.1%type => *)
    (*                       match ta with *)
    (*                       |Datatypes.inl t => t *)
    (*                       |Datatypes.inr _ => f s (*This is an arbitrary choice.*) *)
    (*                       end). *)
    (*   change (f s) with (collapseA ((f +^ 1) (Datatypes.inl s))). *)
    (*   rewrite H. reflexivity. *)
  Defined.

  (* Instance isgroupoid_Sigma (A B : Sigma) (f : A --> B) : IsIsomorphism f := isgroupoid_preSigma A B f.  *)
  
  Lemma faithful_cancellation_Sigma (S T A : Sigma) (f g : S --> T) :
    (f +^ identity A) = (g +^ identity A) -> f = g.
  Proof.
    (* This proof is not natural in A, but this is a proposition so it doesn't matter. . .*)
    intro H.
    apply path_equiv. apply path_arrow. intro s.
    set (collapseA := fun ta : T.1 + A.1%type =>
                        match ta with
                        |Datatypes.inl t => t
                        |Datatypes.inr _ => f s (*This is an arbitrary choice.*)
                        end).
    change (f s) with (collapseA ((f +^ 1) (Datatypes.inl s))).
    rewrite H. reflexivity.
  Qed.    
  
End Monoidal_Category.

(* (* A somewhat stupid tactic that tries to rewrite all the identities *) *)
(* Ltac moncat_rewrite := *)
(*   repeat (repeat rewrite natural_assoc; *)
(*           repeat rewrite natural_lid; *)
(*           repeat rewrite natural_rid; *)
(*           repeat rewrite natural_sym; *)
(*           repeat rewrite symm_inv; *)
(*           repeat rewrite coh_tri; *)
(*           repeat rewrite coh_pent; *)
(*           repeat rewrite coh_hex; *)
(*           repeat rewrite coh_lid_assoc_lid). *)



(* Define the group completion of a symmetric monoidal category *)
Section Group_Completion.
  (* Definition Magma_prod (M N : Magma) : Magma. *)
  (* srapply @Build_Magma. *)
  (* - srapply @Build_Category. *)
  (*   + exact (M*M). *)
  (*   + (* *) *)
  (*     admit. *)
  (* - srapply @Build_Functor. *)
  (*   + intros [[a1 a2] [b1 b2]]. simpl. *)
  (*     exact (a1 + b1, a2 + b2). *)
  (*   + simpl. *)

  Notation "( a , b ) --> ( c , d ) " := (morphism (_ * _) (a, b) (c, d)).
  (* Notation " a ==> b " := (morphism (_ * _) a b) (at level 40). *)
  (* Notation "a +p b" := (Datatypes.fst a + Datatypes.fst b, Datatypes.snd a + Datatypes.snd b) (at level 40). (* Level is just arbitrary. . . *) *)

  (* Assume that M is a symmetric monoidal groupoid with cancellation. *)
  Variable M : Symmetric_Monoidal_Category.
  Variable iscategory_M : IsCategory M.
  Variable isgroupoid_M : forall (a b : M) (f : a --> b), IsIsomorphism f.
  Variable cancellation_M : forall (s t a : M) (f g : s --> t), (f +^ identity a) = (g +^ identity a) -> f = g.
  
  (* Definition isgroupoid (M : Symmetric_Monoidal_Category) : Type := *)
  (*   forall (a b : M) (f : a --> b), IsIsomorphism f. *)
  (* Definition monoid_cancellation (M : Symmetric_Monoidal_Category) : Type := *)
  (*   forall (s t a : M) (f g : s --> t), *)
  (*     (f +^ identity a) = (g +^ identity a) -> f = g. *)

  Instance isgroupoid_prod : forall (a b : (M*M)%category) (f : a --> b), IsIsomorphism f.
  Proof.
    intros [a1 a2] [b1 b2]. intros [f1 f2].
    srapply @Build_IsIsomorphism; simpl.
    - exact (f1^-1, f2^-1).
    - abstract (repeat rewrite left_inverse; reflexivity). 
    - abstract (repeat rewrite right_inverse; reflexivity).
  Defined.

  (* The diagonal functor *)
  Definition diag {C : PreCategory} : Functor C (C*C).
  Proof.
    srapply @Build_Functor.
    (* Map on objects *)
    - exact (fun c => (c,c)).
    (* On morphisms *)
    - intros c1 c2 f. exact (f, f).
    (* Respect composition *) - reflexivity.
    (* Respect identity. *)   - reflexivity.
  Defined.
  
  (* The induced sum on [M*M] *)
  (*    [(a1, a2) + (b1, b2) = (a1+b1, a2 + b2)*)
  Definition sum2 : Functor ((M*M) * (M*M)) (M*M).
  Proof.
    refine (Functor.compose (pair (@binary_op M) (@binary_op M) ) _).
    (* Build a functor swapping 2nd and 3rd component *)
    (* Use associativity to get to where we can swap. *)
    refine (Functor.compose (ProductLaws.Associativity.functor M M (M*M)) _).
    refine (Functor.compose (pair (Functor.identity M) (ProductLaws.Associativity.inverse M M M)) _).
    (* Now we can swap *)
    refine (Functor.compose (pair (Functor.identity M) (pair (ProductLaws.Swap.functor M M) (Functor.identity M) )) _).
    (* Use associativity to get back again *)
    refine (Functor.compose (pair (Functor.identity M) (ProductLaws.Associativity.functor M M M)) _).
    exact (ProductLaws.Associativity.inverse M M (M*M)).
  Defined.

  (* Notation for sum2 on morphisms *)
  Notation "f +^+ g" := (sum2 _1 (pair_1 f g)) (at level 40).

  (* (* Sum of pairs *) *)
  (* Notation "a +p b" := (sum2 (a, b)) (at level 40). *)

  Definition assoc_sum2 (a b c : M*M) : sum2 (sum2 (a,  b), c) --> sum2 (a, (sum2 (b,  c))).
  Proof.
    split; apply assoc.
  Defined.

  (* (* (diag + 1) *) *)
  (* Definition act_on_prod : Functor (M*(M*M)) (M*M) := sum2 o (pair diag (Identity.identity _))%functor.   *)

  (* (* Just to remind me what [act_on_prod] does on objects *) *)
  (* Lemma what_is_act_on_prod : forall (s a1 a2 : M), act_on_prod (s, (a1, a2)) = (s + a1, s + a2). *)
  (*   reflexivity. *)
  (* Qed.  *)
  
  (* Definition act_on_prod (s : M) : Functor (M*M) (M*M). *)
  (* Proof. *)
  (*   refine (Functor.compose sum2 _). *)
  (*   apply Functor.prod. *)
  (*   (* The constant functor (s,s) *) *)
  (*   - srapply @Build_Functor. *)
  (*     + exact (const (s,s)). *)
  (*     + intros. exact (1,1). *)
  (*     + intros. rewrite left_identity. reflexivity. *)
  (*     + reflexivity. *)
  (*   - apply Identity.identity. *)
  (* Defined.   *)

  Definition group_completion_morph :
    (M*M)%category -> (M*M)%category -> Type.
  Proof.
    intros a b. (* [a_p a_m] [b_p b_m]. *)
    exact {s : M & sum2 (diag s, a) --> b}.   (* (s + a_p, s + a_m) --> (b_p, b_m)}. *)
  Defined.



  (* Must I start with everything reduced for the notation to be readable? *)
  Definition equiv_group_completion_morph (a b : M*M) (f g : group_completion_morph a b) :
    f = g <~> {alpha : f.1 --> g.1 & f.2 = g.2 o ((diag _1 alpha) +^+ 1)}.
  (* (act_on_prod _1 (pair_1 alpha 1))}. *)
  (* (pair_1 (alpha +^ 1) (alpha +^ 1))}. *)
  Proof.
    destruct a as [a1 a2]. destruct b as [b1 b2]. unfold group_completion_morph in f, g.
    (* destruct f as [t f]. destruct g as [s g]. simpl. *) (* simpl in f1, f2, g1, g2. *)
    set (F := Functor.prod (translate_fr a1) (translate_fr a2)).
    refine (_ oE equiv_path_sigma (fun s : M => F s --> (b1, b2)) _ _).
    transitivity {p : f.1 = g.1 & f.2 = g.2 o (F _1 (idtoiso M p))}.
    { apply equiv_functor_sigma_id. intro p.
      destruct f as [s f]. destruct g as [t g].
      simpl in p. destruct p. simpl.
      destruct f as [f1 f2]. destruct g as [g1 g2]. simpl in f1, f2, g1, g2. simpl.
      apply equiv_concat_r.
      apply path_prod; simpl; apply inverse; refine (_ @ right_identity M _ _ _);
        refine (ap (fun g => _ o g) _); apply identity_of. }
    (*   transitivity (f.2 o (F _1 (idtoiso M p ))^-1 = g.2). *)
    (*   - apply equiv_concat_l. *)
    (*     apply iso_moveR_pV. *)
    (*     apply (transport_morphism_Fl' F p f.2). *)
    (*   (* Can't find this specific equivalence implemented. . . *) *)
    (*   - srapply @equiv_adjointify. apply iso_moveL_pM. apply iso_moveR_pV. *)
    (*     intro q. apply (trunc_morphism (M*M)). *)
    (*     intro q. apply (trunc_morphism (M*M)). }  *)
    transitivity ({alpha : f.1 <~=~> g.1 & f.2 = g.2 o pair_1 (morphism_isomorphic +^ 1) (morphism_isomorphic +^ 1)}).
    { srapply @equiv_functor_sigma'.
      - exact (BuildEquiv _ _(idtoiso M (y:=g.1)) _).
      - reflexivity.
    } clear F.
    srapply @equiv_functor_sigma'.
    - srapply @equiv_adjointify.
      + intro e. exact morphism_isomorphic.
      + intro e. refine (Build_Isomorphic (isgroupoid_M _ _ e)).
      + intro e. exact idpath.
      + intro e. apply path_isomorphic. exact idpath.
    - reflexivity.
  Defined.

  
  Lemma path_group_completion_morph (a b : M*M) (f g : group_completion_morph a b) (alpha : f.1 --> g.1):
    f.2 = g.2 o ((diag _1 alpha) +^+ 1) -> f = g. (* (pair_1 (alpha +^ 1) (alpha +^ 1)) *)
  Proof.
    intro H.
    exact ((equiv_group_completion_morph a b f g)^-1 (alpha; H))%equiv.
  Qed.
  
  (* (* The following two maps may or may not be equal to the underlying maps of [equiv_group_completion_morph] *) *)
  (* Definition path_to_sigma {M : Symmetric_Monoidal_Category} (a b : M*M) *)
  (*            (f g : group_completion_morph M a b) : *)
  (*   f = g -> {alpha : f.1 --> g.1 & f.2 = g.2 o (pair_1 (alpha +^ 1) (alpha +^ 1))}. *)
  (* Proof. *)
  (*   intro p. *)
  (*   destruct p. *)
  (*   destruct a as [a1 a2]. destruct b as [b1 b2]. *)
  (*   destruct f as [s [f1 f2]]. simpl. *)
  (*   exists (identity s). *)
  (*   apply inverse. *)
  (*   refine (_ @ right_identity (M*M) _ _ (f1, f2)). *)
  (*   apply path_prod; simpl. *)
  (*   apply (ap (fun g => f1 o g)). apply sum_idmap. *)
  (*   apply (ap (fun g => f2 o g)). apply sum_idmap. *)
  (* Defined. *)

  (* Definition path_grp_compl_morph {M : Symmetric_Monoidal_Category} (a b : M*M) *)
  (*            (f g : group_completion_morph M a b) : *)
  (*   {alpha : f.1 --> g.1 & f.2 = g.2 o (pair_1 (alpha +^ 1) (alpha +^ 1))} -> f = g. *)
  (* Proof. *)
  (*   destruct f as [s  f]. destruct g as [t g]. destruct a as [a1 a2]. destruct b as [b1 b2]. simpl. *)
  (*   intros [alpha H]. *)
  (*   srapply @path_sigma; simpl. *)
  (*   - apply (isotoid M _ _). exact (Build_Isomorphic (isgroupoid_smon_magma M s t alpha )). *)
  (*   - (* refine (transport_morphism_Fl (translate_fr ) ((isotoid M s t) *) *)
  (*     (*           {| morphism_isomorphic := alpha; isisomorphism_isomorphic := isgroupoid_smon_magma M s t alpha |}) f *) *)
  (*     (*                               @ _). *) admit. Abort. *)

  

  Instance isset_group_completion_morph (a b : M*M) :
    IsHSet (group_completion_morph a b).
  Proof.
    intros f g. change (IsTrunc_internal (-1)) with (IsTrunc (-1)).
    apply (trunc_equiv' {alpha : f.1 --> g.1 & f.2 = g.2 o (pair_1 (alpha +^ 1) (alpha +^ 1))}).
     refine (equiv_inverse (equiv_group_completion_morph a b f g)).
    destruct a as [a1 a2]. destruct b as [b1 b2].
    destruct f as [s f]. destruct g as [t g]. (* simpl in f1, f2, g1, g2. *) simpl.
    apply trunc_sigma'.
    - intro alpha. exact _.
    - intros [e H] [e' H']. simpl in e, H, e', H'. simpl.
      apply contr_inhabited_hprop. exact _. simpl.
      srapply @cancellation_M. exact a1.
      destruct (H'^). clear H'.
      destruct g as [g g']. simpl in g, g'. simpl in H.
      pose proof (ap Datatypes.fst H) as fstH. simpl in fstH. clear H. clear g'.
      srefine ((iso_compose_V_pp (isgroupoid_M _ _ g) _)^ @ _ @ iso_compose_V_pp (isgroupoid_M _ _ g) _).
      rewrite fstH. exact idpath.
  Qed.

  Definition group_completion_id (m : M*M) : group_completion_morph m m.
  Proof.
  - exists (e M). exact (lid M (fst m), lid M (snd m)).
  Defined.  
  
  Definition group_completion_compose (a b c : M*M)
             (f : group_completion_morph b c) (g : group_completion_morph a b):
    (* group_completion_morph b c -> group_completion_morph a b -> *)
    group_completion_morph a c.
  Proof.
    (* destruct a as [a1 a2]. destruct b as [b1 b2]. destruct c as [c1 c2]. *)
    (* intros [s f] [t [g1 g2]]. simpl in f, g1, g2. *)
    (* intros [s f] [t g]. *)
    exists (f.1 + g.1).    
    refine (f.2 o _).
    change (diag (f.1 + g.1)) with (sum2 ((f.1, f.1), (g.1, g.1))).    
    refine (_ o assoc_sum2 _ _ _).
    apply (morphism_of sum2). exact (1, g.2).
  Defined.

  (* Some auxiliary lemmas *)
  Lemma comp_of_addid_fl : forall (a b c s : M) (f : a --> b) (g : b --> c),
      (identity s) +^ (g o f) = (identity s +^ g) o (identity s +^ f).
  Proof.
    intros. rewrite <- composition_of. simpl. rewrite left_identity. reflexivity.
  Qed.

  Lemma comp_of_addid_fr : forall (a b c s : M) (f : a --> b) (g : b --> c),
      (g o f) +^ (identity s) = (g +^ identity s) o (f +^ identity s).
  Proof.
    intros. rewrite <- composition_of. simpl. rewrite left_identity. reflexivity.
  Qed.  
  
  Lemma comp_of_addid_fl_2 : forall (a b c s : (M*M)%category) (f : a --> b) (g : b --> c),
      (identity s) +^+ (g o f) = (identity s +^+ g) o (identity s +^+ f).
  Proof.
    intros [a1 a2] [b1 b2] [c1 c2] [s1 s2].
    intros [f1 f2] [g1 g2]. simpl. repeat rewrite <- comp_of_addid_fl. reflexivity.
  Qed.

  Lemma associative_group_completion :
    forall (a b c d : (M*M)%category)
           (f : group_completion_morph a b) (g : group_completion_morph b c) (h : group_completion_morph c d),
      group_completion_compose a b d (group_completion_compose b c d h g) f =
      group_completion_compose a c d h (group_completion_compose a b c g f).
  Proof.
    intros a b c d.
    (* intros [r f] [s g] [t h]. *) intros f g h.
    (* intros [a1 a2] [b1 b2] [c1 c2] [d1 d2]. *)
    (* intros [r [f1 f2]] [s [g1 g2]] [t [h1 h2]]. simpl in f1, f2, g1, g2, h1, h2. *)
    srapply @path_group_completion_morph. simpl.
    - exact (assoc M h.1 g.1 f.1). 
    - change (group_completion_compose a b d (group_completion_compose b c d h g) f).2 with
      ((h.2 o (1 +^+ g.2 o assoc_sum2 (h.1, h.1) (g.1, g.1) b)) o
              (1 +^+ f.2 o assoc_sum2 (h.1 + g.1, h.1 + g.1) (f.1, f.1) a)).
      change (group_completion_compose a c d h (group_completion_compose a b c g f)).2 with
      (h.2 o (1 +^+ (g.2 o (1 +^+ f.2 o assoc_sum2 (g.1, g.1) (f.1, f.1) a)) o
                   assoc_sum2 (h.1, h.1) (g.1 + f.1, g.1 + f.1) a)).
      repeat rewrite associativity.
      apply (ap (fun m => h.2 o m)).       
      repeat rewrite comp_of_addid_fl_2.
      repeat rewrite associativity.
      refine (ap (fun m => (1 +^+ g.2)  o m) _).
      (* The nice way to do this is to show that M acts on M*M coherently, but we do it quick and ugly. *)
      destruct a as [a1 a2]. destruct b as [b1 b2]. destruct c as [c1 c2].
      destruct f as [r [f1 f2]]. destruct g as [s [g1 g2]]. destruct h as [t [h1 h2]].
      simpl in f1, f2, g1, g2, h1, h2.
      transitivity (pair_1 ((1 +^ (1 +^ f1)) o (assoc M t s (r + a1) o assoc M (t + s) r a1))
                           ((1 +^ (1 +^ f2)) o (assoc M t s (r + a2) o assoc M (t + s) r a2))); simpl; unfold pair_1.
      { rewrite <- sum_idmap. repeat rewrite <- associativity. repeat rewrite natural_assoc. reflexivity. }
      { unfold pair_1. repeat rewrite coh_pent. repeat rewrite <- associativity. reflexivity. }
  Qed.

  Lemma left_id_group_completion : 
    forall (a b : (M * M)%category) (f : group_completion_morph a b),
      group_completion_compose a b b (group_completion_id b) f = f.
  Proof.
    intros [a1 a2] [b1 b2]. intros [s [f1 f2]].
    srapply @path_group_completion_morph.
    - simpl. apply lid.
    - simpl. repeat rewrite <- associativity.
      repeat rewrite natural_lid. repeat rewrite associativity.
      repeat rewrite coh_lid_assoc_lid.  reflexivity.
  Qed.

  Lemma right_id_group_completion :
    forall (a b : (M * M)%category) (f : group_completion_morph a b),
      group_completion_compose a a b f (group_completion_id a) = f.
  Proof.
    intros [a1 a2] [b1 b2]. intros [s [f1 f2]].
    srapply @path_group_completion_morph.
    - simpl. apply rid.
    - simpl. repeat rewrite coh_tri. reflexivity.
  Qed.
      

  (* The object [(a, b)] represents the difference [a-b]. *)
  Definition group_completion_cat : PreCategory :=
    Build_PreCategory (group_completion_morph) group_completion_id
                      group_completion_compose associative_group_completion
                      left_id_group_completion
                      right_id_group_completion _.

  (* The functor sending object [a] to [a-0] *)
  Definition to_group_completion : Functor M group_completion_cat.
  Proof.
    srapply @Build_Functor; repeat change Core.object with object.
    (* Map on objects *)
    - intro a. exact (a, e M).
    (* Map on arrows *)
    - intros a b f. simpl.
      exists (e M). split; simpl.
      exact (f o lid M a). apply lid.
    (* Respects composition *)
    - intros a b c f g. simpl.
      srapply @path_group_completion_morph.
      + simpl. exact (lid M (e M))^-1.
      + simpl. (* Follows from coherence, but here is a proof. *)
        apply path_prod; simpl.
        * repeat rewrite associativity.
          refine (ap (fun h => g o h) _).
          repeat rewrite <- associativity.
          rewrite natural_lid. repeat rewrite associativity.
          refine (ap (fun h => f o h) _).
          transitivity (lid M a o 1). rewrite right_identity. reflexivity.
          refine (ap (fun h => (lid M a) o h) _).
          repeat rewrite <- associativity.
          rewrite coh_lid_assoc_lid.
          rewrite <- composition_of. simpl.
          rewrite right_inverse. rewrite right_identity. rewrite identity_of. reflexivity.
        * (* rewrite natural_lid. *)
          repeat rewrite <- associativity. rewrite natural_lid. repeat rewrite associativity.
          transitivity (lid M (e M) o 1). rewrite right_identity. reflexivity.
          refine (ap (fun h => (lid M (e M) o h)) _). repeat rewrite <- associativity.
          rewrite coh_lid_assoc_lid. rewrite <- composition_of. simpl. rewrite right_inverse.
          rewrite right_identity. rewrite identity_of. reflexivity.
    (* Respects identity  *)
    - intro a. simpl. unfold group_completion_id. simpl. rewrite left_identity. reflexivity.
  Defined.      

  Definition group_completion_sum : Functor (group_completion_cat * group_completion_cat) group_completion_cat.
  Proof.
    srapply @Build_Functor; change Core.object with object.
    (* Map on objects *)
    - (* [a1 - a2] and [b1 - b2] goes to [(a1 + a2) - (b1 + b2) *)
      apply sum2.
    (* Map on morphisms *)
    - 
      intros [a a'] [b b']. intros [[s f] [s' f']]. simpl in a, a', b, b'.
      unfold Datatypes.fst in f. unfold Datatypes.snd in f'.
      (* intros [[s [f1 f2]] [t [g1 g2]]]. *)
      exists (s + s').
      refine (sum2 _1 (pair_1 f f') o _). change (Core.object_of sum2) with (object_of sum2).
      (* change ((sum2 o (diag, 1))%functor (s + t, sum2 (a, b))) with (sum2 (diag (s + t), sum2 (a, b))). *)
      (* change (Core.object_of sum2 ((sum2 o (diag, 1))%functor (s, a), (sum2 o (diag, 1))%functor (t, b))) with *)
      (*        (sum2 (sum2 (diag s, a), sum2 (diag t, b))). *)
      change (diag (s + s')) with (sum2 (diag s, diag s')).
      refine ((assoc_sum2 _ _ _)^-1  o _ o assoc_sum2 _ _ _).
      refine (1 +^+ _).
      refine (assoc_sum2 _ _ _ o _ o (assoc_sum2 _ _ _)^-1).
      refine (_ +^+ 1). 
      (* It is more general that the product inherits symmetry, but. . . *)
      exact (pair_1 (symm M _ _) (symm M _ _)).
    (* Respect composition *)
    - (* I have half a proof on paper (ignoring associativity), but I do not want to implement it for now.*)
      admit.
      (* simpl. *)
      (* (* intros [a a'] [b b'] [c c']. *) *)
      (* intros [[a_p a_n] [a_p' a_n']] [[b_p b_n] [b_p' b_n']] [[c_p c_n] [c_p' c_n']]. *)
      (* (* intros [[s f] [s' f']]  [[t g] [t' g']]. *) *)
      (* intros [[s [f_p f_n]] [s' [f_p' f_n']]]  [[t [g_p g_n]] [t' [g_p' g_n']]]. *)
      (* simpl in f_p, f_n, f_p', f_n', g_p, g_n, g_p', g_n'. simpl. unfold group_completion_compose. simpl. *)
      (* srapply @path_group_completion_morph. *)
      (* + simpl. *)
      (*   refine ((assoc M _ _ _)^-1 o _ o assoc M _ _ _). *)
      (*   refine (1 +^ _). *)
      (*   refine (assoc M _ _ _ o _ o (assoc M _ _ _)^-1). *)
      (*   refine (_ +^ 1). *)
      (*   apply symm. *)
      (* + apply path_prod ; simpl. *)
      (*   * *)
      (*     (* Don't know why [rewrite <- (composition_of binary_op)] doesn't work directly. . . *) *)
      (*     assert (comp_of_binary_op : forall (a a' b b' c c' : M) (f : b --> c) (f' : b' --> c') (g : a --> b) (g' : a' --> b'), *)
      (*                (f o g) +^ (f' o g') = (f +^ f') o (g +^ g')). *)
      (*     { intros. rewrite <- (composition_of binary_op). simpl. reflexivity. } *)
      (*     rewrite comp_of_binary_op. repeat rewrite associativity. *)
      (*     refine (ap (fun f => (g_p +^ g_p') o f) _). *)
      (*     rewrite comp_of_binary_op.  *)
      (*     repeat rewrite comp_of_addid_fl. repeat rewrite comp_of_addid_fr. repeat rewrite associativity. *)
      (*     repeat rewrite <- comp_of_addid_fl. admit. *)
      (*     * admit. *)
    (* Respect identity *)
    - simpl. intros [[a a'] [b b']]. simpl.
      srapply @path_group_completion_morph.
      + simpl. apply lid.
      + simpl. repeat rewrite associativity. admit. (* Coherence *)
  Admitted.

  (* TODO: Make a section with assumptions that follow from coherence, at use it liberally. *)

  Definition group_completion_moncat : Symmetric_Monoidal_Category.
    srapply (@Build_Symmetric_Monoidal_Category (Build_Magma group_completion_cat group_completion_sum)
            (e M, e M)).
           
          
        
        
      
      
  
End Group_Completion.  
 