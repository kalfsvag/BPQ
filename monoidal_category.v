Require Import HoTT.
Require Import UnivalenceAxiom.
Load stuff.

Definition ap011_pp_pp {A B C : Type} (f : A -> B -> C) {x x' x'' : A} {y y' y'' : B}
           (p : x = x') (p' : x' = x'') (q : y = y') (q' : y' = y'') :
  ap011 f (p @ p') (q @ q') = ap011 f p q @ ap011 f p' q'.
Proof.
  by path_induction.
  (* destruct p, p', q, q'. exact idpath. *)
Qed.

Section Finite.
  (*Fin respects sum*)

  Definition Fin_resp_sum (m n : nat) : Fin (m + n) <~> (Fin m) + (Fin n).
  Proof.
    induction m.
    - (*m is 0*)
      apply equiv_inverse.
      apply (sum_empty_l (Fin n)).
    - simpl.
      refine (_ oE (equiv_functor_sum_r IHm)).
      refine ((equiv_sum_assoc (Fin m) Unit (Fin n))^-1 oE _ oE equiv_sum_assoc (Fin m) (Fin n) Unit).
      apply equiv_functor_sum_l.
      apply equiv_sum_symm.
  Defined.

  Definition trivial_equiv_fin (m n : nat) : m = n -> (Fin m) <~> (Fin n).
  Proof.
    intro p. induction p. exact equiv_idmap.
  Defined.

  (* Definition trivial_is_idmap {m : nat} : trivial_equiv_fin m m idpath  *)
End Finite.



Section Equiv.
  (*Cancellation of equivalences*)
  (*Is there anything to get from saying that g and h are equicalences?*)

  

  (* Definition ewhiskerL {A B C : Type} (f : A -> B) {isequiv_f : IsEquiv f} (g h : B -> C) : *)
  (*   g = h -> g o f = h o f. *)
  (* Proof. *)
  (*   intro p. *)
  (*   apply path_arrow. *)
  (*   intro a. *)
  (*   refine (ap (g o f) (eissect f a)^ @ _ @ ap (h o f) (eissect f a)). *)
     
  
  Definition ecancelL {A B C : Type} (f : A -> B) {isequiv_f : IsEquiv f} (g h : B -> C) :
    g o f = h o f -> g = h.
  Proof.
    intro p.
    apply path_arrow.
    intro b.
    refine (ap g (eisretr f b)^ @ _ @ ap h (eisretr f b)).
    exact (ap10 p (f^-1 b)).
  Defined.

  Definition ecancelR {A B C : Type} (f g : A -> B) (h : B -> C) {isequiv_h : IsEquiv h} :
    h o f = h o g -> f = g.
  Proof.
    intro p.
    apply path_arrow.
    intro a.
    refine ((eissect h (f a))^ @ _ @ (eissect h (g a))).
    exact (ap (h^-1) (ap10 p a)).
  Defined.

  Definition equiv_functor_sum_1 {A B : Type} : @equiv_idmap A +E @equiv_idmap B = equiv_idmap.
  Proof.
    apply path_equiv. apply path_arrow. intros [a | b]; reflexivity.
  Defined.


End Equiv.

        
(*Defining the type of monoidal 1-Types (this corresponds to a monoidal category*)
Section Monoidal_1Type.
  Definition associative {A : Type}  (m : A->A->A) := forall a b c : A, m a (m b c) = m (m a b) c.
  Definition left_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m e a = a.
  Definition right_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a.

  Definition left_cancellation {A : Type} (m : A->A->A) :=
    forall a b c : A, m a b = m a c -> b = c .
  Definition right_cancellation {A : Type} (m : A->A->A) :=
    forall a b c : A, m a b = m c b -> a = c .
  
  
  (* Definition left_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) := *)
  (*   forall a : A, m (inv a) a = e. *)
  (* Definition right_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) := *)
  (*   forall a : A, m a (inv a) = e. *)
  
  Definition coherence_triangle {A : Type} {m : A -> A -> A} {e : A}
             (assoc : associative m) (lid : left_identity m e) (rid : right_identity m e) :=
    forall a b : A,
      assoc a e b @ ap (fun c => m c b) (rid a) = ap (m a) (lid b).

  Definition coherence_pentagram {A : Type} {m : A -> A -> A} (assoc : associative m) :=
    forall a b c d : A,
      assoc a b (m c d) @ assoc (m a b) c d =
      ap (m a) (assoc b c d) @ assoc a (m b c) d @ ap (fun f => m f d) (assoc a b c).


  Record Monoidal_1Type : Type := { mon_type :> Type;
                                    mon_istrunc : IsTrunc 1 mon_type;
                                    mon_mult  : mon_type->mon_type->mon_type;
                                    mon_id : mon_type;
                                    mon_assoc : associative mon_mult;
                                    mon_lid : left_identity mon_mult mon_id ;
                                    mon_rid : right_identity mon_mult mon_id ;
                                    mon_triangle : coherence_triangle mon_assoc mon_lid mon_rid ;
                                    mon_pentagram : coherence_pentagram mon_assoc
                                  }.

  (*Makes mon_istrunc an implicit argument*)
  Global Arguments
         Build_Monoidal_1Type mon_type {mon_istrunc} mon_mult mon_id mon_assoc mon_lid mon_rid
         mon_triangle mon_pentagram.

  (* Unnecessary, easier with [mon_type :> Type] *)
  (*  Coercion mon_type : Monoidal_1Type >-> Sortclass. *)
  Global Arguments mon_mult {m} m1 m2.
  Global Arguments mon_assoc {m} {a} {b} {c}.
  Global Arguments mon_lid {m} a.
  Global Arguments mon_rid {m} a.


  Notation "a + b" := (mon_mult a b) : monoid_scope.


  (*Todo: Define symmetric monoidal category (check coherence criteria)*)
  Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a.



(*Defining the monoidal 1-type of finite sets and isomorphisms*)
Section iFin_1Type.
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Local Notation "'iFin'" := { S : Type & Finite S }.

  (*Finite types are sets *)
  Definition isset_Fin (n : nat) : IsHSet (Fin n).
  Proof.
    induction n.
    - exact _.
    - apply hset_sum.
  Defined.

  Definition isset_Finite (A : Type) :
    Finite A -> IsHSet A.
  Proof.
    intros [m finA]. strip_truncations.
    apply (trunc_equiv' (Fin m) finA^-1).
  Defined.
    
  (*ishprop_finite*)
  (*path_sigma_hprop*)
  (*Could also go via [istrunc_trunctype] . . .*)
  Definition istrunc_iFin : IsTrunc 1 iFin.
  Proof.
    apply trunc_sigma'.
    - exact (fun a => _).
    - intros A B.
      srapply @istrunc_paths_Type.
      apply isset_Finite. exact B.2.
  Defined.

  (*For convinience: Any type of 2-paths in sigma is thus an hprop.*)
  Instance isprop_2path_iFin {S1 S2 : iFin} {p1 p2 : S1 = S2} : IsHProp (p1 = p2) :=
    istrunc_iFin S1 S2 p1 p2.
    
  (*The cardinal of the finite set*)
  Definition cardinal (S : iFin) : nat := @fcard S.1 S.2.

  (*Canonical objects in iFin*)
  Local Notation "[ n ]" := ( Fin n ; finite_fin n ).


  (*Holds by definition: [cardinal [n] = n]*)

  (*Every object is canonical*)
  Lemma canonical_iFin (S : iFin) : merely (S = [cardinal S]).
  Proof.
    refine (Trunc_rec (n:=-1) (A := ( S.1 <~> Fin (fcard S.1))) _ _).
    - intro e.
      apply tr.
      apply path_sigma_hprop.
      exact (path_universe e). 
    - apply merely_equiv_fin.
  Defined.

  (*The monoidal structure on iFin*)
  Definition plus_sigma : iFin-> iFin -> iFin.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (S1 + S2 ; finite_sum _ _)%type.
  Defined.

  Local Notation "S1 + S2" := (plus_sigma S1 S2).

  (*The canonical objects respect sum*)
  Definition sum_canonical (m n : nat) : [m + n]%nat = [m] + [n].
  Proof.
    apply path_sigma_hprop. simpl.
    induction m. simpl.
    apply (path_universe (sum_empty_l (Fin n))^-1).
    simpl.
    rewrite IHm.
    rewrite (path_universe (equiv_sum_assoc (Fin m) (Fin n) Unit)).
    rewrite (path_universe (equiv_sum_assoc (Fin m) Unit (Fin n))).
    rewrite (path_universe (equiv_sum_symm (Fin n) Unit)). reflexivity.
  Qed.


  Definition iFin_assoc : associative plus_sigma.
  Proof.
    intros S1 S2 S3.
    refine (path_sigma_hprop _ _ _).
    srapply @path_universe.
    apply equiv_sum_assoc. exact _.
  Defined.

  (*If the goal is truncated, add this as a hypothesis. (Can speed things up)*)
  Ltac trunc_goal n :=
    match goal with
        | [ |- ?g] => assert (istrunc_goal : IsTrunc n g) by (exact _)
    end.
  
  
  Ltac reduce_iFin :=
    repeat match goal with
             | [S : iFin |- _] => trunc_rewrite (canonical_iFin S);
                                  destruct S as [S [?n H]];
                                  unfold cardinal; cbn; clear H; clear S
           end.

  Ltac simple_reduce_iFin S :=
    trunc_rewrite (canonical_iFin S);
    destruct S as [S [?n H]];
    unfold cardinal; cbn; clear H; clear S.
    

  (*A proof that sigma is merely associative, just using associativity of natural numbers*)
  Definition merely_iFin_assoc : forall S1 S2 S3 : iFin, merely (S1 + (S2 + S3) = (S1 + S2) + S3).
  Proof.
    intros [S1 [n1 fin1]] [S2 [n2 fin2]] [S3 [n3 fin3]].
    (* strip_truncations. *)
    apply tr.
    refine (path_sigma_hprop _ _ _). simpl.
    apply (path_universe (equiv_sum_assoc S1 S2 S3)^-1).
  Defined.
  
  Definition iFin_lid : left_identity plus_sigma ([0]).
  Proof.
    intro S.
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_l S.1)).
  Defined.

  Definition iFin_rid : right_identity plus_sigma ([0]).
  Proof.
    intro S.
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_r S.1)).
  Defined.

  Definition iFin_symmetric : symmetric plus_sigma. 
  Proof.
    intros S1 S2.
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (equiv_sum_symm S1.1 S2.1)).
  Defined.

  (**A few lemmas proving that [cardinal : nat -> iFin] preserves the monoidal structure **)
  (*[cardinal] respects sum*)
  Definition sum_cardinal (S1 S2 : iFin) : cardinal (S1 + S2) = (cardinal S1 + cardinal S2)%nat.
  Proof.
    destruct S1 as [S1 fin1].
    destruct S2 as [S2 fin2].
    apply fcard_sum.
  Defined.

  (*[cardinal] respects associativity*)
  Lemma assoc_cardinal (S1 S2 S3 : iFin) :
    ap cardinal (iFin_assoc S1 S2 S3) @ sum_cardinal (S1 + S2) S3 @
       ap (fun n => (n + (cardinal S3))%nat) (sum_cardinal S1 S2)  =
    sum_cardinal S1 (S2 + S3) @ ap (fun n => ((cardinal S1) + n)%nat) (sum_cardinal S2 S3) @
                 plus_assoc (cardinal S1) (cardinal S2) (cardinal S3).
  Proof.
    destruct S1 as [S1 [n1 fin1]]. destruct S2 as [S2 [n2 fin2]]. destruct S3 as [S3 [n3 fin3]].
    strip_truncations.
    
    (* simple_reduce_iFin S1. simple_reduce_iFin S2. simple_reduce_iFin S3. *)
    (* unfold iFin_assoc. simpl. *)
    (* rewrite (ap_compose (fun S : iFin => S.1) fcard). *)
    
    (* induction n1. *)
    (* simpl. rewrite ap_idmap. rewrite concat_p1. *)
    (* unfold iFin_assoc.  *)
    
    
    (* - unfold plus_assoc. simpl. *)
    
    (* unfold cardinal. unfold fcard. cbn. unfold sum_cardinal. unfold iFin_assoc. simpl. *)
  Abort.

  
  (*TODO: How [cardinal] respects associativity and identity proofs *)
  Definition iFin_triangle : coherence_triangle iFin_assoc iFin_lid iFin_rid.
  Proof.
    intros S1 S2.
    trunc_rewrite (canonical_iFin S1). trunc_rewrite (canonical_iFin S2).
    unfold iFin_assoc.
    simpl.
    (*This was messy.*) Abort.

  (*Definition iFin_pentagram : coherence_pentagram iFin_triangle.*)

  Definition iFin_lcancel : forall S1 S2 S3 : iFin, S1 + S2 = S1 + S3 -> merely (S2 = S3).
  Proof.
    intros S1 S2 S3.
    intro pth.
    trunc_rewrite (canonical_iFin S2).
    trunc_rewrite (canonical_iFin S3).
    apply tr. apply (ap (fun n : nat => [n])).
    apply (nat_plus_cancelL (cardinal S1)).
    refine ((sum_cardinal S1 S2)^ @ _ @ sum_cardinal S1 S3).
    exact (ap cardinal pth).
  Defined.

  Definition sigma_minus (A : iFin) (m n : nat) :
    A + [m] = [n] -> merely (A = [nat_minus m n]).
  Proof.
    intro p.
    pose proof (canonical_iFin A) as q.
    revert q.
    apply (Trunc_rec (A:= A = [cardinal A])). intro q. rewrite q. rewrite q in p. clear q.
    destruct A as [A [l H]].
    unfold cardinal in p. simpl in p.
    unfold cardinal. simpl.
    apply tr.
    induction m, n.
    (* - simpl. simpl in p. *)
    (* induction m; simpl. *)
    (* - refine (_ @ p). *)
    (*   apply (iFin_rid [l])^ . *)
    (* - induction n. *)
    (*   +  *)
  Abort.
    
          
    
    

  Definition unique_choice_groupcompletion_arrow (m n : nat) :
    {A : iFin & A + [m] = [n]} -> Trunc 0 {A : iFin & A + [m] = [n]}.
  Proof.
    intros [A p].
    (* pose proof (iFin_lcancel  *)

    
    (* apply trunc_sigma'. *)
    (* - intro A. apply (istrunc_iFin (A + [m]) [n]). *)
    (* - intros [A p] [B q]. simpl. *)
    (*   unfold IsHProp. unfold IsTrunc_internal. *)
    (*   intros p1 q1. *)
    (*   srapply @BuildContr. *)
    (*   destruct q1. *)
    (*   reduce_iFin. *)
    Abort.  
  

End iFin_1Type.

Section Monoidal_Category.
  Require Import Functor Category.
  Require Import NaturalTransformation.
  (*These notations are defined elsewhere, but I do not know how to import it.*)
  Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
  Notation "F '_0' x" := (object_of F x) (at level 10, no associativity, only parsing) : object_scope.
  Notation "F '_1' m" := (morphism_of F m) (at level 10, no associativity) : morphism_scope.
  Open Scope category_scope.
  Open Scope morphism_scope.

  
  
  (*Another strategy to define monoidal categories*)
  Record Magma : Type :=
    { magma_cat :> PreCategory; binary_op : Functor (magma_cat*magma_cat) magma_cat }.
  Arguments binary_op {m}.
  
  Definition binary_op_0 {M : Magma} : ((object M) * (object M) -> object M )%type :=
    object_of binary_op.

  Local Notation "a + b" := (binary_op (a, b)).

  Definition binary_op_1 {M : Magma} {s1 s2 d1 d2 : object M} :
    ((s1 --> d1) * (s2 --> d2))%type -> ((s1 + s2) --> (d1 + d2)).
  Proof.
    intro m. apply (morphism_of binary_op). exact m.
  Defined.

  Local Notation "f +^ g" := (binary_op_1 (f, g)) (at level 80). (*Don't know how I should choose level.*)
  Record Symmetric_Monoidal_Category : Type :=
    {M : Magma ;
     e : M ;
     assoc : forall a b c : M, a + (b + c) --> (a + b) + c;
     iso_assoc : forall a b c : M, IsIsomorphism (assoc a b c);
     natural_assoc : forall (a b c a' b' c': M) (f : a-->a') (g : b --> b') (h : c --> c'),
       assoc a' b' c' o (f +^ (g +^ h)) = ((f +^ g) +^ h) o assoc a b c;
     lid : forall a : M, e + a --> a;
     iso_lid : forall a : M, IsIsomorphism (lid a);
     natural_lid : forall (a a' : M) (f : a --> a'),
       lid a' o (1 +^ f) = f o lid a;
     rid : forall a : M, a + e --> a;
     iso_rid : forall a : M, IsIsomorphism (rid a);
     natural_rid : forall (a a' : M) (f : a --> a'),
       rid a' o (f +^ 1) = f o rid a;
     symm : forall a b : M, a + b -->  b + a;
     natural_sym : forall (a b a' b' : M) (f : a --> a') (g : b --> b'),
         symm a' b' o (f +^ g) = (g +^ f) o symm a b;
     symm_inv : forall a b : M, symm a b o symm b a = 1;
     coh_tri : forall a b : M,
         (rid a +^ 1) o (assoc a e b) = (1 +^ lid b) ;
     coh_pent : forall a b c d : M,
         (assoc (a+b) c d) o (assoc a b (c+d)) =
         (assoc a b c +^ 1) o (assoc a (b+c) d) o (1 +^ assoc b c d);
     coh_hex : forall a b c : M,
         (assoc c a b) o (symm (a+b) c) o assoc a b c =
         (symm a c +^ 1) o (assoc a c b) o (1 +^ symm b c); (*I am guessing that this is correct*)
    }.

  (*Want to define the category [Sigma] of finite sets and isomorphisms. *)
  (*obj Sigma := {A : Type & Finite A}
    morph A B := Equiv (Fin (card A)) (Fin (card B))*)

  (*Definition Sigma_morphism (m n : nat) := Equiv (Fin m) (Fin n).*)

  Definition Sigma_cat : PreCategory.
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

  (*Prove associativity and so forth as lemmas. . .*)
  Definition preSigma := (Build_Magma Sigma_cat Sigma_coprod).

  Instance isgroupoid_Sigma {a b : preSigma} (f : a --> b) : IsIsomorphism f.
  Proof.
    srapply @Build_IsIsomorphism.
    - exact (f^-1)%equiv.
    - apply ecompose_Ve.
    - apply ecompose_eV.
  Defined.
    
  Definition Sigma : Symmetric_Monoidal_Category.
  Proof.
    srapply (@Build_Symmetric_Monoidal_Category (Build_Magma Sigma_cat Sigma_coprod) ( Fin 0 ; finite_fin 0 )).
    - (*Associativity*)
      intros A B C. apply equiv_inverse.
      apply equiv_sum_assoc.
    - (* Associativity is natural *)
      intros. simpl in f, g, h. simpl.
      apply path_equiv. apply path_arrow. intros [l | [m | n]] ; exact idpath.
    - (*Left identity*)
      intro a.
      apply sum_empty_l.
    - (*Left identity is natural*)
      intros A A' f.
      simpl in A, A', f. simpl.
      apply path_equiv. apply path_arrow. intros [[] | n]. exact idpath.
    - (*Right identity*)
      intro a. apply sum_empty_r.
    - (*Right identity is natural*)
      intros A A' f. simpl.
      apply path_equiv. apply path_arrow. intros [n | []]. exact idpath.
    - (*Symmetry*)
      intros A A'.
      apply equiv_sum_symm.
    - (*Symmetry is natural*)
      simpl.
      intros A A' B B' f g.
      apply path_equiv. apply path_arrow. intros [m | n]; exact idpath.
    - (*Symmetry is its own inverse*)
      simpl.
      intros A B.
      apply path_equiv. apply path_arrow. intros [m | n]; exact idpath.
    - (*Coherence triangle*)
      intros A B. simpl.
      apply path_equiv. apply path_arrow. intros [m | [[]|n]]; exact idpath.
    - (*Coherence pentagon*)
      intros A B C D.
      apply path_equiv. apply path_arrow.
      intros [k | [l | [m | n]]]; exact idpath.
    - (*Coherence hexagon*)
      simpl. intros A B C.
      apply path_equiv. apply path_arrow.
      intros [l | [m | n]]; exact idpath.
  Defined.

End Monoidal_Category.

(* Define the group completion of a symmetric monoidal category *)
Section Group_Completion.
  

