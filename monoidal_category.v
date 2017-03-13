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
  (*TODO: Symmetry*)
  Record Monoidal_Category : Type :=
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
     coh_tri : forall a b : M,
         (rid a +^ 1) o (assoc a e b) = (1 +^ lid b) ;
     coh_pent : forall a b c d : M,
         (assoc (a+b) c d) o (assoc a b (c+d)) =
         (assoc a b c +^ 1) o (assoc a (b+c) d) o (1 +^ assoc b c d) }.  
  





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
    
  Definition Sigma : Monoidal_Category.
  Proof.
    (*This took a long time, because it was searching for isomorphism proofs. Making the proof an instance sped things up.*)
    srapply (@Build_Monoidal_Category (Build_Magma Sigma_cat Sigma_coprod)).
    - (*Identity element*)
      exact ( Fin 0 ; finite_fin 0 ).
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
    - (*Coherence triangle*)
      intros A B. simpl.
      apply path_equiv. apply path_arrow. intros [m | [[]|n]]; exact idpath.
    - (*Coherence pentagon*)
      intros A B C D.
      apply path_equiv. apply path_arrow.
      intros [k | [l | [m | n]]]; exact idpath.
  Defined.






























  (* Defining Sigma with nat as objects *)

  
  (*Want to define the category [Sigma] of finite sets and isomorphisms. *)
  (*obj Sigma := nat
    morph m n := Equiv (Fin m) (Fin n)*)

  (*Definition Sigma_morphism (m n : nat) := Equiv (Fin m) (Fin n).*)

  Definition Sigma_cat : PreCategory.
  Proof.
    srapply (@Build_PreCategory nat (fun m n => Equiv (Fin m) (Fin n))).
    - (*Identity*)
      intro m.
      apply equiv_idmap.
    - (*Compose*)
      intros l m n.
      apply equiv_compose'.
    - (*Associativity*)
      intros h i j k.
      intros e f g.
      apply ecompose_ee_e.
    - (*Composing with identity from left*)
      intros j k. intro f.
      apply ecompose_1e.
    - (*Composing with identity from right*)
      intros j k. intro f.
      apply ecompose_e1.
  Defined.

  (*Is it interesting to see that this category is equivalent to *)
  (*[objects := {A : Type & Finite A}, morphism A B := A = B] ?  *)

  Definition Sigma_coprod : Functor (Sigma_cat*Sigma_cat) Sigma_cat.
  Proof.
    srapply @Build_Functor.
    - (*Map on objects is sum of natural numbers*)
      intro mn.
      apply (Peano.plus (fst mn) (snd mn)).
    - (*Map on morphisms.*)
      (*Fin respects sum*)
      intros [i j] [k l].
      unfold morphism. simpl.
      intros [f g].
      exact ((Fin_resp_sum k l)^-1 oE (f +E g) oE Fin_resp_sum i j).
    - (*Respects composition*)
      intros [i1 i2] [j1 j2] [k1 k2].
      intros [f1 f2] [g1 g2]. simpl.
      repeat (rewrite ecompose_ee_e).
      apply emoveR_Ve.
      rewrite ecompose_e_Ve.
      repeat rewrite ecompose_e_ee.
      apply emoveR_eM.
      rewrite ecompose_ee_V.
      rewrite ecompose_ee_V.
      apply path_equiv. apply path_arrow.
      (*This is [functor_sum] respecting composition.*)
      intros [m1 | m2]; reflexivity.
    - (*Respects identity*)
      intros [i j]. simpl.
      (* transitivity (equiv_path (Fin (i + j)) (Fin (i + j)) idpath). *)
      (* + apply (ap (equiv_path (Fin (i + j)) (Fin (i + j)))). *)
      (*   transitivity (ap Fin (idpath (i+j)))%nat. *)
      (*   * apply (ap (ap Fin)). *)
      (*     apply hset_nat. *)
      (*   * apply ap_1. *)
      (* + apply (path_equiv idpath).  *)
      apply emoveR_eM. rewrite ecompose_1e.
      apply emoveR_Ve. rewrite ecompose_eV.
      (*This is [functor_sum] respecting identity*)
      apply path_equiv. apply path_arrow.
      intros [m1 | m2]; reflexivity.
  Defined.

  (*Prove associativity and so forth as lemmas. . .*)
  Definition preSigma := (Build_Magma Sigma_cat Sigma_coprod).

  Definition assoc_Sigma : forall a b c : preSigma, a + (b + c) --> (a + b) + c.
  Proof.
    (*Reduce to equality in nat*)
    intros a b c. simpl.
    apply (equiv_path _ _). apply (ap Fin).
    apply plus_assoc.

    (* (*Use associativity of sum of types*) *)
    (* intros a b c. simpl. *)
    (* refine ((Fin_resp_sum (a+b) c)^-1  oE _ oE Fin_resp_sum a (b + c)). *)
    (* refine (((Fin_resp_sum a b)^-1 +E equiv_idmap)  oE _ oE (equiv_idmap +E Fin_resp_sum b c)). (*Where to put [^-1]?*) *)
    (* apply equiv_inverse. *)
    (* apply equiv_sum_assoc. *)

    (*Mimic proof of associativity in nat.*)
    (* intros a b c. *)
    (* induction a. *)
    (* + exact equiv_idmap. *)
    (* + simpl. *)
    (*   exact (IHa +E equiv_idmap). *)
  Defined.
  

  Instance isgroupoid_Sigma {a b : preSigma} (f : a --> b) : IsIsomorphism f.
  Proof.
    srapply @Build_IsIsomorphism.
    - exact (f^-1)%equiv.
    - apply ecompose_Ve.
    - apply ecompose_eV.
  Defined.

  (* Redundant: *)
  (* Definition isiso_assoc_sigma : forall a b c : preSigma, IsIsomorphism (assoc_Sigma a b c). *)
  (* Proof. *)
  (*   intros a b c. *)
  (*   srapply @Build_IsIsomorphism. *)
  (*   - (*Construct inverse*) *)
  (*     induction a. *)
  (*     + exact equiv_idmap. *)
  (*     + exact (IHa +E equiv_idmap). *)
  (*   - (*Left inverse*) *)
  (*     apply path_equiv. apply path_arrow.  *)
  (*     induction a. *)
  (*     + exact (fun _ => idpath). *)
  (*     + intros [n | u]. *)
  (*       * (*Equality on [inl] is the induction hypothesis*) *)
  (*         apply (ap Datatypes.inl). apply IHa. *)
  (*       * (*Both sides is just the point in Unit*) exact idpath. *)
  (*   - (*Right inverse. This proof is identic to Left inverse*) *)
  (*     apply path_equiv. apply path_arrow. *)
  (*     induction a. *)
  (*     + exact (fun _ => idpath). *)
  (*     + intros [n | u]. *)
  (*       * apply (ap Datatypes.inl). apply IHa. *)
  (*       * exact idpath. *)
  (* Defined.     *)

  Definition natural_assoc_sigma : forall (a b c a' b' c' : preSigma) (f : a --> a') (g : b --> b') (h : c --> c'),
      assoc_Sigma a' b' c' o (f +^ (g +^ h)) = ((f +^ g) +^ h) o assoc_Sigma a b c.
  Proof.
    intros. simpl in f, g, h. simpl.
    unfold binary_op_1. unfold binary_op. unfold assoc_Sigma. simpl.
    
  (*   refine ((equiv_path_pp _ _)^ @ _). *)
  (*   refine (_ @ equiv_path_pp _ _). *)
  (*   apply (ap (equiv_path (Fin (a + (b + c))) (Fin (a' + b' + c')))). *)
  (*   refine ((ap_pp Fin _ _)^ @ _ @ ap_pp Fin _ _). *)
  (*   apply (ap (ap Fin)). *)
  (*   apply hset_nat. *)
  (* Defined. *)
    
    apply path_equiv. apply path_arrow. intro m. simpl.
    repeat rewrite <- transport_idmap_ap.
    
  
    repeat (rewrite ecompose_ee_e).
    repeat rewrite ecompose_e_Ve.
    apply emoveR_Ve. rewrite ecompose_e_Ve.
    repeat (rewrite ecompose_e_ee).
    apply emoveR_eM. rewrite ecompose_ee_V.

    apply path_equiv.
    unfold equiv_compose'.     unfold equiv_compose. simpl.

    apply path_arrow.
    intro n. simpl.

    induction a, a'. simpl in n.
    - (*a, a' = 0*)reflexivity.
    - simpl.
    induction a, b, c. simpl.
    simpl.
    
    
  (*   unfold assoc_Sigma. *)

  (*   srapply @path_arrow.  *)
    
  (* Admitted. *)

    
  Definition Sigma : Monoidal_Category.
  Proof.
    (*This took a long time, because it was searching for isomorphism proofs. Making the proof an instance sped things up.*)
    srapply (@Build_Monoidal_Category (Build_Magma Sigma_cat Sigma_coprod) 0 assoc_Sigma _ natural_assoc_sigma).
    - (*Left identity*)
      intro a. exact equiv_idmap.
      (* (*This is just reflexivity, but use equiv_path for symmetry with the right identity.*) *)
      (* intro a. *)
      (* apply equiv_path. exact idpath. *)
    - (*Left identity is natural*)
      intros a a' f.
      simpl in a, a', f. simpl.
      refine (ecompose_1e _ @ _ @ (ecompose_e1 _)^).
      apply path_equiv. simpl.
      apply path_arrow. intro m.
      refine ((transport_idmap_ap nat Fin _ _ _ _)^ @ _) .
      generalize (nat_eq_fin_equiv a a' f). intro p. destruct p.
      
      
      rewrite <- (transport_idmap_ap _ Fin .
      unfold transport. simpl.
      unfold equiv_path. simpl. admit.
    - (* Right identity *)
      intro a.
      apply equiv_path. apply (ap Fin).
      apply inverse. apply nat_plus_n_O.
    - (*Right identity is natural*)
      intros a a' f.
      simpl. simpl in a, a', f.
      apply path_equiv. apply path_arrow.
      intro m.
      simpl. repeat rewrite <- transport_idmap_ap.
      

      (*Try and reduce to isset_nat*)
      refine ((equiv_path_pp _ _)^ @ _).
      rewrite (ap_V Fin (nat_plus_n_O a)). rewrite equiv_path_V.
      apply emoveL_eV.
      refine ((equiv_path_pp _ _)^ @ _).
      transitivity (equiv_path (Fin a) (Fin a') (path_universe f)).
      + apply (ap (equiv_path (Fin a) (Fin a'))).
        repeat rewrite <- ap_pp.
      
      





      
      induction l.
      + exact equiv_idmap.
      + simpl.
        exact (IHl +E equiv_idmap).
      (*Mimic proof of associativity in nat.*)
    - (*Left identity*)
      simpl. intro m. exact equiv_idmap. (*reflexivity*)
    - (*Right identity*)
      simpl. intro m.
      (*Mimic the proof of [m+0 = m]*)
      (* Lemma nat_plus_n_O : forall n:nat, n = n + 0. *)
      (* Proof. *)
      (*   induction n. *)
      (*   - reflexivity. *)
      (*   - simpl; apply ap; assumption. *)
      (* Qed. *)
      induction m.
      + exact equiv_idmap. (* reflexivity. *)
      + simpl.
        exact (IHm +E equiv_idmap).
    - (*Coherence triangle*)
      simpl. intros m n.
      induction m.
      + simpl. apply ecompose_e1.
      + simpl. transitivity (@equiv_idmap (Fin ((m+1) + n))).
      + induction m.
        * simpl. admit.
        * 
      + unfold binary_op_1. unfold binary_op. simpl.
        rewrite equiv_functor_sum_1. rewrite ecompose_e1. rewrite ecompose_Ve. reflexivity.
        
      induction m.
      + simpl.
        apply ecompose_e1.
      + simpl.
        transitivity (equiv_idmap .
        
        
        
      
      (* unfold binary_op_1. simpl. *)
      (* repeat (rewrite ecompose_ee_e). *)
      (* apply emoveR_Ve. *)
      (* rewrite (ecompose_e_Ve). *)
      (* repeat (rewrite ecompose_e_ee). *)
      (* apply emoveL_eM. *)
      (* transitivity (@equiv_idmap (Fin m + Fin n)%type). *)
      (* induction m. simpl. (*TODO: Lag equiv-taktikk.*) *)
      

      (* Open Scope function_scope. Open Scope type_scope. *)
      (* + apply path_sum. simpl. *)
      (*   unfold functor_sum. *)
      (*   unfold Fin_resp_sum. simpl. *)
      
      
      

      (* intro s. Open Scope function_scope. *)
      (* simpl. *)
      (* apply (ap ((Fin_resp_sum m n)^-1)). *)
      (* transitivity ((Fin_resp_sum m n) s). *)
      (*   admit. *)

      (*   unfold Fin_resp_sum. *)
      (*   apply path_sum. simpl. *)
      
      (* unfold trivial_equiv_fin. unfold Fin_resp_sum. simpl. *)
      
      (* apply path_sum. *)
      
      (* unfold functor_sum. simpl. *)
      
      
      
      

      
      
    
      
      
      
      
      
      


      
      
      
  

  
  (* (*In an ideal world this would be unnecessary, as it is basically [morphism_of].*) *)
  (* Definition pair_morphism_of {C1 C2 D : PreCategory} (F: Functor (C1*C2) D) {s1 d1 : C1} {s2 d2: C2} : *)
  (*   (s1 --> d1) * (s2 --> d2) -> F (s1, s2) --> F (d1, d2). *)
  (* Proof. *)
  (*   intro m. *)
  (*   apply (morphism_of F). exact m. *)
  (* Defined. *)
  
  
  
  (* Record Monoidal_Category : Type := *)
  (*   Build_Monoidal_Category { M : PreCategory ; *)
  (*                             coprod : Functor (M * M) M where "a + b" := (coprod (a, b)); *)
  (*                             e : M;  *)
  (*                             assoc : forall a b c : M, a + (b + c) --> (a + b) + c; *)
  (*                             lid : forall a : M, e + a --> a; *)
  (*                             rid : forall a : M, a + e --> a; *)
  (*                             coh_tri : forall a b : M, *)
  (*                                 (pair_morphism_of coprod (rid a, 1)) o (assoc a e b) = *)
  (*                                 (pair_morphism_of coprod (1, lid b)) ; *)
  (*                             coh_pent : forall a b c d : M, *)
  (*                                 (assoc (a+b) c d) o (assoc a b (c+d)) = *)
  (*                                 (pair_morphism_of coprod (assoc a b c, 1)) o (assoc a (b + c) d) o *)
  (*                                 (pair_morphism_of coprod (1, assoc b c d)) }. *)
                                                                             
                                  
                                                        

  
  

             
             

             
             
             
             
    

  



  



  
  





End Monoidal_Category.
