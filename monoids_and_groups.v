Load stuff.
Require Import UnivalenceAxiom.


Section Monoids_and_Groups.
  Definition associative {A : Type}  (m : A->A->A) := forall a b c : A, m a (m b c) = m (m a b) c.
  Definition left_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m e a = a.
  Definition right_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a.
  Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a.
  Definition left_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) :=
    forall a : A, m (inv a) a = e.
  Definition right_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) :=
    forall a : A, m a (inv a) = e.


  Record Monoid : Type := { mon_set : Type;
                            mon_isset : IsHSet mon_set;
                            mon_mult  : mon_set->mon_set->mon_set;
                            mon_id : mon_set;
                            mon_assoc : associative mon_mult;
                            mon_lid : left_identity mon_mult mon_id ;
                            mon_rid : right_identity mon_mult mon_id
                          }.
  

  Record Symmetric_Monoid : Type := {mon : Monoid;
                                     mon_sym : symmetric (mon_mult mon) }.
  Global Arguments mon_sym {s} {a} {b}.

  (*Makes mon_isset an implicit argument*)
  Global Arguments Build_Monoid mon_set {mon_isset} mon_mult mon_id mon_assoc mon_lid mon_rid.


  Coercion mon_set : Monoid >-> Sortclass.
  Coercion mon : Symmetric_Monoid >-> Monoid.
  Global Arguments mon_mult {m} m1 m2.
  Global Arguments mon_assoc {m} {a} {b} {c}.
  Global Arguments mon_lid {m} a.
  Global Arguments mon_rid {m} a.

  

  Global Instance ispointed_M {M : Monoid} : IsPointed M := (mon_id M).

(*  (*Formulate the cancellation law for a monoid*)
  Definition right_cancellation_law (M : Monoid) :=
    forall a b s : M, a + s = b + s -> a = b.   *)
  
  Record Group : Type := {grp_mon : Monoid;
                          grp_inv : grp_mon -> grp_mon;
                          grp_linv : left_inverse mon_mult (mon_id grp_mon) grp_inv;
                          grp_rinv : right_inverse mon_mult (mon_id grp_mon) grp_inv
                         }.
  Coercion grp_mon : Group >-> Monoid.
  Global Arguments grp_inv {g} a.
  Global Arguments grp_linv {g} a.
  Global Arguments grp_rinv {g} a.

  Record Abelian_Group : Type :=
    {grp : Group;
     grp_sym : symmetric (@mon_mult (grp_mon grp))}.

  Coercion grp : Abelian_Group >-> Group.
  Global Arguments grp_sym {A} {a} {b} : rename.

  (*Must do some work to get a coercion Abelian_Group >-> Symmetric_Monoid*)
  Definition forget_to_SymMon : Abelian_Group -> Symmetric_Monoid :=
    fun A => Build_Symmetric_Monoid A (@grp_sym A).

  Coercion forget_to_SymMon : Abelian_Group >-> Symmetric_Monoid.    

End Monoids_and_Groups.
  
Section nat_monoid.  
  (*Strangely, I cannot find any proofs of nat being associative*)
  Local Open Scope nat_scope.
  Definition plus_assoc : associative Peano.plus.
    intros j k l.
    induction j, k, l.
    - exact idpath.
    - exact idpath.
    - exact idpath.
    - exact idpath.
    - exact (ap S IHj).
    - exact (ap S IHj).
    - exact (ap S IHj).
    - exact (ap S IHj).
  Defined.
  
  Definition nat_monoid : Monoid :=
    Build_Monoid
      nat Peano.plus O
      plus_assoc (fun _ => idpath) (fun n => (nat_plus_n_O n)^).
End nat_monoid.



Notation "a + b"  := (mon_mult a b) : monoid_scope.
Notation "- a" := (grp_inv a) : monoid_scope.
Notation "a - b" := (mon_mult a (grp_inv b)) : monoid_scope.

(*Just so that you don't have to remember what is monoid structure and what is group structure *)
Notation "'grp_set' G" := (mon_set (grp_mon G)) (at level 0) : monoid_scope.
Notation "'grp_isset' G" := (mon_isset (grp_mon G)) (at level 0) : monoid_scope.
Notation "'grp_id' G" := (mon_id (grp_mon G)) (at level 0) : monoid_scope.
Notation "'grp_mult'" := (@mon_mult (grp_mon _)) (at level 0, only parsing) : monoid_scope.
Notation "'grp_assoc'" := (mon_assoc ( m := grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_lid'" := (@mon_lid (grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_rid'" := (@mon_rid (grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_rid'" := (@mon_rid (grp_mon _)) (at level 0) : monoid_scope.
(*TODO: Use this notation*)

Section Loop_is_group.
  Definition loopGroup (A : pType) {istrunc_A : IsTrunc 1 A} : Group.
    srapply Build_Group.
    exact (Build_Monoid (loops A) concat idpath concat_p_pp concat_1p concat_p1).
    - exact inverse.
    - exact concat_Vp.
    - exact concat_pV.
  Defined.
End Loop_is_group.

Section Group_lemmas.
  Open Scope monoid_scope.
  Definition grp_whiskerL {G : Group} {a b c : G} : b = c -> a + b = a + c
    := ap (fun g => a + g).

  Definition grp_whiskerR {G : Group} {a b c : G} : a = b -> a + c = b + c
    := ap (fun g => g + c).
  
  Definition grp_cancelR {G : Group} {a b : G} (s : G) :
    a + s = b + s -> a = b.
  Proof.
    intro p.      
    refine ((grp_rid a)^ @ _ @ grp_rid b).
    refine ((grp_whiskerL (grp_rinv s))^ @ _ @ grp_whiskerL (grp_rinv s)).
    refine (grp_assoc @ _ @ grp_assoc^).
    exact (grp_whiskerR p).
  Defined.
  
  Definition grp_cancelL {G : Group} {a b} (s : G) :
    s + a = s + b -> a = b.
  Proof.
    intro p.
    refine ((grp_lid a)^ @ _ @ grp_lid b).
    refine ((grp_whiskerR (grp_linv s))^ @ _ @ grp_whiskerR (grp_linv s)).
    refine (grp_assoc^ @ _ @ grp_assoc).
    exact (grp_whiskerL p).
  Defined.

  Definition grp_moveR_Mg {G : Group} {a b c : G} :
    b = -a + c -> a + b = c.
    Proof.
      intro p.
      refine (grp_whiskerL p @ _).
      refine (grp_assoc @ _).
      refine (grp_whiskerR (grp_rinv a) @ _).
      exact (grp_lid c).
    Defined.

  Definition grp_moveR_gM {G : Group} {a b c : G} :
    a = c - b -> a + b = c.
    Proof.
      intro p.
      refine (grp_whiskerR p @ _).
      refine (grp_assoc^ @ _).
      refine (grp_whiskerL (grp_linv b) @ _).
      exact (grp_rid c).
    Defined.      

  Definition grp_moveR_Vg {G : Group} {a b c : G} :
    b = a + c -> - a + b = c.
  Proof.
    intro p.
    refine (grp_whiskerL p @ _).
    refine (grp_assoc @ _).
    refine (grp_whiskerR (grp_linv a) @ _).
    exact (grp_lid c).
  Defined.

  Definition grp_moveR_gV {G : Group} {a b c : G} :
    a = c + b -> a - b = c.
  Proof.
    intro p.
    refine (grp_whiskerR p @ _).
    refine (grp_assoc^ @ _).
    refine (grp_whiskerL (grp_rinv b) @ _).
    exact (grp_rid c).
  Defined.

  Definition grp_moveL_Mg {G : Group} {a b c : G} :
    -b + a = c -> a = b + c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerL p).
    refine (_ @ grp_assoc^).
    refine (_ @ grp_whiskerR (grp_rinv b)^).
    exact (grp_lid a)^.
  Defined.    
    
  Definition grp_moveL_gM {G : Group} {a b c : G} :
    a - c = b-> a = b + c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerR p).
    refine (_ @ grp_assoc).
    refine (_ @ grp_whiskerL (grp_linv c)^).
    exact (grp_rid a)^.
  Defined.

  Definition grp_moveL_Vg {G : Group} {a b c : G} :
    b + a = c -> a = -b + c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerL p).
    refine (_ @ grp_assoc^ ).
    refine (_ @ grp_whiskerR (grp_linv b)^).
    exact (grp_lid a)^.
  Defined.    

  Definition grp_moveL_gV {G : Group} {a b c : G} :
    a + c = b -> a = b - c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerR p).
    refine (_ @ grp_assoc ).
    refine (_ @ grp_whiskerL (grp_rinv c)^).
    exact (grp_rid a)^.
  Defined.

  Definition grp_moveL_1M {G : Group} {a b : G} :
    a - b = grp_id G -> a = b.
  Proof.
    intro p.
    refine (grp_moveL_gM  p @ _).
    exact (grp_lid b).
  Defined.

  Definition grp_moveL_M1 {G : Group} {a b : G} :
    - a + b = grp_id G -> a = b.
  Proof.
    intro p.
    refine (_ @ (grp_moveL_Mg p)^).
    exact (grp_rid a)^ .
  Defined.

  Definition grp_moveL_1V {G : Group} {a b : G} :
    a + b = grp_id G -> a = - b.
  Proof.
    intro p.
    refine (grp_moveL_gV p @ _).
    exact (grp_lid (- b)).
  Defined.

  Definition grp_moveL_V1 {G : Group} {a b : G} :
    a + b = grp_id G -> b = - a.
  Proof.
    intro p.
    refine (grp_moveL_Vg p @ _).
    exact (grp_rid (-a)).
  Defined.
  
  Definition grp_moveR_M1 {G : Group} {a b : G} :
    grp_id G = -a + b -> a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_Mg p).
    exact (grp_rid a)^ .
  Defined.

  Definition grp_moveR_1M {G : Group} {a b : G} :
    grp_id G = b -a -> a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_gM p).
    exact (grp_lid a)^ .
  Defined.

  Definition grp_moveR_1V {G : Group} {a b : G} :
    grp_id G = b + a -> -a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_gV p).
    exact (grp_lid (-a))^ .
  Defined.

  Definition grp_moveR_V1 {G : Group} {a b : G} :
    grp_id G = a + b -> -a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_Vg p).
    exact (grp_rid (-a))^ .
  Defined.

  Definition inv_id {G : Group} : - (grp_id G) = grp_id G
    := grp_moveR_1V (grp_rid _)^ .

  Definition grp_inv_distr {G : Group} {a b: G} :
    - (a + b) = - b - a.
  Proof.
    apply grp_moveL_Vg.
    apply grp_moveR_gV.
    refine (_ @ grp_assoc^).
    refine ( _ @ (grp_whiskerR (grp_linv a)^ ) ).
    exact (grp_lid b)^ .
  Defined.

  Definition path_group2 {G : Group} {a b c d : G} : a = c -> b = d -> a + b = c + d
    := fun p q => grp_whiskerL q @ grp_whiskerR p.

  Definition isequiv_grp_mult {G : Group} (g : G) :
    IsEquiv (fun a => a + g).
  Proof.
    srapply @isequiv_adjointify.
    - exact (fun a => a - g).
    - intro a. apply grp_moveR_gM. reflexivity.
    - intro a. apply grp_moveR_gV. reflexivity.
  Defined.

  Definition grp_mult_equiv {G : Group} (g : G) : G <~>G :=
    BuildEquiv G G (fun a => a+ g) (isequiv_grp_mult g).
  
End Group_lemmas.

Section Homomorphism.
  Open Scope monoid_scope.
  
  Record Homomorphism (M N : Monoid) :=
    {hom_map : M -> N ;
     preserve_id : hom_map (mon_id M) = mon_id N ;
     preserve_mult : forall m1 m2 : M, hom_map (m1 + m2) = (hom_map m1) + (hom_map m2)}. 

  Global Arguments hom_map {M N} h _.
  Global Arguments preserve_id {M N} h.
  Global Arguments preserve_mult {M N} h {m1} {m2}.

  Coercion hom_map : Homomorphism >-> Funclass.

  Definition ishom {M N : Monoid} (f : M -> N) :=
    (f (mon_id M) = mon_id N) * (forall m1 m2 : M, f (m1 + m2) = f m1 + f m2).
      

  Definition issig_hom (M N : Monoid) :
    {f : M -> N &  ishom f} <~> Homomorphism M N.
  Proof.
    equiv_via {f : M -> N &
                          sig (fun _ : (f (mon_id M) = mon_id N) =>
                                 (forall m1 m2 : M, f (m1 + m2) = f m1 + f m2) )}.
    - refine (equiv_functor_sigma_id _).
      intro f.
      apply equiv_inverse.
      exact (equiv_sigma_prod0 _ _).
    - issig (Build_Homomorphism M N) (@hom_map M N) (@preserve_id M N) (@preserve_mult M N).
  Defined.

  Definition prop_ishom {M N : Monoid} :
    forall f : M->N, IsHProp (ishom f).
  Proof.
    intro f.
    set (A := (f (mon_id M) = mon_id N)).
    set (B := (forall m1 m2 : mon_set M, f (m1 + m2) = f m1 + f m2)).
    refine (@trunc_prod -1 A (mon_isset _ _ _) B _).
    unfold B; clear A; clear B.
    set (P := fun m1 : mon_set M => forall m2, f (m1 + m2) = f m1 + f m2).
    refine (@trunc_forall _ (mon_set M) P -1 _).
    intro m1.
    unfold P; clear P.
    set (P := fun m2 : mon_set M =>
                f (m1 + m2) = f m1 + f m2).
    refine (@trunc_forall _ _ P -1 _).
    intro m2; unfold P; clear P.
    exact (mon_isset _ _ _).
  Defined.

  (*Two homomorphisms are equal if their underlying maps are equal.*)
  Definition path_hom {M N : Monoid} (f g : Homomorphism M N) :    
    (hom_map f = hom_map g) -> f = g :> Homomorphism M N.
  Proof.
    intro h.
    apply (equiv_ap (issig_hom M N)^-1 _ _)^-1.
    refine (@path_sigma_hprop _ _ prop_ishom _ _ _).
    exact h.
  Defined.

  Definition idhom {M : Monoid} : Homomorphism M M
    := Build_Homomorphism M M idmap idpath (fun _ _ => idpath).
  
  Definition compose_hom {L M N: Monoid} :
    Homomorphism M N -> Homomorphism L M -> Homomorphism L N.
  Proof.
    intros g f.
    refine (Build_Homomorphism _ _ (g o f) _ _).
    - exact (ap g (preserve_id f) @ (preserve_id g)).
    - intros m1 m2.
      refine ((ap g (preserve_mult f)) @ _).
      exact (preserve_mult g ).
  Defined.

  (*A homomorphism of groups preserve inverses*)
  Definition preserve_inv {G H : Group} (f : Homomorphism G H) (a : G) :
    f (- a) = - (f a).
  Proof.
    apply grp_moveL_V1.
    refine ((preserve_mult f)^ @ _).
    refine (_ @ preserve_id f).
    exact (ap f (grp_rinv a)).
  Defined.
End Homomorphism.

Notation "'Hom'" := Homomorphism : monoid_scope.
Infix "oH" := compose_hom (at level 40, left associativity).
