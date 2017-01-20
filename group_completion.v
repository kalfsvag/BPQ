Require Import HoTT.
Require Import UnivalenceAxiom.
Load stuff.


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
      exact (sig_const _ _).
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

  Definition path_hom {M N : Monoid} (f g : Homomorphism M N) :    
    (hom_map f = hom_map g) -> f = g.
  Proof.
    intro h.
    apply (equiv_ap (issig_hom M N)^-1 _ _)^-1.
    refine (@path_sigma_hprop _ _ prop_ishom _ _ _).
    exact h.
  Defined.    
  
  Definition compose_hom {L M N: Monoid} :
    Homomorphism M N -> Homomorphism L M -> Homomorphism L N.
  Proof.
    intros g f.
    refine (Build_Homomorphism _ _ ((hom_map g) o (hom_map f)) _ _).
    - exact (ap (hom_map g) (preserve_id f) @ (preserve_id g)).
    - intros m1 m2.
      refine ((ap (hom_map g) (preserve_mult f)) @ _).
      exact (preserve_mult g ).
  Defined.

  (*A homomorphism of groups preserve inverses*)
  Definition preserve_inv (G H : Group) (f : Homomorphism G H) (a : G) :
    hom_map f (- a) = - (hom_map f a).
  Proof.
    apply grp_moveL_V1.
    refine ((preserve_mult f)^ @ _).
    refine (_ @ preserve_id f).
    exact (ap (hom_map f) (grp_rinv a)).
  Defined.    
End Homomorphism.

Notation "'Hom'" := Homomorphism : monoid_scope.

Section Group_completion.
  (*The Grothendieck group completion*)
  (*The group completion of a symmetric monoid M is M*M/~ where m~s+m *)
  (*Assume S is a symmetric monoid with cancellation. (Group completion is nicer then.)*)
  Variable S : Symmetric_Monoid.
  (* Variable rc : right_cancellation_law S. *)

  Open Scope monoid_scope . 

  (*Take a triple (a, b ,s) to (s*a, s*b)*)
  Definition as_bs : S*S*S -> S*S.
    intros [[a b] s].
    exact (a+s, b+s).
  Defined.

  Definition grp_compl_set (S:Monoid) := Trunc 0 (Coeq as_bs fst).
  Definition grp_compl_mult : grp_compl_set S -> grp_compl_set S -> grp_compl_set S.
    refine (Trunc_rec _).
    intro g1.
    refine (Trunc_rec _).
    intro g2.
    revert g2.
    srapply @Coeq_rec.
    - (*Fix second variable*)
      intros [n1 n2].
      revert g1.
      srapply @Coeq_rec.
      + (*Fix first variable*)
        intros [m1 m2].
        exact (tr (coeq (m1 + n1, m2 + n2))).
      + (*First variable runs along cp*)
        intros [[a b] s].
        apply (ap (tr)).
        simpl.
        refine (_ @ cp (a + n1 ,b + n2,s)).
        apply (ap coeq). unfold as_bs.
        apply path_prod;
             refine ((mon_assoc)^ @ _ @ (mon_assoc));
             apply (ap (mon_mult _));
             apply mon_sym.
    - (*Second variable runs along cp*)
      intros [[a b] s].
      revert g1.
      srapply @Coeq_ind.
      + (*First variable is fixed*)
        intros [m1 m2].
        apply (ap (tr)).
        simpl.
        refine (_ @ cp (m1+a,m2+b,s)).
        apply (ap coeq). unfold as_bs.
        apply path_prod; apply mon_assoc.
      + (*First variable runs along cp*)
        intro abs'.
        apply (istrunc_truncation 0).
  Defined.
  
(*  Unset Printing Notations.
  Set Printing Implicit. *)
  Definition grp_compl_assoc : associative grp_compl_mult.
    Proof.
      unfold associative.
      srapply @Trunc_ind. intro a.
      srapply @Trunc_ind. intro b.
      srapply @Trunc_ind.
      srapply @Coeq_ind.
      - (*Fix third variable*)
        intros [n1 n2]; revert b.
        srapply @Coeq_ind.
        + (*Fix second variable*)
          intros [m1 m2]; revert a.
          srapply @Coeq_ind.
          * (*Fix first variable*)
            intros [l1 l2].
            apply (ap tr). apply (ap coeq).
            apply path_prod; apply mon_assoc.
          * (*First variable runs along cp*)
            intro abs. apply (istrunc_truncation 0).
        + (*Second variable runs along cp*)
          intro abs.
          apply (istrunc_truncation 0).
      - (*Third variable runs along cp*)
        intro abs. apply (istrunc_truncation 0).
    Defined.
          
  Definition grp_compl_id : grp_compl_set S := tr (coeq (mon_id S, mon_id S)).
  
  Definition grp_compl_lid : left_identity grp_compl_mult grp_compl_id.
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Variable is fixed*)
      intros [m1 m2].
      simpl.
      apply (ap tr).
      apply (ap coeq).
      apply path_prod; apply mon_lid.
    - (*Variable runs along cp*)
      intro x.
      apply (istrunc_truncation 0).
  Defined.
  
  Definition grp_compl_rid : right_identity grp_compl_mult grp_compl_id.
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Variable is fixed*)
      intros [m1 m2].
      simpl.
      apply (ap tr).
      apply (ap coeq).
      apply path_prod; apply mon_rid.
    - (*Variable runs along cp*)
      intro x.
      apply (istrunc_truncation 0).
  Defined.

  Definition grp_compl_sym : symmetric grp_compl_mult.
  Proof.
    srapply @Trunc_ind. intro a.
    srapply @ Trunc_ind.
    srapply @Coeq_ind.
    - (*Fix second variable*)
      intros [n1 n2]. revert a.
      srapply @Coeq_ind.
      + (*Fix first variable*)
        intros [m1 m2].
        apply (ap tr). apply (ap coeq).
        apply path_prod; apply mon_sym.
      + (*First variable runs along cp*)
        intro abs. apply (istrunc_truncation 0).
    - (*Second variable runs along cp*)
      intro abs. apply (istrunc_truncation 0).
  Defined.    

  Definition grp_compl_inv : grp_compl_set S -> grp_compl_set S.
  Proof.
    apply Trunc_rec.
    srapply @Coeq_rec.
    - intros [m1 m2].
      exact (tr (coeq (m2, m1))).
    - intros [[a b] s].
      simpl.
      apply (ap tr).
      exact (cp (b, a, s)).
  Defined.

  Definition grp_compl_linv : left_inverse grp_compl_mult grp_compl_id grp_compl_inv.
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Fix variable*)
      intros [m1 m2].
      simpl.
      apply (ap tr).
      refine (_ @ cp (mon_id S, mon_id S, m1 + m2)).
      apply (ap coeq).
      unfold as_bs.
      apply path_prod.
      + refine (_ @ (mon_lid (m1 + m2))^ ). apply mon_sym.
      + exact (mon_lid (m1+m2))^ .
    - intro abs.
      apply (istrunc_truncation 0).
  Defined.
  
  (*Can choose to prove right identity using lift identity and symmetry, or do the same proof again. . .*)
  Definition grp_compl_rinv : right_inverse grp_compl_mult grp_compl_id grp_compl_inv.
  Proof.
    srapply @Trunc_ind.
    srapply @Coeq_ind.
    - (*Fix variable*)
      intros [m1 m2].
      simpl.
      apply (ap tr).
      refine (_ @ cp (mon_id S, mon_id S, m1 + m2)).
      apply (ap coeq).
      unfold as_bs.
      apply path_prod.
      + simpl.
        exact (mon_lid (m1+m2))^ .
      + simpl.
        refine (_ @ (mon_lid (m1+m2))^).
        apply mon_sym.
    - intro abs.
      apply (istrunc_truncation 0).
  Defined.

  Definition group_completion : Abelian_Group :=
    Build_Abelian_Group
      (Build_Group
         (Build_Monoid
            (grp_compl_set S) 
            (grp_compl_mult) grp_compl_id grp_compl_assoc grp_compl_lid grp_compl_rid )
         grp_compl_inv grp_compl_linv grp_compl_rinv)
      grp_compl_sym.

  
  (*Defining the (monoid) homomorphism from a monoid to its group completion*)
   Definition S_to_grpcmplS : Homomorphism S group_completion.
     srapply @Build_Homomorphism.
    - (*The map on set level*)
      intro m.
      exact (tr (coeq (m, mon_id S))).
    - (*The map preserves identity*)
      exact idpath.
    - (*The map is an isomorphism*)
      intros m1 m2.
      apply (ap tr); apply (ap coeq).
      apply path_prod.
        exact idpath.
        exact (mon_lid (mon_id S))^.
  Defined.

End Group_completion.

Section Functoriality.
  Open Scope monoid_scope.
  Definition functor_group_completion {S S' : Symmetric_Monoid} :
    Hom S S' -> Hom (group_completion S) (group_completion S').
  Proof.
    intro f.
    srapply Build_Homomorphism.
    - (*Construct the map.*)
      apply Trunc_rec.
      srapply @Coeq_rec.
      + (* (a,b) => (f a, f b) *)
        intros [m n].
        exact (tr (coeq (hom_map f m, hom_map f n))).
      + (*The map is well defined.*)
        intros [[a b] s].
        apply (ap tr).
        refine (_ @ cp (hom_map f a, hom_map f b, hom_map f s)).
        apply (ap coeq).
        apply path_prod; apply preserve_mult.
    - (*Preserves identity*)
      apply (ap tr). apply (ap coeq).
      apply path_prod; apply preserve_id.
    - (*Preserves multiplication.*)
      srapply @Trunc_ind. intro a.
      srapply @Trunc_ind.
      srapply @Coeq_ind.
      + (*Second variable is fixed*)
        intros [n1 n2]. revert a.
        srapply @Coeq_ind.
        * (*First variable is fixed*)
          intros [m1 m2].
          apply (ap tr). apply (ap coeq).
          apply path_prod; apply preserve_mult.
        * (*First variable runs along cp*)
          intro abs. apply (istrunc_truncation 0).
      + (*Second variable runs along cp*)
        intro abs. apply (istrunc_truncation 0).
  Defined.        
        
  Definition natural_S_to_grpcmplS {S S' : Symmetric_Monoid} (h : Hom S' S):
    compose_hom (S_to_grpcmplS S) h = compose_hom (functor_group_completion h) (S_to_grpcmplS S').
  Proof.
    apply path_hom.
    apply path_forall.
    intro m.
    apply (ap tr). apply (ap coeq).
    apply path_prod.
      exact idpath.
      exact (preserve_id h)^.
  Defined.      
  
End Functoriality.                                             

Section Adjointness.
  (*Prove that group completion is left adjoint to the forgetful functor from abelian groups to symmetric monoids*)
  Open Scope monoid_scope.
  
  Definition hom_map_extend_to_inv {S : Symmetric_Monoid} {A : Abelian_Group} :
    Homomorphism S A -> ((group_completion S) -> A).
  Proof.
    intro f.
    refine (Trunc_rec (H:=grp_isset _) _).
    srapply @Coeq_rec.
    + (*The variable is fixed*)
      intro m12.
      exact ((hom_map f (fst m12)) - (hom_map f (snd m12))).
    + (*The variable runs along cp (i.e. map is well defined)*)
      intros [[a b] s]. simpl.
      refine (path_group2 (preserve_mult f) (ap grp_inv (preserve_mult f)) @ _).
      refine (grp_assoc^ @ _ ).
      apply grp_whiskerL.
      apply grp_moveR_gV.
      refine (_ @ grp_assoc^ ).
      refine (_ @ grp_whiskerR (grp_linv _)^ ).
      exact (grp_lid _)^ .
  Defined.

  Definition extend_to_inv {S : Symmetric_Monoid} {A : Abelian_Group} :
    Homomorphism S A -> Homomorphism (group_completion S) A.
  Proof.
    intro f.
    refine (Build_Homomorphism _ _ (hom_map_extend_to_inv f) (grp_rinv _) _).
    (*Preserves multiplication*)
    (*First we need to use Trunc_ind
         This is made difficult by Trunc_ind behaving weirdly. . .*)

    (*Trunc_ind uses about 5 minutes to find a proof of this, faster to prove it manually.*)
    assert (Pt : forall m1 m2 : (group_completion S),
                   IsTrunc 0
                           (hom_map_extend_to_inv f (m1 + m2) =
                            hom_map_extend_to_inv f m1 + hom_map_extend_to_inv f m2) ). (*Can also use [enough]. . .*)
    { intros m1 m2.  exact (@trunc_succ -1 _ (mon_isset _ _ _)). }
    intro m1.
    refine (@Trunc_ind 0 (Coeq (as_bs S) fst) _ (Pt m1) _ ).
    intro b. revert m1.
    set (m2 := tr b : (group_completion S)).
    refine (@Trunc_ind 0 (Coeq (as_bs S) fst) _ (fun m1 => Pt m1 m2) _); unfold m2; clear m2.
    intro a. revert b.
    (*Now the truncations are done with. . .*)
    srapply @Coeq_ind.
    - (*Second variable fixed*)
      intros [n1 n2]. revert a.
      srapply @Coeq_ind.
      + (*First variable fixed*)
        intros [m1 m2]. simpl.
        refine (grp_whiskerR (preserve_mult f) @ _).
        refine (grp_assoc^ @ _ @ grp_assoc).
        apply grp_whiskerL.
        refine (grp_whiskerL (ap grp_inv (preserve_mult f)) @ _).
        refine (grp_whiskerL grp_inv_distr @ _).
        refine (_ @ grp_sym).
        exact grp_assoc.
      + (*First variable runs along cp*)
        intro abs. apply (grp_isset A).
    - (*Second variable runs along cp*)
      intro abs. apply (grp_isset A).
  Defined.

  Theorem grp_compl_adjoint (S : Symmetric_Monoid) (A: Abelian_Group) :
    Homomorphism S A <~> Homomorphism (group_completion S) A.
  Proof.
    refine (equiv_adjointify extend_to_inv (fun f => compose_hom f (S_to_grpcmplS S)) _ _).
    (*Prove that the maps are inverses*)
    - intro f.
      refine (path_hom _ _ _) ; simpl.
      apply path_forall.
      (*Trunc_ind uses about 5 minutes to find a proof of this, faster to prove it manually.*)
      assert (Pt : forall m : (group_completion S),
                   IsTrunc 0
                           (hom_map_extend_to_inv (compose_hom f (S_to_grpcmplS S)) m = hom_map f m)).
      { intro m. exact (@trunc_succ -1 _ (mon_isset _ _ _)). }
      refine (@Trunc_ind 0 (Coeq (as_bs S) fst) _ Pt _ ).
      srapply @Coeq_ind. 
      + (*Variable fixed*)
        intros [m1 m2].
        simpl.
        apply grp_moveR_gV.
        refine (_ @ preserve_mult f).
        apply (ap (hom_map f)); apply (ap tr).
        refine ((cp (m1, mon_id S, m2))^ @ _); unfold as_bs.
        apply (ap coeq).
        apply (ap (fun s : S => (m1 + m2, s))).
        exact (mon_lid m2 @ (mon_rid m2)^).
      + (*Variable runs along cp*)
        intro abs.
        apply (grp_isset A).
    - intro f.
      refine (path_hom _ _ _) ; simpl.
      apply path_forall.
      intro m.
      apply grp_moveR_gV.
      refine ((grp_rid _)^ @ _).
      exact (grp_whiskerL (preserve_id f)^ ).
  Defined.

  (*Naturality follows from [natural_S_to_grpcmplS], since the map [Hom (group_completion S) A -> Hom S A is exactly precomposing with [S_to_grpcmplS].*)

End Adjointness.
