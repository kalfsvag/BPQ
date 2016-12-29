Require Import HoTT.
Require Import UnivalenceAxiom.
Load pType_basics.
Load Coequalizer.

(*This section should be elsewhere *)
Section Misc.

  (** The map [ap f] can be viewed as a map between path spaces {x y | x=y }
The lemma [ap12] says that [f=g] implies [ap f == ap g] as maps of path spaces. *)
  (*Is this correctly placed and named?*)
  Definition ap12 {A B : Type} {a b : A} (p : a = b) {f g : A->B} (h : f=g)  :
    (ap10 h a)^ @ ap f p @ ap10 h b= ap g p.
  Proof.
    destruct p, h.
    exact (concat_p1 _ @ concat_1p _).
  Defined.

  Definition sig_const (A B : Type) :
    sig (fun _ : A => B) <~> A * B :=
    (@equiv_adjointify
       (sig (fun _ : A => B)) (A * B)
       (fun ab => match ab with (a ; b) => (a, b) end)
       (fun ab => match ab with (a, b) => (a ;b) end)
       (fun _ => idpath) (fun _ => idpath)).

(*  Definition prod_uncurryD {A B : Type} {P : A -> B -> Type} :
    (forall p : A*B, P (fst p) (snd p)) -> forall a : A, forall b : B, P a b :=
    (equiv_prod_ind _)^-1 . *)
(*
  Definition precomposeD {A B : Type} {P : B -> Type} (f : A->B) :
    (forall a : A, P (f a)) -> forall b : B, P b.
  Proof.
    intro g.
    intro b.
    exact 
  *)  
  
  
End Misc.




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

  (*Makes mon_isset an implicit argument*)
  Global Arguments Build_Monoid mon_set {mon_isset} mon_mult mon_id mon_assoc mon_lid mon_rid.


  Coercion mon_set : Monoid >-> Sortclass.
  Coercion mon : Symmetric_Monoid >-> Monoid.
  Global Arguments mon_mult {m} m1 m2.
  Global Arguments mon_assoc {m} a b c.
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
Notation "'grp_assoc'" := (@mon_assoc (grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_lid'" := (@mon_lid (grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_rid'" := (@mon_rid (grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_rid'" := (@mon_rid (grp_mon _)) (at level 0) : monoid_scope.
(*TODO: Use this notation*)
  


Section Group_lemmas.
  Open Scope monoid_scope.
  Definition grp_cancelR {G : Group} {a b : G} (s : G) :
    a + s = b + s -> a = b.
  Proof.
    intro p.
    refine (_ @ (ap (fun c => (c - s)) p) @ _).
    - refine ((grp_rid a)^ @ _).
      refine ((ap (grp_mult a) (grp_rinv s))^ @ _) .
      exact (grp_assoc _ _ _).
    - refine (_ @ grp_rid b).
      refine (_ @ (ap (grp_mult b) (grp_rinv s))).
      exact (grp_assoc _ _ _)^.
  Defined.

  Definition grp_cancelL {G : Group} {a b} (s : G) :
    s + a = s + b -> a = b.
  Proof.
    intro p.
    refine (_ @ (ap (fun c => (- s + c)) p) @ _).
    - refine (_ @ (grp_assoc _ _ _)^).
      refine ((grp_lid a)^ @ _).
      exact (ap (fun c => c + a) (grp_linv s)^).
    - refine (grp_assoc _ _ _ @ _).
      refine ( _ @ grp_lid b ).
      exact (ap (fun c => c + b) (grp_linv s)).
  Defined.

  Definition grp_moveR_Mg {G : Group} {a b c : G} :
    b = -a + c -> a + b = c.
    Proof.
      intro p.
      apply (grp_cancelL (-a)).
      refine (_ @ p).
      refine (grp_assoc _ _ _ @ _).
      refine ( _ @ (grp_lid b)).
      apply (ap (fun c => c + b)).
      exact (grp_linv a).
    Defined.


  Definition grp_moveR_gM {G : Group} {a b c : G} :
    a = c - b -> a + b = c.
    Proof.
      intro p.
      apply (grp_cancelR (- b)).
      refine (_ @ p).
      refine (_ @ (grp_rid a)).
      refine ((grp_assoc _ _ _)^ @ _).
      apply (ap (grp_mult a)).
      exact (grp_rinv b).
    Defined.
      

  Definition grp_moveR_Vg {G : Group} {a b c : G} :
    b = a + c -> - a + b = c.
  Proof.
    intro p.
    apply (grp_cancelL a).
    refine (_ @ p).
    refine (grp_assoc _ _ _ @ _).
    refine (_ @ grp_lid b).
    apply (ap (fun g => g + b)).
    exact (grp_rinv a).
  Defined.

  Definition grp_moveR_gV {G : Group} {a b c : G} :
    a = c + b -> a - b = c.
  Proof.
    intro p.
    apply (grp_cancelR b).
    refine (_ @ p).
    refine (_ @ (grp_rid a)).
    refine ((grp_assoc _ _ _)^ @ _).
    apply (ap (grp_mult a)).
    exact (grp_linv b).
  Defined.

  Definition grp_moveL_Mg {G : Group} {a b c : G} :
    -b + a = c -> a = b + c.
  Proof.
    intro p.
    apply (grp_cancelL (- b)).
    refine (p @ _).
    refine ((grp_lid c)^ @ _).
    refine (_ @ (grp_assoc _ _ _)^).
    apply (ap (fun g => g + c)).
    exact (grp_linv b)^.
  Defined.    
    
  Definition grp_moveL_gM {G : Group} {a b c : G} :
    a - c = b-> a = b + c.
  Proof.
    intro p.
    apply (grp_cancelR (- c)).
    refine (p @ _).
    refine ((grp_rid b)^ @ _).
    refine (_ @ grp_assoc _ _ _).
    apply (ap (grp_mult b)).
    exact (grp_rinv c)^.
  Defined.

  Definition grp_moveL_Vg {G : Group} {a b c : G} :
    b + a = c -> a = -b + c.
  Proof.
    intro p.
    apply (grp_cancelL b).
    refine (p @ _).
    refine ((grp_lid c)^ @ _).
    refine (_ @ (grp_assoc _ _ _)^).
    apply (ap (fun g => g + c)).
    exact (grp_rinv b)^ .
  Defined.    

  Definition grp_moveL_gV {G : Group} {a b c : G} :
    a + c = b -> a = b - c.
  Proof.
    intro p.
    apply (grp_cancelR c).
    refine (p @ _).
    refine ((grp_rid b)^ @ _).
    refine (_ @ grp_assoc _ _ _).
    apply (ap (grp_mult b)).
    exact (grp_linv c)^ .
  Defined.

  Definition grp_moveL_1M {G : Group} {a b : G} :
    a - b = grp_id G -> a = b.
  Proof.
    intro p.
    apply (grp_cancelR (- b)).
    refine (p @ _).
    exact (grp_rinv b)^ .
  Defined.

  Definition grp_moveL_M1 {G : Group} {a b : G} :
    - a + b = grp_id G -> a = b.
  Proof.
    intro p.
    apply (grp_cancelL (- a)).
    refine (_ @ p^).
    exact (grp_linv a).
  Defined.

  Definition grp_moveL_1V {G : Group} {a b : G} :
    a + b = grp_id G -> a = - b.
  Proof.
    intro p.
    apply (grp_cancelR b).
    refine (p @ _).
    exact (grp_linv b)^ .
  Defined.    

  Definition grp_moveL_V1 {G : Group} {a b : G} :
    a + b = grp_id G -> b = - a.
  Proof.
    intro p.
    apply (grp_cancelL a).
    refine (p @ _).
    exact (grp_rinv a)^ .
  Defined.
  
  Definition grp_moveR_M1 {G : Group} {a b : G} :
    grp_id G = -a + b -> a = b.
  Proof.
    intro p.
    apply (grp_cancelL (- a)).
    refine (_ @ p).
    exact (grp_linv a).
  Defined.

  Definition grp_moveR_1M {G : Group} {a b : G} :
    grp_id G = b -a -> a = b.
  Proof.
    intro p.
    apply (grp_cancelR (- a)).
    refine (_ @ p).
    exact (grp_rinv a).
  Defined.

  Definition grp_moveR_1V {G : Group} {a b : G} :
    grp_id G = b + a -> -a = b.
  Proof.
    intro p.
    apply (grp_cancelR a).
    refine (_ @ p).
    exact (grp_linv a).
  Defined.

  Definition grp_moveR_V1 {G : Group} {a b : G} :
    grp_id G = a + b -> -a = b.
  Proof.
    intro p.
    apply (grp_cancelL a).
    refine (_ @ p).
    exact (grp_rinv a).
  Defined.


  Definition inv_id {G : Group} :
    - (grp_id G) = grp_id G.
  Proof.
    apply (grp_cancelL (grp_id G)).
    refine (_ @ (grp_lid _)^).
    exact (grp_rinv _).
  Defined.



  Definition grp_inv_distr {G : Group} (a b: G) :
    - (a + b) = - b - a.
  Proof.
    apply (grp_cancelL (a + b)).
    refine (grp_rinv _ @ _).    
    refine ((grp_rinv a)^ @ _).
    refine (_ @ grp_assoc _ _ _).
    apply (ap (grp_mult a)).
    refine (_ @ (grp_assoc _ _ _)^).
    apply (grp_moveL_gV).
    exact (grp_linv a @ (grp_rinv b)^ ).
  Defined.
    
 
End Group_lemmas.

  
  

Section Homomorphism.
  Open Scope monoid_scope.
  
  Record Homomorphism (M N : Monoid) :=
    {hom_map : M -> N ;
     preserve_id : hom_map (mon_id M) = mon_id N ;
     preserve_mult : forall m1 m2 : M, hom_map (m1 + m2) = (hom_map m1) + (hom_map m2)}. 

  Global Arguments hom_map {M N} h _.
  Global Arguments preserve_id {M N} h.
  Global Arguments preserve_mult {M N} h m1 m2.

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
    Homomorphism L M -> Homomorphism M N -> Homomorphism L N.
  Proof.
    intros f g.
    refine (Build_Homomorphism _ _ ((hom_map g) o (hom_map f)) _ _).
    - exact (ap (hom_map g) (preserve_id f) @ (preserve_id g)).
    - intros m1 m2.
      refine ((ap (hom_map g) (preserve_mult f m1 m2)) @ _).
      exact (preserve_mult g (hom_map f m1) (hom_map f m2)).
  Defined.

  (*A homomorphism of groups preserve inverses*)
  Definition preserve_inv (G H : Group) (f : Homomorphism G H) (a : G) :
    hom_map f (- a) = - (hom_map f a).
  Proof.
    apply (grp_cancelL (hom_map f a)).
    refine ((preserve_mult f _ _)^ @ _).
    refine (ap (hom_map f) (grp_rinv a) @ _).
    refine (preserve_id f @ _).
    exact (grp_rinv _)^.
  Defined.    
End Homomorphism.


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
    revert g1.
    srapply @Coeq_rec.
    - (*Fix first variable*)
      intros [m1 m2].
      srapply @Coeq_rec.
      + (*Fix second variable*)
        intros [n1 n2].
        exact (tr (coeq (m1 + n1, m2 + n2))).
      + (*Second variable runs along cp*)
        intros [[a b] s].
        apply (ap (tr)).
        simpl.
        refine (_ @ cp (m1+a,m2+b,s)).
        apply (ap coeq). unfold as_bs.
        apply path_prod.
        apply mon_assoc. apply mon_assoc.
    - (*First variable runst along cp*)
      intros [[a b] s].
      apply path_forall.
      srapply @Coeq_ind.
      + (*Fix second variable*)
        intros [m1 m2].
        simpl.
        apply (ap tr).
        refine (_ @ cp (a+m1,b+m2,s)).
        apply (ap coeq). unfold as_bs.
        apply path_prod.
        { simpl.
          refine ((mon_assoc a s m1)^ @ _ @ (mon_assoc a m1 s)).
          apply (ap (mon_mult a)).
          apply mon_sym. }
        { refine ((mon_assoc b s m2)^ @ _ @ (mon_assoc b m2 s)).
          apply (ap (mon_mult b)).
          apply mon_sym. }
      + (*Both variables runs along cp*)
        (*This is a 2-path so we just kill it*)
        intro abs'.
        apply (istrunc_truncation 0).
  Defined.
        
(*  Unset Printing Notations.
  Set Printing Implicit. *)
  Definition grp_compl_assoc : associative grp_compl_mult.
    Proof.
      unfold associative.
      srapply @Trunc_ind.
      intro a.
      srapply @Trunc_ind.
      intro b.
      srapply @Trunc_ind.
      intro c. revert a b c.
      srapply @Coeq_ind.
      - (*Fix first variable*)
        intros [l1 l2].
        srapply @Coeq_ind.
        + (*Fix second variable*)
          intros [m1 m2].
          srapply @Coeq_ind.
          * (*Fix third variable*)
            intros [n1 n2].
            simpl.
            apply (ap tr); apply (ap coeq).
            apply path_prod.
            apply mon_assoc. apply mon_assoc.
          * (*Third variable runs along cp*)
            intro abs.
            apply (istrunc_truncation 0).
        + (*Second variable runs along cp*)
          intro abs.
          apply path_forall.
          intro w. apply (istrunc_truncation 0).
      - (*First variable runs along cp*)
        intro abs.
        apply path_forall.
        intro w1.
        apply path_forall.
        intro w2.
        apply (istrunc_truncation 0).
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
      apply path_prod.
      + apply mon_lid.
      + apply mon_lid.
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
      apply path_prod.
      + apply mon_rid.
      + apply mon_rid.
    - (*Variable runs along cp*)
      intro x.
      apply (istrunc_truncation 0).
  Defined.

  Definition grp_compl_sym : symmetric grp_compl_mult.
  Proof.
    srapply @Trunc_ind.
    intro a.
    srapply @ Trunc_ind.
    revert a.
    srapply @Coeq_ind.
    - (*Fix first variable*)
      intros [m1 m2].
      srapply @Coeq_ind.
      + (*Fix second variable*)
        intros [n1 n2].
        apply (ap tr).
        apply (ap coeq).
        apply path_prod.
        apply mon_sym. apply mon_sym.
      + intro abs.
        apply (istrunc_truncation 0).
    - intro abs.
      apply path_forall.
      intro abs'.
      apply (istrunc_truncation 0).
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
      + simpl.
        refine (_ @ (mon_lid (m1+m2))^).
        apply mon_sym.
      + simpl.
        exact (mon_lid (m1+m2))^ .
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
    + (*The variable runs along cp*)
      intros [[a b] s]. simpl.
      refine (ap (fun c => c - (hom_map f (b + s))) (preserve_mult f a s) @ _).
      refine ((mon_assoc _ _ _)^ @ _).
      apply (ap (mon_mult (hom_map f a))).
      apply grp_moveR_gV.
      apply grp_moveL_Vg.
      exact (preserve_mult f b s)^ .
  Defined.

  Definition extend_to_inv {S : Symmetric_Monoid} {A : Abelian_Group} :
    Homomorphism S A -> Homomorphism (group_completion S) A.
  Proof.
    intro f.
    refine (Build_Homomorphism _ _ (hom_map_extend_to_inv f) (grp_rinv _) _).
    (*Preserves multiplication*)
    (*First we need to use Trunc_ind
         This is made difficult by Trunc_ind behaving weirdly. . .*)
    intro m1.
    set (P := fun m2 =>
                hom_map_extend_to_inv f (m1 + m2) =
                hom_map_extend_to_inv f m1 + hom_map_extend_to_inv f m2).
    refine (@Trunc_ind 0 (Coeq (as_bs S) fst) P _ _ ); unfold P; clear P.
    intro aa.
    exact (@trunc_succ -1 _ (mon_isset _ _ _)).
    intro b.
    revert m1.
    set (m2 := tr b : (group_completion S)).
    set (P := fun m1 =>
                hom_map_extend_to_inv f (m1 + m2) =
                hom_map_extend_to_inv f m1 + hom_map_extend_to_inv f m2).
    refine (@Trunc_ind 0 (Coeq (as_bs S) fst) P _ _); unfold P; clear P.
    intro aa.
    exact (@trunc_succ -1 _ (mon_isset _ _ _)).
    unfold m2; clear m2.
    intro a.
    revert a b.
    (*Now the truncations are done with. . .*)
    srapply @Coeq_ind.
    - (*First variable fixed*)
      intros [m1 m2].
      srapply @Coeq_ind.
      (*Second variable fixed.*)
      intros [n1 n2].
      simpl.
      refine ((ap (fun c => c - (hom_map f (m2 + n2))) (preserve_mult f m1 n1)) @ _).
      refine ((mon_assoc _ _ _)^ @ _ @ mon_assoc _ _ _).
      apply (ap (mon_mult (hom_map f m1))).
      refine (ap (fun c => hom_map f n1 -  c) (preserve_mult f m2 n2) @ _).
      refine (ap (fun c => hom_map f n1 + c) (grp_inv_distr _ _)  @ _).
      refine (_ @ grp_sym _ _ _).
      refine (grp_assoc _ _ _).
      (*Second variable runs along cp*)
      intro abs.
      apply (grp_isset A).
    - (*First variable runs along cp*)
      intro abs.
      apply path_forall.
      intro w.
      apply (grp_isset A).
  Defined.

  Theorem grp_compl_adjoint (S : Symmetric_Monoid) (A: Abelian_Group) :
    Homomorphism S A <~> Homomorphism (group_completion S) A.
  Proof.
    refine (equiv_adjointify extend_to_inv (compose_hom (S_to_grpcmplS S)) _ _).
    (*Prove that the maps are inverses*)
    - intro f.
      refine (path_hom _ _ _) ; simpl.
      apply path_forall.
      intro m.
      (*Somehow Trunc_ind works much faster this way. . .*)
      set (P := fun m =>  hom_map_extend_to_inv (compose_hom (S_to_grpcmplS S) f) m = hom_map f m).
      refine (Trunc_ind P _ _); unfold P; clear P.
      + intro aa.
        exact (@trunc_succ -1 _ (mon_isset _ _ _)).
      + srapply @Coeq_ind. 
        * (*Variable fixed*)
          intros [m1 m2].
          simpl.
          apply grp_moveR_gV.
          refine (_ @ preserve_mult f _ _).
          apply (ap (hom_map f)); apply (ap tr).
          refine ((cp (m1, mon_id S, m2))^ @ _); unfold as_bs.
          apply (ap coeq).
          apply (ap (fun s : S => (m1 + m2, s))).
          exact (mon_lid m2 @ (mon_rid m2)^).
        * (*Variable runs along cp*)
          intro abs.
          apply (grp_isset A).
    - intro f.
      refine (path_hom _ _ _) ; simpl.
      apply path_forall.
      intro m.
      apply grp_moveR_gV.
      refine ((grp_rid _)^ @ _).
      apply (ap (fun a : A => hom_map f m + a)).
      exact (preserve_id f)^.
  Defined.

  (*TODO: Define naturality*)

End Adjointness.
    







(*Defining the monoidal type of finite sets and isomorphisms*)
Section FinIso.
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Definition iFin := { S : Type & Finite S }.
  (*ishprop_finite*)

  (*The cardinal of the finite set*)
  Definition cardinal (S : iFin) : nat := @fcard S.1 S.2.

  (*Canonical objects in iFin*)
  Definition fin (n : nat) : iFin := ( Fin n ; finite_fin n ).

  (*Every object is canonical*)
  Lemma canonical_iFin (S : iFin) : merely (S = fin (cardinal S)).
  Proof.
    refine (Trunc_rec (n:=-1) (A := (S.1 <~> Fin (fcard S.1))) _ _).
    - exact S.2.
    - intro e.
      apply tr.
      refine (path_sigma_hprop _ _ _).
      refine (path_universe _).
        apply e. exact _.
    - apply merely_equiv_fin.
  Defined.
  (*Should be possible to choose an isomorphism? *)

  (*The monoidal structure on iFin*)
  Definition FinPlus : iFin-> iFin -> iFin.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (S1 + S2 ; finite_sum _ _).
  Defined.

  (*I feel it should be possible to make a tactic *)
  Definition FinPlus_assoc : associative FinPlus.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2] [S3 fin_S3].
    refine (path_sigma_hprop _ _ _).
    refine (path_universe _).
    apply equiv_sum_assoc. exact _.
  Defined.
  
  Definition FinPlus_leftid : left_identity FinPlus (fin 0).
  Proof.
    intros [S fin_S].
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_l S)).
  Defined.

  Definition FinPlus_rightid : right_identity FinPlus (fin 0).
  Proof.
    intros [S fin_S].
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_r S)).
  Defined.

  Definition FinPlus_symmetric : symmetric FinPlus. 
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (equiv_sum_symm S1 S2)).
  Defined.

  

  

  
  

End FinIso.
    


      
Section Classifying_Space.
  (*Define the classifying space of a monoid as a cell complex*)

  (*The 1-skeleton of B.*)
  Definition B1 (M : Monoid)  := @Coeq M Unit (const tt) (const tt).
  
  (*B1 has one point:*)
  Global Instance ispointed_B1 {M : Monoid} : IsPointed (B1 M) := coeq tt.
  
  (*B1 has one loop for every m : M*)
  Definition B_loop1 {M : Monoid} : M -> point (B1 M) = point (B1 M) := cp.

  Definition B1_rec {M : Monoid}
             (P : Type)
             (bp : P)
             (l : forall m : M, bp = bp) :
    B1 M -> P.
    refine (Coeq_rec P _ _).
    - exact (const bp). (*intros []. exact bp.*)
    - exact l.
  Defined.

  Definition B1_ind {M : Monoid}
             (P : B1 M -> Type) (bp : P (point (B1 M)))
             (loop' : forall (m : M), transport P (B_loop1 m) bp = bp)
             : forall a : B1 M, P a.
  Proof.
    refine (Coeq_ind _ _ _).
    - intros []. exact bp.
    - exact loop'.
  Defined.
  
  Definition looptofill (M : Monoid) (m1 m2 : M) : S1 -> B1 M.
    refine (S1_rec (B1 M) (point (B1 M)) _).
    exact ((B_loop1 m1) @ (B_loop1 m2) @ (B_loop1 (multM m1 m2))^).
  Defined.

  Definition looptofill_curried (M : Monoid) : M*M*S1 -> B1 M :=
    prod_curry (prod_curry (looptofill M)).  
  
  Definition S1toB1 {M : Monoid} (m1 m2 : M) : S1 -> B1 M :=
    looptofill M m1 m2.

  Definition collapseS1 (M : Monoid) : M*M*S1 -> M*M.
    intros [[m1 m2] x].
    exact (m1, m2).
  Defined. 

  (*Construct 2-cells*)
  Definition B2 (M : Monoid) := pushout
                                  (looptofill_curried M)
                                  (collapseS1 M).

  Definition ispointed_MMS1 {M : Monoid} : IsPointed (M * M * S1) := (mon_id M, mon_id M, base).
  
(*  (*Not sure if this is needed. . .*)
  Definition path_to_other_pt {M : Monoid} (x : M * M * S1) : pushl x = point (B2 M) := pp x. *)

  Definition B1toB2 {M : Monoid} : B1 M -> B2 M := (push o inl).

  Global Instance ispointed_B2 {M : Monoid} : IsPointed (B2 M) := B1toB2 ispointed_B1.
  (*  Definition otherpt_B2 {M : Monoid} (m1 m2 : M) : B2 M := push (inr (m1, m2)).
  Definition path_to_otherpt_B2 {M : Monoid} (m1 m2 : M) : point (B2 M) = otherpt_B2 m1 m2 :=
    pp (m1, m2, base). *)

  Definition B_loop2 {M : Monoid} (m : M) : point (B2 M) = point (B2 M) :=
    ap B1toB2 (B_loop1 m).

(*  Definition nullhom_S1toB2' {M : Monoid} (m1 m2 : M) :
    B1toB2 o (S1toB1 m1 m2) == const (otherpt_B2 m1 m2).
  Proof.
    intro x.
    exact (pp (m1, m2, x)).
  Defined. *)

  Definition nullhom_S1toB2 {M : Monoid} (m1 m2 : M) :
    B1toB2 o (S1toB1 m1 m2) == (fun _ : S1 => B1toB2 (S1toB1 m1 m2 base)) .
  Proof.
    intro x.
    refine (concat (pp (m1, m2, x)) _).
    exact (pp (m1, m2, base))^. (*Weirdly enough, putting this inside the concat doesn't work. . .*)
  Defined.


  Definition const_S1toB2 `{Funext} {M : Monoid} (m1 m2 : M) :
    B1toB2 o (S1toB1 m1 m2) = (fun _ : S1 => B1toB2 (S1toB1 m1 m2 base)) :=
    path_forall _ _ (nullhom_S1toB2 m1 m2).

  

  Definition isHom_MtoB2 `{Funext} {M : Monoid} (m1 m2: M) :
     B_loop2 m1 @ B_loop2 m2 = B_loop2 (multM m1 m2).
  Proof.
    unfold B_loop2.
    apply moveL_1M.
    path_via (ap B1toB2 (ap (S1toB1 m1 m2) loop)).
    - path_via (ap B1toB2 ( (B_loop1 m1) @ (B_loop1 m2) @ (B_loop1 (multM m1 m2))^)).
      + refine (concat _ (ap_pp _ _ _)^).
        apply concat2.
        * refine (ap_pp _ _ _)^.
        * refine (ap_V B1toB2 _)^ .
      + 
        apply ap.
        unfold S1toB1.
        refine (S1_rec_beta_loop _ _ _)^. 
    - refine (concat (ap_compose _ _ _)^ _).
      refine (concat _ (ap_const loop _)). 
      refine (concat _ (ap12 loop (const_S1toB2 m1 m2))).
      rewrite ap_compose.
      rewrite concat_pp_p.
      apply moveL_Vp.
      unfold S1toB1.
      unfold looptofill.
      rewrite S1_rec_beta_loop.      
      unfold const_S1toB2.
      rewrite (path_forall _ _ (ap10_path_forall _ _ _)).
      unfold nullhom_S1toB2.
      hott_simpl.
  Qed.
                          

  Definition B2_rec {M : Monoid}
             (P : Type)
             (bp : P)
             (l : M -> bp = bp)
             (h : forall m1 m2 : M, l m1 @ l m2 = l (multM m1 m2) ) :
    B2 M -> P.
    (*B2 is the pushout of B1 M and M*M*S1*)
    refine (pushout_rec P _ _).
    - apply sum_rect.      
      + (*The map defined on B1 is given by l*)
        refine (B1_rec _ bp _).
        exact l.
        (*The map on M*M*S1 is the constant map (it gives the loops that will be killed)*)
      + exact (const bp).
    - (*Show that the map is well-defined, e.g. m1@m2=m1*m2 *)
      simpl.
      intros [[m1 m2]].
      unfold const.      
      unfold looptofill_curried.
      unfold prod_curry.
      simpl.
      unfold looptofill.
      refine (S1_ind _ _ _ ).
      + exact idpath.
      + refine (concat (transport_paths_Fl loop idpath) _).
        hott_simpl.        (*TODO: Make this transparent?*)
        unfold B1_rec.
        rewrite ap_compose.
        rewrite S1_rec_beta_loop.
        rewrite <- (inv_V idpath).
        apply inverse2.
        rewrite ap_pp.
        rewrite ap_pp.
        unfold B_loop1.
        (*Somehow, rewrite Coeq_rec_beta_cp doesn't work here. . .*)
        rewrite ap_V.
        apply moveR_pV.
        refine (concat (y := l (multM m1 m2)) _ _).
        refine (concat (y := l m1 @ l m2) _ _).
        apply concat2.
        exact (Coeq_rec_beta_cp P (const bp) l m1).
        exact (Coeq_rec_beta_cp P (const bp) l m2).
        exact (h m1 m2).        
        hott_simpl.
        exact (Coeq_rec_beta_cp P (const bp) l (multM m1 m2))^.
  Qed.
        
        
      

   
  
   Definition B2_ind {M : Monoid}
             (P : B2 M -> Type)
             (bp : P (point (B2 M)))
             (l : forall (m : M), transport P (B_loop2 m) bp = bp)
             (h : forall (m1 m2 : M),
                    ap (transport P (B_loop2 m2)) (l m1) @ (l m2) = l (multM m1 m2) )
                        (* transport P (B_loop2 m1) (transport P (B_loop2 m2) bp) *)
                        (* = transport P (B_loop2 (multM m1 m2)) bp ) (*Not right*) *)
             : forall a : B2 M, P a.
    refine (pushout_ind _ _ _ _ _).
    - apply sum_ind.
      + refine (B1_ind _ _ _).
        * exact bp.
        * intro m.
          refine (concat
                    (transport_compose P (push o inl)
                                       (B_loop1 m)
                                       bp )
                    _
                 ).
          apply ident.
      + intros [m1 m2].
        exact (transport P (pp (m1, m2, base)) bp).
    - intros [[m1 m2]].
      refine (S1_ind _ _ _).
      + exact idpath.
      + cbn.
        refine (concat
                  (transport_paths_Fl loop idpath)
                  _
               ).
        apply moveR_Vp.
        refine (concat _ (concat_p1 _)^).
        apply inverse.
        unfold looptofill.
        

          
        unfold B_loop1.

        refine (concat
                  (ap_compose
                     (S1_rec (B1 M) (point (B1 M))
                             ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (multM m1 m2))^) )
                      _ loop
                  )
                  _ ).
        
               
                  
        unfold B1_ind.
        
        

   Admitted.


(*TODO: Use ap11. ap_apply_FlFr ap_to_conjp transport2
*)

(*TODO*) (*
  Global Instance ispointed_S1 : IsPointed S1 := base.
  Definition pS1 := Build_pType S1 _.
  Definition pB1 (M : Monoid) := Build_pType (B1 M) _.
  Definition pB2 (M : Monoid) := Build_pType (B2 M) _.
  Definition pS1toB1 {M : Monoid} (m1 m2 : M) :=
    Build_pMap pS1 (pB1 M) (S1toB1 m1 m2) idpath.
  Definition pB1toB2 {M : Monoid} (m1 m2 : M) : pB1 M ->* pB2 M :=
    Build_pMap (pB1 M) (pB2 M) (B1toB2) idpath.
 
  Lemma pconst_S1toB2 `{Funext} (M : Monoid) (m1 m2 : M) :
    (pB1toB2 m1 m2) o* (pS1toB1 m1 m2) = pconst pS1 (pB2 M).
  Proof.
    apply path_pmap.
    refine (Build_pHomotopy _ _).
    intro x.
    simpl.
    unfold const. unfold point. unfold ispointed_B2. unfold B1toB2. unfold ispointed_B1.
    refine (concat _ (pp ispointed_MMS1)^).
    apply (constant_S1toB2 x).
    - cbn.
      unfold constant_S1toB2.
      hott_simpl.
      apply moveR_pV.
      hott_simpl.
      unfold ispointed_MMS1.
      unfold ispointed_S1.
      
      apply (concat (concat_p1 _) (concat_1p _)^ ).
  Defined.

  Definition pmap_to_loops {A B : pType} (l : loops A) :
    (A ->* B) -> loops B :=
    fun f => (point_eq f)^ @ (ap f l) @ (point_eq f).

  (*TODO: Use this to make the proof below simpler?*)
*)
  
  Definition monid_to_idpath2 `{Funext} {M : Monoid} : B_loop2 (mon_id M) = idpath.
    apply (cancelL (B_loop2 (mon_id M)) _ _).
    refine (concat (isHom_MtoB2 _ _)^ _).
    refine (concat _ (concat_p1 _)^).
    apply (ap B_loop2).
    apply mon_lid.
  Defined.

  Definition B (M : Monoid) := Tr 1 (B2 M).

  Global Instance ispointed_B {M : Monoid} : IsPointed (B M) := tr (point (B2 M)).

  Definition B_loop {M : Monoid} (m : M) : point (B M) = point (B M) := ap tr (B_loop2 m).
  Definition isHom_MtoB `{Funext} {M : Monoid} (m1 m2: M) :
    (B_loop (multM m1 m2)) = ((B_loop m1) @ (B_loop m2)).
    refine (concat _ (ap_pp tr _ _)).
    apply (ap (ap tr)).
    apply isHom_MtoB2.
  Defined.

  Definition monid_to_idpath `{Funext} {M : Monoid} : B_loop (mon_id M) = idpath.
    unfold B_loop.
    refine (concat _ (ap_1 _ tr)).
    apply (ap (ap tr)).
    apply monid_to_idpath2.
  Defined.

  Definition B_rec {M : Monoid}
             (P : Type) (istrunc : IsTrunc 1 P)
             (bp : P)
             (loop' : forall m : M, bp = bp)
             (ishom : forall m1 m2 : M, loop' (multM m1 m2) = loop' m1 @ loop' m2) : B M -> P.
  Proof.
    apply Trunc_rec.
    refine (pushout_rec _ _ _).
    - apply sum_rect.
      + (*What B1 is mapped to*)
        refine (Coeq_rec _ _ _).
        * exact (unit_name bp).
        * exact loop'.
      + exact (unit_name bp). (*
        apply Unit_rec.
        exact bp.*)
    - (*This corresponds to showing that we have a homomorphism*)
      intros [[m1 m2]].
      refine (S1_ind _ idpath _).
      refine (concat (transport_paths_Fl loop idpath) _).
      apply moveR_Vp.
      refine (concat _ (concat_p1 _)^).
      refine (concat _
              (ap_compose
               (S1_rec (B1 M) (point (B1 M)) ((B_loop1 m1 @ B_loop1 m2) @ (B_loop1 (multM m1 m2))^))
               (Coeq_rec P (unit_name bp) loop')
               loop )^
             ).
      refine (concat _
                     (ap
                        (ap (Coeq_rec P (unit_name bp) loop'))
                        (S1_rec_beta_loop _ _ _)^
                      )).
      refine (concat _ (ap_pp _ _ _)^).
      apply moveL_pM.
      refine (concat (concat_1p _) _).
      refine (concat (ap_V _ _)^ _).
      refine (concat (ap
                        (ap (Coeq_rec P (unit_name bp) loop'))
                        (inv_V (B_loop1 (multM m1 m2)))
                      ) _ ).      
      refine (concat (Coeq_rec_beta_cp P (unit_name bp) loop' (multM m1 m2)) _).
      refine (concat _ (ap_pp _ _ _)^).
      refine (concat (ishom m1 m2) _).
      apply concat2.
      + exact (Coeq_rec_beta_cp P (unit_name bp) loop' m1)^.
      + exact (Coeq_rec_beta_cp P (unit_name bp) loop' m2)^.
  Defined.

  Definition B_ind {M : Monoid}
             (P : B M -> Type) (istrunc : forall (a : B M), IsTrunc 1 (P a))
             (bp : P (point (B M)))
             (loop' : forall (m : M), transport P (B_loop m) bp = bp)
             
             : forall a : B M, P a.
    apply Trunc_ind.
    exact istrunc.
    refine (pushout_ind _ _ _ _ _).
    - apply sum_ind.
      + refine (B1_ind _ _ _).
        * exact (transport (P o tr) (pp ispointed_MMS1)^ bp).
        * intro m.
          refine (concat
                    (transport_compose (P o tr) (push o inl)
                                       (B_loop1 m)
                                       (transport (P o tr) (pp ispointed_MMS1)^ bp) )
                    _
                 ).

          refine (concat (transport_pp _ _ _ _)^ _).
          refine (moveL_transport_V (P o tr) _ _ _ _).
          refine (concat (transport_pp _ _ _ _)^ _).
          refine (concat
                    (transport_compose P tr _ _)
                    _ ).
          apply loop'.
      + intros []. exact bp.
    - simpl.
      intros [[m1 m2]].
      refine (S1_ind _ _ _).
      + simpl.
        change (pushout looptofill (const tt)) with (B2 M).
        refine (moveR_transport_p (P o tr) _ _ _ _).
        refine (concat
                  (transport_compose P tr _ _)
                  _ ).
        refine (concat
                  _
                  (transport_compose P tr _ _)^ ).
        apply transport2.
        apply (ap (ap tr)).

  Admitted.        
        

    
  
End Classifying_Space.



Section B2_coeq.
  Definition l12 {M : Monoid} : M * M * S1 -> B1 M.
    intros [[m1 m2]].
    refine (S1_rec (B1 M) (point _) _).
    exact (B_loop1 (multM m1 m2)).
  Defined.

  Definition l1l2 {M : Monoid} : M * M * S1 -> B1 M.
    intros [[m1 m2]].
    refine (S1_rec (B1 M) (point _) _).
    exact ((B_loop1 m1) @ (B_loop1 m2)).
  Defined.

  Definition l12_beta {M : Monoid} (m1 m2 : M) :
    ap (fun x : S1 => l12 (m1, m2, x)) loop = B_loop1 (multM m1 m2) := S1_rec_beta_loop _ _ _.

  Definition l1l2_beta {M : Monoid} (m1 m2 : M) :
    ap (fun x : S1 => l1l2 (m1, m2, x)) loop = ((B_loop1 m1) @ (B_loop1 m2)) := S1_rec_beta_loop _ _ _.
  
  Definition B2' (M : Monoid) := Coeq (@l12 M) l1l2.

  Definition B1toB2' {M : Monoid} : B1 M -> B2' M := coeq.
  Global Instance ispointed_B2' {M : Monoid} : IsPointed (B2' M) := B1toB2' (point (B1 M)).
    
  (*TODO: Bruke transport i stedet?*)
  Definition B_loop2' {M : Monoid} (m : M) : point (B2' M) = point (B2' M) :=  ap B1toB2' (B_loop1 m).

  Definition isHom_MtoB2' `{Funext} {M : Monoid} (m1 m2: M) :
    (B_loop2' (multM m1 m2)) = ((B_loop2' m1) @ (B_loop2' m2)).
  Proof.
    unfold B_loop2'.
    refine (concat _ (ap_pp B1toB2' _ _) ).
    rewrite <- (l12_beta m1 m2).
    rewrite <- (l1l2_beta m1 m2).
    refine (concat (ap_compose (fun x : S1 => l12 (m1, m2, x)) B1toB2' loop)^ _ ).
    refine (concat  _ (ap_compose (fun x : S1 => l1l2 (m1, m2, x)) B1toB2' loop)).
    
    change (B_loop1 (multM m1 m2)) with 
    unfold B_loop1.
    
    unfold B1toB2'.
    

    

(*Prove that B nat <~> Int*)
Section Classifying_Space_Nat.
  Definition BN := B (nat_monoid).

  (*Bruke equiv_loopsS1_int ?*)

  Definition lBN_to_Z : loops (Build_pType BN _) -> Int.
Abort.
(*    Sn_trunctype:
  Univalence -> forall n : trunc_index, IsTrunc n.+1 {x : _ & IsTrunc n x}
   path_sigma_uncurried
   hprop_trunc
   trunc_arrow
 *)

    refine (paths_rec (point (BN)) (fun _ => Int) Int.zero _). (*This is constant. P must be a bit more refined. loop => +1 : Z=Z*)























    (fun m1 => forall m2 : Trunc 0 (Coeq (as_bs S) fst),
                                       Trunc_rec
                                         (Coeq_rec (mon_set (grp_mon (grp A)))
                                                   (fun m12 : mon_set (mon S) * mon_set (mon S) =>
                                                      mon_map f (fst m12) + grp_inv (mon_map f (snd m12)))
                                                   (fun b : mon_set (mon S) * mon_set (mon S) * mon_set (mon S) =>
                                                      ap
                                                        (fun c : mon_set (grp_mon (grp A)) =>
                                                           c +
                                                           grp_inv
                                                             (mon_map f
                                                                      ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                       (let (_, snd) := b in snd))))
                                                        (preserve_mult f (let (fst, _) := let (fst, _) := b in fst in fst)
                                                                       (let (_, snd) := b in snd)) @
                                                        ((mon_assoc
                                                            (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst))
                                                            (mon_map f (let (_, snd) := b in snd))
                                                            (grp_inv
                                                               (mon_map f
                                                                        ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                         (let (_, snd) := b in snd)))))^ @
                                                                                                           ap
                                                                                                           (mon_mult
                                                                                                              (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst)))
                                                                                                           (grp_moveR_gV
                                                                                                              (grp_moveL_Vg
                                                                                                                 (preserve_mult f
                                                                                                                                (let (_, snd) := let (fst, _) := b in fst in snd)
                                                                                                                                (let (_, snd) := b in snd))^)))))
                                         (grp_compl_mult S m1 m2) =
                                       Trunc_rec
                                         (Coeq_rec (mon_set (grp_mon (grp A)))
                                                   (fun m12 : mon_set (mon S) * mon_set (mon S) =>
                                                      mon_map f (fst m12) + grp_inv (mon_map f (snd m12)))
                                                   (fun b : mon_set (mon S) * mon_set (mon S) * mon_set (mon S) =>
                                                      ap
                                                        (fun c : mon_set (grp_mon (grp A)) =>
                                                           c +
                                                           grp_inv
                                                             (mon_map f
                                                                      ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                       (let (_, snd) := b in snd))))
                                                        (preserve_mult f (let (fst, _) := let (fst, _) := b in fst in fst)
                                                                       (let (_, snd) := b in snd)) @
                                                        ((mon_assoc
                                                            (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst))
                                                            (mon_map f (let (_, snd) := b in snd))
                                                            (grp_inv
                                                               (mon_map f
                                                                        ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                         (let (_, snd) := b in snd)))))^ @
                                                                                                           ap
                                                                                                           (mon_mult
                                                                                                              (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst)))
                                                                                                           (grp_moveR_gV
                                                                                                              (grp_moveL_Vg
                                                                                                                 (preserve_mult f
                                                                                                                                (let (_, snd) := let (fst, _) := b in fst in snd)
                                                                                                                                (let (_, snd) := b in snd))^))))) m1 +
                                       Trunc_rec
                                         (Coeq_rec (mon_set (grp_mon (grp A)))
                                                   (fun m12 : mon_set (mon S) * mon_set (mon S) =>
                                                      mon_map f (fst m12) + grp_inv (mon_map f (snd m12)))
                                                   (fun b : mon_set (mon S) * mon_set (mon S) * mon_set (mon S) =>
                                                      ap
                                                        (fun c : mon_set (grp_mon (grp A)) =>
                                                           c +
                                                           grp_inv
                                                             (mon_map f
                                                                      ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                       (let (_, snd) := b in snd))))
                                                        (preserve_mult f (let (fst, _) := let (fst, _) := b in fst in fst)
                                                                       (let (_, snd) := b in snd)) @
                                                        ((mon_assoc
                                                            (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst))
                                                            (mon_map f (let (_, snd) := b in snd))
                                                            (grp_inv
                                                               (mon_map f
                                                                        ((let (_, snd) := let (fst, _) := b in fst in snd) +
                                                                         (let (_, snd) := b in snd)))))^ @
                                                                                                           ap
                                                                                                           (mon_mult
                                                                                                              (mon_map f (let (fst, _) := let (fst, _) := b in fst in fst)))
                                                                                                           (grp_moveR_gV
                                                                                                              (grp_moveL_Vg
                                                                                                                 (preserve_mult f
                                                                                                                                (let (_, snd) := let (fst, _) := b in fst in snd)
                                                                                                                                (let (_, snd) := b in snd))^))))) m2
                          )