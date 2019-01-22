Require Import UnivalenceAxiom.
Load group_complete_1type.
(* Load monoidal_1type. *)


Section Monoids_and_Groups.
  (* Definition associative {A : Type}  (m : A->A->A) := forall a b c : A, m a (m b c) = m (m a b) c. *)
  (* Definition left_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m e a = a. *)
  (* Definition right_identity {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a. *)
  (* Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a. *)
  Definition left_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) :=
    forall a : A, m (inv a) a = e.
  Definition right_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) :=
    forall a : A, m a (inv a) = e.


  Record Monoid : Type := { mon_set :> hSet;
                            (* mon_isset : IsHSet mon_set; *)
                            mon_mult  : mon_set->mon_set->mon_set;
                            mon_id : mon_set;
                            mon_assoc : associative mon_mult;
                            mon_lid : left_identity_mult mon_mult mon_id ;
                            mon_rid : right_identity_mult mon_mult mon_id
                          }.

  (* Definition type_to_monoid : Monoidal_1Type -> Monoid. *)
  (* Proof. *)
  (*   intro M. *)
  (*   srapply (Build_Monoid (BuildTruncType 0 (Trunc 0 M))). *)
  (*   simpl. *)
  (*   (@mon_mult M)). *)
    

  Definition monoid_to_1type : Monoid -> Monoidal_1Type.
  Proof.
    intro M.
    srapply
      (Build_Monoidal_1Type (BuildTruncType 1 M)
                            (mon_mult M) (mon_id M) (mon_assoc M) (mon_lid M) (mon_rid M)).
    - intros a b. apply (istrunc_trunctype_type M).
    - intros a b. apply (istrunc_trunctype_type M).
    - intros a b c d. apply (istrunc_trunctype_type M).
  Defined.

  Coercion monoid_to_1type : Monoid >-> Monoidal_1Type.
  

  Record Symmetric_Monoid : Type := {mon :> Monoid;
                                     mon_sym : symmetric (mon_mult mon) }.
  Global Arguments mon_sym {S} {a} {b} :rename.

  (* (*Makes mon_isset an implicit argument*) *)
  (* Global Arguments Build_Monoid mon_set {mon_isset} mon_mult mon_id mon_assoc mon_lid mon_rid. *)

  Global Arguments mon_id {M} : rename.
  Global Arguments mon_mult {M} a b : rename.
  Global Arguments mon_assoc {M} {a} {b} {c} : rename.
  Global Arguments mon_lid {M} a : rename.
  Global Arguments mon_rid {M} a : rename.

  

  Global Instance ispointed_M {M : Monoid} : IsPointed M := (@mon_id M).

(*  (*Formulate the cancellation law for a monoid*)
  Definition right_cancellation_law (M : Monoid) :=
    forall a b s : M, a + s = b + s -> a = b.   *)
  
  Record Group : Type := {grp_mon :> Monoid;
                          grp_inv : grp_mon -> grp_mon;
                          grp_linv : left_inverse mon_mult (mon_id) grp_inv;
                          grp_rinv : right_inverse mon_mult (mon_id) grp_inv
                         }.
  
  Global Arguments grp_inv {G} a :rename.
  Global Arguments grp_linv {G} a:rename.
  Global Arguments grp_rinv {G} a:rename.

  Record Abelian_Group : Type :=
    {grp :> Group;
     grp_sym : symmetric (@mon_mult (grp_mon grp))}.

  Global Arguments grp_sym {A} {a} {b} : rename.

  (*Must do some work to get a coercion Abelian_Group >-> Symmetric_Monoid*)
  Definition forget_to_SymMon : Abelian_Group -> Symmetric_Monoid :=
    fun A => Build_Symmetric_Monoid A (@grp_sym A).

  Coercion forget_to_SymMon : Abelian_Group >-> Symmetric_Monoid.    

End Monoids_and_Groups.

                                     

Section nat_monoid.
  Require Import nat_lemmas.
  (*Strangely, I cannot find any proofs of nat being associative*)
  Open Scope nat_scope.
  (* Definition plus_assoc : associative Peano.plus. *)
  (*   intros j k l. *)
  (*   induction j, k, l. *)
  (*   - exact idpath. *)
  (*   - exact idpath. *)
  (*   - exact idpath. *)
  (*   - exact idpath. *)
  (*   - exact (ap S IHj). *)
  (*   - exact (ap S IHj). *)
  (*   - exact (ap S IHj). *)
  (*   - exact (ap S IHj). *)
  (* Defined. *)
  
  Definition nat_monoid : Monoid :=
    Build_Monoid
      (BuildhSet nat) Peano.plus O
      plus_assoc (fun _ => idpath) (fun n => (nat_plus_n_O n)^).
  Close Scope nat_scope.

  Definition nat_symm_monoid : Symmetric_Monoid := Build_Symmetric_Monoid nat_monoid nat_plus_comm.    
End nat_monoid.

Infix "+" := mon_mult : monoid_scope.
(* Notation "a + b"  := (mon_mult a b) : monoid_scope. *)
Notation "- a" := (grp_inv a) : monoid_scope.
Notation "a - b" := (mon_mult a (grp_inv b)) : monoid_scope.

(*Just so that you dont have to remember what is monoid structure and what is group structure *)
(* Notation "grp_set G" := (mon_set (grp_mon G)) (at level 0) : monoid_scope. *)
(* Notation "grp_isset G" := (mon_isset (grp_mon G)) (at level 0) : monoid_scope. *)
Notation "'grp_id' G" := (@mon_id (grp_mon G)) (at level 0) : monoid_scope.
Notation "'grp_mult'" := (@mon_mult (grp_mon _)) (at level 0, only parsing) : monoid_scope.
Notation "'grp_assoc'" := (mon_assoc ( M := grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_lid'" := (@mon_lid (grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_rid'" := (@mon_rid (grp_mon _)) (at level 0) : monoid_scope.
Notation "'grp_rid'" := (@mon_rid (grp_mon _)) (at level 0) : monoid_scope.
(*TODO: Use this notation*)



Section Loop_is_group.
  Definition loopGroup (A : pType) {istrunc_A : IsTrunc 1 A} : Group.
    srapply Build_Group.
    exact (Build_Monoid (BuildhSet (loops A)) concat idpath concat_pp_p concat_1p concat_p1).
    - exact inverse.
    - exact concat_Vp.
    - exact concat_pV.
  Defined.
End Loop_is_group.

Section Group_lemmas.
  Open Scope monoid_scope.
  Context {G : Group}.
  Definition grp_whiskerL {a b c : G} : b = c -> a + b = a + c
    := ap (fun g => a + g).

  Definition grp_whiskerR {a b c : G} : a = b -> a + c = b + c
    := ap (fun g => g + c).
  
  Definition grp_cancelR {a b : G} (s : G) :
    a + s = b + s -> a = b.
  Proof.
    intro p.      
    refine ((grp_rid a)^ @ _ @ grp_rid b).
    refine ((grp_whiskerL (grp_rinv s))^ @ _ @ grp_whiskerL (grp_rinv s)).
    refine ((grp_assoc)^ @ _ @ (grp_assoc )).
    exact (grp_whiskerR p).
  Defined.
  
  Definition grp_cancelL {a b} (s : G) :
    s + a = s + b -> a = b.
  Proof.
    intro p.
    refine ((grp_lid a)^ @ _ @ grp_lid b).
    refine ((grp_whiskerR (grp_linv s))^ @ _ @ grp_whiskerR (grp_linv s)).
    refine (grp_assoc @ _ @ grp_assoc^).
    exact (grp_whiskerL p).
  Defined.

  Definition grp_moveR_Mg {a b c : G} :
    b = -a + c -> a + b = c.
    Proof.
      intro p.
      refine (grp_whiskerL p @ _).
      refine (grp_assoc^ @ _).
      refine (grp_whiskerR (grp_rinv a) @ _).
      exact (grp_lid c).
    Defined.

  Definition grp_moveR_gM {a b c : G} :
    a = c - b -> a + b = c.
    Proof.
      intro p.
      refine (grp_whiskerR p @ _).
      refine (grp_assoc @ _).
      refine (grp_whiskerL (grp_linv b) @ _).
      exact (grp_rid c).
    Defined.      

  Definition grp_moveR_Vg {a b c : G} :
    b = a + c -> - a + b = c.
  Proof.
    intro p.
    refine (grp_whiskerL p @ _).
    refine (grp_assoc^ @ _).
    refine (grp_whiskerR (grp_linv a) @ _).
    exact (grp_lid c).
  Defined.

  Definition grp_moveR_gV {a b c : G} :
    a = c + b -> a - b = c.
  Proof.
    intro p.
    refine (grp_whiskerR p @ _).
    refine (grp_assoc @ _).
    refine (grp_whiskerL (grp_rinv b) @ _).
    exact (grp_rid c).
  Defined.

  Definition grp_moveL_Mg {a b c : G} :
    -b + a = c -> a = b + c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerL p).
    refine (_ @ grp_assoc).
    refine (_ @ grp_whiskerR (grp_rinv b)^).
    exact (grp_lid a)^.
  Defined.    
    
  Definition grp_moveL_gM {a b c : G} :
    a - c = b-> a = b + c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerR p).
    refine (_ @ grp_assoc^).
    refine (_ @ grp_whiskerL (grp_linv c)^).
    exact (grp_rid a)^.
  Defined.

  Definition grp_moveL_Vg {a b c : G} :
    b + a = c -> a = -b + c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerL p).
    refine (_ @ grp_assoc ).
    refine (_ @ grp_whiskerR (grp_linv b)^).
    exact (grp_lid a)^.
  Defined.    

  Definition grp_moveL_gV {a b c : G} :
    a + c = b -> a = b - c.
  Proof.
    intro p.
    refine (_ @ grp_whiskerR p).
    refine (_ @ grp_assoc^ ).
    refine (_ @ grp_whiskerL (grp_rinv c)^).
    exact (grp_rid a)^.
  Defined.

  Definition grp_moveL_1M {a b : G} :
    a - b = grp_id G -> a = b.
  Proof.
    intro p.
    refine (grp_moveL_gM  p @ _).
    exact (grp_lid b).
  Defined.

  Definition grp_moveL_M1 {a b : G} :
    - a + b = grp_id G -> a = b.
  Proof.
    intro p.
    refine (_ @ (grp_moveL_Mg p)^).
    exact (grp_rid a)^ .
  Defined.

  Definition grp_moveL_1V {a b : G} :
    a + b = grp_id G -> a = - b.
  Proof.
    intro p.
    refine (grp_moveL_gV p @ _).
    exact (grp_lid (- b)).
  Defined.

  Definition grp_moveL_V1 {a b : G} :
    a + b = grp_id G -> b = - a.
  Proof.
    intro p.
    refine (grp_moveL_Vg p @ _).
    exact (grp_rid (-a)).
  Defined.
  
  Definition grp_moveR_M1 {a b : G} :
    grp_id G = -a + b -> a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_Mg p).
    exact (grp_rid a)^ .
  Defined.

  Definition grp_moveR_1M {a b : G} :
    grp_id G = b -a -> a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_gM p).
    exact (grp_lid a)^ .
  Defined.

  Definition grp_moveR_1V {a b : G} :
    grp_id G = b + a -> -a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_gV p).
    exact (grp_lid (-a))^ .
  Defined.

  Definition grp_moveR_V1 {a b : G} :
    grp_id G = a + b -> -a = b.
  Proof.
    intro p.
    refine (_ @ grp_moveR_Vg p).
    exact (grp_rid (-a))^ .
  Defined.

  Definition inv_id : - (grp_id G) = grp_id G
    := grp_moveR_1V (grp_rid _)^ .

  Definition grp_inv_distr {a b: G} :
    - (a + b) = - b - a.
  Proof.
    apply grp_moveL_Vg.
    apply grp_moveR_gV.
    refine (_ @ grp_assoc).
    refine ( _ @ (grp_whiskerR (grp_linv a)^ ) ).
    exact (grp_lid b)^ .
  Defined.

  Definition path_group2 {a b c d : G} : a = c -> b = d -> a + b = c + d
    := fun p q => grp_whiskerL q @ grp_whiskerR p.

  Definition isequiv_grp_mult (g : G) :
    IsEquiv (fun a => a + g).
  Proof.
    srapply @isequiv_adjointify.
    - exact (fun a => a - g).
    - intro a. apply grp_moveR_gM. reflexivity.
    - intro a. apply grp_moveR_gV. reflexivity.
  Defined.

  Definition grp_mult_equiv (g : G) : G <~>G :=
    BuildEquiv G G (fun a => a+ g) (isequiv_grp_mult g).
  
End Group_lemmas.

Section Homomorphism.
  Open Scope type_scope.
  Open Scope monoid_scope.
  
  Record Homomorphism (M N : Monoid) :=
    {hom_map : M -> N ;
     preserve_id : hom_map (mon_id) = mon_id ;
     preserve_mult : forall m1 m2 : M, hom_map (m1 + m2) = (hom_map m1) + (hom_map m2)}. 

  Global Arguments hom_map {M N} h _.
  Global Arguments preserve_id {M N} h.
  Global Arguments preserve_mult {M N} h {m1} {m2}.

  Coercion hom_map : Homomorphism >-> Funclass.

  Definition ishom {M N : Monoid} (f : M -> N) :=
    (f (mon_id) = mon_id) * (forall m1 m2 : M, f (m1 + m2) = f m1 + f m2).
      

  Definition issig_hom (M N : Monoid) :
    {f : M -> N &  ishom f} <~> Homomorphism M N.
  Proof.
    equiv_via {f : M -> N &
                          sig (fun _ : (f (mon_id) = mon_id) =>
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
    set (A := (f (mon_id) = mon_id)).
    set (B := (forall m1 m2 : mon_set M, f (m1 + m2) = f m1 + f m2)).
    refine (@trunc_prod -1 A _ B _).
    exact (istrunc_trunctype_type N _ _).
    unfold B; clear A; clear B.
    set (P := fun m1 : mon_set M => forall m2, f (m1 + m2) = f m1 + f m2).
    refine (@trunc_forall _ (mon_set M) P -1 _).
    intro m1.
    unfold P; clear P.
    set (P := fun m2 : mon_set M =>
                f (m1 + m2) = f m1 + f m2).
    refine (@trunc_forall _ _ P -1 _).
    intro m2; unfold P; clear P.
    exact (istrunc_trunctype_type N _ _).
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



(* (* Defining sets with a monoid action (see MacLane, p5) *) *)
(* Section Monoid_action. *)
(*   Open Scope monoid_scope. *)
(*   Record Monoid_Action (M : Monoid) (X : hSet) := {function_of : M -> (X -> X); *)
(*                                                    assoc_function_of : forall (m1 m2 : M) (x : X), *)
(*                                                        function_of m1 (function_of m2 x) = function_of (m1 + m2) x; *)
(*                                                    preserve_id_function_of : forall x : X, *)
(*                                                        function_of (mon_id M) x = x *)
(*                                                   }. *)
(*   Arguments function_of {M} {X} _ _ _. *)
(*   Definition product_action (M : Monoid) : Monoid_Action M (BuildhSet (M*M)). *)
(*   Proof. *)
(*     srapply (@Build_Monoid_Action). *)
(*     (* The action *) *)
(*     - intro m. *)
(*       intros [a b]. *)
(*       exact (m + a, m + b). *)
(*     - intros m1 m2 [x1 x2]. *)
(*       apply path_prod; apply mon_assoc. *)
(*     - intros [x1 x2]. apply path_prod; apply mon_lid. *)
(*   Defined. *)

(*   (* [S X] *) *)
(*   (* The quotient X/~, where x ~ y if there is a s : S s.t. s + x = y *) *)
(*   Definition grp_compl_relation {M : Monoid} (X : hSet) (a : Monoid_Action M X) : relation X *)
(*     := (fun x y => {m : M | function_of a m x = y}). *)

(*   Lemma relation_is_mere {M : Monoid} (X : hSet) *)
(*         (a : Monoid_Action M X) *)
(*         (isfree_a : forall (m1 m2 : M) (x : X), (function_of a m1 x = function_of a m2 x -> m1 = m2)) *)
(*     : is_mere_relation X (grp_compl_relation X a). *)
(*   Proof. *)
(*     intros. *)
(*     unfold grp_compl_relation. *)
(*     apply (trunc_sigma' _). *)
(*     - intros [m1 p1] [m2 p2]. simpl. *)
(*       apply (contr_inhabited_hprop _). *)
(*       exact (isfree_a m1 m2 x (p1 @ p2^)). *)
(*   Qed. *)

(*   Definition isfree_product_action (M : Monoid) (right_cancellation_M : forall l m n : M, m + l = n + l -> m = n) *)
(*     : forall (m1 m2 : M) (x : M*M), *)
(*       function_of (product_action M) m1 x = function_of (product_action M) m2 x -> m1 = m2. *)
(*   Proof. *)
(*     intros m1 m2 [x1 x2]. simpl. *)
(*     intro p. *)
(*     apply (right_cancellation_M x1). *)
(*     exact (ap fst p). *)
(*   Defined. *)

(*   Definition group_completion (M : Monoid) (right_cancellation_M : forall l m n : M, m + l = n + l -> m = n) : Type. *)
(*   Proof. *)
(*     refine (quotient (grp_compl_relation (BuildhSet (M*M)) (product_action M)) *)
(*                     (sR := relation_is_mere (BuildhSet (M*M)) (product_action M) (isfree_product_action _ right_cancellation_M))). *)
(*   Defined. *)

(*   (* TODO: Make this cleaner, move to group_completion, and see if the same stuff can be proved. *) *)
    
    
    
  
(*   Definition divide_action (S : Symmetric_Monoid) (X: hSet) (action : Monoid_Action S X): hSet. *)
(*   Proof. *)
    
    
  
(* End Monoid_action. *)

Section MonType_to_Mon.
  (* Truncating a monoidal category to a monoid *)
  Definition montype_to_monoid : Monoidal_1Type -> Monoid.
  Proof.
    intro S.
    srapply @Build_Monoid.
    - exact (BuildTruncType 0 (Trunc 0 S)).
    - intro a.
      apply Trunc_rec.
      revert a.
      simpl.
      apply (Trunc_rec (A := S) (X := S -> Trunc 0 S)).
      intros a b.
      apply tr. exact (montype_mult a b).
    - exact (tr montype_id).
    - unfold associative. simpl.
      intros a b c.
      strip_truncations. simpl.
      apply (ap tr). apply montype_assoc.
    - unfold left_identity_mult.
      intro a. strip_truncations. simpl.
      apply (ap tr). apply montype_lid.
    - unfold right_identity_mult. intro a.
      strip_truncations. simpl.
      apply (ap tr). apply montype_rid.
  Defined.

  Definition functor_montype_to_monoid {M N : Monoidal_1Type} :
    Monoidal_Map M N -> Homomorphism (montype_to_monoid M) (montype_to_monoid N).
  Proof.
    intro f.
    srapply @Build_Homomorphism.
    - simpl. apply Trunc_rec. intro a.
      apply tr. exact (f a).
    - apply (ap tr). apply montype_map_id.
    - intros a b. strip_truncations. simpl.
      apply (ap tr). apply montype_map_mult.
  Defined.

  Definition sym_montype_to_monoid : Symmetric_Monoidal_1Type -> Symmetric_Monoid.
  Proof.
    intro S.
    apply (Build_Symmetric_Monoid (montype_to_monoid S)).
    unfold symmetric. intros a b. strip_truncations. simpl.
    apply (ap tr). apply smontype_sym.
  Defined.


  Definition group_group_completion_to_monoid (S : Symmetric_Monoidal_1Type)
             {faithful_S : left_faithful (@montype_mult S)}
    : Abelian_Group.
  Proof.
    srapply @Build_Abelian_Group.
    srapply @Build_Group.
    srapply @Build_Monoid.
    - exact (BuildTruncType 0 (Trunc 0 (group_completion S faithful_S))).
    - simpl. intro a.
      apply Trunc_rec. revert a.
      apply (Trunc_rec (A := S*S) (X := S*S -> Trunc 0 (S*S))).
      intros a b. apply tr. revert a b.
      apply (mult_group_completion S faithful_S).
    - simpl.
      exact (tr (smontype_id, smontype_id)).
    - unfold associative. simpl.
      intros a b c. strip_truncations. simpl. apply (ap tr).
      
      
    
    
    

  Definition equiv_group_completion_to_monoid (S : Symmetric_Monoidal_Type) :
    group_


                                                   
