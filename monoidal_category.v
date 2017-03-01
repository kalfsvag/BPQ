Require Import HoTT.
Require Import UnivalenceAxiom.
Load stuff.

        
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


  Record Monoidal_Groupoid : Type := { mon_type : Type;
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
         Build_Monoidal_Groupoid mon_type {mon_istrunc} mon_mult mon_id mon_assoc mon_lid mon_rid
         mon_triangle mon_pentagram.


  Coercion mon_type : Monoidal_Groupoid >-> Sortclass.
  Global Arguments mon_mult {m} m1 m2.
  Global Arguments mon_assoc {m} {a} {b} {c}.
  Global Arguments mon_lid {m} a.
  Global Arguments mon_rid {m} a.


  Notation "a + b" := (mon_mult a b) : monoid_scope.


  (*Todo: Define symmetric monoidal category (check coherence criteria)*)
  Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a.



(*Defining the monoidal 1-type of finite sets and isomorphisms*)
Section Finite_Sets.
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Local Notation "'Sigma'" := { S : Type & Finite S }.

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
    intros [m finA]. simpl in finA. revert finA. apply Trunc_rec. intro e.
    apply (trunc_equiv' (Fin m) e^-1).
  Defined.
    
  (*ishprop_finite*)
  (*path_sigma_hprop*)
  (*Could also go via [istrunc_trunctype] . . .*)
  Definition istrunc_Sigma : IsTrunc 1 Sigma.
  Proof.
    apply trunc_sigma'.
    - exact (fun a => _).
    - intros A B.
      srapply @istrunc_paths_Type.
      apply isset_Finite. exact B.2.
  Defined.

  (*For convinience: Any type of 2-paths in sigma is thus an hprop.*)
  Instance isprop_2path_Sigma {S1 S2 : Sigma} {p1 p2 : S1 = S2} : IsHProp (p1 = p2) :=
    istrunc_Sigma S1 S2 p1 p2.
    
  (*The cardinal of the finite set*)
  Definition cardinal (S : Sigma) : nat := @fcard S.1 S.2.

  (*Canonical objects in iFin*)
  Local Notation "[ n ]" := ( Fin n ; finite_fin n ).


  (*Holds by definition: [cardinal [n] = n]*)

  (*Every object is canonical*)
  Lemma canonical_Sigma (S : Sigma) : merely (S = [cardinal S]).
  Proof.
    refine (Trunc_rec (n:=-1) (A := ( S.1 <~> Fin (fcard S.1))) _ _).
    - intro e.
      apply tr.
      apply path_sigma_hprop.
      exact (path_universe e). 
    - apply merely_equiv_fin.
  Defined.

  (*The monoidal structure on Sigma*)
  Definition plus_sigma : Sigma-> Sigma -> Sigma.
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


  Definition Sigma_assoc : associative plus_sigma.
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
  
  
  Ltac reduce_Sigma :=
    repeat match goal with
             | [S : Sigma |- _] => trunc_rewrite (canonical_Sigma S);
                                  destruct S as [S [?n H]];
                                  unfold cardinal; cbn; clear H; clear S
           end.

  Ltac simple_reduce_Sigma S :=
    trunc_rewrite (canonical_Sigma S);
    destruct S as [S [?n H]];
    unfold cardinal; cbn; clear H; clear S.
    

  (*A proof that sigma is merely associative, just using associativity of natural numbers*)
  Definition merely_Sigma_assoc : forall S1 S2 S3 : Sigma, merely (S1 + (S2 + S3) = (S1 + S2) + S3).
  Proof.
    intros S1 S2 S3. repeat reduce_Sigma. 
    apply tr.
    rewrite <- (sum_canonical n0 n).
    rewrite <- (sum_canonical n1 n0).
    rewrite <- (sum_canonical n1 (n0 + n)).
    rewrite <- (sum_canonical (n1 + n0) n).
    apply (ap (fun n => [n])).
    apply plus_assoc.
  Defined.
    
    
    
  
  Definition Sigma_lid : left_identity plus_sigma ([0]).
  Proof.
    intro S.
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_l S.1)).
  Defined.

  Definition Sigma_rid : right_identity plus_sigma ([0]).
  Proof.
    intro S.
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (sum_empty_r S.1)).
  Defined.

  Definition Sigma_symmetric : symmetric plus_sigma. 
  Proof.
    intros S1 S2.
    refine (path_sigma_hprop _ _ _).
    exact (path_universe (equiv_sum_symm S1.1 S2.1)).
  Defined.

  (**A few lemmas proving that [cardinal : nat -> Sigma] preserves the monoidal structure **)
  (*[cardinal] respects sum*)
  Definition sum_cardinal (S1 S2 : Sigma) : cardinal (S1 + S2) = (cardinal S1 + cardinal S2)%nat.
  Proof.
    destruct S1 as [S1 fin1].
    destruct S2 as [S2 fin2].
    apply fcard_sum.
  Defined.

  (*[cardinal] respects associativity*)
  Lemma assoc_cardinal (S1 S2 S3 : Sigma) :
    ap cardinal (Sigma_assoc S1 S2 S3) @ sum_cardinal (S1 + S2) S3 @
       ap (fun n => (n + (cardinal S3))%nat) (sum_cardinal S1 S2)  =
    sum_cardinal S1 (S2 + S3) @ ap (fun n => ((cardinal S1) + n)%nat) (sum_cardinal S2 S3) @
                 plus_assoc (cardinal S1) (cardinal S2) (cardinal S3).
  Proof.
    (* simple_reduce_Sigma S1. simple_reduce_Sigma S2. simple_reduce_Sigma S3. *)
    (* unfold Sigma_assoc. simpl. *)
    (* rewrite (ap_compose (fun S : Sigma => S.1) fcard). *)
    
    (* induction n1. *)
    (* simpl. rewrite ap_idmap. rewrite concat_p1. *)
    (* unfold Sigma_assoc.  *)
    
    
    (* - unfold plus_assoc. simpl. *)
    
    (* unfold cardinal. unfold fcard. cbn. unfold sum_cardinal. unfold Sigma_assoc. simpl. *)
  Abort.

  
  (*TODO: How [cardinal] respects associativity and identity proofs *)
  Definition Sigma_triangle : coherence_triangle Sigma_assoc Sigma_lid Sigma_rid.
  Proof.
    intros S1 S2.
    trunc_rewrite (canonical_Sigma S1). trunc_rewrite (canonical_Sigma S2).
    unfold Sigma_assoc.
    simpl.
    (*This was messy.*) Abort.

  (*Definition Sigma_pentagram : coherence_pentagram Sigma_triangle.*)

  Definition Sigma_lcancel : forall S1 S2 S3 : Sigma, S1 + S2 = S1 + S3 -> merely (S2 = S3).
  Proof.
    intros S1 S2 S3.
    intro pth.
    trunc_rewrite (canonical_Sigma S2).
    trunc_rewrite (canonical_Sigma S3).
    apply tr. apply (ap (fun n : nat => [n])).
    apply (nat_plus_cancelL (cardinal S1)).
    refine ((sum_cardinal S1 S2)^ @ _ @ sum_cardinal S1 S3).
    exact (ap cardinal pth).
  Defined.

  Definition sigma_minus (A : Sigma) (m n : nat) :
    A + [m] = [n] -> merely (A = [nat_minus m n]).
  Proof.
    intro p.
    pose proof (canonical_Sigma A) as q.
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
    (*   apply (Sigma_rid [l])^ . *)
    (* - induction n. *)
    (*   +  *)
  Abort.
    
          
    
    

  Definition unique_choice_groupcompletion_arrow (m n : nat) :
    {A : Sigma & A + [m] = [n]} -> Trunc 0 {A : Sigma & A + [m] = [n]}.
  Proof.
    intros [A p].
    pose proof (Sigma_lcancel 

    
    apply trunc_sigma'.
    - intro A. apply (istrunc_Sigma (A + [m]) [n]).
    - intros [A p] [B q]. simpl.
      unfold IsHProp. unfold IsTrunc_internal.
      intros p1 q1.
      srapply @BuildContr.
      destruct q1.
      reduce_Sigma.
      
  

End Finite_Sets.

Require Import Category.