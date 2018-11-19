Require Import HoTT.
Require Import UnivalenceAxiom.
Load finite_lemmas.
Load equiv_lemmas.
Load path_lemmas.


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
    intros []. reflexivity.
  Defined.
  (* Definition trivial_is_idmap {m : nat} : trivial_equiv_fin m m idpath  *)
End Finite.

        
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

  Definition coherence_pentagon {A : Type} {m : A -> A -> A} (assoc : associative m) :=
    forall a b c d : A,
      assoc a b (m c d) @ assoc (m a b) c d =
      ap (m a) (assoc b c d) @ assoc a (m b c) d @ ap (fun f => m f d) (assoc a b c).

  Record Monoidal_1Type : Type := { mon_type :> 1-Type;
                                    (* mon_istrunc : IsTrunc 1 mon_type; *)
                                    mon_mult  : mon_type->mon_type->mon_type;
                                    mon_id : mon_type;
                                    mon_assoc : associative mon_mult;
                                    mon_lid : left_identity mon_mult mon_id ;
                                    mon_rid : right_identity mon_mult mon_id ;
                                    mon_triangle : coherence_triangle mon_assoc mon_lid mon_rid ;
                                    mon_pentagon : coherence_pentagon mon_assoc
                                  }.

  (*Makes mon_istrunc an implicit argument*)
  Global Arguments
         Build_Monoidal_1Type mon_type (* {mon_istrunc} *) mon_mult mon_id mon_assoc mon_lid mon_rid
         mon_triangle mon_pentagon.
  
  Global Arguments mon_mult {m} m1 m2.
  Global Arguments mon_id {m}.
  Global Arguments mon_assoc {m} a b c.
  Global Arguments mon_lid {m} a.
  Global Arguments mon_rid {m} a.
  
  Infix "⊗" := mon_mult (at level 50,no associativity). 

  (*Todo: Define symmetric monoidal category (check coherence criteria)*)
  Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a.

  Record Monoidal_Map (M N : Monoidal_1Type) :=
    {mon_map :> M -> N;
     mon_map_mult (x y : M) : mon_map (x ⊗ y) = (mon_map x) ⊗ (mon_map y);
     mon_map_id : mon_map (mon_id) = mon_id;
     mon_map_assoc (x y z : M) :
       ap mon_map (mon_assoc x y z) =
       mon_map_mult x (y ⊗ z) @ ap (fun s => mon_map x ⊗ s) (mon_map_mult y z) @
                    mon_assoc (mon_map x) (mon_map y) (mon_map z) @
     (ap (fun s => s ⊗ mon_map z) (mon_map_mult x y))^ @ (mon_map_mult (x ⊗ y) z)^;
     mon_map_lid (x : M) : ap mon_map (mon_lid x) =
                           mon_map_mult mon_id x @ ap (fun s => s ⊗ mon_map x) mon_map_id @ mon_lid (mon_map x);
     mon_map_rid (x : M) : ap mon_map (mon_rid x) =
                           mon_map_mult x mon_id @ ap (fun s => mon_map x ⊗ s) mon_map_id @ mon_rid (mon_map x);
    }.
  Arguments mon_map_mult {M N} F {x y} : rename.
  Arguments mon_map_id {M N} F : rename.
  Arguments mon_map_assoc {M N} F x y z : rename.
  Arguments mon_map_lid {M N} F x : rename.
  Arguments mon_map_rid {M N} F x : rename.

  Definition monoidal_map_id (M : Monoidal_1Type) : Monoidal_Map M M.
  Proof.
    srapply (Build_Monoidal_Map M M idmap); try reflexivity.
    intros. rewrite ap_idmap. repeat rewrite concat_p1. apply inverse. apply concat_1p.
  Defined.
  
  Definition monoidal_map_compose (M N O : Monoidal_1Type) :
    Monoidal_Map M N -> Monoidal_Map N O -> Monoidal_Map M O.
  Proof.
    intros F G.
    srapply @Build_Monoidal_Map.
    - exact (G o F).
    - intros x y.
      transitivity (G (F x ⊗ F y)).
      + apply (ap G). apply mon_map_mult.
      + apply mon_map_mult.
    - transitivity (G mon_id).
      + apply (ap G). apply mon_map_id.
      + apply mon_map_id.
    - intros.
      refine (ap_compose F G _ @ _).
      refine (ap (ap G) (mon_map_assoc F x y z) @ _).
      refine (ap_pp G _ _ @ _).
      refine (whiskerR (ap_pp G _ _ ) _ @ _).
      refine (whiskerR (whiskerR (ap_pp G _ _ ) _) _ @ _).
      refine (whiskerR (whiskerR (whiskerR (ap_pp G _ _ ) _) _) _ @ _).
      repeat refine (concat_pp_p _ _ _ @ _).
      repeat refine (_ @ concat_p_pp _ _ _). apply whiskerL.
      repeat refine (concat_p_pp _ _ _ @ _).
      repeat refine (_ @ concat_pp_p _ _ _).
      refine (_ @ whiskerL _ (inv_pp _ _)^).
      repeat refine (_ @ concat_pp_p _ _ _).
      refine (concat2 _ (ap_V G _)).
      refine (whiskerL _ (ap_V G _) @ _).
      refine (whiskerL _ (ap inverse (ap_compose _ G (mon_map_mult F))^) @ _).
      refine (whiskerR (whiskerR (ap_compose _ G (mon_map_mult F))^ _) _ @ _).
      assert (H : forall (a b c : O) (p : a = b) (q : b = c),
                 (ap (fun s : O => s ⊗ G (F z)) (p @ q))^ =
                 (ap (fun s : O => s ⊗ G (F z)) q)^ @ (ap (fun s : O => s ⊗ G (F z)) p)^).
      { by path_induction. }
      refine (_ @ whiskerR (whiskerL _ (H _ _ _ _ _)^) _). clear H.

      repeat rewrite ap_pp.
      repeat rewrite <- (ap_compose G).
      rewrite (mon_map_assoc G (F x) (F y) (F z)).
      repeat rewrite concat_p_pp.
      refine (concat_pp_p _ _ _ @ _).
      refine (_ @ concat_p_pp _ _ _).
      apply concat2.
      + repeat apply whiskerR. destruct (mon_map_mult F). cbn. destruct (mon_map_mult G). reflexivity.        
      + destruct (mon_map_mult F). cbn. destruct (mon_map_mult G). reflexivity. 
    - intro x. simpl.
      transitivity (ap G (ap F (mon_lid x))).
      { apply (ap_compose F G). }
      refine ( ap (ap G) (mon_map_lid F x) @ _).
      refine (ap_pp G _ _ @ _).
      refine (ap (fun p => p @ ap G (mon_lid (F x))) (ap_pp G _ _) @ _).
      refine (whiskerL _ (mon_map_lid G (F x)) @ _).
      repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      repeat refine (concat_pp_p _ _ _ @ _).
      repeat refine (_ @ concat_p_pp _ _ _). apply whiskerL.
      refine (_ @ whiskerL _ (ap_pp (fun s : O => s ⊗ G (F x)) _ _)^).
      repeat refine (_ @ concat_pp_p _ _ _).
      repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      refine (whiskerR (ap_compose _ G (mon_map_id F))^ _ @ _).
      refine (_ @ whiskerL _ (ap_compose G _ (mon_map_id F))).
      destruct (mon_map_id F). cbn.
      exact (concat_1p _ @ (concat_p1 _)^).
    - intro x. simpl.
      transitivity (ap G (ap F (mon_rid x))).
      { apply (ap_compose F G). }
      refine ( ap (ap G) (mon_map_rid F x) @ _).
      refine (ap_pp G _ _ @ _).
      refine (ap (fun p => p @ ap G (mon_rid (F x))) (ap_pp G _ _) @ _).
      refine (whiskerL _ (mon_map_rid G (F x)) @ _).
      repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      repeat refine (concat_pp_p _ _ _ @ _).
      repeat refine (_ @ concat_p_pp _ _ _). apply whiskerL.
      refine (_ @ whiskerL _ (ap_pp (fun s : O => G (F x) ⊗ s) _ _)^).
      repeat refine (_ @ concat_pp_p _ _ _).
      repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      refine (whiskerR (ap_compose _ G (mon_map_id F))^ _ @ _).
      refine (_ @ whiskerL _ (ap_compose G _ (mon_map_id F))).
      destruct (mon_map_id F). cbn.
      exact (concat_1p _ @ (concat_p1 _)^).
  Defined.
      

  (* Given a 1-Type X, the type X->X is a monoidal 1-type *)
  Definition endomorphism (X : 1-Type) : Monoidal_1Type.
  Proof.
    srapply @Build_Monoidal_1Type.
    - apply (BuildTruncType 1 (X -> X)).
    - intros f g. exact (f o g).
    - cbn. exact idmap.
    - cbn. unfold associative. reflexivity.
    - cbn. unfold left_identity. reflexivity.
    - cbn. unfold right_identity. reflexivity.
    - unfold coherence_triangle. cbn. reflexivity.
    - unfold coherence_pentagon. cbn. reflexivity.
  Defined.

  Definition monoidal_action (M : Monoidal_1Type) (X : 1-Type) := Monoidal_Map M (endomorphism X).
  Definition mon_act_mult {M : Monoidal_1Type} {X : 1-Type} (a : monoidal_action M X)
             (m1 m2 : M) (x : X) :
    a (m1 ⊗ m2) x = a m1 (a m2 x).
  Proof.
    revert x. apply ap10. apply (mon_map_mult a).
  Defined.

  Definition mon_act_id {M : Monoidal_1Type} {X : 1-Type} (a : monoidal_action M X)
             (x : X) :
    a (mon_id) x = x.
  Proof.
    revert x. apply ap10. apply (mon_map_id a).
  Defined.

  (* Definition mon_act_assoc {M : Monoidal_1Type} {X : 1-Type} (a : monoidal_action M X) *)

  (* Todo: mon_act_assoc, mon_act_lid, mon_act_rid *)

  (* Definition left_cancellation_monoid (M : Monoidal_1Type) := left_cancellation (@mon_mult M). *)

  Require Import HoTT.Categories.
  (* If we have a monoidal action with left_cancellation, we can build a category with objects X and arrows*)
  (* {m : M & m ⊗ x = m ⊗ y} *)
  Definition monoidal_action_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) :
    (X -> X -> Type) := fun x y => {s : M & a s x = y}.

  (* Definition ap101 {A B C : Type} {f g : A -> B -> C} (p1 : f = g) { *)
  (*                                                      forall  *)
  
  
  Definition monoidal_action_cat (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) : PreCategory.
  Proof.
    srapply (Build_PreCategory (monoidal_action_morphism M X a)).
    (* identity *)
    - intro x. exists mon_id. apply mon_act_id.
    (* composition *)
    - intros x y z.
      intros [s1 p1] [s2 p2].
      exists (s1 ⊗ s2).
      refine (mon_act_mult a s1 s2 x @ (ap (a s1) p2) @ p1).
    (* associtivity *)
    - intros x1 x2 x3 x4 [s1 p1] [s2 p2] [s3 p3].
      srapply @path_sigma. apply inverse. apply mon_assoc. cbn.
      refine (transport_paths_Fl (mon_assoc s3 s2 s1)^ _ @ _).
      destruct p3. destruct p2. destruct p1. cbn.
      repeat rewrite concat_p1. rewrite ap_V. rewrite inv_V. unfold monoidal_action in a. unfold mon_act_mult.
      assert (H : ap10 (ap a (mon_assoc s3 s2 s1)) x1 = ap (fun x : M => a x x1) (mon_assoc s3 s2 s1)).
      { destruct (mon_assoc s3 s2 s1). reflexivity. } destruct H.
      destruct (ap10_pp
      rewrite <- ap10_pp.

      Check ((mon_map_assoc a s1 s2 s3)).
      Check (ap10 ).
      Check (ap a).
      Check (ap (fun x : M => a x x1)). 

      
      
      destruct (concat_p1 (mon_act_mult a (s3 ⊗ s2) s1 x1))^.
      
      refine (whiskerL () _ @ _)
      

      
      refine (path_sigma _ _ _ (mon_assoc s3 s2 s1)^ _).
      
      
    
  

(*Defining the monoidal 1-type of finite sets and isomorphisms*)
Section BΣ.
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Definition BΣ := { S : Type & Finite S}.
  Definition path_BΣ (S T : BΣ) : S.1 <~> T.1 -> S = T
    := path_finite_types_sum S T.
  
  (* Local Notation "'iFin'" := { S : Type & Finite S }. *)

  (* (*Finite types are sets *) *)
  (* Definition isset_Fin (n : nat) : IsHSet (Fin n). *)
  (* Proof. *)
  (*   induction n. *)
  (*   - exact _. *)
  (*   - apply hset_sum. *)
  (* Defined. *)

  (* Definition isset_Finite (A : Type) : *)
  (*   Finite A -> IsHSet A. *)
  (* Proof. *)
  (*   intros [m finA]. strip_truncations. *)
  (*   apply (trunc_equiv' (Fin m) finA^-1). *)
  (* Defined. *)
    
  (*ishprop_finite*)
  (*path_sigma_hprop*)
  (*Could also go via [istrunc_trunctype] . . .*)
  Definition istrunc_BΣ : IsTrunc 1 BΣ.
  Proof.
    apply trunc_sigma'. intro A. exact _.
    intros A B.
    srapply @istrunc_paths_Type. 
    apply isset_Finite. exact B.2.
  Defined.

  (*For convinience: Any type of 2-paths in sigma is thus an hprop.*)
  Instance isprop_2path_BΣ {S1 S2 : BΣ} {p1 p2 : S1 = S2} : IsHProp (p1 = p2) :=
    istrunc_BΣ S1 S2 p1 p2.
    
  (* (*The cardinal of the finite set*) *)
  Definition cardinal (S : BΣ) : nat := @fcard S.1 S.2.

  (*Canonical objects in BΣ*)
  Definition canon_BΣ (n : nat) : BΣ := (Fin n; Build_Finite (Fin n) n (tr 1%equiv)).
  Notation "[ n ]" := (canon_BΣ n).
  (*Holds by definition: [cardinal [n] = n]*)

  (*Every object is canonical*)
  Lemma canonical_BΣ (S : BΣ) : merely (S = [cardinal S]).
  Proof.
    destruct S as [A [n eA]]. strip_truncations. apply tr.
    apply path_BΣ. cbn. exact eA.
  Defined.

  (*The monoidal structure on BΣ*)
  Definition plus_BΣ : BΣ -> BΣ -> BΣ.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (S1 + S2 ; finite_sum _ _)%type.
  Defined.

  Local Notation "S1 ⊕ S2" := (plus_BΣ S1 S2) (at level 50, no associativity).

  (*The canonical objects respect sum*)
  Definition sum_canonical (m n : nat) : [m + n]%nat = [m] ⊕ [n].
  Proof.
    apply path_BΣ.
    apply Fin_resp_sum.
  Defined.
  
  Definition BΣ_assoc : associative plus_BΣ.
  Proof.
    intros S1 S2 S3.
    apply path_BΣ. 
    apply equiv_inverse.
    apply equiv_sum_assoc. 
  Defined.

  (* (*If the goal is truncated, add this as a hypothesis. (Can speed things up)*) *)
  (* Ltac trunc_goal n := *)
  (*   match goal with *)
  (*       | [ |- ?g] => assert (istrunc_goal : IsTrunc n g) by (exact _) *)
  (*   end. *)
  
  
  (* Ltac reduce_BΣ := *)
  (*   repeat match goal with *)
  (*            | [S : BΣ |- _] => trunc_rewrite (canonical_BΣ S); *)
  (*                                 destruct S as [S [?n H]]; *)
  (*                                 unfold cardinal; cbn; clear H; clear S *)
  (*          end. *)

  (* Ltac simple_reduce_BΣ S := *)
  (*   trunc_rewrite (canonical_BΣ S); *)
  (*   destruct S as [S [?n H]]; *)
  (*   unfold cardinal; cbn; clear H; clear S. *)
    

  (* (*A proof that sigma is merely associative, just using associativity of natural numbers*) *)
  (* Definition merely_BΣ_assoc : forall S1 S2 S3 : BΣ, merely (S1 ⊕ (S2 ⊕ S3) = (S1 ⊕ S2) ⊕ S3). *)
  (* Proof. *)
  (*   intros [S1 [n1 fin1]] [S2 [n2 fin2]] [S3 [n3 fin3]]. *)
  (*   (* strip_truncations. *) *)
  (*   apply tr. *)
  (*   refine (path_sigma_hprop _ _ _). simpl. *)
  (*   apply (path_universe (equiv_sum_assoc S1 S2 S3)^-1). *)
  (* Defined. *)
  
  Definition BΣ_lid : left_identity plus_BΣ ([0]).
  Proof.
    intro S. apply path_BΣ.
    apply sum_empty_l.
  Defined.
  
  Definition BΣ_rid : right_identity plus_BΣ ([0]).
  Proof.
    intro S. apply path_BΣ.
    apply sum_empty_r.
  Defined.

  Definition BΣ_symmetric : symmetric plus_BΣ. 
  Proof.
    intros S1 S2. apply path_BΣ. apply equiv_sum_symm.
  Defined.

  (**A few lemmas proving that [cardinal : nat -> BΣ] preserves the monoidal structure **)
  (*[cardinal] respects sum*)
  Definition sum_cardinal (S1 S2 : BΣ) : cardinal (S1 ⊕ S2) = (cardinal S1 + cardinal S2)%nat.
  Proof.
    destruct S1 as [S1 fin1].
    destruct S2 as [S2 fin2].
    apply fcard_sum.
  Defined.

  (* (*[cardinal] respects associativity*) *)
  (* Lemma assoc_cardinal (S1 S2 S3 : BΣ) : *)
  (*   ap cardinal (BΣ_assoc S1 S2 S3) @ sum_cardinal (S1 + S2) S3 @ *)
  (*      ap (fun n => (n + (cardinal S3))%nat) (sum_cardinal S1 S2)  = *)
  (*   sum_cardinal S1 (S2 + S3) @ ap (fun n => ((cardinal S1) + n)%nat) (sum_cardinal S2 S3) @ *)
  (*                plus_assoc (cardinal S1) (cardinal S2) (cardinal S3). *)
  (* Proof. *)
  (*   destruct S1 as [S1 [n1 fin1]]. destruct S2 as [S2 [n2 fin2]]. destruct S3 as [S3 [n3 fin3]]. *)
  (*   strip_truncations. *)
    
    (* simple_reduce_BΣ S1. simple_reduce_BΣ S2. simple_reduce_BΣ S3. *)
    (* unfold iFin_assoc. simpl. *)
    (* rewrite (ap_compose (fun S : iFin => S.1) fcard). *)
    
    (* induction n1. *)
    (* simpl. rewrite ap_idmap. rewrite concat_p1. *)
    (* unfold iFin_assoc.  *)
    
    
    (* - unfold plus_assoc. simpl. *)
    
    (* unfold cardinal. unfold fcard. cbn. unfold sum_cardinal. unfold iFin_assoc. simpl. *)
  

  
  (*TODO: How [cardinal] respects associativity and identity proofs *)
  Definition BΣ_triangle : coherence_triangle BΣ_assoc BΣ_lid BΣ_rid.
  Proof.
    intros [S1 f1] [S2 f2]. unfold BΣ_assoc. unfold BΣ_rid. unfold BΣ_lid.
    simpl. 
    trunc_rewrite (canonical_BΣ S1). trunc_rewrite (canonical_BΣ S2).
    unfold BΣ_assoc.
    simpl.
    (*This was messy.*) Abort.

  (*Definition BΣ_pentagon : coherence_pentagon BΣ_triangle.*)

  Definition BΣ_lcancel : forall S1 S2 S3 : BΣ, S1 + S2 = S1 + S3 -> merely (S2 = S3).
  Proof.
    intros S1 S2 S3.
    intro pth.
    trunc_rewrite (canonical_BΣ S2).
    trunc_rewrite (canonical_BΣ S3).
    apply tr. apply (ap (fun n : nat => [n])).
    apply (nat_plus_cancelL (cardinal S1)).
    refine ((sum_cardinal S1 S2)^ @ _ @ sum_cardinal S1 S3).
    exact (ap cardinal pth).
  Defined.

  Definition sigma_minus (A : BΣ) (m n : nat) :
    A + [m] = [n] -> merely (A = [nat_minus m n]).
  Proof.
    intro p.
    pose proof (canonical_BΣ A) as q.
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
    (*   apply (BΣ_rid [l])^ . *)
    (* - induction n. *)
    (*   +  *)
  Abort.
    
          
    
    

  Definition unique_choice_groupcompletion_arrow (m n : nat) :
    {A : BΣ & A + [m] = [n]} -> Trunc 0 {A : BΣ & A + [m] = [n]}.
  Proof.
    intros [A p].
    (* pose proof (BΣ_lcancel  *)

    
    (* apply trunc_sigma'. *)
    (* - intro A. apply (istrunc_BΣ (A + [m]) [n]). *)
    (* - intros [A p] [B q]. simpl. *)
    (*   unfold IsHProp. unfold IsTrunc_internal. *)
    (*   intros p1 q1. *)
    (*   srapply @BuildContr. *)
    (*   destruct q1. *)
    (*   reduce_BΣ. *)
    Abort.  
  

End BΣ_1Type.
