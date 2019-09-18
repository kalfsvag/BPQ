Require Import HoTT.

From GC Require Import pointed_lemmas finite_lemmas nat_lemmas trunc_lemmas (* monoidal_1type *)
                       group_complete_1type.

(*Defining the monoidal 1-type of finite sets and isomorphisms*)
Section BSigma.
    
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Record BSigma :=
    {card_BSigma : nat ; fintype_of_BSigma :> Finite_Types card_BSigma}.
    (* {m : nat & Finite_Types m}. *)
    (* { S : Type & Finite S}. *)
  (* Definition type_of_fin : BSigma -> Type := (fun A => A.2.1). *)
  (* Coercion type_of_fin : BSigma  >-> Sortclass. *)

  Definition issig_BSigma :
    BSigma <~> {A : Type & Finite A}.
  Proof.
    srapply @equiv_adjointify.
    - intros [n A]. exists A. exact _.
    - intros [A [n e]]. exact (Build_BSigma n (A; e)).
    - intros [A [n e]]. simpl.
      apply path_sigma_hprop. reflexivity.
    - intros [n A]. simpl. reflexivity.
  Defined.

  Global Instance istrunc_BSigma : IsTrunc 1 BSigma.
  Proof.
    apply (trunc_equiv' {S : Type & Finite S}).
    - apply equiv_inverse. apply issig_BSigma.
    - apply trunc_sigma'.
      +  intro A. exact _.
      +  intros A B.
         srapply @istrunc_paths_Type. 
         apply isset_Finite. exact B.2.
  Defined.

  Definition fin_to_BSigma {n : nat}
    : Finite_Types n -> BSigma
    := Build_BSigma n.

  (*Canonical objects in BSigma*)
  Definition canon_BSigma (n : nat) : BSigma := fin_to_BSigma (canon n).

  Lemma finite_types_eqcard {m n : nat} (A : Finite_Types m) (B : Finite_Types n) :
    A <~> B -> m = n.
  Proof.
    destruct A as [A fA]. destruct B as [B fB]. simpl. intro e.
    strip_truncations.
    apply nat_eq_fin_equiv.
    exact (fB oE e oE (equiv_inverse fA)).
  Qed.

  (* in finite_lemmas: *)
  (* (* Describing the path type of BSigma *) *)
  (* Definition path_BSigma {A B : BSigma} : A <~> B -> A = B. *)
  (* Proof. *)
  (*   refine ((equiv_ap issig_BSigma A B)^-1 o _). *)
  (*   destruct A as [m [A eA]]. destruct B as [n [B eB]]. simpl. *)
  (*   exact (equiv_path_finite_types' (A; finite_finite_type (A; eA)) (B; finite_finite_type (B; eB))). *)
  (* Defined. *)

  (* Definition path_BSigma_inv {A B : BSigma} : A = B -> A <~> B. *)
  (* Proof. *)
  (*   intros []. exact equiv_idmap. *)
  (* Defined. *)

  (* Global Instance isequiv_path_BSigma {A B : BSigma} : IsEquiv (@path_BSigma A B). *)
  (* Proof. *)
  (*   srapply @isequiv_adjointify. *)
  (*   - exact path_BSigma_inv. *)
  (*   - intros []. simpl. *)
  (*     unfold path_BSigma. *)

  
  Definition equiv_path_BSigma (A B : BSigma) :
    (A <~> B) <~> A = B.
  Proof.
    refine ((equiv_ap issig_BSigma A B)^-1 oE _).
    destruct A as [m [A eA]]. destruct B as [n [B eB]]. simpl.
    exact (equiv_path_finite_types' (A; finite_finite_type (A; eA)) (B; finite_finite_type (B; eB))).
  Defined.
  
  Definition path_BSigma (A B : BSigma) : A <~> B -> A = B
       := equiv_path_BSigma A B.
  (* Proof. *)
  (*   destruct A as [m A]. destruct B as [n B]. simpl. *)
  (*   intro e. *)
  (*   destruct (finite_types_eqcard A B e). *)
  (*   apply (path_sigma (fun m : nat => Finite_Types m) (m; A) (m;B) idpath). simpl. *)
  (*   apply path_finite_types. *)
  (*   exact e. *)
  (* Defined. *)


  (* Definition isequiv_path_BSigma {A B : BSigma} : IsEquiv (@path_BSigma A B). *)
  (* Proof. *)
  (*   srapply @isequiv_adjointify. *)
  (*   - intros []. exact equiv_idmap. *)
  (*   - intros []. *)
  (*     unfold path_BSigma. *)
  (*     assert (H : (finite_types_eqcard (pr2 A) (pr2 A) equiv_idmap) = idpath). *)
  (*     { apply hset_nat. } destruct H. *)
  (*     destruct . *)


  (* shorter proof than in finite_lemmas *)

  Definition path_BSigma_1 (A : BSigma) :
    path_BSigma _ _ (equiv_idmap A) = idpath.
  Proof.
    refine (ap (path_BSigma A A) (eissect (@path_BSigma A A) equiv_idmap)^ @ _).
    apply moveR_equiv_M.
    refine (eissect _ _ @ _). simpl.
    reflexivity.
  Defined.

  Definition path_BSigma_V {A B : BSigma} (e : A <~> B)
    : (path_BSigma _ _ e)^ = path_BSigma _ _ (equiv_inverse e).
  Proof.
    refine (_ @ ap (fun g => path_BSigma _ _ (equiv_inverse g)) (eissect (@path_BSigma A B) e)).
    generalize (path_BSigma A B e).  intros [].
    simpl. apply inverse.
    refine (_ @ path_BSigma_1 A).
    apply (ap (path_BSigma _ _)).
    apply path_equiv. simpl.  reflexivity.
  Defined.

  Definition pft_to_pbs {m : nat} {A B : Finite_Types m}
    : A = B -> (fin_to_BSigma A) = (fin_to_BSigma B) 
    := ap (fin_to_BSigma).
    (* : A = B -> (m;A) = (m;B) :> BSigma *)
    (* := fun p => path_sigma Finite_Types (m; A) (m; B) idpath p. *)

  Definition path_BSigma_fix {m : nat} (A B : Finite_Types m) (e : A <~> B)
    : pft_to_pbs (path_finite_types m A B e)
      = @path_BSigma (fin_to_BSigma A) (fin_to_BSigma B) e.
  Proof.
    refine (_ @ ap (@path_BSigma
                      (fin_to_BSigma _)
                      (fin_to_BSigma _))
              (eissect (path_finite_types m A B) e)).
    generalize (path_finite_types m A B e).
    intros []. simpl.
    refine ((path_BSigma_1 _)^).
  Defined.

  Global Instance isequiv_pft_to_pbs {m : nat} {A B : Finite_Types m}
    : IsEquiv (@pft_to_pbs m A B).
  Proof.
    assert (H : @pft_to_pbs m A B
            = equiv_path_BSigma
                (fin_to_BSigma A) (fin_to_BSigma B)
                oE (equiv_path_finite_types m A B)^-1).
    { apply path_arrow. intros []. ev_equiv.
      apply inverse.
      refine (path_BSigma_1 _). }
    rewrite H.
    apply equiv_isequiv.
  Qed.


  (* (* path_BSigma respects composition *) *)  
  Definition path_BSigma_compose {A B C : BSigma} (e1 : A <~> B) (e2 : B <~> C) :
    path_BSigma _ _ (e2 oE e1) = path_BSigma _ _ e1 @ path_BSigma _ _ e2.
  Proof.
    (* path_BSigma e2 @ path_BSigma e1 = path_BSigma (e1 oE e2). *)
  Proof.
    refine
      (ap011 (fun g1 g2 => path_BSigma _ _ (g2 oE g1))
             (eissect (path_BSigma A B) e1)^ (eissect (path_BSigma B C) e2)^ @ _).
    generalize (path_BSigma _ _ e2). intros []. 
    generalize (path_BSigma _ _ e1). intros []. simpl.
    refine (path_BSigma_1 A).
  Qed.
    

  Definition sum_BSigma : BSigma -> BSigma -> BSigma.
  Proof.
    intros [m A] [n B].
    exact (fin_to_BSigma (sum_finite_types A B)).
  Defined.

  Definition BSigma_id : BSigma := canon_BSigma 0.

  Local Notation "S1 ⊕ S2" := (sum_BSigma S1 S2) (at level 50, no associativity).

  (* (* symmetry *) *)
  (* Definition path_BSigma_twist (a b : nat) : *)
  (*   (@path_BSigma *)
  (*     (sum_BSigma (canon_BSigma a) (canon_BSigma b)) *)
  (*     (sum_BSigma (canon_BSigma b) (canon_BSigma a)) *)
  (*     (equiv_sum_symm (canon_BSigma a) (canon_BSigma b))) *)
  (*   @ *)
  (*     @path_BSigma *)
        
  (*       (sum_BSigma (canon_BSigma b) (canon_BSigma a)) *)
  (*       (canon_BSigma _) *)
  (*       (equiv_finsum b a) *)
  (*   = *)
  (*   @path_BSigma *)
  (*     (sum_BSigma (canon_BSigma a) (canon_BSigma b)) *)
  (*     (canon_BSigma _) *)
  (*     (equiv_finsum a b) *)
  (*   @ *)
  (*   ap canon_BSigma (nat_plus_comm b a). *)
  (* Proof. *)
  (*   induction a. *)
  (*   - simpl. *)
  (*     induction b. *)
  (*     + simpl. *)
  (*       refine ((path_BSigma_compose _ _ )^ @ _). *)
        

  (* path_BSigma behaves well with respect to sum *)
  Definition natural_path_BSigma_l {S1 S2 S3: BSigma} (e : S1 <~> S2)
    : ap (fun x : BSigma => x ⊕ S3) (path_BSigma _ _ e)
    = path_BSigma (S1 ⊕ S3) (S2 ⊕ S3) (equiv_functor_sum_r (B := S3) e).
  Proof.    
    refine (_ @ ap (fun e' => @path_BSigma (S1⊕ S3) (S2 ⊕ S3) (equiv_functor_sum_r e'))
              (eissect (@path_BSigma S1 S2) e)).
    generalize (path_BSigma _ _ e). intros [].
    simpl. apply inverse.
    refine (_ @ path_BSigma_1 (S1 ⊕ S3)).
    apply (ap (path_BSigma _ _)).
    apply path_equiv. apply path_arrow. intros [s1 | s3]; reflexivity.
  Qed.

  Definition natural_path_BSigma_r {S1 S2 S3: BSigma} (e : S2 <~> S3)
    : ap (fun x : BSigma => S1 ⊕ x) (path_BSigma _ _ e)
      = path_BSigma (S1 ⊕ S2) (S1 ⊕ S3) (equiv_functor_sum_l (A := S1) e).
  Proof.
    refine (_ @ ap (fun e' => @path_BSigma (S1 ⊕ S2) (S1 ⊕ S3) (equiv_functor_sum_l e'))
              (eissect (@path_BSigma S2 S3) e)).
    generalize (path_BSigma _ _ e). intros [].
    simpl. apply inverse.
    refine (_ @ path_BSigma_1 (S1 ⊕ S2)).
    apply (ap (path_BSigma _ _)).
    apply path_equiv. apply path_arrow. intros [s1 | s2]; reflexivity.
  Qed.
  
  (*The monoidal structure on BSigma*)
  
  Definition BSigma_assoc : associative sum_BSigma.
  Proof.
    intros S1 S2 S3.
    apply path_BSigma.
    apply equiv_sum_assoc. 
  Defined.

  Definition BSigma_lid : left_identity_mult sum_BSigma (canon_BSigma 0).
  Proof.
    intro S. apply path_BSigma.
    apply sum_empty_l.
  Defined.
  
  Definition BSigma_rid : right_identity_mult sum_BSigma (canon_BSigma 0).
  Proof.
    intro S. apply path_BSigma.
    apply sum_empty_r.
  Defined.

  Definition BSigma_symmetric : symmetric sum_BSigma. 
  Proof.
    intros S1 S2. apply path_BSigma. apply equiv_sum_symm.
  Defined.  
  
  Definition BSigma_triangle1 : coherence_triangle1 BSigma_assoc BSigma_lid.
  Proof.
    intros S1 S2.
    unfold BSigma_lid.
    refine (natural_path_BSigma_l _ @ _).
    unfold BSigma_assoc.
    refine (_ @ (path_BSigma_compose _ _)).
    apply (ap (path_BSigma _ _)).
    apply path_equiv. apply path_arrow.
    intros [[[] | s1] | s2]; reflexivity.
  Qed.

  Definition BSigma_triangle2 : coherence_triangle2 BSigma_assoc BSigma_lid BSigma_rid.
  Proof.
    intros S1 S2. unfold BSigma_rid. unfold BSigma_assoc. unfold BSigma_lid. simpl.
    refine (natural_path_BSigma_l _ @ _).
    refine (_ @ whiskerL _ (natural_path_BSigma_r _)^).
    refine (_ @ (path_BSigma_compose  _ _)).
    apply (ap (path_BSigma _ _)).
    apply path_equiv. apply path_arrow.
    intros [[s1 | []] | s2]; reflexivity.
  Qed.
  
  Definition BSigma_pentagon : coherence_pentagon BSigma_assoc.
  Proof.
    intros S1 S2 S3 S4.
    refine (natural_path_BSigma_l _  @ _).
    apply moveL_pV.
    refine ((path_BSigma_compose _ _)^ @ _).
    apply moveL_pV.
    refine (whiskerL _ (natural_path_BSigma_r _) @ _).
    refine ((path_BSigma_compose _ _)^ @ _).
    refine (_ @ (path_BSigma_compose _ _)).
    apply (ap (path_BSigma _ _)).
    apply path_equiv. apply path_arrow.
    intros [[[s1 | s2]| s3] | s4]; reflexivity.
  Defined.

  (* The next two lemmas should be moved *)
  Definition isinj_functor_sum {A1 A2 B1 B2 : Type} (f1 f1' : A1 -> B1) (f2 f2': A2 -> B2) :
    functor_sum f1 f2 = functor_sum f1' f2' -> (f1 = f1') * (f2 = f2').
  Proof.
    intro p.
    set (p' := ap10 p).
    apply pair.
    - apply path_arrow. intro a.
      apply (path_sum_inl B2). exact (p' (inl a)).
    - apply path_arrow. intro a.
      apply (path_sum_inr B1). exact (p' (inr a)).
  Defined.

  Definition isinj_equiv_functor_sum_r {A1 A2 B : Type} (e1 e2 : A1 <~> A2) :
    equiv_functor_sum_r (B := B) e1 = equiv_functor_sum_r e2 -> e1 = e2.
  Proof.
    intro p. apply path_equiv.
    refine (fst ((isinj_functor_sum e1 e2 idmap idmap) _)).
    apply (path_equiv^-1 p).
  Defined.    
  
  Definition BSigma_lcancel (S1 S2 : BSigma) (p q : S1 = S2) (T : BSigma) :
    ap (fun x => x ⊕ T) p = ap (fun x => x ⊕ T) q -> p = q.
  Proof.
    intro h.
    apply (equiv_inj (@path_BSigma S1 S2)^-1).
    apply (isinj_equiv_functor_sum_r (B:=T)
                                     ((equiv_path_BSigma _ _)^-1 p) ((equiv_path_BSigma _ _)^-1 q)) .
    apply (equiv_inj (@path_BSigma (S1 ⊕ T) (S2 ⊕ T))).
    refine ((natural_path_BSigma_l _)^ @ _ @ natural_path_BSigma_l _).
    refine (_ @ h @ _);
      apply (ap (ap (fun x : BSigma => x ⊕ T))).
      - apply eisretr.
      - apply inverse. apply eisretr.
  Defined.

  

  Definition BSigma_moncat : Monoidal_1Type :=
    Build_Monoidal_1Type
      (BuildTruncType 1 BSigma) sum_BSigma (canon_BSigma 0) BSigma_assoc BSigma_lid BSigma_rid
      BSigma_triangle1 BSigma_triangle2 BSigma_pentagon.

  Definition group_completion_BSigma := group_completion BSigma_moncat BSigma_lcancel .


  (* Lemma equiv_toempty (A : Type) : *)
  (*   (A -> Empty) <~> (A <~> Empty). *)
  (* Proof.     *)
  (*   apply equiv_iff_hprop. *)
  (*   - intro f. apply (BuildEquiv A Empty f). apply all_to_empty_isequiv. *)
  (*   - apply equiv_fun. *)
  (* Qed. *)
    
  Lemma sum_empty_is_empty (A B : Type) :
    A + B <~> Empty -> A <~> Empty.
  Proof.
    intro e.
    apply (BuildEquiv A Empty (fun a => e (inl a)) ). apply all_to_empty_isequiv.
  Defined.    

  Definition univalent_group_completion_BSigma :
    Categories.IsCategory group_completion_BSigma.
  Proof.
    apply univalent_monactcat; simpl.
    - intros A B.
      intro p.
      apply path_BSigma. simpl.
      apply (sum_empty_is_empty A B).
      apply ((path_BSigma _ _)^-1 p).
    - intro A.
      apply (trunc_equiv' (Empty <~> A)).
      + apply (equiv_path_BSigma (canon_BSigma 0)).
      + apply (trunc_equiv' (A <~> Empty)).
        * apply equiv_equiv_inverse.
        * exact _.
  Qed.

  
  (* Now we prove that associativity of sum_BSigma on canonical finite types correspond to*)
  (* associativity of natural numbers. *)
  (* move to better place? *)
  (* Lemma ap_pr1_assoc (A B C : BSigma) *)
  (*   : (ap pr1 (BSigma_assoc A B C))^ = (plus_assoc (pr1 C) (pr1 B) (pr1 A)). *)
  (* Proof. *)
  (*   apply hset_nat. *)
  (* Qed. *)

  Definition equiv_sum_assoc_Fin (j k l : nat)
    : (Fin l + Fin k) + Fin j <~>
       Fin l + (Fin k + Fin j).
  Proof.
    induction j.
    - refine (_ oE sum_empty_r _).
      apply (equiv_functor_sum_l (sum_empty_r _)^-1).
    - simpl.
      refine (_ oE (equiv_functor_sum' IHj (equiv_idmap Unit)) oE _).
      + refine (_ oE equiv_sum_assoc _ _ _).
        apply equiv_functor_sum_l. apply equiv_sum_assoc.
      + 
        refine (_ oE (equiv_sum_assoc _ _ _)^-1 ). apply equiv_idmap.
  Defined.

  Definition id_equiv_sum_assoc_Fin (j k l : nat)
    : equiv_sum_assoc (Fin l) (Fin k) (Fin j) = equiv_sum_assoc_Fin j k l.
  Proof.
    induction j.
    - simpl. apply path_equiv. apply path_arrow.
      intros [[x | x] | []]; reflexivity.
    - simpl. rewrite <- IHj.
      apply path_equiv. apply path_arrow.
      intros [[x | x] | [x | []]]; reflexivity.
  Defined.
  
  Definition sum_canon_BSigma (j k : nat) :
    sum_BSigma (canon_BSigma j) (canon_BSigma k) = canon_BSigma (k + j)%nat.
  Proof.
    srapply @path_BSigma. apply equiv_finsum.
  Defined.

  Definition canon_assoc (a b c : nat)
    : Fin (a + (b + c)) <~> Fin ((a + b) + c ).
  Proof.
    refine (_ oE (equiv_finsum _ _)^-1).
    refine (_ oE (equiv_functor_sum_r (equiv_finsum _ _))^-1).
    refine (_ oE ((equiv_sum_assoc' _ _ _))).
    refine (equiv_finsum _ _ oE _).
    apply (equiv_functor_sum_l (equiv_finsum _ _)).
  Defined.

  (* Definition canon_assoc (a b c : nat) *)
  (*   : Fin ((a + b) + c ) <~> Fin (a + (b + c)). *)
  (* Proof. *)
  (*   refine (_ oE (equiv_finsum _ _)^-1). *)
  (*   refine (_ oE (equiv_functor_sum_l (equiv_finsum _ _))^-1). *)
  (*   refine (_ oE ((equiv_sum_assoc _ _ _))^-1). *)
  (*   refine (equiv_finsum _ _ oE _). *)
  (*   apply (equiv_functor_sum_r (equiv_finsum _ _)). *)
  (* Defined. *)

  
  Definition equiv_functor_sum_r_compose
    : forall (A A1 A2 B : Type)
             (e1 : A <~> A1)
             (e2 : A1 <~> A2),
      equiv_functor_sum_r (B := B) (e2 oE e1)
      = equiv_functor_sum_r (B:= B) e2 oE equiv_functor_sum_r (B := B) e1.
  Proof.
    intros. apply path_equiv. apply path_arrow.
    intros [x | x]; reflexivity.
  Defined.

  (* move *)
  Definition equiv_finsum_succ (a b : nat)
    : equiv_finsum a (b.+1) = equiv_functor_sum_r (equiv_finsum a b) oE (equiv_sum_assoc' _ _ _)^-1.
  Proof.
    apply path_equiv. apply path_arrow.
    intro x. simpl. apply finsum_succ.
  Defined.

  Definition functor_sum_assoc {A B C A' B' C' : Type} (f : A -> A') (g : B -> B') (h : C -> C')
    : functor_sum (functor_sum f g) h  o (sum_assoc_inv _ _ _) ==
      sum_assoc_inv _ _ _  o (functor_sum f (functor_sum g h)).
  Proof.
    intros [a | [b | c]]; reflexivity.
  Defined.

  Definition functor_sum_idmap (A B: Type)
    : @functor_sum A A B B idmap idmap == idmap.
  Proof.
    intros [a | b]; reflexivity.
  Defined.

  Definition functor_sum_compose {A A1 A2 B B1 B2 : Type}
             (f1 : A -> A1) (f2 : A1 -> A2)
             (g1 : B -> B1) (g2 : B1 -> B2)
    : functor_sum (f2 o f1) (g2 o g1) == functor_sum f2 g2 o functor_sum f1 g1.
  Proof.
    intros [a | b]; reflexivity.
  Defined.

  
  Definition equiv_functor_sum_r_V (A A' B : Type) (e : A <~> A')
    : equiv_functor_sum_r (B := B) (e^-1) = equiv_inverse (equiv_functor_sum_r e).
  Proof.
    apply path_equiv. reflexivity.
  Defined.

  Definition canon_assoc_succ (a b c : nat)
    : canon_assoc (a.+1) b c
      = equiv_functor_sum_r (canon_assoc a b c).
  Proof.    
    unfold canon_assoc. simpl.
    apply emoveR_eV. apply emoveR_eV.
    rewrite equiv_finsum_succ. rewrite equiv_finsum_succ.
    rewrite equiv_finsum_succ.
    repeat rewrite equiv_functor_sum_r_compose.
    repeat rewrite equiv_functor_sum_r_V.
    apply path_equiv. apply path_arrow. intro x. ev_equiv. simpl.
    apply (ap (equiv_functor_sum_r (equiv_finsum c (a + b)))).
    rewrite <- (functor_sum_compose (finsum (b + c) a) (finsum_inv (b + c) a) idmap idmap).
    change (finsum_inv ?x ?y) with ((equiv_finsum x y)^-1).
    change (finsum ?x ?y ?z) with (equiv_finsum x y z).
    rewrite (path_arrow _ _ (eissect (equiv_finsum (b + c) a))).
    rewrite functor_sum_idmap.  simpl.
    rewrite functor_sum_assoc.
    rewrite <- (functor_sum_compose (finsum c b) (finsum_inv c b) idmap (functor_sum idmap idmap)).
    change (finsum_inv c b) with ((equiv_finsum c b)^-1).
    change (finsum c b ?x) with (equiv_finsum c b x).
    rewrite (path_arrow _ _ (eissect (equiv_finsum c b))).    
    destruct x as [[x | x] | [x | x]]; reflexivity.
  Defined.
      
  Definition canon_BSigma_assoc (a b c : nat) :
    canon_BSigma (a + (b + c))%nat = canon_BSigma ((a + b) + c)%nat.
  Proof.
    apply path_BSigma. exact (canon_assoc a b c).
  Defined.

  (* Definition canon_BSigma_succ (a : nat) *)
  (*   : canon_BSigma (a.+1) = sum_BSigma (canon_BSigma a) (canon_BSigma 1). *)
  (* Proof. *)
  (*   apply path_BSigma. apply equiv_functor_sum_l. *)
  (*   simpl. apply equiv_inverse. *)
  (*   apply sum_empty_l. *)
  (* Defined. *)

  (* Definition canon_BSigma_assoc_succ (a b c : nat) *)
  (*   : canon_BSigma_assoc (a.+1) b c *)
  (*     = canon_BSigma_succ _ @ ap (fun x => sum_BSigma x (canon_BSigma 1)) (canon_BSigma_assoc a b c) *)
  (*                         @ (canon_BSigma_succ _)^. *)
  (* Proof. *)
  (*   unfold canon_BSigma_assoc. unfold canon_BSigma_succ. *)
  (*   apply moveR_Vp. apply moveR_Vp. *)
  (*   unfold sum_canon_BSigma.     *)
  (*   repeat rewrite path_BSigma_V. simpl. *)
  (*   rewrite natural_path_BSigma_l. rewrite natural_path_BSigma_l. *)
  (*   rewrite natural_path_BSigma_r. rewrite natural_path_BSigma_r. *)
  (*   rewrite path_BSigma_V.  *)
  (*   repeat rewrite <- path_BSigma_compose. *)
  (*   rewrite natural_path_BSigma_l. repeat rewrite <- path_BSigma_compose. *)
    
  (*   apply (ap path_BSigma).  *)
  (*   apply path_equiv. apply path_arrow. *)
  (*   intros [x | [x | [x | x]]]; simpl. *)
  (*   - apply (ap inl). *)
  (*     unfold finsum.  *)
  (*   unfold canon_BSigma in x. unfold canon in x.  *)
  (*   simpl in x. *)
    
    
    
    
    

  Definition eq_canon_BSigma_assoc (a b c : nat)
    : canon_BSigma_assoc a b c = ap canon_BSigma (plus_assoc a b c)^.
  Proof.
    unfold canon_BSigma_assoc.
    induction a.
    - simpl. unfold canon_assoc.
      refine (_ @ path_BSigma_1 _).
      apply (ap (path_BSigma _ _)).
      apply emoveR_eV.
      refine (_ @ (ecompose_1e _)^).
      apply emoveR_eV.
      apply path_equiv. apply path_arrow.
      intros [[x | x] | []]; reflexivity.
    - rewrite canon_assoc_succ.
      simpl.
      assert (H : forall (m n : nat) (p : m = n),
                 ap canon_BSigma (ap S p)
                 = @path_BSigma (canon_BSigma (m.+1)) (canon_BSigma (n.+1))
                     (equiv_functor_sum_r
                        (B := Unit)
                        ((equiv_path_BSigma (canon_BSigma (m)) (canon_BSigma (n)))^-1
                                      (ap canon_BSigma p)))).
      { intros m n []. simpl.
        apply inverse. refine (_ @ path_BSigma_1 _).
        apply (ap (path_BSigma _ _)). apply path_equiv. simpl. apply path_arrow.
        intros [x|x]; reflexivity. }
      rewrite <- ap_V.
      rewrite H. clear H.
      apply (ap (path_BSigma _ _)). apply (ap equiv_functor_sum_r).
      apply moveL_equiv_V.
      apply IHa.
  Qed.
  
End BSigma.



      


Definition add_canon (m n : nat) :
  pMap (Build_pType (Finite_Types n) _) (Build_pType (Finite_Types (n+m)) _).
Proof.
  srapply @Build_pMap.
  - simpl. intro B. exact (sum_finite_types (canon m) B).
  - exact (path_finite_types
             (n+m)
             (sum_finite_types (canon m) (canon n))
             (canon (n+m))
             (equiv_finsum m n)).
Defined.



