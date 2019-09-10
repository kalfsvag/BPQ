Require Import HoTT.

From GC Require Import pointed_lemmas finite_lemmas nat_lemmas trunc_lemmas (* monoidal_1type *)
                       group_complete_1type.

(*Defining the monoidal 1-type of finite sets and isomorphisms*)
Section BSigma.
    
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Definition BSigma :=
    {m : nat & Finite_Types m}.
    (* { S : Type & Finite S}. *)
  Definition type_of_fin : BSigma -> Type := (fun A => A.2.1).
  Coercion type_of_fin : BSigma  >-> Sortclass.

  Global Instance istrunc_BSigma : IsTrunc 1 BSigma.
  Proof.
    apply (trunc_equiv' {S : Type & Finite S}).
    - apply equiv_inverse. apply fin_decompose.
    - apply trunc_sigma'.
      +  intro A. exact _.
      +  intros A B.
         srapply @istrunc_paths_Type. 
         apply isset_Finite. exact B.2.
  Defined.

  (*Canonical objects in BSigma*)
  Definition canon_BSigma (n : nat) : BSigma := (n; canon n).

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
  Definition path_BSigma {A B : BSigma} : A <~> B -> A = B
       := equiv_path_BSigma A B.
  (* Proof. *)
  (*   destruct A as [m A]. destruct B as [n B]. simpl. *)
  (*   intro e. *)
  (*   destruct (finite_types_eqcard A B e). *)
  (*   apply (path_sigma (fun m : nat => Finite_Types m) (m; A) (m;B) idpath). simpl. *)
  (*   apply path_finite_types_fix. *)
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
    path_BSigma (equiv_idmap A) = idpath.
  Proof.
    refine (ap (path_BSigma) (eissect (@path_BSigma A A) equiv_idmap)^ @ _).
    apply moveR_equiv_M.
    refine (eissect _ _ @ _). simpl.
    reflexivity.
  Defined.

  Definition path_BSigma_V {A B : BSigma} (e : A <~> B)
    : (path_BSigma e)^ = path_BSigma (equiv_inverse e).
  Proof.
    refine (_ @ ap (fun g => path_BSigma (equiv_inverse g)) (eissect (@path_BSigma A B) e)).
    generalize (path_BSigma e).  intros [].
    simpl. apply inverse.
    refine (_ @ path_BSigma_1 A).
    apply (ap path_BSigma).
    apply path_equiv. simpl.  reflexivity.
  Defined.

  (* (* path_BSigma respects composition *) *)  
  Definition path_BSigma_compose {A B C : BSigma} (e1 : A <~> B) (e2 : B <~> C) :
    path_BSigma (e2 oE e1) = path_BSigma e1 @ path_BSigma e2.
  Proof.
    (* path_BSigma e2 @ path_BSigma e1 = path_BSigma (e1 oE e2). *)
  Proof.
    refine
      (ap011 (fun g1 g2 => path_BSigma (g2 oE g1))
             (eissect (@path_BSigma A B) e1)^ (eissect (@path_BSigma B C) e2)^ @ _).
    generalize (path_BSigma e2). intros []. 
    generalize (path_BSigma e1). intros []. simpl.
    refine (path_BSigma_1 A).
  Qed.
    

  Definition plus_BSigma : BSigma -> BSigma -> BSigma.
  Proof.
    intros [m A] [n B].
    exists (n + m)%nat.
    exact (sum_finite_types A B).
  Defined.

  Definition BSigma_id : BSigma := canon_BSigma 0.

  Local Notation "S1 ⊕ S2" := (plus_BSigma S1 S2) (at level 50, no associativity).

  (* (* symmetry *) *)
  (* Definition path_BSigma_twist (a b : nat) : *)
  (*   (@path_BSigma *)
  (*     (plus_BSigma (canon_BSigma a) (canon_BSigma b)) *)
  (*     (plus_BSigma (canon_BSigma b) (canon_BSigma a)) *)
  (*     (equiv_sum_symm (canon_BSigma a) (canon_BSigma b))) *)
  (*   @ *)
  (*     @path_BSigma *)
        
  (*       (plus_BSigma (canon_BSigma b) (canon_BSigma a)) *)
  (*       (canon_BSigma _) *)
  (*       (fin_resp_sum b a) *)
  (*   = *)
  (*   @path_BSigma *)
  (*     (plus_BSigma (canon_BSigma a) (canon_BSigma b)) *)
  (*     (canon_BSigma _) *)
  (*     (fin_resp_sum a b) *)
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
    : ap (fun x : BSigma => x ⊕ S3) (path_BSigma e)
    = path_BSigma (A := S1 ⊕ S3) (B := S2 ⊕ S3) (equiv_functor_sum_r (B := S3) e).
  Proof.    
    refine (_ @ ap (fun e' => @path_BSigma (S1⊕ S3) (S2 ⊕ S3) (equiv_functor_sum_r e'))
              (eissect (@path_BSigma S1 S2) e)).
    generalize (path_BSigma e). intros [].
    simpl. apply inverse.
    refine (_ @ path_BSigma_1 (S1 ⊕ S3)).
    apply (ap (path_BSigma )).
    apply path_equiv. apply path_arrow. intros [s1 | s3]; reflexivity.
  Qed.

  Definition natural_path_BSigma_r {S1 S2 S3: BSigma} (e : S2 <~> S3)
    : ap (fun x : BSigma => S1 ⊕ x) (path_BSigma e)
      = path_BSigma (A := S1 ⊕ S2) (B := S1 ⊕ S3) (equiv_functor_sum_l (A := S1) e).
  Proof.
    refine (_ @ ap (fun e' => @path_BSigma (S1 ⊕ S2) (S1 ⊕ S3) (equiv_functor_sum_l e'))
              (eissect (@path_BSigma S2 S3) e)).
    generalize (path_BSigma e). intros [].
    simpl. apply inverse.
    refine (_ @ path_BSigma_1 (S1 ⊕ S2)).
    apply (ap (path_BSigma)).
    apply path_equiv. apply path_arrow. intros [s1 | s2]; reflexivity.
  Qed.
  
  (*The monoidal structure on BSigma*)
  
  Definition BSigma_assoc : associative plus_BSigma.
  Proof.
    intros S1 S2 S3.
    apply path_BSigma.
    apply equiv_sum_assoc. 
  Defined.

  Definition BSigma_lid : left_identity_mult plus_BSigma (canon_BSigma 0).
  Proof.
    intro S. apply path_BSigma.
    apply sum_empty_l.
  Defined.
  
  Definition BSigma_rid : right_identity_mult plus_BSigma (canon_BSigma 0).
  Proof.
    intro S. apply path_BSigma.
    apply sum_empty_r.
  Defined.

  Definition BSigma_symmetric : symmetric plus_BSigma. 
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
    apply (ap path_BSigma).
    apply path_equiv. apply path_arrow.
    intros [[[] | s1] | s2]; reflexivity.
  Qed.

  Definition BSigma_triangle2 : coherence_triangle2 BSigma_assoc BSigma_lid BSigma_rid.
  Proof.
    intros S1 S2. unfold BSigma_rid. unfold BSigma_assoc. unfold BSigma_lid. simpl.
    refine (natural_path_BSigma_l _ @ _).
    refine (_ @ whiskerL _ (natural_path_BSigma_r _)^).
    refine (_ @ (path_BSigma_compose  _ _)).
    apply (ap path_BSigma).
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
    apply (ap path_BSigma).
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
      (BuildTruncType 1 BSigma) plus_BSigma (canon_BSigma 0) BSigma_assoc BSigma_lid BSigma_rid
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
      apply ((path_BSigma)^-1 p).
    - intro A.
      apply (trunc_equiv' (Empty <~> A)).
      + apply (equiv_path_BSigma (canon_BSigma 0)).
      + apply (trunc_equiv' (A <~> Empty)).
        * apply equiv_equiv_inverse.
        * exact _.
  Qed.

  
  (* Now we prove that associativity of plus_BSigma on canonical finite types correspond to*)
  (* associativity of natural numbers. *)
  (* move to better place? *)
  Lemma ap_pr1_assoc (A B C : BSigma)
    : (ap pr1 (BSigma_assoc A B C))^ = (plus_assoc (pr1 C) (pr1 B) (pr1 A)).
  Proof.
    apply hset_nat.
  Qed.

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
    plus_BSigma (canon_BSigma j) (canon_BSigma k) = canon_BSigma (k + j)%nat.
  Proof.
    srapply @path_BSigma. apply fin_resp_sum.
  Defined.    
    
  Definition canon_BSigma_assoc (j k l : nat) :
    canon_BSigma (j + k + l)%nat = canon_BSigma (j + (k + l))%nat.
  Proof.
    refine ((sum_canon_BSigma _ _)^ @ _).
    refine ((ap (plus_BSigma (canon_BSigma l)) (sum_canon_BSigma _ _))^ @ _).
    refine ((BSigma_assoc _ _ _)^ @ _).
    refine (_ @ sum_canon_BSigma _ _).
    refine (ap (fun x => plus_BSigma x (canon_BSigma j)) (sum_canon_BSigma _ _)).
  Defined.

  Definition eq_canon_BSigma_assoc (j k l : nat)
    : canon_BSigma_assoc j k l = ap canon_BSigma (plus_assoc j k l).
  Proof.
    unfold canon_BSigma_assoc.
    apply moveR_Vp. apply moveR_Vp.
    unfold BSigma_assoc. simpl.
    unfold sum_canon_BSigma.
    rewrite natural_path_BSigma_l. rewrite natural_path_BSigma_r.
    rewrite path_BSigma_V. (* rewrite id_equiv_sum_assoc_Fin. *)
    refine (_ @ concat_pp_p _ _ _).
    repeat rewrite <- path_BSigma_compose.
    apply moveL_Mp.
    induction j.
    - apply moveR_Vp.
      simpl.
      refine (_ @ (concat_p1 _)^).
      apply (ap path_BSigma).
      apply path_equiv. apply path_arrow. simpl.
      intros [x | [y | []]]; reflexivity.
    - simpl.
      
      
      refine (_ @ ap_compose S canon_BSigma (plus_assoc j k l)).
      assert 
      assert (H : forall x : nat, canon_BSigma x.+1 = plus_BSigma (canon_BSigma x) (canon_BSigma 1)).
      { intro x. apply path_BSigma. 
        apply equiv_functor_sum_l. apply equiv_inverse. apply sum_empty_l. }
      rewrite (path_arrow (fun x : nat => canon_BSigma x.+1)
                          (fun x : nat => plus_BSigma (canon_BSigma x) (canon_BSigma 1)) H).
      assert (H : forall (m n : nat) (p : m = n),
                 ap canon_BSigma (ap S p)
                 = @path_BSigma (canon_BSigma (m.+1)) (canon_BSigma (n.+1))
                     (equiv_functor_sum_r
                        (B := Unit)
                        ((equiv_path_BSigma (canon_BSigma (m)) (canon_BSigma (n)))^-1
                                      (ap canon_BSigma p)))).
      { intros m n []. simpl.
        apply inverse. refine (_ @ path_BSigma_1 _).
        apply (ap path_BSigma). apply path_equiv. simpl. apply path_arrow.
        intros [x|x]; reflexivity. }
      rewrite H. clear H. rewrite <- path_BSigma_compose.
      apply (ap path_BSigma).
      simpl.
      rewrite <- IHj.  clear IHj. apply moveR_Vp. rewrite <- path_BSigma_compose.
      apply (ap path_BSigma). 
      rewrite path_BSigma_V. rewrite <- path_BSigma_compose.
      change (path_BSigma ?f) with (equiv_path_BSigma _ _ f).
      refine (_ @ ap (fun f => equiv_functor_sum_r (B:= Unit) f
                     oE (fin_resp_sum l (j + k).+1 oE equiv_functor_sum_l (fin_resp_sum k j.+1)))
                (eissect
                   (equiv_path_BSigma (canon_BSigma (j + k + l)) (canon_BSigma (j + (k + l))))
                   (fin_resp_sum (k + l) j oE equiv_functor_sum_r (fin_resp_sum l k)
                                 oE (equiv_sum_assoc (Fin l) (Fin k) (Fin j))^-1
                                 oE (fin_resp_sum l (j + k)
                                                  oE equiv_functor_sum_l (fin_resp_sum k j))^-1)
                )^).
      (* move *)
      assert (equiv_functor_sum_r_compose : forall (A A1 A2 B : Type)
                                                   (e1 : A <~> A1)
                                                   (e2 : A1 <~> A2),
                 equiv_functor_sum_r (B := B) (e2 oE e1)
                 = equiv_functor_sum_r (B:= B) e2 oE equiv_functor_sum_r (B := B) e1).
      { intros. apply path_equiv. apply path_arrow.
        intros [x | x]; reflexivity. }
      rewrite equiv_functor_sum_r_compose. rewrite equiv_functor_sum_r_compose.
      rewrite equiv_functor_sum_r_compose. clear equiv_functor_sum_r_compose.
      apply (ap011 (fun f g => f oE g)).
      apply path_equiv. apply path_arrow.
      intros [x | x]; simpl.
      intros [x | [x | [x | x]]]; simpl.
      + apply (ap inl). simpl.
        
      
      


      apply moveL_equiv_V. change (equiv_path_BSigma _ _ ?f) with (path_BSigma f).
      rewrite (eissect (equiv_path_BSigma _ _) (equiv_sum_assoc_Fin j k l)).
      
      
refine (path_BSigma_compose _ _ @ _).
      
      unfold canon_BSigma_assoc. simpl.
      unfold sum_canon_BSigma. simpl.
      rewrite natural_path_BSigma_l. rewrite natural_path_BSigma_r.
      rewrite path_BSigma_V. rewrite path_BSigma_V.
      unfold BSigma_assoc.
      apply (inverse2 (q := idpath)).
      rewrite <- path_BSigma_compose.
      rewrite <- path_BSigma_compose.
      rewrite <- path_BSigma_compose.
      rewrite <- path_BSigma_compose.
      refine (_ @ path_BSigma_1 _).
      apply (ap path_BSigma). simpl.
      refine (ecompose_e_ee _ _ _ @ _).
      apply (emoveR_eV).
      refine (ecompose_e_ee _ _ _ @ _).
      apply emoveR_eV.      
      apply path_equiv. simpl. apply path_arrow.
      
    - simpl. unfold canon_BSigma_assoc.  simpl.
      unfold canon_BSigma_assoc in IHj.
      
      apply (ap (inverse).

  
End BSigma.



      


Definition add_canon (m n : nat) :
  pMap (Build_pType (Finite_Types n) _) (Build_pType (Finite_Types (n+m)) _).
Proof.
  srapply @Build_pMap.
  - simpl. intro B. exact (sum_finite_types (canon m) B).
  - exact (path_finite_types_fix
             (n+m)
             (sum_finite_types (canon m) (canon n))
             (canon (n+m))
             (fin_resp_sum m n)).
Defined.



