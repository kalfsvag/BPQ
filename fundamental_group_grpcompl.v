Require Import HoTT.

(* Print LoadPath. *)
Add Rec LoadPath "~/Coq-projects/groupoids" as GR.
(* Print LoadPath. *)

From GR Require Import cquot cquot_principles.
From GC Require Import finite_lemmas (* path_finite_types *) monoids_and_groups path_lemmas
                       group_complete_1type BSigma delooping permutations determinants pointed_lemmas.

Definition iso_path_finite_types (m n: nat)
  : Isomorphism (SymGrp m) (loopGroup (Finite_Types m) (canon m)).
Proof.
  srapply Build_Grp_Iso'.
  - simpl. apply (equiv_path_finite_types_fix m (canon m) (canon m)).
  - intros alpha beta. simpl.
    apply (path_finite_types_fix_compose m (canon m) (canon m) (canon m) alpha beta).
Defined.

Definition deloop_fin (m n : nat)
  : Homomorphism (SymGrp m) (SymGrp n) -> Finite_Types m -> Finite_Types n.
Proof.
  intro f.
  srefine (deloop_rec (pFin m) (Finite_Types n) (canon n) _ _).
  - 
    apply (@hom_map (loopGroup (Finite_Types m) (canon m)) (loopGroup (Finite_Types n) (canon n))).
    apply (functor_hom
             (iso_inv (iso_path_finite_types m m))
             (iso_path_finite_types n n) f).
  - intros.
    apply (preserve_mult
             (functor_hom (iso_inv (iso_path_finite_types m m)) (iso_path_finite_types n n) f)).
Defined.  

Definition deloop_fin_canon (m n : nat) (f : Homomorphism (SymGrp m) (SymGrp n))
  : deloop_fin m n f (canon m) = canon n.
Proof.
  unfold deloop_fin.
  apply deloop_rec_beta_pt.
Defined.

Definition deloop_fin_loop (m n : nat) (f : Homomorphism (SymGrp m) (SymGrp n))
           (ω : canon m = canon m)
  : (deloop_fin_canon m n f)^ @ ap (deloop_fin m n f) ω  @ (deloop_fin_canon m n f)
    = (functor_hom
         (iso_inv (iso_path_finite_types m m))
         (iso_path_finite_types n n) f) ω.
      
Proof.
  apply deloop_rec_beta_loop.
Defined.

Definition dethom (m : nat) : Homomorphism (SymGrp m) (SymGrp 2).
Proof.
  srapply @Build_GrpHom.
  + apply determinant.
  + apply det_compose.
Defined.

Definition BDet (m : nat) :=
  deloop_fin m 2 (dethom m).

Definition path_triple_prod {A B C : Type} (a1 a2 : A * (B * C)) :
  (fst a1 = fst a2) * ((fst (snd a1) = fst (snd a2)) * (snd (snd a1) = snd (snd a2))) -> a1 = a2.
Proof.
  intros [p [q r]].
  apply (path_prod a1 a2 p (path_prod (_,_) (_,_) q r)).
Defined.
  
Definition equiv_path_triple_prod {A B C : Type} (a1 a2 : A * (B * C)) :
  (fst a1 = fst a2) * ((fst (snd a1) = fst (snd a2)) * (snd (snd a1) = snd (snd a2))) <~> a1 = a2.
Proof.
  srapply (@equiv_adjointify _ _ (path_triple_prod a1 a2)).
  - intro p.
    exact (ap fst p, (ap fst (ap snd p), (ap snd (ap snd p)))).
  - intros []. reflexivity.
  - intros [p [q r]].
    destruct a2 as [a2 [b2 c2]]. simpl in *.
    destruct p,q,r. reflexivity.
Defined.

Local Definition pft {m : nat}
  := path_finite_types_fix m.

Local Definition pft_inv {m : nat} {A B}
  := inv_path_finite_types_fix m A B.

(* move *)
Definition SymGrp2_cases (sigma : Fin 2 <~> Fin 2)
  : (sigma = equiv_idmap) + (sigma = twist2).
Proof.
  recall (sigma (inr tt)) as x eqn:p.
  destruct x as [[[] | []] | []].
  - apply inr.
    apply path_equiv. apply path_arrow. apply sigma2_notfixlast. exact p.
  - apply inl.
    apply path_equiv. apply path_arrow. apply sigma2_fixlast. exact p.
Defined.

Lemma invol_SymGrp2 (sigma : Fin 2 <~> Fin 2)
  : (sigma oE sigma) = equiv_idmap.
Proof.
  destruct (SymGrp2_cases sigma) as [p | p].
  - refine (ap011 equiv_compose' p p @ _).
    apply path_equiv. reflexivity.
  - refine (ap011 equiv_compose' p p @ _).
    apply path_equiv. apply path_arrow.
    intros [[[] | []] | []]; reflexivity.
Qed.

Lemma path_finite_types_sum {a1 a2 : nat}
           (A1 : Finite_Types a1) (A2 : Finite_Types a2)
           (B1 : Finite_Types a1) (B2 : Finite_Types a2)
           (e1 : A1 <~> B1) (e2 : A2 <~> B2)
  : path_finite_types_fix _ (sum_finite_types A1 A2) (sum_finite_types B1 B2)
                          (e1 +E e2)
    = ap011 sum_finite_types
            (path_finite_types_fix _ _ _ e1)
            (path_finite_types_fix _ _ _ e2).
Proof.
  revert e1.
  apply (equiv_functor_forall_pf (equiv_path_finite_types_fix _ A1 B1)).
  intro p. revert e2.
  apply (equiv_functor_forall_pf (equiv_path_finite_types_fix _ A2 B2)).
  intro q.
  destruct p. destruct q.
  simpl.
  refine (_ @ path_finite_types_fix_id (a2 + a1) (sum_finite_types A1 A2) @ _).
  - apply (ap (path_finite_types_fix (a2 + a1) (sum_finite_types A1 A2) (sum_finite_types A1 A2))).
    apply path_equiv. apply path_arrow. intros [x | y]; reflexivity.
  - apply inverse.
    apply (ap011 (ap011 sum_finite_types)
                 (path_finite_types_fix_id a1 A1)
                 (path_finite_types_fix_id a2 A2)).
Defined.

Lemma ap011_VV
  : forall {A B C: Type} (f : A -> B -> C)
           {a0 a1 : A} {b0 b1 : B}
           (p : a0 = a1) (q : b0 = b1),
    (ap011 f p q)^ = ap011 f p^ q^.
Proof.
  intros. destruct p. destruct q. reflexivity.
Defined.

  





Local Definition Z := cquot (group_completion_BSigma).
Require Import Category.Core.
Section BSigma_set_ind.
  Definition cquot_rec' {C : PreCategory} (Y : Type)
             (cclY : C -> Y)
             (ccleqY : forall {a₁ a₂ : C},
                 C a₁ a₂ -> cclY a₁ = cclY a₂)
             (* (ceY : forall (a : C), ccleqY (identity a) = idpath) *)
             (cconcatY : forall (a₁ a₂ a₃: C) (c₁: C a₁ a₂) (c₂: C a₂ a₃),
                 ccleqY (c₂ o c₁)%morphism = ccleqY c₁ @ ccleqY c₂)
             {truncY : IsTrunc 1 Y}
  : cquot C -> Y.
  Proof.
    refine (cquot_rec Y cclY ccleqY _ cconcatY).
    intro c.
    apply (cancelL (ccleqY c c 1%morphism)).
    refine ((cconcatY c c c _ _)^ @ _).
    refine (ap (ccleqY c c) (left_identity C c c _) @ _).
    apply inverse. apply concat_p1.
  Defined.
    

  
Definition fin_resp_sum_id (m n : nat) :
  sum_finite_types (canon m) (canon n) = canon (n+m) :=
  path_finite_types_fix (n+m) (sum_finite_types (canon m) (canon n)) (canon (n+m)) (fin_resp_sum m n).

(* Define this in a bit of a roundabout manner so that it uses fin_resp_sum_id *)
Definition canon_grpclBSigma_sum (m1 m2 n1 n2 : nat) :
  ccl (group_completion_BSigma)
      (functor_prod (plus_BSigma (canon_BSigma m1)) (plus_BSigma (canon_BSigma m2)) (canon_BSigma n1, canon_BSigma n2)) =
  ccl (group_completion_BSigma)
      (canon_BSigma (n1+m1), (canon_BSigma (n2+m2))).
Proof.
  apply (ap (ccl group_completion_BSigma)). unfold plus_BSigma. simpl.
  unfold functor_prod. simpl. unfold canon_BSigma.
  exact (ap (fun x : Finite_Types (n1 + m1) * Finite_Types (n2+m2) =>
               ((n1 + m1; (fst x)), (n2 + m2; (snd x))))
        (path_prod (_,_) (_,_) (fin_resp_sum_id m1 n1) (fin_resp_sum_id m2 n2)))%nat.
Defined.

Definition ccleq_canon (m n s : nat) :
  (ccl (group_completion_BSigma) ((canon_BSigma m), (canon_BSigma n))) =
  (ccl (group_completion_BSigma) ((canon_BSigma (m+s)), (canon_BSigma (n+s)))) :=
  (ccleq group_completion_BSigma ((s; canon s); idpath)) @ canon_grpclBSigma_sum s s m n.

(* Auxillary stuff. Move? *)
Definition double_transport {A B : Type} (P : A -> B -> Type) {a1 a2 : A} {b1 b2 : B} :
  a1 = a2 -> b1 = b2 -> P a1 b1 -> P a2 b2.
Proof.
  intros [] []. exact idmap.
Defined.

Definition double_apD {A B : Type} (P : A -> B -> Type)
           (f : forall (a : A) (b : B), P a b)
           {a1 a2 : A} {b1 b2 : B}
           (p : a1 = a2) (q : b1 = b2) :
  double_transport P p q (f a1 b1) = f a2 b2.
Proof.
  destruct p. destruct q. reflexivity.
Defined.

Definition double_uncurry {A B : Type} (P : A -> B -> Type) :
  (forall (a : A) (b : B), P a b) -> (forall ab : A*B, P (fst ab) (snd ab)).
Proof.
  intro f.
  intros [a b]. exact (f a b).
Defined.

(* Local Open Scope nat_scope. *)

Definition grp_compl_BSigma_rec
           (P : 1-Type)
           (f : BSigma -> BSigma -> P)
           (act_add : forall (S A1 A2:  BSigma),
                             f A1 A2 = f (plus_BSigma S A1) (plus_BSigma S A2))
           (act_add_compose : forall (S T A1 A2 : BSigma),
               act_add (plus_BSigma T S) A1 A2
                       @ (ap011 f (BSigma_assoc T S A1) (BSigma_assoc T S A2))
               = act_add S A1 A2 @ act_add T (plus_BSigma S A1) (plus_BSigma S A2))
  : Z -> P.
Proof.
  set (uncurry_f :=
         fun x : BSigma * BSigma =>
           match x with
             (A1, A2) => f A1 A2 end).
  srapply @cquot_rec'.
  - simpl. intros [A1 A2]. exact (f A1 A2).
  - simpl. intros [A1 A2]. intro B.
    unfold monoidal_action_morphism.
    intros [S p]. simpl in p.
    refine (act_add S _ _ @ _).
    apply (ap uncurry_f p).
  - intros [A1 A2]. intros B C.
    intros [S p]. intros [T q]. 
    destruct q. destruct p. simpl. repeat rewrite concat_p1.
    refine (_ @ act_add_compose _ _ _ _).
    apply whiskerL.
    generalize (BSigma_assoc T S A2) as q. 
    generalize (BSigma_assoc T S A1) as p.
    cut (forall (B1 B2 : BSigma)
                (p : plus_BSigma (plus_BSigma T S) A1 = B1)
                (q : plus_BSigma (plus_BSigma T S) A2 = B2),
            ap uncurry_f
               (path_prod
                  (functor_prod
                     (plus_BSigma (plus_BSigma T S)) (plus_BSigma (plus_BSigma T S)) (A1, A2))
                  (B1, B2) p q)
            = ap011 f p q).
    { intro H. apply H. }
    intros B1 B2. intros [] []. reflexivity.
Defined.



(* change to only one act? *)
Definition grp_compl_BSigma_ind_set
           (P : Z -> hSet)
           (f : forall (m n : nat), P (ccl (group_completion_BSigma) ((canon_BSigma m), (canon_BSigma n))))
           (act_r :
              forall (m n : nat) (σ : canon n = canon n),
                transport
                  (fun x : (Finite_Types n) =>
                     P (ccl (group_completion_BSigma) ((canon_BSigma m), (n; x)))) σ (f m n) = (f m n))
           (act_l :
              forall (m n : nat) (σ : canon m = canon m),
                transport
                  (fun x : (Finite_Types m) =>
                     P (ccl (group_completion_BSigma) ((m; x), (canon_BSigma n)))) σ (f m n) = (f m n))
  
           (act_add :
              (forall (m n : nat) (s : nat),
                transport P (ccleq_canon m n s) (f m n) = f (m+s)%nat (n+s)%nat))
           : forall z : Z, P z.
  Proof.
    srapply @cquot_ind_set.
    - simpl.
      intros [[m x] [n y]]. revert x y.
      srefine (deloop_double_ind_set
               (pFin m) 
               (pFin n)
               _
               (f m n)
               _ _
               
             ).
      + intro.
        simpl. apply act_r. 
      + simpl.
        apply act_l.
    - simpl. unfold monoidal_action_morphism.
      intros [[m a1] [n a2]] b [s p].  destruct p. simpl.
      revert a2.
      srefine (deloop_ind_prop
               (pFin n) 
               _ _).
      revert a1.
      srefine (deloop_ind_prop
               (pFin m)
               _ _).
      destruct s as [s x]. revert x.
      srefine (deloop_ind_prop
               (pFin s)
               _ _).
      simpl.
      rewrite deloop_double_ind_set_beta_pt.
      (* endre til transport bla bla = transport ble ble *)
      set (g := double_uncurry _
                  (deloop_double_ind_set
                     (pFin (m + s))
                     (pFin (n + s))
                     (fun (x1 : Finite_Types (m + s)) (x2 : Finite_Types (n + s)) =>
                        P (ccl group_completion_BSigma ((m + s; x1), (n + s; x2)))) (f (m + s) (n + s))
                     (fun ω : canon (n + s) = canon (n + s) =>
                        act_r (m + s) (n + s) ω) (act_l (m + s) (n + s)))%nat).
      unfold point. 
      change (deloop_double_ind_set (pFin (m + s)) 
                                    (pFin (n + s)) 
       (fun (x1 : Finite_Types (m + s)) (x2 : Finite_Types (n + s)) =>
        P (ccl group_completion_BSigma ((m + s; x1), (n + s; x2)))) (f (m + s) (n + s))
       (fun ω : canon (n + s) = canon (n + s) => act_r (m + s) (n + s) ω) (act_l (m + s) (n + s))
       (sum_finite_types (canon s) (canon m)) (sum_finite_types (canon s) (canon n)))%nat
             with
             (g (sum_finite_types (canon s) (canon m), sum_finite_types (canon s) (canon n))).
      rewrite <-
              (apD g (path_prod (_,_) (_,_) (fin_resp_sum_id s m) (fin_resp_sum_id s n))^).
      unfold g. unfold double_uncurry.
      rewrite deloop_double_ind_set_beta_pt. clear g.
      apply path_to_path_over.
      rewrite <- act_add.
      refine (_ @
                (transport_compose
                   P (fun ab : Finite_Types (m + s) * Finite_Types (n + s) =>
                        (ccl group_completion_BSigma ((m + s; fst ab), (n + s; snd ab))%nat))
                   ((path_prod
                      (sum_finite_types (canon s) (canon m), sum_finite_types (canon s) (canon n))
                      (canon (m + s), canon (n + s)) (fin_resp_sum_id s m) (fin_resp_sum_id s n))^)
                   (transport (fun x : Z => P x) (ccleq_canon m n s) (f m n)))^).
      change (cquot group_completion_BSigma) with Z.
      refine (_ @ transport_pp P _ _ _).
      apply (ap (fun p => transport P p (f m n))). simpl.
      unfold ccleq_canon.
      unfold canon_grpclBSigma_sum.
      refine (_ @ concat_p_pp _ _ _).
      refine ((concat_p1 _)^ @ _).
      apply whiskerL. apply moveL_pM.
      refine (concat_1p _ @ _).
      refine ((ap inverse (ap_V _ _ )@ _)).
      refine (inv_V _ @ _).
      refine ((ap_compose _ _ _)).
  Defined.

End BSigma_set_ind.

  


Section GrpCompl_To_Fin2.

  Definition det_sasb (s a b : nat)
             (sigma : SymGrp s) (alpha : SymGrp a) (betta : SymGrp b) :
    determinant ((b+s)+(a+s)) (block_sum (block_sum sigma alpha) (block_sum sigma betta))
    = determinant (b+a) (block_sum alpha betta).
  Proof.
    refine (det_block_sum _ _ @ _).
    refine (ap011 equiv_compose' (det_block_sum _ _) (det_block_sum _ _) @ _).
    refine (ecompose_ee_e _ _ _ @ _).
    refine (_ @ (det_block_sum _ _)^).
    apply (ap (equiv_compose' (determinant b betta))).
    refine (ap (equiv_compose' (determinant s sigma))
               (symm_sigma2 _ _) @ _).               
    refine (ecompose_e_ee _ _ _ @ _).
    refine (_ @ ecompose_1e _).
    apply (ap (fun f => f oE determinant a alpha)).
    apply invol_SymGrp2.
  Qed.

  Definition BDet_SASB_canon (s a1 a2 : nat) :
    BDet (a2 + a1) (sum_finite_types (canon a1) (canon a2)) =
    BDet (a2 + s + (a1 + s))
         (sum_finite_types
            (sum_finite_types (canon s) (canon a1))
            (sum_finite_types (canon s) (canon a2))).
  Proof.
    transitivity (canon 2).
      * refine (_ @ (deloop_fin_canon (a2 + a1) 2 (dethom _))).
        apply (ap (BDet (a2 + a1)) (sum_finite_types_canon)).
      * apply inverse.
        refine (_ @ (deloop_fin_canon (a2 + s + (a1 + s)) 2 (dethom (a2 + s + (a1 + s))))).
        apply (ap (BDet _)).
        refine (_ @ sum_finite_types_canon).
        apply (ap011 sum_finite_types); apply sum_finite_types_canon.
  Defined.
  
  Definition BDet_SASB (s a1 a2 : nat)
             (S : Finite_Types s) (A1 : Finite_Types a1) (A2 : Finite_Types a2)
  : BDet (a2 + a1) (sum_finite_types A1 A2) =
    BDet (a2 + s + (a1 + s)) (sum_finite_types (sum_finite_types S A1) (sum_finite_types S A2)).
  Proof.
    revert S A1 A2.
    cut (forall SA : (Finite_Types s) * ((Finite_Types a1) * (Finite_Types a2)),
            BDet (a2 + a1) (sum_finite_types (fst (snd SA)) (snd (snd SA))) =
            BDet (a2 + s + (a1 + s))
                 (sum_finite_types (sum_finite_types (fst SA) (fst (snd SA)))
                                   (sum_finite_types (fst SA) (snd (snd SA))))).
    { intros H S A1 A2. exact (H (S, (A1, A2))). }    
    srapply (@deloop_ind_set (conn_ptype_prod (pFin s)
                                              (conn_ptype_prod (pFin a1) (pFin a2)))).
    + simpl. unfold point.
      apply BDet_SASB_canon.
    + simpl. unfold point. intro.
      refine (transport_paths_FlFr ω _ @ _).
      (* revert ω. *)
      (* apply (equiv_functor_forall_pf *)
      (*          (equiv_inverse (equiv_path_prod (_,_) (_,_)))). *)
      (* simpl. intros [sigma p]. revert p. *)
      (* apply (equiv_functor_forall_pf *)
      (*          (equiv_inverse (equiv_path_prod (_,_) (_,_)))). simpl. *)
      (* intros [alpha betta]. *)
      
      assert (
          p : forall (x : Finite_Types s * (Finite_Types a1 * Finite_Types a2))
                     (q : (canon s, (canon a1, canon a2)) = x),
            (ap
               (fun x : Finite_Types s * (Finite_Types a1 * Finite_Types a2) =>
                  BDet (a2 + a1) (sum_finite_types (fst (snd x)) (snd (snd x)))) q)
            =
            ap (BDet (a2 + a1))
               (ap011 sum_finite_types
                      (ap fst (ap snd q))
                      (ap snd (ap snd q)))).
      { intros x []. reflexivity. }
      rewrite (p _ ω). clear p. 
      assert (
          p : forall (x : Finite_Types s * (Finite_Types a1 * Finite_Types a2))
                     (q : (canon s, (canon a1, canon a2)) = x),
            ap (fun x : Finite_Types s * (Finite_Types a1 * Finite_Types a2) =>
                  BDet (a2 + s + (a1 + s))
                       (sum_finite_types (sum_finite_types (fst x) (fst (snd x)))
                                         (sum_finite_types (fst x) (snd (snd x))))) q
            =
            ap (BDet (a2 + s + (a1 + s)))
               (ap011
                  sum_finite_types
                  (ap011 sum_finite_types (ap fst q) (ap fst (ap snd q)))
                  (ap011 sum_finite_types (ap fst q) (ap snd (ap snd q))))).
      { intros x []. reflexivity. }
      rewrite (p _ ω). clear p.
      revert ω.
      apply (equiv_functor_forall_pb
               (equiv_path_triple_prod (canon s, (canon a1, canon a2)) 
                                       (canon s, (canon a1, canon a2)))).
      intros [p [q r]].
      simpl in p. simpl in q. simpl in r.
      change
        (equiv_path_triple_prod ?a ?b ?c) with
      (path_triple_prod a b c).  unfold path_triple_prod.
      rewrite ap_fst_path_prod. rewrite ap_snd_path_prod. rewrite ap_snd_path_prod.
      rewrite ap_fst_path_prod.
      apply moveL_pV. unfold BDet_SASB_canon.
      rewrite inv_pp. 
      repeat rewrite <- concat_p_pp.        
      apply moveR_Vp. apply moveR_Mp. apply moveR_Mp.

      refine (_ @ (ap (pft (canon 2) (canon 2))
                      (det_sasb _ _ _ (pft_inv p) (pft_inv q) (pft_inv r))) @ _).
      -refine (_ @ deloop_fin_loop _ _
                 (dethom (a2 + s + (a1 + s)))
                 (pft (canon _) (canon _)
                      (block_sum (block_sum (pft_inv p) (pft_inv q))
                                              (block_sum (pft_inv p) (pft_inv r)))) @ _).
       { destruct (deloop_fin_canon (a2 + s + (a1 + s)) 2 (dethom (a2 + s + (a1 + s)))).
         rewrite concat_p1. rewrite concat_p1. rewrite concat_1p. rewrite concat_1p.
         rewrite <- ap_pp. rewrite <- ap_V. rewrite <- ap_pp.
         apply (ap (ap (BDet (a2 + s + (a1 + s))))).
         unfold block_sum. unfold pft. apply inverse.
         refine (path_finite_types_fix_compose
                   _ _
                   (sum_finite_types (canon _) (canon _)) _ _ _ @ _).
         rewrite inv_pp.
         refine (_ @ concat_p_pp _ _ _).
         apply concat2.
         { refine (path_finite_types_fix_inv _ _ _). }
         refine (path_finite_types_fix_compose
                   _ _
                   (sum_finite_types (canon _) (canon _)) _ _ _ @ _).
         refine (_ @ concat_pp_p _ _ _). refine (_ @ concat_pp_p _ _ _).
         apply whiskerR.
         refine (path_finite_types_sum (canon (a1 + s)) (canon (a2 + s))
                                       (canon (a1 + s)) (canon (a2 + s))
                                       _ _ @ _).
         refine (_ @ (whiskerR (whiskerR (ap011_VV sum_finite_types _ _) _) _)^).
         refine (_ @ whiskerR (ap011_pp_pp sum_finite_types _ _ _ _) _).
         refine (_ @ ap011_pp_pp sum_finite_types _ _ _ _).
         apply (ap011 (ap011 sum_finite_types)).
         - refine (path_finite_types_fix_compose
                     _
                     _
                     (sum_finite_types (canon _) (canon _))
                     _ _ _ @ _).
           refine (_ @ concat_p_pp _ _ _).
           apply concat2.
           { apply path_finite_types_fix_inv. }
           
           refine (path_finite_types_fix_compose
                     _
                     _
                     (sum_finite_types (canon _) (canon _))
                     _ _ _ @ _).
           apply whiskerR.
           refine (_ @
                     ap011 (ap011 sum_finite_types)
                     (eisretr (equiv_path_finite_types_fix _ _ _) p)
                     (eisretr (equiv_path_finite_types_fix _ _ _) q)). simpl.
           refine (path_finite_types_sum (canon _) (canon _) (canon _) (canon _) _ _ ).
         - refine (path_finite_types_fix_compose
                     _
                     _
                     (sum_finite_types (canon _) (canon _))
                     _ _ _ @ _).
           refine (_ @ concat_p_pp _ _ _).
           apply concat2.
           { apply path_finite_types_fix_inv. }
           
           refine (path_finite_types_fix_compose
                     _
                     _
                     (sum_finite_types (canon _) (canon _))
                     _ _ _ @ _).
           apply whiskerR.
           refine (_ @
                     ap011 (ap011 sum_finite_types)
                     (eisretr (equiv_path_finite_types_fix _ _ _) p)
                     (eisretr (equiv_path_finite_types_fix _ _ _) r)). simpl.
           refine (path_finite_types_sum (canon _) (canon _) (canon _) (canon _) _ _ ). }
       simpl.
       unfold pft.
       apply (ap (path_finite_types_fix 2 (canon 2) (canon 2))).
       apply (ap (determinant _)).
       refine (eissect (equiv_path_finite_types_fix _ (canon _) (canon _)) _).
      - apply inverse.
        refine (_ @ deloop_fin_loop _ _
                  (dethom (a2 + a1)) (pft (canon _) (canon _) (block_sum (pft_inv q) (pft_inv r)))
                  @ _).
        { destruct (deloop_fin_canon (a2 + a1) 2 (dethom (a2 + a1))).
          rewrite concat_p1. rewrite concat_p1. rewrite concat_1p. rewrite concat_1p.
          rewrite <- ap_pp. rewrite <- ap_V. rewrite <- ap_pp.
          apply (ap (ap (BDet (a2 + a1)))).
          unfold block_sum. unfold pft.
          apply inverse.
          refine (path_finite_types_fix_compose _ (canon (a2 + a1))
                                                 (sum_finite_types (canon a1) (canon a2)) _ _ _ @ _).
          apply concat2. 
          { refine (path_finite_types_fix_inv _ _ _). }
          refine (path_finite_types_fix_compose _
                                                (sum_finite_types (canon a1) (canon a2))
                                                (sum_finite_types (canon a1) (canon a2))
                                                (canon (a2 + a1)) _ _ @ _).
          apply whiskerR.
          revert q r. 
          cut (forall (A1 : Finite_Types a1) (A2 : Finite_Types a2)
                      (q : canon a1 = A1) (r : canon a2 = A2),
                  path_finite_types_fix
                    (a2 + a1) (sum_finite_types (canon a1) (canon a2))
                    (sum_finite_types A1 A2) (pft_inv q +E pft_inv r)
                  = ap011 sum_finite_types q r).
          { intro H. apply H. }
          intros A1 A2 q r. simpl. destruct q. destruct r.
          simpl.
          refine (_ @ path_finite_types_fix_id _ _).
          apply (ap (path_finite_types_fix (a2 + a1) (sum_finite_types (canon a1) (canon a2))
                                           (sum_finite_types (canon a1) (canon a2)))).
          apply path_equiv. apply path_arrow. intros [x1 | x2]; reflexivity. }
        unfold functor_hom. unfold pft. simpl.
        apply (ap (path_finite_types_fix 2 (canon 2) (canon 2))).
        apply (ap (determinant (a2 + a1))).
        refine (eissect
                  (equiv_path_finite_types_fix (a2 + a1) (canon (a2 + a1)) (canon (a2 + a1)))
                  (block_sum (pft_inv q) (pft_inv r))
              ).
  Defined.
    
  Definition BDet_SASB_canon_id (s a1 a2 : nat)
    : BDet_SASB s a1 a2 (canon s) (canon a1) (canon a2) = BDet_SASB_canon s a1 a2.
  Proof.
    refine
      (deloop_ind_beta_pt
         (conn_ptype_prod (pFin s) (conn_ptype_prod (pFin a1) (pFin a2))) _
         (BDet_SASB_canon s a1 a2)
         _ _
      ).
  Qed.
  
  Definition grpcompl_to_fin2 : Z -> Finite_Types 2.
  Proof.
    srapply @grp_compl_BSigma_rec.
    - simpl.
      intros [a1 A1] [a2 A2].
      exact (BDet (a2 + a1) (sum_finite_types A1 A2)).
    - simpl. intros [s S] [a1 A1] [a2 A2].
      apply BDet_SASB.
    - intros [s S] [t T] [a1 A1] [a2 A2].
      revert A1.
      apply (deloop_ind_prop (pFin a1)).
      revert A2.
      apply (deloop_ind_prop (pFin a2)).
      revert T.
      apply (deloop_ind_prop (pFin t)).
      revert S.
      apply (deloop_ind_prop (pFin s)).
      hnf.
      change (point (pFin ?n)) with (canon n).
      assert (H : forall (x m n : nat)
                       (S S': Finite_Types x) (A : Finite_Types m) (B : Finite_Types n)
                       (p : S = S'),
                 BDet_SASB _ _ _ S A B =
                 BDet_SASB _ _ _ S' A B
                           @ (ap (BDet _)
                                 (ap (fun x => sum_finite_types (sum_finite_types x A)
                                                                (sum_finite_types x B)) p^))).
      { intros. destruct p. refine (concat_p1 _)^. }
      rewrite (H _ _ _ _ _ _ _ (fin_resp_sum_id t s)). clear H.
      assert (H :
                forall (x m n : nat)
                       (S S': Finite_Types x) (A A' : Finite_Types m) (B B' : Finite_Types n)
                       (p : S = S') (q : A = A') (r : B = B'),
                  BDet_SASB _ _ _ S A B =
                  (ap (BDet _) (ap011 sum_finite_types q r))
                    @ BDet_SASB _ _ _ S' A' B' @
                    (ap (BDet _) (ap011 sum_finite_types
                                        (ap011 sum_finite_types p^ q^)
                                        (ap011 sum_finite_types p^ r^)))).
      { intros. destruct p. destruct q. destruct r.
        refine (_ @ (concat_p1 _)^).
        refine (concat_1p _)^. }
      rewrite (H _ _ _ _ _ _ _ _ _
                 idpath (fin_resp_sum_id s a1) (fin_resp_sum_id s a2)).
      clear H.
      rewrite BDet_SASB_canon_id.
      rewrite BDet_SASB_canon_id.
      rewrite BDet_SASB_canon_id.
      simpl.
      

      
      assert (H
              : ap011
                  (fun X X0 : BSigma => BDet (pr1 X0 + pr1 X) (sum_finite_types (pr2 X) (pr2 X0)))
                  (BSigma_assoc (t; canon t) (s; canon s) (a1; canon a1))
                  (BSigma_assoc (t; canon t) (s; canon s) (a2; canon a2))
                =
                ap (BDet _) (ap011
                               sum_finite_types
                               (ap (fun x : BSigma => pr2 x) (BSigma_assoc (t; canon t) (s; canon s) (a1; canon a1)))
                               (ap pr2 (BSigma_assoc (t; canon t) (s; canon s) (a2; canon a2))))).
      
      unfold BDet_SASB_canon. simpl. 
      simpl. rewrite concat_1p.
      
      
      
                   

      point. unfold ispointed_type. 
      
simpl.
      
              
        
        (* lag lemma *)
        assert(
        ((sum_finite_types_canon^ @ ap011 sum_finite_types q r) @ sum_finite_types_canon)
        = pft (canon (a2 + a1)) (canon (a2 + a1)) (block_sum (pft_inv q) (pft_inv r))).
        { clear p.
          unfold block_sum. unfold pft.
          refine
            (_ @
               (path_finite_types_fix_compose (a2 + a1) (canon (a2 + a1)) (canon (a2 + a1))
                                               _ _)^).
          
          revert q r. unfold block_sum.
          cut (forall (A1 : Finite_Types a1) (A2 : Finite_Types a2)
                      (q : canon a1 = A1) (r : canon a2 = A2),
                  (sum_finite_types_canon^ @ ap011 sum_finite_types q r) @ sum_finite_types_canon =
  pft (canon (a2 + a1)) (canon (a2 + a1))
    (fin_resp_sum a1 a2 oE (pft_inv q +E pft_inv r) oE (fin_resp_sum a1 a2)^-1)).
                  
                  
          

        (* generelt: ap  *)
        
          repeat apply whiskerR.
          generalize (ap (BDet (a2 + a1)) sum_finite_types_canon). intros. reflexivity.
          reflexivity.
        refine (_ @ deloop_fin_loop (a2+a1) 2 (dethom (a2 + a1))
                  (sum_finite_types_canon^
                   @ ap011 sum_finite_types q r
                     @ sum_finite_types_canon) @ _).
        refine (_ @ deloop_fin_loop m 2 
        

            
          
                                   
                 
        
        
        
        cut
          (((deloop_fin_canon (a2 + s + (a1 + s)) 2 (dethom (a2 + s + (a1 + s))))^
            @ (ap (BDet (a2 + s + (a1 + s)))
                  (ap011 sum_finite_types sum_finite_types_canon sum_finite_types_canon
                         @ sum_finite_types_canon))^)
             @ 
                                                                                  
        rewrite <- ap_V. rewrite <- ap_V. rewrite inv_pp. apply moveR_Vp.
        repeat rewrite concat_p_pp.
        rewrite <- ap_pp. rewrite <- ap_pp. 
        
        
        
        repeat rewrite <- concat_p_pp.
        rewrite <- ap_pp.
        
        rewrite <- ap_pp.
        
                 
        assert (ω = path_prod
        assert (forall (A B C D : Type) (a1 a2 : A * (B * C)) (f : A * (B * C) -> D)
                       (p : a1 = a2),
                   ap f p = 
                       
        unfold point. simpl. 
          
          unfold BDet.
          refine (ap (BDet _) (sum_finite_types_canon) @ _).
        
          refine (_ @ deloop_fin_canon (a2 + a1) 2 

      equiv_prod_ind
      (* make triple set induction in deloop.v *)
      (* and also double set induction *)
      simpl in B.







      
      

  
  
  
  
    



Definition Tr1