Require Import HoTT.

Require Import finite_lemmas path_lemmas pointed_lemmas delooping
               permutations BSigma group_complete_1type.
Require Import Category.Core.
Add Rec LoadPath "~/Coq-projects/groupoids" as GR.
From GR Require Import cquot cquot_principles.

Definition Z := cquot (group_completion_BSigma).


Definition ccleq_concat_Z (S A1 B1 : BSigma) (A2 A3 : BSigma * BSigma)
           (p : (sum_BSigma S A1, sum_BSigma S B1) = A2)
           (q : A2 = A3)
  : ccleq group_completion_BSigma (a₁ := (A1, B1)) (S; p @ q) =
    ccleq group_completion_BSigma (a₁ := (A1, B1)) (S; p) @ ap (ccl group_completion_BSigma) q.
Proof.
  destruct q. rewrite concat_p1. rewrite concat_p1. reflexivity.
Qed.
    

Definition BSigma_to_Z : BSigma -> BSigma -> Z.
Proof.
  intros A B.  apply ccl.
  exact (A, B).
Defined.

Definition Fin_to_Z {a b : nat}
  : Finite_Types a -> Finite_Types b -> Z.
  intros A B. apply BSigma_to_Z.
  - exact (fin_to_BSigma A).
  - exact (fin_to_BSigma B).
Defined.
           


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
    
Definition canon_grpclBSigma_sum (m1 m2 n1 n2 : nat) :
  BSigma_to_Z (sum_BSigma (canon_BSigma m1) (canon_BSigma n1))
              (sum_BSigma (canon_BSigma m2) (canon_BSigma n2)) =
  BSigma_to_Z (canon_BSigma (n1 + m1)) (canon_BSigma (n2 + m2)).
Proof.
  apply (ap011 BSigma_to_Z); apply finsum_id.
Defined.
  
  (* ccl (group_completion_BSigma) *)
  (*     (functor_prod (sum_BSigma (canon_BSigma m1)) (sum_BSigma (canon_BSigma m2)) (canon_BSigma n1, canon_BSigma n2)) = *)
  (* ccl (group_completion_BSigma) *)
  (*     (canon_BSigma (n1+m1), (canon_BSigma (n2+m2))). *)
(* Proof. *)
(*   apply (ap (ccl group_completion_BSigma)). unfold sum_BSigma. simpl. *)
(*   unfold functor_prod. simpl. unfold canon_BSigma. *)
(*   exact (ap (fun x : Finite_Types (n1 + m1) * Finite_Types (n2+m2) => *)
(*                (fin_to_BSigma (fst x), (fin_to_BSigma (snd x)))) *)
(*         (path_prod (_,_) (_,_) (finsum_id m1 n1) (finsum_id m2 n2)))%nat. *)
(* Defined. *)


Definition path_Z {A1 B1 A2 B2 : BSigma} (S : BSigma)
  : (sum_BSigma S A1 = A2) -> (sum_BSigma S B1 = B2)
    -> BSigma_to_Z A1 B1 = BSigma_to_Z A2 B2.
Proof.
  intros p q.
  apply ccleq. exists S.
  apply path_prod.
  - exact p. - exact q.
Defined.

Definition path_Z_fr {A1 B1 A2 B2 : BSigma} (S : BSigma)
  : (sum_BSigma A1 S = A2) -> (sum_BSigma B1 S = B2)
    -> BSigma_to_Z A1 B1 = BSigma_to_Z A2 B2.
Proof.
  intros p q.
  apply ccleq. exists S. simpl.
  apply path_prod; simpl.
  - exact (BSigma_symmetric _ _ @ p).
  - exact (BSigma_symmetric _ _ @ q).
Defined.
    
           (* {s a b : nat} (S : Finite_Types s) (A : Finite_Types a) (B : Finite_Types b) *)
Definition lcancel_Z (S A B : BSigma)
  : BSigma_to_Z A B = BSigma_to_Z (sum_BSigma S A) (sum_BSigma S B) :=
  path_Z S idpath idpath.

Definition lcancel_Z_fr (A B S : BSigma)
  : BSigma_to_Z A B = BSigma_to_Z (sum_BSigma A S) (sum_BSigma B S) :=
  path_Z_fr S idpath idpath.
(* Proof. *)
(*   apply (path_Z S); apply BSigma_symmetric. *)
(*   (* refine (lcancel_Z S A B @ _); *) *)
(*   (* apply (ap011 BSigma_to_Z); apply BSigma_symmetric. *) *)
(* Defined. *)

Definition path_Z_pp_r {A1 B1 A2 B2 A2' B2'} (S : BSigma)
           (p1 : sum_BSigma S A1 = A2) (p2 : sum_BSigma S B1 = B2)
           (q1 : A2 = A2') (q2 : B2 = B2')
  : path_Z S (p1 @ q1) (p2 @ q2) =
    path_Z S p1 p2 @ (ap011 BSigma_to_Z q1 q2).
Proof.
  destruct q1. destruct q2. destruct p1. destruct p2. simpl.
  rewrite concat_p1. reflexivity.
Defined.

Definition path_Z_pp_l {A1 B1 A1' B1' A2 B2 S}
           (p1 : A1 = A1') (p2 : B1 = B1')
           (q1 : sum_BSigma S A1' = A2)
           (q2 : sum_BSigma S B1'= B2)
  : path_Z S (ap011 sum_BSigma idpath p1 @ q1) (ap011 sum_BSigma idpath p2 @ q2) =
    ap011 BSigma_to_Z p1 p2 @ path_Z S q1 q2.
Proof.
  destruct q1. destruct q2. destruct p1. destruct p2.
  simpl. 
  rewrite concat_1p. reflexivity.
Defined.

Definition path_Z_fr_pp_r {A1 B1 A2 B2 A2' B2'} (S : BSigma)
           (p1 : sum_BSigma A1 S = A2) (p2 : sum_BSigma B1 S = B2)
           (q1 : A2 = A2') (q2 : B2 = B2')
  : path_Z_fr S (p1 @ q1) (p2 @ q2) =
    path_Z_fr S p1 p2 @ (ap011 BSigma_to_Z q1 q2).
Proof.
  destruct q1. destruct q2. destruct p1. destruct p2. simpl.
  rewrite concat_p1. reflexivity.
Defined.

Definition path_Z_fr_pp_l {A1 B1 A1' B1' A2 B2 S}
           (p1 : A1 = A1') (p2 : B1 = B1')
           (q1 : sum_BSigma A1' S = A2)
           (q2 : sum_BSigma B1' S = B2)
  : path_Z_fr S (ap011 sum_BSigma p1 idpath @ q1) (ap011 sum_BSigma p2 idpath @ q2) =
    ap011 BSigma_to_Z p1 p2 @ path_Z_fr S q1 q2.
Proof.
  destruct p1. destruct p2.
  rewrite concat_1p. rewrite concat_1p. rewrite concat_1p.
  reflexivity.
Defined.


Definition path_Z_100 {A1 B1 A2 B2} (S S' : BSigma) (p : S' = S)
           (q1 : sum_BSigma S A1 = A2)
           (q2 : sum_BSigma S B1 = B2)
  : path_Z S q1 q2 =
    path_Z S' (ap011 sum_BSigma p idpath @ q1)
                       (ap011 sum_BSigma p idpath @ q2).
Proof.
  destruct p.
  rewrite concat_1p. rewrite concat_1p.
  reflexivity.
Defined.

Definition path_Z_fr_100 {A1 B1 A2 B2} (S S' : BSigma) (p : S' = S)
           (q1 : sum_BSigma A1 S = A2)
           (q2 : sum_BSigma B1 S = B2)
  : path_Z_fr S q1 q2 =
    path_Z_fr S' (ap011 sum_BSigma idpath p @ q1)
                       (ap011 sum_BSigma idpath p @ q2).
Proof.
  destruct p.
  rewrite concat_1p. rewrite concat_1p.
  reflexivity.
Defined.

Definition path_is_lcancel {A1 B1 A2 B2} (S : BSigma)
           (p : sum_BSigma S A1 = A2) (q : sum_BSigma S B1 = B2)
  : path_Z S p q = lcancel_Z S A1 B1 @ ap011 BSigma_to_Z p q.
Proof.
  unfold lcancel_Z.
  refine (_ @ path_Z_pp_r S idpath idpath p q).
  rewrite concat_1p. rewrite concat_1p.
  reflexivity.
Defined.

Definition path_fr_is_lcancel {A1 B1 A2 B2} (S : BSigma)
           (p : sum_BSigma A1 S = A2) (q : sum_BSigma B1 S = B2)
  : path_Z_fr S p q = lcancel_Z_fr A1 B1 S @ ap011 BSigma_to_Z p q.
Proof.
  unfold lcancel_Z_fr.
  refine (_ @ path_Z_fr_pp_r S idpath idpath p q).
  rewrite concat_1p. rewrite concat_1p.
  reflexivity.
Defined.


Definition path_Z_compose {A1 B1 A2 B2 A3 B3: BSigma} (S T: BSigma)
           (p1 : sum_BSigma S A1 = A2) (q1 : sum_BSigma S B1 = B2)
           (p2 : sum_BSigma T A2 = A3) (q2 : sum_BSigma T B2 = B3) : 
  (path_Z S p1 q1) @ (path_Z T p2 q2) = 
  @path_Z  A1 B1 A3 B3  (sum_BSigma T S)
                 (BSigma_assoc T S A1 @ ap011 sum_BSigma idpath p1 @ p2)
                 (BSigma_assoc T S B1 @ ap011 sum_BSigma idpath q1 @ q2).
Proof.
  unfold path_Z.
  apply inverse.
  refine (_ @ cconcat _ _ _). simpl.
  apply (ap (ccleq group_completion_BSigma)).
  apply (ap (fun x => (sum_BSigma T S; x))).
  rewrite ap_functor_prod.
  rewrite <- path_prod_pp. rewrite <- path_prod_pp. reflexivity.
Qed.

Definition path_Z_fr_compose {A1 B1 A2 B2 A3 B3: BSigma} (S T: BSigma)
           (p1 : sum_BSigma A1 S = A2) (q1 : sum_BSigma B1 S = B2)
           (p2 : sum_BSigma A2 T = A3) (q2 : sum_BSigma B2 T = B3) :
  (path_Z_fr S p1 q1) @ (path_Z_fr T p2 q2) = 
  @path_Z_fr  A1 B1 A3 B3  (sum_BSigma S T)
                 ((BSigma_assoc A1 S T)^ @ ap011 sum_BSigma p1 idpath @ p2)
                 ((BSigma_assoc B1 S T)^ @ ap011 sum_BSigma q1 idpath @ q2).
Proof.
  rewrite (path_Z_fr_100 _ _ (BSigma_symmetric T S)).
  unfold path_Z_fr.
  apply inverse.
  refine (_ @ cconcat _ _ _). 
  apply (ap (ccleq group_completion_BSigma)). simpl.
  apply (ap (fun x => (sum_BSigma T S; x))).
  rewrite ap_functor_prod.
  rewrite <- path_prod_pp. rewrite <- path_prod_pp.
  destruct q2. destruct p2. destruct q1. destruct p1.
  repeat rewrite concat_p1.
  rewrite <- path_BSigma_1.
  rewrite <- path_BSigma_sum.
  rewrite <- path_BSigma_1.
  rewrite <- path_BSigma_sum.
  rewrite path_BSigma_V.
  rewrite path_BSigma_V.
  rewrite natural_path_BSigma_r.
  rewrite natural_path_BSigma_r.
  repeat rewrite <- path_BSigma_compose.
  apply (ap011 (path_prod _ _)); apply (ap (path_BSigma _ _));
    apply path_equiv; apply path_arrow; intro x;
      repeat destruct x as [x | x]; reflexivity.
  Qed.

Definition lcancel_Z_compose (S T A B : BSigma)
           (* {s t a b : nat} *)
           (* (S : Finite_Types s) (T : Finite_Types t) (A : Finite_Types a) (B : Finite_Types b) *)
  : lcancel_Z (sum_BSigma T S) A B  =
    lcancel_Z S A B @ lcancel_Z T (sum_BSigma S A) (sum_BSigma S B)
              @ (ap011 BSigma_to_Z (BSigma_assoc T S A) (BSigma_assoc T S B))^.
Proof.
  unfold lcancel_Z. apply moveL_pV.
  refine (_ @ (path_Z_compose S T _ _ _ _)^). simpl.
  repeat rewrite concat_p1. destruct (BSigma_assoc T S A). destruct (BSigma_assoc T S B).
  apply concat_p1.
Defined.

Definition lcancel_Z_fr_compose (A B S T: BSigma) 
  : lcancel_Z_fr A B (sum_BSigma T S) =
    lcancel_Z_fr A B T @ (lcancel_Z_fr _ _ S) @
                 (ap011 BSigma_to_Z (BSigma_assoc A T S) (BSigma_assoc B T S)).
Proof.
  unfold lcancel_Z_fr.
  apply moveL_pM.
  refine (_ @ (path_Z_fr_compose T S _ _ _ _)^).
  repeat rewrite concat_p1.
  rewrite ap011_VV.
  destruct (BSigma_assoc A T S)^.
  destruct (BSigma_assoc B T S)^.
  apply concat_p1.
Defined.               
  

Definition lcancel_canon (s m n : nat) :
  BSigma_to_Z (canon_BSigma m) (canon_BSigma n) =
  BSigma_to_Z (canon_BSigma (m + s)) (canon_BSigma (n + s)).
Proof.
  refine (lcancel_Z (canon_BSigma s) _ _ @ _).
  apply (ap011 BSigma_to_Z); apply finsum_id.
  (* apply (path_Z (canon_BSigma s)); *)
  (*   apply finsum_id. *)
Defined.

Definition lcancel_canon_fr (s m n : nat)
  : BSigma_to_Z (canon_BSigma m) (canon_BSigma n) =
    BSigma_to_Z (canon_BSigma (m +' s)) (canon_BSigma (n +' s)).
Proof.
  apply (path_Z_fr (canon_BSigma s)); apply finsum_id.
  (* refine (lcancel_Z_fr _ _ (canon_BSigma s) @ _). *)
  (* apply (ap011 BSigma_to_Z); apply finsum_id. *)
Defined.

Definition lcancel_canon_path_fr (s a b : nat)
           (sigma : Fin s <~> Fin s)
           (alpha : Fin a <~> Fin a) (betta : Fin b <~> Fin b)
  : ap011 BSigma_to_Z
          (path_BSigma (canon_BSigma (a +' s)) (canon_BSigma (a +' s)) (block_sum alpha sigma))
          (path_BSigma (canon_BSigma (b +' s)) (canon_BSigma (b +' s)) (block_sum betta sigma)) =
    (lcancel_canon_fr s a b)^ @
          ap011 BSigma_to_Z (path_BSigma (canon_BSigma a) (canon_BSigma a) alpha)
                            (path_BSigma (canon_BSigma b) (canon_BSigma b) betta)
      @ lcancel_canon_fr s a b.
Proof.
  rewrite path_BSigma_blocksum.
  rewrite path_BSigma_blocksum.
  repeat refine (_ @ concat_p_pp _ _ _).
  apply moveL_Vp.
  unfold lcancel_canon_fr.
  unfold lcancel_Z_fr.
  rewrite <- path_Z_fr_pp_r.
  (* rewrite <- path_Z_fr_pp_r. *)
  repeat rewrite concat_1p.
  rewrite concat_p_Vp. rewrite concat_p_Vp.
  destruct (finsum_id a s). destruct (finsum_id b s).
  rewrite concat_p1. rewrite concat_p1.
  destruct (path_BSigma (canon_BSigma a) (canon_BSigma a) alpha).
  destruct (path_BSigma (canon_BSigma b) (canon_BSigma b) betta).
  destruct (path_BSigma (canon_BSigma s) (canon_BSigma s) sigma). 
  rewrite concat_1p. reflexivity.
Defined.  

Definition lcancel_canon_path (s a b : nat)
           (sigma : Fin s <~> Fin s)
           (alpha : Fin a <~> Fin a) (betta : Fin b <~> Fin b) 
: ap011 BSigma_to_Z
          (path_BSigma (canon_BSigma (a + s)) (canon_BSigma (a + s)) (block_sum sigma alpha))
          (path_BSigma (canon_BSigma (b + s)) (canon_BSigma (b + s)) (block_sum sigma betta)) =
    (lcancel_canon s a b)^ @
          ap011 BSigma_to_Z (path_BSigma (canon_BSigma a) (canon_BSigma a) alpha)
                            (path_BSigma (canon_BSigma b) (canon_BSigma b) betta)
      @ lcancel_canon s a b.
Proof.
  rewrite path_BSigma_blocksum.
  rewrite path_BSigma_blocksum.
  repeat refine (_ @ concat_p_pp _ _ _).
  apply moveL_Vp.
  unfold lcancel_canon.
  unfold lcancel_Z.
  rewrite <- path_Z_pp_r.
  rewrite <- path_Z_pp_r.
  repeat rewrite concat_1p.
  rewrite concat_p_Vp. rewrite concat_p_Vp.
  destruct (finsum_id s a). destruct (finsum_id s b).
  rewrite concat_p1. rewrite concat_p1.
  destruct (path_BSigma (canon_BSigma a) (canon_BSigma a) alpha).
  destruct (path_BSigma (canon_BSigma b) (canon_BSigma b) betta).
  destruct (path_BSigma (canon_BSigma s) (canon_BSigma s) sigma). 
  rewrite concat_1p. reflexivity.
Defined.            
          
          



(* Definition plus_assoc_Z (a1 b1 c1 a2 b2 c2 : nat) *)
(*   : BSigma_to_Z (canon_BSigma ((a1 + b1) + c1)) (canon_BSigma ((a2 + b2) + c2)) = *)
(*     BSigma_to_Z (canon_BSigma (a1 + (b1 + c1))) (canon_BSigma (a2 + (b2 + c2))). *)
(* Proof. *)
(*   apply (ap011 BSigma_to_Z); *)
(*     apply (ap canon_BSigma); apply nat_lemmas.plus_assoc. *)
(* Defined. *)

Definition lcancel_canon_fr_compose (a b s t : nat)
  : lcancel_canon_fr (s +' t) a b =
    lcancel_canon_fr s a b @ lcancel_canon_fr t (a +' s) (b +' s) @
                     (ap011 BSigma_to_Z (canon_BSigma_assoc _ _ _) (canon_BSigma_assoc _ _ _)).
Proof.
  unfold lcancel_canon_fr. unfold lcancel_Z_fr.
  (* rewrite <- path_Z_fr_pp_r. *) (* rewrite <- path_Z_fr_pp_r. rewrite <- path_Z_fr_pp_r. *)
  repeat rewrite concat_1p.
  rewrite path_Z_fr_compose. rewrite <- path_Z_fr_pp_r.
  rewrite (path_Z_fr_100 _ _ (finsum_id s t)). 
  
  rewrite <- path_BSigma_1. rewrite <- path_BSigma_sum.
  rewrite <- path_BSigma_1. rewrite <- path_BSigma_sum.
  rewrite path_BSigma_V. rewrite path_BSigma_V.
  rewrite <- path_BSigma_compose. rewrite <- path_BSigma_compose.
  rewrite <- path_BSigma_1. rewrite <- path_BSigma_sum.
  rewrite <- path_BSigma_compose. rewrite <- path_BSigma_compose.
  rewrite <- path_BSigma_compose.
  rewrite <- path_BSigma_sum.
  rewrite <- path_BSigma_compose.
  rewrite <- path_BSigma_compose. rewrite <- path_BSigma_compose.

  assert (finsum_inv_l : forall (m n : nat),
             finsum_inv m n o (finl m n) == inl).
  { intros m n. intro x.
    exact (eissect (equiv_finsum m n) (inl x)). }
  assert (finsum_inv_r : forall (m n : nat),
             finsum_inv m n o (finr m n) == inr).
  { intros m n. intro x.
    exact (eissect (equiv_finsum m n) (inr x)). }
  
  apply (ap011 (path_Z_fr _)); (apply (ap (path_BSigma _ _)));
    apply path_equiv; apply path_arrow; intro x; 
      repeat destruct x as [x | x]; simpl.
  - rewrite finsum_inv_l. change (functor_sum (B' := ?B) ?f ?g (inl ?y)) with (inl B (f y)).
    rewrite finsum_inv_l. reflexivity.
  - rewrite finsum_inv_l. change (functor_sum (B' := ?B) ?f ?g (inl ?y)) with (inl B (f y)).
    rewrite finsum_inv_r. reflexivity.
  - rewrite finsum_inv_r. reflexivity.
  - rewrite finsum_inv_l. change (functor_sum (B' := ?B) ?f ?g (inl ?y)) with (inl B (f y)).
    rewrite finsum_inv_l. reflexivity.
  - rewrite finsum_inv_l. change (functor_sum (B' := ?B) ?f ?g (inl ?y)) with (inl B (f y)).
    rewrite finsum_inv_r. reflexivity.
  - rewrite finsum_inv_r. reflexivity.
Defined.

Definition lcancel_canon_compose (m n s t : nat)
  : lcancel_canon (s + t) m n  =
    lcancel_canon s m n @ lcancel_canon t (m + s) (n + s)
                  @ (ap011 BSigma_to_Z (canon_BSigma_assoc _ _ _) (canon_BSigma_assoc _ _ _))^.
Proof.
  unfold lcancel_canon.
  assert (H : lcancel_Z  (canon_BSigma (s + t)) (canon_BSigma m) (canon_BSigma n)  =
              lcancel_Z  (sum_BSigma (canon_BSigma t) (canon_BSigma s))
                         (canon_BSigma m) (canon_BSigma n)
              @ (ap011 BSigma_to_Z
                      (ap011 sum_BSigma (finsum_id _ _) idpath)
                      (ap011 sum_BSigma (finsum_id _ _) idpath))).
  { destruct (finsum_id t s). apply inverse. apply concat_p1. }
  rewrite H. clear H.
  rewrite lcancel_Z_compose.
  repeat refine (_ @ concat_p_pp _ _ _).
  repeat refine (concat_pp_p _ _ _ @ _). apply whiskerL.
  (* refine (concat_p_pp _ _ _ @ _). *)
  refine (_ @ (whiskerL _ (concat_p_pp _ _ _ ))).
  refine (_ @ concat_pp_p _ _ _).
  assert (H :lcancel_Z (canon_BSigma t)
                    (sum_BSigma (canon_BSigma s) (canon_BSigma m))
                    (sum_BSigma (canon_BSigma s) (canon_BSigma n))
          = (ap011 BSigma_to_Z (finsum_id s m) (finsum_id s n) @
                   lcancel_Z (canon_BSigma t) (canon_BSigma (m + s)) (canon_BSigma (n + s)))
              @ (ap011 BSigma_to_Z
                       (ap011 sum_BSigma idpath (finsum_id s m))
                       (ap011 sum_BSigma idpath (finsum_id s n)))^).
  { destruct (finsum_id s m). destruct (finsum_id s n).
    rewrite concat_1p. rewrite concat_p1. reflexivity. }
  rewrite H. clear H.
  refine (concat_pp_p _ _ _ @ _). apply whiskerL.
  apply moveR_Vp. apply moveR_Vp.
  refine (_ @ concat_pp_p _ _ _).
  refine (_ @ concat_pp_p _ _ _).
  apply moveL_pV.
  apply moveR_Mp.
  rewrite <- ap011_pp_pp. rewrite <- ap011_pp_pp. rewrite <- ap011_pp_pp.
  rewrite ap011_VV. rewrite <- ap011_pp_pp.
  assert (H : forall (A B C : BSigma) (e : A <~> B),
             ap011 sum_BSigma (path_BSigma A B e) (idpath C)
             = path_BSigma (sum_BSigma A C) (sum_BSigma B C)
                           (equiv_functor_sum_r e)).
  { intros. refine (_ @ natural_path_BSigma_l e).
    destruct (path_BSigma A B e). reflexivity. }
  rewrite H. rewrite H. clear H.
  assert (H : forall (A B C : BSigma) (e : B <~> C),
             ap011 sum_BSigma (idpath A) (path_BSigma B C e)
             = path_BSigma (sum_BSigma A B) (sum_BSigma A C)
                           (equiv_functor_sum_l e)).
  { intros. refine (_ @ natural_path_BSigma_r e).
    destruct (path_BSigma B C e). reflexivity. }
  rewrite H. rewrite H. clear H.
  rewrite <- path_BSigma_compose. rewrite <- path_BSigma_compose.
  rewrite <- path_BSigma_compose. rewrite <- path_BSigma_compose.
  rewrite <- path_BSigma_compose. rewrite <- path_BSigma_compose.
  rewrite path_BSigma_V. rewrite path_BSigma_V.
  rewrite <- path_BSigma_compose. rewrite <- path_BSigma_compose.
  (* now they are basically the same *)
  apply (ap011 (ap011 BSigma_to_Z));
    apply (ap (path_BSigma _ _)); unfold canon_assoc;
    rewrite einv_ee; repeat rewrite ecompose_e_ee;
    reflexivity.
Defined.

(* removable? *)
Definition uncurry_forall {A B : Type} (P : A -> B -> Type) :
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
                             f A1 A2 = f (sum_BSigma S A1) (sum_BSigma S A2))
           (act_add_compose : forall (S T A1 A2 : BSigma),
               act_add (sum_BSigma T S) A1 A2
                       @ (ap011 f (BSigma_assoc T S A1) (BSigma_assoc T S A2))
               = act_add S A1 A2 @ act_add T (sum_BSigma S A1) (sum_BSigma S A2))
  : Z -> P.
Proof.
  (* set (uncurry_f := *)
  (*        fun x : BSigma * BSigma => *)
  (*          match x with *)
  (*            (A1, A2) => f A1 A2 end). *)
  srapply @cquot_rec'.
  - simpl. intros [A1 A2]. exact (f A1 A2).
  - simpl. intros [A1 A2]. intro B.
    unfold monoidal_action_morphism.
    intros [S p]. simpl in p.
    refine (act_add S _ _ @ _).
    apply (ap (uncurry f) p).
  - intros [A1 A2]. intros B C.
    intros [S p]. intros [T q]. 
    destruct q. destruct p. simpl. repeat rewrite concat_p1.
    refine (_ @ act_add_compose _ _ _ _).
    apply whiskerL.
    generalize (BSigma_assoc T S A2) as q. 
    generalize (BSigma_assoc T S A1) as p.
    cut (forall (B1 B2 : BSigma)
                (p : sum_BSigma (sum_BSigma T S) A1 = B1)
                (q : sum_BSigma (sum_BSigma T S) A2 = B2),
            ap (uncurry f)
               (path_prod
                  (functor_prod
                     (sum_BSigma (sum_BSigma T S)) (sum_BSigma (sum_BSigma T S)) (A1, A2))
                  (B1, B2) p q)
            = ap011 f p q).
    { intro H. apply H. }
    intros B1 B2. intros [] []. reflexivity.
Defined.

Definition grp_compl_BSigma_rec_beta_lcancel_Z (P : 1 -Type) (f : BSigma -> BSigma -> P)
           (act_add : forall S A1 A2 : BSigma, f A1 A2 = f (sum_BSigma S A1) (sum_BSigma S A2))
           (act_add_compose : forall (S T A1 A2 : BSigma),
               act_add (sum_BSigma T S) A1 A2
                       @ (ap011 f (BSigma_assoc T S A1) (BSigma_assoc T S A2))
               = act_add S A1 A2 @ act_add T (sum_BSigma S A1) (sum_BSigma S A2))
           (S A B : BSigma)
  : ap (grp_compl_BSigma_rec P f act_add act_add_compose) (lcancel_Z S A B) =
    act_add S A B.
Proof.
  unfold lcancel_Z. unfold path_Z.
  refine (cquot_rec_beta_ccleq group_completion_BSigma P _ _ _ _ _ _ _ _ @ _).
  simpl. apply concat_p1.
Defined.


(* Auxillary stuff for the next result *)
Local Definition grp_compl_BSigma_ind_set_Fin {a b : nat}
      (P : Z -> Type) {isset_P : forall z : Z, IsHSet (P z)}
      (f : forall (m n : nat),
          P (Fin_to_Z (canon m) (canon n)))
          (* P (ccl (group_completion_BSigma) ((canon_BSigma m), (canon_BSigma n)))} *)
      (base_change
              : forall (a b : nat) (alpha : canon a = canon a) (betta : canon b = canon b),
          double_pathover (fun (x : Finite_Types a) (y : Finite_Types b) =>  P (Fin_to_Z x y))
                          alpha betta (f a b) (f a b))
  : forall (x : Finite_Types a) (y : Finite_Types b),
    P (Fin_to_Z x y).
      (* (ccl group_completion_BSigma (fin_to_BSigma x, fin_to_BSigma y)). *)
Proof.
  apply (deloop_double_ind_set'
             (pFin a) (pFin b)
             (fun x y => BuildTruncType 0 (P (Fin_to_Z x y))) (f a b)).
    intros alpha betta.
    apply (double_pathover_to_path
             (fun (x : pFin a) (y : pFin b) =>
                P (Fin_to_Z x y))
             alpha betta (f a b) (f a b)).
    apply base_change.
Defined.

(* Set induction for the group completion of BSigma *)
(* Could relatively easily be generalized to 1-type induction *)
Definition grp_compl_BSigma_ind_set
           (P : Z -> Type) {isset_P : forall z : Z, IsHSet (P z)}
           (f : forall (m n : nat),
               P (Fin_to_Z (canon m) (canon n)))
           (base_change
              : forall (a b : nat) (alpha : canon a = canon a) (betta : canon b = canon b),
               double_pathover (fun (x : Finite_Types a) (y : Finite_Types b) => P (Fin_to_Z x y))

                               alpha betta (f a b) (f a b))
               (* transport *)
               (*   (fun p : Finite_Types a * Finite_Types b => *)
               (*      uncurry *)
               (*        (fun (x : Finite_Types a) (y : Finite_Types b) => *)
               (*           P (ccl group_completion_BSigma (fin_to_BSigma x, fin_to_BSigma y))) p) *)
               (*   (path_prod (canon a, canon b) (canon a, canon b) alpha betta) *)
               (*   (f a b) = f a b) *)
           (act_add :
              (forall (m n : nat) (s : nat),
                path_over P (lcancel_canon s m n) (f m n) (f (m+s)%nat (n+s)%nat)))
           : forall z : Z, P z.
Proof.
  srapply @cquot_ind_set.
  - simpl.
    intros [[a x] [b y]]. 
    change (ccl group_completion_BSigma
                ({| card_BSigma := a; fintype_of_BSigma := x |},
                 {| card_BSigma := b; fintype_of_BSigma := y |}))
    with (Fin_to_Z x y).
    revert x y.
    (* change {| card_BSigma := ?a; fintype_of_BSigma := ?A |} with (fin_to_BSigma A). *)
    apply (@grp_compl_BSigma_ind_set_Fin a b P _ f base_change).
  - simpl. unfold monoidal_action_morphism.
    intros [[a A] [b B]] C [S p].  destruct p. simpl.
    revert B.
    srefine (deloop_ind_prop
               (pFin b) 
               _ _).
    revert A.
    srefine (deloop_ind_prop
               (pFin a)
               _ _).
    destruct S as [s S]. revert S.
      srefine (deloop_ind_prop
               (pFin s)
               _ _).
      simpl.
      change (@ccleq group_completion_BSigma (?A, ?B) _
                    ({| card_BSigma := s; fintype_of_BSigma := point (Finite_Types s) |}; idpath))
             with
             (lcancel_Z (canon_BSigma s) A B).
      change {| card_BSigma := ?x; fintype_of_BSigma := point (Finite_Types ?x) |}
             with (canon_BSigma x).
      
      assert (H : (lcancel_Z (canon_BSigma s) (canon_BSigma a) (canon_BSigma b)) =
              (lcancel_canon s a b) @ (canon_grpclBSigma_sum s s a b)^).
      { unfold lcancel_canon. unfold canon_grpclBSigma_sum.
        destruct (ap011 BSigma_to_Z (finsum_id s a) (finsum_id s b)).
        rewrite concat_p1.  rewrite concat_p1. reflexivity.

        (* unfold path_Z. *)
        (* unfold canon_grpclBSigma_sum. (* unfold lcancel_Z. *) *)
        (* destruct (finsum_id s a). destruct (finsum_id s b). *)
        (* simpl. rewrite concat_p1. *)
        (* rewrite (path_is_lcancel  *)
        (* reflexivity. *) }
        (* destruct (canon_grpclBSigma_sum s s a b). repeat rewrite concat_p1. reflexivity. } *)
      rewrite H. clear H.
      
      srapply @path_over_concat; simpl.
      + apply (grp_compl_BSigma_ind_set_Fin P f base_change).
        (* apply f. *)
      + (* apply path_to_path_over. *)
        unfold grp_compl_BSigma_ind_set_Fin.
        rewrite (deloop_double_ind_set_beta_pt').
        rewrite (deloop_double_ind_set_beta_pt').        
        apply act_add.
      + unfold canon_grpclBSigma_sum.
        change (point (Finite_Types ?a)) with (canon a).
        unfold finsum_id.
        rewrite <- (path_BSigma_fix (sum_finite_types (canon s) (canon _)) (canon (_ + s))
                                    (equiv_finsum s _)).
        rewrite <- (path_BSigma_fix (sum_finite_types (canon s) (canon _)) (canon (_ + s))
                                    (equiv_finsum s _)).
        simpl.
        cut (forall (A : Finite_Types (a + s)) (B : Finite_Types (b + s))
                    (p : sum_finite_types (canon s) (canon a) = A)
                    (q : sum_finite_types (canon s) (canon b) = B),
                path_over
                  P (ap011 BSigma_to_Z (pft_to_pbs p) (pft_to_pbs q))^
                (grp_compl_BSigma_ind_set_Fin P f base_change A B)
                  (grp_compl_BSigma_ind_set_Fin P f base_change (sum_finite_types (canon s) (canon a))
                                                (sum_finite_types (canon s) (canon b)))).
        { intro H. apply H. }
        intros A B [] []. apply path_over_id.
        (* apply path_over_inv. *)
        (* change (grp_compl_BSigma_ind_set_Fin (base_change := base_change) ?x ?y) with *)
        (* (uncurry_forall _ (grp_compl_BSigma_ind_set_Fin (base_change := base_change)) (x,y)). *)
        (* apply *)
        (*   (apd_po *)
        (*      (uncurry_forall (fun (x : Finite_Types (a + s)) (y : Finite_Types (b + s)) => *)
        (*                         P (ccl group_completion_BSigma (fin_to_BSigma x, fin_to_BSigma y))) *)
        (*                      (grp_compl_BSigma_ind_set_Fin (base_change := base_change))) *)
        (*      (a₁ := (sum_finite_types (canon s) (canon a), sum_finite_types (canon s) (canon b))) *)
        (*      (a₂ := (canon (a + s), canon (b + s)))). *)
        
        (* generalize to some version of apd: *)
        (* cut (forall (A A' : Finite_Types (a + s)) (B B' : Finite_Types (b + s)) *)
        (*             (p : A = A') (q : B = B'), *)
        (*         path_over *)
        (*           P *)
        (*           (ap (ccl group_completion_BSigma) *)
        (*               (ap *)
        (*                  (fun x : Finite_Types (a + s) * Finite_Types (b + s) => *)
        (*                     (fin_to_BSigma (fst x), fin_to_BSigma (snd x))) *)
        (*   (path_prod (A, B) (A', B') p q))) *)
        (*           (grp_compl_BSigma_ind_set_Fin (base_change := base_change) A B) *)
        (*           (grp_compl_BSigma_ind_set_Fin (base_change := base_change) A' B')). *)
        (* { intro H. apply H. } *)
        (* intros. destruct p. destruct q. simpl. apply path_over_id. *)
Defined.


Definition grp_compl_BSigma_ind_hprop
           (P : Z -> Type) {hprop_P : forall z : Z, IsHProp (P z)}
           (f : forall (m n : nat),
               P (Fin_to_Z (canon m) (canon n)))
  : forall z : Z, P z.
Proof.
  srefine (grp_compl_BSigma_ind_set P f _ _).
  - intros. apply path_to_double_pathover.
    apply hprop_P.
  - intros. apply path_to_path_over.
    apply hprop_P.
Defined.
    

(* (* change to only one act? *) *)
(* Definition grp_compl_BSigma_ind_set *)
(*            (P : Z -> hSet) *)
(*            (f : forall (m n : nat), *)
(*                P (ccl (group_completion_BSigma) ((canon_BSigma m), (canon_BSigma n)))) *)
(*            (act_r : *)
(*               forall (m n : nat) (σ : canon n = canon n), *)
(*                 transport *)
(*                   (fun x : (Finite_Types n) => *)
(*                      P (ccl (group_completion_BSigma) *)
(*                             ((canon_BSigma m), (fin_to_BSigma x)))) σ (f m n) = (f m n)) *)
(*            (act_l : *)
(*               forall (m n : nat) (σ : canon m = canon m), *)
(*                 transport *)
(*                   (fun x : (Finite_Types m) => *)
(*                      P (ccl (group_completion_BSigma) ((fin_to_BSigma x), (canon_BSigma n)))) σ (f m n) = (f m n)) *)
  
(*            (act_add : *)
(*               (forall (m n : nat) (s : nat), *)
(*                 transport P (ccleq_canon m n s) (f m n) = f (m+s)%nat (n+s)%nat)) *)
(*            : forall z : Z, P z. *)

End BSigma_set_ind.

