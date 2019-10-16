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
  - simpl. apply (equiv_path_finite_types m (canon m) (canon m)).
  - intros alpha beta. simpl.
    apply (path_finite_types_compose m (canon m) (canon m) (canon m) alpha beta).
Defined.

Definition deloop_fin (m n : nat)
  : Homomorphism (SymGrp m) (SymGrp n) -> Finite_Types m -> Finite_Types n.
Proof.
  intro f.
  srefine (deloop_rec (pFin m) (Finite_Types n) (canon n) _ _).
  - 
    apply (hom_map (M := loopGroup (Finite_Types m) (canon m))
                   (N := loopGroup (Finite_Types n) (canon n))).
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

Definition BDet_uncurry : BSigma -> Finite_Types 2.
Proof.
  intros [a A]. exact (BDet a A).
Defined.



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
  := path_finite_types m.

Local Definition pft_inv {m : nat} {A B}
  := inv_path_finite_types m A B.

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

Local Definition pbs_inv {A B : BSigma} 
  := equiv_inverse (equiv_path_BSigma A B).

Lemma path_BSigma_sum (A1 A2 B1 B2 : BSigma)
      (e1 : A1 <~> B1) (e2  : A2 <~> B2)
  : path_BSigma (sum_BSigma A1 A2) (sum_BSigma B1 B2) (e1 +E e2)
    = ap011 sum_BSigma (path_BSigma _ _ e1) (path_BSigma _ _ e2).
Proof.
  rewrite (ap011 equiv_functor_sum'
                    (eissect (equiv_path_BSigma A1 B1) e1)^ (eissect (equiv_path_BSigma A2 B2) e2)^).
  change ((equiv_path_BSigma ?A ?B) ?e) with (path_BSigma A B e).
  destruct (path_BSigma A1 B1 e1). destruct (path_BSigma A2 B2 e2).
  simpl.
  refine (_ @ path_BSigma_1 _).
  apply (ap (path_BSigma _ _)).
  apply path_equiv. apply path_arrow.
  intros [a | a]; reflexivity.
Defined.                               
  

Lemma path_finite_types_sum {a1 a2 : nat}
           (A1 : Finite_Types a1) (A2 : Finite_Types a2)
           (B1 : Finite_Types a1) (B2 : Finite_Types a2)
           (e1 : A1 <~> B1) (e2 : A2 <~> B2)
  : path_finite_types _ (sum_finite_types A1 A2) (sum_finite_types B1 B2)
                          (e1 +E e2)
    = ap011 sum_finite_types
            (path_finite_types _ _ _ e1)
            (path_finite_types _ _ _ e2).
Proof.
  revert e1.
  apply (equiv_functor_forall_pf (equiv_path_finite_types _ A1 B1)).
  intro p. revert e2.
  apply (equiv_functor_forall_pf (equiv_path_finite_types _ A2 B2)).
  intro q.
  destruct p. destruct q.
  simpl.
  refine (_ @ path_finite_types_id (a2 + a1) (sum_finite_types A1 A2) @ _).
  - apply (ap (path_finite_types (a2 + a1) (sum_finite_types A1 A2) (sum_finite_types A1 A2))).
    apply path_equiv. apply path_arrow. intros [x | y]; reflexivity.
  - apply inverse.
    apply (ap011 (ap011 sum_finite_types)
                 (path_finite_types_id a1 A1)
                 (path_finite_types_id a2 A2)).
Defined.

(* move *)
Lemma ap011_VV
  : forall {A B C: Type} (f : A -> B -> C)
           {a0 a1 : A} {b0 b1 : B}
           (p : a0 = a1) (q : b0 = b1),
    (ap011 f p q)^ = ap011 f p^ q^.
Proof.
  intros. destruct p. destruct q. reflexivity.
Defined.

  

(* Definition ccleq_act_concat (M : Monoidal_1Type) (X : 1-Type) *)
(*            (act : monoidal_action M X) (lf : left_faithful act) *)
(*            (s : M) (x y z : X) *)
(*            (p : act s x = y) (q : y = z) *)
(*   : ccleq (monoidal_action_cat M X act lf) (s; p @ q) = *)
(*     ccleq (monoidal_action_cat M X act lf) (s; p) @ (ap (ccl (monoidal_action_cat M X act lf)) q). *)
(* Proof. *)
(*   destruct q. rewrite concat_p1. rewrite concat_p1. reflexivity. *)
(* Qed. *)

    
Local Definition Z := cquot (group_completion_BSigma).
Require Import Category.Core.

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
    

  
Definition finsum_id (m n : nat) :
  sum_BSigma (canon_BSigma m) (canon_BSigma n) = canon_BSigma (n+m) :=
  path_BSigma (sum_BSigma (canon_BSigma m) (canon_BSigma n)) (canon_BSigma (n+m)) (equiv_finsum m n).

Definition finsum_id_fix (m n : nat)
  : sum_finite_types (canon m) (canon n) = canon (n + m) :=
  path_finite_types _ (sum_finite_types (canon m) (canon n)) (canon (n+m)) (equiv_finsum m n).

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
    
           (* {s a b : nat} (S : Finite_Types s) (A : Finite_Types a) (B : Finite_Types b) *)
Definition lcancel_Z (S A B : BSigma)
  : BSigma_to_Z A B = BSigma_to_Z (sum_BSigma S A) (sum_BSigma S B) :=
  path_Z S idpath idpath.

Definition path_is_lcancel {A1 B1 A2 B2} (S : BSigma)
           (p : sum_BSigma S A1 = A2) (q : sum_BSigma S B1 = B2)
  : path_Z S p q = lcancel_Z S A1 B1 @ ap011 BSigma_to_Z p q.
Proof.
  destruct p. destruct q. rewrite concat_p1.
  reflexivity.
Defined.

(* move *)
(* Arguments Build_BSigma {card_BSigma}. *)

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
(*   unfold lcancel_Z. *)
(*   apply moveL_pV. *)
(*   refine (_ @ cconcat group_completion_BSigma _ _). *)
(*   simpl. *)
(*   rewrite concat_p1. rewrite concat_p1.  *)
(*   change (functor_prod ?f ?g (?x, ?y)) with (f x, g y). *)
(*   change (functor_prod ?f ?g (?x, ?y)) with (f x, g y). *)
(*   apply inverse. *)
(*   refine (_ @ *)
(*             ccleq_concat_Z *)
(*             (sum_BSigma T S) A B _ _ idpath *)
(*             (path_prod (sum_BSigma (sum_BSigma T S) A, sum_BSigma (sum_BSigma T S) B) *)
(*                        (sum_BSigma T (sum_BSigma S A), sum_BSigma T (sum_BSigma S B)) *)
(*                        (BSigma_assoc T S A) *)
(*                        (BSigma_assoc T S B)) @ _). *)
(*   { rewrite concat_1p. reflexivity. } *)
(*   apply whiskerL. *)
(*   destruct (BSigma_assoc T S A).  destruct (BSigma_assoc T S B). reflexivity. *)
(* Qed. *)

Definition lcancel_canon (s m n : nat) :
  BSigma_to_Z (canon_BSigma m) (canon_BSigma n) =
  BSigma_to_Z (canon_BSigma (m+s)) (canon_BSigma (n + s)).
Proof.
  refine (lcancel_Z (canon_BSigma s) _ _@ _).
  apply (ap011 BSigma_to_Z); apply finsum_id.
  (* apply (path_Z (canon_BSigma s)); *)
  (*   apply finsum_id. *)
Defined.

Definition lcancel_canon_path (s a b : nat)
           (alpha : Fin a <~> Fin a) (betta : Fin b <~> Fin b) 
  : ap011 BSigma_to_Z
          (path_BSigma (canon_BSigma (a+s)) (canon_BSigma (a+s)) (block_sum equiv_idmap alpha))
          (path_BSigma (canon_BSigma (b+s)) (canon_BSigma (b+s)) (block_sum equiv_idmap betta)) =
    (lcancel_canon s a b)^ @
          ap011 BSigma_to_Z (path_BSigma (canon_BSigma a) (canon_BSigma a) alpha)
                            (path_BSigma (canon_BSigma b) (canon_BSigma b) betta)
      @ lcancel_canon s a b.
Proof.
  unfold lcancel_canon.
  rewrite inv_pp.
  repeat refine (_ @ concat_p_pp _ _ _).
  apply moveL_Vp.
  rewrite <- ap011_pp_pp.
  repeat refine (_ @  (concat_pp_p _ _ _)).
  apply moveL_pM.
  rewrite ap011_VV.
  rewrite <- ap011_pp_pp.
  assert (H : forall (x : nat) (e : Fin x <~> Fin x),
             (finsum_id s x @
                         path_BSigma (canon_BSigma (x + s)) (canon_BSigma (x + s)) (block_sum 1 e))
               @ (finsum_id s x)^ = 
             path_BSigma (sum_BSigma (canon_BSigma s) (canon_BSigma x))
                         (sum_BSigma (canon_BSigma s) (canon_BSigma x))
                         (equiv_functor_sum_l e)).
  { intros.
    unfold block_sum.
    rewrite <- path_BSigma_compose.
    rewrite path_BSigma_V.
    rewrite <- path_BSigma_compose.
    apply (ap (path_BSigma _ _)).
    repeat rewrite ecompose_ee_e.
    rewrite ecompose_V_ee. rewrite ecompose_Ve.
    rewrite ecompose_e1. reflexivity. }
  rewrite H. rewrite H. clear H.
  rewrite <- natural_path_BSigma_r. rewrite <- natural_path_BSigma_r.
  destruct (path_BSigma (canon_BSigma a) (canon_BSigma a) alpha).
  destruct (path_BSigma (canon_BSigma b) (canon_BSigma b) betta).
  rewrite concat_p1. rewrite concat_Vp. reflexivity.
Defined.
  
  
                                                                                     
  
                            
   
          
          
          



(* Definition plus_assoc_Z (a1 b1 c1 a2 b2 c2 : nat) *)
(*   : BSigma_to_Z (canon_BSigma ((a1 + b1) + c1)) (canon_BSigma ((a2 + b2) + c2)) = *)
(*     BSigma_to_Z (canon_BSigma (a1 + (b1 + c1))) (canon_BSigma (a2 + (b2 + c2))). *)
(* Proof. *)
(*   apply (ap011 BSigma_to_Z); *)
(*     apply (ap canon_BSigma); apply nat_lemmas.plus_assoc. *)
(* Defined. *)

Definition lcancel_canon_compose (m n s t : nat)
  : lcancel_canon (s + t) m n  =
    lcancel_canon s m n @ lcancel_canon t (m + s) (n + s)
                  @ (ap011 BSigma_to_Z (canon_BSigma_assoc _ _ _) (canon_BSigma_assoc _ _ _))^.
Proof.
  unfold lcancel_canon.
  assert (H : lcancel_Z (canon_BSigma (s + t)) (canon_BSigma m) (canon_BSigma n) =
              lcancel_Z (sum_BSigma (canon_BSigma t) (canon_BSigma s))
                        (canon_BSigma m) (canon_BSigma n)
              @ ap011 BSigma_to_Z
                      (ap011 sum_BSigma (finsum_id _ _) idpath)
                      (ap011 sum_BSigma (finsum_id _ _) idpath)).
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

(* Lemma nat_symm_r (a b c : nat) *)
(*     : (a + b + c = a + (c + b))%nat. *)
(* Proof. *)
(*   refine ((nat_lemmas.plus_assoc _ _ _) @ _). *)
(*   apply (ap (Peano.plus a)). *)
(*   apply nat_plus_comm.  *)
(* Defined. *)

(* Lemma nat_symm_l (a b c : nat) *)
(*   : (a + b + c = b + a + c)%nat. *)
(* Proof. *)
(*   rewrite (nat_plus_comm a b). *)
(*   reflexivity. *)
(* Defined. *)

(* Definition lcancel_canon_diff (s a b : nat) *)
(*   : BSigma_to_Z (canon_BSigma (a + s)) (canon_BSigma (b + s)) =  *)
(*     BSigma_to_Z (canon_BSigma (a + (s.+1))) (canon_BSigma (b + (s.+1))).     *)
(* Proof. *)
(*   refine (lcancel_Z (canon_BSigma 1) _ _ @ _). *)
(*   refine (ap011 BSigma_to_Z (finsum_id _ _) (finsum_id _ _) @ _). *)
(*   apply (ap011 BSigma_to_Z); apply (ap canon_BSigma); simpl. *)
(* Defined. *)
                

(* Definition lcancel_canon_succ (s a b : nat)  *)
(*   : lcancel_canon (s.+1) a b = *)
(*     lcancel_canon s a b @ (lcancel_canon_diff s a b). *)
(* Proof. *)
(*   unfold lcancel_canon_diff. *)
(*   unfold nat_symm_r. *)
  
(*   transitivity *)
(*     (lcancel_canon (1 + s) a b *)
(*                    @ *)
(*      (ap011 BSigma_to_Z (ap canon_BSigma (nat_symm_r a s 1)) (ap canon_BSigma (nat_symm_r b s 1)))^). *)
                  
                  
(*                   (ap011 BSigma_to_Z (canon_BSigma_assoc _ _ _) (canon_BSigma_assoc _ _ _))^ *)
(*                   @ ap011 (BSigma_to_Z) *)
(*                           (ap canon_BSigma (nat_symm_l _ _ _)) *)
(*                           (ap canon_BSigma (nat_symm_l _ _ _)). *)
(* Proof. *)
(*   transitivity *)
(*     (lcancel_canon (1 + s) a b *)
(*                    @ ap011 (BSigma_to_Z) *)
(*                            (ap canon_BSigma (nat_plus_comm _ _)) *)
(*                            (ap canon_BSigma (nat_plus_comm _ _))). *)
                   
                   

(*   Lemma nat_symm_r (a b c : nat) *)
(*     : a + (b + c) = a + (c + b). *)

(*   (lcancel_canon (s.+1) a b)^ @  lcancel_canon s a b @ lcancel_canon 1 _ _ *)


(*   = *)
(*     lcancel_canon s a b @ lcancel_canon 1 _ _ @ . *)

           





(* Proof. *)
(*   unfold lcancel_canon. *)
(*   rewrite  path_Z_compose. *)
(*   rewrite path_is_lcancel. *)
(*   rewrite path_is_lcancel. *)
  

  
(*                   (ap011 (fun x y => BSigma_to_Z (canon_BSigma x) (canon_BSigma y)) *)
(*                          (nat_lemmas.plus_assoc _ _ _) *)


  (* -  *)
  (* := lcancel_Z _ _ _ @ canon_grpclBSigma_sum _ _ _ _. *)
  (* := *)
  (* (ccl (group_completion_BSigma) ((canon_BSigma m), (canon_BSigma n))) = *)
  (* (ccl (group_completion_BSigma) ((canon_BSigma (m+s)), (canon_BSigma (n+s)))) := *)
  (* (ccleq group_completion_BSigma (canon_BSigma s; idpath)) @ canon_grpclBSigma_sum s s m n. *)

(* (* Auxillary stuff. Move? *) *)
(* Definition double_transport {A B : Type} (P : A -> B -> Type) {a1 a2 : A} {b1 b2 : B} : *)
(*   a1 = a2 -> b1 = b2 -> P a1 b1 -> P a2 b2. *)
(* Proof. *)
(*   intros [] []. exact idmap. *)
(* Defined. *)

(* Definition double_apD {A B : Type} (P : A -> B -> Type) *)
(*            (f : forall (a : A) (b : B), P a b) *)
(*            {a1 a2 : A} {b1 b2 : B} *)
(*            (p : a1 = a2) (q : b1 = b2) : *)
(*   double_transport P p q (f a1 b1) = f a2 b2. *)
(* Proof. *)
(*   destruct p. destruct q. reflexivity. *)
(* Defined. *)

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

Definition double_pathover {A B : Type} (P : A -> B -> Type)
           {a a' : A} (p : a = a')
           {b b' : B} (q : b = b')
           (c : P a b) (c' : P a' b') : Type.
Proof.
  destruct p,q. exact (c = c').
Defined.

Definition double_pathover_to_path {A B : Type} (P : A -> B -> Type)
           {a a' : A} (p : a = a')
           {b b' : B} (q : b = b')
           (c : P a b) (c' : P a' b')
  : double_pathover P p q c c' ->
    transport (uncurry P) (path_prod (a,b) (a',b') p q) c = c'.
Proof.
  destruct p, q. exact idmap.
Defined.

Definition apd_po011
           (A B : Type) (C : A -> B -> Type) (f : forall (a : A) (b : B), C a b)
           (a1 a2 : A) (b1 b2 : B)
           (p : a1 = a2) (q : b1 = b2)
  : double_pathover C p q (f a1 b1) (f a2 b2).
Proof.
  destruct p. destruct q. reflexivity.
Defined.


(* Auxillary stuff for the next result *)
Local Definition grp_compl_BSigma_ind_set_Fin {a b : nat}
      {P : Z -> hSet}
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
             (fun x y => P (Fin_to_Z x y)) (f a b)).
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
           (P : Z -> hSet)
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
    apply (@grp_compl_BSigma_ind_set_Fin a b P f base_change).
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
      + apply (grp_compl_BSigma_ind_set_Fin f base_change).
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
                (grp_compl_BSigma_ind_set_Fin f base_change A B)
                  (grp_compl_BSigma_ind_set_Fin f base_change (sum_finite_types (canon s) (canon a))
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

  (* make these their own lemmas because they don't need to get unfolded later *)
  (* Definition BDet_sum_sum (s a1 a2 : nat) *)
  (*   : BDet _ (sum_finite_types (sum_finite_types (canon s) (canon a1)) *)
  (*                              (sum_finite_types (canon s) (canon a2))) *)
  (*     = BDet _ (sum_finite_types (canon (a1 + s)) (canon (a2 + s))) *)
  (*   := ap (BDet _) (ap011 sum_finite_types *)
  (*                         (sum_finite_types_canon) *)
  (*                         (sum_finite_types_canon)). *)

  Definition sum_BSigma_uncurry : BSigma * BSigma -> BSigma
    := fun AB =>
         match AB with
           (A,B) => sum_BSigma A B
         end.

  Definition canonsum_BSigma (a b : nat)
    : sum_BSigma (canon_BSigma a) (canon_BSigma b) = canon_BSigma (b+a)
    :=
      path_BSigma
        (sum_BSigma (canon_BSigma a) (canon_BSigma b))
        (canon_BSigma (b+a))
        (equiv_finsum a b).
                                                     

  Definition BDet_sum2 (s a b : nat)
    : BDet _ (sum_finite_types
              (sum_finite_types (canon s) (canon a))
              (sum_finite_types (canon s) (canon b))) =
      BDet _ (sum_finite_types (canon (a + s)) (canon (b + s))).

  (*     BDet_uncurry *)
  (*       (fin_to_BSigma *)
  (*          (sum_finite_types *)
  (*             (sum_finite_types (canon s) (canon a)) *)
  (*             (sum_finite_types (canon s) (canon b)))) = *)
  (*     BDet_uncurry (fin_to_BSigma (sum_finite_types (canon (a + s)) (canon (b + s)))). *)
  (* Proof. *)
  (*   apply (ap (BDet_uncurry)). *)
  (*   exact (ap011 sum_BSigma (canonsum_BSigma s a) (canonsum_BSigma s b)). *)
  (* Defined. *)
    apply (ap (BDet _)).
    apply (ap011 sum_finite_types);
      apply sum_finite_types_canon.
  Defined.

  Definition BDet_sum_canon2 (a1 a2 : nat)
    : BDet _ (sum_finite_types (canon a1) (canon a2)) = canon 2
    := ap (BDet _) sum_finite_types_canon @ deloop_fin_canon (a2 + a1) 2 (dethom _).
             
  (*   : BDet_uncurry (fin_to_BSigma (sum_finite_types (canon a1) (canon a2))) = canon 2. *)
  (* Proof. *)
  (*   refine (_ @ deloop_fin_canon (a2 + a1) 2 (dethom _)). *)
  (*   (* change (BDet ?m ?x) with (BDet_uncurry (m; x)). *) *)
  (*   change (deloop_fin ?m 2 (dethom ?m) ?x) with (BDet_uncurry (fin_to_BSigma x)). *)
  (*   apply (ap BDet_uncurry). *)
  (*   apply (canonsum_BSigma a1 a2). *)
  (* Defined. *)


  Definition BDet_SASB_canon (s a1 a2 : nat) :
    (* BDet_uncurry (fin_to_BSigma (sum_finite_types (canon a1) (canon a2))) = *)
    (* BDet_uncurry (fin_to_BSigma (sum_finite_types *)
    (*                                  (sum_finite_types (canon s) (canon a1)) *)
    (*                                  (sum_finite_types (canon s) (canon a2)))) *)
                 
    BDet (a2 + a1) (sum_finite_types (canon a1) (canon a2)) =
    BDet (a2 + s + (a1 + s))
         (sum_finite_types
            (sum_finite_types (canon s) (canon a1))
            (sum_finite_types (canon s) (canon a2)))
  := 
    BDet_sum_canon2 a1 a2 @ (BDet_sum_canon2 (a1+s) (a2 + s))^ @ (BDet_sum2 s a1 a2)^.

  Lemma blocksum_is_ap011 (a b : nat) (alpha : canon a = canon a) (betta : canon b = canon b)
    : block_sum (pft_inv alpha) (pft_inv betta) =
      pft_inv (sum_finite_types_canon^
               @ (ap011 sum_finite_types alpha betta @ sum_finite_types_canon)).
  Proof.
    intros. unfold block_sum.
    unfold sum_finite_types_canon.
    change (path_finite_types ?m ?A ?B) with (pft A B).
    assert (pft_inv_pp
            : forall (m : nat) (A B C : Finite_Types m) (x : A = B) (y : B = C),
               pft_inv (x @ y) = pft_inv y oE pft_inv x).
    { intros m A B C [] []. simpl. apply inverse. apply ecompose_e1. }
    rewrite pft_inv_pp. rewrite pft_inv_pp. clear pft_inv_pp.
    assert (pft_sect : forall (m : nat) (A B : Finite_Types m) (e : A <~> B),
               pft_inv (pft A B e)
              = e).
    { intros. exact (eissect (equiv_path_finite_types _ A B) e). }
    rewrite pft_sect. 
    rewrite <- path_finite_types_V. rewrite pft_sect.
    apply (ap (fun f => f oE (equiv_finsum a b)^-1)).
    apply (ap (fun f => equiv_finsum a b oE f)).
    cut (forall (A : Finite_Types a) (B : Finite_Types b)
                (alpha' : canon a = A) (betta' : canon b = B),
            pft_inv alpha' +E pft_inv betta' = pft_inv (ap011 sum_finite_types alpha' betta')).
    { intro H. apply (H _ _ alpha betta). }
    intros A B [] []. apply path_equiv. apply path_arrow. intros [x | x]; reflexivity.
  Qed.
      
  Definition BDet_SASB (s a1 a2 : nat)
             (S : Finite_Types s) (A1 : Finite_Types a1) (A2 : Finite_Types a2)
  : BDet (a2 + a1) (sum_finite_types A1 A2) =
    BDet (a2 + s + (a1 + s)) (sum_finite_types (sum_finite_types S A1) (sum_finite_types S A2)).
  Proof.
    revert S A1 A2.
    cut (forall SA : (Finite_Types s) * ((Finite_Types a1) * (Finite_Types a2)),
            BDet_uncurry (fin_to_BSigma (sum_finite_types (fst (snd SA)) (snd (snd SA)))) =
            BDet_uncurry
              (fin_to_BSigma (sum_finite_types (sum_finite_types (fst SA) (fst (snd SA)))
                                               (sum_finite_types (fst SA) (snd (snd SA)))))).
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
            
            (* ap (BDet_uncurry) (ap (fin_to_BSigma) *)
            (*                       (ap011 sum_finite_types *)
            (*                              (ap fst (ap snd q)) *)
            (*                              (ap snd (ap snd q))))). *)
            
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
            (* ap (BDet_uncurry) *)
            (*    (ap (fin_to_BSigma) *)
            (*        (ap011 *)
            (*           sum_finite_types *)
            (*           (ap011 sum_finite_types ((ap fst q)) *)
            (*                  ((ap fst (ap snd q)))) *)
            (*           (ap011 sum_finite_types ((ap fst q)) *)
            (*                  ((ap snd (ap snd q))))))). *)
            ap (BDet _)
               (ap011
                  sum_finite_types
                  (ap011 sum_finite_types ((ap fst q))
                         ((ap fst (ap snd q))))
                  (ap011 sum_finite_types ((ap fst q))
                         ((ap snd (ap snd q)))))).
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

      
      rewrite ap_fst_path_prod. unfold BDet_SASB_canon.
      unfold BDet_sum_canon2. unfold BDet_sum2.
      apply moveL_pV. apply moveL_pV.
      repeat rewrite concat_pp_p.
      apply moveR_Vp. apply moveR_Mp. apply moveR_Mp.
      rewrite inv_pp.
      rewrite <- ap_V.
      rewrite <- ap_V.
      rewrite <- (ap_V (BDet (a2 + a1)%nat) sum_finite_types_canon).
      repeat refine (_ @ concat_pp_p _ _ _).
      apply moveL_pM.
      repeat refine (_ @ concat_p_pp _ _ _).
      rewrite <- (ap_pp (BDet (a2 + a1)%nat)).
      rewrite <- (ap_pp (BDet (a2 + a1)%nat)).
      apply moveR_pV.
      repeat refine (concat_p_pp _ _ _ @ _).
      apply moveR_pM.
      repeat refine (concat_pp_p _ _ _ @ _).
      rewrite <- (ap_pp (BDet (_ + _)%nat)).
      rewrite <- (ap_pp (BDet (_ + _)%nat)).
      rewrite <- (ap_pp (BDet (_ + _)%nat)).
      rewrite <- (ap_pp (BDet (_ + _)%nat)).
      apply moveL_pV.
      refine (_ @ (deloop_fin_loop _ _ _ _)^).
      refine (deloop_fin_loop _ _ _ _ @ _). simpl.
      apply (ap (path_finite_types 2 _ _)).
      refine (_ @ ((det_sasb _ _ _ (pft_inv p) (pft_inv q) (pft_inv r))) @ _);
        apply (ap (determinant _)).
      - apply inverse.
        refine (_ @ blocksum_is_ap011
                  (a1 + s) (a2 + s)
                  (pft (canon _) (canon _)
                       (block_sum (pft_inv p) (pft_inv q)))
                  (pft (canon _) (canon _) (block_sum (pft_inv p) (pft_inv r))) @ _ ).
        { apply (ap011 block_sum).
          - apply inverse.
            exact (eissect
                     (equiv_path_finite_types (a1 + s) (canon (a1 + s)) (canon (a1 + s)))
                     (block_sum (pft_inv p) (pft_inv q))
                  ).
          - apply inverse.
            exact (eissect
                     (equiv_path_finite_types (a2 + s) (canon (a2 + s)) (canon (a2 + s)))
                     (block_sum (pft_inv p) (pft_inv r))
                  ). }
        apply (ap (inv_path_finite_types (a2 + s + (a1 + s)) (canon (a2 + s + (a1 + s))) 
                                             (canon (a2 + s + (a1 + s))))).
        apply whiskerL.
        repeat refine (_ @ concat_pp_p _ _ _). apply whiskerR.
        rewrite blocksum_is_ap011.  rewrite blocksum_is_ap011.
        rewrite ap011_VV.
        rewrite <- ap011_pp_pp. rewrite <- ap011_pp_pp.
        apply (ap011 (ap011 sum_finite_types)).
        * refine (eisretr
                   (equiv_path_finite_types (a1 + s) (canon (a1 + s)) (canon (a1 + s)))
                   (sum_finite_types_canon^ @ (ap011 sum_finite_types p q @ sum_finite_types_canon))
                   @ _ ).
          apply concat_p_pp.
        * refine (eisretr
                   (equiv_path_finite_types (a2 + s) (canon (a2 + s)) (canon (a2 + s)))
                   (sum_finite_types_canon^ @ (ap011 sum_finite_types p r @ sum_finite_types_canon))
                   @ _ ).
          apply concat_p_pp.
      - refine (blocksum_is_ap011 _ _ q r ).
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

  Definition ap011_BDet_canon {m1 m2 n1 n2 : nat} (p1 : m1 = n1) (p2 : m2 = n2)
    : BDet (m2 + m1) (sum_finite_types (canon m1) (canon m2))
      = BDet (n2 + n1) (sum_finite_types (canon n1) (canon n2)).
  Proof.
    (* change (BDet (m2 + m1) (sum_finite_types (canon m1) (canon m2))) *)
    (*        with (sum_BSigma (canon_BSigma m1) (canon_BSigma m2)). *)
    change (BDet ?m ?A) with (BDet_uncurry (fin_to_BSigma A)).
    apply (ap BDet_uncurry).
    
    (* change (sum_finite_types (canon m1) (canon m2)) with (sum_BSigma (canon_BSigma m1) *)
    (*                                                                  (canon_BSigma m2)). *)

    change (sum_finite_types (canon ?m) (canon ?n)) with (sum_finite_types (canon_BSigma m)
                                                                           (canon_BSigma n)).
    change (fin_to_BSigma
              (sum_finite_types (canon_BSigma ?m) (canon_BSigma ?n))) with
    (sum_BSigma (canon_BSigma m) (canon_BSigma n)).
    apply (ap011 sum_BSigma); apply (ap canon_BSigma).
    - exact p1. - exact p2.
        
    (* apply (ap011 (fun a b => fin_to_BSigma (sum_finite_types (canon a) (canon b))) p1 p2). *)
  Defined.
  
  Definition grpcompl_to_fin2 : Z -> Finite_Types 2.
  Proof.
    srapply @grp_compl_BSigma_rec.
    - simpl.
      intros A B. apply (BDet_uncurry). exact (sum_BSigma A B).
      (* intros [a1 A1] [a2 A2]. *)
      (* exact (BDet (a2 + a1) (sum_finite_types A1 A2)). *)
    - simpl. intros [s S] [a1 A1] [a2 A2].
      apply BDet_SASB.
    - intros [s S] [t T] [a1 A1] [a2 A2]. 
      
      change {| card_BSigma := ?m; fintype_of_BSigma := ?A |} with (fin_to_BSigma A).
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

      (* unfold sum_BSigma. *)
      change (fin_to_BSigma (canon ?m)) with
      (canon_BSigma m). 
      
      assert (H : forall (x m n : nat)
                       (S S': Finite_Types x) (A : Finite_Types m) (B : Finite_Types n)
                       (p : S = S'),
                 BDet_SASB _ _ _ S A B =
                 BDet_SASB _ _ _ S' A B
                           @ (ap (BDet _)
                                 (ap011 sum_finite_types
                                        (ap011 sum_finite_types p idpath)
                                        (ap011 sum_finite_types p idpath)))^).
                                 (* (ap (fun x => sum_finite_types (sum_finite_types x A) *)
                                 (*                                (sum_finite_types x B)) p))^). *)
      { intros. destruct p. refine (concat_p1 _)^. }
      rewrite (H _ _ _ _ _ _ _ (finsum_id_fix t s)). clear H.
      assert (H :
                forall (x m n : nat)
                       (S S': Finite_Types x) (A A' : Finite_Types m) (B B' : Finite_Types n)
                       (p : S = S') (q : A = A') (r : B = B'),
                  BDet_SASB _ _ _ S A B =
                  (ap (BDet _) (ap011 sum_finite_types q r))
                    @ BDet_SASB _ _ _ S' A' B' @
                    (ap (BDet _) (ap011 sum_finite_types
                                        (ap011 sum_finite_types p q)
                                        (ap011 sum_finite_types p r)))^).
      { intros. destruct p. destruct q. destruct r.
        refine (_ @ (concat_p1 _)^).
        refine (concat_1p _)^. }
      rewrite (H _ _ _ _ _ _ _ _ _
                 idpath (finsum_id_fix s a1) (finsum_id_fix s a2)).
      (* rewrite (H _ _ _ _ _ _ _ _ _ *)
      (*            (finsum_id t s) idpath idpath). *)
      clear H.
      (* rewrite (BDet_SASB_canon_id s a1 a2). *)
      rewrite BDet_SASB_canon_id.
      rewrite BDet_SASB_canon_id.
      rewrite BDet_SASB_canon_id.
      unfold BDet_SASB_canon.
      change (ap (BDet (a2 + s + (a1 + s)))
                 (ap011 sum_finite_types (finsum_id_fix s a1) (finsum_id_fix s a2)))
      with (BDet_sum2 s a1 a2).
      repeat rewrite (concat_pp_p (BDet_sum_canon2 a1 a2)). apply whiskerL.
      (* rewrite <- (inv_V (BDet_sum_canon2 a1 a2)). *)
      
      (* destruct ((BDet_sum_canon2 a1 a2)^). rewrite concat_1p. rewrite concat_1p. *)
      rewrite <- (inv_pp (BDet_sum2 s a1 a2) (BDet_sum_canon2 (a1 + s) (a2 + s)) ).
      rewrite (concat_pp_p (BDet_sum_canon2 (a1 + s) (a2 + s))).
      rewrite (concat_p_pp (BDet_sum2 s a1 a2)).
      rewrite (concat_pp_p (BDet_sum2 s a1 a2 @ BDet_sum_canon2 (a1 + s) (a2 + s))).
      rewrite concat_V_pp.
      assert (H : forall (m1 m2 n1 n2 : nat) (p1 : m1 = n1) (p2 : m2 = n2),
                 (BDet_sum_canon2 n1 n2)^
                 = (BDet_sum_canon2 m1 m2)^ @ (ap011_BDet_canon p1 p2)).
      { intros. destruct p1. destruct p2. apply inverse. apply concat_p1.  }
      
      rewrite (H _ _ _ _ (nat_lemmas.plus_assoc a1 s t)^ (nat_lemmas.plus_assoc a2 s t)^).
      clear H. repeat rewrite concat_pp_p. apply whiskerL.
      apply moveR_Vp.
      unfold BDet_sum2.
      apply moveR_Vp.
      repeat rewrite concat_p_pp.
      apply moveL_pV. apply moveL_pV.
      rewrite <- (ap_pp (BDet (a2 + (s + t) + (a1 + (s + t))))).
      rewrite <- ap011_pp_pp.
      rewrite concat_pp_p.
      rewrite <- (ap_pp (BDet (a2 + s + t + (a1 + s + t)))).
      rewrite <- ap011_pp_pp.
      assert (H : forall (X1 X2 Y1 Y2 : BSigma) (p : X1 = X2) (q : Y1 = Y2),
                 ap011 (fun A B : BSigma => BDet_uncurry (sum_BSigma A B)) p q =
                 ap BDet_uncurry (ap011 sum_BSigma p q)).
      { intros. destruct p. destruct q. reflexivity. }
      rewrite H. clear H. unfold ap011_BDet_canon.
      assert (H : forall (m : nat) (A B : Finite_Types m) (p : A = B),
                 ap (BDet m) p =
                 ap BDet_uncurry (ap fin_to_BSigma p)).
      { intros. destruct p. reflexivity. }
      rewrite H. rewrite H. clear H.
      
      refine (_ @ ap_pp BDet_uncurry (ap fin_to_BSigma _)
                                     (ap011 sum_BSigma
                                            (ap canon_BSigma _) (ap canon_BSigma _))).
                
                                     (* (ap011 (fun a b : nat => *)
                                     (*           fin_to_BSigma (sum_finite_types (canon a) (canon b))) *)
                                     (*        _ _)). *)
      refine ((ap_pp BDet_uncurry
                     (ap011 sum_BSigma
                            (BSigma_assoc (canon_BSigma t) (canon_BSigma s) (canon_BSigma a1))
                            (BSigma_assoc (canon_BSigma t) (canon_BSigma s) (canon_BSigma a2)))
                     _)^ @ _).
      apply (ap (ap BDet_uncurry)).
      assert (H : forall (m n : nat) (A1 A2 : Finite_Types m) (B1 B2 : Finite_Types n)
                         (p1 : A1 = A2) (p2 : B1 = B2),
                 ap fin_to_BSigma (ap011 sum_finite_types p1 p2) =
                 ap011 sum_BSigma (ap fin_to_BSigma p1) (ap fin_to_BSigma p2)).
      { intros. destruct p1. destruct p2. reflexivity. }
      rewrite H. rewrite H. clear H.
      rewrite <- ap011_pp_pp.
      refine (_ @ ap011_pp_pp sum_BSigma _ _ _ _).
      cut (forall (a : nat),
              BSigma_assoc (canon_BSigma t) (canon_BSigma s) (canon_BSigma a) @
                           ap fin_to_BSigma (ap011 sum_finite_types 1 (finsum_id_fix s a) @
                                                   sum_finite_types_canon) =
              ap fin_to_BSigma (ap011 sum_finite_types (finsum_id_fix t s) 1 @
                                       sum_finite_types_canon) @
                  ap canon_BSigma (nat_lemmas.plus_assoc a s t)^).
      { intro H.
        apply (ap011 (ap011 sum_BSigma)); apply H. }
      intro a.
      apply moveL_Mp. (* hei *)
      refine (_ @ eq_canon_BSigma_assoc _ _ _).
      unfold canon_BSigma_assoc.
      unfold canon_assoc.
      (* move? *)
      assert (path_finite_types_nat_l : forall (m n: nat)
                                               (A1 A2 : Finite_Types m)
                                               (B : Finite_Types n)
                                               (e : A1 <~> A2),
                 ap011 sum_finite_types
                       (path_finite_types _ A1 A2 e)
                       (idpath B) =
                 path_finite_types _ (sum_finite_types A1 B) (sum_finite_types A2 B) 
                                   (equiv_functor_sum_r e )).
      { intros.
        refine (_ @ ap
                  (fun f =>
                     path_finite_types (n + m)
                                       (sum_finite_types A1 B)
                                       (sum_finite_types A2 B)
                                       (equiv_functor_sum_r f))
                  (eissect (equiv_path_finite_types _ _ _) e)).
        simpl.
        destruct (path_finite_types m A1 A2 e).
        apply inverse.
        refine (_ @ path_finite_types_id _ _).
        apply (ap (path_finite_types _ _ _)). simpl.
        apply path_equiv. apply path_arrow. intros [x | x]; reflexivity. }

      assert (path_finite_types_nat_r : forall (m n: nat)
                                               (A : Finite_Types m)
                                               (B1 B2 : Finite_Types n)
                                               (e : B1 <~> B2),
                 ap011 sum_finite_types
                       (idpath A)
                       (path_finite_types _ B1 B2 e) =
                 path_finite_types _ (sum_finite_types A B1) (sum_finite_types A B2) 
                                   (equiv_functor_sum_l e )).
      { intros.
        refine (_ @ ap
                  (fun f =>
                     path_finite_types (n + m)
                                       (sum_finite_types _ _)
                                       (sum_finite_types _ _)
                                       (equiv_functor_sum_l f))
                  (eissect (equiv_path_finite_types _ _ _) e)).
        simpl.
        destruct (path_finite_types _ _ _ e).
        apply inverse.
        refine (_ @ path_finite_types_id _ _).
        apply (ap (path_finite_types _ _ _)). simpl.
        apply path_equiv. apply path_arrow. intros [x | x]; reflexivity. }

      
      
      (* assert (path_finite_types_nat : forall (m1 m2 : nat) *)
      (*                                        (A1 B1 : Finite_Types m1) *)
      (*                                        (A2 B2 : Finite_Types m2) *)
      (*                                        (e1 : A1 <~> B1) *)
      (*                                        (e2 : A2 <~> B2), *)
      (*            ap011 sum_finite_types *)
      (*                  (path_finite_types _ A1 B1 e1) *)
      (*                  (path_finite_types _ A2 B2 e2) = *)
      (*            path_finite_types _ (sum_finite_types A1 A2) (sum_finite_types B1 B2) *)
      (*                              (equiv_functor_sum' e1 e2)). *)
      (* { intros. *)
      (*   refine (_ @ ap011 *)
      (*             (fun f g => *)
      (*                path_finite_types (m2 + m1) *)
      (*                                  (sum_finite_types A1 A2) (sum_finite_types B1 B2) (f +E g)) *)
      (*             (eissect (equiv_path_finite_types _ _ _) e1) *)
      (*             (eissect (equiv_path_finite_types _ _ _) e2)). *)
      (*   simpl. *)
      (*   destruct (path_finite_types m1 A1 B1 e1). *)
      (*   destruct (path_finite_types m2 A2 B2 e2). *)
      (*   apply inverse. *)
      (*   refine (_ @ path_finite_types_id _ _). *)
      (*   apply (ap (path_finite_types _ _ _)). simpl. *)
      (*   apply path_equiv. apply path_arrow. intros [x | x]; reflexivity. } *)

      rewrite path_finite_types_nat_l. clear path_finite_types_nat_l.
      rewrite path_finite_types_nat_r. clear path_finite_types_nat_r.
      change (ap fin_to_BSigma ?p) with (pft_to_pbs p).
      unfold BSigma_assoc.
      unfold sum_BSigma.  unfold canon_BSigma.
      (* change sum_BSigma . . . with fin_to_BSigma . . . *)
      
      (* refine (whiskerR (ap inverse *)
      (*                      (@path_BSigma_fix *)
      (*            (a + (s + t))%nat *)
      (*            (sum_finite_types (sum_finite_types (canon t) (canon s)) (canon a)) *)
      (*   (sum_finite_types (canon (s + t)) (canon a)) (equiv_functor_sum_r (equiv_finsum t s)) *)
      (*         )) _ @ _). *)
      (* Arguments pft_to_pbs : clear implicits. *)
      unfold sum_finite_types_canon.
      rewrite <- path_finite_types_compose.
      rewrite <- path_finite_types_compose.
      rewrite path_BSigma_fix.
      rewrite path_BSigma_fix.
      apply moveR_Vp.
      rewrite <- path_BSigma_compose.
      rewrite <- path_BSigma_compose.

      apply (ap
               (fun e =>
                  path_BSigma
                    (fin_to_BSigma
                       (sum_finite_types
                          (fin_to_BSigma
                             (sum_finite_types (fin_to_BSigma (canon t)) (fin_to_BSigma (canon s))))
                          (fin_to_BSigma (canon a))))
                    (fin_to_BSigma (canon (a + s + t))) e)).
      simpl.
      repeat rewrite ecompose_ee_e.
      rewrite ecompose_V_ee.
      rewrite ecompose_Ve. rewrite ecompose_e1.
      reflexivity.
  Defined.


End GrpCompl_To_Fin2.


Section IsEquiv_GrpCompl_To_Fin2.
    (* move? *)
  Definition transpose_last_two_is_block_sum (a : nat)
    : fin_transpose_last_two a = (block_sum equiv_idmap twist2).
  Proof.
    apply path_equiv. apply path_arrow.
    intros [[x | []] | []]; reflexivity.
  Defined.

  Definition block_sum_is_id (m n : nat)
    : equiv_idmap (Fin (n + m)) = block_sum (equiv_idmap (Fin m)) (equiv_idmap (Fin n)).
  Proof.
    unfold block_sum.
    assert (p : equiv_idmap (Fin m) +E equiv_idmap (Fin n) = equiv_idmap ((Fin m) + (Fin n))).
    { apply path_equiv. apply path_arrow. intros [x | x]; reflexivity. }
    rewrite p.
    rewrite ecompose_e1. apply inverse. apply ecompose_eV.
  Qed.

  
  (* We want to show that the map above induces and equivalence on the component of cardinality 2 *)
  (* First we connect all the canonical points in this component *)

  (* Definition path_base_0 (A : BSigma) *)
  (* : BSigma_to_Z (canon_BSigma 0) (canon_BSigma 0) = BSigma_to_Z A A. *)
  (* Proof. *)
  (*   refine (lcancel_Z A _ _ @ _). *)
  (*   apply (ap011 BSigma_to_Z); apply path_BSigma; apply sum_empty_r. *)
  (* Defined. *)

  Definition path_base_2 (a : nat)
    : BSigma_to_Z (canon_BSigma 2) (canon_BSigma 0) =
      BSigma_to_Z (canon_BSigma (a.+2)) (canon_BSigma a)
    := lcancel_canon a _ _.

  Definition path_base_diff (a : nat)
    : BSigma_to_Z (canon_BSigma (a.+2)) (canon_BSigma a) =
      BSigma_to_Z (canon_BSigma ((a.+1).+2)) (canon_BSigma a.+1).
  Proof.
    refine (lcancel_canon 1 _ _ @ _).
    apply (ap (fun x => BSigma_to_Z (canon_BSigma (2 + x)) (canon_BSigma (x)))).
    (* apply (ap011 BSigma_to_Z); apply (ap canon_BSigma); *)
    apply nat_plus_comm.
  Defined.


  Definition path_base_succ (a : nat)
    : path_base_2 (a.+1) =
      path_base_2 a @ path_base_diff a.
  Proof.
    unfold path_base_diff.
    unfold path_base_2.
    assert (H : forall (m n : nat) (p : m = n),
               lcancel_canon n 2 0 =
               lcancel_canon m 2 0 @
                    ap (fun x => BSigma_to_Z (canon_BSigma (2 + x)) (canon_BSigma (0 + x))) p).
    { intros m n []. apply inverse. apply concat_p1. }
    rewrite (H _ _ (nat_plus_comm a 1)). clear H.
    refine (_ @ concat_pp_p _ _ _).
    apply whiskerR.
    refine (lcancel_canon_compose _ _ _ _ @ _). (* simpler proof to just prove this here? *)
    apply moveR_pV. refine ((concat_p1 _)^ @ _). apply whiskerL.
    change idpath with (ap011 BSigma_to_Z
                              (idpath (canon_BSigma (2 + (a + 1))))
                              (idpath (canon_BSigma ((a + 1))))).
    rewrite <- path_BSigma_1.  rewrite <- path_BSigma_1. 
    unfold canon_BSigma_assoc. simpl.
    apply (ap011 (fun f g => ap011 BSigma_to_Z (path_BSigma _ _ f) (path_BSigma _ _ g))).
    +  unfold canon_assoc.
       apply emoveL_eV. apply emoveL_eV.
       apply path_equiv. apply path_arrow.
       intros [[x | x] | [[[]|x] | x]]; reflexivity.
    + unfold canon_assoc.
      apply emoveL_eV. apply emoveL_eV.
      apply path_equiv. apply path_arrow.
      intros [[x | x] | []]; reflexivity.
  Defined.

  (* Definition path_base_2_SS (a : nat) *)
  (*   : BSigma_to_Z (canon_BSigma 2) (canon_BSigma 2) *)
  (*     = BSigma_to_Z (canon_BSigma a.+2) (canon_BSigma a.+2) *)
  (*   := (lcancel_canon _ _ a). *)
  (* Proof. *)
  (*   (* induction a. *) *)
  (*   (* - exact idpath. *) *)
  (*   (* - refine (IHa @ _). *) *)
  (*   (*   refine (lcancel_Z (canon_BSigma 1) _ _ @ _). *) *)
  (*   (*   apply (ap011 BSigma_to_Z); *) *)
  (*   (*     refine (BSigma_symmetric _ _ @ _); apply finsum_id.         *) *)
  (*   apply (path_Z (canon_BSigma a)); apply finsum_id. *)
  (* Defined. *)
    
    (* refine (lcancel_Z (canon_BSigma a) _ _ @ _). *)
    (* apply (ap011 BSigma_to_Z); apply finsum_id. *)
  

  (* Definition path_succ ( a : nat ) *)
  (*   : BSigma_to_Z (canon_BSigma a) (canon_BSigma a) = *)
  (*     BSigma_to_Z (canon_BSigma a.+1) (canon_BSigma a.+1). *)
  (* Proof. *)
  (*   refine (lcancel_canon _ _ 1 @ _). *)
  (*   apply (ap011 BSigma_to_Z); apply (ap canon_BSigma); apply nat_plus_comm. *)
  (*   (* apply (ap011 (fun x y => BSigma_to_Z (canon_BSigma x) (canon_BSigma y))); *) *)
  (*   (*   apply nat_plus_comm. *) *)
  (* Defined. *)
    (* refine (lcancel_Z (canon_BSigma 1) _ _ @ _). *)
    (* apply (path_Z (canon_BSigma 1)); *)
    (*   refine ((finsum_id 1 a) @ _); apply (ap canon_BSigma); apply nat_plus_comm. *)
  (*     (* refine (BSigma_symmetric _ _ @ _); apply finsum_id. *) *)
  (*   (* apply ccleq. *) *)
  (*   (* exists (canon_BSigma 1). simpl. *) *)
  (*   (* apply path_prod; *) *)
  (* Defined. *)

(*   Definition path_Z_bc {S S' : BSigma} {A1 B1 A2 B2 : BSigma} *)
(*              (p : sum_BSigma S A1 = A2) (q : sum_BSigma S B1 = B2) *)
(*              (h : S' = S) *)
(*     : path_Z S p q = path_Z S' (ap011 sum_BSigma h idpath @ p) *)
(*                                (ap011 sum_BSigma h idpath @ q). *)
(*   Proof. *)
(*     destruct h. *)
(*     rewrite concat_1p. rewrite concat_1p. *)
(*     reflexivity. *)
(*   Defined. *)

(*   Definition path_base_2_succ (a : nat) *)
(*     : path_base_2_SS a.+1 = *)
(*       path_base_2_SS a @ (path_succ _). *)
(*   Proof.     *)
(*     unfold path_base_2_SS. unfold path_succ. *)
(*     unfold lcancel_canon. (* refine (_ @ concat_pp_p _ _ _). *) *)
(*     (* refine (_ @ whiskerR (path_Z_compose _ _ _ _ _ _)^ _). *) *)
(*     refine (_ @ (path_Z_compose _ _ _ _ _ _)^). *)
    
(*     refine (path_Z_bc _ _ (* (BSigma_symmetric _ _ @ finsum_id a 1 ) @ _). *) *)
(*                       (* (finsum_id 1 a @ (ap canon_BSigma (nat_plus_comm _ _))) @ _). *) *)
(*                       ((ap canon_BSigma (nat_plus_comm a 1))) @ _). *)
    
(*     refine (_ @ (path_Z_compose _ _ _ _ _ _)^). *)
(*     unfold path_Z. *)
(*     apply (ap (ccleq group_completion_BSigma)). *)
(*     apply (ap (fun x => (_ ; x))). *)
(*     simpl. unfold functor_prod. simpl. *)
(*     assert (forall (A B : Type) (a a' : A) (b b' : B) (p : a = a') (q : b = b'), *)
(*         path_prod (a,b) (a', b') p q = ap011 pair p q). *)
(*     { intros. destruct p. destruct q. reflexivity. } *)
(*     rewrite X. rewrite X. clear X. *)
    
(*     unfold BSigma_symmetric. unfold finsum_id. *)
(*     repeat rewrite <- path_BSigma_compose. *)
(*     rewrite <- path_BSigma_1. rewrite <- path_BSigma_1.  *)
(*     rewrite <- path_BSigma_sum. rewrite <- path_BSigma_sum.  *)
(*     rewrite <- path_BSigma_compose. *)
(*     rewrite <- path_BSigma_compose. *)
(*     rewrite <- path_BSigma_compose.     *)
(*     apply (ap011 (ap011 pair)); apply (ap (path_BSigma _ _)); *)
(*       apply path_equiv; apply path_arrow. *)
(*     - intro x. *)
(*     intros [[[[] | []] | x] | x]; try reflexivity; simpl. *)
    
(*     apply (ap (path_prod (sum_BSigma (sum_BSigma (canon_BSigma 1) (canon_BSigma a)) (canon_BSigma 2), *)
(*                           sum_BSigma (sum_BSigma (canon_BSigma 1) (canon_BSigma a)) (canon_BSigma 2)) *)
(*                          (canon_BSigma a.+3, canon_BSigma a.+3))). *)
    
(*     apply (ap (path_Z (sum_BSigma (canon_BSigma 1) (canon_BSigma a)))). *)

    
(*     transitivity (path_Z (sum_BSigma (canon_BSigma a) (canon_BSigma 1)) _)     *)
    
    

(* rewrite <- path_BSigma_compose. *)
    
(*     unfold path_Z. *)
    
(*     refine (_ @ cconcat _ _ _). simpl. *)
(*     apply (ap (ccleq _)). *)
(*     apply inverse. *)
(*     srapply @path_sigma. *)
(*     { simpl. apply (BSigma_symmetric _ _ @ finsum_id a 1). } *)
(*     simpl. *)
                         
(*     apply (path_sigma _ _ _ (finsum_id _ _)). *)

    
(*     apply inverse. *)
    
(*     refine ( *)
      
(*       lcancel_Z (canon_BSigma a) _ _ @ (ap011 BSigma_to_Z (finsum_id _ _) (finsum_id _ _)). *)
(*   Proof. *)
(*     induction a. *)
(*     { simpl. *)
      
(*       unfold lcancel_Z. *)
(*       rewrite <- (ce group_completion_BSigma). *)
(*       refine ((concat_p1 _)^ @ _). *)
(*       apply concat2. *)
(*       unfold finsum_id. simpl. *)
      

(*   Definition path_base_2 (a : nat) *)
(*     : BSigma_to_Z (canon_BSigma 2) (canon_BSigma 2) = BSigma_to_Z (canon_BSigma a) (canon_BSigma a). *)
(*   Proof. *)
(*     destruct a as [ | a]. *)
(*     { apply inverse. *)
(*       refine (lcancel_Z (canon_BSigma 2) _ _ @ _). *)
(*       apply (ap011 (BSigma_to_Z)); apply finsum_id. } *)
(*     destruct a as [ | a]. *)
(*     { apply inverse. *)
(*       refine (lcancel_Z (canon_BSigma 1) _ _ @ _). *)
(*       apply (ap011 (BSigma_to_Z)); apply finsum_id. } *)
(*     apply path_base_2_SS. *)
(*   Defined. *)
  
    (* := (path_base_0 _)^ @ (path_base_0 _). *)    

    Definition twist2_Z : BSigma_to_Z (canon_BSigma 2) (canon_BSigma 0) =
                          BSigma_to_Z (canon_BSigma 2) (canon_BSigma 0).
  Proof.
    apply (ap011 BSigma_to_Z).
    - exact (path_BSigma (canon_BSigma 2) (canon_BSigma 2) twist2).
    - exact idpath.
  Defined.

  Definition transpose_Z (a : nat) (i : Fin (a.+1))
    : BSigma_to_Z (canon_BSigma (a.+2)) (canon_BSigma (a)) =
      BSigma_to_Z (canon_BSigma (a.+2)) (canon_BSigma (a)).
    apply (ap011 BSigma_to_Z).
    - apply path_BSigma.
      apply (fin_transpose_last_with (a.+1) (inl i)).
    - exact idpath.
  Defined.
  
  Definition transpose_last_two_is_twist_Z (a : nat)
        : ap011
            BSigma_to_Z
            (path_BSigma (canon_BSigma a.+2) (canon_BSigma a.+2) (fin_transpose_last_two a)) 1 =
          (* transpose_Z a (inr tt) = *)
          ((path_base_2 _)^ @ twist2_Z) @ path_base_2 _.
  Proof.
    simpl.
    rewrite transpose_last_two_is_block_sum.
    rewrite <- path_BSigma_1.
    rewrite (ap (path_BSigma (canon_BSigma a) (canon_BSigma a)) (block_sum_is_id a 0)).
    unfold block_sum.
    rewrite (path_BSigma_compose (B := sum_BSigma (canon_BSigma a) (canon_BSigma 2))).
    rewrite (path_BSigma_compose (B := sum_BSigma (canon_BSigma a) (canon_BSigma 2))).
    rewrite (path_BSigma_compose (B := sum_BSigma (canon_BSigma a) (canon_BSigma 0))).
    rewrite (path_BSigma_compose (B := sum_BSigma (canon_BSigma a) (canon_BSigma 0))).
    rewrite ap011_pp_pp. rewrite ap011_pp_pp.
    (* unfold path_to_base_2. unfold lcancel_Z. *)
    rewrite <- path_BSigma_V.
    (* rewrite <- path_BSigma_V. *)
    change (path_BSigma
              (sum_BSigma (canon_BSigma a) (canon_BSigma 2))
              (canon_BSigma (a.+2)) (equiv_finsum a 2)) with (finsum_id a 2).
    (* assert (H : forall (A : BSigma) (p : A = (canon_BSigma a.+2)), *)
    (*            path_base_2 (canon_BSigma a.+2) = *)
    (*            path_base_2 A @ (ap011 BSigma_to_Z p p)). *)
    (* { intros A []. rewrite concat_p1. reflexivity. } *)
    (* rewrite (H _ (finsum_id a 2)). clear H. *)
    
     unfold path_base_2_SS.
    rewrite inv_pp.
    rewrite <- ap011_VV.    
    repeat refine (_ @ concat_p_pp _ _ _). 
    apply whiskerL.
    repeat refine (_ @ concat_pp_p _ _ _). apply whiskerR.
    unfold twist2_Z.
    rewrite (path_BSigma_sum (canon_BSigma a) (canon_BSigma 2)).
    rewrite (path_BSigma_sum (canon_BSigma a) (canon_BSigma 2)).
    
    rewrite path_BSigma_1. rewrite path_BSigma_1. 
    change (ap011 sum_BSigma (idpath (canon_BSigma a)) (idpath (canon_BSigma 2)))
    with (idpath (sum_BSigma (canon_BSigma a) (canon_BSigma 2))).
    destruct (path_BSigma (canon_BSigma 2) (canon_BSigma 2) twist2).
    rewrite concat_p1. rewrite concat_Vp. reflexivity.
  Qed.

  (* Definition add1_BSigma : BSigma -> BSigma *)
  (*   := fun A => fin_to_BSigma (add_one A). *)
  
  (* Definition path_BSigma_sum_succ (a b : nat) (f : canon_BSigma a <~> canon_BSigma b) *)
  (*   : path_BSigma (canon_BSigma a.+1) (canon_BSigma b.+1) (f +E 1) = *)
  (*     ap add1_BSigma (path_BSigma _ _ f). *)
             

  Definition transpose_is_twist_Z (a : nat) (i : Fin (a.+1))
    : transpose_Z a i =
      (path_base_2 (a.+2))^ @ twist2_Z @ (path_base_2 (a.+2)).
  Proof.
    unfold transpose_Z. simpl. 
    destruct i as [i | []].
    - simpl.
      rewrite (path_BSigma_compose (B := canon_BSigma a.+2)).
      rewrite (path_BSigma_compose (B:= canon_BSigma a.+2)).      
      rewrite (ap011_pp_pp BSigma_to_Z _ _ idpath idpath).
      rewrite (ap011_pp_pp BSigma_to_Z _ _ idpath idpath).
      refine (whiskerR (transpose_last_two_is_twist_Z a) _ @ _).
      refine (whiskerL _ (whiskerL _ (transpose_last_two_is_twist_Z a)) @ _). simpl.
      refine (concat_p_pp _ _ _ @ _).
      refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      refine (concat_pp_p _ _ _ @ _).
      refine (concat_pp_p _ _ _ @ _).
      refine (concat_pp_p _ _ _ @ _). apply whiskerL.
      assert (twist2_Z @ twist2_Z = idpath).
      { unfold twist2_Z.
        rewrite <- ap011_pp_pp.
        rewrite <- path_BSigma_compose.
        assert (twist2 oE twist2 = equiv_idmap).
        { apply path_equiv. apply path_arrow.
          intros [[[] | []] | []]; reflexivity. } rewrite X. clear X.
        rewrite path_BSigma_1. reflexivity. }
      refine (_ @ (concat_p1 _)).
      rewrite <- X. clear X.
      apply whiskerL.
      refine (concat_p_pp _ _ _ @ _).
      refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      
      
      apply moveR_pV. apply moveR_Mp.
      
      
      induction a. { destruct i. }
                   
                   
      destruct i as [i | []].
      + refine (_ @ IHa i).
        simpl.       change (fin_transpose_last_two a oE (fin_transpose_last_with a (inl i) +E 1)
         oE fin_transpose_last_two a )
             with (fin_transpose_last_with (a.+1) (inl (inl i))).

        admit.
      + simpl.

        transpose_last_two_is_twist_Z
      
      unfold transpose_Z. simpl. 
      rewrite (path_BSigma_compose (B := canon_BSigma a.+3)).
      rewrite (path_BSigma_compose (B:= canon_BSigma a.+3)).      
      rewrite (ap011_pp_pp BSigma_to_Z _ _ idpath idpath).
      rewrite (ap011_pp_pp BSigma_to_Z _ _ idpath idpath).
      refine (whiskerR (transpose_last_two_is_twist_Z a.+1) _ @ _).
      refine (whiskerL _ (whiskerL _ (transpose_last_two_is_twist_Z a.+1)) @ _).
      refine (concat_p_pp _ _ _ @ _).
      refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      refine (concat_pp_p _ _ _ @ _).
      refine (concat_pp_p _ _ _ @ _).
      refine (concat_pp_p _ _ _ @ _). apply whiskerL.
      assert (twist2_Z @ twist2_Z = idpath).
      { unfold twist2_Z.
        rewrite <- ap011_pp_pp.
        rewrite <- path_BSigma_compose.
        assert (twist2 oE twist2 = equiv_idmap).
        { apply path_equiv. apply path_arrow.
          intros [[[] | []] | []]; reflexivity. } rewrite X. clear X.
        rewrite path_BSigma_1. reflexivity. }
      refine (_ @ (concat_p1 _)).
      rewrite <- X. clear X.
      apply whiskerL.
      refine (concat_p_pp _ _ _ @ _).
      refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      refine (_ @ moveR_Mp _ _ _ (moveR_pV _ _ _(IHa i))).
      simpl.
      change (fin_transpose_last_two a oE (fin_transpose_last_with a (inl i) +E 1)
         oE fin_transpose_last_two a )
             with (fin_transpose_last_with (a.+1) (inl (inl i))).
      rewrite (path_BSigma_sum)
      apply whiskerR.
      
      admit.
      + unfold transpose_Z. simpl.                   
                   
      unfold transpose_Z. simpl.
    induction a.
    { destruct i as [[] | []]. simpl.
    

  
  (* Definition path_card_0_sum {a b : nat} (A : Finite_Types a) (B : Finite_Types b) *)
  (*   : path_card_0 (sum_finite_types A B) = *)
  (*     path_card_0 B @ lcancel_Z A B B. *)
  (* Proof. *)
  (*   unfold path_card_0. *)

  (* Definition twist2_Z : Fin_to_Z (canon 2) (canon 2) = Fin_to_Z (canon 2) (canon 2). *)
  (* Proof. *)
  (*   apply (ap (fun x : Finite_Types 2 => Fin_to_Z x (canon 2))). *)
  (*   exact (path_finite_types _ (canon 2) (canon 2) twist2). *)
  (* Defined. *)

  (* Definition twist2_Z0 : Fin_to_Z (canon 0) (canon 0) = Fin_to_Z (canon 0) (canon 0) *)
  (*   := path_card_0 (canon 2) @ twist2_Z @ (path_card_0 (canon 2))^. *)

  (* (* A path that is a transposition on the left side and the identity on the right side *) *)
  (* Definition transpose_Z (a : nat) (i : Fin (a)) *)
  (*   : Fin_to_Z (canon (1 + a)) (canon (1 + a)) = Fin_to_Z (canon (1 + a)) (canon (1 +a)). *)
  (*   (* use ap011 to make this easier down below. . . *) *)
  (*   apply (ap011 Fin_to_Z). *)
  (*   - apply path_finite_types. *)
  (*     apply (fin_transpose_last_with (a)). exact (inl i). *)
  (*   - exact idpath.             (*  *) *)
  (* Defined. *)


  (* Definition transpose_last_two_is_twist2_Z0 (a : nat) *)
  (*   : (* ap (fun x : Finite_Types a.+2 => Fin_to_Z x (canon a.+2)) *) *)
  (*     ap011 Fin_to_Z *)
  (*           (path_finite_types a.+2 (canon a.+2) (canon a.+2) (fin_transpose_last_two a)) idpath = *)
  (*     ((path_card_0 (canon a.+2))^ @ twist2_Z0) @ path_card_0 (canon a.+2). *)
  (* Proof. *)
  (*   rewrite transpose_last_two_is_block_sum. *)
  (*   rewrite <- path_finite_types_id. *)
  (*   rewrite (block_sum_is_id a 2). *)
  (*   unfold block_sum. *)
  (*   rewrite (path_finite_types_compose (a.+2) _ (sum_finite_types (canon a) (canon 2))). *)
  (*   rewrite (path_finite_types_compose (a.+2) _ (sum_finite_types (canon a) (canon 2))). *)
  (*   rewrite (path_finite_types_compose (a.+2) _ (sum_finite_types (canon a) (canon 2))). *)
  (*   rewrite (path_finite_types_compose (a.+2) _ (sum_finite_types (canon a) (canon 2))). *)
  (*   rewrite path_finite_types_V. *)
  (*   change *)
  (*     (path_finite_types a.+2 (sum_finite_types (canon a) (canon 2)) (canon a.+2) (equiv_finsum a 2)) *)
  (*     with *)
  (*     (finsum_id a 2). *)
    
  (*   assert (H : forall (A A' : Finite_Types (a.+2)) (p : A = A'), *)
  (*              path_card_0 A' = *)
  (*              path_card_0 A @ (ap011 Fin_to_Z p p)). *)
  (*   { destruct p. apply inverse. apply concat_p1. } *)
  (*   rewrite (H _ _ (finsum_id a 2)). clear H. *)
    

  (*   rewrite (ap011_pp_pp Fin_to_Z _ _ _ _). *)
  (*   rewrite (ap011_pp_pp Fin_to_Z _ _ _ _). *)
  (*   rewrite inv_pp. *)
  (*   repeat refine (concat_p_pp _ _ _ @ _). *)
  (*   refine (_ @ concat_pp_p _ _ _). apply whiskerR. *)
  (*   refine (_ @ concat_p_pp _ _ _). *)
  (*   refine (_ @ concat_p_pp _ _ _). *)
  (*   apply concat2. *)
  (*   { apply inverse. apply ap011_VV. } *)
  (*   unfold twist2_Z0. unfold path_card_0. *)

  (*   apply whiskerR. *)
  (*   repeat rewrite concat_p_pp. apply whiskerR. *)
  (*   repeat rewrite concat_pp_p. apply whiskerL. *)
    

  (*   reflexivity. *)
  (*     change (a.+2) with (1 + (1 + a))%nat. unfold canon. *)
  (*     apply path_sigma_hprop. simpl. *)
  (*     rewrite <- (nat_lemmas.plus_assoc 1 1 a). *)
  (*     unfold canon. apply (ap (fun x : nat => (Fin x; tr 1))). *)
  (*     apply (ap (fun a : nat => canon a)). *)
  (*   rewrite (H (sum_finite_types (canon a) (canon 2)) *)

  (* Definition transpose_is_twist_Z (a : nat) (i : Fin a) *)
  (*   : transpose_Z a i = *)
  (*     (path_card_0 _)^ @ twist2_Z0 @ (path_card_0 _). *)
  (* Proof. *)
  (*   induction a. *)
  (*   {destruct i. } *)
  (*   simpl. *)
  (*   unfold transpose_Z. simpl. destruct i as [i | []]; simpl. *)
  (*   - admit. *)
  (*   -  unfold twist2_Z0. rewrite transpose_last_two_is_block_sum. *)
  (*     unfold block_sum. *)
      
  (*     unfold twist2_Z. *)
      
  (*     refine (ap (fun y : (Fin 2) <~> (Fin 2) => *)
  (*                   ap (fun x : Finite_Types a.+2 => Fin_to_Z x (canon a.+2)) *)
  (*                      (path_finite_types a.+2 (canon a.+2) (canon a.+2) (block_sum equiv_idmap y))) *)
  (*                (eissect (equiv_path_finite_types 2 (canon 2) (canon 2)) twist2)^ @ _). *)
  (*     simpl. *)
  (*     refine (ap (fun y : (Fin a) <~> (Fin a) => *)
  (*                   ap (fun x : Finite_Types a.+2 => Fin_to_Z x (canon a.+2)) *)
  (*                      (path_finite_types a.+2 (canon a.+2) (canon a.+2) *)
  (*                           (block_sum *)
  (*                              y *)
  (*                              (inv_path_finite_types 2 (canon 2) (canon 2) *)
  (*                                                     (path_finite_types 2 (canon 2) (canon 2) *)
  (*                                                                        twist2))))) *)
  (*                (eissect (equiv_path_finite_types a (canon a) (canon a)) equiv_idmap)^ @ _). *)
  (*     simpl. *)
  (*     rewrite blocksum_is_ap011. *)
  (*     rewrite path_finite_types_id. *)
  (*     change (pft_inv ?x) with ((equiv_path_finite_types (a.+2) (canon _) (canon _))^-1 x). *)
  (*     change (path_finite_types ?x ?y ?y ?z) with (equiv_path_finite_types x y y z). *)
  (*     rewrite (eisretr (equiv_path_finite_types (a.+2) (canon _) (canon _)) (sum_finite_types_canon^ @ *)
  (*          (ap011 sum_finite_types 1 (path_finite_types 2 (canon 2) (canon 2) twist2) @ *)
  (*           sum_finite_types_canon))). *)
                 
  (*     destruct (path_finite_types 2 (canon 2) (canon 2) twist2). *)
      
  (*     rewrite (eissect (equiv_path_finite_types 2 (canon 2) (canon 2)) twist2) *)

  (*     unfold fin_transpose_last_two. *)
  (*   assert *)
  (*     (fin_transpose_last_with a.+1 (inl i) = *)
  (*      (fin_transpose_last_two a oE (fin_transpose_last_with a i +E equiv_idmap) oE *)
  (*                              (fin_transpose_last_two a))). *)
  (*   { destruct i as [i | []]; try reflexivity. *)
  (*     simpl. *)
      

                 


  

  
  (* ________ *)
    
  (* Definition path_card_2 {a : nat} (A : Finite_Types a) *)
  (* :  Fin_to_Z (canon 2) (canon 0) = Fin_to_Z (sum_finite_types A (canon 2)) A. *)
  (* Proof. *)
  (*   refine (lcancel_Z A (canon 2) (canon 0) @ _). *)
  (*   apply (ap (Fin_to_Z (sum_finite_types A (canon 2)))). *)
  (*   apply path_finite_types. apply sum_empty_r. (* make its own lemma? *) *)
  (* Defined. *)

  Definition path_to_base_2 (a : nat)
    :  BSigma_to_Z (canon_BSigma 2) (canon_BSigma 0) =
       BSigma_to_Z (canon_BSigma (2 + a)) (canon_BSigma a) .
  Proof.
    refine (lcancel_Z (canon_BSigma a) (canon_BSigma 2) (canon_BSigma 0) @ _).
    apply (ap011 BSigma_to_Z); apply finsum_id.
  Defined.

  Definition path_to_base_succ (a : nat)
    : BSigma_to_Z (canon_BSigma (3 + a)) (canon_BSigma (1 + a)) =
      BSigma_to_Z (canon_BSigma (2 + a)) (canon_BSigma a)
    := (path_to_base_2 (a.+1))^ @ path_to_base_2 a.
    
  
  (* Definition succ_is_sum_BSigma (a : nat) *)
  (*   :  sum_BSigma (canon_BSigma 1) (canon_BSigma a) = canon_BSigma (a.+1). *)
  (* Proof. *)
  (*   refine (_ @ finsum_id a 1). *)
  (*   apply BSigma_symmetric. *)
  (* Defined. *)

  (* Definition lcancel_succ (a b : nat) *)
  (*   : BSigma_to_Z (canon_BSigma a) (canon_BSigma b) = *)
  (*     BSigma_to_Z (canon_BSigma a.+1) (canon_BSigma b.+1). *)
  (*            (* {a b : nat} (A : Finite_Types a) (B : Finite_Types b) *) *)
  (*   (* : Fin_to_Z A B = Fin_to_Z (add_one A) (add_one B). *) *)
  (* Proof. *)
    
  (*   refine (lcancel_Z (canon_BSigma 1) _ _ @ _). *)
  (*   refine ((ap011 BSigma_to_Z (succ_is_sum_BSigma a) (succ_is_sum_BSigma b))). *)
  (* Defined. *)

    
  (* Definition path_to_base_2_succ (a : nat) *)
  (*   : path_to_base_2 (a.+1) = path_to_base_2 a @ (lcancel_succ (a.+2) a). *)
  (* Proof. *)
  (*   unfold path_to_base_2. unfold lcancel_succ. *)
  (*   apply moveR_pM.  *)
  (*   refine (_ @ lcancel_Z_compose (canon_BSigma 1) (canon_BSigma a) (canon_BSigma 2) (canon_BSigma 0) *)
  (*             @ _). *)
  (*   unfold lcancel_Z. *)
  (*   change {| card_BSigma := ?x; fintype_of_BSigma := canon ?x |} with *)
  (*   (canon_BSigma x). *)
    
    
    
    
  (*   cconcat *)

  Definition twist2_Z : BSigma_to_Z (canon_BSigma 2) (canon_BSigma 0) = BSigma_to_Z (canon_BSigma 2) (canon_BSigma 0).
  Proof.
    apply (ap011 BSigma_to_Z).
    - exact (path_BSigma (canon_BSigma 2) (canon_BSigma 2) twist2).
    - exact idpath.
  Defined.

  Definition transpose_Z (a : nat) (i : Fin (a.+1))
    : BSigma_to_Z (canon_BSigma (a.+2)) (canon_BSigma a) =
      BSigma_to_Z (canon_BSigma (a.+2)) (canon_BSigma a).
    apply (ap011 BSigma_to_Z).
    - apply path_BSigma.
      apply (fin_transpose_last_with (a.+1) (inl i)).
    - exact idpath.
  Defined.
  
  Definition transpose_last_two_is_twist_Z (a : nat)
        : (* ap011 *)
          (*   BSigma_to_Z *)
          (*   (path_BSigma (canon_BSigma a.+2) (canon_BSigma a.+2) (fin_transpose_last_two a)) 1 = *)
          transpose_Z a (inr tt) =
          ((path_to_base_2 a)^ @ twist2_Z) @ path_to_base_2 a.
  Proof.
    unfold transpose_Z. simpl.
    rewrite transpose_last_two_is_block_sum.
    rewrite <- path_BSigma_1.
    rewrite (ap (path_BSigma (canon_BSigma a) (canon_BSigma a)) (block_sum_is_id a 0)).
    unfold block_sum.
    rewrite (path_BSigma_compose (B := sum_BSigma (canon_BSigma a) (canon_BSigma 2))).
    rewrite (path_BSigma_compose (B := sum_BSigma (canon_BSigma a) (canon_BSigma 2))).
    rewrite (path_BSigma_compose (B := sum_BSigma (canon_BSigma a) (canon_BSigma 0))).
    rewrite (path_BSigma_compose (B := sum_BSigma (canon_BSigma a) (canon_BSigma 0))).
    rewrite ap011_pp_pp. rewrite ap011_pp_pp.
    (* unfold path_to_base_2. unfold lcancel_Z. *)
    rewrite <- path_BSigma_V.
    rewrite <- path_BSigma_V.
    change (path_BSigma
              (sum_BSigma (canon_BSigma a) (canon_BSigma (0)))
              (canon_BSigma (a)) (equiv_finsum a 0)) with (finsum_id a 0).
    change (path_BSigma
              (sum_BSigma (canon_BSigma a) (canon_BSigma (2)))
              (canon_BSigma (a.+2)) (equiv_finsum a 2)) with (finsum_id a 2).
    unfold path_to_base_2.
    rewrite inv_pp.
    rewrite <- ap011_VV. 
    repeat refine (_ @ concat_p_pp _ _ _). 
    apply whiskerL.
    repeat refine (_ @ concat_pp_p _ _ _). apply whiskerR.
    unfold twist2_Z.
    rewrite (path_BSigma_sum (canon_BSigma a) (canon_BSigma 2)).
    rewrite (path_BSigma_sum (canon_BSigma a) (canon_BSigma 0)).
    rewrite path_BSigma_1. rewrite path_BSigma_1.
    change (ap011 sum_BSigma (idpath (canon_BSigma a)) (idpath (canon_BSigma 0)))
    with (idpath (sum_BSigma (canon_BSigma a) (canon_BSigma 0))).
    destruct (path_BSigma (canon_BSigma 2) (canon_BSigma 2) twist2).
    rewrite concat_p1. rewrite concat_Vp. reflexivity.
  Qed.    

  Fixpoint transpose_is_twist_Z (a : nat) (i : Fin (a.+1))
    : transpose_Z a i =
      (path_to_base_2 a)^ @ twist2_Z @ (path_to_base_2 a).
  Proof.
    destruct i as [i | []].
    - induction a. {destruct i. }
      destruct i as [i | []].
      +  
      
      unfold transpose_Z. simpl. 
      rewrite (path_BSigma_compose (B := canon_BSigma a.+3)).
      rewrite (path_BSigma_compose (B:= canon_BSigma a.+3)).      
      rewrite (ap011_pp_pp BSigma_to_Z _ _ idpath idpath).
      rewrite (ap011_pp_pp BSigma_to_Z _ _ idpath idpath).
      refine (whiskerR (transpose_last_two_is_twist_Z a.+1) _ @ _).
      refine (whiskerL _ (whiskerL _ (transpose_last_two_is_twist_Z a.+1)) @ _).
      refine (concat_p_pp _ _ _ @ _).
      refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      refine (concat_pp_p _ _ _ @ _).
      refine (concat_pp_p _ _ _ @ _).
      refine (concat_pp_p _ _ _ @ _). apply whiskerL.
      assert (twist2_Z @ twist2_Z = idpath).
      { unfold twist2_Z.
        rewrite <- ap011_pp_pp.
        rewrite <- path_BSigma_compose.
        assert (twist2 oE twist2 = equiv_idmap).
        { apply path_equiv. apply path_arrow.
          intros [[[] | []] | []]; reflexivity. } rewrite X. clear X.
        rewrite path_BSigma_1. reflexivity. }
      refine (_ @ (concat_p1 _)).
      rewrite <- X. clear X.
      apply whiskerL.
      refine (concat_p_pp _ _ _ @ _).
      refine (concat_p_pp _ _ _ @ _). apply whiskerR.
      refine (_ @ moveR_Mp _ _ _ (moveR_pV _ _ _(IHa i))).
      
      admit.
      + unfold transpose_Z. simpl.
      Check 
      refine (_ @


      
      unfold path_to_base_2.
      apply whiskerR.
      
        apply (ap 
      
            refine (concat_p_pp _ _ _ @ _).
      
      
      
      repeat rewrite concat_p_pp.
      
      rewrite (transpose_is_twist_Z a (inl i)).
      
      
      
      
    - apply transpose_last_two_is_twist_Z.
      
      
      

  
  
  
  
    





