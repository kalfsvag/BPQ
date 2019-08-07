Require Import HoTT.

(* Print LoadPath. *)
Add Rec LoadPath "~/Coq-projects/groupoids" as GR.
(* Print LoadPath. *)

From GR Require Import cquot cquot_principles.
From GC Require Import finite_lemmas (* path_finite_types *) monoids_and_groups
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
  : ap (deloop_fin m n f) ω =
    (deloop_fin_canon m n f @ (functor_hom
                              (iso_inv (iso_path_finite_types m m))
                              (iso_path_finite_types n n) f) ω)
      @ (deloop_fin_canon m n f)^.
Proof.
  apply deloop_rec_beta_loop'.
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

Local Definition Z := cquot (group_completion_BSigma).

Local Definition pft {m : nat}
  := path_finite_types_fix m.

Local Definition pft_inv {m : nat} {A B}
  := inv_path_finite_types_fix m A B.

Section GrpCompl_To_Fin2.
  Definition grpcompl_to_fin2 : Z -> Finite_Types 2.
  Proof.
    srapply @cquot_rec.
    - simpl.
      intros [[a1 A1] [a2 A2]].
      exact (BDet (a2 + a1) (sum_finite_types A1 A2)).
    - intros [[a1 A1] [a2 A2]] B [[s S] p]. simpl in *. destruct p. simpl.
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
        unfold BDet.
        transitivity (canon 2).
        * refine (_ @ (deloop_fin_canon (a2 + a1) 2 (dethom _))).
          apply (ap (BDet (a2 + a1)) (sum_finite_types_canon)).
        * apply inverse.
          refine (_ @ (deloop_fin_canon (a2 + s + (a1 + s)) 2 (dethom (a2 + s + (a1 + s))))).
          apply (ap (BDet _)).
          refine (_ @ sum_finite_types_canon).
          apply (ap011 sum_finite_types); apply sum_finite_types_canon.
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
        apply moveL_pV.
        rewrite inv_pp. 
        repeat rewrite <- concat_p_pp.        
        apply moveR_Vp. apply moveR_Mp. apply moveR_Mp.
        transitivity
          (pft (canon 2) (canon 2)
               (determinant _ (block_sum
                                 (pft_inv q)
                                 (pft_inv r)))).
        { transitivity
            (pft (canon 2) (canon 2)
                 (determinant _ (block_sum
                                   (block_sum (pft_inv p) (pft_inv q))
                                   (block_sum (pft_inv p) (pft_inv r))))).
          - admit.
          - apply (ap (pft (canon 2) (canon 2))).
            refine (det_block_sum _ _ @ _).
            refine (ap011 (fun f g => f oE g)
                          (det_block_sum _ _)
                          (det_block_sum _ _) @ _).
            refine (_ @ (det_block_sum _ _)^).
            refine (ap (fun f => determinant a2 (pft_inv r) oE determinant s (pft_inv p)
                                             oE f)
                       (symm_sigma2 _ _) @ _).
            refine (ecompose_ee_e _ _ _ @ _).
            apply (ap (fun f => determinant a2 (pft_inv r) oE f)).
            refine ((ecompose_ee_e _ _ _)^ @ _).
            refine (_ @ ecompose_1e _).
            apply (ap (fun f => f oE determinant a1 (pft_inv q))).
            generalize (determinant s (pft_inv p)). intro e.
            admit. } 
        

            
          
                                   
                 
        
        
        
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





Section BSigma_set_ind.
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

Local Open Scope nat_scope.

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
      unfold point. unfold ispointed_finite_types.
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
                        (ccl group_completion_BSigma ((m + s; fst ab), (n + s; snd ab))))
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

      
      

  
  
  
  
    



Definition Tr1