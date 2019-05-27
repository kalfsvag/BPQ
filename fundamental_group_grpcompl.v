Require Import HoTT.
Print LoadPath.
Add Rec LoadPath "~/Coq-projects/groupoids" as GR.
Print LoadPath.

From GR Require Import cquot cquot_principles.
From GC Require Import finite_lemmas group_complete_1type BSigma delooping.

Local Definition Z := cquot (group_completion_BΣ).


Definition canon_grpclBΣ_sum (m1 m2 n1 n2 : nat) :
                                                    
  ccl (group_completion_BΣ)
      (functor_prod (plus_BΣ (canon_BΣ m1)) (plus_BΣ (canon_BΣ m2)) (canon_BΣ n1, canon_BΣ n2)) =
  ccl (group_completion_BΣ)
      (canon_BΣ (n1+m1), (canon_BΣ (n2+m2))).
Proof.
  apply (ap (ccl group_completion_BΣ)).
  apply path_prod; simpl;
  apply path_finite_types; apply fin_resp_sum.
Defined.
  
(* The proof that  *)
Definition ccleq_canon (m n s : nat) :
  (ccl (group_completion_BΣ) ((canon_BΣ m), (canon_BΣ n))) =
  (ccl (group_completion_BΣ) ((canon_BΣ (m+s)), (canon_BΣ (n+s)))) :=
  (ccleq group_completion_BΣ ((s; canon s); idpath)) @ canon_grpclBΣ_sum s s m n. 

Definition grp_compl_BΣ_ind_set
           (P : Z -> hSet)
           (f : forall (m n : nat), P (ccl (group_completion_BΣ) ((canon_BΣ m), (canon_BΣ n))))
           (act_r :
              forall (m n : nat) (σ : canon n = canon n),
                transport
                  (fun x : (Finite_Types n) =>
                     P (ccl (group_completion_BΣ) ((canon_BΣ m), (n; x)))) σ (f m n) = (f m n))
           (act_l :
              forall (m n : nat) (σ : canon m = canon m),
                transport
                  (fun x : (Finite_Types m) =>
                     P (ccl (group_completion_BΣ) ((m; x), (canon_BΣ n)))) σ (f m n) = (f m n))
           (act_add :
              forall (m n : nat) (s : nat),
                transport P
                          (ccleq_canon m n s)
                          (f m n) =
                f (m+s)%nat (n+s)%nat)
                
           : forall z : Z, P z.
  Proof.
    srapply @cquot_ind_set.
    - simpl.
      intros [[m x] [n y]]. revert x y.
      srefine (deloop_double_ind_set
               (Finite_Types m) (canon m) (isconn_finite_types m)
               (Finite_Types n) (canon n) (isconn_finite_types n)
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
               (Finite_Types n) (canon n) (isconn_finite_types n)
               _ _).
      revert a1.
      srefine (deloop_ind_prop
               (Finite_Types m) (canon m) (isconn_finite_types m)
               _ _).
      destruct s as [s x]. revert x.
      srefine (deloop_ind_prop
               (Finite_Types s) (canon s) (isconn_finite_types s)
               _ _).
      simpl.
      rewrite deloop_double_ind_set_beta_x0.
      set (h := path_finite_types_fix _
                                      (sum_finite_types (canon s) (canon m)) (canon (m+s))
                                      (fin_resp_sum s m)).
      
      assert ((deloop_double_ind_set (Finite_Types (m + s)) (canon (m + s)) (isconn_finite_types (m + s))
       (Finite_Types (n + s)) (canon (n + s)) (isconn_finite_types (n + s))
       (fun (x1 : Finite_Types (m + s)) (x2 : Finite_Types (n + s)) =>
        P (ccl group_completion_BΣ ((m + s; x1), (n + s; x2)))) (f (m + s) (n + s))
       (fun ω : canon (n + s) = canon (n + s) => act_r (m + s) (n + s) ω) (act_l (m + s) (n + s))
       (sum_finite_types (canon s) (canon m)) (sum_finite_types (canon s) (canon n))) =
              transport (fun x : ) (path_prod (_,_) (_,_) h h)^

      
      set (h := path_finite_types_fix _
                                      (sum_finite_types (canon s) (canon m)) (canon (m+s))
                                      (fin_resp_sum s m)).
      apply path_to_path_over.
      unfold ccleq_canon in act_add. 
      Check
        (transport_pp P (ccleq group_completion_BΣ ((s; canon s); idpath))
                      (canon_grpclBΣ_sum s s m n)
                            (f m n) )^ @ (act_add m n s).
      apply (equiv_inj (equiv_transport (fun x : Z => P x) _ _ (canon_grpclBΣ_sum s s m n))).
      simpl.
      refine ((transport_pp P (ccleq group_completion_BΣ ((s; canon s); idpath))
                      (canon_grpclBΣ_sum s s m n)
                            (f m n) )^ @ _).
      refine (act_add m n s @ _).
      apply inverse.
      refine (_ @deloop_double_ind_set_beta_x0
                (Finite_Types (m + s)) (canon (m + s)) (isconn_finite_types (m + s))
                (Finite_Types (n + s)) (canon (n + s)) (isconn_finite_types (n + s))
                (fun (x1 : Finite_Types (m + s))
                     (x2 : Finite_Types (n + s)) =>
                   P (ccl group_completion_BΣ ((m + s; x1), (n + s; x2)))) (f (m + s) (n + s))
                (fun ω : canon (n + s) = canon (n + s) =>
                   act_r (m + s) (n + s) ω) (act_l (m + s) (n + s)))%nat.
      unfold canon_grpclBΣ_sum.
      refine ((transport_compose P (ccl group_completion_BΣ) _ _)^ @ _).
      refine (transport_path_prod _ _ _ _ @ _). simpl.
      tr
      
      simpl.  
      generalize
      
      transitivity (deloop_do
      

        
      rewrite (transport_pp P (ccleq group_completion_BΣ ((s; canon s); idpath))
                            (ap (ccl group_completion_BΣ)
                                (path_prod (functor_prod
                                              (plus_BΣ (s; canon s)) (plus_BΣ (s; canon s))
                                              (canon_BΣ m, canon_BΣ n))
                                           (canon_BΣ (m + s), canon_BΣ (n + s))
                                           ((path_finite_types
                                               (plus_BΣ (s; canon s) (canon_BΣ m)) (canon_BΣ (m + s)))
                                              (fin_resp_sum s m))
                                           ((path_finite_types
                                               (plus_BΣ (s; canon s) (canon_BΣ n)) (canon_BΣ (n + s)))
                                              (fin_resp_sum s n))))
                            (f m n)

              ) in act_add.
      assert (h : sum_finite_types (canon s) (canon m) = canon (m + s)).
      { apply path_finite_types_fix.
        simpl. apply fin_resp_sum. }
      refine (_ @
                apD011
                (deloop_double_ind_set (Finite_Types (m + s)) (canon (m + s))
                                       (isconn_finite_types (m + s))
                                       (Finite_Types (n + s)) (canon (n + s))
                                       (isconn_finite_types (n + s))
                                       (fun (x1 : Finite_Types (m + s))
                                            (x2 : Finite_Types (n + s)) =>
                                          P (ccl group_completion_BΣ
                                                 ((m + s; x1), (n + s; x2)))) (f (m + s) (n + s))
                                       (fun ω : canon (n + s) = canon (n + s) =>
                                          act_r (m + s) (n + s) ω) (act_l (m + s) (n + s)))%nat
                h h).
      assert (sum_finite_types (canon s) (canon m) = canon (m + s)).
      { apply path_finite_types_fix.
        simpl. apply fin_resp_sum. }
      rewrite X.
        apply path_sigma_hprop. simpl.
        apply path_universe_un.
      rewrite deloop_double_ind_set_beta_x0.
      unfold deloop_double_ind_set. simpl.
      admit.
    
    



Definition Tr1