Require Import HoTT.
Require Import UnivalenceAxiom.

Require Import finite_lemmas.

Section Fin_Transpose.
  Definition fin_transpose {n : nat} (x y : Fin n)
  : Fin n <~> Fin n.
  Proof.
    induction n.
    - destruct x.
    - destruct y as [y | []].
      + destruct x as [x | []].
        * exact (IHn x y +E 1).
        * exact (fin_transpose_last_with n (inl y)).
      + exact (fin_transpose_last_with n x).
  Defined.

  (* Definition fin_transpose_is_withlast_r {n : nat} (x : Fin n.+1) : *)
  (*   fin_transpose x (inr tt) = fin_transpose_last_with n x := idpath. *)

  (* Definition fin_transpose_is_withlast_l {n : nat} (y : Fin n.+1) : *)
  (*   fin_transpose (n := n.+1) (inr tt) y = fin_transpose_last_with n y. *)
  (* Proof. *)
  (*   destruct y as [y | []]; reflexivity. *)
  (* Defined. *)

  Definition fin_transpose_same_is_id {n : nat} (x : Fin n) :
    fin_transpose x x == idmap.
  Proof.
    intro i.
    induction n.
    { destruct x. }
    destruct x as [x | []].
    - simpl. destruct i as [i | []].
      + apply (ap inl). apply IHn.
      + reflexivity.
    - simpl. apply fin_transpose_last_with_last_other.
  Defined.

  Definition fin_transpose_invol {n : nat} (x y : Fin n) :
    fin_transpose x y o fin_transpose x y == idmap.
  Proof.
    induction n.
    {destruct x. }
    intro i. ev_equiv.
    destruct y as [y | []].
    - destruct x as [x | []].
      + simpl. destruct i as [i | []].
        { simpl. apply (ap inl). apply IHn. }
        reflexivity.
      + simpl. apply fin_transpose_last_with_invol.
    - simpl. apply fin_transpose_last_with_invol.
  Defined.

  Definition fin_transpose_sym {n : nat} (x y : Fin n) :
    fin_transpose x y == fin_transpose y x.
  Proof.
    induction n.
    { destruct x. }
    intro i.
    destruct y as [y | []]; destruct x as [x | []]; try reflexivity.
    - simpl. destruct i as [i | []].
      + apply (ap inl). apply IHn.
      + reflexivity.
  Defined.

  Definition fin_transpose_beta_r {n : nat} (x y : Fin n) :
    fin_transpose x y y = x.
  Proof.
    induction n.
    { destruct x. }
    destruct y as [y | []]; destruct x as [x | []]; try (apply fin_transpose_last_with_last).
    - simpl. apply (ap inl). apply IHn.
    - simpl. apply fin_transpose_last_with_with.
  Defined.

  Definition fin_transpose_beta_l {n : nat} (x y : Fin n) :
    fin_transpose x y x = y.
  Proof.
    refine (fin_transpose_sym x y x @ _).
    apply fin_transpose_beta_r.
  Defined.

  Definition fin_transpose_other {n : nat} (x y : Fin n) (i : Fin n):
    (i <> x) -> (i <> y) -> fin_transpose x y i = i.
  Proof.
    intros n_x n_y.
    induction n.
    { destruct x.  }
    destruct y as [y | []].
    - destruct x as [x | []].
      + simpl. destruct i as [i | []].
        * apply (ap inl). apply IHn.
          { intro p. apply n_x. exact (ap inl p). }
          { intro p. apply n_y. exact (ap inl p). }
        * reflexivity.
      + simpl. destruct i as [i | []].
        * apply fin_transpose_last_with_rest.
          intro p. apply n_y. exact p^.
        * destruct (n_x idpath).
    - simpl. destruct i as [i | []].
      + apply fin_transpose_last_with_rest.
        intro p. apply n_x. exact p^.
      + destruct (n_y idpath).
  Defined.

  (* either i = x, i = y, or equal to neither *)
  Definition decompose_fin_n {n : nat} (x y : Fin n) (i : Fin n) :
    (i = x) + (i = y) + ((i <> x) * (i <> y)).
  Proof.
    destruct (decidablepaths_fin n i x).
    - exact (inl (inl p)).
    - destruct (decidablepaths_fin n i y).
      + apply inl. exact (inr p).
      + apply inr. exact (n0, n1).
  Qed.    

  Definition natural_fin_transpose {n : nat} (x y : Fin n) (e : Fin n <~> Fin n) :
    e o (fin_transpose x y) == fin_transpose (e x) (e y) o e.
  Proof.
    intro i. ev_equiv.
    destruct (decompose_fin_n x y i) as [[p | p] |[n_x n_y] ].
    - rewrite p.
      rewrite fin_transpose_beta_l.
      apply inverse. apply fin_transpose_beta_l.
    - rewrite p.
      rewrite fin_transpose_beta_r.
      apply inverse. apply fin_transpose_beta_r.
    - rewrite (fin_transpose_other x y i n_x n_y).
      apply inverse. apply fin_transpose_other.
      + intro p. apply n_x. apply (equiv_inj e p).
      + intro p. apply n_y. apply (equiv_inj e p).
  Qed.

  Definition fin_transpose_eta {n : nat} (x y : Fin n) (e : Fin n -> Fin n) :
    (e x = y) -> (e y = x) -> (forall i : Fin n, i <> x -> i <> y -> e i = i) ->
    fin_transpose x y == e.
  Proof.
    intros p q neq.
    intro i.
    destruct (decidablepaths_fin n i x) as [eq_x | neq_x].
    - rewrite eq_x.
      rewrite p.
      apply fin_transpose_beta_l.
    - destruct (decidablepaths_fin n i y) as [eq_y | neq_y].
      + rewrite eq_y.  rewrite q.
        apply fin_transpose_beta_r.
      + rewrite (neq i neq_x neq_y).
        apply (fin_transpose_other _ _ _ neq_x neq_y).
  Qed.
  
  
End Fin_Transpose.

Section Sigma2.
  Definition sigma2_fixlast (σ : Fin 2 <~> Fin 2) :
    (σ (inr tt) = inr tt) -> σ == equiv_idmap.
  Proof.
    intro p.
    intros [[[] | []] | []]; simpl.
    - recall (σ ((inl (inr tt)))) as x eqn:q.
      rewrite q.
      destruct x as [[[] | []] | []].
      + reflexivity.
      + destruct (inr_ne_inl tt (inr tt) (equiv_inj σ (p @ q^))). (* absurd case *)
    - exact p.
  Qed.

  Definition twist2 : Fin 2 <~> Fin 2 :=
    fin_transpose (n := 2) (inl (inr tt)) (inr tt).

  Definition twist2_inv : equiv_inverse twist2 = twist2.
  Proof.
    apply path_equiv. reflexivity.
  Qed.

  Definition sigma2_notfixlast (σ : Fin 2 <~> Fin 2) :
    (σ (inr tt) = inl (inr tt)) -> σ == twist2.
  Proof.
    intro p.
    intros [[[] | []] | []]; simpl.
    - recall (σ ((inl (inr tt)))) as x eqn:q.
      rewrite q.
      destruct x as [[[] | []] | []].
      + destruct (inr_ne_inl tt (inr tt) (equiv_inj σ (p @ q^))). (* absurd case *)
      + reflexivity.
    - exact p.
  Qed.

  Definition symm_sigma2 (σ1 σ2 : Fin 2 <~> Fin 2) :
    σ1 oE σ2 = σ2 oE σ1.
  Proof.
    recall (σ1 (inr tt)) as x eqn:p.
    destruct x as [[[] | []] | []].
    - rewrite (path_equiv (path_forall _ _ (sigma2_notfixlast σ1 p))).
      recall (σ2 (inr tt)) as y eqn:q.
      destruct y as [[[] | []] | []].
      + rewrite (path_equiv (path_forall _ _ (sigma2_notfixlast σ2 q))).
        reflexivity.
      + rewrite (path_equiv (path_forall _ _ (sigma2_fixlast σ2 q))).
        rewrite ecompose_e1. rewrite ecompose_1e. reflexivity.
    - rewrite (path_equiv (path_forall _ _ (sigma2_fixlast σ1 p))).
      rewrite ecompose_e1. rewrite ecompose_1e. reflexivity.
  Qed.    

End Sigma2.

Section Restrict_Equivalence.
  Context {n : nat}
          {A : Type}
          (e : A + Unit <~> Fin n.+1)
          (fixlast : e (inr tt) = inr tt).

  Lemma not_inr_is_inl {X Y : Type}
        (x :  X + Y)
        (not_inr : forall y : Y, x <> inr y)
    : is_inl x.
  Proof.
    destruct x as [x | y'].
    - exact tt.
    - destruct (not_inr y' idpath).
  Qed.
  
  Lemma fix_last_is_inr :
    forall u : Unit, is_inr (e (inr u)).
  Proof.
    intros []. rewrite fixlast.
    exact tt.
  Qed.

  Lemma fix_last_is_inl :
    forall a : A, is_inl (e (inl a)).
  Proof.
    intro a. apply not_inr_is_inl.
    intros []. rewrite <- fixlast.
    intro q. apply (inl_ne_inr a tt).
    exact (equiv_inj e q).
  Qed.

  Definition equiv_restrict :=
    equiv_unfunctor_sum_l e fix_last_is_inl fix_last_is_inr.

  Definition swap_last := fin_transpose (e (inr tt)) (inr tt).

  Lemma swap_fix_last :
    (swap_last oE e) (inr tt) = inr tt.
  Proof.
    unfold swap_last. ev_equiv. apply fin_transpose_last_with_with.
  Qed.

  
  Definition equiv_restrict_eta :
    equiv_restrict +E equiv_idmap == e.
  Proof.
    intro x.
    refine (_ @ unfunctor_sum_eta _ fix_last_is_inl fix_last_is_inr x).
    destruct x as [x | []]; try reflexivity.   
    simpl.
    destruct (unfunctor_sum_r e fix_last_is_inr tt).
    reflexivity.
  Qed.      
End Restrict_Equivalence.

Definition equiv_restrict_plus1 {n : nat} {A : Type} (e : A <~> Fin n) :
  equiv_restrict (e +E equiv_idmap) idpath == e.
Proof.
  intro a.
  apply (path_sum_inl Unit).
  refine (unfunctor_sum_l_beta _ _ a ).
Qed.

Definition inj_equiv_plus1 {n : nat} {A : Type} (e1 e2 : A <~> Fin n) :
  (e1 +E (equiv_idmap Unit)) == (e2 +E (equiv_idmap Unit)) -> e1 == e2.
Proof.
  intro H.
  intro x.
  apply (path_sum_inl Unit). apply (H (inl x)).
Qed.

Definition fin_decompose_ind {m n : nat} (P : Fin (n+m) -> Type)
           (Pl : forall i : Fin m, P (finl _ _ i))
           (Pr : forall i : Fin n, P (finr _ _ i))
  : forall i : Fin (n+m), P i.
Proof.
  cut (forall j : (Fin m)+(Fin n), P (finsum m n j)).
  - intro f.
    intro i.
    apply (transport P (eisretr (finsum m n) i)).
    exact (f ((finsum m n)^-1 i)).
  - intros [j | j].
    + exact (Pl j).
    + exact (Pr j).
Defined.

Section Block_Sum.
Definition block_sum {m n: nat} (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n) :
  Fin (n+m)%nat <~> Fin (n+m)%nat :=
  (fin_resp_sum m n) oE (e1 +E e2) oE (equiv_inverse (fin_resp_sum m n)).

Definition block_sum_beta_finl {m n : nat} (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n)
           (i : Fin m) :
  block_sum e1 e2 (finl _ _ i) = finl _ _ (e1 i).
Proof.
  unfold block_sum. ev_equiv.
  rewrite (eissect (fin_resp_sum m n) (inl i)). reflexivity.
Qed.

Definition block_sum_beta_finr {m n : nat} (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n)
           (i : Fin n) :
  block_sum e1 e2 (finr _ _ i) = finr _ _ (e2 i).
Proof.
  unfold block_sum. ev_equiv.
  rewrite (eissect (fin_resp_sum m n) (inr i)). reflexivity.
Qed.

Definition block_sum_eta {m n : nat} 
           (e1 : Fin m <~> Fin m) (e2 : Fin n <~> Fin n)
           (g : Fin (n + m) <~> Fin (n + m))
           (eq_l : forall i : Fin m,
               finl _ _(e1 i)
               = g (finl _ _ i))
           (eq_r : forall i : Fin n,
               (finr _ _ (e2 i)
                = g (finr _ _ i)))
  : block_sum e1 e2 == g .
Proof.
  unfold block_sum. intro j. revert j.
  apply fin_decompose_ind.
  - simpl. intro i. rewrite (eissect (fin_resp_sum m n) (inl i)).
    apply eq_l.
  - simpl. intro i. rewrite (eissect (fin_resp_sum m n) (inr i)).
    apply eq_r.
Qed.

Definition block_sum_compose {m n : nat}
           (e1 g1 : Fin m <~> Fin m)
           (e2 g2 : Fin n <~> Fin n) :
  block_sum (e1 oE g1) (e2 oE g2) ==
  (block_sum e1 e2) oE (block_sum g1 g2).
Proof.
  apply block_sum_eta.
  - intro i. ev_equiv.
    rewrite block_sum_beta_finl.
    rewrite block_sum_beta_finl.
    reflexivity.
  - intro i. ev_equiv.
    rewrite block_sum_beta_finr.
    rewrite block_sum_beta_finr.
    reflexivity.
Qed.

Definition block_sum_plus1 {m n : nat}
           (e1 : Fin m <~> Fin m)
           (e2 : Fin n <~> Fin n) :
  block_sum (n := n.+1) e1 (e2 +E (equiv_idmap Unit)) == (block_sum e1 e2) +E (equiv_idmap Unit).
Proof.
  
  apply block_sum_eta.
  - simpl.
    intro i. apply (ap inl).
    rewrite (eissect (finsum m n) (inl i)). reflexivity.
  - simpl. intros [i | []].
    + simpl. rewrite (eissect (finsum m n) (inr i)). reflexivity.
    + reflexivity.
Qed.

End Block_Sum.

Require Import monoids_and_groups.

Definition SymGrp (m : nat) := AutGroup (Fin m).

Section Block_Sum_Hom.
  Open Scope monoid_scope.
  (* Block sum as a homomorphism *)
  Definition block_sum_hom (m n : nat):
    Hom (grp_prod (SymGrp m) (SymGrp n)) (SymGrp (n+m)).
  Proof.
    srapply @Build_Homomorphism.
    - intros [s t].
      exact (block_sum s t).
    - simpl. apply path_equiv. apply path_arrow.
      apply block_sum_eta; reflexivity.
    - simpl. intros [s1 s2] [t1 t2].
      apply path_equiv. apply path_arrow.
      apply block_sum_compose.
  Defined.
End Block_Sum_Hom.