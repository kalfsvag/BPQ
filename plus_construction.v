Require Import HoTT.
Require Import UnivalenceAxiom.
Load stuff.

(* Another notation for pointed maps *)
Notation "X ->* Y" := (pMap (Build_pType X _) (Build_pType Y _)).
Infix "o*" := pmap_compose.
Definition add_pt : Type -> pType :=
  fun X => Build_pType (X + Unit) (inr tt).

(* Definition psusp_rec_beta_unit {X Y : pType} (p : X ->* loops Y) : *)
(*   forall x : X, loops_functor ((loop_susp_adjoint X Y)^-1 p) (loop_susp_unit X x) = p x. *)
(* Proof. *)
(*   intro x. cbn. *)
(*   refine (concat_1p _ @ _). refine (concat_p1 _ @ _). *)

(*   transitivity (ap (Susp_rec North North p *)
(*   refine (ap_compose (Susp_rec North South (fun x1 : X => merid (p x1))) *)
(*                      (Susp_rec (point Y) (point Y) idmap) (merid x @ (merid (point X))^)  @ _). *)
  
  
(*   refine (ap_pp *)
(*             (fun x0 : Susp X => Susp_rec (point Y) (point Y) idmap *)
(*                                          (Susp_rec North South (fun x1 : X => merid (p x1)) x0)) *)
(*             (merid x) *)
(*             (merid (point X))^ @ _). *)
(*   transitivity (p x @ 1). *)
(*   apply concat2. *)
(*   - refine (Susp_rec_beta_merid x @ _). *)
                
  
  
(*     loops_functor ( H_S p) (loop_susp_unit X x) = p x @ (p (point X))^. *)
(* Proof. *)


Definition psusp_rec {X Y : pType} (p : X -> loops Y) :
  psusp X ->* Y
    :=  Build_pMap (psusp X) Y (Susp_rec (point Y) (point Y) p) idpath.

(* Make another less intuitive version which is easier to work with *)
Definition psusp_rec' {X Y : pType} (H_S : Y) (p : X -> point Y = H_S) :
  psusp X ->* Y
  := Build_pMap (psusp X) Y (Susp_rec (point Y) H_S p) idpath.

Definition psusp_rec_beta_unit {X Y : pType} (p : X ->* loops Y) :
  forall x : X, loops_functor (psusp_rec p) (loop_susp_unit X x) = p x.
Proof.
  intro x. refine (concat_1p _ @ _). simpl. refine (concat_p1 _ @ _).
  refine (ap_pp (Susp_rec (point Y) (point Y) p) (merid x) (merid (point X))^ @ _).
  refine (_ @ concat_p1 _).
  apply concat2.
  - apply Susp_rec_beta_merid.
  - refine (ap_V _ _ @ _).
    apply (ap inverse (y:=idpath)).
    refine (_ @ point_eq p).
    apply Susp_rec_beta_merid.
Defined.

Definition psusp_rec_beta_unit' {X Y : pType} (H_S : Y) (p : X -> point Y = H_S) :
  forall x : X, loops_functor (psusp_rec' H_S p) (loop_susp_unit X x) = p x @ (p (point X))^.
Proof.
  intro x. cbn.
  refine (concat_1p _ @ _). refine (concat_p1 _ @ _).
  refine (ap_pp (Susp_rec (point Y) (point Y) p) (merid x) (merid (point X))^ @ _).
  apply concat2.
  - apply Susp_rec_beta_merid.
  - refine (ap_V _ _ @ _).
    apply (ap inverse).
    apply Susp_rec_beta_merid.
Defined.



(* (* This "psusp_rec" should be the same as the inverse in the adjointness proof *) *)
(* Definition eq_psusp_rec_adjoint_inverse {X Y : pType} (p : X ->* loops Y) : *)
(*   (loop_susp_adjoint X Y)^-1 p = psusp_rec p. *)
(* Proof. *)
(*   cbn. *)
(*   apply path_pmap. *)
(*   srapply @Build_pHomotopy. *)
(*   - srapply @Susp_ind; try reflexivity. *)
(*     intro x. refine (transport_paths_FlFr _ _ @ _). rewrite concat_p1. *)
(*     apply moveR_Vp. rewrite concat_p1. *)
(*     unfold psusp_rec. cbn. *)
(*     refine (Susp_rec_beta_merid x @ _). *)
  

  

(* Global Instance ispointed_ptype : IsPointed pType := Build_pType Unit _. *)

(* Definition psusp_ind {X : pType} (P : psusp X -> pType) (H_S : P South) : *)
(*   (forall x : X, transport P (merid x) (point (P North)) = H_S) -> forall y : psusp X, P y. *)
(* Proof. *)
(*   intro merid'. *)
(*   srapply @Susp_ind. *)
(*   - exact (point (P North)). *)
(*   - exact H_S. *)
(*   - exact merid'. *)
(* Defined. *)
  

Definition pconst (X Y : pType) : X ->* Y :=
  Build_pMap X Y (const (point Y)) idpath.

Definition loops_functor_pp {X Y : pType} (f : X ->*Y ) (p q : loops X) :
  loops_functor f (p @ q) = loops_functor f p @ loops_functor f q.
Proof.
  destruct X as [X x0]. destruct Y as [Y y0].
  destruct f as [f ispointed_f].
  cbn in *. destruct ispointed_f.
  cut (forall (x1 x2 : X) (p' : x0 = x1) (q' : x1 = x2),
              1^ @ (ap f (p' @  q') @ 1) = (1^ @ (ap f p' @ 1)) @ (1^ @ (ap f q' @ 1))).
  intro H. apply H. destruct p', q'. reflexivity.
Defined.

Definition loops_functor_V {X Y : pType} (f : X ->* Y) (p : loops X) :
  loops_functor f p^ = (loops_functor f p)^.
Proof.
  destruct X as [X x0]. destruct Y as [Y y0].
  destruct f as [f ispointed_f].
  cbn in *. destruct ispointed_f.
  cut (forall (x1 : X) (p' : x0 = x1),
          1^ @ (ap f p'^ @ 1) = (1^ @ (ap f p' @ 1))^).
  intro H. apply H. destruct p'. reflexivity.
Defined.
  

(* Fixpoint iterated_prod (A : Type) (m : nat) : Type := *)
(*   match m with *)
(*     | O => Unit (* A^0 := 1 *) *)
(*     | m.+1 => (iterated_prod A m) * A (* A^m+1 := A^m * A *) *)
(*   end. *)

(* Fixpoint iterated_concat {A : Type} {a0 : A} {m : nat} : iterated_prod (a0 = a0) m -> a0 = a0 := *)
(*   match m with *)
(*     | O => const idpath       (*  *) *)
(*     | m.+1 => fun p => match p with *)
(*                          (prod, p) => iterated_concat prod @ p *)
(*                        end *)
(*   end. *)

(* Fixpoint iterated_concat {X : pType} (l : list (loops X)) : loops X := *)
(*   match l with *)
(*   | nil => idpath *)
(*   | cons p l => p @ iterated_concat l *)
(*   end. *)

(* Fixpoint functor_list {X Y : Type} (f : X -> Y) (l : list X) : list Y := *)
(*   match l with *)
(*     | nil => nil *)
(*     | cons x l => cons (f x) (functor_list f l) *)
(*   end. *)

(* (* Fixpoint iterated_eComp {A : Type} (l : list (A <~> A)) : A <~> A := *) *)
(* (*   match l with *) *)
(* (*     | nil => equiv_idmap *) *)
(* (*     | cons e l => iterated_eComp l oE e *) *)
(* (*   end. *) *)

(* Definition functor_iterated_concat {X Y : pType} (f : pMap X Y) (l : list (loops X)) : *)
(*   loops_functor f (iterated_concat l) = iterated_concat (functor_list (loops_functor f) l). *)
(* Proof. *)
(*   induction l. *)
(*   - simpl. apply moveR_Vp. exact (concat_1p _ @ (concat_p1 _)^). *)
(*   - simpl. pointed_reduce. *)
(*     rename ispointed_type0 into a0. *)
(*     apply ap_pp. *)
(* Defined. *)
    

  
               
Section Plus_Construction.
  (* Assume that B is a pointed 1-type with perfect loop space *)
  (* This type does probably not exist, but we do this simplification for now. Refinement: the loop space contains a perfect subgroup *)
  Context {B : pType}.
  Context `{IsTrunc 1 B}.
  (* Want: P is a perfect subgroup of loops B *)
  (* Do for now: P is the whole of B *)
  Definition P := loops B.
  
  (* Context {isinP : loops B -> hProp}. *)
  (* Definition P := {b : loops B & isinP b}. Definition PtolB : P -> loops B := pr1. *)
  (* Coercion PtolB : P >-> pointed_type. *)
  (* Todo: Formulate how P is a subgroup of B. *)
  
  (* Context {P : pType}. *)
  (* Context {i : P -> loops B}. *)

  (* Context {inj_i : forall a b : P, i a = i b -> a = b}. *)
  (* Context {id_i : forall a b : P, i *)
  (* Context {supgroup_P : forall a b : P, exists c : P, i a @ i b = i c}. *)
  Context {perfect : forall alpha : P, exists s t : P, alpha = s^ @ t^ @ s @ t}.
  Variable perfect_1 : (idpath; (idpath; idpath)) = perfect idpath.

  (* Definition hprop_perfect : forall alpha : P, IsHProp (exists s t : P, alpha = s^ @ t^ @ s @ t). *)
  (* Proof. *)
  (*   intro alpha. *)
  (*   cut (IsHProp {st : P * P & alpha = (fst st)^ @ (snd st)^ @ (fst st) @ (snd st)}). *)
  (*   { apply trunc_equiv'. *)
  (*     (* Easier to prove directly. . . *) *)
  (*     srapply @equiv_adjointify. *)
  (*     - intros [[s t] p]. exact (s ; (t; p)). *)
  (*     - intros [s [t p]]. exact ((s,t);p). *)
  (*     - intros [s [t p]]. reflexivity. *)
  (*     - intros [[s t] p]. reflexivity. } *)
  (*   apply trunc_sigma'. *)
  (*   - intro a. apply (H (point B) (point B) alpha). *)
  (*   - intros [[s1 t1] p1]. intros [[s2 t2] p2]. cbn. *)
  (*     cut (Contr ((s1 = s2) * (t1 = t2))). *)
  (*     { apply trunc_equiv'. apply (equiv_path_prod (s1, t1) (s2, t2)). }       *)
  (*     apply contr_inhabited_hprop. *)
  (*     { apply (trunc_prod (n := -1)). } *)
  (*     apply pair. *)
  (*     + simpl in *. *)



  (*     +  *)
      
    
  (*   apply trunc_sigma'. *)

  
  (* Context (alpha : loops B). *)
  (* (* Perfect implies that there are elements s,t such that alpha = s@t@s^@t^ *) *)
  (* Variables s t : loops B. *)
  (* Context (perfect : alpha = s @ t @ s^ @ t^). *)
  (* (* Aut E is normally generated by alpha, so s and t are products of conjugates of alpha *) *)
  (* Variables s_list t_list : list (loops B). *)
  (* Context (normally_generated_s : s = iterated_concat (functor_list (fun p : loops B => p^ @ alpha @ p) s_list)). *)
  (* Context (normally_generated_t : t = iterated_concat (functor_list (fun p : loops B => p^ @ alpha @ p) t_list)). *)

  (* Now we should be able to define the plus construction in two steps. *)
  (* 1: Kill all alpha in BAut E *)
  (* 2: Find the correct 2-spheres in this type, and kill them *)

  (* (* The map E <~> E -> loops (BAut E) *) *)
  (* Definition loops_baut : E <~> E -> loops (Build_pType (BAut E) _). *)
  (* Proof. *)
  (*   intro e. apply path_baut. exact e. *)
  (* Defined.   *)


  (* Definition pconst (A B : pType) : pMap A B := *)
  (*   Build_pMap A B (const (point B)) idpath. *)

  (* X1 should be the pushout wedge (alpha : loops B) S1, but that corresponds to Susp ((loops B)_+) *)
  (* Don't need the extra point, as that only adds a path 1 = 1 *)
  Definition susp_P_to_B : psusp (P) ->* B.
  Proof.
    apply (psusp_rec' (point B)). exact (pmap_idmap P).
    (* exact (pmap_compose (loop_susp_counit B) (psusp_functor (pmap_idmap P))). *)
    (* Change this when P is properly defined *)
  Defined.
    
  (* Global Instance ispointed_S1 : IsPointed S1 := base. *)
  (* (* First the map S1 -> B corresponding to alpha *) *)
  (* Definition alpha_map : S1 ->* B. *)
  (* Proof. *)
  (*   srapply @Build_pMap. *)
  (*   - srapply @S1_rec. *)
  (*     (* Basepoint goes to basepoint *) *)
  (*     + exact (point B). *)
  (*     + exact alpha. *)
  (*   - reflexivity. *)
  (* Defined. *)

  (* X1 is the BAut E where we kill this map *)
  Definition X1 := Build_pType (pushout susp_P_to_B (const tt)) (push (inr tt)).
  Definition B_to_X1 : B ->* X1.
    srapply @Build_pMap.
    - exact (push o inl).
    - exact (pp North).
  Defined.

  Definition const_SP_to_X1 : B_to_X1 o* susp_P_to_B = pconst (psusp P) X1.
  Proof.
    apply path_pmap.
    srapply @Build_pHomotopy.
    - exact pp.
    - cbn. exact (concat_p1 _ @ (concat_1p _)^).
  Defined.

  

  (* Now we show that all loops in B are killed in X1 *)
  (* Instead: Use loops_functor, loops_functor_compose *)
  Definition kill_loop (alpha : P) : loops_functor B_to_X1 alpha = idpath.
  Proof.
    transitivity (loops_functor (pconst (psusp P) X1) (loop_susp_unit P alpha)).
    transitivity (loops_functor (B_to_X1 o* susp_P_to_B) (loop_susp_unit P alpha)).
    transitivity (loops_functor B_to_X1 (loops_functor susp_P_to_B (loop_susp_unit P alpha))).
    - apply (ap (loops_functor B_to_X1)).
      apply inverse. unfold susp_P_to_B.
      exact (psusp_rec_beta_unit _ alpha).
    - apply inverse. apply loops_functor_compose.
    - apply (ap (fun f : psusp P ->* X1 =>
             loops_functor f ((loop_susp_unit P) alpha))).
      exact const_SP_to_X1.
    - cbn. refine (concat_1p _ @ concat_p1 _ @ _). exact (ap_const _ _).
  Defined.

  Definition loops_functor_1 {X Y : pType} (f : X ->* Y) : loops_functor f idpath = idpath.
  Proof.
    unfold loops_functor. cbn.
    refine (ap (concat (point_eq f)^) (concat_1p _) @ _). apply concat_Vp.
  Defined.

  (* Definition kill_loop_1 : kill_loop 1 = loops_functor_1 _. *)
  (* Proof. *)
  (*   unfold kill_loop. unfold loops_functor_1. cbn. *)
  (*   unfold const. *)

  Definition loops_functor_VVpp {X Y : pType} (f : X ->* Y) (p q r s : loops X) :
    (loops_functor f) (p^ @ q^ @ r @ s) =
    (loops_functor f p)^ @ (loops_functor f q)^ @ (loops_functor f r) @ (loops_functor f s).
  Proof.
    destruct X as [X x0]. destruct Y as [Y y0]. destruct f as [f pf]. cbn in f, pf, p,q,r,s. cbn. destruct pf.
    cut (forall (x1 x2 x3 x4 : X) (p' : x1 = point X) (q' : x2 = x1) (r' : x2 = x3) (s' : x3 = x4),
            1^ @ (ap f (((p'^ @ q'^) @ r') @ s') @ 1) =
            (((1^ @ (ap f p' @ 1))^ @ (1^ @ (ap f q' @ 1))^) @ (1^ @ (ap f r' @ 1))) @ (1^ @ (ap f s' @ 1))).
    { intro gen. apply gen. }
    intros. path_induction. reflexivity.
  Defined.
            
    

  Definition P_to_loopsloopsX1 : P -> loops (loops X1).
  Proof.
    intro alpha. cbn.
    refine ((kill_loop alpha)^ @ _).
    refine (ap (loops_functor B_to_X1) (perfect alpha).2.2 @ _).
    refine (loops_functor_VVpp _ _ _ _ _ @ _).
    destruct (kill_loop (perfect alpha).1)^.
    destruct (kill_loop (perfect alpha).2.1)^. reflexivity.
  Defined.

  (* Definition P_to_loopsloopsX1_1 : P_to_loopsloopsX1 idpath = idpath. *)
  (* Proof. *)
  (*   unfold P_to_loopsloopsX1. *)
  (*   rewrite perfect_1. cbn. repeat rewrite concat_p1. apply moveR_Vp. *)
  (*   refine (concat_1p _ @ _). *)
  (*   refine (_ @ (concat_p1 _)^). *)
  (*   simpl. generalize (kill_loop 1).  *)
  (*   generalize (loops_functor B_to_X1). *)
    

  (* (* Now we show that s and t are killed in X1 *) *)
  (* Definition kill_s : ap (B_to_X1) s = idpath. *)
  (* Proof. *)
  (*   transitivity (loops_functor B_to_X1 s). *)
  (*   { simpl. *)
  (*     admit. } *)
  (*   refine (ap (loops_functor B_to_X1) normally_generated_s @ _). *)
  (*   refine (functor_iterated_concat B_to_X1 (functor_list (fun p : loops B => (p^ @ alpha) @ p) s_list) @ _). *)
  (*   clear perfect normally_generated_s normally_generated_t. *)
  (*   induction s_list. *)
  (*   - reflexivity. *)
  (*   - simpl. *)
  (*     repeat rewrite concat_p1. repeat rewrite concat_1p. *)
  (*     rewrite IHl. rewrite concat_p1.  *)
  (*     repeat rewrite ap_pp. *)
  (*     admit. *)
  (*     (* TODO : Gjør uten rewrite. *) *)
      
      
      
    
  (*   transitivity (iterated_concat (functor_list (fun p : loops B => *)
  (*                                                  loops_functor B_to_X1 (p^ @ alpha @ p)) s_list)). *)
  (*   { admit.                    (* functor_list is functorial *) } *)
  (*   cut ((fun p : loops B => (loops_functor B_to_X1) ((p^ @ alpha) @ p)) = fun p : loops B => idpath). *)
  (*   intro path. rewrite path. *)
    
  (*   simpl. *)
    
  (*   induction (functor_list (loops_functor B_to_X1) (functor_list (fun p : loops B => (p^ @ alpha) @ p) s_list)). *)
  (*   - reflexivity. *)
  (*   - simpl. destruct (IHl)^. *)
    
  (*   simpl. *)
  (*   induction (functor_list (fun p : point B = point B => 1 @ (ap (fun b : B => push (inl b)) p @ 1)) *)
  (*      (functor_list (fun p : point B = point B => (p^ @ alpha) @ p) s_list)). *)

  (* Now we want maps SSP -> X1 and X1 -> SSP such that the composition is the identity *)
  Definition SSP_to_X1 : psusp (psusp P) ->* X1 :=
    psusp_rec (psusp_rec P_to_loopsloopsX1).
  
    (* - cbn. cut (IsTrunc 1 X1). intro H'. apply H'. (* not true *) *)
    (*   refine (H (point B) (point B) _ _ _ _). *)
      
      
    (*   apply moveR_Vp. refine (_ @ (concat_p1 _)^). refine (_ @ concat_1p _). *)
    (*   apply whiskerR. *)
    (*    refine (_ @ concat_p1 _). apply concat2. *)
    (*   refine (ap_pp  _ _  _@ _).  *)
    (*   refine (ap_pp  _ _  _@ _). refine (_ @ concat_p1 _). apply concat2. *)
    (*   refine (ap_V _ _ @ _). refine (ap inverse (kill_ *)

  Definition X1_to_SSP : X1 ->* psusp (psusp P).
  Proof.
    srapply @Build_pMap. cbn.
    srapply @pushout_rec.
    - exact (const North).
    - intro p. unfold const.
      apply (loop_susp_unit (psusp P)). exact p.
    - reflexivity.
  Defined.

  Definition id_comp : (X1_to_SSP o SSP_to_X1) == idmap.
  Proof.
    srapply @Susp_ind.
    - reflexivity.
    - apply (merid North).
    - intro x.
      refine (transport_paths_FlFr _ _ @ _). cbn. rewrite concat_p1. rewrite ap_idmap.
      revert x. srapply @Susp_ind.
      + cbn.
        apply moveR_pM. rewrite concat_pV.
        refine (ap inverse (y := 1) _).
        rewrite ap_compose.
        rewrite Susp_rec_beta_merid. reflexivity.
      + cbn.
        apply moveR_Vp. apply moveL_pM. apply inverse.
        rewrite ap_compose. rewrite Susp_rec_beta_merid. cbn.
        apply moveL_pV. rewrite concat_1p.
        apply (ap merid). apply merid. exact idpath.
      + 

        
        refine (pushout_rec_beta_pp North @ _).

    

  

  (* Now we want to show that the composition is the identity. . . *)
  Definition id_comp : (X1_to_SSP o* SSP_to_X1) = pmap_idmap _.
  Proof.
    apply (equiv_inj (loop_susp_adjoint (psusp P) (psusp (psusp P))) ).
    apply (equiv_inj (loop_susp_adjoint P (loops (psusp (psusp P))))).
    cbn.
    rewrite (path_pmap (loops_functor_compose X1_to_SSP SSP_to_X1)).
    rewrite (path_pmap (pmap_compose_assoc _ _ _)).
    rewrite (path_pmap (loops_functor_compose _ _)).
    rewrite (path_pmap (pmap_compose_assoc _ _ _)).
    cut (loops_functor (loops_functor SSP_to_X1 o* loop_susp_unit (psusp P)) o* loop_susp_unit P =
         P_to_loopsloopsX1).
    
    
    
    refine ((ap (fun f => loops_functor (f o* loop_susp_unit (psusp P)) o* loop_susp_unit P)
                (path_pmap (loops_functor_compose _ _))) @ _).
    
    
    refine (path_pmap (pmap_compose_assoc _ _ _) @ _).
    
    
    refine (path_pmap (pmap_compose_assoc _ _ _) @ _).
    
    transitivity (loops_functor (loops_functor (X1_to_SSP o* SSP_to_X1)) o* (fun alpha => 
    
    refine ((path_pmap (loops_functor_compose _ _)) @ _).
    refine (_ @ (path_pmap (loops_functor_compose _ _))^).
    apply (ap (fun f => f o* loops_functor (loop_susp_unit (psusp P)))).
    refine (ap loops_functor (path_pmap (loops_functor_compose _ _)) @ _).
    refine (path_pmap (loops_functor_compose _ _ ) @ _ ).
    apply path_pmap.
    srapply @Build_pHomotopy.
    - intro alpha. cbn. repeat rewrite concat_p1. repeat rewrite concat_1p.
      
    
    refine 
    
    
    apply (ap (fun f => loops_functor (loo
    
    
    
    unfold pointwise_paths. intro x. simpl in x. revert x.
    srapply @Susp_ind.
    - reflexivity.
    - exact (merid (point _)).
    - intro x.
      refine (transport_paths_FlFr (f:= X1_to_SSP o SSP_to_X1) (merid x) idpath @ _).
      rewrite concat_p1.
      rewrite ap_idmap. rewrite ap_compose.
      rewrite Susp_rec_beta_merid.
      apply moveR_Vp. apply inverse.
      revert x.
      srapply @Susp_ind.
      + cbn. apply concat_1p.
      + cbn. refine (concat_1p _ @ _). apply (ap merid).  exact (merid (point _)).
      + cbn. intro p.
        refine (transport_paths_FlFr (merid p) (concat_1p (merid North)) @ _).
        
        rewrite <- ap_compose.
        
        cbn.
    

        