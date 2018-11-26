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
  (* Record preMonoidal_1Type : Type := *)
  (*   { mon_type :> 1-Type; *)
  (*     mon_mult : mon_type -> mon_type -> mon_type; *)
  (*     mon_id : mon_type; *)
  (*     mon_assoc : forall (a b c : mon_type), mon_mult (mon_mult a b) c = mon_mult a (mon_mult b c); *)
  (*     mon_lid : forall (a : mon_type), mon_mult mon_id a = a; *)
  (*     mon_rid : forall (a : mon_type), mon_mult a mon_id a = a; *)
      
  
  (* Definition associative {A : Type}  (m : A-> A -> A) := forall (a b : A), (m a) o (m b) = m (m a b). *)
  (* Definition left_identity {A : Type} (m : A->A->A) (e : A) := m e = idmap. *)
  (* Definition right_identity_mult {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a. *)
    (* Definition right_identity_mult {A : Type} (m : A->A->A) (e : A) := (fun a : A => m a e) = idmap. *)
  
  Definition associative {A : Type}  (m : A-> A -> A) := forall (a b c: A),  m (m a b) c = m a (m b c).
  Definition left_identity_mult {A : Type} (m : A->A->A) (e : A) := forall a : A, m e a = a.
  Definition right_identity_mult {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a.

  (* Definition left_cancellation {A : Type} (m : A->A->A) := *)
  (*   forall a b c : A, m a b = m a c -> b = c . *)
  (* Definition right_cancellation {A : Type} (m : A->A->A) := *)
  (*   forall a b c : A, m a b = m c b -> a = c . *)
  
  
  (* Definition left_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) := *)
  (*   forall a : A, m (inv a) a = e. *)
  (* Definition right_inverse {A : Type} (m : A -> A -> A) (e : A) (inv : A -> A) := *)
  (*   forall a : A, m a (inv a) = e. *)
  
  (* Unneccesary but easier to just assume *)
  Definition coherence_triangle1 {A : Type} {m : A -> A -> A} {e : A}
             (assoc : associative m) (lid : left_identity_mult m e)  :=
    forall a b : A,
      ap (fun x => m x b) (lid a) = assoc e a b @ lid (m a b).
  
  Definition coherence_triangle2 {A : Type} {m : A -> A -> A} {e : A}
             (assoc : associative m) (lid : left_identity_mult m e) (rid : right_identity_mult m e) :=
    forall a b : A,
      ap (fun c => m c b) (rid a) = assoc a e b @ ap (m a) (lid b).

  Definition coherence_pentagon {A : Type} {m : A -> A -> A} (assoc : associative m) :=
    forall a b c d: A,
      ap (fun x => m x d) (assoc a b c) =
      assoc (m a b) c d @ assoc a b (m c d) @ (ap (m a) (assoc b c d))^ @ (assoc a (m b c) d)^.
      

  Record Monoidal_1Type : Type := { mon_type :> 1-Type;
                                    (* mon_istrunc : IsTrunc 1 mon_type; *)
                                    mon_mult  : mon_type->mon_type->mon_type;
                                    mon_id : mon_type;
                                    mon_assoc : associative mon_mult;
                                    mon_lid : left_identity_mult mon_mult mon_id ;
                                    mon_rid : right_identity_mult mon_mult mon_id ;
                                    mon_triangle1 : coherence_triangle1 mon_assoc mon_lid ;
                                    mon_triangle2 : coherence_triangle2 mon_assoc mon_lid mon_rid ;
                                    mon_pentagon : coherence_pentagon mon_assoc
                                  }.

  (*Makes mon_istrunc an implicit argument*)
  (* Global Arguments *)
  (*        Build_Monoidal_1Type mon_type (* {mon_istrunc} *) mon_mult mon_id mon_assoc mon_lid mon_rid *)
  (*        mon_triangle mon_pentagon. *)
  
  Global Arguments mon_mult {m} m1 m2.
  Global Arguments mon_id {m}.
  Global Arguments mon_assoc {m} a b c.
  Global Arguments mon_lid {m} a.
  Global Arguments mon_rid {m} a.

  
  Infix "⊗" := mon_mult (at level 50,no associativity).
  (* Lemma ap_mon_id (M : Monoidal_1Type) {a b : M} (p : a = b) : *)
  (*   ap (mon_mult mon_id) p = (mon_lid a @ p @ (mon_lid b)^). *)
  (* Proof. *)
  (*   destruct p. hott_simpl. *)
  (* Qed. *)

  (* Lemma ap_mon_id_mon_lid (M : Monoidal_1Type) {a : M}: *)
  (*   ap (mon_mult mon_id) (mon_lid a) = mon_lid (mon_mult mon_id a). *)
  (* Proof. *)
  (*   refine (ap_mon_id M _ @ _). hott_simpl. *)
  (* Qed. *)

  (* Lemma mon_assoc_mon_id (M : Monoidal_1Type) {a b : M} : *)
  (*   mon_assoc mon_id a b = *)
  (*   (mon_lid ((mon_id ⊗ a) ⊗ b))^ @ *)
  (*    (((ap (fun x : M => x ⊗ b) (mon_assoc mon_id mon_id a) @ mon_assoc mon_id (mon_id ⊗ a) b)^ @ *)
  (*   (mon_assoc (mon_id ⊗ mon_id) a b @ mon_assoc mon_id mon_id (a ⊗ b))) @ mon_lid (mon_id ⊗ (a ⊗ b))). *)
  (* Proof. *)
  (*   apply moveL_Vp. *)
  (*   apply moveL_pM. *)
  (*   refine ((ap_mon_id M _)^ @ _). *)
  (*   apply moveL_Vp. apply moveR_pM. apply moveR_pM. apply (mon_pentagon M mon_id mon_id a b). *)
  (* Qed.     *)

  (* Definition mon_triangle2 (M : Monoidal_1Type) : forall (a b : M), *)
  (*     ap (fun x => x ⊗ b) (mon_lid a) = *)
  (*     mon_assoc mon_id a b @ mon_lid (a ⊗ b). *)
  (* Proof. *)
  (*   intros a b. *)
  (*   apply moveL_Mp. *)
  (*   apply (ap (concat (mon_lid (mon_id ⊗ (a ⊗ b)))))^-1. *)
  (*   rewrite (mon_assoc_mon_id). hott_simpl. repeat rewrite concat_pp_p. *)
  (*   Check (mon_triangle M mon_id a). *)
  (*   Check (mon_triangle M mon_id a @ whiskerL _ (ap_mon_id_mon_lid M)). *)
  (*   Check (moveR_pV _ _ _ (mon_triangle M mon_id a @ whiskerL _ (ap_mon_id_mon_lid M)))^. *)
  (*   rewrite (moveR_pV _ _ _ (mon_triangle M mon_id a @ whiskerL _ (ap_mon_id_mon_lid M)))^. *)
  (*   rewrite ap_pp. rewrite <- (ap_compose (fun c : M => c ⊗ a) (fun x : M => x ⊗ b)) . *)
  (*   rewrite ap_V. *)
  (*   repeat rewrite inv_pp. repeat rewrite inv_V. *)
  (*   repeat rewrite concat_p_pp. *)
  (*   Check (mon_triangle M a mon_id). *)
    

    
    


  (*Todo: Define symmetric monoidal category (check coherence criteria)*)
  Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a.

  Record Monoidal_Map (M N : Monoidal_1Type) :=
    {mon_map :> M -> N;
     mon_map_mult (a b : M) : mon_map (a ⊗ b) = (mon_map a) ⊗ (mon_map b) ;
     mon_map_id : mon_map (mon_id) = mon_id;
     mon_map_assoc (a b c : M) :
       ap mon_map (mon_assoc a b c) =
       mon_map_mult (a ⊗ b) c @ ap (fun x => x ⊗ (mon_map c)) (mon_map_mult a b) @ mon_assoc (mon_map a) (mon_map b) (mon_map c) @
                    (ap (mon_mult (mon_map a)) (mon_map_mult b c))^ @ (mon_map_mult a (b ⊗ c))^ ;
     mon_map_lid (x : M) : ap mon_map (mon_lid x) =
                           mon_map_mult mon_id x @ ap (fun s => s ⊗ mon_map x) mon_map_id @ mon_lid (mon_map x);
     mon_map_rid (x : M) : ap mon_map (mon_rid x) =
                           mon_map_mult x mon_id @ ap (mon_mult (mon_map x)) mon_map_id @ mon_rid (mon_map x) }.
         
       
       
     

       
       (* ap mon_map (ap10 (mon_assoc x y) z) = *)
     (*   mon_map_mult x (y ⊗ z) @ ap (fun s => mon_map x ⊗ s) (mon_map_mult y z) @ *)
     (*                (ap10 (mon_assoc (mon_map x) (mon_map y)) (mon_map z) @ *)
     (* (ap (fun s => s ⊗ mon_map z) (mon_map_mult x y))^ @ (mon_map_mult (x ⊗ y) z)^; *)
     (* mon_map_lid (x : M) : ap mon_map (mon_lid x) = *)
     (*                       mon_map_mult mon_id x @ ap (fun s => s ⊗ mon_map x) mon_map_id @ mon_lid (mon_map x); *)
     (* mon_map_rid (x : M) : ap mon_map (mon_rid x) = *)
     (*                       mon_map_mult x mon_id @ ap (fun s => mon_map x ⊗ s) mon_map_id @ mon_rid (mon_map x); *)
     (* mon_map_mult (x y : M) : mon_map (x ⊗ y) = (mon_map x) ⊗ (mon_map y); *)
     (* mon_map_id : mon_map (mon_id) = mon_id; *)
     (* mon_map_assoc (x y z : M) : *)
     (*   ap mon_map (ap10 (mon_assoc x y) z) = *)
     (*   mon_map_mult x (y ⊗ z) @ ap (fun s => mon_map x ⊗ s) (mon_map_mult y z) @ *)
     (*                (ap10 (mon_assoc (mon_map x) (mon_map y)) (mon_map z) @ *)
     (* (ap (fun s => s ⊗ mon_map z) (mon_map_mult x y))^ @ (mon_map_mult (x ⊗ y) z)^; *)
     (* mon_map_lid (x : M) : ap mon_map (mon_lid x) = *)
     (*                       mon_map_mult mon_id x @ ap (fun s => s ⊗ mon_map x) mon_map_id @ mon_lid (mon_map x); *)
     (* mon_map_rid (x : M) : ap mon_map (mon_rid x) = *)
     (*                       mon_map_mult x mon_id @ ap (fun s => mon_map x ⊗ s) mon_map_id @ mon_rid (mon_map x); *)
    (* }. *)
  Arguments mon_map_mult {M N} F a b : rename.
  Arguments mon_map_id {M N} F : rename.
  Arguments mon_map_assoc {M N} F a b c : rename.
  Arguments mon_map_lid {M N} F a : rename.
  Arguments mon_map_rid {M N} F a : rename.

  Definition monoidal_map_id (M : Monoidal_1Type) : Monoidal_Map M M.
  Proof.
    srapply (Build_Monoidal_Map M M idmap); try reflexivity.
    - intros. simpl.
      rewrite ap_idmap. repeat rewrite concat_p1. apply inverse. apply concat_1p.
  Defined.
  
  Definition monoidal_map_compose (M N O : Monoidal_1Type) :
    Monoidal_Map M N -> Monoidal_Map N O -> Monoidal_Map M O.
  Proof.
    intros F G.
    srapply @Build_Monoidal_Map.
    - exact (G o F).
    (* - intros a b . *)
    (*   refine (ap (fun f => G o f) (mon_map_mult F m) @ _). *)
    (*   apply (ap (fun f => f o F) (mon_map_mult G (F m))). *)
    (* - apply (ap G (mon_map_id F) @ mon_map_id G). *)
    (* - simpl. intros m n. *)
        
    (*   refine (ap_compose (fun f => F o f) (fun f => G o f) _ @ _). *)
    (*   refine (ap (ap (fun f => G o f)) (mon_map_assoc F m n) @ _). *)
      
      
      

    (*   refine (ap_pp (fun f => G o f) _ _ @ _). *)
    (*   refine (whiskerR (ap_pp (fun f => G o f) _ _ ) _ @ _). *)
    (*   refine (whiskerR (whiskerR (ap_pp (fun f => G o f) _ _ ) _) _ @ _). *)
    (*   refine (whiskerR (whiskerR (whiskerR (ap_pp (fun f => G o f) _ _ ) _) _) _ @ _). *)
    (*   repeat rewrite ap_pp. *)
    (*   repeat rewrite concat_pp_p. *)
    (*   rewrite <- (ap_compose (fun (f : M -> N) (x : M) => G (f x)) (fun (f : M -> O) (x : M) => f (n ⊗ x))). *)
    (*   rewrite <- (ap_compose (fun (f : N -> O) (x : M) => f (F x)) (fun (f : M -> O) (x : M) => f (n ⊗ x)) (mon_map_mult G (F m))). *)
    (*   rewrite <- (ap_compose (fun (f : M -> N) (x : M) => G (f x)) (fun (f : M -> O) (x : M) => G (F m) ⊗ f x)). *)
    (*   rewrite <- (ap_compose (fun (f : N -> O) (x : M) => f (F x)) (fun (f : M -> O) (x : M) => G (F m) ⊗ f x) (mon_map_mult G (F n))). *)
    (*   rewrite ap10_pp. rewrite ap_pp. *)
    (*   repeat rewrite inv_pp.  repeat rewrite ap_V.  *)
    (*   repeat rewrite concat_pp_p. *)
    (*   apply concat2. *)
    (*   { apply inverse. *)
    (*     apply (ap_compose (fun (f : M -> N) (x : M) => f (n ⊗ x)) (fun (f : M -> N) (x : M) => G (f x)) (mon_map_mult F m)). } *)
    (*   Admitted. *)
  (*     rewrite (ap10_ap_precompose G). *)
      
  (*     ap10_ap_precompose *)
  (*     ap10_ap_postcompose *)


  (*     apply whiskerL. *)
  (*     repeat refine (concat_p_pp _ _ _ @ _). *)
  (*     repeat refine (_ @ concat_pp_p _ _ _). *)
  (*     refine (_ @ whiskerL _ (inv_pp _ _)^). *)
  (*     repeat refine (_ @ concat_pp_p _ _ _). *)
  (*     refine (concat2 _ (ap_V G _)). *)
  (*     refine (whiskerL _ (ap_V G _) @ _). *)
  (*     refine (whiskerL _ (ap inverse (ap_compose _ G (mon_map_mult F _ _))^) @ _). *)
  (*     refine (whiskerR (whiskerR (ap_compose _ G (mon_map_mult F _ _))^ _) _ @ _). *)
  (*     assert (H : forall (a b c : O) (p : a = b) (q : b = c), *)
  (*                (ap (fun s : O => s ⊗ G (F z)) (p @ q))^ = *)
  (*                (ap (fun s : O => s ⊗ G (F z)) q)^ @ (ap (fun s : O => s ⊗ G (F z)) p)^). *)
  (*     { by path_induction. } *)
  (*     refine (_ @ whiskerR (whiskerL _ (H _ _ _ _ _)^) _). clear H. *)

  (*     repeat rewrite ap_pp. *)
  (*     repeat rewrite <- (ap_compose G). *)
  (*     rewrite (mon_map_assoc G (F x) (F y) (F z)). *)
  (*     repeat rewrite concat_p_pp. *)
  (*     refine (concat_pp_p _ _ _ @ _). *)
  (*     refine (_ @ concat_p_pp _ _ _). *)
  (*     apply concat2. *)
  (*     + repeat apply whiskerR. destruct (mon_map_mult F _ _). cbn. destruct (mon_map_mult G _ _). reflexivity.         *)
  (*     + destruct (mon_map_mult F _ _). cbn. destruct (mon_map_mult G _ _ ). reflexivity.  *)
  (*   - intro x. simpl. *)
  (*     transitivity (ap G (ap F (mon_lid x))). *)
  (*     { apply (ap_compose F G). } *)
  (*     refine ( ap (ap G) (mon_map_lid F x) @ _). *)
  (*     refine (ap_pp G _ _ @ _). *)
  (*     refine (ap (fun p => p @ ap G (mon_lid (F x))) (ap_pp G _ _) @ _). *)
  (*     refine (whiskerL _ (mon_map_lid G (F x)) @ _). *)
  (*     repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR. *)
  (*     repeat refine (concat_pp_p _ _ _ @ _). *)
  (*     repeat refine (_ @ concat_p_pp _ _ _). apply whiskerL. *)
  (*     refine (_ @ whiskerL _ (ap_pp (fun s : O => s ⊗ G (F x)) _ _)^). *)
  (*     repeat refine (_ @ concat_pp_p _ _ _). *)
  (*     repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR. *)
  (*     refine (whiskerR (ap_compose _ G (mon_map_id F))^ _ @ _). *)
  (*     refine (_ @ whiskerL _ (ap_compose G _ (mon_map_id F))). *)
  (*     destruct (mon_map_id F). cbn. *)
  (*     exact (concat_1p _ @ (concat_p1 _)^). *)
  (*   - intro x. simpl. *)
  (*     transitivity (ap G (ap F (mon_rid x))). *)
  (*     { apply (ap_compose F G). } *)
  (*     refine ( ap (ap G) (mon_map_rid F x) @ _). *)
  (*     refine (ap_pp G _ _ @ _). *)
  (*     refine (ap (fun p => p @ ap G (mon_rid (F x))) (ap_pp G _ _) @ _). *)
  (*     refine (whiskerL _ (mon_map_rid G (F x)) @ _). *)
  (*     repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR. *)
  (*     repeat refine (concat_pp_p _ _ _ @ _). *)
  (*     repeat refine (_ @ concat_p_pp _ _ _). apply whiskerL. *)
  (*     refine (_ @ whiskerL _ (ap_pp (fun s : O => G (F x) ⊗ s) _ _)^). *)
  (*     repeat refine (_ @ concat_pp_p _ _ _). *)
  (*     repeat refine (concat_p_pp _ _ _ @ _). apply whiskerR. *)
  (*     refine (whiskerR (ap_compose _ G (mon_map_id F))^ _ @ _). *)
  (*     refine (_ @ whiskerL _ (ap_compose G _ (mon_map_id F))). *)
  (*     destruct (mon_map_id F). cbn. *)
  (*     exact (concat_1p _ @ (concat_p1 _)^). *)
  (* Defined. *)
  
    - intros a b.
      refine (ap G (mon_map_mult F a b) @ mon_map_mult G _ _).
    - refine (ap G (mon_map_id F) @ mon_map_id G).
    - intros.
      refine (ap_compose F G _ @ _).
      refine (ap (ap G) (mon_map_assoc F a b c) @ _).
      repeat rewrite ap_pp.
      rewrite (mon_map_assoc G (F a) (F b) (F c)). 
      repeat rewrite (concat_pp_p). apply whiskerL.
      repeat rewrite <- (ap_compose G).
      rewrite ap_V. rewrite ap_V. 
      rewrite <- (ap_compose (mon_mult (F a)) G (mon_map_mult F b c)).
      rewrite <- (ap_compose (fun x : N => x ⊗ F c) G).
      rewrite inv_pp. rewrite inv_pp. 
      
      repeat rewrite concat_p_pp.
      assert (H : (ap (fun x : N => G (x ⊗ F c)) (mon_map_mult F a b) @ mon_map_mult G (F a ⊗ F b) (F c)) =
              (mon_map_mult G (F (a ⊗ b)) (F c) @ ap (fun x : N => G x ⊗ G (F c)) (mon_map_mult F a b))).
      { destruct (mon_map_mult F a b). hott_simpl. }
      rewrite H. repeat rewrite concat_pp_p. repeat (apply whiskerL).
      repeat rewrite concat_p_pp. apply whiskerR.
      destruct (mon_map_mult F b c). hott_simpl.
    - intro x.
      refine (ap_compose F G _ @ _).
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
    - intro x.
      refine (ap_compose F G _ @ _ ).
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
    - cbn. unfold left_identity_mult. reflexivity.
    - cbn. unfold right_identity_mult. reflexivity.
    - unfold coherence_triangle1. cbn. reflexivity.
    - unfold coherence_triangle2. cbn. reflexivity.
    - unfold coherence_pentagon. cbn. reflexivity.
  Defined.

  Definition monoidal_action (M : Monoidal_1Type) (X : 1-Type) := Monoidal_Map M (endomorphism X).

  (* Definition Build_Monoidal_Action (M : Monoidal_1Type) (X : 1-Type) *)
  (*            (a : M -> X -> X) *)
  (*            (mon_act_mult : forall (s t : M) (x : X), a s (a t x) = a (s ⊗ t) x) *)
  (*            (mon_act_id : forall x : X, a mon_id x = x) *)
             
             

  Definition ap010 {A B C : Type} (f : A -> B -> C) {x x' : A} (p : x = x') (y : B) : f x y = f x' y := ap10 (ap f p) y.
  Definition action_on_path {M} {X} (a : monoidal_action M X) {s t : M} (p : s = t) := ap10 (ap a p).
  
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

  (* Definition cancel_left_monoidal_action {M : Monoidal_1Type} {X : 1-Type} (a : monoidal_action M X) := *)
  (*   forall (s t : M) (p q : s = t), *)
  (*     (forall x : X, action_on_path a p  x = action_on_path a q x) -> p = q. *)

  Definition path_arrow_V {A B : Type} {f g : A -> B} (H : f == g) :
    path_arrow g f (fun a => (H a)^) = (path_arrow f g H)^.
  Proof.
    transitivity (path_arrow f g (ap10 (path_forall _ _ H)))^.
    transitivity (path_arrow g f (fun a => (ap10 (path_forall _ _ H) a)^)).
    - apply (ap (path_arrow g f)). apply path_forall.
      intro a. apply (ap inverse). apply inverse. apply (ap10_path_arrow).
    - destruct (path_forall f g H). simpl.
      destruct (path_forall _ _ (ap10_1 (f:= f)))^.
      destruct (path_arrow_1 f)^. reflexivity.
    - apply (ap inverse). apply (ap (path_arrow f g)). apply (path_forall _ _ (ap10_path_arrow f g H)).
  Defined.
  
  Definition act_on_self (M : Monoidal_1Type) : monoidal_action M M.
  Proof.
    srapply @Build_Monoidal_Map.
    - simpl. apply mon_mult.
    - intros a b. apply path_arrow. intro c.
      apply mon_assoc.
    - apply path_arrow. apply mon_lid.
    - intros a b c. simpl. hott_simpl.
      transitivity (path_arrow _ _ (fun d : M => ap (fun x : M => x ⊗ d) (mon_assoc a b c))).
      simpl.
      { destruct (mon_assoc a b c). simpl. apply inverse. apply path_forall_1. }      
      rewrite (path_forall _ _ (mon_pentagon M a b c) ).
      repeat rewrite path_arrow_pp.
      rewrite path_arrow_V. rewrite path_arrow_V.
      apply whiskerR. apply concat2.
      apply whiskerL.
      + apply inverse.
        refine (ap_functor_arrow _ idmap (mon_mult (a ⊗ b)) (fun x : M => a ⊗ (b ⊗ x)) (fun c0 : M => mon_assoc a b c0) @ _).
        apply (ap (path_arrow (fun b0 : M => (a ⊗ b) ⊗ (c ⊗ b0)) (fun b0 : M => a ⊗ (b ⊗ (c ⊗ b0))))).
        apply path_forall. intro m.
        apply ap_idmap.
      + apply (ap inverse).
        apply inverse.
        refine (ap_functor_arrow idmap _ (mon_mult (b ⊗ c)) (fun x : M => b ⊗ (c ⊗ x)) (fun c0 : M => mon_assoc b c c0) ).        
    - intro a. simpl. hott_simpl.
      transitivity (path_arrow _ _ (fun b : M => ap (fun x : M => x ⊗ b) (mon_lid a))).
      { simpl. destruct (mon_lid a). simpl. apply inverse. apply path_forall_1. }
      Check (mon_triangle1 M a).
      rewrite (path_forall _ _ (mon_triangle1 M a)).
      repeat rewrite path_arrow_pp.
      apply whiskerL.
      apply inverse.
      refine (ap_functor_arrow (mon_mult a) idmap (mon_mult mon_id) idmap mon_lid @ _).
      apply (ap (path_arrow (fun b : M => mon_id ⊗ (a ⊗ b)) (fun b : M => a ⊗ b))).
      apply path_forall. intro b. apply ap_idmap.
    - intro a. simpl. hott_simpl.
      transitivity (path_arrow _ _ (fun b : M => ap (fun x : M => x ⊗ b) (mon_rid a))).
      { simpl. destruct (mon_rid a). simpl. apply inverse. apply path_forall_1. }
      Check (mon_triangle2 M a).
      rewrite (path_forall _ _ (mon_triangle2 M a)).
      repeat rewrite path_arrow_pp.
      apply whiskerL.
      apply inverse.
      refine (ap_functor_arrow _ _ (mon_mult mon_id) idmap mon_lid ).
  Defined.

  (* Definition functor_prod_compose {A1 A2 B1 B2 C1 C2 : Type} {f1 : A1 -> B1} {f2 : A2 -> B2} {g1 : B1 -> C1} {g2 : B2 -> C2} : *)
  (*   functor_prod (g1 o f1) (g2 o f2) = (functor_prod g1 g2) o (functor_prod f1 f2) := idpath. *)
  
  (* Definition functor_prod_id {A B: Type} : *)
  (*   functor_prod (fun a : A => a) (fun b : B => b) = idmap := idpath. *)

  (* Definition functor_prod_uncurried {A1 A2 B1 B2} : (A1 -> B1) * (A2 -> B2) -> ((A1*A2) -> B1*B2). *)
  (* Proof. intros [f g]. exact (functor_prod f g). *)
  (* Defined. *)
  
             
  Definition act_on_prod (M : Monoidal_1Type) (X Y: 1-Type) (a1 : monoidal_action M X) (a2 : monoidal_action M Y):
    monoidal_action M (BuildTruncType 1 (X*Y)).
  Proof.
    srapply @Build_Monoidal_Map.
    - simpl. intro s.
      apply (functor_prod (a1 s) (a2 s)).
    - intros s t. simpl.
      apply (ap011 functor_prod (mon_map_mult a1 _ _) (mon_map_mult a2 _ _)).
    - apply (ap011 functor_prod (mon_map_id a1) (mon_map_id a2)).
    - intros s t u. simpl.
      (* transitivity (ap functor_prod_uncurried *)
      (*              (ap (fun m : M * M => (a1 (fst m), a2 (snd m))) *)
      (*                  (path_prod ((s ⊗ t) ⊗ u, (s ⊗ t) ⊗ u) (s ⊗ (t ⊗ u), s ⊗ (t ⊗ u)) (mon_assoc s t u) (mon_assoc s t u)))). *)
      (* { destruct (mon_assoc s t u). reflexivity. } *)
      transitivity (ap011 (functor_prod) (ap a1 (mon_assoc s t u)) (ap a2 (mon_assoc s t u))).
      { destruct (mon_assoc s t u). reflexivity. } hott_simpl.
      transitivity (ap011 functor_prod
                          (((mon_map_mult a1 (s ⊗ t) u @ ap (fun x : (X -> X) => x o (a1 u)) (mon_map_mult a1 s t))
                              @ (ap (mon_mult (a1 s)) (mon_map_mult a1 t u))^) @ (mon_map_mult a1 s (t ⊗ u))^)
                          (((mon_map_mult a2 (s ⊗ t) u @ ap (fun y : (Y -> Y) => y o (a2 u)) (mon_map_mult a2 s t))
                              @ (ap (mon_mult (a2 s)) (mon_map_mult a2 t u))^) @ (mon_map_mult a2 s (t ⊗ u))^)).
      { apply (ap011 (ap011 functor_prod)).
        - refine (mon_map_assoc a1 s t u @ _). simpl. hott_simpl.
        - refine (mon_map_assoc a2 s t u @ _). simpl. hott_simpl. }
      refine (ap011_pp_pp functor_prod _ _ _ _ @ _).
      refine (whiskerR (ap011_pp_pp functor_prod _ _ _ _ ) _ @ _).
      refine (whiskerR (whiskerR (ap011_pp_pp functor_prod _ _ _ _ ) _) _ @ _).
      apply concat2. apply concat2. apply whiskerL.
      + (* generalize (mon_map_mult a1 s t). intro p. *)
        (* generalize (mon_map_mult a2 s t). intro q. *)
        cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2),
                ap011 functor_prod (ap (fun f => f o (a1 u)) p) (ap (fun g => g o (a2 u)) q) =
                ap (fun f => f o (functor_prod (a1 u) (a2 u))) (ap011 functor_prod p q)).
        { intro H. apply H. }
        by path_induction.
      + simpl.
        (* generalize (mon_map_mult a1 t u). intro p. *)
        (* generalize (mon_map_mult a2 t u). intro q. *)
        cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2),
                ap011 functor_prod (ap (fun f => (a1 s) o f) p)^ (ap (fun g => (a2 s) o g) q)^ =
                (ap (fun f => (functor_prod (a1 s) (a2 s)) o f) (ap011 functor_prod p q))^).
        { intro H. apply H. }
        by path_induction.        
      + cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2),
                ap011 functor_prod p^ q^ = (ap011 functor_prod p q)^).
        { intro H. apply H. }
        by path_induction.        
    - intro s.
      transitivity (ap011 functor_prod (ap a1 (mon_lid s)) (ap a2 (mon_lid s))).
      { destruct (mon_lid s). reflexivity. }
      transitivity (ap011 functor_prod
                          ((mon_map_mult a1 mon_id s @ ap (fun f => f o (a1 s)) (mon_map_id a1)))
                          ((mon_map_mult a2 mon_id s @ ap (fun f => f o (a2 s)) (mon_map_id a2)))).
      { apply (ap011 (ap011 functor_prod)).
        - refine (mon_map_lid a1 s @ _). hott_simpl.
        - refine (mon_map_lid a2 s @ _). hott_simpl. }
      refine (ap011_pp_pp functor_prod _ _ _ _ @ _). simpl. hott_simpl. apply whiskerL.
      cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2),
              ap011 functor_prod (ap (fun f => f o (a1 s)) p) (ap (fun g => g o (a2 s)) q) =
              ap (fun f => f o (functor_prod (a1 s) (a2 s))) (ap011 functor_prod p q)).
      { intro H.  apply (H _ _ _ _ (mon_map_id a1) (mon_map_id a2)). }
        by path_induction.
    - intro s.
      transitivity (ap011 functor_prod (ap a1 (mon_rid s)) (ap a2 (mon_rid s))).
      { destruct (mon_rid s). reflexivity. }
      transitivity (ap011 functor_prod
                          ((mon_map_mult a1 s mon_id @ ap (mon_mult (a1 s)) (mon_map_id a1)))
                          ((mon_map_mult a2 s mon_id @ ap (mon_mult (a2 s)) (mon_map_id a2)))).
      { apply (ap011 (ap011 functor_prod)).
        - refine (mon_map_rid a1 s @ _). hott_simpl.
        - refine (mon_map_rid a2 s @ _). hott_simpl. }
      refine (ap011_pp_pp functor_prod _ _ _ _ @ _). simpl. hott_simpl. apply whiskerL.
      cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2),
              ap011 functor_prod (ap (fun f => (a1 s) o f) p) (ap (fun g => (a2 s) o g) q) =
              ap (fun f => (functor_prod (a1 s) (a2 s)) o f) (ap011 functor_prod p q)).
      { intro H.  apply (H _ _ _ _ (mon_map_id a1) (mon_map_id a2)). }
        by path_induction.
  Defined.  

  Require Import HoTT.Categories.
  (* if we have a monoidal action with left_cancellation, we can build a category with objects X and arrows*)
  (* {m : M & m ⊗ x = m ⊗ y} *)
  Definition monoidal_action_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) :
    (X -> X -> Type) := fun x y => {s : M & a s x = y}.

  (* Definition ap101 {A B C : Type} {f g : A -> B -> C} (p1 : f = g) { *)
  (*                                                      forall  *)
  

  (* Ltac destruct_inverse p := *)
  (*   set (q := p^); set (H := idpath : p^ = q); destruct q; . *)
    
  (*   recall p^ as q eqn:H; destruct q; destruct (ap inverse H^ @ inv_V p). *)
  
  Definition monoidal_action_cat (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X)
             (left_cancel : forall (s t : M) (p q : s = t) (x : X),
                 action_on_path a p x = action_on_path a q x -> p = q)
    : PreCategory.
  Proof.
    srapply (Build_PreCategory (monoidal_action_morphism M X a)).
    (* identity *)
    - intro x. exists mon_id. apply mon_act_id.
    (* composition *)
    - intros x y z.
      intros [s1 p1] [s2 p2].
      exists (s1 ⊗ s2).
      exact (mon_act_mult a s1 s2 x @ ap (a s1) p2 @ p1).
    (* associtivity *)
    - intros x1 x2 x3 x4 [s1 []] [s2 []] [s3 []]. repeat rewrite ap_1. repeat rewrite concat_p1.
      srapply @path_sigma. apply mon_assoc. cbn.
      refine (transport_paths_Fl (mon_assoc s3 s2 s1) _ @ _).
      rewrite (ap_apply_Fl (mon_assoc s3 s2 s1) a x1).
      rewrite (mon_map_assoc a). simpl. unfold mon_act_mult. rewrite concat_p1.
      apply moveR_pM.
      repeat rewrite ap10_pp. repeat rewrite ap10_V. repeat rewrite inv_pp. 
      repeat rewrite inv_V.
      repeat rewrite concat_pp_p. 
      apply whiskerL. apply concat2.
      { apply (ap10_ap_postcompose (a s3) (mon_map_mult a s2 s1)). }
      apply whiskerR. apply (ap inverse).
      apply (ap10_ap_precompose (a s1) (mon_map_mult a s3 s2)). 
    (* left identity *)
    - simpl.
      intros x1 x2 [s []]. simpl. rewrite concat_p1.
      srapply @path_sigma. apply mon_lid. simpl. 
      refine (transport_paths_Fl (mon_lid s) _ @ _).
      apply moveR_Vp. refine (_ @ (concat_p1 _)^).
      rewrite (ap_apply_Fl (mon_lid s) a x1).
      unfold mon_act_mult. unfold mon_act_id.
      rewrite (mon_map_lid a). simpl. rewrite concat_p1.
      rewrite ap10_pp.
      apply whiskerL.
      apply inverse.
      apply (ap10_ap_precompose (a s) (mon_map_id a)).
    (* right identity *)
    - simpl.
      intros x1 x2 [s []]. simpl. rewrite concat_p1.
      srapply @path_sigma. apply mon_rid. simpl. 
      refine (transport_paths_Fl (mon_rid s) _ @ _).
      apply moveR_Vp. refine (_ @ (concat_p1 _)^).
      rewrite (ap_apply_Fl (mon_rid s) a x1).
      unfold mon_act_mult. unfold mon_act_id.
      rewrite (mon_map_rid a). simpl. rewrite concat_p1.
      rewrite ap10_pp.
      apply whiskerL.
      apply inverse.
      apply (ap10_ap_postcompose (a s) (mon_map_id a)).
    (* the morphisms form a set. . . *)
    - intros x1 x2.
      unfold monoidal_action_morphism.
      intros [s1 p1] [s2 p2].
      apply (trunc_equiv' {q : s1 = s2 & transport (fun s => a s x1 = x2) q p1 = p2}).
      { apply equiv_inverse. apply equiv_path_sigma. }
      (* apply (trunc_equiv' {q : s1 = s2 & p1 = (ap (fun s => a s x1) q) @ p2}). *)
      apply (trunc_equiv' {q : s1 = s2 & p1 = action_on_path a q x1 @ p2}).
      { apply equiv_functor_sigma_id. intro q. destruct q. simpl. destruct p2. apply equiv_idmap. }
      apply trunc_sigma'.
      + intro p. exact _.
      + simpl.
        intros [q1 r1] [q2 r2]. simpl.
        apply contr_inhabited_hprop. exact _.
        apply (left_cancel _ _ q1 q2 x1).
        transitivity (p1 @ p2^).
        { apply moveL_pV. apply r1^. }
        { apply moveR_pV. apply r2. }
  Defined.

  Definition concat_fl {A : Type} {a1 a2 b1 b2 : A} (p1 : a1 = b1) (p2 : a2 = b2) :
    a1 = a2 -> b1 = b2.
  Proof. by path_induction. Defined.

  Definition group_completion (M : Monoidal_1Type)
             (left_cancel : forall (s t : M) (p q : s = t) (a : M),
                 ap10 (ap mon_mult p) a = ap10 (ap mon_mult q) a -> p = q) : PreCategory.
  Proof.
    apply (monoidal_action_cat M (BuildTruncType 1 (M*M)) (act_on_prod M M M (act_on_self M) (act_on_self M))).
    simpl. intros s t p q [a b].
    unfold action_on_path. simpl.
    intro H. apply (left_cancel _ _ _ _ a).
    refine ((ap_fst_path_prod (z := (s ⊗ a, s ⊗ b )) (z' := (t ⊗ a, t ⊗ b ))
                (ap10 (ap mon_mult p) a) (ap10 (ap mon_mult p) b))^ @ _ @
             ap_fst_path_prod (z := (s ⊗ a, s ⊗ b )) (z' := (t ⊗ a, t ⊗ b ))
                (ap10 (ap mon_mult q) a) (ap10 (ap mon_mult q) b)).
    apply (ap (ap fst)).
    revert H.
    apply concat_fl.
    - destruct p. reflexivity.
    - destruct q. reflexivity.
  Defined.
End Monoidal_1Type.  

(*Defining the monoidal 1-type of finite sets and isomorphisms*)
Section BΣ.
    
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Definition BΣ := { S : Type & Finite S}.
  Definition type_of_fin : BΣ -> Type := pr1.
  Coercion type_of_fin : BΣ  >-> Sortclass.
  Definition path_BΣ {S T : BΣ} : S <~> T -> S = T
    := path_finite_types_sum S T.

  Definition path_BΣ_compose (S T U : BΣ) (e1 : T <~> S) (e2 : U <~> T) :
    path_BΣ e2 @ path_BΣ e1 = path_BΣ (e1 oE e2).
  Proof.
    unfold path_BΣ. unfold path_finite_types_sum. Admitted.
    



  
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
  
  Definition BΣ_lid : left_identity_mult plus_BΣ ([0]).
  Proof.
    intro S. apply path_BΣ.
    apply sum_empty_l.
  Defined.
  
  Definition BΣ_rid : right_identity_mult plus_BΣ ([0]).
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
  
  Definition natural_path_BΣ {S1 S2 S3: BΣ} (e : S1 <~> S2) :
    ap (fun x : BΣ => x ⊕ S3) (path_BΣ e) = path_BΣ (S := S1 ⊕ S3) (T := S2 ⊕ S3) (equiv_functor_sum_r (B := S3) e).
  Proof.
    unfold path_BΣ.
    apply (equiv_inj (path_finite_types_sum _ _)^-1).
    refine (_ @ (eissect (path_finite_types_sum (S1 ⊕ S3) (S2 ⊕ S3)) (equiv_functor_sum_r e))^).
    apply path_equiv. (* apply path_arrow. *) simpl.
    (* intros [s1 | s3]. simpl. *)
    (* destruct S1 as [S1 fin1]. destruct S2 as [S2 fin2]. destruct S3 as [S3 fin3]. simpl in *. *)
    unfold pr1_path. 
    transitivity
      (transport idmap (ap (fun X : Type => X + S3) (ap pr1 (path_sigma_hprop S1 S2 (path_universe_uncurried e))))).
    { apply (ap (transport idmap)).
      refine ((ap_compose (fun x : BΣ => x ⊕ S3) pr1 _)^ @ ap_compose pr1 (fun X : Type => X + S3) _). }
    apply path_arrow. intro s.
    refine ((transport_idmap_ap _ _ _ _ _ _)^ @ _).
    transitivity (transport (fun X : Type => X + S3) (path_universe_uncurried e) s).
    { apply (ap (fun p => transport (fun X : Type => X + S3) p s)).
      apply (ap_pr1_path_sigma_hprop). }
    destruct s as [s1 | s2].
    - simpl.      
      destruct S1 as [S1 fin1]. destruct S2 as [S2 fin2]. destruct S3 as [S3 fin3]. simpl in *.
      clear fin1 fin2 fin3.

      revert s1. revert e.
      apply (equiv_induction
               (fun S2 e => forall s1 : S1, transport (fun X : Type => X + S3) (path_universe_uncurried e) (inl s1) = inl (e s1))).
      intros s1. simpl.
      change (path_universe_uncurried 1) with (path_universe (A := S1) idmap).      
      rewrite path_universe_1. reflexivity.
    - simpl.
      destruct S1 as [S1 fin1]. destruct S2 as [S2 fin2]. destruct S3 as [S3 fin3]. simpl in *.
      clear fin1 fin2 fin3. destruct (path_universe_uncurried e). reflexivity.
  Defined.



  
  
  (*TODO: How [cardinal] respects associativity and identity proofs *)
  Definition BΣ_triangle : coherence_triangle1 BΣ_assoc BΣ_lid.
  Proof.
    intros S1 S2. unfold BΣ_lid. unfold BΣ_assoc. simpl.
    unfold BΣ_assoc. unfold BΣ_lid.
    simpl. 
    trunc_rewrite (canonical_BΣ S1). trunc_rewrite (canonical_BΣ S2).
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
