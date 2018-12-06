Require Import HoTT.
Require Import UnivalenceAxiom.
(* Load finite_lemmas. *)
Require Import equiv_lemmas.
Require Import path_lemmas.
Require Import trunc_lemmas.

(*Defining the type of monoidal 1-Types (this corresponds to a monoidal category*)

Definition associative {A : Type}  (m : A-> A -> A) := forall (a b c: A),  m (m a b) c = m a (m b c).
Definition left_identity_mult {A : Type} (m : A->A->A) (e : A) := forall a : A, m e a = a.
Definition right_identity_mult {A : Type} (m : A->A->A) (e : A) := forall a : A, m a e = a.

(* Unneccesary but perhaps easier to just assume *)
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
                                  mon_mult  : mon_type->mon_type->mon_type;
                                  mon_id : mon_type;
                                  mon_assoc : associative mon_mult;
                                  mon_lid : left_identity_mult mon_mult mon_id ;
                                  mon_rid : right_identity_mult mon_mult mon_id ;
                                  mon_triangle1 : coherence_triangle1 mon_assoc mon_lid ;
                                  mon_triangle2 : coherence_triangle2 mon_assoc mon_lid mon_rid ;
                                  mon_pentagon : coherence_pentagon mon_assoc
                                }.

Global Arguments mon_mult {M} a b : rename.
Global Arguments mon_id {M} : rename.
Global Arguments mon_assoc {M} a b c : rename.
Global Arguments mon_lid {M} a : rename.
Global Arguments mon_rid {M} a : rename.


Infix "⊗" := mon_mult (at level 50,no associativity).

Definition left_faithful {A B : Type} (m : A -> B -> B) :=
  forall (s t : A) (p q : s = t) (b : B),
                 ap (fun x => m x b) p = ap (fun x => m x b) q -> p = q.



Section Monoidal_Map.
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
         
  Global Arguments mon_map_mult {M N} F a b : rename.
  Global Arguments mon_map_id {M N} F : rename.
  Global Arguments mon_map_assoc {M N} F a b c : rename.
  Global Arguments mon_map_lid {M N} F a : rename.
  Global Arguments mon_map_rid {M N} F a : rename.

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

  Lemma path_arrow_V {A B : Type} {f g : A -> B} (H : f == g) :
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
  
  Definition to_endomorphism (M : Monoidal_1Type) : Monoidal_Map M (endomorphism M).
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

             
  Definition old_act_on_prod (M : Monoidal_1Type) (X Y: 1-Type) (a1 : Monoidal_Map M (endomorphism X)) (a2 : Monoidal_Map M (endomorphism Y)):
    Monoidal_Map M (endomorphism (BuildTruncType 1 (X*Y))).
  Proof.
    srapply @Build_Monoidal_Map.
    - simpl. intro s.
      apply (functor_prod (a1 s) (a2 s)).
    - intros s t. simpl.
      apply (ap011 functor_prod (mon_map_mult a1 _ _) (mon_map_mult a2 _ _)).
    - apply (ap011 functor_prod (mon_map_id a1) (mon_map_id a2)).
    - intros s t u. simpl.
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
      + cut (forall (f1 f2 : X -> X) (g1 g2 : Y -> Y) (p : f1 = f2) (q : g1 = g2),
                ap011 functor_prod (ap (fun f => f o (a1 u)) p) (ap (fun g => g o (a2 u)) q) =
                ap (fun f => f o (functor_prod (a1 u) (a2 u))) (ap011 functor_prod p q)).
        { intro H. apply H. }
        by path_induction.
      + simpl.
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
End Monoidal_Map.

Section Monoidal_Action.
  (* Definition monoidal_action (M : Monoidal_1Type) (X : 1-Type) := Monoidal_Map M (endomorphism X). *)

  Record monoidal_action (M : Monoidal_1Type) (X : 1-Type) :=
    { act :> M -> X -> X;
      mon_act_mult : forall (s t : M) (x : X), act (s ⊗ t) x = act s (act t x) ;
      mon_act_id : forall x : X, act mon_id x = x;
      mon_act_triangle1 : forall (a : M) (x : X),
          ap (fun m : M => act m x) (mon_lid a) = mon_act_mult mon_id a x @ mon_act_id (act a x);
      mon_act_triangle2 : forall (a : M) (x : X),
          ap (fun m : M => act m x) (mon_rid a) = mon_act_mult a mon_id x @ ap (fun y : X => act a y) (mon_act_id x);
      mon_act_pentagon : forall (a b c : M) (x : X),
          ap (fun m : M => act m x) (mon_assoc a b c) =
          mon_act_mult (a ⊗ b) c x @ mon_act_mult a b (act c x) @ (ap (act a) (mon_act_mult b c x))^ @ (mon_act_mult a (b ⊗ c) x)^ }.

  Global Arguments mon_act_mult {M} {X} a s t x : rename.
  Global Arguments mon_act_id {M} {X} a x : rename.
             

  Definition action_on_path {M} {X} (a : monoidal_action M X) {s t : M} (x : X) (p : s = t)  := ap (fun s => a s x) p.


  Definition act_on_self (M : Monoidal_1Type) : monoidal_action M M.
  Proof.
    srapply @Build_monoidal_action.
    - exact mon_mult.
    - apply mon_assoc.
    - apply mon_lid.
    - apply mon_triangle1.
    - apply mon_triangle2.
    - apply mon_pentagon.
  Defined.

  Definition endomorphism_to_action (M : Monoidal_1Type) (X : 1-Type) (F : Monoidal_Map M (endomorphism X)):
    monoidal_action M X.
  Proof.
    srapply @Build_monoidal_action.
    - exact F.
    - intros s t. apply ap10.
      apply (mon_map_mult F).
    - apply ap10.
      apply (mon_map_id F).
    - intros a x.      
      refine (ap_compose F (fun f => f x) (mon_lid a) @ _).
      rewrite mon_map_lid.
      repeat rewrite ap_pp. simpl. rewrite concat_p1.
      rewrite <- (ap_compose (fun (s : X -> X) (x0 : X) => s (F a x0)) (fun f : X -> X => f x) (mon_map_id F)). simpl.
      rewrite ap_apply_l. rewrite ap_apply_l. reflexivity.
    - intros a x.
      refine (ap_compose F (fun f => f x) (mon_rid a) @ _).
      rewrite mon_map_rid.
      repeat rewrite ap_pp. simpl. rewrite concat_p1.
      rewrite ap_apply_l. apply whiskerL.
      rewrite ap_apply_l.
      apply (ap10_ap_postcompose (F a) (mon_map_id F) x).
    - intros a b c x. simpl.
      refine (ap_compose F (fun f => f x) (mon_assoc a b c) @ _).
      rewrite mon_map_assoc.
      repeat rewrite ap_pp. simpl. rewrite concat_p1.
      rewrite ap_apply_l. rewrite ap_apply_l. rewrite ap_apply_l. rewrite ap_apply_l.
      apply concat2. apply concat2. apply whiskerL.
      + apply (ap10_ap_precompose (F c) (mon_map_mult F a b) x ).
      + rewrite ap10_V. apply (ap inverse).
        apply (ap10_ap_postcompose (F a) (mon_map_mult F b c) x).
      + apply (ap10_V (mon_map_mult F a (b ⊗ c)) x).
  Defined.

  Definition monmap_to_action {M : Monoidal_1Type} {X : Monoidal_1Type} (F : Monoidal_Map M X) :
    monoidal_action M X.
  Proof.
    apply endomorphism_to_action.
    apply (monoidal_map_compose M X (endomorphism X) F).
    apply (to_endomorphism).
  Defined.
  
  Definition path_prod_VV {A B : Type} (z z' : A*B) (p1 : fst z = fst z') (p2 : snd z = snd z') :
    path_prod z' z p1^ p2^ = (path_prod z z' p1 p2)^.
  Proof.
    destruct z as [z1 z2]. destruct z' as [z1' z2']. simpl in *. destruct p1, p2. reflexivity.
  Defined.
  

  Definition act_on_prod (M : Monoidal_1Type) (X Y: 1-Type) (act1 : monoidal_action M X) (act2 : monoidal_action M Y) :
    monoidal_action M (BuildTruncType 1 (X*Y)).
  Proof.
    srapply @Build_monoidal_action; simpl.
    - intro s.
      apply (functor_prod (act1 s) (act2 s)).
    - simpl. intros s t x.
      apply path_prod; apply mon_act_mult.
    - simpl. intro x.
      apply path_prod; apply mon_act_id.
    - simpl. intros s x.
      transitivity (path_prod (_,_) (_,_) (ap (fun m : M => act1 m (fst x)) (mon_lid s)) (ap (fun m : M => act2 m (snd x)) (mon_lid s))).
      { destruct (mon_lid s). reflexivity. }
      refine (_ @ path_prod_pp _ _ _ _ _ _ _).      
      apply (ap011 (path_prod _ _)); apply mon_act_triangle1.
    - intros s x. simpl.
      transitivity (path_prod (_,_) (_,_) (ap (fun m : M => act1 m (fst x)) (mon_rid s)) (ap (fun m : M => act2 m (snd x)) (mon_rid s))).
      { destruct (mon_rid s). reflexivity. }
      refine (_ @ whiskerL _ (ap_functor_prod _ _ _ _ _ _)^).      
      refine (_ @ path_prod_pp _ _ _ _ _ _ _).
      apply (ap011 (path_prod _ _)); apply mon_act_triangle2.
    - intros a b c x. simpl.
      transitivity (path_prod (_,_) (_,_)
                              (ap (fun m : M => act1 m (fst x)) (mon_assoc a b c)) (ap (fun m : M => act2 m (snd x)) (mon_assoc a b c))).
      { destruct (mon_assoc a b c). reflexivity. }
      rewrite (ap_functor_prod).
      repeat rewrite <- path_prod_VV.
      repeat rewrite <- path_prod_pp.
      apply (ap011 (path_prod _ _)); apply mon_act_pentagon.
  Defined.

  (* Definition act_from_monmap (M X : Monoidal_1Type) (F : Monoidal_Map M X) : *)
  (*   monoidal_action M X. *)
  (* Proof. *)
  (*   srapply @Build_monoidal_action. *)
  (*   - intros m x. exact ((F m) ⊗ x). *)
  (*   - intros s t x. simpl. *)
  (*     refine (ap (fun y => y ⊗ x) (mon_map_mult F s t) @ _). *)
  (*     apply mon_assoc. *)
  (*   - intro x. simpl. *)
  (*     exact (ap (fun y => y ⊗ x) (mon_map_id F) @ (mon_lid x)). *)
  (*   - intros a x. simpl. *)
  (*     refine (ap_compose F (fun y : X => y ⊗ x) (mon_lid a) @ _). *)
  (*     rewrite mon_map_lid. *)
  (*     repeat rewrite ap_pp. *)
  (*     rewrite mon_triangle1. *)
  (*     repeat rewrite concat_p_pp. apply whiskerR. *)
  (*     repeat rewrite concat_pp_p. apply whiskerL. *)
  (*     rewrite <- (ap_compose (fun s : X => s ⊗ F a) (fun y : X => y ⊗ x)). *)
  (*     destruct (mon_map_id F). simpl. *)
  (*     destruct (mon_assoc (F mon_id) (F a) x). reflexivity. *)
  (*   - intros a x. simpl. *)
  (*     refine (ap_compose F (fun y : X => y ⊗ x) (mon_rid a) @ _). *)
  (*     rewrite mon_map_rid. *)
  (*     repeat rewrite ap_pp. *)
  (*     rewrite mon_triangle2. *)
  (*     repeat rewrite concat_p_pp. apply whiskerR. *)
  (*     repeat rewrite concat_pp_p. apply whiskerL. *)
  (*     rewrite <- (ap_compose (mon_mult (F a)) (fun y : X => y ⊗ x)). *)
  (*     destruct (mon_map_id F). simpl. *)
  (*     destruct (mon_assoc (F a) (F mon_id)  x). reflexivity. *)
  (*   - intros a b c x. simpl. *)
  (*     refine (ap_compose F (fun y : X => y ⊗ x) (mon_assoc a b c) @ _). *)
  (*     rewrite mon_map_assoc. *)
  (*     repeat rewrite ap_pp. *)
  (*     rewrite mon_pentagon. *)
  (*     repeat rewrite concat_pp_p. apply whiskerL. *)
      
  (*     repeat rewrite concat_p_pp. apply whiskerR. *)


      
      
  (*     refine (ap_pp _ _ _ @ _). *)
      
  (*     refine (mon_triangle1 M _ _ @ _). *)
    

    
End Monoidal_Action.


Section Symmetric_Monoidal_1Type.
  
  Definition symmetric {A : Type} (m : A->A->A) := forall a b : A, m a b = m b a.
  Definition coherence_hexagon {A : Type} {m : A -> A -> A} (assoc : associative m) (symm : symmetric m) :=
    forall (a b c : A),
    ap (fun x : A => m x c) (symm a b) =
           assoc a b c @ symm a (m b c) @ assoc b c a @ (ap (m b) (symm a c))^ @ (assoc b a c)^.

  Record Symmetric_Monoidal_1Type : Type :=
    { smon_type :> 1-Type;
      smon_mult  : smon_type -> smon_type -> smon_type;
      smon_id : smon_type;
      smon_assoc : associative smon_mult;
      smon_lid : left_identity_mult smon_mult smon_id ;
      smon_rid : right_identity_mult smon_mult smon_id ;
      smon_sym : symmetric smon_mult ;
      smon_sym_inv : forall a b : smon_type, smon_sym a b = (smon_sym b a)^;
      smon_triangle1 : coherence_triangle1 smon_assoc smon_lid ;
      smon_triangle2 : coherence_triangle2 smon_assoc smon_lid smon_rid ;
      smon_pentagon : coherence_pentagon smon_assoc;
      smon_hexagon : coherence_hexagon smon_assoc smon_sym                                         
    }.
  Global Arguments smon_mult {S} a b : rename.
  Global Arguments smon_id {S} : rename.
  Global Arguments smon_assoc {S} a b c : rename.
  Global Arguments smon_lid {S} a : rename.
  Global Arguments smon_rid {S} a : rename.
  Global Arguments smon_sym {S} a b : rename.

  Definition forget_symmetry : Symmetric_Monoidal_1Type -> Monoidal_1Type :=
    fun S => Build_Monoidal_1Type S smon_mult smon_id smon_assoc smon_lid smon_rid
                                  (smon_triangle1 S) (smon_triangle2 S) (smon_pentagon S).

  Coercion forget_symmetry : Symmetric_Monoidal_1Type >-> Monoidal_1Type.



End Symmetric_Monoidal_1Type.

  



     
                   
  
  