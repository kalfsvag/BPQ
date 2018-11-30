Require Import HoTT.
Require Import UnivalenceAxiom.
Load finite_lemmas.
Load equiv_lemmas.
Load path_lemmas.

Section Type_to_Cat.
  Require Import HoTT.Categories Category.Morphisms.
  
  Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
  Definition Type_to_Cat : 1-Type -> PreCategory.
  Proof.
    intro X.
    srapply (Build_PreCategory (fun x y : X => x = y)).
    - reflexivity.
    - cbn. intros x y z p q.
      exact (q @ p).
    - intros x1 x2 x3 x4 p q r. simpl. apply concat_p_pp.
    - cbn. intros x1 x2 p. apply concat_p1.
    - intros x y p. simpl. apply concat_1p.
  Defined.

  Global Instance isgroupoid_type_to_cat (X : 1-Type) (x1 x2 : (Type_to_Cat X)) (f : x1 --> x2) :
    IsIsomorphism f.
  Proof.
    srapply @Build_IsIsomorphism.
    - exact f^.
    - apply concat_pV.
    - apply concat_Vp.
  Defined.
    

  Definition arrow_to_functor {X Y : 1-Type} (F : X -> Y) :
    Functor (Type_to_Cat X) (Type_to_Cat Y).
  Proof.
    srapply @Build_Functor. exact F.
    - intros x1 x2. simpl.
      exact (ap F).
    - simpl. intros x1 x2 x3 p q.
      apply ap_pp.
    - simpl. reflexivity.
  Defined.

  Definition cat_of_arrow (X Y : 1-Type) :
    Functor (Type_to_Cat (BuildTruncType 1 (X -> Y))) (functor_category (Type_to_Cat X) (Type_to_Cat Y)).
  Proof.
    srapply @Build_Functor; simpl.
    apply arrow_to_functor.
    - intros f g p.
      srapply @Build_NaturalTransformation; simpl.
      + apply (ap10 p).
      + intros x1 x2 q.
        destruct p, q. reflexivity.        
    - intros f g h p q. simpl.
      unfold NaturalTransformation.Composition.Core.compose. simpl. destruct p, q. simpl.
      apply NaturalTransformation.path_natural_transformation. simpl. intro x. reflexivity.
    - intro f. simpl.
      apply NaturalTransformation.path_natural_transformation. simpl. intro x. reflexivity.
  Defined.
End Type_to_Cat.


        
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
    
Section Localize.
  Require Import HoTT.Categories.
  (* if we have a monoidal action with left_cancellation, we can build a category with objects X and arrows*)
  (* {m : M & m ⊗ x = m ⊗ y} *)
  Definition monoidal_action_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) :
    (X -> X -> Type) := fun x y => {s : M & a s x = y}.

  Instance isset_mon_morphism (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X) (x1 x2 : X)
           (left_cancel : left_faithful a)
    (* (left_cancel : forall (s t : M) (p q : s = t) (x : X), *)
    (*              action_on_path a x p = action_on_path a x q -> p = q)  *):
    IsHSet (monoidal_action_morphism M X a x1 x2).
  Proof.
    unfold monoidal_action_morphism.
    intros [s1 p1] [s2 p2].
    apply (trunc_equiv' {q : s1 = s2 & transport (fun s => a s x1 = x2) q p1 = p2}).
    { apply equiv_inverse. apply equiv_path_sigma. }
    (* apply (trunc_equiv' {q : s1 = s2 & p1 = (ap (fun s => a s x1) q) @ p2}). *)
    apply (trunc_equiv' {q : s1 = s2 & p1 = action_on_path a x1 q @ p2}).
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

  Definition monoidal_action_cat (M : Monoidal_1Type) (X : 1-Type) (a : monoidal_action M X)
             (left_cancel : left_faithful a)
             (* (left_cancel : forall (s t : M) (p q : s = t) (x : X), *)
             (*     action_on_path a x p = action_on_path a x q -> p = q) *)
    : PreCategory.
  Proof.
    srefine (Build_PreCategory (monoidal_action_morphism M X a) _ _ _ _ _ (fun x1 x2 => isset_mon_morphism M X a x1 x2 left_cancel)).
    (* identity *)
    - intro x. exists mon_id. apply mon_act_id.
    (* composition *)
    - intros x y z.
      intros [s1 p1] [s2 p2].
      exists (s1 ⊗ s2).
      exact (mon_act_mult a s1 s2 x @ ap (a s1) p2 @ p1).
    (* associativity *)
    - intros x1 x2 x3 x4 [s1 []] [s2 []] [s3 []]. repeat rewrite ap_1. repeat rewrite concat_p1.
      srapply @path_sigma. apply mon_assoc. cbn.
      refine (transport_paths_Fl (mon_assoc s3 s2 s1) _ @ _).
      rewrite mon_act_pentagon. repeat rewrite inv_pp. repeat rewrite inv_V.
      apply moveR_pM.
      repeat rewrite concat_pp_p. apply whiskerL. apply whiskerL.
      apply inverse. apply inv_pp.
    (* left identity *)
    - simpl.
      intros x1 x2 [s []]. simpl. rewrite concat_p1.
      srapply @path_sigma. apply mon_lid. simpl. 
      refine (transport_paths_Fl (mon_lid s) _ @ _).
      apply moveR_Vp. refine (_ @ (concat_p1 _)^). apply inverse.
      apply mon_act_triangle1.
    (* right identity *)
    - simpl.
      intros x1 x2 [s []]. simpl. rewrite concat_p1.
      srapply @path_sigma. apply mon_rid. simpl. 
      refine (transport_paths_Fl (mon_rid s) _ @ _).
      apply moveR_Vp. refine (_ @ (concat_p1 _)^). apply inverse.
      apply mon_act_triangle2.
  Defined.

  Definition localize_action (M : Monoidal_1Type) (X : 1-Type) (act : monoidal_action M X)
             (left_cancel : left_faithful (@mon_mult M))
             (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q)  *): PreCategory.
  Proof.
    apply (monoidal_action_cat M (BuildTruncType 1 (M*X)) (act_on_prod M M X (act_on_self M) act)). simpl.
    intros s t p q [a x].
    unfold action_on_path. simpl.
    intro H. apply (left_cancel s t p q a). 
    refine ((ap_fst_path_prod (z := (s ⊗ a, act s x )) (z' := (t ⊗ a, act t x ))
                (ap (fun m : M => m ⊗ a) p) (ap (fun m : M => act m x) p))^ @ _ @
             ap_fst_path_prod (z := (s ⊗ a, act s x )) (z' := (t ⊗ a, act t x ))
                (ap (fun m : M => m ⊗ a) q) (ap (fun m : M => act m x) q)). 
    apply (ap (ap fst)).
    refine (_ @ H @ _).
    - destruct p. reflexivity.
    - destruct q. reflexivity.
  Defined.    

  Definition group_completion (M : Monoidal_1Type)
             (left_cancel : left_faithful (@mon_mult M))
             (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *) : PreCategory :=
    localize_action M M (act_on_self M) left_cancel.

  Definition contr_self_category (M : Monoidal_1Type)
             (left_cancel : left_faithful (@mon_mult M))
             (* (left_cancel : forall (s t : M) (p q : s = t) (a : M), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *)
    : forall x : object (monoidal_action_cat M M (act_on_self M) left_cancel),
      Contr (morphism (monoidal_action_cat M M (act_on_self M) left_cancel) mon_id x).
  Proof.
    simpl. intro a. unfold monoidal_action_morphism. unfold act_on_self. simpl.
    apply (contr_equiv' {s : M & s = a}).
    - srapply @equiv_functor_sigma'. exact equiv_idmap.
      intro m. simpl.
      apply equiv_concat_l. apply mon_rid.
    - apply contr_basedpaths'.
  Defined.

  Definition ap_homotopy_idmap {A : Type} (f : A -> A) (h : f == idmap) (a : A):
    ap f (h a) = h (f a).
  Proof.
    cut (forall p : f a = a,
              ap f p = h (f a) @ p @ (h a)^).
    - intro H. refine (H (h a) @ _).
      refine (concat_pp_p _ _ _ @ _). 
      refine (whiskerL _ (concat_pV _) @ _). apply concat_p1.
    - intros []. destruct (h (f a)). reflexivity.
  Defined.    
  
  (* Definition ap_homotopic_idmap {A : Type} (f : A -> A) (h : f == idmap) {a b : A} (p : a = b) : *)
  (*   ap f p = (h a) @ p @ (h b)^. *)
  (* Proof. *)
  (*   destruct p. destruct (h a). reflexivity. *)
  (* Defined. *)

  Definition prod_to_groupcompletion (S : Monoidal_1Type)
             (left_cancel : left_faithful (@mon_mult S))
             (* (left_cancel : forall (s t : S) (p q : s = t) (a : S), *)
             (*     ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *):
    Functor ((Type_to_Cat S)*(Type_to_Cat S))%category (group_completion S left_cancel).
  Proof.
    srapply @Build_Functor; simpl. exact idmap.
    - intros a b [p q].
      unfold monoidal_action_morphism.
      exists mon_id. apply path_prod. apply (mon_lid _ @ p). apply (mon_lid _ @ q).
    - intros [a1 a2] [b1 b2] [c1 c2] [p1 p2] [q1 q2]. simpl in *.
      destruct q2, q1, p2, p1. simpl. repeat rewrite concat_p1.
      srapply @path_sigma;simpl. apply inverse. apply mon_lid. 
      refine (transport_paths_Fl (mon_lid mon_id)^
              (path_prod (functor_prod (mon_mult mon_id) (mon_mult mon_id) (a1, a2)) (a1, a2) (mon_lid a1) (mon_lid a2)) @ _).
      rewrite ap_V. rewrite inv_V.
      apply whiskerR.
      transitivity (path_prod ((mon_id ⊗ mon_id) ⊗ a1, (mon_id ⊗ mon_id) ⊗ a2) (_,_)

                              (ap (fun x : S => mon_mult x a1) (mon_lid mon_id)) (ap (fun x : S => mon_mult x a2) (mon_lid mon_id))).
      { destruct (mon_lid mon_id). reflexivity. }
      rewrite ap_functor_prod.
      rewrite <- path_prod_pp.
      apply (ap011 (path_prod _ _));
      refine (mon_triangle1 S mon_id _ @ _); apply whiskerL;
      apply inverse; simpl; apply ap_homotopy_idmap.
    - intro x. simpl. rewrite concat_p1. rewrite concat_p1. reflexivity.
  Defined.

  Definition to_prod (C : PreCategory) :
    Functor C (C*C)%category.
  Proof.
    apply Functor.prod; apply Functor.identity.
  Defined.
  
  Definition to_groupcompletion (S : Monoidal_1Type)
             (left_cancel : left_faithful (@mon_mult S))
           (* (left_cancel : forall (s t : S) (p q : s = t) (a : S), *)
           (*       ap (fun x => x ⊗ a) p = ap (fun x => x ⊗ a) q -> p = q) *):
  Functor (Type_to_Cat S) (group_completion S left_cancel) :=
    Functor.compose (prod_to_groupcompletion S left_cancel) (to_prod _).

End Localize.

Section Symmetric_Monoidal_Category.
  
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



End Symmetric_Monoidal_Category.
      

Section Monoidal_Category.
  Require Import Category.Morphisms.
  Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
  Open Scope morphism.

  Definition BiFunctor (A B C : PreCategory) :=
    Functor A (functor_category B C).

  Definition morphism_of_1 {A B C : PreCategory} (F : BiFunctor A B C)
             {a a' : A} (f : a --> a') (b : B)  :
    F a b --> F a' b :=
    morphism_of F f b.

  Definition morphism_of_2 {A B C : PreCategory} (F : BiFunctor A B C)
             (a : A) {b b' : B} (g : b --> b') :
    F a b --> F a b' :=
    morphism_of (F a) g.

  Definition morphism_of_12 {A B C : PreCategory} (F : BiFunctor A B C)
             {a a' : A} (f : a --> a') {b b' : B} (g : b --> b') :
    F a b --> F a' b' :=
    (morphism_of_2 F a' g) o (morphism_of_1 F f b).
  (* Could define it the other way as well. . . *)    
    

  Record Monoidal_Category :=
    {moncat : PreCategory;
     moncat_mult : BiFunctor moncat moncat moncat;
     moncat_id : moncat;
     
     moncat_assoc : forall a b c : moncat,
          (moncat_mult (moncat_mult a b) c) --> (moncat_mult a (moncat_mult b c));
     natl_assoc : forall (a b c a' b' c' : moncat)
                         (f : a --> a') (g : b --> b') (h : c --> c'),
         morphism_of_12 moncat_mult f (morphism_of_12 moncat_mult g h) o moncat_assoc a b c =
         moncat_assoc a' b' c' o morphism_of_12 moncat_mult (morphism_of_12 moncat_mult f g) h;
     iso_assoc : forall a b c : moncat,
         IsIsomorphism (moncat_assoc a b c);
     
     moncat_lid : forall a : moncat,
         (moncat_mult moncat_id a) --> a;
     natl_lid : forall (a a' : moncat) (f : a --> a'),
         f o (moncat_lid a) = (moncat_lid a') o (morphism_of_2 moncat_mult moncat_id f);
     iso_lid : forall a : moncat,
         IsIsomorphism (moncat_lid a);
     
     moncat_rid : forall a : moncat,
         (moncat_mult a moncat_id) -->  a;
     natl_rid : forall (a a' : moncat) (f : a --> a'),
         f o (moncat_rid a) = (moncat_rid a') o (morphism_of_1 moncat_mult f moncat_id);
     iso_rid : forall a : moncat,
         IsIsomorphism (moncat_rid a);

     moncat_triangle1 : forall (a b : moncat),
         morphism_of_1 moncat_mult (moncat_lid a) b = moncat_lid (moncat_mult a b) o moncat_assoc moncat_id a b;
     moncat_triangle2 : forall (a b : moncat),
         morphism_of_1 moncat_mult (moncat_rid a) b = morphism_of_2 moncat_mult a (moncat_lid b) o moncat_assoc a moncat_id b;

     moncat_pentagon : forall (a b c d : moncat),
         morphism_of_1 moncat_mult (moncat_assoc a b c) d =
         (moncat_assoc a (moncat_mult b c) d)^-1 o ((morphism_of_2 moncat_mult a (moncat_assoc b c d))^-1 o
         (moncat_assoc a b (moncat_mult c d) o moncat_assoc (moncat_mult a b) c d))

    }.

    
  Infix "⊗" := smon_mult (at level 50,no associativity).
  Definition moncat_of_montype : Monoidal_1Type -> Monoidal_Category.
  Proof.
    
    intros [S m e assoc lid rid triangle1 triangle2 pentagon].
    refine
      (Build_Monoidal_Category (Type_to_Cat S) (cat_of_arrow S S o (arrow_to_functor m))%functor e assoc _ _ lid _ _ rid _ _ _ _ _); simpl.
    - intros a b c a' b' c' [] [] []. simpl. destruct (assoc a b c). reflexivity.
    - intros a a' []. destruct (lid a). reflexivity.
    - intros a a' []. destruct (rid a). reflexivity.
    - intros a b. refine (_ @ triangle1 a b).
      unfold morphism_of_1. simpl.
      destruct (lid a). reflexivity.
    - intros a b. refine (_ @ triangle2 a b).
      unfold morphism_of_1. simpl.
      destruct (rid a). reflexivity.
    - intros a b c d.
      unfold morphism_of_1. simpl.
      refine (_ @ pentagon a b c d @ _).
      + destruct (assoc a b c). reflexivity.
      + apply whiskerR. apply whiskerL.
        destruct (assoc b c d). reflexivity.      
  Defined.

  (* Definition moncat_action_category (S : Symmetric_Monoidal_1Type) (X : Monoidal_1Type) (F : Monoidal_Map S X) *)
  (*            (left_cancel : forall (s t : S) (p q : s = t) (a : S), *)
  (*                ap (fun x => smon_mult x a) p = ap (fun x => smon_mult x a) q -> p = q) : Monoidal_Category. *)
  (* Proof. *)
  (*   srefine (Build_Monoidal_Category (monoidal_action_cat S X (monmap_to_action F) left_cancel) _ _ _ _ (fun a b c => Build_IsIsomorphism _ _ _ _ _ _ _) *)
  (*                                    _ _ (fun a => Build_IsIsomorphism _ _ _ _ _ _ _) _ _ (fun a => Build_IsIsomorphism _ _ _ _ _ _ _)). *)
  Lemma ap_homotopy {A B : Type} {a b : A} (p : a = b) (f g : A -> B) (H : g == f) :
    ap f p = (H a)^ @ (ap g p) @ (H b).
  Proof.
    destruct p. simpl. destruct (H a). reflexivity.
  Defined.

  Lemma grp_complete_bifun_lem1' (S : Symmetric_Monoidal_1Type) (a b s t : S) :
      (((smon_assoc (t ⊗ s) a b)^ @ ap (fun x : S => x ⊗ b) (smon_sym (t ⊗ s) a)) @ smon_assoc a (t ⊗ s) b) @
           ap (smon_mult a) (smon_assoc t s b) =
      (smon_assoc t s (a ⊗ b) @ ap (smon_mult t) (((smon_assoc s a b)^ @ ap (fun x : S => x ⊗ b) (smon_sym s a)) @ smon_assoc a s b))
        @ (((smon_assoc t a (s ⊗ b))^ @ ap (fun x : S => x ⊗ (s ⊗ b)) (smon_sym t a)) @ smon_assoc a t (s ⊗ b)).
  Proof.
    repeat rewrite ap_pp. rewrite ap_V.
    assert (p : ap (smon_mult t) (ap (fun x : S => x ⊗ b) (smon_sym s a)) =
                (smon_assoc t (s ⊗ a) b)^ @ ap (fun x : S => x ⊗ b) (ap (fun x : S => t ⊗ x) (smon_sym s a)) @ smon_assoc t (a ⊗ s) b).
    destruct (smon_sym s a). simpl.
    destruct (smon_assoc t (s ⊗ a) b). simpl.  reflexivity.
    rewrite p. clear p. repeat rewrite concat_pp_p.
    assert (p : ap (fun x : S => x ⊗ (s ⊗ b)) (smon_sym t a) =
                (smon_assoc (t ⊗ a) s b)^ @ ap (fun x : S => x ⊗ b) (ap (fun x : S => x ⊗ s) (smon_sym t a)) @ smon_assoc (a ⊗ t) s b).
    destruct (smon_sym t a). simpl.
    destruct (smon_assoc (t ⊗ a) s b). simpl. reflexivity.
    rewrite p. clear p.
    rewrite (smon_sym_inv S t a). repeat rewrite ap_V.
    rewrite (smon_hexagon S a t s).
    repeat rewrite ap_pp. repeat rewrite ap_V.
    repeat rewrite concat_pp_p.
    repeat rewrite (smon_pentagon).
    repeat rewrite inv_pp. repeat rewrite inv_V.
    repeat rewrite concat_pp_p.
    repeat rewrite concat_V_pp. rewrite concat_Vp. rewrite concat_p1.
    rewrite concat_p_Vp. rewrite concat_p_Vp.
    rewrite (smon_sym_inv S a (t ⊗ s)). rewrite ap_V. rewrite inv_V.
    rewrite (smon_sym_inv S s a). rewrite ap_V. rewrite ap_V.
    repeat rewrite concat_V_pp. 
    repeat rewrite concat_p_pp. repeat apply whiskerR. rewrite concat_pV.
    apply inverse. apply concat_1p.
  Qed.

  Lemma grp_complete_bifun_lem1 
        (S : Symmetric_Monoidal_1Type)
        (a1 a2 b1 b2 : S) (c d : S * S) (s : S)
        (p : functor_prod (smon_mult s) (smon_mult s) (b1, b2) = c) (t : S)
        (q : functor_prod (smon_mult t) (smon_mult t) c = d) : 
    path_prod ((t ⊗ s) ⊗ (a1 ⊗ b1), (t ⊗ s) ⊗ (a2 ⊗ b2)) (a1 ⊗ ((t ⊗ s) ⊗ b1), a2 ⊗ ((t ⊗ s) ⊗ b2))
              (((smon_assoc (t ⊗ s) a1 b1)^ @ ap (fun x : S => x ⊗ b1) (smon_sym (t ⊗ s) a1)) @ smon_assoc a1 (t ⊗ s) b1)
              (((smon_assoc (t ⊗ s) a2 b2)^ @ ap (fun x : S => x ⊗ b2) (smon_sym (t ⊗ s) a2)) @ smon_assoc a2 (t ⊗ s) b2) @
              ap (functor_prod (smon_mult a1) (smon_mult a2))
              ((path_prod (functor_prod (smon_mult (t ⊗ s)) (smon_mult (t ⊗ s)) (b1, b2))
                          (functor_prod (smon_mult t) (smon_mult t) (functor_prod (smon_mult s) (smon_mult s) (b1, b2)))
                          (smon_assoc t s b1) (smon_assoc t s b2) @ ap (functor_prod (smon_mult t) (smon_mult t)) p) @ q) =
    (path_prod (functor_prod (smon_mult (t ⊗ s)) (smon_mult (t ⊗ s)) (functor_prod (smon_mult a1) (smon_mult a2) (b1, b2)))
               (functor_prod (smon_mult t) (smon_mult t)
                             (functor_prod (smon_mult s) (smon_mult s) (functor_prod (smon_mult a1) (smon_mult a2) (b1, b2))))
               (smon_assoc t s (a1 ⊗ b1)) (smon_assoc t s (a2 ⊗ b2)) @
               ap (functor_prod (smon_mult t) (smon_mult t))
               (path_prod (s ⊗ (a1 ⊗ b1), s ⊗ (a2 ⊗ b2)) (a1 ⊗ (s ⊗ b1), a2 ⊗ (s ⊗ b2))
                          (((smon_assoc s a1 b1)^ @ ap (fun x : S => x ⊗ b1) (smon_sym s a1)) @ smon_assoc a1 s b1)
                          (((smon_assoc s a2 b2)^ @ ap (fun x : S => x ⊗ b2) (smon_sym s a2)) @ smon_assoc a2 s b2) @
                          ap (functor_prod (smon_mult a1) (smon_mult a2)) p))
      @ (path_prod (t ⊗ (a1 ⊗ fst c), t ⊗ (a2 ⊗ snd c)) (a1 ⊗ (t ⊗ fst c), a2 ⊗ (t ⊗ snd c))
                   (((smon_assoc t a1 (fst c))^ @ ap (fun x : S => x ⊗ (let (fst, _) := c in fst))
                                                  (smon_sym t a1)) @ smon_assoc a1 t (fst c))
                   (((smon_assoc t a2 (snd c))^ @ ap (fun x : S => x ⊗ (let (_, snd) := c in snd)) (smon_sym t a2))
                      @ smon_assoc a2 t (snd c))
                   @ ap (functor_prod (smon_mult a1) (smon_mult a2)) q).
  Proof.
    destruct p,q.    
    repeat rewrite ap_pp.
    repeat rewrite ap_functor_prod. simpl. repeat rewrite concat_p1. 
    repeat rewrite <- path_prod_pp.
    apply (ap011 (path_prod _ _)); apply grp_complete_bifun_lem1'.
  Qed.

  Lemma grp_complete_bifun_lem2 (S : Symmetric_Monoidal_1Type) (a b : S) :
            (((smon_assoc smon_id a b)^ @ ap (fun x : S => x ⊗ b) (smon_sym smon_id a)) @ smon_assoc a smon_id b)
              @ ap (smon_mult a) (smon_lid b) = smon_lid (a ⊗ b).
  Proof.
    rewrite smon_sym_inv. rewrite ap_V.
    rewrite smon_hexagon.
    rewrite inv_pp. rewrite inv_pp. rewrite inv_pp. rewrite inv_pp.
    rewrite inv_V. rewrite inv_V.
    repeat rewrite concat_pp_p.
    rewrite concat_V_pp. rewrite concat_V_pp.
    assert (natl : ap (smon_mult smon_id) (smon_sym a b) =
                       smon_lid (a ⊗ b) @ smon_sym a b @ (smon_lid (b ⊗ a))^).
    { destruct (smon_sym a b). destruct (smon_lid (a ⊗ b)). reflexivity. }
    rewrite natl. clear natl.
    assert (natl : smon_sym a (smon_id ⊗ b) =
                   ap (smon_mult a) (smon_lid b) @ smon_sym a b @ (ap (fun x => x ⊗ a) (smon_lid b))^).
    { destruct (smon_lid b). simpl.
      destruct (smon_sym a (smon_id ⊗ b)). reflexivity. }
    rewrite natl. clear natl.
    rewrite smon_triangle1.
    rewrite inv_pp. rewrite inv_pp. rewrite inv_pp. rewrite inv_pp. rewrite inv_V. rewrite inv_V. 
    repeat rewrite concat_pp_p.

    repeat rewrite concat_V_pp. rewrite concat_p_Vp. rewrite concat_Vp.
    apply concat_p1.
  Qed.

  Lemma grp_complete_bifun_lem3' (S : Symmetric_Monoidal_1Type) (a s c t : S):
    (ap (fun x : S => x ⊗ (a ⊗ c)) (smon_sym s t))^
    @ ((smon_assoc s t (a ⊗ c) @ (((ap (smon_mult s) (smon_assoc t a c))^
       @ ap (smon_mult s) (ap (fun x : S => x ⊗ c) (smon_sym t a)))
       @ ap (smon_mult s) (smon_assoc a t c))) @ (smon_assoc s a (t ⊗ c))^) =
          (smon_assoc t s (a ⊗ c) @ (ap (smon_mult t) (smon_assoc s a c))^)
            @ (((smon_assoc t (s ⊗ a) c)^ @ ap (fun x : S => x ⊗ c) (smon_sym t (s ⊗ a))) @ smon_assoc (s ⊗ a) t c).
  Proof.
    assert (p : (ap (fun x : S => x ⊗ (a ⊗ c)) (smon_sym s t)) =
                (smon_assoc (s ⊗ t) a c)^ @ ap (fun x : S => x ⊗ c) (ap (fun x : S => x ⊗ a) (smon_sym t s))^ @
                                                                                                                    (smon_assoc (t ⊗ s) a c)).
    { rewrite (smon_sym_inv S t s). destruct (smon_sym s t). simpl.
      destruct (smon_assoc (s ⊗ t) a c). reflexivity. }
    rewrite p. clear p.
    assert (p : ap (smon_mult s) (ap (fun x : S => x ⊗ c) (smon_sym t a)) =
                (smon_assoc s (t ⊗ a) c)^ @ ap (fun x => x ⊗ c) (ap (fun x => s ⊗ x) (smon_sym t a)) @
                                              smon_assoc s (a ⊗ t) c).
    { destruct (smon_sym t a). simpl.
      destruct (smon_assoc s (t ⊗ a) c). reflexivity. }
    rewrite p. clear p.                  
    repeat rewrite inv_pp. rewrite ap_V. repeat rewrite inv_V.
    rewrite (smon_hexagon S t s).
    repeat rewrite ap_pp. repeat rewrite ap_V. 
    repeat rewrite concat_pp_p.
    repeat rewrite smon_pentagon.
    repeat rewrite inv_pp. repeat rewrite inv_V.
    change (fun x : S => s ⊗ x) with (smon_mult s).
    repeat rewrite concat_pp_p.
    repeat rewrite concat_V_pp.
    repeat rewrite concat_p_Vp.
    repeat rewrite concat_V_pp.
    repeat apply whiskerL. rewrite concat_pV. apply concat_p1.
  Qed.

  Lemma grp_complete_bifun_lem3
        (S : Symmetric_Monoidal_1Type) (left_cancel : left_faithful mon_mult) (a1 a2 : S) (b : S * S) (s : S)
        (p : functor_prod (smon_mult s) (smon_mult s) (a1, a2) = b) (c1 c2 : S) (d : Core.object (group_completion S left_cancel)) 
        (t : S) (q : functor_prod (smon_mult t) (smon_mult t) (c1, c2) = d): 
    (ap (fun x : S => functor_prod (smon_mult x) (smon_mult x) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2))) (smon_sym s t))^
    @ ((path_prod (functor_prod (smon_mult (s ⊗ t)) (smon_mult (s ⊗ t)) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2)))
                  (functor_prod (smon_mult s) (smon_mult s)
                                (functor_prod (smon_mult t) (smon_mult t) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2))))
                  (smon_assoc s t (a1 ⊗ c1)) (smon_assoc s t (a2 ⊗ c2))
                  @ ap (functor_prod (smon_mult s) (smon_mult s)) (path_prod (t ⊗ (a1 ⊗ c1), t ⊗ (a2 ⊗ c2)) (a1 ⊗ (t ⊗ c1), a2 ⊗ (t ⊗ c2))
                    (((smon_assoc t a1 c1)^ @ ap (fun x : S => x ⊗ c1) (smon_sym t a1)) @ smon_assoc a1 t c1)
                    (((smon_assoc t a2 c2)^ @ ap (fun x : S => x ⊗ c2) (smon_sym t a2)) @ smon_assoc a2 t c2) @
                    ap (functor_prod (smon_mult a1) (smon_mult a2)) q))
         @ (path_prod (s ⊗ (a1 ⊗ fst d), s ⊗ (a2 ⊗ snd d)) ((s ⊗ a1) ⊗ fst d, (s ⊗ a2) ⊗ snd d) (smon_assoc s a1 (fst d))^
            (smon_assoc s a2 (snd d))^ @ ap (fun b0 : S * S => functor_prod (smon_mult (fst b0)) (smon_mult (snd b0)) d) p)) =
    (path_prod (functor_prod (smon_mult (t ⊗ s)) (smon_mult (t ⊗ s)) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2)))
               (functor_prod (smon_mult t) (smon_mult t)
                             (functor_prod (smon_mult s) (smon_mult s) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2))))
               (smon_assoc t s (a1 ⊗ c1)) (smon_assoc t s (a2 ⊗ c2)) @ ap (functor_prod (smon_mult t) (smon_mult t))
               (path_prod (s ⊗ (a1 ⊗ c1), s ⊗ (a2 ⊗ c2)) ((s ⊗ a1) ⊗ c1, (s ⊗ a2) ⊗ c2) (smon_assoc s a1 c1)^ (smon_assoc s a2 c2)^
                @ ap (fun b0 : S * S => functor_prod (smon_mult (fst b0)) (smon_mult (snd b0)) (c1, c2)) p))
      @ (path_prod (t ⊗ (fst b ⊗ c1), t ⊗ (snd b ⊗ c2)) (fst b ⊗ (t ⊗ c1), snd b ⊗ (t ⊗ c2))
                   (((smon_assoc t (fst b) c1)^ @ ap (fun x : S => x ⊗ c1) (smon_sym t (let (fst, _) := b in fst)))
                      @ smon_assoc (fst b) t c1)
                   (((smon_assoc t (snd b) c2)^ @ ap (fun x : S => x ⊗ c2) (smon_sym t (let (_, snd) := b in snd)))
                      @ smon_assoc (snd b) t c2) @ ap (functor_prod (smon_mult (fst b)) (smon_mult (snd b))) q).
  Proof.
    destruct p,q. simpl.
    repeat rewrite concat_p1.
    repeat rewrite ap_functor_prod.
    assert (p :
              (ap (fun x : S => functor_prod (smon_mult x) (smon_mult x) (functor_prod (smon_mult a1) (smon_mult a2) (c1, c2)))
                  (smon_sym s t) =
               path_prod (_,_) (_,_)
                         (ap (fun x => x ⊗ (a1 ⊗ c1)) (smon_sym s t)) (ap (fun x => x ⊗ (a2 ⊗ c2)) (smon_sym s t)))).
    { destruct (smon_sym s t). simpl. reflexivity. }
    rewrite p. clear p.
    rewrite <- path_prod_VV.
    repeat rewrite <- path_prod_pp. repeat rewrite ap_pp. repeat rewrite ap_V. 
    apply (ap011 (path_prod _ _)); apply grp_complete_bifun_lem3'.
  Qed.  

  Definition mult_group_completion_fix_fst (S : Symmetric_Monoidal_1Type) (left_cancel : left_faithful (@mon_mult S))
             (a : group_completion S left_cancel) :
    Functor (group_completion S left_cancel) (group_completion S left_cancel).
  Proof.
    srapply @Build_Functor.
    + simpl.
      exact (functor_prod (smon_mult (fst a)) (smon_mult (snd a))).
    + simpl. intros b c.
      unfold monoidal_action_morphism. simpl. unfold functor_prod. simpl.

      intros [s p].
      exists s.
      refine (_ @ ap (functor_prod (smon_mult (fst a)) (smon_mult (snd a))) p).
      unfold functor_prod. simpl. apply path_prod; simpl; refine ((smon_assoc _ _ _)^ @ _ @ smon_assoc _ _ _);
                                    apply (ap (fun x => x ⊗ _ b) (smon_sym s (_ a))).
    + intros b c d. simpl in b,c,d.        
      intros [s p] [t q]. simpl in p,q.  simpl.
      destruct a as [a1 a2]; destruct b as [b1 b2]; simpl.
      srapply @path_sigma. reflexivity. simpl.
      apply grp_complete_bifun_lem1.
    + simpl. intro b.
      srapply @path_sigma. simpl. reflexivity. simpl.
      refine (whiskerL _ (ap_functor_prod _ _ _ _ _ _) @ _).
      destruct a as [a1 a2]. destruct b as [b1 b2]. simpl.
      refine ((path_prod_pp _ _ _ _ _ _ _)^ @ _).
      apply (ap011 (path_prod _ _)); apply grp_complete_bifun_lem2.
  Defined.
  
  Definition mult_group_completion (S : Symmetric_Monoidal_1Type) (left_cancel : left_faithful (@mon_mult S)) :
    BiFunctor (group_completion S left_cancel) (group_completion S left_cancel) (group_completion S left_cancel).
  Proof.
    unfold BiFunctor.
    srapply (Build_Functor (group_completion S left_cancel) (group_completion S left_cancel -> group_completion S left_cancel)
                         (fun (a : (group_completion S left_cancel)) => (mult_group_completion_fix_fst S left_cancel a))).
    - intros a b. simpl in a, b. simpl.
      intros [s p]. simpl in p. 
      srapply @Build_NaturalTransformation.
      + simpl. intro c.
        unfold monoidal_action_morphism. simpl.
        exists s.
        refine (_ @ ap (fun b => functor_prod (smon_mult (fst b)) (smon_mult (snd b)) c) p).
        unfold functor_prod. simpl.
        apply path_prod;
          apply ((smon_assoc _ _ _)^).
      + destruct a as [a1 a2]. intros [c1 c2] d.
        intros [t q]. simpl in q.
        srapply @path_sigma. apply smon_sym.
        refine (transport_paths_Fl (smon_sym s t) _ @ _). cbn.
        apply grp_complete_bifun_lem3.
    - intros a b c [s p] [t q].
      apply NaturalTransformation.path_natural_transformation. simpl.
      intro d. destruct p, q.
      srapply @path_sigma. reflexivity. simpl.
      repeat rewrite concat_p1.

      destruct q. destruct p.
simpl.
        apply group_complete_bifun_lem3.

          
        
        
        
          
        
          destruct 
          apply inverse
                  
        rewrite (ap_functor_prod 
        

        
        refine ((smon_assoc _ _ _)^ @ _). apply (ap (fun x => x ⊗ _) 
        

        
          
        
        
    - 
      
    
    
    
  
  Definition moncat_group_completion (S : Symmetric_Monoidal_1Type)
             (left_cancel : forall (s t : S) (p q : s = t) (a : S),
                 ap (fun x => smon_mult x a) p = ap (fun x => smon_mult x a) q -> p = q) : Monoidal_Category.
  Proof.
    srefine (Build_Monoidal_Category (group_completion S left_cancel) _ _ _ _ (fun a b c => Build_IsIsomorphism _ _ _ _ _ _ _)
                                    _ _ (fun a => Build_IsIsomorphism _ _ _ _ _ _ _) _ _ (fun a => Build_IsIsomorphism _ _ _ _ _ _ _)
            _ _ _).
    - unfold BiFunctor.
      srapply @Build_Functor. simpl.
      intro a. srapply @Build_Functor. simpl.
      + exact (functor_prod (smon_mult (fst a)) (smon_mult (snd a))).
      + simpl. intros b c.
        unfold monoidal_action_morphism. simpl. unfold functor_prod. simpl.
        intros [s p].
        exists s.
        refine (_ @ ap (functor_prod (smon_mult (fst a)) (smon_mult (snd a))) p).
        unfold functor_prod. simpl. apply path_prod; simpl; refine ((smon_assoc _ _ _)^ @ _ @ smon_assoc _ _ _);
        apply (ap (fun x => x ⊗ _ b) (smon_sym s (_ a))).
      
      + intros b c d. simpl in b,c,d.
        intros [s p] [t q]. simpl in p,q.  simpl. destruct p,q. simpl.
        srapply @path_sigma. reflexivity. simpl. destruct a as [a1 a2]; destruct b as [b1 b2]; simpl.
        
apply grp_complete_moncat_diagram1.
      + 


        
        repeat rewrite ap_pp.
        repeat rewrite ap_functor_prod. simpl. repeat rewrite concat_p1. 
        repeat rewrite <- path_prod_pp.
        apply (ap011 (path_prod _ _)).
          * destruct a as [a1 a2]; destruct b as [b1 b2]; simpl.



                                      
          repeat rewrite ap_pp. rewrite ap_V.
          assert (p : ap (smon_mult t) (ap (fun x : S => x ⊗ b1) (smon_sym s a1)) =
                  (mon_assoc t (s ⊗ a1) b1)^ @ ap (fun x : S => x ⊗ b1) (ap (fun x : S => t ⊗ x) (smon_sym s a1)) @ mon_assoc t (a1 ⊗ s) b1).
            destruct (smon_sym s a1). simpl.
            destruct (smon_assoc t (s ⊗ a1) b1). simpl.  reflexivity.
          rewrite p. clear p. repeat rewrite concat_pp_p.
          assert (p : ap (fun x : S => x ⊗ (s ⊗ b1)) (smon_sym t a1) =
                      (smon_assoc (t ⊗ a1) s b1)^ @ ap (fun x : S => x ⊗ b1) (ap (fun x : S => x ⊗ s) (smon_sym t a1)) @ smon_assoc (a1 ⊗ t) s b1).
            destruct (smon_sym t a1). simpl.
            destruct (smon_assoc (t ⊗ a1) s b1). simpl. reflexivity.
          rewrite p. clear p.
          rewrite (smon_sym_inv S t a1). repeat rewrite ap_V.
          rewrite (smon_hexagon S a1 t s).
          repeat rewrite ap_pp. repeat rewrite ap_V.
          repeat rewrite concat_pp_p.
          rewrite (smon_pentagon S a1 t s b1). rewrite (smon_pentagon S t a1 s b1). rewrite smon_pentagon.
          (* rewrite smon_pentagon. *)
          repeat rewrite inv_pp. repeat rewrite inv_V. 
          repeat rewrite concat_pp_p.
          repeat rewrite concat_V_pp. rewrite concat_Vp. rewrite concat_p1.
          rewrite concat_p_Vp. rewrite concat_p_Vp.
          rewrite (smon_sym_inv S a1 (t ⊗ s)). rewrite ap_V. rewrite inv_V.
          rewrite (smon_sym_inv S s a1). rewrite ap_V. rewrite ap_V.
          repeat rewrite concat_V_pp. 
          repeat rewrite concat_p_pp. repeat apply whiskerR. rewrite concat_pV.
          apply inverse. apply concat_1p.

                                      destruct a as [a1 a2]; destruct b as [b1 b2]; simpl.
          repeat rewrite ap_pp. rewrite ap_V.
          assert (p : ap (smon_mult t) (ap (fun x : S => x ⊗ b2) (smon_sym s a2)) =
                  (mon_assoc t (s ⊗ a2) b2)^ @ ap (fun x : S => x ⊗ b2) (ap (fun x : S => t ⊗ x) (smon_sym s a2)) @ mon_assoc t (a2 ⊗ s) b2).
            destruct (smon_sym s a2). simpl.
            destruct (smon_assoc t (s ⊗ a2) b2). simpl.  reflexivity.
          rewrite p. clear p. repeat rewrite concat_pp_p.
          assert (p : ap (fun x : S => x ⊗ (s ⊗ b2)) (smon_sym t a2) =
                      (smon_assoc (t ⊗ a2) s b2)^ @ ap (fun x : S => x ⊗ b2) (ap (fun x : S => x ⊗ s) (smon_sym t a2)) @ smon_assoc (a2 ⊗ t) s b2).
            destruct (smon_sym t a2). simpl.
            destruct (smon_assoc (t ⊗ a2) s b2). simpl. reflexivity.
          rewrite p. clear p.
          rewrite (smon_sym_inv S t a2). repeat rewrite ap_V.
          rewrite (smon_hexagon S a2 t s).
          repeat rewrite ap_pp. repeat rewrite ap_V.
          repeat rewrite concat_pp_p.
          rewrite (smon_pentagon S a2 t s b2). rewrite (smon_pentagon S t a2 s b2). rewrite smon_pentagon.
          (* rewrite smon_pentagon. *)
          repeat rewrite inv_pp. repeat rewrite inv_V. 
          repeat rewrite concat_pp_p.
          repeat rewrite concat_V_pp. rewrite concat_Vp. rewrite concat_p1.
          rewrite concat_p_Vp. rewrite concat_p_Vp.
          rewrite (smon_sym_inv S a2 (t ⊗ s)). rewrite ap_V. rewrite inv_V.
          rewrite (smon_sym_inv S s a2). rewrite ap_V. rewrite ap_V.
          repeat rewrite concat_V_pp. 
          repeat rewrite concat_p_pp. repeat apply whiskerR. rewrite concat_pV.
          apply inverse. apply concat_1p.
          
          
          
          
destruct (smon_assoc (t ⊗ s) a1 b1). 
reflexivity.

          apply whiskerL.
          rewrite <- (ap_compose (fun x : S => t ⊗ x) (fun x : S => x ⊗ b1)).
          rewrite <- (ap_compose (smon_mult a1) (fun x : S => x ⊗ b1)).
          repeat rewrite concat_p_pp. apply whiskerR. apply whiskerR. 
          repeat rewrite concat_pp_p.
          repeat refine (_ @ concat_pp_p _ _ _). refine (_ @ concat_p_pp _ _ _). apply concat2.
           apply concat2.
          hott_simpl.
          
          
          repeat rewrite ap_pp. repeat rewrite ap_V.

          apply moveL_Mp. apply moveL_Vp. apply moveL_Vp.
          
          apply moveR_Vp. apply moveR_pM.
          
          
          
          repeat rewrite smon_hexagon. repeat rewrite ap_pp.

          rewrite concat_Vp. rewrite concat_p1.
          repeat rewrite ap_V.
          repeat rewrite concat_V_pp.
          repeat rewrite concat_p_pp. apply moveL_pV. repeat rewrite concat_pp_p.
          repeat rewrite <- ap_V.
          rewrite <- (ap_compose (smon_mult a1) (smon_mult t)).          
          repeat rewrite ap_V.
          rewrite (ap_homotopy (smon_sym s b1) (fun x : S => t ⊗ (a1 ⊗ x)) (fun x : S => (t ⊗ a1) ⊗ x) (mon_assoc t a1)).
          repeat rewrite inv_pp.
          repeat rewrite concat_pp_p. rewrite inv_V.
          rewrite smon_hexagon.
            
          rewrite (ap_compose 

          
          repeat rewrite <- ap_pp.
          repeat rewrite concat_p_pp. 
          apply moveL_pM. apply moveL_pM. repeat rewrite concat_pp_p.
          repeat rewrite <- ap_pp.
          repeat rewrite concat_p_pp.
          apply moveR_pV. apply moveR_pV. repeat rewrite concat_pp_p. apply moveL_Mp.
          repeat rewrite concat_p_pp.
          generalize (((smon_assoc t s (a1 ⊗ b1))^ @ smon_sym (t ⊗ s) (a1 ⊗ b1)) @ smon_assoc a1 b1 (t ⊗ s)). intro p.
          generalize (

              ap (smon_mult a1) (smon_sym s b1)^) @ smon_sym t (a1 ⊗ (s ⊗ b1))) @
  smon_assoc a1 (s ⊗ b1) t
          generalize (smon_sym (t ⊗ s) (a1 ⊗ b1) @ smon_assoc a1 b1 (t ⊗ s)). intro p.
          generalize (smon_sym t (a1 ⊗ (s ⊗ b1))) @ smon_assoc a1 (s ⊗ b1) t.
          
          
          rewrite <- (ap_pp (smon_mult a1)).

          


          concat_V_pp: forall (A : Type) (x y z : A) (p : x = y) (q : y = z), p^ @ (p @ q) = q
concat_p_Vp: forall (A : Type) (x y z : A) (p : x = y) (q : x = z), p @ (p^ @ q) = q
concat_pp_V: forall (A : Type) (x y z : A) (p : x = y) (q : y = z), (p @ q) @ q^ = p
concat_pV_p: forall (A : Type) (x y z : A) (p : x = z) (q : y = z), (p @ q^) @ q = p
                                                                                     
          rewrite smon_hexagon. rewrite ap_pp. repeat rewrite ap_V. repeat rewrite ap_pp.
          repeat rewrite concat_pp_p. apply moveL_Mp. repeat rewrite concat_p_pp. rewrite concat_Vp. rewrite concat_1p.
          apply moveL_pV. apply moveL_pM. apply moveL_pM. apply moveL_pV.
          repeat rewrite concat_pp_p.          
          rewrite concat_Vp. rewrite concat_p1. repeat rewrite concat_pp_p.
          rewrite smon_hexagon. simpl.
          repeat rewrite inv_pp. repeat rewrite inv_V. repeat rewrite concat_pp_p.
          apply moveR_Vp. apply moveR_Mp. apply moveR_Mp.
          apply moveR_Vp. apply moveR_Mp.
          repeat rewrite concat_p_pp. rewrite concat_Vp. rewrite concat_1p. repeat rewrite concat_pp_p.
          

          repeat rewrite <- ap_pp. 
          apply moveR_Mp. repeat rewrite <- ap_V.
          repeat rewrite inv_pp. repeat rewrite inv_V. repeat rewrite concat_p_pp.
          repeat rewrite <- ap_pp. repeat rewrite concat_pp_p.
          
          
          
          rewrite (ap_compose _ _ (smon_sym t a1)).

          
          rewrite <- (ap_compose (fun x : S => x ⊗ b1)(smon_mult t)). 
          

          hott_simpl.
          assert (smon_assoc a1 (t ⊗ s) b1 @ ap (smon_mult a1) (smon_assoc t s b1) =
                  ap (fun x : S => x ⊗ (s ⊗ b1)) (smon_sym t a1) @ smon_assoc a1 t (s ⊗ b1)).
          
        
        rewrite ap_functor_prod.
        
        apply path_sigma_1.
        
        

        (* Need symmetry *)
  Abort.
        
        
    

             
End Monoidal_Category.


  
  

(*Defining the monoidal 1-type of finite sets and isomorphisms*)
Section BΣ.
    
  (*This type corresponds to the category of finite sets and isomorphisms*)
  Definition BΣ := { S : Type & Finite S}.
  Definition type_of_fin : BΣ -> Type := pr1.
  Coercion type_of_fin : BΣ  >-> Sortclass.

  Global Instance istrunc_BΣ : IsTrunc 1 BΣ.
  Proof.
    apply trunc_sigma'. intro A. exact _.
S    intros A B.
    srapply @istrunc_paths_Type. 
    apply isset_Finite. exact B.2.
  Defined.

  (*Canonical objects in BΣ*)
  Definition canon_BΣ (n : nat) : BΣ := (Fin n; Build_Finite (Fin n) n (tr 1%equiv)).
  


  (* Describing the path type of BΣ *)
  Definition path_BΣ {S T : BΣ} : S <~> T <~> S = T
    := path_finite_types_sum S T.

  (* path_BΣ respects composition *)
  Definition path_BΣ_compose {S1 S2 S3 : BΣ} (e1 : S2 <~> S1) (e2 : S3 <~> S2) :
    path_BΣ e2 @ path_BΣ e1 = path_BΣ (e1 oE e2).
  Proof.
    apply (equiv_inj path_BΣ^-1).
    refine (_ @ (eissect (path_BΣ) (e1 oE e2))^).
    apply path_equiv. simpl.
    unfold pr1_path.
    rewrite ap_pp.
    rewrite ap_pr1_path_sigma_hprop. rewrite ap_pr1_path_sigma_hprop. apply path_arrow. intro s.
    refine (transport_pp idmap _ _ _ @ _).
    refine (ap10 (transport_idmap_path_universe e1) _ @ _). apply (ap e1).
    apply (ap10 (transport_idmap_path_universe e2)).
  Qed.

  Definition plus_BΣ : BΣ -> BΣ -> BΣ.
  Proof.
    intros [S1 fin_S1] [S2 fin_S2].
    refine (S1 + S2 ; finite_sum _ _)%type.
  Defined.

  Definition BΣ_id : BΣ := canon_BΣ 0.

  Local Notation "S1 ⊕ S2" := (plus_BΣ S1 S2) (at level 50, no associativity).  

  (* path_BΣ behaves well with respect to sum *)
  Definition natural_path_BΣ_l {S1 S2 S3: BΣ} (e : S1 <~> S2) :
    ap (fun x : BΣ => x ⊕ S3) (path_BΣ e) = path_BΣ (S := S1 ⊕ S3) (T := S2 ⊕ S3) (equiv_functor_sum_r (B := S3) e).
  Proof.
    apply (equiv_inj (path_BΣ)^-1).
    refine (_ @ (eissect (path_finite_types_sum (S1 ⊕ S3) (S2 ⊕ S3)) (equiv_functor_sum_r e))^).
    apply path_equiv. simpl.
    unfold pr1_path. 
    transitivity
      (transport idmap (ap (fun X : Type => X + S3) (ap pr1 (path_sigma_hprop S1 S2 (path_universe_uncurried e))))).
    { apply (ap (transport idmap)).
      refine ((ap_compose (fun x : BΣ => x ⊕ S3) pr1 _)^ @ ap_compose pr1 (fun X : Type => X + S3) _). }
    apply path_arrow. intro s.
    refine ((transport_idmap_ap _ _ _ _ _ _)^ @ _).
    refine ((ap (fun p => transport (fun X : Type => X + S3) p s) (ap_pr1_path_sigma_hprop _ _ _)) @ _).
    destruct S1 as [S1 fin1]. destruct S2 as [S2 fin2]. destruct S3 as [S3 fin3]. simpl in *.
    clear fin1 fin2 fin3.
    revert e s.
    apply (equiv_induction
           (fun S2 e => forall s : (S1 + S3), transport (fun X : Type => X + S3) (path_universe_uncurried e) s = functor_sum e idmap s)).
    change (path_universe_uncurried 1) with (path_universe (A := S1) idmap).      
    rewrite path_universe_1. simpl.
    intros [s1 | s3]; reflexivity.
  Qed.

  Definition natural_path_BΣ_r {S1 S2 S3: BΣ} (e : S2 <~> S3) :
    ap (fun x : BΣ => S1 ⊕ x) (path_BΣ e) = path_BΣ (S := S1 ⊕ S2) (T := S1 ⊕ S3) (equiv_functor_sum_l (A := S1) e).
  Proof.
    apply (equiv_inj (path_BΣ)^-1).
    refine (_ @ (eissect (path_finite_types_sum (S1 ⊕ S2) (S1 ⊕ S3)) (equiv_functor_sum_l e))^).
    apply path_equiv. simpl.
    unfold pr1_path. 
    transitivity
      (transport idmap (ap (fun X : Type => S1 + X) (ap pr1 (path_sigma_hprop S2 S3 (path_universe_uncurried e))))).
    { apply (ap (transport idmap)).
      refine ((ap_compose (fun x : BΣ => S1 ⊕ x) pr1 _)^ @ ap_compose pr1 (fun X : Type => S1 + X ) _). }
    apply path_arrow. intro s.
    refine ((transport_idmap_ap _ _ _ _ _ _)^ @ _).
    refine ((ap (fun p => transport (fun X : Type => S1 + X) p s) (ap_pr1_path_sigma_hprop _ _ _)) @ _).
    destruct S1 as [S1 fin1]. destruct S2 as [S2 fin2]. destruct S3 as [S3 fin3]. simpl in *.
    clear fin1 fin2 fin3. change (path_universe_uncurried e) with (path_universe e). 
    revert e s. 
    apply (equiv_induction
           (fun S3 e => forall s : (S1 + S2), transport (fun X : Type => S1 + X) (path_universe e) s = functor_sum idmap e s)).
    rewrite path_universe_1. simpl.
    intros [s1 | s2]; reflexivity.
  Qed.
  
  (*The monoidal structure on BΣ*)
  
  Definition BΣ_assoc : associative plus_BΣ.
  Proof.
    intros S1 S2 S3.
    apply path_BΣ.
    apply equiv_sum_assoc. 
  Defined.

  Definition BΣ_lid : left_identity_mult plus_BΣ (canon_BΣ 0).
  Proof.
    intro S. apply path_BΣ.
    apply sum_empty_l.
  Defined.
  
  Definition BΣ_rid : right_identity_mult plus_BΣ (canon_BΣ 0).
  Proof.
    intro S. apply path_BΣ.
    apply sum_empty_r.
  Defined.

  Definition BΣ_symmetric : symmetric plus_BΣ. 
  Proof.
    intros S1 S2. apply path_BΣ. apply equiv_sum_symm.
  Defined.



  
  
  (*TODO: How [cardinal] respects associativity and identity proofs *)
  Definition BΣ_triangle1 : coherence_triangle1 BΣ_assoc BΣ_lid.
  Proof.
    intros S1 S2.
    unfold BΣ_lid.
    refine (natural_path_BΣ_l _ @ _).
    unfold BΣ_assoc.
    refine (_ @ (path_BΣ_compose _ _)^).
    apply (ap path_BΣ).
    apply path_equiv. apply path_arrow.
    intros [[[] | s1] | s2]; reflexivity.
  Qed.

  Definition BΣ_triangle2 : coherence_triangle2 BΣ_assoc BΣ_lid BΣ_rid.
  Proof.
    intros S1 S2. unfold BΣ_rid. unfold BΣ_assoc. unfold BΣ_lid. simpl.
    refine (natural_path_BΣ_l _ @ _).
    refine (_ @ whiskerL _ (natural_path_BΣ_r _)^).
    refine (_ @ (path_BΣ_compose  _ _)^).
    apply (ap path_BΣ).
    apply path_equiv. apply path_arrow.
    intros [[s1 | []] | s2]; reflexivity.
  Qed.
  
  Definition BΣ_pentagon : coherence_pentagon BΣ_assoc.
  Proof.
    intros S1 S2 S3 S4.
    refine (natural_path_BΣ_l _  @ _).
    apply moveL_pV.
    refine (path_BΣ_compose _ _ @ _).
    apply moveL_pV.
    refine (whiskerL _ (natural_path_BΣ_r _) @ _).
    refine (path_BΣ_compose _ _ @ _).
    refine (_ @ (path_BΣ_compose _ _)^).
    apply (ap path_BΣ).
    apply path_equiv. apply path_arrow.
    intros [[[s1 | s2]| s3] | s4]; reflexivity.
  Defined.

  Definition isinj_functor_sum {A1 A2 B1 B2 : Type} (f1 f1' : A1 -> B1) (f2 f2': A2 -> B2) :
    functor_sum f1 f2 = functor_sum f1' f2' -> (f1 = f1') * (f2 = f2').
  Proof.
    intro p.
    set (p' := ap10 p).
    apply pair.
    - apply path_arrow. intro a.
      refine ((path_sum (inl (f1 a)) (inl (f1' a)))^-1 (p' (inl a))).
      apply (@isequiv_path_sum B1 B2 (inl (f1 a)) (inl (f1' a))).
    - apply path_arrow. intro a.
      refine ((path_sum (inr (f2 a)) (inr (f2' a)))^-1 (p' (inr a))).
      apply (@isequiv_path_sum B1 B2 (inr (f2 a)) (inr (f2' a))).
  Defined.

  Definition isinj_equiv_functor_sum_r {A1 A2 B : Type} (e1 e2 : A1 <~> A2) :
    equiv_functor_sum_r (B := B) e1 = equiv_functor_sum_r e2 -> e1 = e2.
  Proof.
    intro p. apply path_equiv.
    refine (fst ((isinj_functor_sum e1 e2 idmap idmap) _)).
    apply (path_equiv^-1 p).
  Defined.    
  
  Definition BΣ_lcancel (S1 S2 : BΣ) (p q : S1 = S2) (T : BΣ) :
    ap (fun x => x ⊕ T) p = ap (fun x => x ⊕ T) q -> p = q.
  Proof.
    intro h.
    apply (equiv_inj (@path_BΣ S1 S2)^-1).
    apply (isinj_equiv_functor_sum_r (B:=T) (path_BΣ^-1 p) (path_BΣ^-1 q)) .
    apply (equiv_inj (@path_BΣ (S1 ⊕ T) (S2 ⊕ T))).
    refine ((natural_path_BΣ_l _)^ @ _ @ natural_path_BΣ_l _).
    refine (_ @ h @ _);
      apply (ap (ap (fun x : BΣ => x ⊕ T))).
      - apply eisretr.
      - apply inverse. apply eisretr.
  Defined.

  Definition BΣ_moncat : Monoidal_1Type :=
    Build_Monoidal_1Type (BuildTruncType 1 BΣ) plus_BΣ (canon_BΣ 0) BΣ_assoc BΣ_lid BΣ_rid BΣ_triangle1 BΣ_triangle2 BΣ_pentagon.

  Definition group_completion_BΣ := group_completion BΣ_moncat BΣ_lcancel .
    
  
End BΣ.


     
                   
  
  