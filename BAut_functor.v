Require Import HoTT.
Require Import UnivalenceAxiom.
Require Import smash.
Require Import pointed_lemmas.
Require Import finite_lemmas.

(* Definition pMap' (A B : pType) := Build_pType (pMap A B) (Build_pMap A B (fun a => point B) idpath). *)

(* Definition universal_smash (A B C : pType) : *)
(*   pEquiv (pMap' (smash A B) C) (pMap' A (pMap' B C)). *)
(* Proof. *)
(*   Admitted. *)



Section Symmetric_Smash.
  Variable X : pType.
  
  (* What we really want: *)
  (* Inductive Symmetric_Smash' : Type -> pType := *)
  (*   |ss_0 : pSphere 0 ->* Symmetric_Smash' Empty *)
  (*   |ss_1 : X ->* Symmetric_Smash' Unit *)
  (*   |ss_AB (A B : Type) : smash (Symmetric_Smash' A) (Symmetric_Smash' B) ->* Symmetric_Smash' (A + B). *)
  (* Cannot define pTypes by induction in this way, so we have to work around and define it as a HIT  *)

  (* Use that smash can be defined as the pushout of the two maps from A+B into Unit+Unit and A*B and bake that into the HIT *)

  (* Why doesn't this work? *)
  (* Private Inductive Symmetric_Smash : Type -> Type := *)
  (*   |ss_basepoint (A : Type) : Symmetric_Smash A *)
  (*   |pt : Symmetric_Smash Empty (* SS Empty is the 0-sphere *) *)
  (*   |ss_1 : X -> Symmetric_Smash Unit *)
  (*   |ss_sum {A B : Type} : (smash (Symmetric_Smash A) (ss_basepoint A) (Symmetric_Smash B) (ss_basepoint B)) -> Symmetric_Smash (A+B). *)

  
  (* Use that smash can be defined as the pushout of the two maps from A+B into Unit+Unit and A*B and bake that into the HIT *)
  
  Private Inductive Symmetric_Smash : Type -> Type :=
    |ss_basepoint (A : Type) : Symmetric_Smash A
    |pt : Symmetric_Smash Empty (* SS Empty is the 0-sphere *)
    |ss1 : X -> Symmetric_Smash Unit
    |ss_sum {A B : Type} : Symmetric_Smash A -> Symmetric_Smash B -> Symmetric_Smash (A + B)
    |hub_r (A B : Type) : Symmetric_Smash (A + B) (* An extra point needed to define the smash product as a HIT *).

  Axiom pointed_ss1 : ss1 (point X) = ss_basepoint Unit. (* ss1 is a pointed map *)
  Axiom pointed_ss_sum_l : forall (A B : Type) (y : Symmetric_Smash B), ss_sum (ss_basepoint A) y = ss_basepoint (A+B).
  Axiom pointed_ss_sum_r : forall (A B : Type) (x : Symmetric_Smash A), ss_sum x (ss_basepoint B) = hub_r A B.
  

  Definition SS_ind (P : forall A : Type, Symmetric_Smash A -> Type)
             (ss_basepoint' : forall A : Type, P A (ss_basepoint A))
             (pt' : P Empty pt)
             (ss1' : forall x : X, P Unit (ss1 x))
             (pointed_ss1' : transport (P Unit) (pointed_ss1) (ss1' (point X)) = ss_basepoint' Unit)
             (ss_sum' : forall {A B : Type} (x : Symmetric_Smash A) (y : Symmetric_Smash B), P (A+B) (ss_sum x y))
             (hub_r' : forall (A B : Type), P (A+B) (hub_r A B))
             (pointed_ss_sum_l' : forall (A B : Type) (y : Symmetric_Smash B),
                 transport (P (A + B)) (pointed_ss_sum_l A B y) (ss_sum' (ss_basepoint A) y ) = (ss_basepoint' (A+B)))
             (pointed_ss_sum_r' : forall (A B : Type) (x : Symmetric_Smash A),
                 transport (P (A + B)) (pointed_ss_sum_r A B x) (ss_sum' x (ss_basepoint B)) = hub_r' A B)
             

                 : forall (A : Type) (x : Symmetric_Smash A), P A x.
    Proof.
      intros A a. destruct a.
      - exact (ss_basepoint' A).
      - exact pt'.
      - exact (ss1' p).
      - exact (ss_sum' A B a1 a2).
      - exact (hub_r' A B).
    Defined.



    Axiom SS_ind_beta_pointed_ss1 :
      forall (P : forall A : Type, Symmetric_Smash A -> Type)
             (ss_basepoint' : forall A : Type, P A (ss_basepoint A))
             (pt' : P Empty pt)
             (ss1' : forall x : X, P Unit (ss1 x))
             (pointed_ss1' : transport (P Unit) (pointed_ss1) (ss1' (point X)) = ss_basepoint' Unit)
             (ss_sum' : forall {A B : Type} (x : Symmetric_Smash A) (y : Symmetric_Smash B), P (A+B) (ss_sum x y))
             (hub_r' : forall (A B : Type), P (A+B) (hub_r A B))
             (pointed_ss_sum_l' : forall (A B : Type) (y : Symmetric_Smash B),
                 transport (P (A + B)) (pointed_ss_sum_l A B y) (ss_sum' (ss_basepoint A) y ) = (ss_basepoint' (A+B)))
             (pointed_ss_sum_r' : forall (A B : Type) (x : Symmetric_Smash A),
                 transport (P (A + B)) (pointed_ss_sum_r A B x) (ss_sum' x (ss_basepoint B)) = hub_r' A B),
      apD (SS_ind P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r' pointed_ss_sum_l' pointed_ss_sum_r' Unit) pointed_ss1 = pointed_ss1'.

    Axiom SS_ind_beta_pointed_ss_sum_l :
      forall (P : forall A : Type, Symmetric_Smash A -> Type)
             (ss_basepoint' : forall A : Type, P A (ss_basepoint A))
             (pt' : P Empty pt)
             (ss1' : forall x : X, P Unit (ss1 x))
             (pointed_ss1' : transport (P Unit) (pointed_ss1) (ss1' (point X)) = ss_basepoint' Unit)
             (ss_sum' : forall {A B : Type} (x : Symmetric_Smash A) (y : Symmetric_Smash B), P (A+B) (ss_sum x y))
             (hub_r' : forall (A B : Type), P (A+B) (hub_r A B))
             (pointed_ss_sum_l' : forall (A B : Type) (y : Symmetric_Smash B),
                 transport (P (A + B)) (pointed_ss_sum_l A B y) (ss_sum' (ss_basepoint A) y ) = (ss_basepoint' (A+B)))
             (pointed_ss_sum_r' : forall (A B : Type) (x : Symmetric_Smash A),
                 transport (P (A + B)) (pointed_ss_sum_r A B x) (ss_sum' x (ss_basepoint B)) = hub_r' A B)
             (A B : Type) (y : Symmetric_Smash B),
        apD (SS_ind P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r' pointed_ss_sum_l' pointed_ss_sum_r' (A+B))
               (pointed_ss_sum_l A B y) = pointed_ss_sum_l' A B y.

    Axiom SS_ind_beta_pointed_ss_sum_r :
      forall (P : forall A : Type, Symmetric_Smash A -> Type)
             (ss_basepoint' : forall A : Type, P A (ss_basepoint A))
             (pt' : P Empty pt)
             (ss1' : forall x : X, P Unit (ss1 x))
             (pointed_ss1' : transport (P Unit) (pointed_ss1) (ss1' (point X)) = ss_basepoint' Unit)
             (ss_sum' : forall {A B : Type} (x : Symmetric_Smash A) (y : Symmetric_Smash B), P (A+B) (ss_sum x y))
             (hub_r' : forall (A B : Type), P (A+B) (hub_r A B))
             (pointed_ss_sum_l' : forall (A B : Type) (y : Symmetric_Smash B),
                 transport (P (A + B)) (pointed_ss_sum_l A B y) (ss_sum' (ss_basepoint A) y ) = (ss_basepoint' (A+B)))
             (pointed_ss_sum_r' : forall (A B : Type) (x : Symmetric_Smash A),
                 transport (P (A + B)) (pointed_ss_sum_r A B x) (ss_sum' x (ss_basepoint B)) = hub_r' A B)
             (A B : Type) (x : Symmetric_Smash A),
        apD (SS_ind P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r' pointed_ss_sum_l' pointed_ss_sum_r' (A+B))
            (pointed_ss_sum_r A B x) = pointed_ss_sum_r' A B x.


    (* Things needed to prove: *)
    (* SS Empty <~> S^0 *)
    (* SS Unit <~> X *)
    (* SS (A + B) <~> smash (SS A) (SS B) *)
    (* smash S1 A <~> Susp A *)


  Definition SS_rec
             (P : Type -> Type)
             (ss_basepoint' :forall (A : Type), P A)
             (pt' : P Empty)
             (ss1' : X -> P Unit)
             (pointed_ss1' : ss1' (point X) = ss_basepoint' Unit)
             (ss_sum' : forall {A B : Type},
                 Symmetric_Smash A -> Symmetric_Smash B -> P (A + B))
             (hub_r' : forall (A B : Type), P (A + B))
             (pointed_ss_sum_l' : forall (A B : Type) (y : Symmetric_Smash B),
                 ss_sum' (ss_basepoint A) y = ss_basepoint' (A+B))
             (pointed_ss_sum_r' : forall (A B : Type) (x : Symmetric_Smash A),
                 ss_sum' x (ss_basepoint B) = hub_r' A B)
    : forall A : Type, Symmetric_Smash A -> P A.
  Proof.
    refine (SS_ind (fun A _ => P A) ss_basepoint' pt' ss1' _ (@ss_sum') hub_r' _ _);
      intros; refine (transport_const _ _ @ _).
    - exact pointed_ss1'.
    - exact (pointed_ss_sum_l' A B y).
    - exact (pointed_ss_sum_r' A B x).
  Defined.



  Definition SS_rec_beta_pointed_ss1
             (P : Type -> Type)
             (ss_basepoint' :forall (A : Type), P A)
             (pt' : P Empty)
             (ss1' : X -> P Unit)
             (pointed_ss1' : ss1' (point X) = ss_basepoint' Unit)
             (ss_sum' : forall {A B : Type},
                 Symmetric_Smash A -> Symmetric_Smash B -> P (A + B))
             (hub_r' : forall (A B : Type), P (A + B))
             (pointed_ss_sum_l' : forall (A B : Type) (y : Symmetric_Smash B),
                 ss_sum' (ss_basepoint A) y = ss_basepoint' (A+B))
             (pointed_ss_sum_r' : forall (A B : Type) (x : Symmetric_Smash A),
                 ss_sum' x (ss_basepoint B) = hub_r' A B)
    : ap (SS_rec P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r'
                 pointed_ss_sum_l' pointed_ss_sum_r' Unit) (pointed_ss1) = (pointed_ss1').
  Proof.
    apply (cancelL (transport_const (pointed_ss1) (ss1' (point X)))).
    transitivity (apD (SS_rec P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r'
                              pointed_ss_sum_l' pointed_ss_sum_r' Unit) (pointed_ss1)).
    symmetry. refine (apD_const (SS_rec P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r'
                                        pointed_ss_sum_l' pointed_ss_sum_r' Unit) _).
    refine (SS_ind_beta_pointed_ss1 (fun A _ => P A) _ _ _ _ _ _ _ _).
  Defined.

  Definition SS_rec_beta_pointed_ss_sum_l
             (P : Type -> Type)
             (ss_basepoint' :forall (A : Type), P A)
             (pt' : P Empty)
             (ss1' : X -> P Unit)
             (pointed_ss1' : ss1' (point X) = ss_basepoint' Unit)
             (ss_sum' : forall {A B : Type},
                 Symmetric_Smash A -> Symmetric_Smash B -> P (A + B))
             (hub_r' : forall (A B : Type), P (A + B))
             (pointed_ss_sum_l' : forall (A B : Type) (y : Symmetric_Smash B),
                 ss_sum' (ss_basepoint A) y = ss_basepoint' (A+B))
             (pointed_ss_sum_r' : forall (A B : Type) (x : Symmetric_Smash A),
                 ss_sum' x (ss_basepoint B) = hub_r' A B)
             (A B : Type) (y : Symmetric_Smash B)
    : ap (SS_rec P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r'
                 pointed_ss_sum_l' pointed_ss_sum_r' (A+B)) (pointed_ss_sum_l A B y) =
      pointed_ss_sum_l' A B y.
  Proof.
    apply (cancelL (transport_const (pointed_ss_sum_l A B y) (ss_sum' A B (ss_basepoint A) y ))).
    transitivity (apD (SS_rec P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r'
                              pointed_ss_sum_l' pointed_ss_sum_r' (A+B)) (pointed_ss_sum_l A B y)).
    symmetry. refine (apD_const (SS_rec P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r'
                                        pointed_ss_sum_l' pointed_ss_sum_r' (A+B)) _).
    refine (SS_ind_beta_pointed_ss_sum_l (fun A _ => P A) _ _ _ _ _ _ _ _ _ _ _).
  Defined.


    

  Definition SS_rec_beta_pointed_ss_sum_r
             (P : Type -> Type)
             (ss_basepoint' :forall (A : Type), P A)
             (pt' : P Empty)
             (ss1' : X -> P Unit)
             (pointed_ss1' : ss1' (point X) = ss_basepoint' Unit)
             (ss_sum' : forall {A B : Type},
                 Symmetric_Smash A -> Symmetric_Smash B -> P (A + B))
             (hub_r' : forall (A B : Type), P (A + B))
             (pointed_ss_sum_l' : forall (A B : Type) (y : Symmetric_Smash B),
                 ss_sum' (ss_basepoint A) y = ss_basepoint' (A+B))
             (pointed_ss_sum_r' : forall (A B : Type) (x : Symmetric_Smash A),
                 ss_sum' x (ss_basepoint B) = hub_r' A B)
             (A B : Type) (x : Symmetric_Smash A)
    : ap (SS_rec P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r'
                 pointed_ss_sum_l' pointed_ss_sum_r' (A+B)) (pointed_ss_sum_r A B x) =
      pointed_ss_sum_r' A B x.
  Proof.
    apply (cancelL (transport_const (pointed_ss_sum_r A B x) (ss_sum' A B x (ss_basepoint B)))).
    transitivity (apD (SS_rec P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r'
                              pointed_ss_sum_l' pointed_ss_sum_r' (A+B)) (pointed_ss_sum_r A B x)).
    symmetry. refine (apD_const (SS_rec P ss_basepoint' pt' ss1' pointed_ss1' (@ss_sum') hub_r'
                                        pointed_ss_sum_l' pointed_ss_sum_r' (A+B)) _).
    refine (SS_ind_beta_pointed_ss_sum_r (fun A _ => P A) _ _ _ _ _ _ _ _ _ _ _).
  Defined.
End Symmetric_Smash.

Global Instance ispointed_SS (X : pType) (A : Type) : IsPointed (Symmetric_Smash X A) := ss_basepoint X A.
Definition Symmetric_Smash' (X : pType) (A : Type) :=
  Build_pType (Symmetric_Smash X A) _.

(* ss_sum induces a pointed map from the smash product *)
Definition ss_sum_smash (X : pType) {A B : Type} :
           smash (Symmetric_Smash' X A) (Symmetric_Smash' X B) ->* Symmetric_Smash' X (A+B).
Proof.
  srapply @Build_pMap. cbn.
  srapply @smash_rec.
  - apply ss_sum.               (* map on product *)
  - apply ss_basepoint.         (* basepoint *)
  - apply hub_r.                (* other hub *)
  - intro y. apply (pointed_ss_sum_l X).
  - intro x. apply (pointed_ss_sum_r X).
  - cbn. reflexivity.
Defined.

Definition iterated_smash (X : pType) (n : nat) : pType.
Proof.
  induction n.
  - exact (Build_pType (pSphere 0) _).
  - exact (Build_pType (smash X IHn) _). 
Defined.

Definition smash_over_magma (X : pType) (A : Type) (m : Magma A) : pType.
Proof.
  induction m.
  - exact (Build_pType (pSphere 0) _).          (* A is empty *)
  - exact X.                                    (* A is Unit *)
  - exact (Build_pType (smash IHm1 IHm2) _).
Defined.

(* Want: forall A : Type, m : Magma A, then SS X A is smash_over_magma *)

Definition som_to_SS (X : pType) (A : Type) (m : Magma A) :
  smash_over_magma X A m ->* Symmetric_Smash X A.
Proof.
  induction m.
  - srapply @Build_pMap. cbn.
    intros [[]|[]].
    + apply ss_basepoint. + apply pt.
    + cbn. reflexivity.
  - srapply @Build_pMap. cbn.
    apply ss1. cbn.
    apply pointed_ss1.
  - refine ((ss_sum_smash X) o* _).
    apply functor_smash.
    { exact IHm1. } { exact IHm2. }
Defined.

(* (* Lets see if we can show that this is an equivalence *) *)
(* Definition isequiv_som_to_SS (X: pType) (A : Type) (m : Magma A) : *)
(*   IsEquiv (som_to_SS X A m). *)
(* Proof. *)
(*   apply isequiv_fcontr. cbn. *)
(*   intro x. *)
(*   revert A x m. *)
(*   srapply @SS_ind. *)
(*   - cbn. intros A m. *)
(*     srapply @BuildContr. *)
(*     { exists (point _). apply (point_eq (som_to_SS X A m)). } *)
(*     intros [x p]. *)
(*     induction m. *)
(*     { cbn. *)


(* Definition parallel_induction (X : pType) *)
(*            (P : forall (A : Type) (m : Magma A) (x : Symmetric_Smash X A), Type) *)
(*            (ss_basepoint' : forall (A: Type) (m : Magma A), P A m (ss_basepoint X A)) *)
(*            (pt' : P Empty m0 (pt X)) *)
(*            (ss1' : forall x : X, P Unit m1 (ss1 X x)) *)
(*            (pointed_ss1' : transport (P Unit m1) (pointed_ss1 X) (ss1' (point X)) = ss_basepoint' Unit m1) *)
(*            (ss_sum' : forall {A B : Type} (m1 : Magma A) (m2 : Magma B) (x : Symmetric_Smash X A) (y : Symmetric_Smash X B), P (A+B) (m_sum m1 m2) *)
(*                                                                                                                                (ss_sum X x y)) *)
(*            (hub_r' : forall (A B : Type) (m1 : Magma A) (m2 : Magma B), P (A+B) (m_sum m1 m2) (hub_r X A B)) *)
(*            (pointed_ss_sum_l' : forall (A B : Type) (m1 : Magma A) (m2 : Magma B) (y : Symmetric_Smash X B), *)
(*                transport (P (A + B) (m_sum m1 m2)) (pointed_ss_sum_l X A B y) (ss_sum' m1 m2 (ss_basepoint X A) y ) = (ss_basepoint' (A+B) (m_sum m1 m2))) *)
(*            (pointed_ss_sum_r' : forall (A B : Type) (m1 : Magma A) (m2 : Magma B) (x : Symmetric_Smash X A), *)
(*                transport (P (A + B) (m_sum m1 m2)) (pointed_ss_sum_r X A B x) (ss_sum' m1 m2 x (ss_basepoint X B)) = hub_r' A B m1 m2) *)
(*   : forall (A : Type) (m : Magma A) (x : Symmetric_Smash X A), P A m x. *)
(* Proof. *)
(*   intros A m x. *)
(*   match (m, x) with *)
  

  
    



Fixpoint SS_to_som (X : pType) (A : Type) (m : Magma A) :
  Symmetric_Smash X A -> smash_over_magma X A m.
Proof.
  intro x. revert m. revert A x.
  srapply @SS_rec.
  
  - cbn. intros A m. exact (point _). (* Basepoint *)
  - cbn. intro m.
    exact (match m with
             |m0 => inr tt
           end).
    destruct m.
    cbn. exact (inr tt).
    { cbn. exact (point X).     (* this doesn't make sense. . . *) }
    { exact (point _). }        (* makes no sense *)
  - cbn. intro x.
    destruct m.
    { exact (point _). }        (* makes no sense *)
    exact x.
    { exact (point _). }        (* makes no sense *)
  - cbn.
    apply path_forall. intro m. induction m.
    { cbn. reflexivity. }
    { cbn. reflexivity. }
    cbn. reflexivity.
  - cbn.
    intros A B x y m.
    apply SS_to_som. apply (ss_sum X x y).
  - cbn.                        (* hub_r' *)
    intros A B m.
    recall (A + B) as C eqn:e. apply (transport (fun D => smash_over_magma X D (transport Magma e m) e).
    destruct m.
    

  
    

  

(* Want to prove this *)
Definition iterated_SS (X : pType) (n : nat) :
  pEquiv (iterated_smash X n) (Symmetric_Smash' X (Fin n)).
Proof.
  srapply @Build_pEquiv.
  - induction n.
    { cbn. srapply @Build_pMap.
      intros [[] | []].
      { exact (ss_basepoint X Empty). } (* Basepoint *)
      { exact (pt X). }                 (* Other point *)
      cbn. reflexivity.
    } 
    apply (pequiv_inverse (universal_smash _ _ _)).
    srapply (@Build_pMap).
    + intro x. srapply @Build_pMap.
      { cbn. intro y. apply ss_sum.
        { apply IHn. exact y. }
        { apply ss1. exact x. }
      }
      cbn.
      transitivity (hub_r X (Fin n) Unit).        
      refine (_ @ pointed_ss_sum_r X (Fin n) Unit (ss1 X x)).
      apply (ap (fun y => ss_sum X y (ss1 X x))).
      apply (point_eq IHn).
      exact ((pointed_ss_sum_r X (Fin n) Unit (ss_basepoint X _))^ @
                                                                     pointed_ss_sum_l X (Fin n) Unit (ss_basepoint X _)).
    +  cbn.
       apply path_pmap.
       srapply @Build_pHomotopy.
       { intro x. cbn.
         transitivity (ss_sum X (IHn x) (ss_basepoint X Unit)).
         apply (ap (ss_sum X (IHn x))).
         apply pointed_ss1.
         apply pointed_ss_sum_l.
       }
       cbn.
       rewrite concat_p1.
       assert (ap


                 
       
       transitivity ((ap (fun y : Symmetric_Smash X (Fin n) => ss_sum X y (ss1 X (point X))) (point_eq IHn) @
                        pointed_ss_sum_r X (Fin n) Unit (ss_basepoint X Unit)) @
                    ((pointed_ss_sum_r X (Fin n) Unit (ss_basepoint X Unit))^ @
                      pointed_ss_sum_l X (Fin n) Unit (ss_basepoint X (Fin n)))).
       
       admit.
  - cbn.
       transitivity (ap (ss_sum X (ss_basepoint X (Fin n))) (pointed_ss1 X) @
                        pointed_ss_sum_l X (Fin n) Unit (ss_basepoint X (Fin n))).
       rewrite (point_eq IHn).
       unfold point.
           

           
           apply (pointed_fun _ (Build_pType (Symmetric_Smash X (Fin n.+1)) _ )).
         
         apply ss_sum.
         { cbn in x. apply IHn. admit. }
         { 




Definition SS_S0_to_S0 : forall A : Type, Symmetric_Smash (Build_pType (pSphere 0) _) A -> pSphere 0.
Proof.
  srapply (@SS_rec (Build_pType (pSphere 0) _)).
  intro A. cbn.
  - exact (point (pSphere 0)).
  - cbn. exact (inl tt).
  - cbn. exact idmap.
  - cbn. exact idpath.
  - intros A B x y.
    cbn.
    (* Problem. Define as fixpoint? *)


Section SS1.
  Definition pUnit := Build_pType Unit tt.
  (*  *)
  Definition contr_SS1 (A : Type) (a : A) : Contr (Symmetric_Smash pUnit A).
  Proof.
    apply (BuildContr _ (ss_basepoint _ _)).
    intro x. revert A x a.
    srapply @SS_ind; cbn.
    - reflexivity.
    - intros [].
    - intros [] [].
      exact (pointed_ss1 pUnit)^.
    - apply path_arrow. intros [].
      refine (transport_arrow_fromconst (pointed_ss1 pUnit) (fun a : Unit => match a with
                                                                   | tt => (pointed_ss1 pUnit)^
                                                                   end) tt @ _).
      refine (transport_paths_r (pointed_ss1 pUnit) (pointed_ss1 pUnit)^  @ _).
      apply concat_Vp.
    - intros A B x y .

      

  

(* If we have something in SS A, then we have something in Magma A *)
Section SS_to_Magma.
  (* This is how I remember Håkon's definition of Magma *)
  Inductive Magma : Type -> Type :=
    | m0 : Magma Empty
    | m1 : Magma Unit
    | m_sum : forall (A B : Type), Magma A -> Magma B -> Magma (A + B).

  (* (* That doesn't work (need it to be pointed) Let's try something else *) *)
  (* Inductive pMagma : Type -> Type := *)
  (*   | bp : forall A : Type, pMagma A *)
  (*   | pm_sum : forall (A B : Type), pMagma A -> pMagma B -> pMagma (A + B). *)

  (* Fixpoint SS_to_Magma (A : Type) (x : Symmetrix_Smash A) : pMagma A. *)
  (* Proof. *)
  (*   revert A a. *)
  (*   srapply @SS_rec. *)
  (*   - exact bp. *)
  (*   - exact (bp Empty). *)
  (*   - intro x. exact (bp Unit). *)
  (*   - reflexivity. *)
  (*   - intros A B a b. *)
  (*     apply pm_sum; apply SS_to_Magma. exact a. exact b. *)
  (*   - intros. exact (bp (A+B)). *)
  (*   - intros. cbn. *)
    
  (* Definition SS_to_Magma (A : Type) : Symmetric_Smash A -> (Magma A) + Unit. *)
  (* Proof. *)
  (*   revert A. *)
  (*   srapply @SS_rec. *)
  (*   - intros. exact (inr tt). *)
  (*   - cbn. exact (inl m0). *)
  (*   - cbn. intro x. exact (inl m1). *)
  (*   - cbn. *)


  


    

  
                                          



Section Generalized_Sphere.
  (* Want a map Type -> Type sending canon n to the n-sphere *)
  (* I.e. a generalization of the sphere to all types *)
  (* Also need that equalities of finite sets are sent to the right equalities. . . *)

  (* Variable smash : Type -> Type -> Type. *)
  (* Variable smash_S0_l : forall A : Type, smash ((pSphere 0) A <~> A. *)
  (* Variable smash_S0_r : forall A : Type, smash A (pSphere 0) <~> A. *)
  (* Variable smash_S1 : forall A : Type, smash A (pSphere 1) <~> Susp A. *)

  Inductive Empty' : Type :=.
  
  
  Inductive gSphere : Type -> Type :=
    |nil : Unit + Unit -> gSphere Empty
    |consL (A : Type) : Susp (gSphere A) -> gSphere (Unit + A)
    |consR (A : Type) : Susp (gSphere A) -> gSphere (A + Unit).

  Definition gSphere_ind_0 (P : gSphere Empty -> Type)
             (l : P (nil (inl tt)))
             (r : P (nil (inr tt)))
    :forall x : gSphere Empty, P x.
  Proof.
    recall Empty as A eqn:p.
    intro x.
    set (P' := fun (A' : Type) (x' : gSphere A') => { p : (Empty = A' :> Type) |  (P (transport gSphere p^ x'))}).
    apply pr2 (
    apply (gSphere_rect P').
    apply (ap P (transport gSphere p^)

    

  Definition gSphere_ind_0' (A : Type) (e : A = Empty) (P : gSphere A -> Type)
             (l : P (transport gSphere e^ (nil (inl tt))))
             (r : P (transport gSphere e^ (nil (inr tt)))) :
    forall x : gSphere A, P x.
  Proof.
    induction x.
    - 

      
      cut (idpath = e). intro p. destruct p.
      destruct s as [[]|[]].
      { assert (e = idpath). apply (hprop_Empty 
    
    intro x. revert x.
    recall Empty' as A eqn:p.
    intro x.
    apply (gSphere_rect (fun A (y : gSphere A) => (forall p : Empty' = A, P (transport gSphere p^ y)))).
    
    revert x. 
    

  Definition gSphere_0 : gSphere Empty <~> pSphere 0.
  Proof.
    

    


Old
Section Generalized_Sphere.
  (* Want a map Type -> Type sending canon n to the n-sphere *)
  (* I.e. a generalization of the sphere to all types *)
  (* What we need is that all these contain North and South, and then a map gSphere A -> North (A+Unit) = South (A+Unit) *)

  (* gSphere is for generalized_sphere *)
  Private Inductive gSphere : Type -> Type :=
  |gNorth (A : Type) : gSphere (A)
  |gSouth (A : Type) : gSphere (A)
  .

  Axiom gMerid : forall A : Type, gSphere A ->  gNorth (A + Unit) = gSouth (A + Unit).

  Definition gSphere_ind (P : forall A : Type, gSphere A -> Type)
             (H_N : forall A : Type, P A (gNorth A))
             (H_S : forall A : Type, P A (gSouth A))
             (H_merid : forall (A : Type) (x : gSphere A), transport (P (A + Unit)) (gMerid A x) (H_N (A + Unit)) = H_S (A + Unit))
    : forall (A : Type) (x : gSphere A), P A x.
  Proof.
    intros A x. destruct x. exact (H_N A). exact (H_S A).
  Defined.

  Axiom gSphere_ind_beta_merid : forall (P : forall A : Type, gSphere A -> Type)
                                        (H_N : forall A : Type, P A (gNorth A))
                                        (H_S : forall A : Type, P A (gSouth A))
                                        (H_merid : forall (A : Type) (x : gSphere A), transport (P (A + Unit)) (gMerid A x) (H_N (A + Unit)) = H_S (A + Unit))
                                        (A : Type) (x : gSphere A),
      apD (gSphere_ind P H_N H_S H_merid (A+Unit)) (gMerid A x) = H_merid A x. 

End Generalized_Sphere.

Definition gSphere_rec (P : forall A : Type, Type)
           (H_N : forall A : Type, P A)
           (H_S : forall A : Type, P A)
           (H_merid : forall A : Type, gSphere A -> H_N (A + Unit) = H_S (A + Unit))
  : forall A : Type, gSphere A -> P A.
Proof.
  apply (gSphere_ind (fun A _ => P A) H_N H_S).
  intros A x.
  exact (transport_const _ _ @ H_merid A x).
Defined.

Definition gSphere_rec_beta_merid (P : forall A : Type, Type)
           (H_N : forall A : Type, P A)
           (H_S : forall A : Type, P A)
           (H_merid : forall A : Type, gSphere A -> H_N (A + Unit) = H_S (A + Unit))
           (A : Type) (x : gSphere A)
  : ap (gSphere_rec P H_N H_S H_merid (A+Unit)) (gMerid A x) = H_merid A x.
Proof.
  apply (cancelL (transport_const (gMerid A x) (H_N (A + Unit)))).
  transitivity (apD (gSphere_rec P H_N H_S H_merid (A + Unit)) (gMerid A x)).
  symmetry; refine (apD_const (gSphere_rec P H_N H_S H_merid (A + Unit)) _).
  refine (gSphere_ind_beta_merid (fun A _  => P A) _ _ _ _ _).
Defined.

Definition gSphere_to_pSphere (A : Type) (n : nat) (e : A <~> Fin n) : gSphere A -> pSphere n.
Proof.
  revert A e.
  induction n.
  - intros A e x. revert A x e.
    srapply @gSphere_rec; cbn.
    intros. exact (inl tt). intros. exact (inr tt).
    cbn. intros. apply path_arrow. intro e. apply Empty_rec. exact (e (inr tt)).
  - intro A. intros e x. revert A x n e IHn.
    srapply @gSphere_rec; cbn.
    intros. exact North.
    intros. exact South.
    intros A x. cbn. apply path_forall. intro n. apply path_forall. intro e. apply path_forall. intro H.
    apply merid. apply (H A). exact (equiv_restrict e). exact x.
Defined.

  
(*   intro x. revert A x n e. *)
(*   srapply (@gSphere_rec (fun A => forall n : nat, A <~> Fin n -> pSphere n)); cbn.  *)
(*   - intros A n e. *)
(*     destruct n. exact (inl tt). exact North. *)
(*   -  intros A n e. *)
(*      destruct n. exact (inr tt). exact South. *)
(*   - cbn.  *)
(*     intro A. intro x. apply path_forall. intro n. apply path_forall. intro e. revert e. *)
(*     revert x. revert A. *)
(*     destruct n. *)
(*     { intros. apply Empty_rec. exact (e (inr tt)).  } (* Do away with base case *) *)
(*     intros. *)
(*     apply merid. *)
(*     refine (gSphere_to_pSphere A n _ x). *)
(*     exact (equiv_restrict e). *)
(* Defined. *)

(* (* Have to prove that this respects the beta rule *) *)
(* Definition gSphere_to_pSphere_beta_merid (A : Type) (n : nat) (e : A + Unit <~> Fin n.+1) (x : gSphere A) : *)
(*   ap (gSphere_to_pSphere (A + Unit) n.+1 e) (gMerid A x) = merid (gSphere_to_pSphere A n (equiv_restrict e) x). *)
(* Proof. *)
(*   revert n e. *)
(*   revert A x. srapply @gSphere_ind. *)
(*   intros. cbn. intros. *)
(*   refine (_ @ gSphere_rec_beta_merid *)
(*   rewrite (gSphere_rec_beta_merid). *)

Definition pSphere_to_gSphere (* (A : Type) *) (n : nat) (* (e : A <~> Fin n) *) : pSphere n -> gSphere (Fin n).
Proof.
  (* intro x. apply (transport gSphere (path_universe e)^). revert x. clear e. clear A. *)
  induction n.
  - intros [[]|[]]. exact (gNorth _). exact (gSouth _).
  - srapply @Susp_rec.
    exact (gNorth _). exact (gSouth _).
    intro x. apply gMerid. apply IHn. exact x.
Defined.

Definition gSphere_finite_equal_sphere : forall (* (A : Type) *) (n : nat) (* (e : A <~> Fin n) *), gSphere (Fin n) <~> pSphere n.
Proof.
  (* induction n. *)
  (* - intro e. *)
  (*   destruct (path_universe e)^. *)
  (*   srapply @equiv_adjointify. *)
  (*   + intro x. induction x. *)
  (*     { exact (inl tt). } {exact (inr tt). } *)
  intros.
  - srapply @equiv_adjointify.
    apply (gSphere_to_pSphere (Fin n) n equiv_idmap).
    apply (pSphere_to_gSphere n).
    +  unfold Sect.
       induction n.
       { intros [[]|[]]; reflexivity. }
       srapply @Susp_ind.
       * cbn. reflexivity.
       * cbn. reflexivity.
       * intro x.
         refine (transport_paths_FlFr (f := (fun y : Susp (pSphere n) => gSphere_to_pSphere (Fin n.+1) n.+1 1 (pSphere_to_gSphere n.+1 y)))
                                      (merid x) idpath @ _).
         rewrite ap_idmap. rewrite concat_p1.
         apply moveR_Vp. rewrite concat_p1. apply inverse.
         rewrite (ap_compose (pSphere_to_gSphere n.+1) (gSphere_to_pSphere (Fin n.+1) (n.+1) equiv_idmap)).
         rewrite Susp_rec_beta_merid.
         change  with (Fin n).
         
         cbn. simpl.
         rewrite gSphere_rec_beta_merid.
         
         
         
         
         cbn.
         
         (* Must define gSphere differently so that gSphere_to_pSphere is only by induction? *)
         
         
.
         
    + 

       
    
    + intro x. revert e. revert n. revert x. revert A.
      srapply (@gSphere_rec (fun A => forall n : nat, A <~> Fin n -> pSphere n)); cbn. 
      * intros A n e.
        destruct n. exact (inl tt). exact North.
      * intros A n e.
        destruct n. exact (inr tt). exact South.
      * cbn. 
        intro A. intro x. apply path_forall. intro n. apply path_forall. intro e.
        revert e. revert x. revert A.
        destruct n.
        { intros. apply Empty_rec. apply e. exact (inr tt). } (* Do away with base case *)
        intros.
        apply merid. 
        
        

        cbn. apply path_arrow. intro e.
        induction n.
      
      * intros n e. destruct n.
        exact (inl tt). exact North.
      * intros n e. destruct n.
        { exact (inr tt). } exact South.
    + revert A e. induction n.
      intros A e [_ |_ ]. exact (north A). exact (south A).
      intros A e.
      srapply @Susp_rec.
      * exact (north A).
      * exact (south A).
      * intro x.
        rewrite (path_universe e).
        apply merid'.
        apply IHn. apply equiv_idmap. exact x.
    + unfold Sect.
      destruct n.
      { cbn. intros [[]|[]]; reflexivity. }
      srapply @Susp_ind; try reflexivity.
      * cbn. 
      


        destruct (fin_empty n e^-1)^. exact (inr tt).
      * intros n e. 
        cut (exists m : nat, n = m.+1%nat).
        { intros [m p]. rewrite p. rewrite p in e. clear p.
          north A x
          
          apply (IHx m.+1%nat).
          revert x.
          
          