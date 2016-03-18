Require Import HoTT.

Local Open Scope pointed_scope.

Section pType_prelim.

(* 	(*The constant map between two pointed types*)
	Definition const_map (A B: pType) : A->B := 
		fun a:(pointed_type A) => point B.
 *)
	(*This map is a pointed map*)
	Definition pconst (A B: pType) : pMap A B := 
		Build_pMap A B (const (point B)) idpath.
	
	Global Instance ispointed_pmap {A B:pType} : IsPointed (pMap A B) := 
		pconst A B.
	
	(* (*The pointed type of pointed maps
		(Overwrite the standard definition, which is not a pointed type)*)
	Definition ptMap (A B: pType) : pType := 
		Build_pType (pMap A B) (const_pmap A B).
	 *)
	 
	(*Define the pointed sphere. 
	It is not evident here, but the baspoint is always North.*)
	Fixpoint pSphere (n:nat) : pType :=
		match n with
		|O => Build_pType (Sphere O) North
		|S n => psusp (pSphere n)
		end.
	Definition add_pt (A:Type) :  pType := Build_pType (A+Unit) (inr tt).
	Definition pBool : pType := Build_pType Bool true.
	Definition pUnit : pType := Build_pType Unit tt.
	
	(*Define the wedge. The basepoint could just as well have been pushr tt,
	but some choice had to be made.*)
	Definition wedge (A B:pType) := 
		Build_pType 
			(pushout (@const Unit A (point A)) (@const Unit B (point B) ) )
			(pushl tt).
	
	Definition sum_to_product {A B:pType} (x : A+B) : A*B:=
		match x with
			|inl a => (a, point B)
			|inr b => (point A, b)
		end.
	
	Definition wedge_in_product {A B:pType} : wedge A B -> A*B :=
		pushout_rec (A*B) sum_to_product (fun _ => idpath).
	
	Definition smash (A B : pType) :=
		pushout (wedge_in_product) (pconst (wedge A B) pUnit).
	
	Lemma const_comp (A B C: pType) (f:A->*B) : 
		pconst B C o* f = pconst A C.
		Proof.
		decompose record f.
		unfold pconst.
		unfold pmap_compose ; simpl.
		unfold const. 
		rewrite ap_const; simpl.
		reflexivity.
	Qed.
	
	Definition sph0xA_to_A {A:pType} : A*(Sphere 0) -> A.
		intro p; elim p.
		intro a.
		exact (Susp_rec (point A) (a) (Empty_rec)).
	Defined.
	
	
	Definition smash_A_to_A  {A:pType} : smash A (pSphere 0)  -> A.
		refine (pushout_rec _ _ _).
		-intro x. elim x.
			+exact sph0xA_to_A.
			+exact (pconst _ _).
		-simpl. refine (pushout_ind _ _ _ _ _).
			+apply sum_ind.
				*intro a. exact idpath.
				*unfold const.
				apply (@Susp_ind Empty _ idpath idpath). apply Empty_ind.
			+simpl.
			intro a; destruct a. 
			unfold const at 11.
			
				
				intro w.
				
			
			unfold wedge_in_product.
			unfold sum_to_product.
			simpl.
			
			
			
			unfold wedge_in_product.
			unfold sph0xA_to_A.
			simpl.
			
			
			admit.
	Admitted.
	
	
End pType_prelim.

(*Show that my two-pointed types are equivalent*)
Section Two_points.
	Definition two_pts := add_pt Unit.
	
	Definition pBool_to_two_pts : pBool ->* two_pts.
		refine (Build_pMap _ _ _ _).
				(*Construct map*)
				-intro b.	exact (if b then (inr tt) else (inl tt)).
				(*Show it is pointed.*)
				-exact idpath.
	Defined.

	Definition two_pts_to_bool : add_pt Unit -> pBool.
		intro x; elim x.
					(*Left element (non-basepoint*)
					apply Unit_rec. exact false.
					(*Right element (basepoint)*)
					apply Unit_rec. exact true.
	Defined.
	
	Definition Sect_1 : Sect two_pts_to_bool pBool_to_two_pts.
		unfold Sect. induction x.
				+ induction a. exact idpath.
				+ induction b. exact idpath.
	Defined.

	Definition Sect_2 : Sect pBool_to_two_pts two_pts_to_bool.
			-unfold Sect. apply Bool_ind ; exact idpath.
	Defined.
	
	Lemma pequiv_bool_addpt1 : pBool <~>* add_pt Unit.
		Proof.
		refine (Build_pEquiv pBool (add_pt Unit) pBool_to_two_pts _).
		refine (BuildIsEquiv pBool (add_pt Unit) pBool_to_two_pts two_pts_to_bool Sect_1 Sect_2 _).
		apply Bool_ind ; reflexivity.
	Qed.
	
	Definition pMap_to_Map {A:Type } {B:pType} : ( (add_pt A) ->* B  ) -> ( A -> (pointed_type B) ).
		intro f.
		exact (f o inl).
	Defined.
	
	Definition Map_to_pMap {A:Type } {B:pType} : ( A->(pointed_type B) ) -> ( (add_pt A) ->* B  ).
		intro f.
		transparent assert (h: (add_pt A -> B)).
			-intro x.
			exact match x with
				|inl a => f a
				|inr u => (match u with | tt => point B end)
			end.
		-exact (Build_pMap _ _ h idpath).
	Defined.

	
	(*Lemma 6_5_3 in book:*)
	Lemma addpt_forget_adjoint {A:Type} {B:pType} : 
		( (add_pt A) ->* B  ) <~> ( A -> (pointed_type B) ).
		refine (BuildEquiv _ _ pMap_to_Map _ ).
		refine (BuildIsEquiv _ _ pMap_to_Map Map_to_pMap _ _ _).
			-exact (fun _ => idpath).
			-unfold Sect.
			intro f; destruct f.
			rename pointed_fun into pf; rename point_eq into pe.
			unfold pMap_to_Map. simpl.
			
			simpl in pe. unfold point in pe at 1.
			unfold Map_to_pMap.
			
			
	Admitted. (*TODO*)
  
	
	Lemma twotoA_is_A {A:pType} : (two_pts ->* A) <~> A.
		(*TODO: Find result on  Unit->A <~> A  *)
	Admitted.
	

End Two_points.

Section Loops.
	(*Define Omega n A as pointed maps from the n-sphere*)
	Definition Omega (n:nat) (A:pType) :pType :=
		Build_pType (pMap (pSphere n) A) _.
		
Lemma Omega0_Equiv_A {A:pType} : Omega 0 A <~> A.
	unfold Omega.
		cut ( (pSphere 0 ->* A) <~> (two_pts ->* A) ).
			-intro f.
			(*TODO*)
			(* exact (equiv_compose addpt_forget_adjoint f).
			
			exact ( functor_arrow pBool_to_two_pts idmap ).
	 *)
	Admitted.

	(*This should be equivalent to the loop space in the library*)
	Theorem omega_loops_equiv `{Funext} : forall n:nat, forall A:pType,
		Omega n A <~> iterated_loops n A.
		induction n.
			-intro A. exact Omega0_Equiv_A.
			-intro A.
			equiv_via (pSphere n ->* loops A).
				+apply loop_susp_adjoint.
				+exact (IHn (loops A) ).
	Qed.
	
	(*TODO*) Theorem omega_loops_peq `{Funext} :forall n:nat, forall A:pType,
		Omega n A <~>* iterated_loops n A. Abort.

End Loops.

Section homotopy_groups.


Definition homotopy_group (n:nat) (A:pType) :pType :=
	pTr 0 (Omega n A).

Notation "'HtGr'" := homotopy_group.

Definition SphereToOmega_functor {m n:nat} (f:pSphere m ->* pSphere n) (A:pType) :
	Omega n A ->* Omega m A.
	
	refine (Build_pMap _ _ _ _).
	(*Define the map*)
	* intro h. exact (h o* f).
	(*Prove that it is pointed map.*)
	* apply const_comp.
Defined.

Definition OmegaToHtGr_functor {m n : nat} {A:pType} (f : Omega n A ->* Omega m A) :
	HtGr n A ->* HtGr m A.
	
	refine (Build_pMap _ _ _ _).
	(*Construct map*)
	*apply Trunc_rec.
	intro loop.
	apply tr.
	exact (f loop).
	(*Show that it is pointed.*)
	*apply (ap tr).
	rewrite (point_eq f).
	reflexivity.
Defined.

Definition SphereToHtGr_functor {m n : nat} (f:pSphere m ->* pSphere n) (A:pType) :
	HtGr n A ->* HtGr m A :=
		OmegaToHtGr_functor (SphereToOmega_functor f A).
		
		
		
		
(*Stuff that probably should be removed:*)

(*Alternative definition to Omega. Should be possible to show that these are equivalent.*)
Fixpoint Omega' (n:nat) (A:pType) : pType :=
	match n with
		|O => A
		|S n => Build_pType (point A = point A) idpath
	end.



Definition pSph0_to_Bool : pSphere 0 ->* pBool.
	refine (Build_pMap _ _ _ _).
			-exact Sph0_to_Bool.
			-reflexivity.
Defined.

Lemma isequiv_pSph0_to_Bool : IsEquiv pSph0_to_Bool.
	exact isequiv_Sph0_to_Bool.
Qed.

(* Definition sph0map_to_boolmap {A:pType} : (pBool -> A) -> (pSphere 0 -> A)
	 := functor_arrow pSph0_to_Bool idmap.

Lemma isEquiv_sph0mapToBoolmap `{Funext} {A:pType} : IsEquiv (@sph0map_to_boolmap A).
	apply isequiv_functor_arrow.
Qed. *)

Lemma equiv_sph0pMap_boolpMap `{Funext} {A:pType} : (pBool ->* A) <~> (pSphere 0 ->* A).
	refine (BuildEquiv _ _ _ _).
		*intro f.
		refine (Build_pMap _ _ _ _).
			-exact (sph0mapToBoolmap f).
			-(* cbn. *)
			unfold sph0mapToBoolmap.
			unfold functor_arrow.
			unfold functor_forall.
			rewrite (point_eq pSph0ToBool).
			exact (point_eq f).
		*refine (BuildIsEquiv _ _ _ _).
	

(* Lemma pIsEquiv_Sph0ToBool : IsEquiv pSph0ToBool.
	exact isequiv_Sph0_to_Bool.
Defined. *)


(*Construct map equivalence between omega and iterated loops (base case)*)

Definition f {A:pType} : Omega 0 A -> A.
	intro h.
	exact (h South).
Defined.

Definition g {A:pType} : A -> Omega 0 A.
	intro a.
	unfold Omega.
	refine (Build_pMap _ _ _ _).
		(*Construct map from S^0 to A. North is mapped to point A, South is mapped to a.*)
		*transparent assert (bin : (Bool -> A)).
			intro b.
			exact match b with
				|true => point A
				|false => a
			end.
		exact (bin o pSph0ToBool).
		*reflexivity.
Defined.

Lemma Omega0_Equiv_A {A:pType} : Omega 0 A <~> A.
	refine (BuildEquiv _ _ _ _).
		*exact f.
		*refine (BuildIsEquiv  _ _ _ _ _ _ _).
			-exact g.
			-unfold Sect. reflexivity. (*fg==id*)
			-unfold Sect. (*gf==id*)
			intro h.
			
			unfold Omega.
			intro h.
			unfold f.
			unfold g.
			intro x; elim x; intros h p; clear x.
			simpl.
			unfold g.
			unfold point at 1 in p. simpl in p.
			
Theorem omega_loops_equiv `{Funext} : forall n:nat, forall A:pType,
	Omega n A <~> iterated_loops n A.
	intros n A.
	induction n.
	(*Base case*)
		*refine (BuildEquiv _ _ _ _).
			(*Construct equivalence*)
			-simpl. 
			intro f.
			exact (f South).
			(*Show that it is an equivalence*)
			-refine (BuildIsEquiv  _ _ _ _ _ _ _).
				(*Construct inverse*)
				+simpl.
				intro a.
				refine (Build_pMap _ _ _ _).
				transparent assert (g : (Susp Empty -> A)).
					intro x.
					exact (match x with
						|North => point A
						|South => a
					end ).
