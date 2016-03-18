(*TODO : Import definitions*)
Require Import HoTT.










(*Stuff that probably should be removed:*)
(* 
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
	Qed. *)