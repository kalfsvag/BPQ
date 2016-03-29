Require Import HoTT.
Local Open Scope pointed_scope.

(*Shorthand for making a pointed type from a type. (Assuming that an instance of IsPointed is made earlier)*)
Notation "'p' A" := (Build_pType A _) (at level 0). (*TODO: What level to choose?*)

Ltac pHomotopy_via mid := apply (phomotopy_compose (g := mid)).


Section pType_prelim.
	

	(*The constant map between ptypes.*)
	Definition pconst (A B: pType) : pMap A B := 
		Build_pMap A B (const (point B)) idpath.
	(*The constant map is base point for the type pMap A B*)
	Global Instance ispointed_pmap {A B:pType} : IsPointed (pMap A B) := 
		pconst A B.
	
	(*Define the pointed sphere. 
	It may not be evident here, but the basepoint is always North.*)
	Fixpoint pSphere (n:nat) : pType :=
		match n with
		|O => Build_pType (Sphere O) North
		|S n => psusp (pSphere n)
		end.
        
        (*The functor from Type to pType*)
	Definition add_pt (A:Type) :  pType := Build_pType (A+Unit) (inr tt).
	
	Global Instance ispointed_unit : IsPointed Unit := tt.
	
	Lemma const_comp (A B C: pType) (f:A->*B) : 
		pconst B C o* f = pconst A C.
		Proof.
		unfold pconst.
		unfold pmap_compose ; simpl.
		unfold const. 
		rewrite ap_const; simpl.
		reflexivity.
	Qed.
	
	Definition functor_sphere {m n:nat} (k:nat) (f:pSphere m->*pSphere n) :
		pSphere (k+m) ->* pSphere (k+n).
		induction k.
			-exact f.
			-exact (psusp_functor IHk).
	Defined.
	
End pType_prelim.