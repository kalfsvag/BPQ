Require Import HoTT.
Local Open Scope pointed_scope.

Section pType_prelim.
	

	(*The constant map between ptypes.*)
	Definition pconst (A B: pType) : pMap A B := 
		Build_pMap A B (const (point B)) idpath.
	
	Global Instance ispointed_pmap {A B:pType} : IsPointed (pMap A B) := 
		pconst A B.
	
	(*Define the pointed sphere. 
	It may not be evident here, but the basepoint is always North.*)
	Fixpoint pSphere (n:nat) : pType :=
		match n with
		|O => Build_pType (Sphere O) North
		|S n => psusp (pSphere n)
		end.
	Definition add_pt (A:Type) :  pType := Build_pType (A+Unit) (inr tt).
	(* 
	Definition pBool : pType := Build_pType Bool true. *)
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
	
	Definition natural_sphere {m n:nat} (k:nat) (f:pSphere m->*pSphere n) :
		pSphere (k+m) ->* pSphere (k+n).
		induction k.
			-exact f.
			-exact (psusp_functor IHk).
	Defined.

End pType_prelim.

Ltac phomotopy_via mid := apply (phomotopy_compose (g := mid)).