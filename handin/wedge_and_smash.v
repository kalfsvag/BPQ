Require Import HoTT.
Load pType_basics.

Section wedge_and_smash.
	(*Define the wedge. The basepoint could just as well have been pushr tt,
	but some choice had to be made.*)
(* 	Definition wedge (A B:pType) := 
		Build_pType 
			(pushout (unit_name (point A)) (unit_name (point B) ) )
			(pushl tt). *)
	Definition wedge (A B : pType) := pushout (unit_name (point A)) (unit_name (point B) ).
	
	Global Instance ispointed_wedge {A B:pType} : IsPointed (wedge A B) := pushl tt.
	
	Definition sum_to_wedge {A B:pType} : (A+B)->(wedge A B) := push.
	
	Definition wedgepath {A B:pType} : 
		sum_to_wedge (inl (point A)) = sum_to_wedge (inr (point B)) 
		:= pp tt.
	
	
	Definition wedge_ind {A B:pType} 
		(P : (wedge A B)->Type) 
		(f:forall x:A + B, P (sum_to_wedge x)) 
		(pp' : forall u : Unit, transport P (pp u) (f (inl (point A))) = f (inr (point B)) )
		:forall w : wedge A B, P w.
			exact (pushout_ind 
				(unit_name (point A)) 
				(unit_name (point B)) 
				P
				f
				pp').
	Defined.
	
	(*To construct a map out of a wedge, you need:
		-map from A
		-map from B 
		-and a proof that these map the basepoints to the same point.*)
	Definition wedge_rec {A B : pType}
		(P : Type)
		(f : A+B->P)
		(pp' : f (inl (point A)) = f (inr (point B) )) : (wedge A B) -> P.
			refine (pushout_rec _ f _).
			 -exact (fun _ => pp'). (* intros []. exact pp'. *)
	Defined.
	
	Ltac path_via mid :=
		apply (concat (y:=mid)).
	
	Definition wedge_functor {A B C D:pType} (f:A->*C) (g:B->*D) : 
		(wedge A B) -> (wedge C D).
			rapply (@wedge_rec A B).
				-exact (sum_to_wedge o (functor_sum f g)).
				-
				path_via (@sum_to_wedge C D (inl (point C))).
					exact (ap (sum_to_wedge o inl) (point_eq f)).
					path_via (@sum_to_wedge C D (inr (point D))).
						exact wedgepath.
						exact (ap (sum_to_wedge o inr) (point_eq g)^).
	Defined.
	(*Todo:	Show that the result is a pMap*)
	
	Definition sum_to_product {A B:pType} (x : A+B) : A*B:=
		match x with
			|inl a => (a, point B)
			|inr b => (point A, b)
		end.
	
	Definition wedge_in_prod {A B:pType} : wedge A B -> A*B :=
		wedge_rec (A*B) sum_to_product idpath.
	
	Definition pair' {A B:Type} : B->A->A*B := fun (b:B) (a:A) => pair a b.
	 (*TODO: Flip*)
	Definition natural_wedge_in_prod {A B C D: pType} (f:A->*C) (g:B->*D) : 
		forall w : wedge A B, 
		functor_prod f g (wedge_in_prod w) = wedge_in_prod (wedge_functor f g w).
		rapply (@wedge_ind A B).
			intros [a|b].
				(* +apply path_prod.
					exact idpath.*)
				+exact (ap (pair (f a)) (point_eq g) ).
				+exact (ap (flip (pair) (g b)) (point_eq f) ).
				(*
				exact (ap011 pair (point_eq f) idpath).
				 
				apply (ap (fun d:D => (f a, d))).
				exact (point_eq g).
				+apply (ap (fun c:C => (c, g b))).
				exact (point_eq f). *)
				+intros [].
		Admitted.
	
	Definition smash (A B : pType) :=
		pushout (@const (wedge A B) Unit tt) (wedge_in_prod).
	
(* 	Definition smashpush {A B:pType} :=
		@push (wedge A B) pUnit (A*B) (@const (wedge A B) Unit tt) wedge_in_prod.
		(*TODO: Remove residues of smashpush*)
 *)	
	Definition prod_to_smash {A B:pType} (pair:A*B) : smash A B
		 := push (inr pair).
	
	Global Instance ispointed_smash {A B:pType} : IsPointed (smash A B) := push (inl tt).
	
	Definition smash_rec {A B:pType} 
		(P:Type)
		(basepoint:P)
		(f:A*B->P)
		(Ht: forall w : wedge A B, basepoint = f (wedge_in_prod w)) : (smash A B) -> P.
			refine (pushout_rec _ _ _).
			-intros [ [] | pair ].
				+exact (basepoint).
				+exact (f pair).
			-exact Ht.
	Defined.
	
	
	(*TODO : Smash and wedge are pointed. Functors map to pointed maps.*)
	(*TODO: Comment better.*)
	
		Definition smash_functor {A B C D:pType} (f:A->*C) (g:B ->* D) :
		smash A B -> smash C D.
 			rapply (@smash_rec A B).
			-exact (ispointed_smash). (*Basepoint*)
			-exact (prod_to_smash o (functor_prod f g)). (* : A*B -> smash C D*)
			(*Well defined:*)
			-simpl. intro w.
			path_via (prod_to_smash (wedge_in_prod (wedge_functor f g w))).
				+unfold prod_to_smash. unfold ispointed_smash.
				exact (pp (wedge_functor f g w)).
				+exact (ap prod_to_smash (natural_wedge_in_prod f g w))^.
		Defined.
End wedge_and_smash.

