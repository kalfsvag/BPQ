Require Import HoTT.
Require Import UnivalenceAxiom.
Load finite.
Load stuff.

Require Import Functor Category.
(*These notations are defined elsewhere, but I do not know how to import it.*)
Local Notation "x --> y" := (morphism _ x y) (at level 99, right associativity, y at level 200) : type_scope.
Notation "F '_0' x" := (Functor.Core.object_of F x) (at level 10, no associativity, only parsing) : object_scope.
Notation "F '_1' m" := (Functor.Core.morphism_of F m) (at level 10, no associativity) : morphism_scope.
Open Scope category_scope.
Open Scope morphism_scope.



Definition Nerve (n : nat) (C : PreCategory) := {c : C*^(n.+1) & (forall j : Fin n, projection
