Require Import HoTT.
Require Import UnivalenceAxiom.


Definition Type_Over (X : Type)   :=
  {Y : Type & Y -> X}.


Definition type_of_over {X : Type}: (Type_Over X) -> Type := pr1.

Coercion type_of_over : Type_Over >-> Sortclass.

Context {X : Type}.

Definition prod_over : (Type_Over X) -> (Type_Over X) -> Type_Over X.
Proof.
  intros [A f] [B g].
  exists ({ a : A & {b : B & f a = g b}}).
  intros [a b]. exact (f a).
Defined.

Definition fst_over (A B : Type_Over X)
  : prod_over A B -> A.
Proof.
  intros [a b]. exact a.
Defined.

Definition snd_over (A B : Type_Over X)
  : prod_over A B -> B.
Proof.
  intros [a [b p]]. exact b.
Defined.

Definition sum_over : (Type_Over X) -> (Type_Over X) -> Type_Over X.
Proof.
  intros A B.
  exists (pushout (fst_over A B) (snd_over A B)).
  destruct A as [A f]. destruct B as [B g].
  srapply @pushout_rec.
  - intros [a | b]. exact (f a). exact (g b).
  - intros [a [b p]]. exact p.
Defined.

Definition assoc_prod_over : forall A B C : Type_Over X,
    prod_over A (prod_over B C) = prod_over (prod_over A B) C.
Proof.
  intros [A f] [B g] [C h].
  srapply @path_sigma.
  - simpl.
    srapply @path_universe.
    { intros [a [[b [c p]] q]].
      srapply @existT.
      exists a. exists b. exact q.
      exists c. exact (q @ p). }
    srapply @isequiv_adjointify.
    { intros [[a [b p] [c q]]].
      exists a. srapply @existT. exists b. exists c. exact (p^ @ q). exact p. }
    + intros [[a [b p] [c q]]].
      srapply @path_sigma. reflexivity.
      srapply @path_sigma. reflexivity. 
      cbn. apply moveR_Mp. reflexivity.
    + intros [a [[b [c p]] q]].
      srapply @path_sigma. reflexivity.
      srapply @path_sigma.
      srapply @path_sigma. reflexivity.
      srapply @path_sigma. reflexivity.
      cbn. apply moveR_Vp. reflexivity.
      cbn.
      refine
        (transport_paths_Fr
           (path_sigma (fun a0 : B => {b0 : C & g a0 = h b0}) (b; (c; q^ @ (q @ p))) (b; (c; p)) 1
                       (path_sigma (fun b0 : C => g b = h b0) (c; q^ @ (q @ p)) (c; p) 1 (moveR_Vp (q @ p) p q 1)))
           q @ _).
      apply moveR_Mp.
      refine (_ @ (concat_Vp q)^).
      refine (ap_compose pr1 g (path_sigma (fun a0 : B => {b0 : C & g a0 = h b0}) (b; (c; q^ @ (q @ p))) (b; (c; p)) 1
       (path_sigma (fun b0 : C => g b = h b0) (c; q^ @ (q @ p)) (c; p) 1 (moveR_Vp (q @ p) p q 1))) @ _).
      
      change 
      apply pr1_path_sigma.
      
      refine (transport_compose (fun b0 : B => f a = g b0)
                                (fun x : {a0 : B & {b0 : C & g a0 = h b0}} => pr1 x) _ _ @ _).
      
    
    
    refine (transport_pr1_path_sigma _ _ _ @ _).
    
    
    
    
    
    



(* Todo: Associativity of intersect *)
(* Distributy law *)
(* Closed under injections *)

