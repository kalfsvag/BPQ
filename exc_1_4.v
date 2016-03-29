Require Import HoTT.
(*Require Import Coq.Program.Tactics.*)

Section Book_1_4.
  Variable C:Type.

  (*Defining the iterator.*)
  Fixpoint iter (C:Type) (c0:C) (cs:C->C) (n:nat) : C := 
    match n with
      |O=>c0
      |S p => cs (iter C c0 cs p)
    end.


  (*Make an iterative step function N*C->N*C from the recursive step function cs.*) 
  Definition c_it (cs:nat->C->C) : (nat*C -> nat*C) :=
    fun p => match p with (n,c) => (S n, cs n c) end.

  (*Define recursion in terms of the iterator.*)
  Definition Rec (c0:C) (cs : nat->C->C) (n:nat) : C :=
    snd (iter (nat*C) (O,c0)  (c_it cs) n).

  Lemma iter_formula : forall (n:nat) (c0:C) (cs : nat->C->C), 
                         iter (nat*C) (O,c0) (c_it cs) n = (n, Rec c0 cs n).
  Proof.
    intros n c0 cs.
    induction n.
    *(*Base case*)
      reflexivity.
      
    *(*Step case*)
      simpl.
      unfold Rec.
      simpl.
      rewrite IHn.
      simpl.
      unfold c_it.
      reflexivity.
  Qed.

  Proposition Rec_equals_natrec : forall (c0:C)(cs : nat->C->C)(n:nat), 
                                    Rec c0 cs n = nat_rec C c0 cs n.
  intros c0 cs.
  induction n.
  *(*Base case:*)
    reflexivity.
    
  *(*Step case*)
    simpl.
    rewrite <- IHn.
    unfold Rec at 1.
    simpl.
    rewrite iter_formula.
    simpl.
    reflexivity.
  Qed.

End Book_1_4.