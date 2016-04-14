Require Import HoTT.

Load wedge_and_smash.
(*
Definition m : S1 -> S1 -> S1.
  refine (S1_rec _ (S1_rec _ base idpath) idpath).
  *)

Definition multN : S1 -> S1 := idmap.

Definition multS : S1 -> S1.
  refine (S1_rec S1 base loop^).
refine (Coeq_rec S1 _ _).
  


Section myS1.
  Definition S1 := pSphere 1.
  Definition fig_eight := wedge S1 S1.
  (*
Definition m1 : S1 * S1 -> S1.
  intros [x y].
  refine (Susp_rec _ _ _ _).
  -exact S1.
  -
   *)
  Definition multN : S1 -> S1 := idmap.

  Definition multS : S1 -> S1. (*Rotation the circle by 90 degrees*)
    refine (Susp_rec South North _).
    +refine (Susp_rec (merid South)^ (merid North)^ Empty_rec). 
  Defined.

  Definition m1 `{Funext}: S1 -> S1 -> S1.
    refine (Susp_rec multN multS _).
    -(*Define functions giving multiplication by paths*)
      refine (Susp_rec _ _ _).
      +(*Multiplication by merid N*)
        apply path_forall.
        refine (Susp_ind _ _ _ _).
        * (* merid N x N *) 
          exact (merid North).
        * (* merid N x S*) 
          exact (merid South)^.
          * refine (Susp_ind _ _ _ _).
          { (*merid N * merid N*) 
            rewrite transport_paths_FlFr. (*TODO: Make transparent*) hott_simpl.
            refine (@Susp_comp_nd_merid S1 S1 South North _ North ).
            
            
            
            
            
            



