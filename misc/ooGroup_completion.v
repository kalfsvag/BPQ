Load classifying_space.
Open Scope monoid_scope.

(*Defining the classifying space of a monoid quick and dirty*)
Definition B (M : Monoid) := B2 M.
Definition B_loop {M : Monoid} := @B2_loop M.
Definition B_resp_mul {M : Monoid} (m n : M) := @B2_resp_mul M m n.
Definition B_resp_id {M : Monoid} := @B2_resp_id M.

Section trystuff.
  Variable M : Monoid.
  Variable C : Type. Variable Cp : M -> C.
  Variables l m n : M.
End trystuff.

Definition C_id {M : Monoid}
           {C : Type} {c0 : C}
           {Cp : M -> c0 = c0}
           (Cmul : forall m n : M, Cp (m + n) = Cp m @ Cp n) :
  Cp (mon_id M) = idpath.
Proof.
  apply (cancelR _ _ (Cp (mon_id M))).
  refine (_ @ (concat_1p _)^).
  refine (_ @ (ap Cp (mon_lid (mon_id M)))).
  apply (Cmul (mon_id M) (mon_id M))^.
Defined.
  

(*Now comes the cheating*)
Definition B_rec {M : Monoid}
           (C : Type) (c0 : C)
           (Cp : M -> c0 = c0)
           (Cmul : forall m n : M, Cp (m + n) = Cp m @ Cp n)
           (C_assoc : forall l m n : M,
                       ap Cp (@mon_assoc M l m n) @ Cmul (l + m) n @ whiskerR (Cmul l m) (Cp n) =
                       Cmul l (m + n) @ whiskerL (Cp l) (Cmul m n) @ concat_p_pp (Cp l) (Cp m) (Cp n))
           (C_lid : forall m : M,
                      ap Cp (mon_lid m) =
                      Cmul (mon_id M) m @ whiskerR (C_id Cmul) (Cp m) @ (concat_1p (Cp m)))
           (C_rid : forall m : M,
                      ap Cp (mon_rid m) =
                      Cmul m (mon_id M) @ whiskerL (Cp m) (C_id Cmul) @ (concat_p1 (Cp m)))
                       
           : B M -> C
  := B2_rec C c0 Cp Cmul. (*Cheating cheating cheating*)

Definition B_rec_beta_Cp {M : Monoid}
           (C : Type) (c0 : C) (Cp : forall m : M, c0 = c0)
           (Cmul : forall m n : M, Cp (m + n) = Cp m @ Cp n)
           (C_assoc : forall l m n : M,
                       ap Cp (@mon_assoc M l m n) @ Cmul (l + m) n @ whiskerR (Cmul l m) (Cp n) =
                       Cmul l (m + n) @ whiskerL (Cp l) (Cmul m n) @ concat_p_pp (Cp l) (Cp m) (Cp n))
           (C_lid : forall m : M,
                      ap Cp (mon_lid m) =
                      Cmul (mon_id M) m @ whiskerR (C_id Cmul) (Cp m) @ (concat_1p (Cp m)))
           (C_rid : forall m : M,
                      ap Cp (mon_rid m) =
                      Cmul m (mon_id M) @ whiskerL (Cp m) (C_id Cmul) @ (concat_p1 (Cp m)))
           (m : M) :
  ap (B_rec C c0 Cp Cmul C_assoc C_lid C_rid) (B_loop m) = Cp m.
  apply B2_rec_beta_l.
Defined.

(*Inconsistent:*)
Definition B_rec_beta_Cmul {M : Monoid}
           (C : Type) (c0 : C) (Cp : forall m : M, c0 = c0)
           (Cmul : forall m n : M, Cp (m + n) = Cp m @ Cp n)
           (C_assoc : forall l m n : M,
                       ap Cp (@mon_assoc M l m n) @ Cmul (l + m) n @ whiskerR (Cmul l m) (Cp n) =
                       Cmul l (m + n) @ whiskerL (Cp l) (Cmul m n) @ concat_p_pp (Cp l) (Cp m) (Cp n))
           (C_lid : forall m : M,
                      ap Cp (mon_lid m) =
                      Cmul (mon_id M) m @ whiskerR (C_id Cmul) (Cp m) @ (concat_1p (Cp m)))
           (C_rid : forall m : M,
                      ap Cp (mon_rid m) =
                      Cmul m (mon_id M) @ whiskerL (Cp m) (C_id Cmul) @ (concat_p1 (Cp m)))
           (m n : M) : 
  ap02 (B_rec C c0 Cp Cmul C_assoc C_lid C_rid) (B_resp_mul m n) =
  (B_rec_beta_Cp C c0 Cp Cmul C_assoc C_lid C_rid (m + n))
    @ Cmul m n @
    ((B_rec_beta_Cp C c0 Cp Cmul C_assoc C_lid C_rid m)^ @@
     (B_rec_beta_Cp C c0 Cp Cmul C_assoc C_lid C_rid n)^) @ (ap_pp _ _ _)^.
Admitted.




           ap02
    section_to_depfun
