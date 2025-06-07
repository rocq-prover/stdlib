From Stdlib.nsatz Require Import NsatzTactic.
Export (ltac.notations) NsatzTactic.

From Stdlib.QArith Require Import QArith_base.

#[export] Instance Qops: @Ring_ops Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq := {}.

#[export]
Instance Qri : Ring (Ro:=Qops).
Proof.
  split.
  - apply Q_Setoid.
  - apply Qplus_comp.
  - apply Qmult_comp.
  - apply Qminus_comp.
  - apply Qopp_comp.
  - exact Qplus_0_l.
  - exact Qplus_comm.
  - apply Qplus_assoc.
  - exact Qmult_1_l.
  - exact Qmult_1_r.
  - apply Qmult_assoc.
  - apply Qmult_plus_distr_l.
  - intros. apply Qmult_plus_distr_r.
  - reflexivity.
  - exact Qplus_opp_r.
Defined.

#[export] Instance Qcri: Cring (Rr:=Qri).
Proof. exact Qmult_comm. Defined.

#[export] Instance Qdi : Integral_domain (Rcr:=Qcri).
Proof. split; [ exact Qmult_integral | exact Q_apart_0_1 ]. Qed.
