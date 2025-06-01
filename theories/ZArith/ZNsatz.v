From Stdlib Require Import BinInt Lia NsatzTactic.
Export (ltac.notations) NsatzTactic.

(** Make use of [lia] in [nsatz] *)
Ltac nsatz_internal_lia ::= lia.

#[export] Existing Instance Zr.

#[export] Instance Zcri : Cring (Rr:=Zr).
Proof. exact Z.mul_comm. Qed.

#[export] Instance Zdi : Integral_domain (Rcr:=Zcri).
Proof. split; [ exact Zmult_integral | discriminate ]. Qed.
