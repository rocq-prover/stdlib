From Stdlib Require Import BinInt Lia NsatzTactic.

(** Make use of [lia] in [nsatz] *)
Ltac nsatz_internal_lia ::= lia.

Lemma Z_one_zero: 1%Z <> 0%Z.
Proof. lia. Qed.

#[global]
Instance Zcri : Cring (Rr:=Zr).
Proof. exact Z.mul_comm. Qed.

#[global]
Instance Zdi : Integral_domain (Rcr:=Zcri).
Proof.
  split.
  - exact Zmult_integral.
  - exact Z_one_zero.
Qed.
