(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Export Cring.
From Stdlib Require Export Integral_domain.
From Stdlib Require Export Ncring_initial.

#[global]
Instance Zcri: (Cring (Rr:=Zr)).
Proof.
red. exact Z.mul_comm. Defined.

Lemma Z_one_zero: 1%Z <> 0%Z.
Proof. discriminate. Qed.

#[global]
Instance Zdi : (Integral_domain (Rcr:=Zcri)).
Proof.
constructor.
- exact Zmult_integral.
- exact Z_one_zero.
Defined.
