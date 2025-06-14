(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import BinInt Integral_domain ENsatzTactic.
Export (ltac.notations) ENsatzTactic.

#[export] Existing Instance Zr.

#[export] Instance Zcri : Cring (Rr:=Zr).
Proof. exact Z.mul_comm. Qed.

#[export] Instance Zdi : Integral_domain (Rcr:=Zcri).
Proof. split; [ exact Zmult_integral | discriminate ]. Qed.
