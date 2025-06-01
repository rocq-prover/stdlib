(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import NsatzTactic.
Export (ltac.notations) NsatzTactic.

From Stdlib Require Import Raxioms RIneq DiscrR.

Ltac nsatz_internal_discrR ::= discrR.

Local Ltac extra_reify :=
  lazymatch goal with |- Ncring_tac.extra_reify _ (IZR ?z) =>
    lazymatch isZcst z with
    | true => exact (PEc z)
    end
  end.
#[export] Hint Extern 1 (Ncring_tac.extra_reify _ _) => extra_reify : typeclass_instances.

#[export] Instance Rops: @Ring_ops R 0%R 1%R Rplus Rmult Rminus Ropp (@eq R) := {}.

#[export] Instance Rri : Ring (Ro:=Rops).
Proof.
  split.
  { exact _. }
  1,2,3,4: Morphisms.solve_proper.
  - exact Rplus_0_l.
  - exact Rplus_comm.
  - symmetry. apply Rplus_assoc.
  - exact Rmult_1_l.
  - exact Rmult_1_r.
  - symmetry. apply Rmult_assoc.
  - exact Rmult_plus_distr_r.
  - intros; apply Rmult_plus_distr_l.
  - exact Rminus_def.
  - exact Rplus_opp_r.
Qed.

#[export] Instance Rcri: (Cring (Rr:=Rri)).
Proof. exact Rmult_comm. Qed.

#[export] Instance Rdi : (Integral_domain (Rcr:=Rcri)).
Proof. split; [ exact Rmult_integral | exact R1_neq_R0 ]. Qed.
