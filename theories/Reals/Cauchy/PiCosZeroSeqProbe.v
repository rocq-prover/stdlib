(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The consumption-side certificate of the cosine zero sequence

    Mission.  The consumption-side certificate for the cosine zero
    sequence [cos_zero_seq]: with the half-power step
    [eps_n = (1/2)^(n+1)] as the tolerance, the n-th zero is taken
    from the [sig] witness of the main existence theorem for the
    zeros of the cosine ([PiCosApproxRoot.approx_root_cos]).  The
    definition face is verbatim the same shape as the [Q]-level form
    of [cos_zero_seq] at [S10_KVQuantTrig.v:L8119] ([proj1_sig] taken
    directly).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs];
    [QCauchyZeroCos] ([log_eps]/[log_eps_pos]);
    [PiCosApproxRoot] ([approx_root_cos]).

    References.  [S10_KVQuantTrig.v:L8119] (the [Q]-level form of
    [cos_zero_seq]).

    Constructivity.  Statements carried at the [Set] level (with
    [Q] as the carrier); assumption-free and fully proved, with no
    non-constructive principles.

    Build.  [coqc -native-compiler no -q -Q . "" PiCosZeroSeqProbe.v]
    (Rocq 9.1.0).

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
Require Import QCauchyZeroCos.
Require Import PiCosApproxRoot.

(** The n-th term of the zero sequence: the localization point with
    tolerance [eps_n] (taken directly from the [sig] witness). *)
Definition cos_zero_seq (n : nat) : Q :=
  proj1_sig (approx_root_cos (log_eps n) (log_eps_pos n)).

Print Assumptions cos_zero_seq.
