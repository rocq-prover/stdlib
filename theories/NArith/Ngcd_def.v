(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import BinPos BinNat.
#[local] Open Scope N_scope.

(** Obsolete file, see [BinNat] now,
    only compatibility notations remain here. *)

Abbreviation Ndivide := N.divide (only parsing).
Abbreviation Ngcd := N.gcd (only parsing).
Abbreviation Nggcd := N.ggcd (only parsing).
Abbreviation Nggcd_gcd := N.ggcd_gcd (only parsing).
Abbreviation Nggcd_correct_divisors := N.ggcd_correct_divisors (only parsing).
Abbreviation Ngcd_divide_l := N.gcd_divide_l (only parsing).
Abbreviation Ngcd_divide_r := N.gcd_divide_r (only parsing).
Abbreviation Ngcd_greatest := N.gcd_greatest (only parsing).
