(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Instances of [ZifyClasses] for dealing with advanced [nat] operators. *)

From Stdlib Require Import BinInt Znat.
From Stdlib.micromega Require Import ZifyClasses ZifyInst Zify SatDivMod.

Ltac zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(** Support for [nat] *)

#[local]
Existing Instance Inj_nat_Z.

#[global]
Instance Op_mod : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp Op_mod.

#[global]
Instance Op_div : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp Op_div.

#[global]
Instance Op_pow : BinOp Nat.pow :=
  {| TBOp := Z.pow ; TBOpInj := Nat2Z.inj_pow |}.
Add Zify BinOp Op_pow.
