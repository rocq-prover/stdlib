(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Instances of [ZifyClasses] for dealing with advanced [N] operators. *)

From Stdlib Require Import BinNat BinInt Znat.
From Stdlib.micromega Require Import ZifyClasses ZifyInst Zify SatDivMod.

Ltac zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(** Support for [N] *)

#[local]
Existing Instance Inj_N_Z.

#[global]
Instance Op_N_div : BinOp N.div :=
  {| TBOp := Z.div ; TBOpInj := N2Z.inj_div |}.
Add Zify BinOp Op_N_div.

#[global]
Instance Op_N_mod : BinOp N.modulo :=
  {| TBOp := Z.rem ; TBOpInj := N2Z.inj_rem |}.
Add Zify BinOp Op_N_mod.

#[global]
Instance Op_N_pow : BinOp N.pow :=
  {| TBOp := Z.pow ; TBOpInj := N2Z.inj_pow|}.
Add Zify BinOp Op_N_pow.

#[local]
Open Scope Z_scope.

#[local]
Lemma Z_div_nonneg_nonneg a b : 0 <= a -> 0 <= b -> 0 <= a / b.
Proof.
  intros H; pose proof Z.div_pos a b H.
  case (Z.ltb_spec 0 b); auto.
  intros A B; rewrite (Z.le_antisymm _ _ A B).
  case a; cbv; congruence.
Qed.

#[local]
Lemma Z_mod_nonneg_nonneg a b : 0 <= a -> 0 <= b -> 0 <= a mod b.
Proof.
  case (Z.ltb_spec 0 b); intros.
  { apply Z.mod_pos_bound; trivial. }
  rewrite <-(Z.le_antisymm 0 b); trivial.
  case a in *; cbv in *; congruence.
Qed.

#[global]
Instance SatDiv : Saturate Z.div :=
  {|
    PArg1 := fun x => 0 <= x;
    PArg2 := fun y => 0 <= y;
    PRes  := fun _ _ r => 0 <= r;
    SatOk := Z_div_nonneg_nonneg
  |}.
Add Zify Saturate SatDiv.

#[global]
Instance SatMod : Saturate Z.modulo :=
  {|
    PArg1 := fun x => 0 <= x;
    PArg2 := fun y => 0 <= y;
    PRes  := fun _ _ r => 0 <= r;
    SatOk := Z_mod_nonneg_nonneg
  |}.
Add Zify Saturate SatMod.
