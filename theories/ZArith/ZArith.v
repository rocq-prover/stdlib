(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Library for manipulating integers based on binary encoding *)

From Stdlib Require Export BinNums.
From Stdlib Require Export BinPos.
From Stdlib Require Export BinNat.
From Stdlib Require Export BinInt.
From Stdlib Require Export Zcompare.
From Stdlib Require Export Zorder.
From Stdlib Require Export Zeven.
From Stdlib Require Export Zminmax.
From Stdlib Require Export Zmin.
From Stdlib Require Export Zmax.
From Stdlib Require Export Zabs.
From Stdlib Require Export Znat.
From Stdlib Require Export auxiliary.
From Stdlib Require Export ZArith_dec.
From Stdlib Require Export Zbool.
From Stdlib Require Export Zmisc.
From Stdlib Require Export Wf_Z.

#[global]
Hint Resolve Z.le_refl Z.add_comm Z.add_assoc Z.mul_comm Z.mul_assoc Z.add_0_l
  Z.add_0_r Z.mul_1_l Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_add_distr_l
  Z.mul_add_distr_r: zarith.

From Stdlib Require Export Zhints.

(** Extra definitions *)

From Stdlib Require Export Zpow_def.

(** Extra modules using [Ring]. *)

From Stdlib Require Export OmegaLemmas.
From Stdlib Require Export PreOmega.
From Stdlib Require Export ZArith_hints.
From Stdlib Require Export Zcomplements.
From Stdlib Require Export Zpower.
From Stdlib Require Export Zdiv.
From Stdlib Require Export Zdivisibility.
From Stdlib Require Export Zdiv_facts.
From Stdlib Require Export Zbitwise.
From Stdlib Require Export ZModOffset.

Export ZArithRing.
