(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Library for binary natural numbers *)

From Stdlib Require Export BinNums.
From Stdlib Require Export BinPos.
From Stdlib Require Export BinNat.
From Stdlib Require Export Nnat.
From Stdlib Require Export Ndiv_def.
From Stdlib Require Export Nsqrt_def.
From Stdlib Require Export Ngcd_def.

(** [N] contains an [order] tactic for natural numbers *)

(** Note that [N.order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

#[local] Open Scope N_scope.

Section TestOrder.
 Let test : forall x y, x<=y -> y<=x -> x=y.
 Proof.
 N.order.
 Defined.
End TestOrder.
