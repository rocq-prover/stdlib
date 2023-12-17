(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This module gathers the necessary base to build an instance of the
   ring tactic. Abstract rings need more theory, depending on
   ZArith_base. *)

Declare ML Module "ring_plugin:coq-core.plugins.ring".
From Stdlib Require Export Ring_theory.
From Stdlib Require Export Ring_tac.
From Stdlib Require Import InitialRing.
