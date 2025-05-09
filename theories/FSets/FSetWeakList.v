(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Finite sets library *)

(** This file proposes an implementation of the non-dependent
    interface [FSetInterface.WS] using lists without redundancy. *)

From Stdlib Require Import FSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.

(** This is just a compatibility layer, the real implementation
    is now in [MSetWeakList] *)

From Stdlib Require Equalities FSetCompat MSetWeakList.

Module Make (X: DecidableType) <: WS with Module E := X.
 Module E := X.
 Module X' := Equalities.Update_DT X.
 Module MSet := MSetWeakList.Make X'.
 Include FSetCompat.Backport_WSets X MSet.
End Make.
