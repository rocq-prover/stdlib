(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


From Stdlib Require Import TifyClasses.
Declare ML Module "rocq-runtime.plugins.zify".


Ltac tify r := intros;
               tify_elim_let ;
               tify_op r;
               tify_iter_specs;
               tify_saturate.
