(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria)      2016                             *)
(*                                                                      *)
(************************************************************************)

From Stdlib Require Import RMicromega.
From Stdlib Require Import QMicromega.
From Stdlib Require Import Rdefinitions.
From Stdlib Require Import RingMicromega.
From Stdlib Require Import VarMap.
From Stdlib.micromega Require Tauto.
From Stdlib Require Import Rregisternames.
From Stdlib Require Import Tify.
(* With the exception of [Zfloor] and [sqrt],
   importing Rify by default would be feasible but is unwise.
   The goal may blow up because [Rmin], [Rmax] and [Rabs]
   generate case splits.
   (* From Stdlib Require Import Rify. *)
   If Rify is imported, [lra] and [nra] are using [tify R].
   We provide [simple lra] and [simple nra] which do not call [tify R].
 *)

Declare ML Module "rocq-runtime.plugins.micromega".

Ltac rchange :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff ;
  change (Tauto.eval_bf (eReval_formula (@find R 0%R __varmap)) __ff) ;
  apply (RTautoChecker_sound __ff __wit).

Ltac rchecker_no_abstract := rchange ; vm_compute ; reflexivity.
Ltac rchecker_abstract := rchange ; vm_cast_no_check (eq_refl true).

Ltac rchecker := rchecker_no_abstract.

(** Here, lra stands for linear real arithmetic *)
Ltac lra := unfold Rdiv in *; tify R ; xlra_R rchecker.

(** Here, nra stands for non-linear real arithmetic *)
Ltac nra := unfold Rdiv in *;tify R ; xnra_R rchecker.

Tactic Notation "simple" "nra" := unfold Rdiv in *; xnra_R rchecker.

Tactic Notation "simple" "lra" := unfold Rdiv in *; xlra_R rchecker.

Ltac xpsatz dom d :=
  let tac := lazymatch dom with
  | R =>
    (xsos_R rchecker) || (xpsatz_R d rchecker)
  | _ => fail "Unsupported domain"
 end in tac.

Tactic Notation "psatz" constr(dom) int_or_var(n) := xpsatz dom n.
Tactic Notation "psatz" constr(dom) := xpsatz dom ltac:(-1).

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
