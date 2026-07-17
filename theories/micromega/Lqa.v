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

From Stdlib Require Import QMicromega.
From Stdlib Require Import QArith_base.
From Stdlib Require Import RingMicromega.
From Stdlib Require Import VarMap.
From Stdlib Require Import DeclConstant.
From Stdlib.micromega Require Tauto.
From micromega_plugin Require Export tactics.

Ltac rchange :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff ;
  change (Tauto.eval_bf (Qeval_formula (@find Q 0%Q __varmap)) __ff) ;
  apply (QTautoChecker_sound __ff __wit).

Ltac rchecker_no_abstract := rchange ; vm_compute ; reflexivity.
Ltac rchecker_abstract := rchange ; vm_cast_no_check (eq_refl true).

Ltac rchecker := rchecker_no_abstract.

(** Here, lra stands for linear rational arithmetic *)
Ltac lra := mp_lra_Q rchecker.

(** Here, nra stands for non-linear rational arithmetic *)
Ltac nra := mp_nra_Q rchecker.

Ltac xpsatz dom d :=
  let tac := lazymatch dom with
  | Q =>
    ((mp_sos_Q rchecker) || (mp_psatz_Q d rchecker))
  | _ => fail "Unsupported domain"
  end in tac.

Tactic Notation "psatz" constr(dom) int_or_var(n) := xpsatz dom n.
Tactic Notation "psatz" constr(dom) := xpsatz dom ltac:(-1).

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
