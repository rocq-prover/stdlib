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
(*  Frédéric Besson (Irisa/Inria) 2006-2016                             *)
(*                                                                      *)
(************************************************************************)

From Stdlib Require Import ZMicromega.
From Stdlib Require Import QMicromega.
From Stdlib Require Import RMicromega.
From Stdlib Require Import QArith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Rdefinitions.
From Stdlib Require Import RingMicromega.
From Stdlib Require Import VarMap.
From Stdlib.micromega Require Tauto.
From Stdlib Require Lia.
From Stdlib Require Lra.
From Stdlib Require Lqa.
From Stdlib Require Export micromega_tactics.

Ltac lia := Lia.lia.

Ltac nia := Lia.nia.

Ltac xpsatz dom d :=
  let tac := lazymatch dom with
  | Z => (xsos_Z Lia.zchecker) || (xpsatz_Z d Lia.zchecker)
  | R => (xsos_R Lra.rchecker) || (xpsatz_R d Lra.rchecker)
  | Q => (xsos_Q Lqa.rchecker) || (xpsatz_Q d Lqa.rchecker)
  | _ => fail "Unsupported domain"
  end in tac.

Tactic Notation "psatz" constr(dom) int_or_var(n) := xpsatz dom n.
Tactic Notation "psatz" constr(dom) := xpsatz dom ltac:(-1).

Ltac psatzl dom :=
  let tac := lazymatch dom with
  | Z => Lia.lia
  | Q => Lqa.lra
  | R => Lra.lra
  | _ => fail "Unsupported domain"
  end in tac.

Ltac lra :=
  first [ psatzl R | psatzl Q ].

Ltac nra :=
  first [ Lra.nra | Lqa.nra ].

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
