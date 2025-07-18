(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Decidable setoid equality theory.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A B .

(** Export notations. *)

From Stdlib.Classes Require Export SetoidClass.

(** The [DecidableSetoid] class asserts decidability of a [Setoid].
   It can be useful in proofs to reason more classically. *)

From Stdlib.Logic Require Import Decidable.

Class DecidableSetoid `(S : Setoid A) :=
  setoid_decidable : forall x y : A, decidable (x == y).

(** The [EqDec] class gives a decision procedure for a particular setoid
   equality. *)

Class EqDec `(S : Setoid A) :=
  equiv_dec : forall x y : A, { x == y } + { x =/= y }.

(** We define the [==] overloaded notation for deciding equality. It does not
   take precedence of [==] defined in the type scope, hence we can have both
   at the same time. *)

Notation " x == y " := (equiv_dec x y) (no associativity, at level 70).

Definition swap_sumbool {A B} (x : { A } + { B }) : { B } + { A } :=
  match x with
    | left H => @right _ _ H
    | right H => @left _ _ H
  end.

From Stdlib.Program Require Import Program.

#[local] Open Scope program_scope.

(** Invert the branches. *)

Program Definition nequiv_dec `{EqDec A} (x y : A) : { x =/= y } + { x == y } := swap_sumbool (x == y).

(** Overloaded notation for inequality. *)

Infix "=/=" := nequiv_dec (no associativity, at level 70).

(** Define boolean versions, losing the logical information. *)

Definition equiv_decb `{EqDec A} (x y : A) : bool :=
  if x == y then true else false.

Definition nequiv_decb `{EqDec A} (x y : A) : bool :=
  negb (equiv_decb x y).

Infix "==b" := equiv_decb (no associativity, at level 70).
Infix "<>b" := nequiv_decb (no associativity, at level 70).

(** Decidable leibniz equality instances. *)

From Stdlib.Arith Require Import Arith_base.

(** The equiv is buried inside the setoid, but we can recover
  it by specifying which setoid we're talking about. *)

#[global]
Program Instance eq_setoid A : Setoid A | 10 :=
  { equiv := eq ; setoid_equiv := eq_equivalence }.

#[global]
Program Instance nat_eq_eqdec : EqDec (eq_setoid nat) :=
  eq_nat_dec.

From Stdlib.Bool Require Import Bool.

#[global]
Program Instance bool_eqdec : EqDec (eq_setoid bool) :=
  bool_dec.

#[global]
Program Instance unit_eqdec : EqDec (eq_setoid unit) :=
  fun x y => in_left.

  Next Obligation.
  Proof.
    do 2 match goal with x : () |- _ => destruct x end.
    reflexivity.
  Qed.

#[global]
Program Instance prod_eqdec `(! EqDec (eq_setoid A), ! EqDec (eq_setoid B))
 : EqDec (eq_setoid (prod A B)) :=
  fun x y =>
    let '(x1, x2) := x in
    let '(y1, y2) := y in
    if x1 == y1 then
      if x2 == y2 then in_left
      else in_right
    else in_right.

  Solve Obligations with unfold complement ; program_simpl.

(** Objects of function spaces with countable domains like bool
  have decidable equality. *)

#[global]
Program Instance bool_function_eqdec `(! EqDec (eq_setoid A))
 : EqDec (eq_setoid (bool -> A)) :=
  fun f g =>
    if f true == g true then
      if f false == g false then in_left
      else in_right
    else in_right.

  Solve Obligations with try red ; unfold complement ; program_simpl.

  Next Obligation.
  Proof.
    extensionality x.
    destruct x ; auto.
  Qed.
