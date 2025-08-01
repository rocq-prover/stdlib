(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Decidable equivalences.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

(** Export notations. *)

From Stdlib.Classes Require Export Equivalence.

(** The [DecidableSetoid] class asserts decidability of a [Setoid].
   It can be useful in proofs to reason more classically. *)

From Stdlib.Logic Require Import Decidable.
From Stdlib.Bool Require Import Bool.
From Stdlib.Arith Require Import Peano_dec.
From Stdlib.Program Require Import Program.

Generalizable Variables A B R.

Open Scope equiv_scope.

Class DecidableEquivalence `(equiv : Equivalence A) :=
  setoid_decidable : forall x y : A, decidable (x === y).

(** The [EqDec] class gives a decision procedure for a particular
   setoid equality. *)

Class EqDec A R {equiv : Equivalence R} :=
  equiv_dec : forall x y : A, { x === y } + { x =/= y }.

(** We define the [==] overloaded notation for deciding equality. It does not
   take precedence of [==] defined in the type scope, hence we can have both
   at the same time. *)

Notation " x == y " := (equiv_dec x y) (no associativity, at level 70) : equiv_scope.

Definition swap_sumbool {A B} (x : { A } + { B }) : { B } + { A } :=
  match x with
    | left H => @right _ _ H
    | right H => @left _ _ H
  end.

#[local] Open Scope program_scope.

(** Invert the branches. *)

Program Definition nequiv_dec `{EqDec A} (x y : A) : { x =/= y } + { x === y } :=
          swap_sumbool (x == y).


(** Overloaded notation for inequality. *)

Infix "<>" := nequiv_dec (no associativity, at level 70) : equiv_scope.

(** Define boolean versions, losing the logical information. *)

Definition equiv_decb `{EqDec A} (x y : A) : bool :=
  if x == y then true else false.

Definition nequiv_decb `{EqDec A} (x y : A) : bool :=
  negb (equiv_decb x y).

Infix "==b" := equiv_decb (no associativity, at level 70).
Infix "<>b" := nequiv_decb (no associativity, at level 70).

(** Decidable leibniz equality instances. *)

(** The equiv is buried inside the setoid, but we can recover it by specifying
   which setoid we're talking about. *)

#[global]
Program Instance nat_eq_eqdec : EqDec nat eq := eq_nat_dec.

#[global]
Program Instance bool_eqdec : EqDec bool eq := bool_dec.

#[global]
Program Instance unit_eqdec : EqDec unit eq := fun x y => in_left.

  Next Obligation.
  Proof.
    do 2 match goal with [ x : () |- _ ] => destruct x end.
    reflexivity.
  Qed.

#[global] Obligation Tactic := unfold complement, equiv ; program_simpl.
#[export] Obligation Tactic := unfold complement, equiv ; program_simpl.

#[global]
Program Instance prod_eqdec `(EqDec A eq, EqDec B eq) :
  EqDec (prod A B) eq :=
  { equiv_dec x y :=
    let '(x1, x2) := x in
    let '(y1, y2) := y in
    if x1 == y1 then
      if x2 == y2 then in_left
      else in_right
    else in_right }.

#[global]
Program Instance sum_eqdec `(EqDec A eq, EqDec B eq) :
  EqDec (sum A B) eq := {
  equiv_dec x y :=
    match x, y with
      | inl a, inl b => if a == b then in_left else in_right
      | inr a, inr b => if a == b then in_left else in_right
      | inl _, inr _ | inr _, inl _ => in_right
    end }.

(** Objects of function spaces with countable domains like bool have decidable
  equality. Proving the reflection requires functional extensionality though. *)

#[global]
Program Instance bool_function_eqdec `(EqDec A eq) : EqDec (bool -> A) eq :=
  { equiv_dec f g :=
    if f true == g true then
      if f false == g false then in_left
      else in_right
    else in_right }.

  Next Obligation.
  Proof.
    extensionality x.
    destruct x ; auto.
  Qed.

From Stdlib Require Import List.

#[global]
Program Instance list_eqdec `(eqa : EqDec A eq) : EqDec (list A) eq :=
  { equiv_dec :=
    fix aux (x y : list A) :=
    match x, y with
      | nil, nil => in_left
      | cons hd tl, cons hd' tl' =>
        if hd == hd' then
          if aux tl tl' then in_left else in_right
          else in_right
      | _, _ => in_right
    end }.

  Next Obligation.
    match goal with y : list _ |- _ => destruct y end ;
    unfold not in *; eauto.
  Defined.

  Solve Obligations with unfold equiv, complement in * ;
    program_simpl ; intuition (discriminate || eauto).

#[export]
Program Instance option_eqdec `(eqa : EqDec A eq) : EqDec (option A) eq :=
  { equiv_dec (x y : option A) :=
    match x, y with
      | None, None => in_left
      | Some s, Some s' =>
        if s == s' then in_left else in_right
      | _, _ => in_right
    end
  }.

  Next Obligation.
    match goal with y : option _ |- _ => destruct y end ;
    unfold not in *; eauto.
  Defined.

  Solve Obligations with unfold equiv, complement in * ;
    program_simpl; intuition (discriminate || eauto).
