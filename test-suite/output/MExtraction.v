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
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

(* Used to generate plugins/micromega/micromega.ml
   Don't forget to update it in Rocq core when editing this MExtraction.v file
   or MExtraction.out *)

From Stdlib Require Extraction.
From Stdlib Require Import ZMicromega.
From Stdlib Require Import QMicromega.
From Stdlib Require Import RMicromega.
From Stdlib Require Import VarMap.
From Stdlib Require Import RingMicromega.
From Stdlib Require Import NArith.
From Stdlib Require Import QArith.

Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive list => list [ "[]" "(::)" ].
Extract Inductive bool => bool [ true false ].
Extract Inductive sumbool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive sumor => option [ Some None ].
(** Then, in a ternary alternative { }+{ }+{ },
   -  leftmost choice (Inleft Left) is (Some true),
   -  middle choice (Inleft Right) is (Some false),
   -  rightmost choice (Inright) is (None) *)


(** To preserve its laziness, andb is normally expanded.
    Let's rather use the ocaml && *)
Extract Inlined Constant andb => "(&&)".

Import Reals.Rdefinitions.

Extract Constant R => "int".
Extract Constant R0 => "0".
Extract Constant R1 => "1".
Extract Constant Rplus => "( + )".
Extract Constant Rmult => "( * )".
Extract Constant Ropp  => "fun x -> - x".
Extract Constant Rinv   => "fun x -> 1 / x".

(** In order to avoid annoying build dependencies the actual
    extraction is only performed as a test in the test suite. *)
Recursive Extraction
           Tauto.mapX Tauto.foldA Tauto.collect_annot Tauto.ids_of_formula Tauto.map_bformula
           Tauto.abst_form
           ZMicromega.cnfZ  ZMicromega.Zeval_const QMicromega.cnfQ
           List.map simpl_cone (*map_cone  indexes*)
           denorm QArith_base.Qpower vm_add
   normZ normQ normQ Z.to_N N.of_nat ZTautoChecker ZWeakChecker QTautoChecker RTautoChecker find.

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
