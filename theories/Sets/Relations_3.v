(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

From Stdlib Require Export Relations_1.
From Stdlib Require Export Relations_2.

Section Relations_3.
   Variable U : Type.
   Variable R : Relation U.

   Definition coherent (x y:U) : Prop :=
      exists z : _, Rstar U R x z /\ Rstar U R y z.

   Definition locally_confluent (x:U) : Prop :=
     forall y z:U, R x y -> R x z -> coherent y z.

   Definition Locally_confluent : Prop := forall x:U, locally_confluent x.

   Definition confluent (x:U) : Prop :=
     forall y z:U, Rstar U R x y -> Rstar U R x z -> coherent y z.

   Definition Confluent : Prop := forall x:U, confluent x.

   Inductive noetherian (x: U) : Prop :=
       definition_of_noetherian :
         (forall y:U, R x y -> noetherian y) -> noetherian x.

   Definition Noetherian : Prop := forall x:U, noetherian x.

End Relations_3.
#[global]
Hint Unfold coherent: sets.
#[global]
Hint Unfold locally_confluent: sets.
#[global]
Hint Unfold confluent: sets.
#[global]
Hint Unfold Confluent: sets.
#[global]
Hint Resolve definition_of_noetherian: sets.
#[global]
Hint Unfold Noetherian: sets.
