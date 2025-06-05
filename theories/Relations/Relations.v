(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
From Stdlib Require Export Relation_Definitions.
From Stdlib Require Export Relation_Operators.
From Stdlib Require Export Operators_Properties.
From Stdlib Require Export RelationClasses.

Lemma Equivalence_on [A B] (f:A -> B) (r:relation B) :
    Equivalence r -> Equivalence (fun x y => r (f x) (f y)).
Proof. intros []; split; red; eauto. Qed.

Lemma Equivalence_eq_on [A B] (f:A -> B) : Equivalence (fun x y => f x = f y).
Proof. apply Equivalence_on; exact _. Qed.

#[deprecated(since="9.1", use=Equivalence_on)]
#[warning="-deprecated"]
Lemma inverse_image_of_equivalence :
  forall (A B:Type) (f:A -> B) (r:relation B),
    equivalence B r -> equivalence A (fun x y:A => r (f x) (f y)).
Proof.
  intros A B f r H; split; elim H; red; auto.
  intros _ equiv_trans _ x y z H0 H1; apply equiv_trans with (f y); assumption.
Qed.

#[deprecated(since="9.1", use=Equivalence_eq_on)]
#[warning="-deprecated"]
Lemma inverse_image_of_eq :
  forall (A B:Type) (f:A -> B), equivalence A (fun x y:A => f x = f y).
Proof.
  intros A B f; split; red;
    [  (* reflexivity *) reflexivity
      |  (* transitivity *) intros x y z; transitivity (f y); assumption
      |  (* symmetry *) intros; symmetry ; assumption ].
Qed.
