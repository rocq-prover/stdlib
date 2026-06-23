(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Author: Bruno Barras *)

From Stdlib Require Import Relation_Definitions Relation_Operators.

Section WfInclusion.
  Variable A : Type.
  Variables R1 R2 : A -> A -> Prop.

  Lemma Acc_partial_incl : forall z : A,
      (forall x y, clos_refl_trans _ R1 y z -> R1 x y -> R2 x y) ->
      Acc R2 z -> Acc R1 z.
  Proof.
    intros z H.
    induction 1 as [z Hz IH].
    apply Acc_intro.
    intros y Hy.
    apply IH.
    - apply H,Hy.
      auto with sets.
    - intros x z' Hz' HR.
      apply H, HR.
      apply rt_trans with y;auto with sets.
  Qed.

  Lemma Acc_incl : inclusion A R1 R2 -> forall z:A, Acc R2 z -> Acc R1 z.
  Proof.
    induction 2.
    apply Acc_intro; auto.
  Qed.

  #[local]
  Hint Resolve Acc_incl : core.

  Theorem wf_incl : inclusion A R1 R2 -> well_founded R2 -> well_founded R1.
  Proof.
    unfold well_founded; auto.
  Qed.

End WfInclusion.
