(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

From Stdlib Require Export Decidable.
From Stdlib Require Export ZAxioms.
From Stdlib Require Import NZMulOrder.

Module ZBaseProp (Import Z : ZAxiomsMiniSig').
Include NZMulOrderProp Z.

Lemma Private_succ_pred n : n ~= 0 -> S (P n) == n.
Proof. intros _; exact (succ_pred _). Qed.

Lemma le_pred_l n : P n <= n.
Proof. rewrite <-(succ_pred n), pred_succ; exact (le_succ_diag_r _). Qed.

Include NZAddOrder.NatIntAddOrderProp Z.

(* Theorems that are true for integers but not for natural numbers *)

Theorem pred_inj : forall n m, P n == P m -> n == m.
Proof.
intros n m H. apply succ_wd in H. now rewrite 2 succ_pred in H.
Qed.

Theorem pred_inj_wd : forall n1 n2, P n1 == P n2 <-> n1 == n2.
Proof.
intros n1 n2; split; [apply pred_inj | intros; now f_equiv].
Qed.

Lemma succ_m1 : S (-1) == 0.
Proof.
 now rewrite one_succ, opp_succ, opp_0, succ_pred.
Qed.

End ZBaseProp.

