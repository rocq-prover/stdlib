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

(**
* Some properties of the addition for modules implementing [NZBasicFunsSig']

This file defines the [NZAddProp] functor type. This functor type is meant
to be [Include]d in a module implementing [NZBasicFunsSig'].

This gives the following lemmas:
- [add_0_r], [add_1_l], [add_1_r]
- [add_succ_r], [add_succ_comm], [add_comm]
- [add_assoc]
- [add_cancel_l], [add_cancel_r]
- [add_shuffle0],  [add_shuffle3] to rearrange sums of 3 elements
- [add_shuffle1],  [add_shuffle2] to rearrange sums of 4 elements
- [sub_1_r]
*)
From Stdlib.Numbers.NatInt Require Import NZAxioms NZBase.

Module Type NZAddProp (Import NZ : NZBasicFunsSig')(Import NZBase : NZBaseProp NZ).

#[global] Hint Rewrite
 pred_succ add_0_l add_succ_l mul_0_l mul_succ_l sub_0_r sub_succ_r : nz.
#[global] Hint Rewrite one_succ two_succ : nz'.
Ltac nzsimpl := autorewrite with nz.
Ltac nzsimpl' := autorewrite with nz nz'.

Theorem add_0_r : forall n, n + 0 == n.
Proof.
  intro n; nzinduct n.
  - now nzsimpl.
  - intro. nzsimpl. now rewrite succ_inj_wd.
Qed.

Theorem add_succ_r : forall n m, n + S m == S (n + m).
Proof.
  intros n m; nzinduct n.
  - now nzsimpl.
  - intro. nzsimpl. now rewrite succ_inj_wd.
Qed.

Theorem add_succ_comm : forall n m, S n + m == n + S m.
Proof.
intros n m. now rewrite add_succ_r, add_succ_l.
Qed.

#[global] Hint Rewrite add_0_r add_succ_r : nz.

Theorem add_comm : forall n m, n + m == m + n.
Proof.
  intros n m; nzinduct n.
  - now nzsimpl.
  - intro. nzsimpl. now rewrite succ_inj_wd.
Qed.

Theorem add_1_l : forall n, 1 + n == S n.
Proof.
intro n; now nzsimpl'.
Qed.

Theorem add_1_r : forall n, n + 1 == S n.
Proof.
intro n; now nzsimpl'.
Qed.

#[global] Hint Rewrite add_1_l add_1_r : nz.

Theorem add_assoc : forall n m p, n + (m + p) == (n + m) + p.
Proof.
  intros n m p; nzinduct n.
  - now nzsimpl.
  - intro. nzsimpl. now rewrite succ_inj_wd.
Qed.

Theorem add_cancel_l : forall n m p, p + n == p + m <-> n == m.
Proof.
intros n m p; nzinduct p.
- now nzsimpl.
- intro p. nzsimpl. now rewrite succ_inj_wd.
Qed.

Theorem add_cancel_r : forall n m p, n + p == m + p <-> n == m.
Proof.
intros n m p. rewrite (add_comm n p), (add_comm m p). apply add_cancel_l.
Qed.

Theorem add_shuffle0 : forall n m p, n+m+p == n+p+m.
Proof.
intros n m p. rewrite <- 2 add_assoc, add_cancel_l. apply add_comm.
Qed.

Theorem add_shuffle1 : forall n m p q, (n + m) + (p + q) == (n + p) + (m + q).
Proof.
intros n m p q. rewrite 2 add_assoc, add_cancel_r. apply add_shuffle0.
Qed.

Theorem add_shuffle2 : forall n m p q, (n + m) + (p + q) == (n + q) + (m + p).
Proof.
intros n m p q. rewrite (add_comm p). apply add_shuffle1.
Qed.

Theorem add_shuffle3 : forall n m p, n + (m + p) == m + (n + p).
Proof.
intros n m p. now rewrite add_comm, <- add_assoc, (add_comm p).
Qed.

Theorem sub_1_r : forall n, n - 1 == P n.
Proof.
intro n; now nzsimpl'.
Qed.

#[global] Hint Rewrite sub_1_r : nz.

End NZAddProp.
