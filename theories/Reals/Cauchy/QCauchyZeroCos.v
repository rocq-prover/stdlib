(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The logarithmic step-size machine for the Cauchy slice of the
    cosine zero sequence

    Mission.  The [Q]-level supply file for the Cauchy slice of the
    cosine zero sequence.  The first section loads the logarithmic
    step-size machine (the [log_eps] machine): the half-power step
    [eps_n = (1/2)^(n+1)] serves as the error scale of the zero
    approximation, with a kit of six companion results -- the
    monotonicity of the half powers (non-increase and strict
    decrease), the monotonicity for large [m], the positivity, and
    the reachability of [eps_m < delta].  This machine supplies the
    Cauchy rate of the zero sequence (whose roots are taken step by
    step with tolerance [eps_n]): the distance between neighboring
    zeros is controlled by the sum of the step sizes.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [QArith.Qfield], [ZArith.ZArith], [Arith.PeanoNat], [Setoid],
    [Morphisms], [Lia]; [PiKernelSlack]
    ([q_pow]/[qeq_le]/[q_pow_nonneg]).

    References.  [S07_RealSetoidExpLog.v], [q_pow_half_le@4190],
    [q_pow_half_lt_self@4203], [log_eps@5082], [log_eps_pos@5084],
    [q_pow_half_mono@5095], [log_eps_lt_delta@5105] (the statement
    faces and the proofs are taken over verbatim).

    Constructivity.  All statements live on the stdlib [Qlt]/[Qle]
    order predicates (an auxiliary face, consumed by the Cauchy main
    file of the sequence); assumption-free and fully proved, with no
    non-constructive principles; [lia] only for [nat] bookkeeping
    steps.  The three numerical witnesses are [vm_compute] checks,
    cross-checked against independent exact-arithmetic recomputation.

    Build.  [coqc -native-compiler no -q -Q . "" QCauchyZeroCos.v]
    (Rocq 9.1.0).

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.

(* ============================================================ *)
(* Section 1. The logarithmic step-size machine ([eps_n])       *)
(* ============================================================ *)

(** [eps_n := (1/2)^(S n)] (tends to [0]). *)
Definition log_eps (n : nat) : Q := q_pow (1 / 2) (Datatypes.S n).

(** The powers of [1/2] are non-increasing. *)
Lemma q_pow_half_le : forall n : nat, Qle (q_pow (1 / 2) (Datatypes.S n)) (q_pow (1 / 2) n).
Proof.
  intros n.
  apply (Qle_trans _ ((1 / 2) * q_pow (1 / 2) n) _).
  - apply qeq_le. reflexivity.
  - apply (Qle_trans _ (1 * q_pow (1 / 2) n) _).
    + apply (Qmult_le_compat_r (1 / 2) 1 (q_pow (1 / 2) n)).
      * change (Qle (1 / 2) 1). unfold Qle, Qdiv. simpl. lia.
      * apply (q_pow_nonneg (1 / 2) n). change (Qle 0 (1 / 2)). unfold Qle, Qdiv. simpl. lia.
    + apply qeq_le. ring.
Qed.

(** Strict decrease: [(1/2)^(S n) < (1/2)^n]. *)
Lemma q_pow_half_lt_self : forall n : nat, Qlt (q_pow (1 / 2) (Datatypes.S n)) (q_pow (1 / 2) n).
Proof.
  intros n.
  induction n as [| m IH]; simpl.
  - change (Qlt (1 / 2) 1). unfold Qdiv. simpl. reflexivity.
  - apply (Qle_lt_trans ((1 / 2) * ((1 / 2) * q_pow (1 / 2) m))
                        (((1 / 2) * q_pow (1 / 2) m) * (1 / 2))
                        ((1 / 2) * q_pow (1 / 2) m)).
    + apply qeq_le. ring.
    + apply (Qlt_le_trans _ ((q_pow (1 / 2) m) * (1 / 2)) _).
      * apply (Qmult_lt_compat_r ((1 / 2) * q_pow (1 / 2) m) (q_pow (1 / 2) m) (1 / 2)).
        -- change (Qlt 0 (1 / 2)). unfold Qdiv. simpl. reflexivity.
        -- apply IH.
      * apply qeq_le. ring.
Qed.

(** [eps_n] is strictly positive. *)
Lemma log_eps_pos : forall n : nat, Qlt 0 (log_eps n).
Proof.
  intros n. unfold log_eps.
  induction n as [| m IH]; simpl.
  - change (Qlt 0 (1 / 2)). unfold Qdiv. simpl. reflexivity.
  - apply (Qmult_lt_0_compat (1 / 2) (q_pow (1 / 2) (Datatypes.S m))).
    + change (Qlt 0 (1 / 2)). unfold Qdiv. simpl. reflexivity.
    + exact IH.
Qed.

(** [q_pow (1/2)] is antitone: [m <= n] implies [(1/2)^n <= (1/2)^m]. *)
Lemma q_pow_half_mono : forall m n : nat, (m <= n)%nat -> Qle (q_pow (1 / 2) n) (q_pow (1 / 2) m).
Proof.
  intros m n Hmn.
  induction Hmn as [ | n' Hrec IH ]; [apply Qle_refl | ].
  apply (Qle_trans _ (q_pow (1 / 2) n') _).
  - apply q_pow_half_le.
  - exact IH.
Qed.

(** [eps_m < delta]: if [m >= S t] and [(1/2)^t < delta], then
    [eps_m < delta]. *)
Lemma log_eps_lt_delta : forall (delta : Q) (t m : nat),
  Qlt (1 * q_pow (1 / 2) t) delta ->
  (Datatypes.S t <= m)%nat ->
  Qlt (log_eps m) delta.
Proof.
  intros delta t m Ht Hm.
  unfold log_eps.
  apply (Qle_lt_trans (q_pow (1 / 2) (Datatypes.S m)) (q_pow (1 / 2) (Datatypes.S t))
                      delta).
  - apply (q_pow_half_mono (Datatypes.S t) (Datatypes.S m)); lia.
  - apply (Qlt_le_trans (q_pow (1 / 2) (Datatypes.S t)) (q_pow (1 / 2) t)
                        delta).
    + apply q_pow_half_lt_self.
    + apply (Qle_trans (q_pow (1 / 2) t) (1 * q_pow (1 / 2) t) delta).
      * apply qeq_le. ring.
      * apply Qlt_le_weak. exact Ht.
Qed.

(* ============================================================ *)
(* Section 2. Numerical witnesses ([vm_compute] checks)         *)
(* ============================================================ *)

Lemma log_eps_4_val : log_eps 4 == (1 # 32)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma log_eps_5_val : log_eps 5 == (1 # 64)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma log_eps_7_val : log_eps 7 == (1 # 256)%Q.
Proof. vm_compute. reflexivity. Qed.
