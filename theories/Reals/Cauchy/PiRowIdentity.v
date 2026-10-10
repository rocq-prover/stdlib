(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The row identity behind the partial-sum stratification of the
    double-angle sine

    Mission.  The row identity in the partial-sum stratification of
    [sin(2x) = 2 sin x cos x] -- the pointwise equality, row by row,
    between the double-product coefficient row
    [row_m(x) := sum_{i<=m} 2 * sin_term i x * cos_term (m-i) x] and
    the double-angle sine term [sin_term m (2x)].  The route
    multiplies both sides by [(2m+1)!] to reach pure binomial
    content: the row side concludes with the Pascal odd half-row
    [sum_{i<=m} C(2m+1,2i+1) == 2^(2m)], and the term side concludes
    through divisor cancellation (explicit step by step via
    [Qmult_inv_r]) and a power split.

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith],
    [Arith.PeanoNat], [Lia]; [PiKernelSlack] (the
    [sin_term]/[cos_term]/[q_pow]/[q_fact]/[bpa_binom] definitions
    native to it); [PiPascalMachine] (the [piLsb_sumR] row-sum
    machine, the [piLsb_bpa_bridge] binomial-factorial bridge, the
    [piLsb_row_odd] odd half-row).

    References.  The row-cancellation layer of the offset row
    decomposition [piL_sin_dres] in Section 2 of
    [PiKernelSlack_D1_identity] (this file supplies its row-level
    content); the standard identities of binomial coefficients (the
    row-sum and odd-half-row splits).

    Constructivity.  The statement level consists entirely of [Qeq]
    identities (in the statement shape of the
    [PiKernelSlack_D1_identity]/[PiPascalMachine] family);
    assumption-free and fully proved, with no non-constructive
    principles; induction with explicit algebraic chains and zero
    solver endings on the [Q] side ([Lia] only for [nat]-side
    bookkeeping); the computational witnesses of the final section
    are auxiliary statements whose trivial character is declared
    explicitly.  Extractable.

    Build.  [coqc -native-compiler no -q -Q . "" PiRowIdentity.v];
    the first eight bytes of the artifact are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.
Require Import PiPascalMachine.

(* ============ Section 1. The product-coefficient row (carried by the row-sum machine [sumR]) and the scalar lemmas ============ *)

(** The coefficient row of the double product
    [2 * (sum sin_term) * (sum cos_term)], grouped by [i+j=m].  The
    carrier directly reuses [piLsb_sumR] (consuming the existing
    row-sum machine instead of coining another isomorphic
    [Fixpoint]). *)
Definition piLrowB_row (m : nat) (x : Q) : Q :=
  piLsb_sumR (fun i => 2%Q * sin_term i x * cos_term (m - i)%nat x) (Datatypes.S m).

Lemma piLrowB_row_scal : forall (c : Q) (f : nat -> Q) (n : nat),
  piLsb_sumR (fun i => c * f i) n == c * piLsb_sumR f n.
Proof.
  intros c f n. induction n as [| n IH].
  - cbn [piLsb_sumR]. ring.
  - cbn [piLsb_sumR]. rewrite IH. ring.
Qed.

Lemma piLrowB_row_scal_r : forall (c : Q) (f : nat -> Q) (n : nat),
  piLsb_sumR f n * c == piLsb_sumR (fun i => f i * c) n.
Proof.
  intros c f n.
  rewrite (Qmult_comm (piLsb_sumR f n) c).
  rewrite <- (piLrowB_row_scal c f n).
  apply (piLsb_sumR_ext (fun i => c * f i) (fun i => f i * c) n).
  intros i _. cbv beta. apply Qmult_comm.
Qed.

(** The row-sum-machine representation of the partial sums:
    [sin_partial n == sum_{i<=n} sin_term i] (the offset-band
    regrouping layer takes this as the entry point that views the
    partial sums as sums on the row machine). *)
Lemma piLrowB_sin_partial_sumR : forall (n : nat) (x : Q),
  sin_partial n x == piLsb_sumR (fun m => sin_term m x) (Datatypes.S n).
Proof.
  intros n x. induction n as [| p IH].
  - cbn [sin_partial piLsb_sumR]. cbv beta. ring.
  - cbn [sin_partial].
    rewrite (piLsb_sumR_snoc (fun m => sin_term m x) (Datatypes.S p)).
    cbv beta. rewrite IH. ring.
Qed.

Lemma piLrowB_cos_partial_sumR : forall (n : nat) (x : Q),
  cos_partial n x == piLsb_sumR (fun m => cos_term m x) (Datatypes.S n).
Proof.
  intros n x. induction n as [| p IH].
  - cbn [cos_partial piLsb_sumR]. cbv beta. ring.
  - cbn [cos_partial].
    rewrite (piLsb_sumR_snoc (fun m => cos_term m x) (Datatypes.S p)).
    cbv beta. rewrite IH. ring.
Qed.

(* ============ Section 2. Cancellation base lemmas ([Qmult_inv_r], explicit at every step) ============ *)

Lemma piLrowB_qfact_neq0 : forall n : nat, ~ (q_fact n == 0)%Q.
Proof.
  intros n H. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)).
  apply Qeq_sym. exact H.
Qed.

Lemma piLrowB_div_mul_both : forall (a d : Q), ~ (d == 0)%Q -> (a / d) * d == a.
Proof.
  intros a d Hd. unfold Qdiv.
  rewrite <- Qmult_assoc.
  rewrite (Qmult_comm (/ d) d).
  rewrite (Qmult_inv_r d Hd).
  apply Qmult_1_r.
Qed.

Lemma piLrowB_qeq_cancel_l : forall (a b c : Q),
  ~ (c == 0)%Q -> a * c == b * c -> a == b.
Proof.
  intros a b c Hc H.
  pose proof (Qmult_inv_r c Hc) as Hcc.
  assert (Hl : a == a * (c * Qinv c)).
  { rewrite Hcc. symmetry. apply Qmult_1_r. }
  rewrite Hl.
  transitivity (b * (c * Qinv c)).
  - assert (Hstep : a * (c * Qinv c) == b * (c * Qinv c)).
    { transitivity ((a * c) * Qinv c).
      - ring.
      - rewrite H. ring. }
    exact Hstep.
  - rewrite Hcc. apply Qmult_1_r.
Qed.

(* ============ Section 3. Row-piece denominator cancellation (product form; one [Qmult_inv_r] pair per piece) ============ *)

Lemma piLrowB_rowpiece : forall (m t : nat) (x : Q), (t <= m)%nat ->
  (2 * sin_term t x * cos_term (m - t)%nat x) * q_fact (Datatypes.S (2 * m))
  == 2%Q * q_pow (-1)%Q m * q_pow x (Datatypes.S (2 * m))
     * bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * t)).
Proof.
  intros m t x Htm.
  (* The common-factor form of the row term (in reciprocal form):
     the sign, power, and reciprocal groups merged *)
  assert (Hfac : 2%Q * sin_term t x * cos_term (m - t)%nat x
                 == q_pow (-1)%Q m * q_pow x (Datatypes.S (2 * m)) * 2%Q
                    * Qinv (q_fact (Datatypes.S (2 * t)) * q_fact (2 * m - 2 * t)%nat)).
  { assert (Hreg0 : 2%Q * sin_term t x * cos_term (m - t)%nat x
                 == 2%Q * (q_pow (-1)%Q t * q_pow (-1)%Q (m - t)%nat)
                    * (q_pow x (Datatypes.S (2 * t)) * q_pow x (2 * (m - t))%nat)
                    * (Qinv (q_fact (Datatypes.S (2 * t))) * Qinv (q_fact (2 * (m - t))%nat))).
    { unfold sin_term, cos_term, Qdiv. ring. }
    rewrite Hreg0.
    rewrite <- (lw0_q_pow_add (-1)%Q t (m - t)%nat).
    assert (Hnm : (t + (m - t))%nat = m) by lia.
    rewrite Hnm.
    rewrite <- (lw0_q_pow_add x (Datatypes.S (2 * t)) (2 * (m - t))%nat).
    assert (Hsm : (Datatypes.S (2 * t) + 2 * (m - t))%nat = Datatypes.S (2 * m)) by lia.
    rewrite Hsm.
    rewrite <- (Qinv_mult_distr (q_fact (Datatypes.S (2 * t))) (q_fact (2 * (m - t))%nat)).
    assert (Hmi : (2 * (m - t))%nat = (2 * m - 2 * t)%nat) by lia.
    rewrite Hmi.
    ring. }
  rewrite Hfac.
  (* Substitution through the Pascal bridge: [q_fact(S(2m))]
     normalizes to [bpa * q_fact(S(2t)) * q_fact(2m-2t)] *)
  assert (Hk : (Datatypes.S (2 * t) <= Datatypes.S (2 * m))%nat) by lia.
  pose proof (piLsb_bpa_bridge (Datatypes.S (2 * m)) (Datatypes.S (2 * t)) Hk) as Hbb.
  assert (Hsub : (Datatypes.S (2 * m) - Datatypes.S (2 * t))%nat = (2 * m - 2 * t)%nat) by lia.
  rewrite Hsub in Hbb.
  pose proof (piLrowB_qfact_neq0 (Datatypes.S (2 * t))) as Hn1.
  pose proof (piLrowB_qfact_neq0 (2 * m - 2 * t)%nat) as Hn2.
  assert (H1 : q_fact (Datatypes.S (2 * t)) * Qinv (q_fact (Datatypes.S (2 * t))) == 1%Q)
    by (apply Qmult_inv_r; exact Hn1).
  assert (H2 : q_fact (2 * m - 2 * t) * Qinv (q_fact (2 * m - 2 * t)) == 1%Q)
    by (apply Qmult_inv_r; exact Hn2).
  assert (Hreg : (q_pow (-1)%Q m * q_pow x (Datatypes.S (2 * m)) * 2%Q
                    * Qinv (q_fact (Datatypes.S (2 * t)) * q_fact (2 * m - 2 * t)%nat))
                 * q_fact (Datatypes.S (2 * m))
                 == q_pow (-1)%Q m * q_pow x (Datatypes.S (2 * m)) * 2%Q
                    * ((q_fact (Datatypes.S (2 * t)) * Qinv (q_fact (Datatypes.S (2 * t))))
                       * (q_fact (2 * m - 2 * t) * Qinv (q_fact (2 * m - 2 * t))))
                    * bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * t))).
  { rewrite Qinv_mult_distr. rewrite <- Hbb. ring. }
  rewrite Hreg, H1, H2. ring.
Qed.

(* ============ Section 4. The row sum with canceled denominators (after piece-by-piece cancellation, the odd half-row concludes) ============ *)

Lemma piLrowB_row_fact_sum : forall (m : nat) (x : Q),
  piLrowB_row m x * q_fact (Datatypes.S (2 * m))
  == 2%Q * q_pow (-1)%Q m * q_pow x (Datatypes.S (2 * m)) * q_pow 2%Q (2 * m)%nat.
Proof.
  intros m x. unfold piLrowB_row.
  assert (Hrev : piLsb_sumR (fun i => 2%Q * sin_term i x * cos_term (m - i)%nat x) (Datatypes.S m)
                 * q_fact (Datatypes.S (2 * m))
                 == piLsb_sumR (fun i => (2%Q * sin_term i x * cos_term (m - i)%nat x)
                                         * q_fact (Datatypes.S (2 * m))) (Datatypes.S m))
    by (apply (piLrowB_row_scal_r (q_fact (Datatypes.S (2 * m)))
                 (fun i => 2%Q * sin_term i x * cos_term (m - i)%nat x) (Datatypes.S m))).
  rewrite Hrev.
  assert (Hext : piLsb_sumR (fun i => (2%Q * sin_term i x * cos_term (m - i)%nat x)
                                      * q_fact (Datatypes.S (2 * m))) (Datatypes.S m)
                 == piLsb_sumR (fun i => 2%Q * q_pow (-1)%Q m * q_pow x (Datatypes.S (2 * m))
                                              * bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i)))
                               (Datatypes.S m)).
  { apply piLsb_sumR_ext. intros i Hi. apply piLrowB_rowpiece. lia. }
  rewrite Hext.
  rewrite (piLrowB_row_scal (2%Q * q_pow (-1)%Q m * q_pow x (Datatypes.S (2 * m)))
             (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i))) (Datatypes.S m)).
  rewrite piLsb_row_odd. ring.
Qed.

(* ============ Section 5. The main theorem, the row identity (both sides multiplied by the denominator and the factor canceled) ============ *)

Theorem piLrowB_row_sin_term : forall (m : nat) (x : Q),
  piLrowB_row m x == sin_term m (2 * x)%Q.
Proof.
  intros m x.
  assert (Hne : ~ (q_fact (Datatypes.S (2 * m)) == 0%Q)) by (apply piLrowB_qfact_neq0).
  apply (piLrowB_qeq_cancel_l _ _ (q_fact (Datatypes.S (2 * m))) Hne).
  transitivity (2%Q * q_pow (-1)%Q m * q_pow x (Datatypes.S (2 * m)) * q_pow 2%Q (2 * m)%nat).
  - apply piLrowB_row_fact_sum.
  - unfold sin_term.
    rewrite <- (Qmult_assoc (q_pow (-1)%Q m)
                  (q_pow (2 * x)%Q (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)))
                  (q_fact (Datatypes.S (2 * m)))).
    rewrite (piLrowB_div_mul_both (q_pow (2 * x)%Q (Datatypes.S (2 * m)))
               (q_fact (Datatypes.S (2 * m))) Hne).
    rewrite <- (lw0_q_pow_mult 2%Q x (Datatypes.S (2 * m))).
    rewrite (q_pow_succ 2%Q (2 * m)%nat).
    ring.
Qed.

(* ============ Section 6. Computational witnesses (auxiliary statements; trivial character declared explicitly) ============ *)

(** In-kernel witnesses for small instances: for [m] = 3 and [4]
    with [x = 13/10], the row values agree with the double-angle
    sine terms; the row values in fraction form (after reduction)
    agree with independent exact-arithmetic recomputation. *)
Definition piLrowB_witness_row3 : Q := piLrowB_row 3 (13 # 10)%Q.

Lemma piLrowB_witness_row3_val : piLrowB_witness_row3 == (-62748517 # 393750000)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piLrowB_witness_row3_term : piLrowB_witness_row3 == sin_term 3 (2 * (13 # 10))%Q.
Proof. unfold piLrowB_witness_row3. apply piLrowB_row_sin_term. Qed.

Definition piLrowB_witness_row4 : Q := piLrowB_row 4 (13 # 10)%Q.

Lemma piLrowB_witness_row4_val : piLrowB_witness_row4 == (10604499373 # 708750000000)%Q.
Proof. vm_compute. reflexivity. Qed.
