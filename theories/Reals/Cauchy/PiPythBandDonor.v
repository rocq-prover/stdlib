(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(* ============================================================ *)
(* PiPythBandDonor.v                                            *)
(*                                                              *)
(* Mission: a partial-sum stratification of the Pythagorean      *)
(*       identity sin^2+cos^2=1 -- the diagonal-band representation *)
(*       of the truncation residual piL_pyth_dres and a uniform   *)
(*       smallness supply. The full diagonal coefficient equals   *)
(*       even half-row minus odd half-row (the even/odd halves of *)
(*       a Pascal row have equal sums), hence zero, so the        *)
(*       truncation residual is exactly the sum over the window   *)
(*       rows [k+1,2k+2]; the row majorant and the geometric tail *)
(*       band give some j such that k >= j and |x| <= B imply     *)
(*       |piL_pyth_dres k x| < dt.                                *)
(* Dependencies: Stdlib QArith.QArith, QArith.Qabs, ZArith.ZArith, *)
(*       Arith.PeanoNat, Lia; PiKernelSlack (q_pow/q_fact,        *)
(*       sin_term/cos_term, and, from its merged identity segment, *)
(*       piL_pyth_dres, piL_pythag_partial, piL_cos_term_0);      *)
(*       PiPascalMachine (the piLsb_sumR row-sum machine);        *)
(*       PiRowIdentity (piLrowB_row_scal); PiCosBandAssemble      *)
(*       (the row families ccrow/ssrow, row majorants, half-row   *)
(*       closed forms, the geometric tail band and the choice of  *)
(*       the truncation length).                                  *)
(* References: the sum side of the partial-sum band expansion of  *)
(*       cos(2x)=cos^2-sin^2 (piLe_dcos_band_rows): on the        *)
(*       difference side the full diagonal pairings form the      *)
(*       double-angle terms; on the sum side they cancel to zero. *)
(* Constructivity: statements on stdlib Qeq/Qle/Qlt with          *)
(*       Set-carried sigT; zero axioms, nothing admitted, no         *)
(*       classical logic; induction with explicit algebraic       *)
(*       chains; zero Q-domain solver (Lia for nat bookkeeping    *)
(*       only).                                                   *)
(* Build: coqc -native-compiler no -q -Q . "" PiPythBandDonor.v   *)
(*       (Rocq 9.1.0).                                            *)
(* ============================================================ *)

(* WARNING: this file is experimental and likely to change in future *)
(* releases.                                                        *)
From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.
Require Import PiPascalMachine.
Require Import PiRowIdentity.
Require Import PiCosBandAssemble.

(* ================= §1 Square-sum reshaping ================= *)

(* The square-sum form of the Pythagorean residual: pyth_dres k x == S_k^2 + C_k^2 - 1. *)
Lemma piLh_pyth_sq_form : forall (k : nat) (x : Q),
  piL_pyth_dres k x
  == sin_partial k x * sin_partial k x
     + cos_partial k x * cos_partial k x - 1.
Proof.
  intros k x. rewrite (piL_pythag_partial k x). ring.
Qed.

(* ============ §2 Full-diagonal cancellation (even half-row - odd half-row = 0) ============ *)

(* The full diagonal sum: sum_{i<S N} c_i c_{N-i} + sum_{i<N} s_i s_{N-1-i} == 0
   (N >= 1).  Each half-row equals 2^(2N)*(1/2) times the common factor
   (-1)^N / (-1)^(N-1); the two signs are opposite, so the sum is zero. *)
Lemma piLh_rowP_cross : forall (N : nat) (x : Q), (1 <= N)%nat ->
  piLsb_sumR (fun i => cos_term i x * cos_term (N - i)%nat x) (S N)
  + piLsb_sumR (fun i => sin_term i x * sin_term (N - 1 - i)%nat x) N
  == 0%Q.
Proof.
  intros N x HN.
  assert (HD0 : ~ (q_fact (2 * N)%nat == 0)%Q) by apply piLrowB_qfact_neq0.
  assert (Hcc : piLsb_sumR (fun i => cos_term i x * cos_term (N - i)%nat x) (S N)
                == q_pow (-1)%Q N * q_pow x (2 * N)%nat / q_fact (2 * N)%nat
                   * (q_pow 2%Q (2 * N)%nat * (1 # 2)%Q)).
  { rewrite <- (piLe_row_half_even_val N HN).
    rewrite <- (piLrowB_row_scal (q_pow (-1)%Q N * q_pow x (2 * N)%nat / q_fact (2 * N)%nat)
                  (fun i => bpa_binom (2 * N)%nat (2 * i)%nat) (S N)).
    apply piLsb_sumR_ext. intros i Hi.
    transitivity ((q_pow (-1)%Q N * q_pow x (2 * N)%nat
                   * bpa_binom (2 * N)%nat (2 * i)%nat) / q_fact (2 * N)%nat).
    - apply (piLe_qeq_mul_div_r _ _ _ HD0).
      apply (piLe_rowpiece_cc N i x). lia.
    - unfold Qdiv. ring. }
  assert (Hss : piLsb_sumR (fun i => sin_term i x * sin_term (N - 1 - i)%nat x) N
                == q_pow (-1)%Q (N - 1)%nat * q_pow x (2 * N)%nat / q_fact (2 * N)%nat
                   * (q_pow 2%Q (2 * N)%nat * (1 # 2)%Q)).
  { rewrite <- (piLe_row_half_odd_val N HN).
    rewrite <- (piLrowB_row_scal (q_pow (-1)%Q (N - 1)%nat * q_pow x (2 * N)%nat
                                  / q_fact (2 * N)%nat)
                  (fun i => bpa_binom (2 * N)%nat (S (2 * i)%nat)) N).
    apply piLsb_sumR_ext. intros i Hi.
    transitivity ((q_pow (-1)%Q (N - 1)%nat * q_pow x (2 * N)%nat
                   * bpa_binom (2 * N)%nat (S (2 * i)%nat)) / q_fact (2 * N)%nat).
    - apply (piLe_qeq_mul_div_r _ _ _ HD0).
      apply (piLe_rowpiece_ss N i x). lia.
    - unfold Qdiv. ring. }
  rewrite Hcc, Hss.
  assert (Hsg : q_pow (-1)%Q (N - 1)%nat == - q_pow (-1)%Q N).
  { replace (q_pow (-1)%Q N) with (q_pow (-1)%Q (S (N - 1))%nat)
      by (f_equal; lia).
    rewrite q_pow_succ. ring. }
  unfold Qdiv. rewrite Hsg. ring.
Qed.

(* ========= §3 Diagonal-band representation (residual = exact window-row sum) ========= *)

(* Band representation: pyth_dres k x == sum_{u<S k} [ccrow k (S(k+u)) x
   + ssrow k (S(k+u)) x].  The square sum goes through the product
   row-sum form, the square split, the lower triangle flattened along
   diagonals (rows w<=k are full rows of sum zero; after subtracting 1
   only the 1 of row 0 remains), and the upper triangle transposed into
   window rows (rows m=S(k+u), u<S k, i.e. the row range [k+1,2k+1]). *)
Lemma piLh_pyth_band_rows : forall (k : nat) (x : Q),
  piL_pyth_dres k x
  == piLsb_sumR (fun u => piLe_ccrow k (S (k + u))%nat x
                          + piLe_ssrow k (S (k + u))%nat x)
                (S k).
Proof.
  intros k x.
  assert (Hccrow_reidx : forall u : nat,
    piLe_ccrow k (S (k + u))%nat x
    == piLsb_sumR (fun i => cos_term (S (u + i))%nat x
                            * cos_term (S k - S (u + i) + u)%nat x) (k - u)%nat).
  { intros u. unfold piLe_ccrow.
    replace (2 * k + 1 - S (k + u))%nat with (k - u)%nat by lia.
    apply piLsb_sumR_ext. intros i Hi. cbv beta.
    replace (S (k + u) - k + i)%nat with (S (u + i))%nat by lia.
    replace (k - i)%nat with (S k - S (u + i) + u)%nat by lia.
    apply Qeq_refl. }
  assert (Hssrow_reidx : forall u : nat, (u < S k)%nat ->
    piLe_ssrow k (S (k + u))%nat x
    == piLsb_sumR (fun i => sin_term (u + i)%nat x
                            * sin_term (k - (u + i) + u)%nat x) (S (k - u))%nat).
  { intros u Hu. unfold piLe_ssrow.
    replace (2 * k + 2 - S (k + u))%nat with (S (k - u))%nat by lia.
    apply piLsb_sumR_ext. intros i Hi. cbv beta.
    replace (S (k + u) - 1 - k + i)%nat with (u + i)%nat by lia.
    replace (k - i)%nat with (k - (u + i) + u)%nat by lia.
    apply Qeq_refl. }
  rewrite (piLh_pyth_sq_form k x).
  rewrite (piLe_partial_cos_sumR k x).
  rewrite (piLe_partial_sin_sumR k x).
  rewrite (piLe_sumR_prod (S k) (S k) (fun i => cos_term i x) (fun i => cos_term i x)).
  rewrite (piLe_sumR_prod (S k) (S k) (fun i => sin_term i x) (fun i => sin_term i x)).
  cbv beta.
  assert (Hsplitc : piLsb_sumR
                      (fun i : nat => piLsb_sumR (fun j : nat => cos_term i x * cos_term j x)
                                          (S k)) (S k)
                    == piLsb_sumR
                         (fun i : nat => piLsb_sumR (fun j : nat => cos_term i x * cos_term j x)
                                             (S k - i)) (S k)
                       + piLsb_sumR
                           (fun i : nat => piLsb_sumR
                                              (fun u : nat => cos_term i x
                                                              * cos_term (S k - i + u) x) i)
                           (S k))
    by (apply (piLe_sumR_square_split_gen (S k) (fun i => S k - i)%nat (fun i => i)
                (fun i j => cos_term i x * cos_term j x)); intros i Hi; lia).
  rewrite Hsplitc.
  assert (Hsplits : piLsb_sumR
                      (fun i : nat => piLsb_sumR (fun j : nat => sin_term i x * sin_term j x)
                                          (S k)) (S k)
                    == piLsb_sumR
                         (fun i : nat => piLsb_sumR (fun j : nat => sin_term i x * sin_term j x)
                                             (k - i)) (S k)
                       + piLsb_sumR
                           (fun i : nat => piLsb_sumR
                                              (fun u : nat => sin_term i x
                                                              * sin_term (k - i + u) x)
                                              (Datatypes.S i)) (S k))
    by (apply (piLe_sumR_square_split_gen (S k) (fun i => k - i)%nat (fun i => Datatypes.S i)
                (fun i j => sin_term i x * sin_term j x)); intros i Hi; lia).
  rewrite Hsplits.
  assert (Hflatc : piLsb_sumR
                     (fun i : nat => piLsb_sumR (fun j : nat => cos_term i x * cos_term j x)
                                         (S k - i)) (S k)
                   == piLsb_sumR
                        (fun w : nat => piLsb_sumR
                                           (fun v : nat => cos_term v x
                                                           * cos_term (w - v) x) (S w))
                        (S k))
    by (apply (piLe_sumR_flatten_full (S k) (fun i j => cos_term i x * cos_term j x))).
  rewrite Hflatc.
  rewrite (piLsb_sumR_snoc
             (fun i => piLsb_sumR (fun j => sin_term i x * sin_term j x) (k - i)) k).
  cbv beta. replace (k - k)%nat with 0%nat by lia.
  rewrite piLe_sumR_0.
  assert (Hflats : piLsb_sumR
                     (fun i : nat => piLsb_sumR (fun j : nat => sin_term i x * sin_term j x)
                                         (k - i)) k
                   == piLsb_sumR
                        (fun w : nat => piLsb_sumR
                                           (fun v : nat => sin_term v x
                                                           * sin_term (w - v) x) (S w))
                        k)
    by (apply (piLe_sumR_flatten_full k (fun i j => sin_term i x * sin_term j x))).
  rewrite Hflats.
  assert (Hrowcdef : forall w : nat,
    piLe_rowc_full w x
    == piLsb_sumR (fun v : nat => cos_term v x * cos_term (w - v)%nat x) (S w)).
  { intros w. unfold piLe_rowc_full. apply Qeq_refl. }
  rewrite <- (piLsb_sumR_ext
                (fun w => piLe_rowc_full w x)
                (fun w => piLsb_sumR
                            (fun v : nat => cos_term v x * cos_term (w - v) x) (S w))
                (S k) (fun w _ => Hrowcdef w)).
  assert (Hrowsreidx : forall w : nat,
    piLe_rows_full (Datatypes.S w) x
    == piLsb_sumR (fun v : nat => sin_term v x * sin_term (w - v) x) (S w)).
  { intros w. unfold piLe_rows_full.
    apply piLsb_sumR_ext. intros v Hv.
    replace (Datatypes.S w - 1 - v)%nat with (w - v)%nat by lia.
    apply Qeq_refl. }
  rewrite <- (piLsb_sumR_ext
                (fun w => piLe_rows_full (Datatypes.S w) x)
                (fun w => piLsb_sumR
                            (fun v : nat => sin_term v x * sin_term (w - v) x) (S w))
                k (fun w _ => Hrowsreidx w)).
  assert (Hsh : piLsb_sumR (fun w : nat => piLe_rows_full (Datatypes.S w) x) k
                == piLsb_sumR (fun w : nat => piLe_rows_full w x) (S k))
    by (apply (piLe_sumR_shift_succ k (fun w => piLe_rows_full w x));
        cbv beta; unfold piLe_rows_full; cbn [piLsb_sumR]; ring).
  rewrite Hsh.
  assert (Htswl : piLsb_sumR
                    (fun i : nat => piLsb_sumR
                                       (fun u : nat => cos_term i x
                                                       * cos_term (S k - i + u) x) i) (S k)
                  == piLsb_sumR
                       (fun u : nat => piLsb_sumR
                                          (fun i : nat => cos_term (S (u + i)) x
                                                          * cos_term (S k - S (u + i) + u) x)
                                          (k - u)) (S k))
    by (apply (piLe_sumR_trapswap_lt k
                 (fun i u => cos_term i x * cos_term (S k - i + u) x))).
  rewrite Htswl.
  assert (Htswle : piLsb_sumR
                     (fun i : nat => piLsb_sumR
                                        (fun u : nat => sin_term i x
                                                        * sin_term (k - i + u) x)
                                        (Datatypes.S i)) (S k)
                   == piLsb_sumR
                        (fun u : nat => piLsb_sumR
                                           (fun i : nat => sin_term (u + i) x
                                            * sin_term (k - (u + i) + u) x)
                                           (S (k - u))) (S k))
    by (apply (piLe_sumR_trapswap_le k
                 (fun i u => sin_term i x * sin_term (k - i + u) x))).
  rewrite Htswle.
  rewrite <- (piLsb_sumR_ext
                (fun u => piLe_ccrow k (S (k + u))%nat x)
                (fun u => piLsb_sumR
                            (fun i : nat => cos_term (S (u + i)) x
                                            * cos_term (S k - S (u + i) + u) x) (k - u))
                (S k) (fun u _ => Hccrow_reidx u)).
  rewrite <- (piLsb_sumR_ext
                (fun u => piLe_ssrow k (S (k + u))%nat x)
                (fun u => piLsb_sumR
                            (fun i : nat => sin_term (u + i) x
                                            * sin_term (k - (u + i) + u) x) (S (k - u)))
                (S k) (fun u Hu => Hssrow_reidx u Hu)).
  rewrite (piLsb_sumR_plus (fun u => piLe_ccrow k (S (k + u))%nat x)
                (fun u => piLe_ssrow k (S (k + u))%nat x) (S k)).
  transitivity (piLsb_sumR (fun w : nat => piLe_rowc_full w x) (S k)
                + piLsb_sumR (fun w : nat => piLe_rows_full w x) (S k) - 1
                + piLsb_sumR (fun u => piLe_ccrow k (S (k + u))%nat x) (S k)
                + piLsb_sumR (fun u => piLe_ssrow k (S (k + u))%nat x) (S k)).
  { ring. }
  assert (Hfull : piLsb_sumR (fun w : nat => piLe_rowc_full w x) (S k)
                  + piLsb_sumR (fun w : nat => piLe_rows_full w x) (S k) == 1%Q).
  { rewrite <- (piLsb_sumR_plus (fun w => piLe_rowc_full w x)
                  (fun w => piLe_rows_full w x) (S k)).
    rewrite piLsb_sumR_head. cbv beta.
    assert (H0 : piLe_rowc_full 0%nat x + piLe_rows_full 0%nat x == 1%Q).
    { unfold piLe_rowc_full, piLe_rows_full. cbn [piLsb_sumR]. cbv beta.
      vm_compute. reflexivity. }
    assert (Ht : piLsb_sumR
                   (fun i : nat => piLe_rowc_full (Datatypes.S i) x
                                   + piLe_rows_full (Datatypes.S i) x) k
                 == piLsb_sumR (fun w : nat => 0%Q) k).
    { apply piLsb_sumR_ext. intros w Hw. cbv beta.
      transitivity (piLe_rowc_full (Datatypes.S w) x
                    + piLe_rows_full (Datatypes.S w) x).
      - apply Qeq_refl.
      - unfold piLe_rowc_full, piLe_rows_full.
        rewrite piLh_rowP_cross by lia. reflexivity. }
    assert (Hzall : forall n : nat, piLsb_sumR (fun w : nat => 0%Q) n == 0%Q).
    { induction n as [| n' IHn].
      - apply piLe_sumR_0.
      - cbn [piLsb_sumR]. rewrite IHn. ring. }
    rewrite Ht, Hzall, H0. ring. }
  rewrite Hfull. ring.
Qed.

(* ================= §4 Band bound and slot-face supply ================= *)

(* Band bound: |pyth_dres k x| <= band_bound k B (all k, |x| <= B). *)
Theorem piLh_pyth_band_le : forall (k : nat) (x B : Q),
  Qle (Qabs x) B -> Qle (Qabs (piL_pyth_dres k x)) (piLe_band_bound k B).
Proof.
  intros k x B Hx.
  rewrite piLh_pyth_band_rows.
  apply (Qle_trans _
           (piLsb_sumR (fun u => Qabs (piLe_ccrow k (S (k + u))%nat x
                                       + piLe_ssrow k (S (k + u))%nat x))
                       (S k))).
  { apply piLe_abs_sumR_le. }
  apply (Qle_trans _
           (piLsb_sumR (fun u => Qabs (piLe_ccrow k (S (k + u))%nat x)
                                 + Qabs (piLe_ssrow k (S (k + u))%nat x))
                       (S k))).
  { apply piLe_sumR_le. intros u _. apply Qabs_triangle. }
  apply (Qle_trans _
           (piLsb_sumR (fun u => (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B
                                 + (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)
                       (S k))).
  { apply piLe_sumR_le. intros u Hu.
    apply (Qplus_le_compat
             (Qabs (piLe_ccrow k (S (k + u))%nat x))
             ((1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)
             (Qabs (piLe_ssrow k (S (k + u))%nat x))
             ((1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)).
    - apply (piLe_ccrow_abs_le k (S (k + u)) x B); [lia | exact Hx].
    - apply (piLe_ssrow_abs_le k (S (k + u)) x B); [lia | exact Hx]. }
  assert (Hdouble : forall u : nat,
    ((1 # 2)%Q * piLe_tc_term (S (k + u))%nat B
     + (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)
    == piLe_tc_term (S (k + u))%nat B) by (intros u; ring).
  assert (H0B : Qle 0 B)
    by (apply (Qle_trans 0 (Qabs x) B); [apply Qabs_nonneg | exact Hx]).
  unfold piLe_band_bound.
  rewrite (piLsb_sumR_snoc (fun u => piLe_tc_term (S (k + u))%nat B) (S k)).
  cbv beta.
  rewrite (piLsb_sumR_ext
                (fun u => (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B
                          + (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)
                (fun u => piLe_tc_term (S (k + u))%nat B)
                (S k) (fun u _ => Hdouble u)).
  apply (Qle_trans _
           (piLsb_sumR (fun u => piLe_tc_term (S (k + u))%nat B) (S k) + 0%Q)).
  { rewrite Qplus_0_r. apply Qle_refl. }
  apply (Qplus_le_compat
           (piLsb_sumR (fun u => piLe_tc_term (S (k + u))%nat B) (S k))
           (piLsb_sumR (fun u => piLe_tc_term (S (k + u))%nat B) (S k))
           0%Q
           (piLe_tc_term (S (k + S k))%nat B)).
  - apply Qle_refl.
  - apply piLe_tc_term_nonneg. exact H0B.
Qed.

(* Slot-face supply: there is j such that k >= j and |x| <= B imply
   |pyth_dres k x| < dt.  The statement face is verbatim that of the
   Pythagorean-residual band slot of the half-window assembly segment. *)
Lemma piLh_pyth_small : forall (B dt : Q),
  Qlt 0 B -> Qlt 0 dt ->
  sigT (fun j : nat => forall (k : nat) (x : Q),
    (j <= k)%nat -> Qle (Qabs x) B -> Qlt (Qabs (piL_pyth_dres k x)) dt).
Proof.
  intros B dt HB Hdt.
  destruct (piLe_band_small B dt HB Hdt) as [j Hj].
  exists j. intros k x Hkx HxB.
  apply (Qle_lt_trans _ (piLe_band_bound k B)).
  - apply (piLh_pyth_band_le k x B HxB).
  - apply (Hj k Hkx).
Qed.

Print Assumptions piLh_pyth_sq_form.
Print Assumptions piLh_rowP_cross.
Print Assumptions piLh_pyth_band_rows.
Print Assumptions piLh_pyth_band_le.
Print Assumptions piLh_pyth_small.
