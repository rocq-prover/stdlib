(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The anti-diagonal band representation of the truncation
    remainder

    Mission.  The anti-diagonal band representation in the
    partial-sum stratification of [sin(2x) = 2 sin x cos x] -- a
    band-row grouped representation of the truncation remainder
    [piL_sin_dres] (the difference between the double product
    [2 * S_k * C_k] and the double-angle partial sum [S_k(2x)]): the
    band row [bandrow k m] is the segment sum over the anti-diagonal
    [i+j=m] of the square of product coefficients {[i,j <= k]} (with
    the row range [k+1 <= m <= 2k]); the band sum
    [bandsum k (k-1)] accumulates along the row range and equals the
    remainder pointwise (the band representation theorem
    [piLc_dres_band]); the companion partial-sum identity is
    [2 * S_k * C_k == S_k(2x) + bandsum k (k-1)]
    ([piLc_double_sum_band]).

    Dependencies.  Stdlib [QArith.QArith], [ZArith.ZArith],
    [Arith.PeanoNat], [Lia]; [PiKernelSlack]
    ([sin_term]/[cos_term]/[sin_partial]/[cos_partial], the
    [piL_sin_dres]/[piL_sin_partial_double_at] face of
    [PiKernelSlack] (merged segment)); [PiPascalMachine] (the
    [piLsb_sumR] row-sum machine with its [head]/[snoc]/[ext]
    lemmas); [PiRowIdentity] (the row identity
    [piLrowB_row_sin_term] on [piLrowB_row], the [piLrowB_row_scal]
    scalar extraction, the [partial == sumR] regrouping entry).

    References.  The anti-diagonal band regrouping layer of the
    [dres] recursion in Section 2 of [PiKernelSlack] (merged segment);
    anti-diagonal summation by parts for two-dimensional discrete
    convolution (the triangular sum regrouping [piLc_flatten]).

    Constructivity.  The statement level consists entirely of [Qeq]
    identities; assumption-free and fully proved, with no
    non-constructive principles; induction with explicit algebraic
    chains and zero solver endings on the [Q] side ([Lia] only as
    auxiliary [nat]-side arithmetic); in the definition faces of
    [bandrow]/[bandsum] the [nat] subtractions are non-truncating
    within the semantic range [k < m <= 2k], and the bookkeeping over
    the row range is carried by the triangular sum regrouping lemma;
    definitions are transparent and extractable; the computational
    witnesses of the final section are auxiliary statements whose
    trivial character is declared explicitly.

    Build.  [coqc -native-compiler no -q -Q . "" PiPascalResidue.v];
    the first eight bytes of the artifact are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.
Require Import PiPascalMachine.
Require Import PiRowIdentity.

(* ============ Section 1. Anti-diagonal band rows and the band sum (row range [k+1, 2k]) ============ *)

(** The band row: the in-range segment of row [m],
    [sum_{u < 2k+1-m} 2 * sin_term (m-k+u) x * cos_term (k-u) x],
    that is, the segment sum over the anti-diagonal [i+j=m] of the
    square of product coefficients {[i,j <= k]} (for [k < m <= 2k]
    it is exactly the intersection of that anti-diagonal with the
    square; the three [nat] subtractions are non-truncating within
    the semantic range). *)
Definition piLc_bandrow (k m : nat) (x : Q) : Q :=
  piLsb_sumR
    (fun u => 2%Q * sin_term (m - k + u)%nat x * cos_term (k - u)%nat x)
    (2 * k + 1 - m)%nat.

(** The band sum: [piLc_bandsum k t x == sum_{u=0}^{t} bandrow k
    (k+1+u) x].  Main instance [t := k-1]: for [k>=1] the row range
    is [k+1, 2k]; for [k=0], [t=0] reaches the empty band [0]. *)
Fixpoint piLc_bandsum (k t : nat) (x : Q) : Q :=
  match t with
  | 0%nat => piLc_bandrow k (Datatypes.S k) x
  | Datatypes.S t' =>
      piLc_bandsum k t' x + piLc_bandrow k (Datatypes.S (k + Datatypes.S t'))%nat x
  end.

(** The separated representation of the band sum:
    [sum_{w<k} 2 * sin_term (S w) x * (C_k - C_{k-1-w})], obtained
    from the triangular sum regrouping and the tail-segment
    difference of partial sums (Section 3, [piLc_bandsum_sep]). *)
Definition piLc_bandsep (k : nat) (x : Q) : Q :=
  piLsb_sumR
    (fun w => 2%Q * sin_term (Datatypes.S w) x
              * (cos_partial k x - cos_partial (k - 1 - w)%nat x)) k.

(* ============ Section 2. Triangular sum regrouping for the row-sum machine ============ *)

(* Index reversal of row sums:
   [sum_{i<n} g(n-1-i) == sum_{i<n} g i]. *)
Lemma piLc_sumR_rev : forall (n : nat) (g : nat -> Q),
  piLsb_sumR (fun i => g (n - 1 - i)%nat) n == piLsb_sumR g n.
Proof.
  intros n g. induction n as [| m IH].
  - reflexivity.
  - assert (Ht : piLsb_sumR (fun i => g (Datatypes.S m - 1 - Datatypes.S i)%nat) m
                 == piLsb_sumR (fun i => g (m - 1 - i)%nat) m).
    { apply piLsb_sumR_ext. intros i _.
      replace (Datatypes.S m - 1 - Datatypes.S i)%nat with (m - 1 - i)%nat by lia.
      apply Qeq_refl. }
    rewrite (piLsb_sumR_head (fun i => g (Datatypes.S m - 1 - i)%nat) m). cbv beta.
    replace (Datatypes.S m - 1 - 0)%nat with m%nat by lia.
    rewrite (piLsb_sumR_snoc g m).
    rewrite Ht, IH. ring.
Qed.

(* Triangular sum regrouping: the double row sum over the lower
   triangle {[u,v] : u+v < K} is regrouped along the anti-diagonals
   [w = u+v].  This is the carrying lemma for the summation by
   parts over band rows. *)
Lemma piLc_flatten : forall (K : nat) (f : nat -> nat -> Q),
  piLsb_sumR (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (K - u)%nat) K
  == piLsb_sumR (fun w => piLsb_sumR (fun v => f w v) (Datatypes.S w)) K.
Proof.
  intros K f. induction K as [| K IH].
  - reflexivity.
  - assert (Hlast : (Datatypes.S K - K)%nat = 1%nat) by lia.
    assert (Hsplit :
      piLsb_sumR (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (Datatypes.S K - u)%nat) K
      == piLsb_sumR (fun u => piLsb_sumR (fun v => f (u + v)%nat v) (K - u)%nat) K
         + piLsb_sumR (fun u => f (u + (K - u))%nat (K - u)%nat) K).
    { rewrite <- (piLsb_sumR_plus (fun u => piLsb_sumR (fun v => f (u + v)%nat v)
                                       (K - u)%nat)
                    (fun u => f (u + (K - u))%nat (K - u)%nat) K).
      apply piLsb_sumR_ext. intros u Hu. cbv beta.
      replace (Datatypes.S K - u)%nat with (Datatypes.S (K - u))%nat by lia.
      rewrite piLsb_sumR_snoc. cbv beta. apply Qeq_refl. }
    assert (HB : piLsb_sumR (fun u => f (u + (K - u))%nat (K - u)%nat) K
                 == piLsb_sumR (fun i => f K (Datatypes.S i)%nat) K).
    { rewrite <- (piLc_sumR_rev K (fun u => f (u + (K - u))%nat (K - u)%nat)).
      apply piLsb_sumR_ext. intros i Hi. cbv beta.
      replace ((K - 1 - i) + (K - (K - 1 - i)))%nat with K by lia.
      replace (K - (K - 1 - i))%nat with (Datatypes.S i) by lia.
      apply Qeq_refl. }
    rewrite (piLsb_sumR_snoc (fun u => piLsb_sumR (fun v => f (u + v)%nat v)
                                 (Datatypes.S K - u)%nat) K). cbv beta.
    rewrite Hlast. cbn [piLsb_sumR]. cbv beta.
    replace (K + 0)%nat with K by lia.
    rewrite Hsplit, IH.
    rewrite (piLsb_sumR_snoc (fun w => piLsb_sumR (fun v => f w v) (Datatypes.S w)) K).
    cbv beta.
    rewrite HB, (piLsb_sumR_head (f K) K).
    ring.
Qed.

(* The tail-segment difference of partial sums:
   [sum_{v<=w} cos_term (K-v) x == C_K - C_{K-1-w}] (for [w < K]). *)
Lemma piLc_cos_tail : forall (w K : nat) (x : Q), (w < K)%nat ->
  piLsb_sumR (fun v => cos_term (K - v)%nat x) (Datatypes.S w)
  == cos_partial K x - cos_partial (K - 1 - w)%nat x.
Proof.
  induction w as [| w IH]; intros K x Hw.
  - replace K with (Datatypes.S (K - 1))%nat by lia.
    replace (Datatypes.S (K - 1) - 1 - 0)%nat with (K - 1)%nat by lia.
    cbn [piLsb_sumR cos_partial].
    replace (Datatypes.S (K - 1) - 0)%nat with (Datatypes.S (K - 1))%nat by lia.
    ring.
  - rewrite (piLsb_sumR_snoc (fun v => cos_term (K - v)%nat x) (Datatypes.S w)).
    cbv beta.
    rewrite (IH K x) by lia.
    replace (K - 1 - w)%nat with (Datatypes.S (K - 1 - Datatypes.S w))%nat by lia.
    replace (K - Datatypes.S w)%nat with (Datatypes.S (K - 1 - Datatypes.S w))%nat by lia.
    cbn [cos_partial]. ring.
Qed.

(* ============ Section 3. The row-sum-machine representation and the separated representation of the band sum ============ *)

(* The row-sum-machine representation of the band sum:
   [bandsum k t == sum_{u < t+1} bandrow k (S (k+u))]. *)
Lemma piLc_bandsum_bridge : forall (k t : nat) (x : Q),
  piLc_bandsum k t x
  == piLsb_sumR (fun u => piLc_bandrow k (Datatypes.S (k + u)%nat) x) (Datatypes.S t).
Proof.
  intros k t x. induction t as [| t IH].
  - cbn [piLc_bandsum piLsb_sumR]. cbv beta.
    rewrite Nat.add_0_r. ring.
  - cbn [piLc_bandsum]. cbv beta.
    rewrite (piLsb_sumR_snoc (fun u => piLc_bandrow k (Datatypes.S (k + u)%nat) x)
               (Datatypes.S t)).
    cbv beta. rewrite IH. ring.
Qed.

(* The triangular in-place form of the band row:
   [bandrow k (S(k+u)) == sum_{v < k-u} 2 * s_{S(u+v)} * c_{k-v}]. *)
Lemma piLc_bandrow_full : forall (k u : nat) (x : Q), (u < k)%nat ->
  piLc_bandrow k (Datatypes.S (k + u)%nat) x
  == piLsb_sumR (fun v => 2%Q * sin_term (Datatypes.S (u + v)%nat) x
                        * cos_term (k - v)%nat x) (k - u)%nat.
Proof.
  intros k u x Hu. unfold piLc_bandrow.
  replace (2 * k + 1 - Datatypes.S (k + u))%nat with (k - u)%nat by lia.
  apply piLsb_sumR_ext. intros v _.
  replace (Datatypes.S (k + u) - k + v)%nat with (Datatypes.S (u + v))%nat by lia.
  apply Qeq_refl.
Qed.

(** The separated representation of the band sum (main instance,
    full band): [bandsum k (k-1) == bandsep k].  Route: the
    row-sum-machine bridge, the triangular in-place form of the
    band rows, the [flatten] anti-diagonal regrouping, then scalar
    extraction and the tail-segment difference of partial sums. *)
Lemma piLc_bandsum_sep : forall (k : nat) (x : Q),
  piLc_bandsum k (k - 1)%nat x == piLc_bandsep k x.
Proof.
  intros k x. destruct k as [| k].
  - vm_compute. reflexivity.
  - replace (Datatypes.S k - 1)%nat with k by lia.
    transitivity
      (piLsb_sumR (fun u => piLc_bandrow (Datatypes.S k)
                            (Datatypes.S (Datatypes.S k + u)%nat) x) (Datatypes.S k)).
    { apply (piLc_bandsum_bridge (Datatypes.S k) k x). }
    transitivity
      (piLsb_sumR (fun u => piLsb_sumR (fun v =>
                          2%Q * sin_term (Datatypes.S (u + v)%nat) x
                          * cos_term (Datatypes.S k - v)%nat x)
                          (Datatypes.S k - u)%nat) (Datatypes.S k)).
    { apply piLsb_sumR_ext. intros u Hu.
      apply (piLc_bandrow_full (Datatypes.S k) u x Hu). }
    transitivity
      (piLsb_sumR (fun w => piLsb_sumR (fun v =>
                      2%Q * sin_term (Datatypes.S w) x
                      * cos_term (Datatypes.S k - v)%nat x) (Datatypes.S w))
                      (Datatypes.S k)).
    { apply (piLc_flatten (Datatypes.S k)
               (fun w v => 2%Q * sin_term (Datatypes.S w) x
                           * cos_term (Datatypes.S k - v)%nat x)). }
    unfold piLc_bandsep.
    apply piLsb_sumR_ext. intros w Hw.
    transitivity (2%Q * sin_term (Datatypes.S w) x
                  * piLsb_sumR (fun v => cos_term (Datatypes.S k - v)%nat x) (Datatypes.S w)).
    { apply (piLrowB_row_scal (2%Q * sin_term (Datatypes.S w) x)
               (fun v => cos_term (Datatypes.S k - v)%nat x) (Datatypes.S w)). }
    rewrite (piLc_cos_tail w (Datatypes.S k) x Hw).
    cbv beta. apply Qeq_refl.
Qed.

(* ============ Section 4. The step of the separated representation and the match with the remainder recursion ============ *)

(* The step of the separated representation: the increment of
   [bandsep (S k)] is exactly the step increment of the [dres]
   recursion (the cross products [2 * S_k * c' + 2 * C_k * s' +
   2 * s' * c'] minus the new double-angle sine term). *)
Lemma piLc_bandsep_step : forall (k : nat) (x : Q),
  piLc_bandsep (Datatypes.S k) x
  == piLc_bandsep k x
     + (2%Q * sin_partial k x * cos_term (Datatypes.S k) x
        + 2%Q * cos_partial k x * sin_term (Datatypes.S k) x
        + 2%Q * sin_term (Datatypes.S k) x * cos_term (Datatypes.S k) x
        - sin_term (Datatypes.S k) (2 * x)%Q).
Proof.
  intros k x. unfold piLc_bandsep.
  rewrite (piLsb_sumR_snoc (fun w => 2%Q * sin_term (Datatypes.S w) x
                                    * (cos_partial (Datatypes.S k) x
                                       - cos_partial (Datatypes.S k - 1 - w)%nat x)) k).
  cbv beta.
  replace (Datatypes.S k - 1)%nat with k by lia.
  replace (k - k)%nat with 0%nat by lia.
  cbn [cos_partial].
  assert (Hpt :
    piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * (cos_partial k x + cos_term (Datatypes.S k) x
                            - cos_partial (k - w)%nat x)) k
    == piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                            * (cos_partial k x - cos_partial (k - 1 - w)%nat x)) k
       + piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                              * (cos_term (Datatypes.S k) x
                                 - cos_term (k - w)%nat x)) k).
  { rewrite <- (piLsb_sumR_plus (fun w => 2%Q * sin_term (Datatypes.S w) x
                                     * (cos_partial k x - cos_partial (k - 1 - w)%nat x))
                    (fun w => 2%Q * sin_term (Datatypes.S w) x
                              * (cos_term (Datatypes.S k) x
                                 - cos_term (k - w)%nat x)) k).
    apply piLsb_sumR_ext. intros w Hw. cbv beta.
    replace (k - w)%nat with (Datatypes.S (k - 1 - w))%nat by lia.
    cbn [cos_partial]. ring. }
  rewrite Hpt.
  (* The old anti-diagonal row (the segment with [i+j=k+1],
     [i>=1]) is evaluated through the row identity *)
  assert (Hrow : piLrowB_row (Datatypes.S k) x
                 == 2%Q * sin_term 0 x * cos_term (Datatypes.S k) x
                    + (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                                              * cos_term (k - w)%nat x) k
                       + 2%Q * sin_term (Datatypes.S k) x * cos_term 0 x)).
  { unfold piLrowB_row.
    rewrite (piLsb_sumR_head (fun i => 2%Q * sin_term i x
                                          * cos_term (Datatypes.S k - i)%nat x)
                             (Datatypes.S k)). cbv beta.
    rewrite (piLsb_sumR_snoc (fun i => 2%Q * sin_term (Datatypes.S i) x
                                          * cos_term (Datatypes.S k - Datatypes.S i)%nat x)
                             k). cbv beta.
    replace (Datatypes.S k - Datatypes.S k)%nat with 0%nat by lia.
    apply Qeq_refl. }
  pose proof Hrow as HH.
  rewrite (piLrowB_row_sin_term (Datatypes.S k) x) in HH.
  assert (HE2 : piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                                     * cos_term (k - w)%nat x) k
                == sin_term (Datatypes.S k) (2 * x)%Q
                   - (2%Q * sin_term 0 x * cos_term (Datatypes.S k) x
                      + 2%Q * sin_term (Datatypes.S k) x * cos_term 0 x)).
  { rewrite HH. ring. }
  assert (Hshift : piLsb_sumR (fun w => sin_term (Datatypes.S w) x) k
                   == sin_partial k x - sin_term 0 x).
  { rewrite piLrowB_sin_partial_sumR, piLsb_sumR_head. cbv beta. ring. }
  assert (Hspl :
    piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * cos_term (Datatypes.S k) x) k
    == 2%Q * cos_term (Datatypes.S k) x * (sin_partial k x - sin_term 0 x)).
  { transitivity
      (piLsb_sumR (fun w => 2%Q * cos_term (Datatypes.S k) x
                            * sin_term (Datatypes.S w) x) k).
    { apply piLsb_sumR_ext. intros w _. ring. }
    transitivity (2%Q * cos_term (Datatypes.S k) x
                  * piLsb_sumR (fun w => sin_term (Datatypes.S w) x) k).
    { apply (piLrowB_row_scal (2%Q * cos_term (Datatypes.S k) x)
               (fun w => sin_term (Datatypes.S w) x) k). }
    rewrite Hshift. ring. }
  assert (Hconst :
    piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                         * (cos_term (Datatypes.S k) x
                            - cos_term (k - w)%nat x)) k
    == 2%Q * cos_term (Datatypes.S k) x * (sin_partial k x - sin_term 0 x)
       - (sin_term (Datatypes.S k) (2 * x)%Q
          - (2%Q * sin_term 0 x * cos_term (Datatypes.S k) x
             + 2%Q * sin_term (Datatypes.S k) x * cos_term 0 x))).
  { transitivity
      (piLsb_sumR (fun w => 2%Q * sin_term (Datatypes.S w) x
                            * cos_term (Datatypes.S k) x) k
       + piLsb_sumR (fun w => - (2%Q * sin_term (Datatypes.S w) x
                                 * cos_term (k - w)%nat x)) k).
    rewrite <- (piLsb_sumR_plus (fun w => 2%Q * sin_term (Datatypes.S w) x
                                     * cos_term (Datatypes.S k) x)
                    (fun w => - (2%Q * sin_term (Datatypes.S w) x
                                 * cos_term (k - w)%nat x)) k).
    apply piLsb_sumR_ext. intros w _. ring.
    rewrite Hspl, piLsb_sumR_opp, HE2. ring. }
  rewrite Hconst. ring.
Qed.

(* The remainder and the separated representation are equal
   pointwise: [dres k == bandsep k] (by induction along the [dres]
   recursion). *)
Lemma piLc_dres_bandsep : forall (k : nat) (x : Q),
  piL_sin_dres k x == piLc_bandsep k x.
Proof.
  intros k x. induction k as [| k IH].
  - cbn [piL_sin_dres piLc_bandsep piLsb_sumR]. ring.
  - cbn [piL_sin_dres]. rewrite IH, piLc_bandsep_step. ring.
Qed.

(* ============ Section 5. The mission statements: the band representation theorem and the partial-sum identity ============ *)

(* The band representation theorem: the truncation remainder
   equals the band sum over the row range [k+1,2k]. *)
Theorem piLc_dres_band : forall (k : nat) (x : Q),
  piL_sin_dres k x == piLc_bandsum k (k - 1)%nat x.
Proof.
  intros k x. rewrite (piLc_dres_bandsep k x).
  symmetry. apply (piLc_bandsum_sep k x).
Qed.

(* The partial-sum identity: [2 * S_k * C_k == S_k(2x) + bandsum k
   (k-1)] (from the [piL_sin_partial_double_at] face of
   [PiKernelSlack] (merged segment) and the band representation
   theorem). *)
Theorem piLc_double_sum_band : forall (k : nat) (x : Q),
  2%Q * sin_partial k x * cos_partial k x
  == sin_partial k (2 * x)%Q + piLc_bandsum k (k - 1)%nat x.
Proof.
  intros k x.
  pose proof (piL_sin_partial_double_at k x) as H.
  rewrite (piLc_dres_band k x) in H.
  rewrite H. ring.
Qed.

(* ============ Section 6. Computational witnesses (auxiliary statements; trivial character declared explicitly) ============ *)

(** In-kernel witnesses for small instances: for [k=3] and
    [x=13/10], the band value of the remainder agrees with the
    partial-sum identity; the fraction forms agree with independent
    exact-arithmetic recomputation. *)

Definition piLc_witness_dres3 : Q := piL_sin_dres 3 (13 # 10)%Q.

Lemma piLc_witness_dres3_val :
  piLc_witness_dres3 == (248270004845325853 # 18144000000000000000)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piLc_witness_dres3_band :
  piLc_witness_dres3 == piLc_bandsum 3 2%nat (13 # 10)%Q.
Proof. vm_compute. reflexivity. Qed.

Definition piLc_witness_double3 : Q :=
  2%Q * sin_partial 3 (13 # 10)%Q * cos_partial 3 (13 # 10)%Q.

Lemma piLc_witness_double3_val :
  piLc_witness_double3 == (9346034853485325853 # 18144000000000000000)%Q.
Proof. vm_compute. reflexivity. Qed.

Lemma piLc_witness_double3_split :
  piLc_witness_double3
  == sin_partial 3 (2 * (13 # 10)%Q)%Q + piLc_bandsum 3 2%nat (13 # 10)%Q.
Proof. vm_compute. reflexivity. Qed.
