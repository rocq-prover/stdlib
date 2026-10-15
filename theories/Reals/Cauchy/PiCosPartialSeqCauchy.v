(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Order-Cauchy property of the cosine partial-sum sequence at a
    fixed point

    Mission.  The order-Cauchy property of the cosine partial-sum
    sequence at the fixed point [z_m]: for every [m : nat] and
    tolerance [dt > 0] there is a [K : nat] such that every [k >= K]
    satisfies [|P_k(z_m) - P_K(z_m)| < dt], where [z_m] is the cosine
    zero-localization sequence ([PiCosZeroSeqProbe.cos_zero_seq]) and
    [P_k = cos_partial] ([PiKernelSlack]).  The proof composes tail
    bounds directly: the tail bound
    [|P_k(x) - P_M(x)| <= (3/2) * t_{M+1}] for [0 <= x <= 2] and
    [2 <= M <= k] ([PiCosTailScan.vt_cos_partial_tail_bound]); the
    step-wise decay [t_{M+i} <= (1/3)^i * t_M] ([vt_abs_term_decay]);
    the base monotonicity [(1/3)^n <= (1/2)^n]
    ([PiCosApproxRoot.vt_q_pow_base_mono]); and the half-power
    Archimedean property [D * (1/2)^n < dt] ([vt_pow_half_arch]).
    Note: [z_m] is a rational localization point, not an exact zero of
    cosine, so the direct fixed-point statement [|P_k(z_m)| -> 0] is
    false; the order-Cauchy property stated here is its provable
    substitute form.

    Dependencies.  Stdlib [QArith] ([QArith]/[Qabs]/[Qfield]),
    [ZArith.ZArith], [Arith.PeanoNat], [Lia], [Setoid], [Morphisms];
    [PiKernelSlack]; [QCauchyZeroCos]; [PiCosTailScan];
    [PiVertexPolyDiff]; [PiCosApproxRoot]; [PiCosZeroSeqProbe];
    [PiCosZeroSeqConv].

    References.  [S10_KVQuantTrig.v :8296] ([cos_seq_cauchy]) is the
    adjacent statement: the Cauchy property of the zero-localization
    sequence [(z_n)_n] itself.  This file proves the Cauchy property
    of the partial-sum sequence [(P_k(z_m))_k] at the fixed point
    [z_m]; the two are orthogonal and complementary.

    Constructivity.  Statements carried at the [Set] level (a [sig]
    witness [K : nat]); the premise-consumption sites all sit at
    [Qlt]/[Qle] goal positions, with no [Set] elimination;
    assumption-free and fully proved, with no non-constructive
    principles (the closing [Print Assumptions] line reports closed).

    Build.  [rocq c -native-compiler no -q -Q . ""
    PiCosPartialSeqCauchy.v]; the first eight bytes of the artifact
    are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid Morphisms.
Require Import PiKernelSlack.
Require Import QCauchyZeroCos.
Require Import PiCosTailScan.
Require Import PiVertexPolyDiff.
Require Import PiCosApproxRoot.
Require Import PiCosZeroSeqProbe.
Require Import PiCosZeroSeqConv.

(* Order-Cauchy property: the partial-sum sequence at the fixed point
   [z_m] is a Cauchy sequence.  Choice of the witness [K]: [K := n + 2],
   where [n] is given by the half-power Archimedean witness at
   [D = (3/2) * t_3].  For [k >= K] the tail bound gives
   [|P_k(z_m) - P_K(z_m)| <= (3/2) * t_{K+1}], while
   [t_{K+1} = t_{3+n} <= (1/3)^n * t_3 <= (1/2)^n * t_3], so the tail
   amount [(3/2) * t_{K+1} <= D * (1/2)^n < dt]. *)
Lemma cos_partial_seq_cauchy : forall (m : nat) (dt : Q), Qlt 0 dt ->
  { K : nat | forall k : nat, (K <= k)%nat ->
      Qlt (Qabs (cos_partial k (cos_zero_seq m) - cos_partial K (cos_zero_seq m))) dt }.
Proof.
  intros m dt Hdt.
  assert (Hz0 : Qle 0 (cos_zero_seq m)) by apply cos_zero_nonneg.
  assert (Hz2 : Qle (cos_zero_seq m) 2) by apply cos_zero_le_two.
  assert (H032 : Qle 0 (3#2)%Q) by (unfold Qle; simpl; lia).
  assert (H0T3 : Qle 0 (cos_abs_term (cos_zero_seq m) 3))
    by (apply (vt_abs_term_nonneg _ _ Hz0)).
  assert (HD : Qle 0 ((3#2)%Q * cos_abs_term (cos_zero_seq m) 3))
    by (apply Qmult_le_0_compat; assumption).
  destruct (vt_pow_half_arch ((3#2)%Q * cos_abs_term (cos_zero_seq m) 3) dt HD Hdt)
    as [n Hn].
  exists ((n + 2)%nat).
  intros k Hk.
  assert (Hk2 : (2 <= n + 2)%nat) by lia.
  assert (Hdec : Qle (cos_abs_term (cos_zero_seq m) (Datatypes.S (n + 2)))
                     (q_pow (1#3) n * cos_abs_term (cos_zero_seq m) 3)).
  { replace (Datatypes.S (n + 2)) with (3 + n)%nat by lia.
    apply (vt_abs_term_decay (cos_zero_seq m) 3 n);
      [exact Hz0 | exact Hz2 | lia]. }
  assert (Hbr : Qle (q_pow (1#3) n) (q_pow (1#2) n))
    by (apply (vt_q_pow_base_mono (1#3) (1#2) n); unfold Qle; simpl; lia).
  assert (Hsbr : Qle ((3#2)%Q * q_pow (1#3) n) ((3#2)%Q * q_pow (1#2) n))
    by (apply (sc_qmult_le_l (q_pow (1#3) n) (q_pow (1#2) n) (3#2)%Q Hbr H032)).
  assert (Hmain : Qle ((3#2)%Q * cos_abs_term (cos_zero_seq m) (Datatypes.S (n + 2)))
                      (((3#2)%Q * cos_abs_term (cos_zero_seq m) 3) * q_pow (1#2) n)).
  { apply (Qle_trans _ ((3#2)%Q * (q_pow (1#3) n * cos_abs_term (cos_zero_seq m) 3))).
    - exact (sc_qmult_le_l (cos_abs_term (cos_zero_seq m) (Datatypes.S (n + 2)))
                           (q_pow (1#3) n * cos_abs_term (cos_zero_seq m) 3)
                           (3#2)%Q Hdec H032).
    - apply (Qle_trans _ (((3#2)%Q * q_pow (1#3) n) * cos_abs_term (cos_zero_seq m) 3)).
      + apply qeq_le. ring.
      + apply (Qle_trans _ (((3#2)%Q * q_pow (1#2) n) * cos_abs_term (cos_zero_seq m) 3)).
        * exact (Qmult_le_compat_r _ _ _ Hsbr H0T3).
        * apply qeq_le. ring. }
  apply (Qle_lt_trans
           (Qabs (cos_partial k (cos_zero_seq m) - cos_partial (n + 2) (cos_zero_seq m)))
           ((3#2)%Q * cos_abs_term (cos_zero_seq m) (Datatypes.S (n + 2))) dt).
  - exact (vt_cos_partial_tail_bound (cos_zero_seq m) (n + 2) k Hz0 Hz2 Hk2 Hk).
  - apply (Qle_lt_trans _ (((3#2)%Q * cos_abs_term (cos_zero_seq m) 3) * q_pow (1#2) n) dt).
    + exact Hmain.
    + exact Hn.
Qed.

(* Assumption audit for the mission statement of this file. *)
Print Assumptions cos_partial_seq_cauchy.
