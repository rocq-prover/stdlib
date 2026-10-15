(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Constructive [exp] and [sin] series with bounds over the rationals

    Mission.  Constructive [exp]/[sin] series and their bounds in [Q]
    rational arithmetic: the partial-sum series [exp_series], its
    one-step and chained monotonicity, the sin-derivative-form series
    [sc_sin_deriv_series], the nonnegativity of the series, the
    termwise domination of the series by the [exp] series, and the
    successor-step Lipschitz bound for the cosine partial sums.

    Dependencies.  [PiCompareT] (the [Id]-reflected forms [QleT'] and
    [QltT]); [PiKernelSlack] ([q_pow]/[q_fact], [cos_term]/
    [cos_partial], [sc_cos_term_diff], [q_le_div_le], [qeq_le],
    [Qle_plus_nonneg_r]); stdlib [QArith], [ZArith], [PeanoNat],
    [Lia], [Setoid], [Morphisms].

    References.  This development, [S03_QExp.v
    :292/:475/:489/:784/:791/:801], [S10_KVQuantTrig.v
    :1783/:1817/:2051/:2227], [S02_CauchyComplete.v :562]
    (statements and proofs transcribed verbatim from the source
    passages; the bridge statements such as [sc_cos_term_diff] are
    consumed under the same names from [PiKernelSlack]).

    Constructivity.  The statement level is entirely [Qle]/[QleT'],
    carried at the [Set] level; assumption-free and fully proved,
    with no non-constructive principles, and no external decision
    procedure closes a main statement; the two bookkeeping lemmas
    [Qle_0_1] and [Q2_nonneg] close by unfolding [Qle] to a linear
    integer cross-product decision (auxiliary bookkeeping lemmas).

    Build.  [rocq c -native-compiler no -q -Q . "" PiExpTrigSeries.v];
    the first eight bytes of the artifact are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia Setoid Morphisms.
Require Import PiCompareT.
Require Import PiKernelSlack.

(* ---- [Q] bookkeeping constants: [0 <= 1] and [0 <= 2] ---- *)

Lemma Qle_0_1 : Qle 0 1.
Proof.
  unfold Qle. simpl. lia.
Qed.

Lemma Q2_nonneg : Qle 0 (1 + 1)%Q.
Proof.
  unfold Qle. simpl. lia.
Qed.

(* ---- [0 <= A^m / m!] and its doubled form ---- *)

Lemma q_pow_fact_nonneg : forall A m, Qle 0 A -> Qle 0 (q_pow A m / q_fact m).
Proof.
  intros A m HA.
  apply (q_le_div_le 0 1 (q_pow A m) (q_fact m)).
  - unfold Qlt; simpl; lia.
  - apply q_fact_pos.
  - apply (Qle_trans _ 0 _).
    + apply qeq_le. ring.
    + apply (Qle_trans _ (q_pow A m) _).
      * apply q_pow_nonneg. exact HA.
      * apply qeq_le. ring.
Qed.

Lemma q_pow_fact2_nonneg : forall A m, Qle 0 A -> Qle 0 ((q_pow A m / q_fact m) * (1 + 1)%Q).
Proof.
  intros A m HA.
  exact (Qmult_le_compat_r 0 (q_pow A m / q_fact m) (1 + 1)%Q
  (q_pow_fact_nonneg A m HA) Q2_nonneg).
Qed.

(* ---- The [exp] series: [exp_series n B = sum of B^j / j! for j = 0..n] ---- *)

Fixpoint exp_series (n : nat) (B : Q) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => exp_series m B + q_pow B (Datatypes.S m) / q_fact (Datatypes.S m)
  end.

(* One-step monotonicity: [0 <= B] implies [exp_series n B <= exp_series (S n) B]
   (nonnegative terms). *)
Lemma exp_series_step_mono : forall (B : Q) (n : nat), Qle 0 B ->
  Qle (exp_series n B) (exp_series (Datatypes.S n) B).
Proof.
  intros B n HB. simpl.
  exact (Qle_plus_nonneg_r (exp_series n B)
  (q_pow B (Datatypes.S n) / q_fact (Datatypes.S n))
  (q_pow_fact_nonneg B (Datatypes.S n) HB)).
Qed.

(* Chained monotonicity: [n <= m] implies [exp_series n B <= exp_series m B]. *)
Lemma exp_series_mono : forall (B : Q) (n m : nat), Qle 0 B -> (n <= m)%nat ->
  Qle (exp_series n B) (exp_series m B).
Proof.
  intros B n m HB Hnm. induction Hnm as [| m' _ IHIH].
  - exact (Qle_refl (exp_series n B)).
  - exact (Qle_trans (exp_series n B) (exp_series m' B)
  (exp_series (Datatypes.S m') B) IHIH (exp_series_step_mono B m' HB)).
Qed.

(* ---- The sin-derivative-form series: [sc_sin_deriv_series n B =
       sum of B^{2j+1}/(2j+1)! for j <= n] ---- *)

Fixpoint sc_sin_deriv_series (n : nat) (B : Q) : Q :=
  match n with
  | 0%nat => q_pow B 1 / q_fact 1
  | Datatypes.S m => sc_sin_deriv_series m B +
                     q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))
  end.

(* Nonnegativity of the series (a sum of nonnegative terms). *)
Lemma sc_sin_deriv_series_nonneg : forall n B, QleT' 0 B -> Qle 0 (sc_sin_deriv_series n B).
Proof.
  intros n B HB. induction n as [| n IH]; simpl.
  - change (Qle 0 (q_pow B 1 / q_fact 1)).
    apply (q_pow_fact_nonneg B 1). exact (QleT'_to_Qle _ _ HB).
  - apply (Qle_trans _ (sc_sin_deriv_series n B) _).
    + exact IH.
    + apply (Qle_plus_nonneg_r (sc_sin_deriv_series n B)
             (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))))).
      apply q_pow_fact_nonneg. exact (QleT'_to_Qle _ _ HB).
Qed.

(* [sc_sin_deriv_series n B <= exp_series (S(2n)) B]: the odd-power terms form
   a sub-sum of the first 2n+1 terms of the [exp] series. *)
Lemma sc_sin_deriv_series_le_exp : forall n B, QleT' 0 B ->
  Qle (sc_sin_deriv_series n B) (exp_series (Datatypes.S (2 * n)) B).
Proof.
  intros n B HB.
  induction n as [| n IH].
  - (* n = 0: [B^1/1! <= exp_series 1 B = 1 + B^1/1!]. *)
    change (q_pow B 1 / q_fact 1 <= 1 + (q_pow B 1 / q_fact 1)).
    setoid_replace (1 + (q_pow B 1 / q_fact 1)) with ((q_pow B 1 / q_fact 1) + 1) by ring.
    apply Qle_plus_nonneg_r. apply Qle_0_1.
  - (* [sc_sin_deriv_series (S n)] = [sc_sin_deriv_series n] + [Y]
       ([Y := B^{S(S(S(2n)))}/(S(S(S(2n))))!], definitional);
       [exp_series (S(2(S n))) B] is [exp_series (S(S(S(2n)))) B]
       = [exp_series (S(S(2n))) + Y], and
       [exp_series (S(S(2n))) = exp_series (S(2n)) + U']. *)
    change (sc_sin_deriv_series n B +
            (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))) <=
            exp_series (Datatypes.S (2 * Datatypes.S n)) B).
    replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    apply (Qle_trans _ (exp_series (Datatypes.S (2 * n)) B +
                         (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))))) _).
    + apply Qplus_le_compat; [exact IH | apply Qle_refl].
    + change (exp_series (Datatypes.S (2 * n)) B +
              (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))) <=
              exp_series (Datatypes.S (Datatypes.S (2 * n))) B +
              (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))))).
      apply Qplus_le_compat.
      * apply exp_series_step_mono. exact (QleT'_to_Qle _ _ HB).
      * apply Qle_refl.
Qed.

(* Lipschitz bound for the cosine partial sums (successor-step form):
   [|cos_partial (S n) x - cos_partial (S n) y| <=
    |x - y| * sc_sin_deriv_series n B]. *)
Lemma sc_cos_partial_lipschitz_succ : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  Qle (Qabs (cos_partial (Datatypes.S n) x - cos_partial (Datatypes.S n) y))
      (Qmult (Qabs (x - y)) (sc_sin_deriv_series n B)).
Proof.
  intros x y B n HB Hx Hy.
  induction n as [| n IH].
  - (* n = 0: the [cos_partial 1] difference equals the [cos_term 1]
       difference; [sc_sin_deriv_series 0 = B^1/1!]. *)
    assert (Hd : cos_partial 1 x - cos_partial 1 y == cos_term 1 x - cos_term 1 y).
    { change (cos_term 0 x + cos_term 1 x - (cos_term 0 y + cos_term 1 y) ==
              cos_term 1 x - cos_term 1 y).
      assert (Hc0x : cos_term 0 x == 1).
      { unfold cos_term. reflexivity. }
      assert (Hc0y : cos_term 0 y == 1).
      { unfold cos_term. reflexivity. }
      rewrite Hc0x. rewrite Hc0y. ring. }
    apply (Qle_trans _ (Qabs (cos_term 1 x - cos_term 1 y)) _).
    + apply qeq_le. apply (Qabs_wd (cos_partial 1 x - cos_partial 1 y) (cos_term 1 x - cos_term 1 y)). exact Hd.
    + apply (Qle_trans _ (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (2 * 0)) / q_fact (Datatypes.S (2 * 0)))) _).
      * apply (sc_cos_term_diff x y B 0);
          [ exact (QleT'_to_Qle _ _ HB)
          | exact (QleT'_to_Qle _ _ Hx)
          | exact (QleT'_to_Qle _ _ Hy) ].
      * apply qeq_le. reflexivity.
  - (* Step: the [S(S n)] difference splits as the [S n] difference plus the
       [S(S n)] term difference; [sc_sin_deriv_series (S n)] =
       [sc_sin_deriv_series n] + [B^{S(S(S(2n)))}/(S(S(S(2n))))!]. *)
    assert (Hsplit : cos_partial (Datatypes.S (Datatypes.S n)) x - cos_partial (Datatypes.S (Datatypes.S n)) y ==
                     (cos_partial (Datatypes.S n) x - cos_partial (Datatypes.S n) y) +
                     (cos_term (Datatypes.S (Datatypes.S n)) x - cos_term (Datatypes.S (Datatypes.S n)) y)).
    { change (cos_partial (Datatypes.S n) x + cos_term (Datatypes.S (Datatypes.S n)) x -
              (cos_partial (Datatypes.S n) y + cos_term (Datatypes.S (Datatypes.S n)) y) ==
              (cos_partial (Datatypes.S n) x - cos_partial (Datatypes.S n) y) +
              (cos_term (Datatypes.S (Datatypes.S n)) x - cos_term (Datatypes.S (Datatypes.S n)) y)).
      ring. }
    rewrite Hsplit.
    apply (Qle_trans _ (Qabs (cos_partial (Datatypes.S n) x - cos_partial (Datatypes.S n) y) +
                         Qabs (cos_term (Datatypes.S (Datatypes.S n)) x - cos_term (Datatypes.S (Datatypes.S n)) y)) _).
    + apply Qabs_triangle.
    + (* Term-bound reshaping: [sc_cos_term_diff (S n)] gives
         [B^{S(2(S n))}/(S(2(S n)))!], rewritten into the [S(S(S(2n)))]
         form. *)
      assert (Hterm : Qle (Qabs (cos_term (Datatypes.S (Datatypes.S n)) x - cos_term (Datatypes.S (Datatypes.S n)) y))
                          (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))))).
      { apply (Qle_trans _ (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (2 * Datatypes.S n)) / q_fact (Datatypes.S (2 * Datatypes.S n)))) _).
        - apply (sc_cos_term_diff x y B (Datatypes.S n));
            [ exact (QleT'_to_Qle _ _ HB)
            | exact (QleT'_to_Qle _ _ Hx)
            | exact (QleT'_to_Qle _ _ Hy) ].
        - apply qeq_le. replace (2 * Datatypes.S n)%nat with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia. reflexivity. }
      apply (Qle_trans _ (Qplus (Qmult (Qabs (x - y)) (sc_sin_deriv_series n B))
                                  (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))))) _).
      * apply Qplus_le_compat.
        -- exact IH.
        -- exact Hterm.
      * apply qeq_le.
        change (sc_sin_deriv_series (Datatypes.S n) B)
          with (sc_sin_deriv_series n B + q_pow B (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))).
        ring.
Qed.
