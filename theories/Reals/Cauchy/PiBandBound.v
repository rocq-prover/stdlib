(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** * PiBandBound.v: band bound of the sin truncation remainder

    Mission.  The absolute-value upper bound and the monotonicity of
    the offset band [k+1,2k] of the truncation remainder
    [piL_sin_dres] -- the band row controlling term
    [t_m(B) = (2B)^(2m+1)/(2m+1)!] and the band-sum bound
    [band_bound k B = sum_{u<k} t_{k+1+u}].  Three items:
    (1) row majorants: [|bandrow k m x| <= t_m(B)] for [k < m]
    (carried by the full-row binomial closed form
    [sum_{i<=m} 1/((2i+1)!(2m-2i)!) == 2^(2m)/(2m+1)!]);
    (2) the main band bound: [|dres k x| <= band_bound k B];
    (3) monotonicity and truncation-length selection: [band_bound] is
    nonincreasing for [2*ceil(B) < k1 <= k2] (carried by the
    quarter-step descent and the geometric tail bound), and a
    truncation length [j] is given in [sigT] witness form such that
    [band_bound k B < eps] whenever [k >= j].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [QArith.Qround], [ZArith.ZArith], [Arith.PeanoNat], [Lia];
    [PiKernelSlack] ([q_pow]/[q_fact], [sin_term]/[cos_term],
    [QleT'_to_Qle], [Qle_div_same_denom], [q_neq_of_lt]);
    [PiPascalMachine] (the [piLsb_sumR] row-sum machine with its
    [ext]/[snoc]/[head] lemmas, [piLsb_row_odd], [piLsb_bpa_bridge]);
    [PiRowIdentity] ([piLrowB_qfact_neq0], [piLrowB_qeq_cancel_l]);
    [PiPascalResidue] (the offset-band representation
    [piLc_bandrow]/[piLc_bandsum]/[piLc_dres_band]);
    [PiKernelSlack_D1_identity] ([piL_sin_dres]);
    [PiKernelSlack_D2_remainder] (term-level absolute-value bounds);
    [PiKernelSlack_D3_prereq] (the witness lemma [d3p_quarter_pow_lt],
    [d3p_inject_ceiling_ge]).

    References.  Row-by-row controlling terms and the geometric tail
    bound for the offset band of an alternating series (the
    quarter-step descent and the identity
    [sum_{i<n}(1/4)^i + (4/3)(1/4)^n == 4/3]); full-row binomial
    closed-form identities (the odd half-sum of the Pascal row
    [sum_{i<=m} C(2m+1,2i+1) == 2^(2m)]).

    Constructivity.  Statements live entirely on the stdlib
    [Qeq]/[Qle]/[Qlt]; zero axioms, no abandoned proofs, no
    classical logic; induction with explicit algebraic chains and
    zero solvers on the [Q] side ([Lia] only for auxiliary [nat]
    arithmetic); definitions are transparent and extractable.

    Build.  [coqc -native-compiler no -q -Q . "" PiBandBound.v]
    WARNING: this file is experimental and likely to change in future releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.
Require Import PiPascalMachine.
Require Import PiRowIdentity.
Require Import PiPascalResidue.

(* ============ Section 1. Carrying definitions ============ *)

(** The band row controlling term: [t_m(B) = (2B)^(2m+1)/(2m+1)!]. *)
Definition piLd_t_term (m : nat) (B : Q) : Q :=
  q_pow (2 * B) (Datatypes.S (2 * m))%nat / q_fact (Datatypes.S (2 * m))%nat.

(** The band-sum bound: [band_bound k B = sum_{u<k} t_{k+1+u}(B)] over the row range [k+1, 2k]; for [k = 0] the empty sum is [0], aligned with [dres 0 = 0]. *)
Definition piLd_band_bound (k : nat) (B : Q) : Q :=
  piLsb_sumR (fun u => piLd_t_term (Datatypes.S (k + u))%nat B) k.

(* ============ Section 2. Row-sum machine supplements ============ *)

Lemma piLd_sumR_scal : forall (f : nat -> Q) (c : Q) (n : nat),
  piLsb_sumR (fun i => f i * c) n == piLsb_sumR f n * c.
Proof.
  intros f c n. induction n as [| n IH].
  - reflexivity.
  - cbn [piLsb_sumR]. rewrite IH. ring.
Qed.

Lemma piLd_sumR_nonneg : forall (f : nat -> Q) (n : nat),
  (forall i : nat, (i < n)%nat -> Qle 0 (f i)) -> Qle 0 (piLsb_sumR f n).
Proof.
  intros f n. induction n as [| n IH]; intros Hf.
  - apply Qle_refl.
  - cbn [piLsb_sumR].
    apply (Qplus_le_compat 0%Q (piLsb_sumR f n) 0%Q (f n)).
    + apply IH. intros i Hi. apply Hf.
      apply (Nat.lt_trans _ n _ Hi). apply Nat.lt_succ_diag_r.
    + apply Hf. apply Nat.lt_succ_diag_r.
Qed.

Lemma piLd_sumR_le : forall (f g : nat -> Q) (n : nat),
  (forall i : nat, (i < n)%nat -> Qle (f i) (g i)) ->
  Qle (piLsb_sumR f n) (piLsb_sumR g n).
Proof.
  intros f g n. induction n as [| n IH]; intros Hf.
  - apply Qle_refl.
  - cbn [piLsb_sumR].
    apply (Qplus_le_compat (piLsb_sumR f n) (piLsb_sumR g n) (f n) (g n)).
    + apply IH. intros i Hi. apply Hf.
      apply (Nat.lt_trans _ n _ Hi). apply Nat.lt_succ_diag_r.
    + apply Hf. apply Nat.lt_succ_diag_r.
Qed.

Lemma piLd_abs_sumR_le : forall (f : nat -> Q) (n : nat),
  Qle (Qabs (piLsb_sumR f n)) (piLsb_sumR (fun i => Qabs (f i)) n).
Proof.
  intros f n. induction n as [| n IH].
  - cbn [piLsb_sumR]. apply Qle_refl.
  - cbn [piLsb_sumR].
    apply (Qle_trans _ (Qabs (piLsb_sumR f n) + Qabs (f n))).
    + apply Qabs_triangle.
    + apply (Qplus_le_compat (Qabs (piLsb_sumR f n))
               (piLsb_sumR (fun i => Qabs (f i)) n) (Qabs (f n)) (Qabs (f n))).
      * exact IH.
      * apply Qle_refl.
Qed.

Lemma piLd_sumR_split : forall (f : nat -> Q) (a p : nat),
  piLsb_sumR f (a + p)%nat
  == piLsb_sumR f a + piLsb_sumR (fun i => f (a + i)%nat) p.
Proof.
  intros f a p. induction p as [| p IH].
  - rewrite Nat.add_0_r. cbn [piLsb_sumR]. ring.
  - replace (a + Datatypes.S p)%nat with (Datatypes.S (a + p))%nat by lia.
    cbn [piLsb_sumR]. rewrite IH. ring.
Qed.

(* ============ Section 3. Auxiliary arithmetic lemmas ============ *)

Lemma piLd_qmult_le_l : forall (z x y : Q),
  Qle 0 z -> Qle x y -> Qle (z * x) (z * y).
Proof.
  intros z x y Hz Hxy.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply (Qmult_le_compat_r x y z Hxy Hz).
Qed.

Lemma piLd_qmult_nonneg_r : forall x y : Q,
  Qle 0 x -> Qle 0 y -> Qle 0 (x * y).
Proof.
  intros x y Hx Hy. apply (Qle_trans _ (0 * y)%Q).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply (Qmult_le_compat_r 0 x y Hx Hy).
Qed.

Lemma piLd_qle_sub_r : forall a x : Q, Qle 0 x -> Qle (a - x) a.
Proof.
  intros a x Hx.
  apply (Qle_trans _ ((a - x) + x)%Q).
  - apply (Qle_trans (a - x) ((a - x) + 0)%Q ((a - x) + x)%Q).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (Qplus_le_compat (a - x) (a - x) 0%Q x); [apply Qle_refl | exact Hx].
  - assert (Heq : (a - x) + x == a + 0) by ring.
    rewrite Heq, Qplus_0_r. apply Qle_refl.
Qed.

Lemma piLd_qle_sub_l : forall a x y : Q, Qle y x -> Qle (a - x) (a - y).
Proof.
  intros a x y Hyx.
  assert (Hxy0 : Qle 0 (x - y)%Q).
  { pose proof (Qplus_le_compat y x (- y) (- y) Hyx (Qle_refl (- y))) as H.
    rewrite Qplus_opp_r in H. exact H. }
  apply (Qle_trans _ ((a - x) + (x - y))%Q).
  - apply (Qle_trans (a - x) ((a - x) + 0)%Q ((a - x) + (x - y))%Q).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (Qplus_le_compat (a - x) (a - x) 0%Q (x - y)); [apply Qle_refl | exact Hxy0].
  - assert (Heq : (a - x) + (x - y) == a - y) by ring.
    rewrite Heq. apply Qle_refl.
Qed.

Lemma piLd_sumR_prefix_le : forall (f : nat -> Q) (p q : nat),
  (p <= q)%nat -> (forall i : nat, Qle 0 (f i)) ->
  Qle (piLsb_sumR f p) (piLsb_sumR f q).
Proof.
  intros f p q Hle. induction Hle as [| q Hle IH]; intros Hf.
  - apply Qle_refl.
  - apply (Qle_trans _ (piLsb_sumR f q)).
    + apply IH. exact Hf.
    + cbn [piLsb_sumR].
      apply (Qle_trans _ (piLsb_sumR f q + 0%Q)%Q).
      * rewrite Qplus_0_r. apply Qle_refl.
      * apply (Qplus_le_compat (piLsb_sumR f q) (piLsb_sumR f q) 0%Q (f q));
          [apply Qle_refl | apply Hf].
Qed.

Lemma piLd_shift_sum_le : forall (h : nat -> Q) (a p n : nat),
  (forall i : nat, Qle 0 (h i)) ->
  (a + p <= n)%nat ->
  Qle (piLsb_sumR (fun u => h (a + u)%nat) p) (piLsb_sumR h (Datatypes.S n)).
Proof.
  intros h a p n Hh Hle.
  apply (Qle_trans _ (piLsb_sumR h (a + p)%nat)).
  - rewrite (piLd_sumR_split h a p).
    apply (Qle_trans _ (0%Q + piLsb_sumR (fun u => h (a + u)%nat) p)%Q).
    + rewrite Qplus_0_l. apply Qle_refl.
    + apply (Qplus_le_compat 0%Q (piLsb_sumR h a)
               (piLsb_sumR (fun u => h (a + u)%nat) p)
               (piLsb_sumR (fun u => h (a + u)%nat) p)).
      * apply piLd_sumR_nonneg. intros i _. apply Hh.
      * apply Qle_refl.
  - apply (Qle_trans _ (piLsb_sumR h n)).
    + apply piLd_sumR_prefix_le; [lia | exact Hh].
    + apply piLd_sumR_prefix_le; [apply Nat.le_succ_diag_r | exact Hh].
Qed.

Lemma piLd_inject_le : forall a b : nat, (a <= b)%nat ->
  Qle (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b H. unfold Qle; cbn [Qnum Qden]; rewrite !Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_le a b)). exact H.
Qed.

Lemma piLd_inject_pos : forall n : nat, Qlt 0 (Z.of_nat (Datatypes.S n) # 1).
Proof.
  intros n. unfold Qlt; cbn [Qnum Qden]; rewrite !Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S n))). apply Nat.lt_0_succ.
Qed.

Lemma piLd_inject_neq0 : forall n : nat,
  ~ (Z.of_nat (Datatypes.S n) # 1 == 0)%Q.
Proof.
  intros n H.
  exact (Qlt_not_eq 0 (Z.of_nat (Datatypes.S n) # 1) (piLd_inject_pos n)
           (Qeq_sym (Z.of_nat (Datatypes.S n) # 1) 0%Q H)).
Qed.

Lemma piLd_inject_nonneg : forall n : nat, Qle 0 (Z.of_nat n # 1).
Proof.
  intros n. apply (Qle_trans 0 (Z.of_nat 0 # 1) (Z.of_nat n # 1)).
  - apply Qle_refl.
  - apply piLd_inject_le. apply Nat.le_0_l.
Qed.

Lemma piLd_qfact_pair_neq0 : forall i j : nat,
  ~ (q_fact i * q_fact j == 0)%Q.
Proof.
  intros i j H.
  exact (q_neq_of_lt (q_fact i * q_fact j)
           (Qmult_lt_0_compat (q_fact i) (q_fact j) (q_fact_pos i) (q_fact_pos j)) H).
Qed.

Lemma piLd_qinv_distr : forall a d : Q,
  ~ (a == 0)%Q -> ~ (d == 0)%Q -> / a * / d == / (a * d)%Q.
Proof.
  intros a d Ha Hd.
  assert (Had : ~ ((a * d)%Q == 0)).
  { intro H0. apply Ha.
    apply (piLrowB_qeq_cancel_l a 0%Q d Hd).
    rewrite H0. symmetry. apply Qmult_0_l. }
  apply (piLrowB_qeq_cancel_l (/ a * / d) (/ (a * d)) (a * d) Had).
  assert (Hkey : (/ a * / d) * (a * d) == 1%Q).
  { assert (Hr : (/ a * / d) * (a * d) == (a * / a) * (d * / d)) by ring.
    rewrite Hr, (Qmult_inv_r a Ha), (Qmult_inv_r d Hd). reflexivity. }
  rewrite Hkey, (Qmult_comm (/ (a * d)) (a * d)).
  symmetry. apply (Qmult_inv_r (a * d) Had).
Qed.

Lemma piLd_q_pow_pos : forall (x : Q) (n : nat), Qlt 0 x -> Qlt 0 (q_pow x n).
Proof.
  intros x n Hx. induction n as [| n IH].
  - unfold Qlt; cbn [q_pow Qnum Qden]. lia.
  - rewrite q_pow_succ. apply Qmult_lt_0_compat; [exact Hx | exact IH].
Qed.

Lemma piLd_q_pow_one : forall n : nat, q_pow 1%Q n == 1%Q.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite q_pow_succ, IH. apply Qmult_1_l.
Qed.

Lemma piLd_q_fact_ge1 : forall n : nat, Qle 1%Q (q_fact n).
Proof.
  induction n as [| n IH].
  - apply Qle_refl.
  - rewrite q_fact_succ.
    assert (Hsn : Qle 1 (Z.of_nat (Datatypes.S n) # 1)).
    { apply (Qle_trans 1 (Z.of_nat 1 # 1) (Z.of_nat (Datatypes.S n) # 1)).
      - apply Qle_refl.
      - apply piLd_inject_le. lia. }
    apply (Qmult_le_compat_nonneg 1%Q (Z.of_nat (Datatypes.S n) # 1)
             1%Q (q_fact n)).
    + split; [unfold Qle; cbn [Qnum Qden]; lia | exact Hsn].
    + split; [unfold Qle; cbn [Qnum Qden]; lia | exact IH].
Qed.

Lemma piLd_t_term_nonneg : forall (B : Q) (j : nat),
  Qle 0 B -> Qle 0 (piLd_t_term j B).
Proof.
  intros B j H0B. unfold piLd_t_term.
  assert (H02 : Qle 0 2%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (H02B : Qle 0 (2 * B)) by (apply piLd_qmult_nonneg_r; [exact H02 | exact H0B]).
  apply (Qle_trans _ ((0 * / q_fact (Datatypes.S (2 * j))%nat)%Q)).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply (Qmult_le_compat_nonneg 0%Q (q_pow (2 * B) (Datatypes.S (2 * j)))
             (/ q_fact (Datatypes.S (2 * j))%Q) (/ q_fact (Datatypes.S (2 * j))%Q)).
    + split; [apply Qle_refl | apply q_pow_nonneg; exact H02B].
    + split; [apply (Qlt_le_weak 0 _); apply Qinv_lt_0_compat; apply q_fact_pos
              | apply Qle_refl].
Qed.

(* ============ Section 4. Term-level absolute-value bounds (Group D support) ============ *)

(** Absolute-value bound at the cross-multiplication points: [|2 s_j x c_{mm-j} x| <= 2·B^{2j+1}/(2j+1)!·B^{2(mm-j)}/(2(mm-j))!]. *)
Lemma piLd_point_term_le : forall (mm j : nat) (x B : Q), Qle (Qabs x) B ->
  Qle (Qabs (2%Q * sin_term j x * cos_term (mm - j)%nat x))
      (2%Q * (q_pow B (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))
           * (q_pow B (2 * (mm - j)) / q_fact (2 * (mm - j)))).
Proof.
  intros mm j x B Hx.
  assert (H02 : Qle 0 2%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (H0B : Qle 0 B)
    by (apply (Qle_trans 0 (Qabs x) B); [apply Qabs_nonneg | exact Hx]).
  assert (H02B : Qle 0 (2 * B))
    by (apply piLd_qmult_nonneg_r; [exact H02 | exact H0B]).
  pose proof (QleT'_to_Qle _ _
             (piL_sin_term_abs_bound j x B (Qle_to_QleT' (Qabs x) B Hx))) as Hs.
  pose proof (QleT'_to_Qle _ _
             (piL_cos_term_abs_bound (mm - j)%nat x B
                (Qle_to_QleT' (Qabs x) B Hx))) as Hc.
  rewrite (Qabs_Qmult (2%Q * sin_term j x) (cos_term (mm - j)%nat x)).
  rewrite (Qabs_Qmult 2%Q (sin_term j x)).
  assert (Ha2 : Qabs 2%Q == 2%Q) by reflexivity.
  rewrite Ha2.
  apply (Qle_trans _
           (2%Q * (q_pow B (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))
              * Qabs (cos_term (mm - j)%nat x))).
  - apply (Qmult_le_compat_r (2%Q * Qabs (sin_term j x))
             (2%Q * (q_pow B (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))))
             (Qabs (cos_term (mm - j)%nat x))).
    + apply piLd_qmult_le_l; [exact H02 | exact Hs].
    + apply Qabs_nonneg.
  - apply piLd_qmult_le_l.
    + apply piLd_qmult_nonneg_r.
      * exact H02.
      * apply (Qle_trans _ ((0 * / q_fact (Datatypes.S (2 * j)))%Q)).
        -- rewrite Qmult_0_l. apply Qle_refl.
        -- apply (Qmult_le_compat_nonneg 0%Q (q_pow B (Datatypes.S (2 * j)))
                    (/ q_fact (Datatypes.S (2 * j))%Q)
                    (/ q_fact (Datatypes.S (2 * j))%Q)).
           ++ split; [apply Qle_refl | apply q_pow_nonneg; exact H0B].
           ++ split;
                [apply (Qlt_le_weak 0 _); apply Qinv_lt_0_compat; apply q_fact_pos
                | apply Qle_refl].
    + exact Hc.
Qed.

(* ============ Section 5. Row majorants (Group D) ============ *)

(** Pointwise reshaping: [1/(F1·F2) == C(S(2m),S(2i))/F(S(2m))] (pointwise denominator cancellation along the binomial-factorial bridge). *)
Lemma piLd_point_binom_div : forall (m i : nat), (i <= m)%nat ->
  1 / (q_fact (Datatypes.S (2 * i))%nat * q_fact (2 * (m - i))%nat)
  == bpa_binom (Datatypes.S (2 * m))%nat (Datatypes.S (2 * i))%nat
     / q_fact (Datatypes.S (2 * m))%nat.
Proof.
  intros m i Hle.
  assert (Hb : bpa_binom (Datatypes.S (2 * m))%nat (Datatypes.S (2 * i))%nat
               * q_fact (Datatypes.S (2 * i))%nat
               * q_fact (2 * (m - i))%nat
               == q_fact (Datatypes.S (2 * m))%nat).
  { replace (2 * (m - i))%nat
      with (Datatypes.S (2 * m) - Datatypes.S (2 * i))%nat by lia.
    apply piLsb_bpa_bridge. lia. }
  assert (HneD : ~ (q_fact (Datatypes.S (2 * i))%nat * q_fact (2 * (m - i))%nat == 0)%Q)
    by (apply piLd_qfact_pair_neq0).
  assert (HneF : ~ (q_fact (Datatypes.S (2 * m))%nat == 0)%Q)
    by (apply piLrowB_qfact_neq0).
  unfold Qdiv.
  assert (HkeyL : bpa_binom (Datatypes.S (2 * m))%nat (Datatypes.S (2 * i))%nat
                  * / q_fact (Datatypes.S (2 * m))%nat
                  * (q_fact (Datatypes.S (2 * i))%nat * q_fact (2 * (m - i))%nat)
                  == 1%Q).
  { assert (Hz : bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i))
                   * / q_fact (Datatypes.S (2 * m))
                   * (q_fact (Datatypes.S (2 * i)) * q_fact (2 * (m - i)))
                   == bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i))
                      * q_fact (Datatypes.S (2 * i)) * q_fact (2 * (m - i))
                      * / q_fact (Datatypes.S (2 * m))) by ring.
    rewrite Hz, Hb, (Qmult_inv_r (q_fact (Datatypes.S (2 * m))) HneF).
    reflexivity. }
  assert (HkeyR : 1%Q * / (q_fact (Datatypes.S (2 * i))%nat * q_fact (2 * (m - i))%nat)
                  * (q_fact (Datatypes.S (2 * i))%nat * q_fact (2 * (m - i))%nat)
                  == 1%Q).
  { assert (Hz : 1%Q * / (q_fact (Datatypes.S (2 * i)) * q_fact (2 * (m - i)))
                 * (q_fact (Datatypes.S (2 * i)) * q_fact (2 * (m - i)))
                 == (q_fact (Datatypes.S (2 * i)) * q_fact (2 * (m - i)))
                    * / (q_fact (Datatypes.S (2 * i)) * q_fact (2 * (m - i)))) by ring.
    rewrite Hz. apply Qmult_inv_r. exact HneD. }
  apply (piLrowB_qeq_cancel_l
           (1%Q * / (q_fact (Datatypes.S (2 * i))%nat * q_fact (2 * (m - i))%nat))
           (bpa_binom (Datatypes.S (2 * m))%nat (Datatypes.S (2 * i))%nat
            * / q_fact (Datatypes.S (2 * m))%nat)
           (q_fact (Datatypes.S (2 * i))%nat * q_fact (2 * (m - i))%nat) HneD).
  rewrite HkeyR, HkeyL. reflexivity.
Qed.

(** Full-row binomial closed form: [sum_{i<=m} 1/((2i+1)!(2m-2i)!) == 2^(2m)/(2m+1)!]. *)
Lemma piLd_row_binom_full : forall m : nat,
  piLsb_sumR
    (fun i => 1 / (q_fact (Datatypes.S (2 * i))%nat * q_fact (2 * (m - i))%nat))
    (Datatypes.S m)
  == q_pow 2%Q (2 * m)%nat / q_fact (Datatypes.S (2 * m))%nat.
Proof.
  intros m.
  assert (Hext : piLsb_sumR
    (fun i => 1 / (q_fact (Datatypes.S (2 * i))%nat * q_fact (2 * (m - i))%nat))
    (Datatypes.S m)
    == piLsb_sumR
    (fun i => bpa_binom (Datatypes.S (2 * m))%nat (Datatypes.S (2 * i))%nat
       / q_fact (Datatypes.S (2 * m))%nat) (Datatypes.S m)).
  { apply piLsb_sumR_ext. intros i Hi. apply piLd_point_binom_div. lia. }
  assert (Hscal : piLsb_sumR
    (fun i => bpa_binom (Datatypes.S (2 * m))%nat (Datatypes.S (2 * i))%nat
       / q_fact (Datatypes.S (2 * m))%nat) (Datatypes.S m)
    == piLsb_sumR
    (fun i => bpa_binom (Datatypes.S (2 * m))%nat (Datatypes.S (2 * i))%nat)
       (Datatypes.S m) / q_fact (Datatypes.S (2 * m))%nat).
  { unfold Qdiv.
    rewrite (piLd_sumR_scal (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i)))
                            (/ q_fact (Datatypes.S (2 * m))) (Datatypes.S m)).
    reflexivity. }
  rewrite Hext, Hscal, piLsb_row_odd. reflexivity.
Qed.

(** Row majorant: [|bandrow k m x| <= t_m(B)] for [k < m]; in the [m > 2k] branch the band row segment is the empty sum [0]. *)
Lemma piLd_bandrow_abs_le : forall (k m : nat) (x B : Q),
  (k < m)%nat -> Qle (Qabs x) B ->
  Qle (Qabs (piLc_bandrow k m x)) (piLd_t_term m B).
Proof.
  intros k m x B Hkm Hx.
  assert (H0B : Qle 0 B)
    by (apply (Qle_trans 0 (Qabs x) B); [apply Qabs_nonneg | exact Hx]).
  assert (H02 : Qle 0 2%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (H02B : Qle 0 (2 * B))
    by (apply piLd_qmult_nonneg_r; [exact H02 | exact H0B]).
  assert (Htpos : forall j : nat, Qle 0 (piLd_t_term j B))
    by (intros j; apply piLd_t_term_nonneg; exact H0B).
  unfold piLc_bandrow, piLd_t_term.
  apply (Qle_trans _
           (piLsb_sumR
              (fun u =>
                 Qabs (2%Q * sin_term (m - k + u)%nat x * cos_term (k - u)%nat x))
              (2 * k + 1 - m)%nat)).
  { apply piLd_abs_sumR_le. }
  assert (Hqdiv : forall e d : nat, Qle 0 (q_pow B e / q_fact d)).
  { intros e d. apply (Qle_trans _ ((0 * / q_fact d)%Q)).
    - rewrite Qmult_0_l. apply Qle_refl.
    - apply (Qmult_le_compat_nonneg 0%Q (q_pow B e)
               (/ q_fact d%nat) (/ q_fact d%nat)).
      + split; [apply Qle_refl | apply q_pow_nonneg; exact H0B].
      + split; [apply (Qlt_le_weak 0 _); apply Qinv_lt_0_compat; apply q_fact_pos
                | apply Qle_refl]. }
  assert (Hh : forall j : nat,
    Qle 0 (2%Q * (q_pow B (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))
              * (q_pow B (2 * (m - j)) / q_fact (2 * (m - j))))).
  { intros j. apply piLd_qmult_nonneg_r.
    - apply piLd_qmult_nonneg_r; [exact H02 | exact (Hqdiv (Datatypes.S (2 * j)) (Datatypes.S (2 * j)))].
    - exact (Hqdiv (2 * (m - j))%nat (2 * (m - j))%nat). }
  assert (Hcos : forall u : nat, (u < 2 * k + 1 - m)%nat ->
    (k - u)%nat = (m - (m - k + u))%nat) by (intros u Hu; lia).
  assert (Hpt : forall u : nat, (u < 2 * k + 1 - m)%nat ->
    Qabs (2%Q * sin_term (m - k + u)%nat x * cos_term (k - u)%nat x)
    == Qabs (2%Q * sin_term (m - k + u)%nat x
             * cos_term (m - (m - k + u)%nat)%nat x)).
  { intros u Hu. rewrite (Hcos u Hu). reflexivity. }
  rewrite (piLsb_sumR_ext
             (fun u => Qabs (2%Q * sin_term (m - k + u)%nat x * cos_term (k - u)%nat x))
             (fun u => Qabs (2%Q * sin_term (m - k + u)%nat x
                             * cos_term (m - (m - k + u)%nat)%nat x))
             (2 * k + 1 - m)%nat
             (fun u Hu => Hpt u Hu)).
  apply (Qle_trans _
           (piLsb_sumR
              (fun u => 2%Q * (q_pow B (Datatypes.S (2 * (m - k + u)))
                                / q_fact (Datatypes.S (2 * (m - k + u))))
                         * (q_pow B (2 * (m - (m - k + u)))
                                / q_fact (2 * (m - (m - k + u)))))
              (2 * k + 1 - m)%nat)).
  - apply piLd_sumR_le. intros u _.
    exact (piLd_point_term_le m (m - k + u)%nat x B Hx).
  - destruct (Nat.le_gt_cases m (2 * k)) as [Hm2 | Hmgt].
    + (* case [m <= 2k]: the band row segment is contained in the full row [0, m] *)
      apply (Qle_trans _
               (piLsb_sumR
                  (fun j => 2%Q * (q_pow B (Datatypes.S (2 * j))
                                    / q_fact (Datatypes.S (2 * j)))
                             * (q_pow B (2 * (m - j)) / q_fact (2 * (m - j))))
                  (Datatypes.S m))).
      * apply (piLd_shift_sum_le
                 (fun j => 2%Q * (q_pow B (Datatypes.S (2 * j))
                                   / q_fact (Datatypes.S (2 * j)))
                            * (q_pow B (2 * (m - j)) / q_fact (2 * (m - j))))
                 (m - k) (2 * k + 1 - m) m).
        -- exact Hh.
        -- lia.
      * assert (Hex :
          piLsb_sumR
            (fun j => 2%Q * (q_pow B (Datatypes.S (2 * j))
                              / q_fact (Datatypes.S (2 * j)))
                       * (q_pow B (2 * (m - j)) / q_fact (2 * (m - j))))
            (Datatypes.S m)
          == 2%Q * q_pow B (Datatypes.S (2 * m))
             * piLsb_sumR
                 (fun j => 1 / (q_fact (Datatypes.S (2 * j))%nat
                                * q_fact (2 * (m - j))%nat))
                 (Datatypes.S m)).
        { assert (Hpre :
            2%Q * q_pow B (Datatypes.S (2 * m))
            * piLsb_sumR
                (fun j => 1 / (q_fact (Datatypes.S (2 * j))%nat
                               * q_fact (2 * (m - j))%nat))
                (Datatypes.S m)
            == piLsb_sumR
                 (fun j => 1 / (q_fact (Datatypes.S (2 * j))%nat
                                * q_fact (2 * (m - j))%nat))
                 (Datatypes.S m)
              * (2%Q * q_pow B (Datatypes.S (2 * m)))) by ring.
          rewrite Hpre.
          rewrite <- (piLd_sumR_scal
                        (fun j => 1 / (q_fact (Datatypes.S (2 * j))%nat
                                       * q_fact (2 * (m - j))%nat))
                        (2%Q * q_pow B (Datatypes.S (2 * m))) (Datatypes.S m)).
          apply piLsb_sumR_ext. intros j Hi. cbv beta.
          assert (Hpow : q_pow B (Datatypes.S (2 * j)) * q_pow B (2 * (m - j))
                         == q_pow B (Datatypes.S (2 * m))).
          { rewrite <- (lw0_q_pow_add B (Datatypes.S (2 * j)) (2 * (m - j))).
            replace (Datatypes.S (2 * j) + 2 * (m - j))%nat
              with (Datatypes.S (2 * m))%nat by lia.
            reflexivity. }
          unfold Qdiv.
          rewrite <- (piLd_qinv_distr
                        (q_fact (Datatypes.S (2 * j))%nat)
                        (q_fact (2 * (m - j))%nat)
                        (piLrowB_qfact_neq0 (Datatypes.S (2 * j)))
                        (piLrowB_qfact_neq0 (2 * (m - j)))).
          assert (Hreg :
            2%Q * (q_pow B (Datatypes.S (2 * j)) * / q_fact (Datatypes.S (2 * j)))
              * (q_pow B (2 * (m - j)) * / q_fact (2 * (m - j)))
            == q_pow B (Datatypes.S (2 * j)) * q_pow B (2 * (m - j))
               * (2%Q * (/ q_fact (Datatypes.S (2 * j)) * / q_fact (2 * (m - j)))))
            by ring.
          rewrite Hreg, Hpow. ring. }
        rewrite Hex, piLd_row_binom_full.
        assert (Hclose :
          2%Q * q_pow B (Datatypes.S (2 * m))
            * (q_pow 2%Q (2 * m) / q_fact (Datatypes.S (2 * m))%nat)
          == q_pow (2 * B) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))%nat).
        { unfold Qdiv.
          rewrite (q_pow_succ (2 * B) (2 * m)).
          rewrite <- (lw0_q_pow_mult 2%Q B (2 * m)).
          rewrite (q_pow_succ B (2 * m)).
          ring. }
        rewrite Hclose. apply Qle_refl.
    + (* case [m > 2k]: the band row segment length truncates to [0] in [nat] *)
      assert (HL0 : (2 * k + 1 - m)%nat = 0%nat) by lia.
      rewrite HL0. cbn [piLsb_sumR]. exact (Htpos m).
Qed.

(* ============ Section 6. The main band bound (Group E) ============ *)

(** Partial band bound: [|bandsum k t x| <= sum_{u<=t} t_{k+1+u}(B)]. *)
Lemma piLd_bandsum_abs_le : forall (k t : nat) (x B : Q),
  Qle (Qabs x) B ->
  Qle (Qabs (piLc_bandsum k t x))
      (piLsb_sumR (fun u => piLd_t_term (Datatypes.S (k + u))%nat B) (Datatypes.S t)).
Proof.
  intros k t x B Hx. induction t as [| t IH].
  - cbn [piLc_bandsum]. cbv beta.
    rewrite piLsb_sumR_snoc. cbv beta.
    cbn [piLsb_sumR]. cbv beta.
    rewrite Qplus_0_l.
    replace (Datatypes.S (k + 0))%nat with (Datatypes.S k)%nat by lia.
    apply (piLd_bandrow_abs_le k (Datatypes.S k) x B).
    + apply Nat.lt_succ_diag_r.
    + exact Hx.
  - cbn [piLc_bandsum]. cbv beta.
    apply (Qle_trans _ (Qabs (piLc_bandsum k t x)
                        + Qabs (piLc_bandrow k (Datatypes.S (k + Datatypes.S t))%nat x))).
    + apply Qabs_triangle.
    + rewrite piLsb_sumR_snoc. cbv beta.
      apply (Qplus_le_compat (Qabs (piLc_bandsum k t x))
               (piLsb_sumR (fun u => piLd_t_term (Datatypes.S (k + u))%nat B) (Datatypes.S t))
               (Qabs (piLc_bandrow k (Datatypes.S (k + Datatypes.S t))%nat x))
               (piLd_t_term (Datatypes.S (k + Datatypes.S t)) B)).
      * exact IH.
      * apply (piLd_bandrow_abs_le k (Datatypes.S (k + Datatypes.S t)) x B).
        -- lia.
        -- exact Hx.
Qed.

(** The main band-bound theorem: [|dres k x| <= band_bound k B] for all [k]. *)
Lemma piLd_dres_band_le : forall (k : nat) (x B : Q),
  Qle (Qabs x) B -> Qle (Qabs (piL_sin_dres k x)) (piLd_band_bound k B).
Proof.
  intros k x B Hx. destruct k as [| k].
  - cbn [piL_sin_dres piLd_band_bound piLsb_sumR]. apply Qle_refl.
  - rewrite (piLc_dres_band (Datatypes.S k) x).
    replace (Datatypes.S k - 1)%nat with k%nat by lia.
    unfold piLd_band_bound.
    exact (piLd_bandsum_abs_le (Datatypes.S k) k x B Hx).
Qed.

(* ============ Section 7. Monotonicity (Group F) ============ *)

(** Quarter-step descent for the [t] terms: [t_{m+1} <= (1/4)·t_m] for [0 <= B] and [2*ceil(B) <= m]. *)
Lemma piLd_t_term_quarter_step : forall (B : Q) (m : nat),
  Qle 0 B -> (2 * Z.to_nat (Qceiling B) <= m)%nat ->
  Qle (piLd_t_term (Datatypes.S m) B) ((1 # 4)%Q * piLd_t_term m B).
Proof.
  intros B m H0B Hm.
  assert (H02 : Qle 0 2%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (HBceil : Qle B (Z.of_nat (Z.to_nat (Qceiling B)) # 1))
    by exact (QleT'_to_Qle B (d3p_inject_nat (Z.to_nat (Qceiling B)))
                (d3p_inject_ceiling_ge B H0B)).
  assert (HBB : Qle (B * B)
                  ((Z.of_nat (Z.to_nat (Qceiling B)) # 1)
                   * (Z.of_nat (Z.to_nat (Qceiling B)) # 1))).
  { apply (Qmult_le_compat_nonneg B (Z.of_nat (Z.to_nat (Qceiling B)) # 1)
             B (Z.of_nat (Z.to_nat (Qceiling B)) # 1));
      repeat split; assumption. }
  assert (Hreg : (2 * B) * (2 * B) == 4%Q * (B * B)) by ring.
  assert (Hs16 : 4%Q * ((2 * B) * (2 * B)) == 16%Q * (B * B))
    by (rewrite Hreg; ring).
  assert (H016 : Qle 0 16%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (Hstep1 : Qle (16%Q * (B * B))
                     (16%Q * ((Z.of_nat (Z.to_nat (Qceiling B)) # 1)
                              * (Z.of_nat (Z.to_nat (Qceiling B)) # 1))))
    by (apply (Qmult_le_compat_nonneg 16%Q 16%Q (B * B)
                 ((Z.of_nat (Z.to_nat (Qceiling B)) # 1)
                  * (Z.of_nat (Z.to_nat (Qceiling B)) # 1)));
        [split; [unfold Qle; cbn [Qnum Qden]; lia | apply Qle_refl]
        | split;
            [exact (piLd_qmult_nonneg_r B B H0B H0B) | exact HBB]]).
  assert (Hconv : 16%Q * ((Z.of_nat (Z.to_nat (Qceiling B)) # 1)
                          * (Z.of_nat (Z.to_nat (Qceiling B)) # 1))
                  == (4%Q * (Z.of_nat (Z.to_nat (Qceiling B)) # 1))
                     * (4%Q * (Z.of_nat (Z.to_nat (Qceiling B)) # 1))) by ring.
  assert (H4q : (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1)
                == 4%Q * (Z.of_nat (Z.to_nat (Qceiling B)) # 1)).
  { unfold Qeq, Qmult; cbn [Qnum Qden Qmult].
    rewrite !Z.mul_1_r, (Nat2Z.inj_mul 4 (Z.to_nat (Qceiling B))).
    reflexivity. }
  assert (H4i1 : Qle (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1)
                     (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1))
    by (apply piLd_inject_le; lia).
  assert (H4i2 : Qle (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1)
                     (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))
    by (apply piLd_inject_le; lia).
  assert (Hnn4 : Qle 0 (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1))
    by (apply piLd_inject_nonneg).
  assert (HR : Qle (4%Q * ((2 * B) * (2 * B)))
                   ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                    * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))).
  { rewrite Hs16.
    apply (Qle_trans _ (16%Q * ((Z.of_nat (Z.to_nat (Qceiling B)) # 1)
                                * (Z.of_nat (Z.to_nat (Qceiling B)) # 1)))).
    - exact Hstep1.
    - rewrite Hconv, <- H4q.
      apply (Qmult_le_compat_nonneg
               (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1)
               (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
               (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1)
               (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1));
        repeat split; assumption. }
  assert (HDne : ~ (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                     * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q == 0)).
  { intro H0.
    exact (q_neq_of_lt
             ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
              * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q
             (Qmult_lt_0_compat
                (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
                (Z.of_nat (Datatypes.S (2 * m)) # 1)
                (piLd_inject_pos (Datatypes.S (Datatypes.S (2 * m))))
                (piLd_inject_pos (Datatypes.S (2 * m)))) H0). }
  assert (H0D : Qle 0 (/ ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                          * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)).
  { apply (Qlt_le_weak 0 _).
    apply Qinv_lt_0_compat.
    apply Qmult_lt_0_compat; apply piLd_inject_pos. }
  assert (HHD : Qle (4%Q * ((2 * B) * (2 * B)
                            * / ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                                 * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q))
                    1%Q).
  { assert (Hreg2 : 4%Q * ((2 * B) * (2 * B)
                            * / ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                                 * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)
                    == (4%Q * ((2 * B) * (2 * B)))
                       * / ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                            * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q) by ring.
    rewrite Hreg2, <- (Qmult_inv_r ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                                    * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q HDne).
    apply (Qmult_le_compat_r (4%Q * ((2 * B) * (2 * B)))
               ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q
               (/ ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                  * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q) HR H0D). }
  assert (H0q4 : Qle 0 (1 # 4)%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (Hcore : Qle ((2 * B) * (2 * B)
                       * / ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                            * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)
                      (1 # 4)%Q).
  { assert (Hq1 : (2 * B) * (2 * B)
                  * / ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                       * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q
                  == (1 # 4)%Q * (4%Q * ((2 * B) * (2 * B)
                                          * / ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                                               * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)))
      by ring.
    rewrite Hq1.
    apply (Qle_trans _ ((1 # 4)%Q * 1%Q)%Q).
    + apply piLd_qmult_le_l; [exact H0q4 | exact HHD].
    + assert (Hc14 : (1 # 4)%Q * 1%Q == (1 # 4)%Q) by ring.
      rewrite Hc14. apply Qle_refl. }
  assert (HneZF : ~ ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
                     * q_fact (Datatypes.S (2 * m))%nat == 0)%Q).
  { apply q_neq_of_lt. apply Qmult_lt_0_compat;
      [apply piLd_inject_pos | apply q_fact_pos]. }
  assert (Hratio : piLd_t_term (Datatypes.S m) B
    == (2 * B) * (2 * B)
       * / ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
            * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q
       * piLd_t_term m B).
  { unfold piLd_t_term at 1. unfold Qdiv.
    replace (Datatypes.S (2 * Datatypes.S m))%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by lia.
    rewrite (q_pow_succ (2 * B) (Datatypes.S (Datatypes.S (2 * m)))).
    rewrite (q_pow_succ (2 * B) (Datatypes.S (2 * m))).
    rewrite (q_fact_succ (Datatypes.S (Datatypes.S (2 * m)))).
    rewrite (q_fact_succ (Datatypes.S (2 * m))).
    rewrite <- (piLd_qinv_distr
                  (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                  ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
                   * q_fact (Datatypes.S (2 * m))%nat)
                  (piLd_inject_neq0 (Datatypes.S (Datatypes.S (2 * m)))) HneZF).
    rewrite <- (piLd_qinv_distr
                  (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
                  (q_fact (Datatypes.S (2 * m))%nat)
                  (piLd_inject_neq0 (Datatypes.S (2 * m)))
                  (piLrowB_qfact_neq0 (Datatypes.S (2 * m)))).
    unfold piLd_t_term. unfold Qdiv.
    rewrite <- (piLd_qinv_distr
                  (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                  (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
                  (piLd_inject_neq0 (Datatypes.S (Datatypes.S (2 * m))))
                  (piLd_inject_neq0 (Datatypes.S (2 * m)))).
    ring. }
  assert (Htm : piLd_t_term m B
                == q_pow (2 * B) (Datatypes.S (2 * m))
                   * / q_fact (Datatypes.S (2 * m))%nat)
    by (unfold piLd_t_term, Qdiv; reflexivity).
  assert (H0PF : Qle 0 (q_pow (2 * B) (Datatypes.S (2 * m))
                         * / q_fact (Datatypes.S (2 * m))%nat)).
  { apply (Qle_trans _ ((0 * / q_fact (Datatypes.S (2 * m)))%Q)).
    - rewrite Qmult_0_l. apply Qle_refl.
    - apply (Qmult_le_compat_nonneg 0%Q (q_pow (2 * B) (Datatypes.S (2 * m)))
               (/ q_fact (Datatypes.S (2 * m))%Q) (/ q_fact (Datatypes.S (2 * m))%Q)).
      + split;
          [apply Qle_refl
          | apply q_pow_nonneg; exact (piLd_qmult_nonneg_r 2%Q B H02 H0B)].
      + split; [apply (Qlt_le_weak 0 _); apply Qinv_lt_0_compat; apply q_fact_pos
                | apply Qle_refl]. }
  rewrite Hratio, Htm.
  apply (Qmult_le_compat_r ((2 * B) * (2 * B)
                            * / ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))) # 1)
                                 * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)
             (1 # 4)%Q
             (q_pow (2 * B) (Datatypes.S (2 * m))
              * / q_fact (Datatypes.S (2 * m))%Q) Hcore H0PF).
Qed.

(** Chain form of the quarter-step descent for the [t] terms: [t_{m+p} <= (1/4)^p·t_m]. *)
Lemma piLd_t_term_quarter_chain : forall (B : Q) (m p : nat),
  Qle 0 B -> (2 * Z.to_nat (Qceiling B) <= m)%nat ->
  Qle (piLd_t_term (m + p)%nat B) (q_pow (1 # 4)%Q p * piLd_t_term m B).
Proof.
  intros B m p H0B Hm. induction p as [| p IH].
  - replace (m + 0)%nat with m%nat by lia.
    cbn [q_pow]. rewrite Qmult_1_l. apply Qle_refl.
  - replace (m + Datatypes.S p)%nat with (Datatypes.S (m + p))%nat by lia.
    apply (Qle_trans _ ((1 # 4)%Q * piLd_t_term (m + p) B)).
    + apply piLd_t_term_quarter_step.
      * exact H0B.
      * apply (Nat.le_trans _ m); [exact Hm | lia].
    + rewrite (q_pow_succ (1 # 4)%Q p).
      apply (Qle_trans _ ((1 # 4)%Q * (q_pow (1 # 4)%Q p * piLd_t_term m B))).
      * apply piLd_qmult_le_l;
          [(unfold Qle; cbn [Qnum Qden]; lia) | exact IH].
      * rewrite Qmult_assoc. apply Qle_refl.
Qed.

(** The exact 1/4 geometric-sum identity. *)
Lemma piLd_quarter_sum_identity : forall n : nat,
  piLsb_sumR (fun i => q_pow (1 # 4)%Q i) n
  + (4 # 3)%Q * q_pow (1 # 4)%Q n == (4 # 3)%Q.
Proof.
  intros n. induction n as [| n IH].
  - cbn [piLsb_sumR q_pow]. cbv beta. ring.
  - cbn [piLsb_sumR]. cbv beta.
    rewrite (q_pow_succ (1 # 4)%Q n).
    assert (Hs : piLsb_sumR (fun i : nat => q_pow (1 # 4)%Q i) n
                 == (4 # 3)%Q - (4 # 3)%Q * q_pow (1 # 4)%Q n).
    { transitivity (piLsb_sumR (fun i : nat => q_pow (1 # 4)%Q i) n
                    + (4 # 3)%Q * q_pow (1 # 4)%Q n
                    - (4 # 3)%Q * q_pow (1 # 4)%Q n).
      - ring.
      - rewrite IH. ring. }
    rewrite Hs. ring.
Qed.

(** Geometric tail bound: [band_bound k B <= (4/3)·t_{k+1}(B)] for [2*ceil(B) < k]. *)
Lemma piLd_band_bound_geometric : forall (B : Q) (k : nat),
  Qle 0 B -> (2 * Z.to_nat (Qceiling B) < k)%nat ->
  Qle (piLd_band_bound k B) ((4 # 3)%Q * piLd_t_term (Datatypes.S k) B).
Proof.
  intros B k H0B Hk. unfold piLd_band_bound.
  apply (Qle_trans _
           (piLsb_sumR (fun u => q_pow (1 # 4)%Q u * piLd_t_term (Datatypes.S k) B) k)).
  - apply piLd_sumR_le. intros u Hu.
    apply (piLd_t_term_quarter_chain B (Datatypes.S k) u H0B). lia.
  - rewrite (piLd_sumR_scal (fun u => q_pow (1 # 4)%Q u)
               (piLd_t_term (Datatypes.S k) B) k).
    assert (Hsumle : Qle (piLsb_sumR (fun u => q_pow (1 # 4)%Q u) k) (4 # 3)%Q).
    { pose proof (piLd_quarter_sum_identity k) as Hid.
      assert (Hqpos : Qle 0 ((4 # 3)%Q * q_pow (1 # 4)%Q k)).
      { apply piLd_qmult_nonneg_r.
        - unfold Qle; cbn [Qnum Qden]; lia.
        - apply q_pow_nonneg. unfold Qle; cbn [Qnum Qden]; lia. }
      assert (H2 : piLsb_sumR (fun u => q_pow (1 # 4)%Q u) k
                   == (4 # 3)%Q - (4 # 3)%Q * q_pow (1 # 4)%Q k).
      { transitivity (piLsb_sumR (fun u => q_pow (1 # 4)%Q u) k
                      + (4 # 3)%Q * q_pow (1 # 4)%Q k
                      - (4 # 3)%Q * q_pow (1 # 4)%Q k).
        - ring.
        - rewrite Hid. ring. }
      rewrite H2. apply piLd_qle_sub_r. exact Hqpos. }
    assert (Htpos : Qle 0 (piLd_t_term (Datatypes.S k) B))
      by (apply piLd_t_term_nonneg; exact H0B).
    apply (Qmult_le_compat_r (piLsb_sumR (fun u => q_pow (1 # 4)%Q u) k)
               (4 # 3)%Q (piLd_t_term (Datatypes.S k) B) Hsumle Htpos).
Qed.

(** Nonincreasing: [band_bound k2 <= band_bound k1] for [0 <= B] and [2*ceil(B) < k1 <= k2]. *)
Lemma piLd_band_bound_anti : forall (B : Q) (k1 k2 : nat),
  Qle 0 B -> (2 * Z.to_nat (Qceiling B) < k1)%nat -> (k1 <= k2)%nat ->
  Qle (piLd_band_bound k2 B) (piLd_band_bound k1 B).
Proof.
  intros B k1 k2 H0B Hk1 Hle.
  destruct (Nat.eq_dec k1 k2) as [Heq | Hne].
  - subst k2. apply Qle_refl.
  - assert (Hlt : (k1 < k2)%nat) by lia.
    assert (Hlow : Qle (piLd_t_term (Datatypes.S k1) B) (piLd_band_bound k1 B)).
    { unfold piLd_band_bound.
      replace k1%nat with (Datatypes.S (k1 - 1))%nat by lia.
      rewrite piLsb_sumR_head. cbv beta. rewrite Nat.add_0_r.
      apply (Qle_trans _ (piLd_t_term (Datatypes.S (Datatypes.S (k1 - 1))) B
                          + 0%Q)).
      - rewrite Qplus_0_r. apply Qle_refl.
      - apply (Qplus_le_compat
                 (piLd_t_term (Datatypes.S (Datatypes.S (k1 - 1))) B)
                 (piLd_t_term (Datatypes.S (Datatypes.S (k1 - 1))) B) 0%Q
                 (piLsb_sumR
                    (fun i => piLd_t_term
                                (Datatypes.S (Datatypes.S (k1 - 1) + Datatypes.S i)) B)
                    (k1 - 1))).
        + apply Qle_refl.
        + apply piLd_sumR_nonneg. intros i _.
          apply piLd_t_term_nonneg. exact H0B. }
    assert (Hfac : Qle ((4 # 3)%Q * q_pow (1 # 4)%Q (k2 - k1)) 1%Q).
    { pose proof (piLd_quarter_sum_identity (k2 - k1)) as Hid.
      assert (Hq1 : (4 # 3)%Q * q_pow (1 # 4)%Q (k2 - k1)
                    == (4 # 3)%Q
                       - piLsb_sumR (fun i => q_pow (1 # 4)%Q i) (k2 - k1)).
      { transitivity (piLsb_sumR (fun i => q_pow (1 # 4)%Q i) (k2 - k1)
                      + (4 # 3)%Q * q_pow (1 # 4)%Q (k2 - k1)
                      - piLsb_sumR (fun i => q_pow (1 # 4)%Q i) (k2 - k1)).
        - ring.
        - rewrite Hid. ring. }
      assert (Hge1 : Qle 1%Q (piLsb_sumR (fun i => q_pow (1 # 4)%Q i) (k2 - k1))).
      { destruct (k2 - k1)%nat as [| p] eqn:Hp.
        - exfalso. lia.
        - rewrite piLsb_sumR_head. cbv beta.
          apply (Qle_trans _ (q_pow (1 # 4)%Q 0 + 0%Q)%Q).
          + rewrite Qplus_0_r. apply Qle_refl.
          + apply (Qplus_le_compat (q_pow (1 # 4)%Q 0) (q_pow (1 # 4)%Q 0) 0%Q
                     (piLsb_sumR (fun i => q_pow (1 # 4)%Q (Datatypes.S i)) p)).
            * apply Qle_refl.
            * apply piLd_sumR_nonneg. intros i _.
              apply q_pow_nonneg. unfold Qle; cbn [Qnum Qden]; lia. }
      assert (Hq4 : Qle 0 (4 # 3)%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
      rewrite Hq1.
      apply (Qle_trans _ ((4 # 3)%Q - 1%Q)).
      - apply piLd_qle_sub_l. exact Hge1.
      - assert (Hconv : (4 # 3)%Q - 1%Q == (1 # 3)%Q) by ring.
        rewrite Hconv. unfold Qle; cbn [Qnum Qden]; lia. }
    assert (Hpre : (2 * Z.to_nat (Qceiling B) <= Datatypes.S k1)%nat) by lia.
    assert (Hq : Qle (piLd_t_term (Datatypes.S k2) B)
                     (q_pow (1 # 4)%Q (k2 - k1) * piLd_t_term (Datatypes.S k1) B)).
    { pose proof (piLd_t_term_quarter_chain B (Datatypes.S k1) (k2 - k1) H0B
                    Hpre) as Hqc.
      replace (Datatypes.S k1 + (k2 - k1))%nat with (Datatypes.S k2)%nat in Hqc
        by lia.
      exact Hqc. }
    assert (Hscale : Qle ((4 # 3)%Q * piLd_t_term (Datatypes.S k2) B)
                       ((4 # 3)%Q * (q_pow (1 # 4)%Q (k2 - k1)
                                     * piLd_t_term (Datatypes.S k1) B)))
      by (apply piLd_qmult_le_l; [unfold Qle; cbn [Qnum Qden]; lia | exact Hq]).
    apply (Qle_trans _ ((4 # 3)%Q * piLd_t_term (Datatypes.S k2) B)).
    + apply piLd_band_bound_geometric; [exact H0B | lia].
    + apply (Qle_trans _
               ((4 # 3)%Q * (q_pow (1 # 4)%Q (k2 - k1)
                             * piLd_t_term (Datatypes.S k1) B))).
      * exact Hscale.
      * apply (Qle_trans _ (piLd_t_term (Datatypes.S k1) B)).
        -- assert (Hs : (4 # 3)%Q * (q_pow (1 # 4)%Q (k2 - k1)
                                     * piLd_t_term (Datatypes.S k1) B)
                        == ((4 # 3)%Q * q_pow (1 # 4)%Q (k2 - k1))
                           * piLd_t_term (Datatypes.S k1) B) by ring.
           rewrite Hs.
           assert (Htpos : Qle 0 (piLd_t_term (Datatypes.S k1) B))
             by (apply piLd_t_term_nonneg; exact H0B).
           apply (Qle_trans _ (1%Q * piLd_t_term (Datatypes.S k1) B)).
           ++ apply (Qmult_le_compat_r ((4 # 3)%Q * q_pow (1 # 4)%Q (k2 - k1))
                      1%Q (piLd_t_term (Datatypes.S k1) B) Hfac Htpos).
           ++ rewrite Qmult_1_l. apply Qle_refl.
        -- exact Hlow.
Qed.

(* ============ Section 8. Truncation-length selection (Group G, in [sigT] witness form) ============ *)

Lemma piLd_band_small : forall (B dt : Q),
  Qlt 0 B -> Qlt 0 dt ->
  sigT (fun j : nat => forall k : nat, (j <= k)%nat -> Qlt (piLd_band_bound k B) dt).
Proof.
  intros B dt HB Hdt.
  assert (HBpos : Qle 0 B) by (apply (Qlt_le_weak 0%Q B); exact HB).
  assert (Hc : Qlt 0 ((4 # 3)%Q
                      * piLd_t_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)).
  { apply Qmult_lt_0_compat.
    - unfold Qlt; cbn [Qnum Qden]; lia.
    - unfold piLd_t_term. apply Qmult_lt_0_compat.
      + apply piLd_q_pow_pos. apply Qmult_lt_0_compat;
          [unfold Qlt; cbn [Qnum Qden]; lia | exact HB].
      + apply Qinv_lt_0_compat. apply q_fact_pos. }
  destruct (d3p_quarter_pow_lt ((4 # 3)%Q
                                * piLd_t_term
                                    (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)
                  dt Hc Hdt) as [d0 Hd0].
  exists (Datatypes.S (2 * Z.to_nat (Qceiling B)) + d0)%nat.
  intros k Hk.
  apply (Qle_lt_trans _
           (((4 # 3)%Q
             * piLd_t_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)
            * q_pow (1 # 4)%Q d0)).
  - apply (Qle_trans _
             (((4 # 3)%Q
               * piLd_t_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)
              * q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))).
    + apply (Qle_trans _
               ((4 # 3)%Q * piLd_t_term (Datatypes.S k) B)).
      * apply piLd_band_bound_geometric; [exact HBpos | lia].
      * assert (Hpre2 : (2 * Z.to_nat (Qceiling B) <= k)%nat) by lia.
        assert (Hq : Qle (piLd_t_term (Datatypes.S k) B)
                         (piLd_t_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B
                          * q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))).
        { apply (Qle_trans _ ((1 # 4)%Q * piLd_t_term k B)).
          - apply (piLd_t_term_quarter_step B k HBpos Hpre2).
          - apply (Qle_trans _
                     ((1 # 4)%Q
                      * (q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B)))
                         * piLd_t_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B))).
            + apply piLd_qmult_le_l.
              * unfold Qle; cbn [Qnum Qden]; lia.
              * pose proof (piLd_t_term_quarter_chain B
                              (Datatypes.S (2 * Z.to_nat (Qceiling B)))
                              (k - Datatypes.S (2 * Z.to_nat (Qceiling B)))
                              HBpos (Nat.le_succ_diag_r _)) as Hqc.
                replace (Datatypes.S (2 * Z.to_nat (Qceiling B))
                         + (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))%nat
                  with k%nat in Hqc by lia.
                exact Hqc.
            + apply (Qle_trans _ (1%Q * (q_pow (1 # 4)%Q
                                            (k - Datatypes.S (2 * Z.to_nat (Qceiling B)))
                                         * piLd_t_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B))).
              * apply (Qmult_le_compat_r (1 # 4)%Q 1%Q
                           (q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B)))
                            * piLd_t_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B));
                   [unfold Qle; cbn [Qnum Qden]; lia
                   | apply piLd_qmult_nonneg_r;
                       [apply q_pow_nonneg; unfold Qle; cbn [Qnum Qden]; lia
                       | apply piLd_t_term_nonneg; exact HBpos]].
              * rewrite Qmult_1_l,
                  (Qmult_comm (q_pow (1 # 4)%Q
                                (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))
                              (piLd_t_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)).
                apply Qle_refl. }
        rewrite <- (Qmult_assoc (4 # 3)%Q
                      (piLd_t_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)
                      (q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))).
        apply piLd_qmult_le_l;
          [unfold Qle; cbn [Qnum Qden]; lia | exact Hq].
    + assert (Hp : Qle (q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))
                       (q_pow (1 # 4)%Q d0)).
      { replace (k - Datatypes.S (2 * Z.to_nat (Qceiling B)))%nat
          with (d0 + (k - (Datatypes.S (2 * Z.to_nat (Qceiling B)) + d0)))%nat by lia.
        rewrite lw0_q_pow_add.
        apply (Qle_trans _ (1%Q * q_pow (1 # 4)%Q d0)).
        - rewrite (Qmult_comm (q_pow (1 # 4)%Q d0)
                     (q_pow (1 # 4)%Q
                        (k - (Datatypes.S (2 * Z.to_nat (Qceiling B)) + d0)))).
          apply (Qmult_le_compat_r
                     (q_pow (1 # 4)%Q
                        (k - (Datatypes.S (2 * Z.to_nat (Qceiling B)) + d0))) 1%Q
                     (q_pow (1 # 4)%Q d0));
            [apply (Qle_trans _ (q_pow 1%Q
                             (k - (Datatypes.S (2 * Z.to_nat (Qceiling B)) + d0))));
               [apply (q_pow_mono (1 # 4)%Q 1%Q
                          (k - (Datatypes.S (2 * Z.to_nat (Qceiling B)) + d0)));
                  [unfold Qle; cbn [Qnum Qden]; lia
                  | unfold Qle; cbn [Qnum Qden]; lia]
               | rewrite piLd_q_pow_one; apply Qle_refl]
            | apply q_pow_nonneg; unfold Qle; cbn [Qnum Qden]; lia].
        - rewrite Qmult_1_l. apply Qle_refl. }
      apply piLd_qmult_le_l.
      * apply piLd_qmult_nonneg_r.
        -- unfold Qle; cbn [Qnum Qden]; lia.
        -- apply piLd_t_term_nonneg; exact HBpos.
      * exact Hp.
  - exact Hd0.
Qed.

(* ============ Section 9. The sigma2 assembly prerequisite (Group H) ============ *)

Lemma piLd_dres_small : forall (B dt : Q),
  Qlt 0 B -> Qlt 0 dt ->
  sigT (fun j : nat => forall (k : nat) (x : Q),
          (j <= k)%nat -> Qle (Qabs x) B -> Qlt (Qabs (piL_sin_dres k x)) dt).
Proof.
  intros B dt HB Hdt.
  destruct (piLd_band_small B dt HB Hdt) as [j Hj].
  exists j. intros k x Hk Hx.
  apply (Qle_lt_trans _ (piLd_band_bound k B)).
  - apply piLd_dres_band_le. exact Hx.
  - apply Hj. exact Hk.
Qed.
