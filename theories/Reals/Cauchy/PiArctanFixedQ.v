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
(** * PiArctanFixedQ.v

    Mission.  The explicit [Q]-side form of the fixed-value identity
    for arctan: the paired arctan truncation
    [A_m(x) := sum_{j <= m} (x^{4j+1}/(4j+1) - x^{4j+3}/(4j+3))],
    whose per-pair terms are carried by [lp_a] (the source of the odd
    terms of the Leibniz series for [pi]); the core geometric identity
    [(1 + x^2) * G_m(x) == 1 - x^{4m+4}] (with [G_m] the termwise
    derivative sum of [A_m]); the fixed-value bridge
    [A_m(1) == lp_odd m]; the scaling band [lp_odd m <= 1]; and the
    per-pair positivity band ([0 <= x <= 1] implies [0 <= A_m(x)]).
    This file provides the definition side and the supplying bounds
    for the main statement [piL_arctan_fixed_sc] (a uniform small
    bound on [|S_k(lp_odd m) - C_k(lp_odd m)|] by a discrete Gronwall
    argument).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [QArith.Qfield], [ZArith.ZArith], [Arith.PeanoNat], [Lia];
    [PiLeibnizCReal] (the source of [lp_a]/[lp_pair]/[lp_odd]) and
    [PiKernelSlack] ([q_pow], [q_fact], [sin_partial], [cos_partial],
    [qeq_le], [q_pow_nonneg], [q_pow_mono], [q_fact_pos],
    [q_lt_0_succ_den], [q_lt_0_odd_den], [sc_q_pow_one],
    [sc_lpa_decr_le]).

    References.  [S10_KVQuantTrig.v], the [sc_lp] family (the source
    coordinates of the [PiKernelSlack] port); the discrete-Gronwall
    main file of the derivative-free five-step route continues in the
    later segments of the same development.

    Constructivity.  Auxiliary lemma conclusions live on the stdlib
    [Qle]/[Qlt]/[Qeq] side (purely constructive); assumption-free and
    fully proved, with no non-constructive principles; [lia]/[field]
    are used only in auxiliary bookkeeping steps; extractable.

    Build.  [coqc -native-compiler no -q -Q . "" PiArctanFixedQ.v]
    WARNING: this file is experimental and likely to change in future releases. *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import QArith.Qfield.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
Require Import PiLeibnizCReal.
Require Import PiKernelSlack.

(* ================= Section 0. Common small [Q]-arithmetic helpers ================= *)

Lemma pa_qpos_neq0 : forall x : Q, Qlt 0 x -> ~ (x == 0).
Proof.
  intros x H Heq.
  apply (Qlt_not_eq 0 x H).
  rewrite <- Heq.
  apply Qeq_refl.
Qed.

(** Right extension along [Qeq]: [x <= y] and [y == z] imply [x <= z]
    (the standard route for rewriting along [Qeq] into a [Qle] goal). *)
Lemma pa_le_qeq_r : forall x y z : Q, Qle x y -> y == z -> Qle x z.
Proof.
  intros x y z Hxy Heq.
  apply (Qle_trans _ y _).
  - exact Hxy.
  - apply qeq_le.
    exact Heq.
Qed.

Lemma pa_zsucc_qmake : forall n : nat,
  (Z.of_nat (Datatypes.S n) # 1)%Q == ((Z.of_nat n # 1) + 1)%Q.
Proof.
  intro n.
  replace (Z.of_nat (Datatypes.S n)) with (Z.succ (Z.of_nat n))
    by (rewrite Nat2Z.inj_succ; reflexivity).
  unfold Qeq.
  simpl.
  lia.
Qed.

(** Order preservation under left multiplication (the stdlib has no
    [Qmult_le_compat_l] under that exact name; route through
    commutativity). *)
Lemma pa_Qmult_le_l : forall a b c : Q,
  Qle a b -> Qle 0 c -> Qle (c * a) (c * b).
Proof.
  intros a b c Hab Hc.
  assert (H1 : c * a == a * c) by ring.
  assert (H2 : c * b == b * c) by ring.
  rewrite H1.
  rewrite H2.
  apply Qmult_le_compat_r; assumption.
Qed.

(** Order preservation under subtraction on the left (direction
    check: [b <= c] implies [a - c <= a - b]). *)
Lemma pa_Qminus_le : forall a b c : Q, Qle b c -> Qle (a - c) (a - b).
Proof.
  intros a b c Hbc.
  change (a - c) with (a + (- c)).
  change (a - b) with (a + (- b)).
  apply (Qplus_le_compat a a (- c) (- b)).
  - apply Qle_refl.
  - apply Qopp_le_compat. exact Hbc.
Qed.

Lemma pa_qpow_0 : forall x : Q, q_pow x 0 == 1.
Proof. reflexivity. Qed.

Lemma pa_qpow_add : forall (x : Q) (n m : nat),
  q_pow x (n + m) == q_pow x n * q_pow x m.
Proof.
  intros x n m.
  induction m as [| p IH].
  - replace (n + 0)%nat with n by lia.
    rewrite pa_qpow_0.
    ring.
  - replace (n + Datatypes.S p)%nat with (Datatypes.S (n + p)) by lia.
    change (q_pow x (Datatypes.S (n + p))) with (x * q_pow x (n + p)).
    change (q_pow x (Datatypes.S p)) with (x * q_pow x p).
    rewrite IH.
    ring.
Qed.

Lemma pa_qpow_add2 : forall (x : Q) (n : nat),
  q_pow x (n + 2) == q_pow x n * x * x.
Proof.
  intros x n.
  rewrite pa_qpow_add.
  change (q_pow x 2) with (x * (x * q_pow x 0)).
  rewrite pa_qpow_0.
  ring.
Qed.

(** Geometric difference sum:
    [y^n - x^n == (y - x) * gsum n x y] with
    [gsum n x y := sum_{i < n} x^i * y^{n-1-i}]. *)
Fixpoint gsum (n : nat) (x y : Q) : Q :=
  match n with
  | 0%nat => 0%Q
  | Datatypes.S p => q_pow x p + y * gsum p x y
  end.

Lemma pa_pow_diff : forall (n : nat) (x y : Q),
  q_pow y n - q_pow x n == (y - x) * gsum n x y.
Proof.
  intros n x y.
  induction n as [| p IH].
  - simpl. ring.
  - simpl.
    assert (Hr : y * q_pow y p - x * q_pow x p
                 == (y - x) * q_pow x p + y * (q_pow y p - q_pow x p)) by ring.
    rewrite Hr.
    rewrite IH.
    ring.
Qed.

Lemma pa_gsum_nonneg : forall (n : nat) (x y : Q),
  Qle 0 x -> Qle 0 y -> Qle 0 (gsum n x y).
Proof.
  intros n x y H0 Hy.
  induction n as [| p IH].
  - apply Qle_refl.
  - change (gsum (Datatypes.S p) x y) with (q_pow x p + y * gsum p x y).
    apply (Qplus_le_compat 0%Q (q_pow x p) 0%Q (y * gsum p x y)).
    + apply (q_pow_nonneg x p H0).
    + apply Qmult_le_0_compat; [exact Hy | exact IH].
Qed.

(** Lower bound for [gsum]:
    [(S p)#1 * x^p <= gsum (S p) x y] (for [0 <= x], [0 <= y],
    [x <= y]). *)
Lemma pa_gsum_lower : forall (p : nat) (x y : Q),
  Qle 0 x -> Qle 0 y -> Qle x y ->
  Qle ((Z.of_nat (Datatypes.S p) # 1) * q_pow x p) (gsum (Datatypes.S p) x y).
Proof.
  intros p x y H0 Hy Hxy.
  induction p as [| q IH].
  - change (gsum 1 x y) with (q_pow x 0 + y * gsum 0 x y).
    change (gsum 0 x y) with 0%Q.
    change (q_pow x 0) with 1%Q.
    apply (pa_le_qeq_r ((Z.of_nat 1 # 1) * 1%Q) 1%Q (1%Q + y * 0%Q)).
    + change ((Z.of_nat 1 # 1) * 1%Q) with 1%Q.
      apply Qle_refl.
    + assert (Hyq : 1%Q == 1%Q + y * 0%Q) by ring.
      exact Hyq.
  - apply (Qle_trans _ (x * ((Z.of_nat (Datatypes.S q) # 1)%Q * q_pow x q) + x * q_pow x q) _).
    + apply (pa_le_qeq_r
        ((Z.of_nat (Datatypes.S (Datatypes.S q)) # 1) * q_pow x (Datatypes.S q))
        (((Z.of_nat (Datatypes.S q) # 1)%Q + 1) * (x * q_pow x q))
        (x * ((Z.of_nat (Datatypes.S q) # 1)%Q * q_pow x q) + x * q_pow x q)).
      * apply qeq_le.
        rewrite pa_zsucc_qmake.
        change (q_pow x (Datatypes.S q)) with (x * q_pow x q).
        ring.
      * assert (Hrx : ((Z.of_nat (Datatypes.S q) # 1)%Q + 1) * (x * q_pow x q)
                      == x * ((Z.of_nat (Datatypes.S q) # 1)%Q * q_pow x q) + x * q_pow x q) by ring.
        exact Hrx.
    + change (gsum (Datatypes.S (Datatypes.S q)) x y)
        with (q_pow x (Datatypes.S q) + y * gsum (Datatypes.S q) x y).
      apply (Qle_trans _ (x * q_pow x q + x * ((Z.of_nat (Datatypes.S q) # 1)%Q * q_pow x q)) _).
      * apply qeq_le. ring.
      * apply (Qplus_le_compat _ (q_pow x (Datatypes.S q)) _ (y * gsum (Datatypes.S q) x y)).
        -- apply Qle_refl.
        -- apply (Qle_trans _ (x * gsum (Datatypes.S q) x y) _).
           { apply (pa_Qmult_le_l ((Z.of_nat (Datatypes.S q) # 1)%Q * q_pow x q)
                      (gsum (Datatypes.S q) x y) x);
               [exact IH | exact H0]. }
           { apply Qmult_le_compat_r;
               [exact Hxy
               | apply (pa_gsum_nonneg (Datatypes.S q) x y H0 Hy)]. }
Qed.

(* ================= Section 1. Definitions: [aG]/[aA]/[aF] ================= *)

Definition aG_term (j : nat) (x : Q) : Q := q_pow x (4 * j) - q_pow x (4 * j + 2).

Fixpoint aG (m : nat) (x : Q) : Q :=
  match m with
  | 0%nat => aG_term 0%nat x
  | Datatypes.S p => aG p x + aG_term (Datatypes.S p) x
  end.

Definition aA_term (j : nat) (x : Q) : Q :=
  q_pow x (4 * j + 1) * lp_a (2 * j) - q_pow x (4 * j + 3) * lp_a (2 * j + 1).

Fixpoint aA (m : nat) (x : Q) : Q :=
  match m with
  | 0%nat => aA_term 0%nat x
  | Datatypes.S p => aA p x + aA_term (Datatypes.S p) x
  end.

Definition aF (k m : nat) (x : Q) : Q :=
  sin_partial k (aA m x) - x * cos_partial k (aA m x).

(* ================= Section 2. The fixed-value bridge and the band bounds ================= *)

Lemma pa_lp_a_val : forall k : nat, lp_a k == (/ (Z.of_nat (2 * k + 1) # 1))%Q.
Proof.
  intro k.
  unfold lp_a, Qdiv.
  ring.
Qed.

Lemma pa_lpa_pos : forall k : nat, Qlt 0 (lp_a k).
Proof.
  intro k.
  unfold lp_a, Qdiv.
  apply Qmult_lt_0_compat.
  - assert (H1 : Qlt 0 1) by (unfold Qlt; simpl; lia).
    exact H1.
  - apply Qinv_lt_0_compat.
    apply (q_lt_0_odd_den k).
Qed.

Lemma pa_aA_term_one : forall j : nat, aA_term j 1 == lp_pair j.
Proof.
  intro j.
  unfold aA_term, lp_pair.
  rewrite (sc_q_pow_one (4 * j + 1)).
  rewrite (sc_q_pow_one (4 * j + 3)).
  ring.
Qed.

(** [A_m(1) == lp_odd m] (the fixed-value bridge). *)
Lemma aA_one_lp_odd : forall m : nat, aA m 1 == lp_odd m.
Proof.
  intro m.
  induction m as [| p IH].
  - apply pa_aA_term_one.
  - change (aA (Datatypes.S p) 1) with (aA p 1 + aA_term (Datatypes.S p) 1).
    rewrite IH.
    rewrite pa_aA_term_one.
    reflexivity.
Qed.

Lemma pa_lp_pair_S : forall m : nat,
  lp_pair (Datatypes.S m) == lp_a (2 * m + 2) - lp_a (2 * m + 3).
Proof.
  intro m.
  unfold lp_pair.
  replace (2 * Datatypes.S m)%nat with (2 * m + 2)%nat by lia.
  replace (2 * m + 2 + 1)%nat with (2 * m + 3)%nat by lia.
  apply Qeq_refl.
Qed.

(** Scaling invariant: [lp_odd m <= lp_a 0 - lp_a (2m+1)]. *)
Lemma pa_lp_odd_inv : forall m : nat, Qle (lp_odd m) (lp_a 0 - lp_a (2 * m + 1)).
Proof.
  intro m.
  induction m as [| p IH].
  - change (lp_odd 0) with (lp_pair 0).
    unfold lp_pair.
    apply Qle_refl.
  - replace (2 * Datatypes.S p + 1)%nat with (2 * p + 3)%nat by lia.
    apply (Qle_trans _ ((lp_a 0 - lp_a (2 * p + 1)) + lp_pair (Datatypes.S p)) _).
    + apply Qplus_le_compat; [exact IH | apply Qle_refl].
    + apply (Qle_trans _ ((lp_a 0 - lp_a (2 * p + 1)) + (lp_a (2 * p + 2) - lp_a (2 * p + 3))) _).
      * apply Qplus_le_compat.
        { apply Qle_refl. }
        { apply (pa_le_qeq_r (lp_pair (Datatypes.S p)) (lp_pair (Datatypes.S p))
                   (lp_a (2 * p + 2) - lp_a (2 * p + 3))).
          { apply Qle_refl. }
          { apply pa_lp_pair_S. } }
      * apply (Qle_trans _ ((lp_a 0 - lp_a (2 * p + 2)) + (lp_a (2 * p + 2) - lp_a (2 * p + 3))) _).
        { apply Qplus_le_compat.
          { apply (pa_Qminus_le (lp_a 0) (lp_a (2 * p + 2)) (lp_a (2 * p + 1))).
            apply (sc_lpa_decr_le (2 * p + 1) (2 * p + 2)). lia. }
          { apply Qle_refl. } }
        { assert (Hfold : lp_a 0 - lp_a (2 * p + 2) + (lp_a (2 * p + 2) - lp_a (2 * p + 3)) == lp_a 0 - lp_a (2 * p + 3)) by field.
          apply (pa_le_qeq_r
                   ((lp_a 0 - lp_a (2 * p + 2)) + (lp_a (2 * p + 2) - lp_a (2 * p + 3)))
                   ((lp_a 0 - lp_a (2 * p + 2)) + (lp_a (2 * p + 2) - lp_a (2 * p + 3)))
                   (lp_a 0 - lp_a (2 * p + 3))).
          { apply Qle_refl. }
          { exact Hfold. } }
Qed.

Lemma pa_lp_a_0_one : lp_a 0 == 1.
Proof.
  rewrite pa_lp_a_val.
  reflexivity.
Qed.

(** Scaling band: [lp_odd m <= 1]. *)
Lemma pa_lp_odd_le_1 : forall m : nat, Qle (lp_odd m) 1.
Proof.
  intro m.
  apply (Qle_trans _ (lp_a 0 - lp_a (2 * m + 1)) _).
  - apply pa_lp_odd_inv.
  - apply (Qle_trans _ (lp_a 0 - 0) _).
    + apply (pa_Qminus_le (lp_a 0) 0 (lp_a (2 * m + 1))).
      apply Qlt_le_weak.
      apply (pa_lpa_pos (2 * m + 1)).
    + apply qeq_le.
      rewrite pa_lp_a_0_one.
      ring.
Qed.

(** Factorization of the per-pair term (the numerator is balanced
    over the common denominator). *)
Lemma pa_aA_term_split : forall (j : nat) (x : Q),
  aA_term j x ==
  q_pow x (4 * j + 1) * ((Z.of_nat (4 * j + 3) # 1) - (Z.of_nat (4 * j + 1) # 1) * (x * x))
    * (/ (Z.of_nat (4 * j + 1) # 1)) * (/ (Z.of_nat (4 * j + 3) # 1)).
Proof.
  intros j x.
  assert (Ha : ~ ((Z.of_nat (4 * j + 1) # 1) == 0)%Q).
  { apply pa_qpos_neq0.
    replace (4 * j + 1)%nat with (2 * (2 * j) + 1)%nat by lia.
    apply (q_lt_0_odd_den (2 * j)). }
  assert (Hb : ~ ((Z.of_nat (4 * j + 3) # 1) == 0)%Q).
  { apply pa_qpos_neq0.
    replace (4 * j + 3)%nat with (2 * (2 * j + 1) + 1)%nat by lia.
    apply (q_lt_0_odd_den (2 * j + 1)). }
  unfold aA_term.
  rewrite pa_lp_a_val.
  rewrite (pa_lp_a_val (2 * j + 1)).
  replace (2 * (2 * j) + 1)%nat with (4 * j + 1)%nat by lia.
  replace (2 * (2 * j + 1) + 1)%nat with (4 * j + 3)%nat by lia.
  assert (Hq : q_pow x (4 * j + 3) == q_pow x (4 * j + 1) * (x * x)).
  { replace (4 * j + 3)%nat with (4 * j + 1 + 2)%nat by lia.
    rewrite pa_qpow_add2.
    ring. }
  rewrite Hq.
  field; split; assumption.
Qed.

Lemma pa_aA_term_nonneg : forall (j : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> Qle 0 (aA_term j x).
Proof.
  intros j x H0 H1.
  assert (H01 : Qle 0 1) by (unfold Qle; simpl; lia).
  assert (Hx2 : Qle (x * x) 1).
  { apply (Qle_trans _ (x * 1%Q) _).
    - apply (pa_Qmult_le_l x 1%Q x); assumption.
    - apply (Qle_trans _ (1%Q * 1%Q) _).
      + apply (Qmult_le_compat_r x 1 1 H1 H01).
      + apply qeq_le. ring. }
  assert (HB1pos : Qle 0 (Z.of_nat (4 * j + 1) # 1))
    by (unfold Qle; simpl; lia).
  assert (HdB1 : Qle ((Z.of_nat (4 * j + 1) # 1) * (x * x)) ((Z.of_nat (4 * j + 3) # 1))).
  { apply (Qle_trans _ ((Z.of_nat (4 * j + 1) # 1) * 1%Q) _).
    - apply (pa_Qmult_le_l (x * x) 1%Q (Z.of_nat (4 * j + 1) # 1)%Q); [exact Hx2 | exact HB1pos].
    - apply (Qle_trans _ (Z.of_nat (4 * j + 1) # 1)%Q _).
      + apply qeq_le. ring.
      + unfold Qle; simpl; lia. }
  assert (Hdpos : Qle 0 ((Z.of_nat (4 * j + 3) # 1) - (Z.of_nat (4 * j + 1) # 1) * (x * x))).
  { apply (Qle_trans _ ((Z.of_nat (4 * j + 3) # 1) - (Z.of_nat (4 * j + 3) # 1)) _).
    - apply qeq_le. ring.
    - apply (pa_Qminus_le (Z.of_nat (4 * j + 3) # 1)%Q
               ((Z.of_nat (4 * j + 1) # 1) * (x * x))
               (Z.of_nat (4 * j + 3) # 1)%Q).
      exact HdB1. }
  rewrite pa_aA_term_split.
  apply (Qmult_le_0_compat
    (q_pow x (4 * j + 1)
      * ((Z.of_nat (4 * j + 3) # 1) - (Z.of_nat (4 * j + 1) # 1) * (x * x))
      * (/ (Z.of_nat (4 * j + 1) # 1)))
    ((/ (Z.of_nat (4 * j + 3) # 1)))).
  { apply (Qmult_le_0_compat
      (q_pow x (4 * j + 1)
        * ((Z.of_nat (4 * j + 3) # 1) - (Z.of_nat (4 * j + 1) # 1) * (x * x)))
      ((/ (Z.of_nat (4 * j + 1) # 1)))).
    { apply (Qmult_le_0_compat (q_pow x (4 * j + 1))
        ((Z.of_nat (4 * j + 3) # 1) - (Z.of_nat (4 * j + 1) # 1) * (x * x))).
      - apply (q_pow_nonneg x (4 * j + 1) H0).
      - exact Hdpos. }
    { apply Qlt_le_weak.
      apply Qinv_lt_0_compat.
      replace (4 * j + 1)%nat with (2 * (2 * j) + 1)%nat by lia.
      apply (q_lt_0_odd_den (2 * j)). } }
  { apply Qlt_le_weak.
    apply Qinv_lt_0_compat.
    replace (4 * j + 3)%nat with (2 * (2 * j + 1) + 1)%nat by lia.
    apply (q_lt_0_odd_den (2 * j + 1)). }
Qed.

Lemma pa_aA_nonneg : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> Qle 0 (aA m x).
Proof.
  intros m x H0 H1.
  induction m as [| p IH].
  - apply (pa_aA_term_nonneg 0 x H0 H1).
  - change (aA (Datatypes.S p) x) with (aA p x + aA_term (Datatypes.S p) x).
    apply (Qplus_le_compat 0%Q (aA p x) 0%Q (aA_term (Datatypes.S p) x)).
    + exact IH.
    + apply (pa_aA_term_nonneg (Datatypes.S p) x H0 H1).
Qed.

(* ================= Section 3. The core geometric identity ================= *)

Lemma pa_gG_term_x2 : forall (j : nat) (x : Q),
  (1 + x * x) * aG_term j x == q_pow x (4 * j) - q_pow x (4 * j + 4).
Proof.
  intros j x.
  unfold aG_term.
  assert (H2 : q_pow x (4 * j + 2) == q_pow x (4 * j) * x * x)
    by (apply (pa_qpow_add2 x (4 * j))).
  assert (H4 : q_pow x (4 * j + 4) == q_pow x (4 * j) * x * x * x * x).
  { replace (4 * j + 4)%nat with ((4 * j + 2) + 2)%nat by lia.
    rewrite pa_qpow_add2.
    rewrite H2.
    ring. }
  rewrite H2.
  rewrite H4.
  ring.
Qed.

(** The core geometric identity:
    [(1 + x^2) * G_m(x) == 1 - x^{4m+4}]. *)
Lemma gG_one_x2 : forall (m : nat) (x : Q),
  (1 + x * x) * aG m x == 1 - q_pow x (4 * m + 4).
Proof.
  intros m x.
  induction m as [| p IH].
  - change (aG 0 x) with (aG_term 0 x).
    rewrite pa_gG_term_x2.
    replace (4 * 0)%nat with 0%nat by lia.
    rewrite pa_qpow_0.
    ring.
  - replace (4 * Datatypes.S p + 4)%nat with (4 * p + 8)%nat by lia.
    change (aG (Datatypes.S p) x) with (aG p x + aG_term (Datatypes.S p) x).
    assert (Hd : (1 + x * x) * (aG p x + aG_term (Datatypes.S p) x)
                 == (1 + x * x) * aG p x + (1 + x * x) * aG_term (Datatypes.S p) x) by ring.
    rewrite Hd.
    rewrite IH.
    rewrite pa_gG_term_x2.
    replace (4 * Datatypes.S p)%nat with (4 * p + 4)%nat by lia.
    replace (4 * p + 4 + 4)%nat with (4 * p + 8)%nat by lia.
    ring.
Qed.

(* ================= Section 3b. The termwise sharp band for [aA] (supply for the step bookkeeping) ================= *)

Lemma pa_qpow_1 : forall x : Q, q_pow x 1 == x.
Proof.
  intro x.
  change (q_pow x 1) with (x * q_pow x 0).
  rewrite pa_qpow_0.
  ring.
Qed.

(** Per-pair term bounded by the paired final value ([x] in [0,1]).
    Route (a difference-form coupling chain):
    [lp_pair j - aA_term j x == (1/A1) * a - (1/A3) * b] with
    [a := 1 - x^{4j+1}], [b := 1 - x^{4j+3}], [A1 := (4j+1)#1] and
    [A3 := (4j+3)#1]; after multiplying by [A1 * A3 > 0] this becomes
    [A3 * a - A1 * b == (1+1) * a - A1 * x^{4j+1} * (1 - x^2)], and
    [A1 * x^{4j+1} * (1 - x^2) = A1 * x^{4j+1} * (1 - x) * (1 + x)
    <= (1+1) * (1 - x) * A1 * x^{4j+1} <= (1+1) * (1 - x) * A1 * x^{4j}
    <= (1+1) * (1 - x) * gsum (4j+1) x 1 == (1+1) * a]
    (using [1 + x <= 1 + 1], [x^{4j+1} <= x^{4j}], [pa_gsum_lower] and
    [pa_pow_diff]). *)
Lemma pa_aA_term_le_lp_pair : forall (j : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> Qle (aA_term j x) (lp_pair j).
Proof.
  intros j x H0 H1.
  assert (H01 : Qle 0 1) by (unfold Qle; simpl; lia).
  assert (H1m : Qle 0 (1 - x)%Q) by (apply leibsep_qle_minus; exact H1).
  assert (HA1pos : Qlt 0 (Z.of_nat (4*j+1) # 1)%Q).
  { replace (4*j+1)%nat with (2*(2*j)+1)%nat by lia.
    apply (q_lt_0_odd_den (2*j)). }
  assert (HA3pos : Qlt 0 (Z.of_nat (4*j+3) # 1)%Q).
  { replace (4*j+3)%nat with (2*(2*j+1)+1)%nat by lia.
    apply (q_lt_0_odd_den (2*j+1)). }
  assert (Hxa : Qle (q_pow x (4*j+1)) (q_pow x (4*j))).
  { rewrite (pa_qpow_add x (4*j) 1), pa_qpow_1.
    apply (pa_le_qeq_r (q_pow x (4*j) * x) (q_pow x (4*j) * 1%Q) (q_pow x (4*j))).
    - apply (pa_Qmult_le_l x 1%Q (q_pow x (4*j)));
        [exact H1 | apply (q_pow_nonneg x (4*j) H0)].
    - apply Qmult_1_r. }
  assert (Hq43 : q_pow x (4*j+3) == q_pow x (4*j+1) * (x*x)%Q).
  { replace (4*j+3)%nat with (4*j+1+2)%nat by lia.
    rewrite pa_qpow_add2.
    ring. }
(* Key step: [(1+1) * a - A1 * x^{4j+1} * (1 - x^2) >= 0]. *)
  assert (Hstep : Qle ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1) * (1 - x*x)%Q)
                      ((1 + 1)%Q * (1 - q_pow x (4*j+1)))).
  { assert (Honele : Qle (1 + x)%Q (1 + 1)%Q)
      by (apply (Qplus_le_compat 1%Q 1%Q x 1%Q); [apply Qle_refl | exact H1]).
    assert (Hw1 : Qle 0 ((1 + 1)%Q * (1 - x)%Q))
      by (apply Qmult_le_0_compat; [unfold Qle; simpl; lia | exact H1m]).
    assert (Hw2 : Qle 0 ((1 - x)%Q * (1 + 1)%Q))
      by (apply Qmult_le_0_compat; [exact H1m | unfold Qle; simpl; lia]).
    assert (HA1le : Qle ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1))
                        ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j)))
      by (apply (pa_Qmult_le_l (q_pow x (4*j+1)) (q_pow x (4*j))
                   (Z.of_nat (4*j+1) # 1)%Q);
             [exact Hxa | apply Qlt_le_weak; exact HA1pos]).
    assert (Hpd : (1 - x)%Q * gsum (4*j+1) x 1 == 1%Q - q_pow x (4*j+1)).
    { rewrite <- (pa_pow_diff (4*j+1) x 1).
      rewrite (sc_q_pow_one (4*j+1)).
      reflexivity. }
    apply (Qle_trans _ (((1 - x)%Q * (1 + 1)%Q) * ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j))) _).
    - apply (Qle_trans _ ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1) * ((1 - x)%Q * (1 + 1)%Q)) _).
      { apply (Qle_trans _ ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1) * ((1 - x)%Q * (1 + x)%Q)) _).
        { apply qeq_le. ring. }
        { apply (pa_Qmult_le_l
                   ((1 - x)%Q * (1 + x)%Q)
                   ((1 - x)%Q * (1 + 1)%Q)
                   ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1))).
          { apply (pa_Qmult_le_l (1 + x)%Q (1 + 1)%Q (1 - x)%Q);
              [exact Honele | exact H1m]. }
          { apply Qmult_le_0_compat;
              [apply Qlt_le_weak; exact HA1pos | apply (q_pow_nonneg x (4*j+1) H0)]. } } }
      { apply (Qle_trans _ (((1 - x)%Q * (1 + 1)%Q) * ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1))) _).
        { apply qeq_le. ring. }
        { apply (pa_Qmult_le_l
                   ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1))
                   ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j))
                   ((1 - x)%Q * (1 + 1)%Q)); [exact HA1le | exact Hw2]. } }
    - apply (Qle_trans _ ((1 + 1)%Q * (1 - x)%Q * (gsum (4*j+1) x 1)) _).
      { apply (Qle_trans _ ((1 + 1)%Q * (1 - x)%Q * ((Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j))) _).
        { apply qeq_le. ring. }
        { pose proof (pa_gsum_lower (4*j) x 1 H0 H01 H1) as Hgl.
          replace (Datatypes.S (4*j)) with (4*j+1)%nat in Hgl by lia.
          apply (pa_Qmult_le_l _ _ ((1 + 1)%Q * (1 - x)%Q)); [exact Hgl | exact Hw1]. } }
      { apply (pa_le_qeq_r
          ((1 + 1)%Q * (1 - x)%Q * (gsum (4*j+1) x 1))
          ((1 + 1)%Q * (1 - x)%Q * (gsum (4*j+1) x 1))
          ((1 + 1)%Q * (1 - q_pow x (4*j+1)))).
        { apply Qle_refl. }
        { assert (Hfin2 : (1 + 1)%Q * (1 - x)%Q * gsum (4*j+1) x 1
                          == (1 + 1)%Q * (1 - q_pow x (4*j+1))%Q).
          { rewrite <- Qmult_assoc.
            rewrite Hpd.
            reflexivity. }
          exact Hfin2. } } }
(* The difference form is >= 0 in two stages: from the scaled form
   back to the original form. *)
  assert (HRp : Qle 0 ((1 + 1)%Q * (1 - q_pow x (4*j+1))
                       - (Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1) * (1 - x*x)%Q))
    by (apply leibsep_qle_minus; exact Hstep).
  assert (HRp' : Qle 0 ((Z.of_nat (4*j+3) # 1)%Q * (1 - q_pow x (4*j+1))
                        - (Z.of_nat (4*j+1) # 1)%Q * (1 - q_pow x (4*j+3)))).
  { apply (pa_le_qeq_r 0%Q
             ((1 + 1)%Q * (1 - q_pow x (4*j+1))
              - (Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1) * (1 - x*x)%Q) _).
    - exact HRp.
    - assert (Hid : (Z.of_nat (4*j+3) # 1)%Q * (1 - q_pow x (4*j+1))
                    - (Z.of_nat (4*j+1) # 1)%Q * (1 - q_pow x (4*j+3))
                    == (1 + 1)%Q * (1 - q_pow x (4*j+1))
                       - (Z.of_nat (4*j+1) # 1)%Q * q_pow x (4*j+1) * (1 - x*x)%Q).
      { assert (HA1A3 : (Z.of_nat (4*j+3) # 1)%Q
                        == (Z.of_nat (4*j+1) # 1)%Q + (1 + 1)%Q).
        { replace (4*j+3)%nat with (4*j+1+2)%nat by lia.
          rewrite Nat2Z.inj_add.
          unfold Qeq; simpl; lia. }
        rewrite HA1A3.
        rewrite Hq43.
        ring. }
      apply Qeq_sym.
      exact Hid. }
  assert (HA1ne : ~ ((Z.of_nat (4*j+1) # 1)%Q == 0)%Q).
  { apply pa_qpos_neq0.
    replace (4*j+1)%nat with (2*(2*j)+1)%nat by lia.
    apply (q_lt_0_odd_den (2*j)). }
  assert (HA3ne : ~ ((Z.of_nat (4*j+3) # 1)%Q == 0)%Q).
  { apply pa_qpos_neq0.
    replace (4*j+3)%nat with (2*(2*j+1)+1)%nat by lia.
    apply (q_lt_0_odd_den (2*j+1)). }
  assert (Hscale : (Z.of_nat (4*j+1) # 1)%Q * (Z.of_nat (4*j+3) # 1)%Q
                   * (lp_pair j - aA_term j x)
                   == (Z.of_nat (4*j+3) # 1)%Q * (1 - q_pow x (4*j+1))
                      - (Z.of_nat (4*j+1) # 1)%Q * (1 - q_pow x (4*j+3))).
  { unfold lp_pair, aA_term.
    rewrite (pa_lp_a_val (2*j)). rewrite (pa_lp_a_val (2*j+1)).
    replace (2*(2*j)+1)%nat with (4*j+1)%nat by lia.
    replace (2*(2*j+1)+1)%nat with (4*j+3)%nat by lia.
    field; split; assumption. }
  assert (HRpos : Qle 0 ((Z.of_nat (4*j+1) # 1)%Q * (Z.of_nat (4*j+3) # 1)%Q
                   * (lp_pair j - aA_term j x))).
  { apply (pa_le_qeq_r 0%Q
             ((Z.of_nat (4*j+3) # 1)%Q * (1 - q_pow x (4*j+1))
              - (Z.of_nat (4*j+1) # 1)%Q * (1 - q_pow x (4*j+3))) _);
     [exact HRp' | apply Qeq_sym; exact Hscale]. }
  assert (Hinvpos : Qle 0 ((/ (Z.of_nat (4*j+1) # 1))%Q * (/ (Z.of_nat (4*j+3) # 1))%Q)).
  { apply Qmult_le_0_compat;
      [apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HA1pos
      |apply Qlt_le_weak; apply Qinv_lt_0_compat; exact HA3pos]. }
  assert (HRfinal : Qle 0 (lp_pair j - aA_term j x)).
  { assert (Hm : Qle 0 (((Z.of_nat (4*j+1) # 1)%Q * (Z.of_nat (4*j+3) # 1)%Q
                          * (lp_pair j - aA_term j x))
                        * ((/ (Z.of_nat (4*j+1) # 1))%Q * (/ (Z.of_nat (4*j+3) # 1))%Q)))
      by (apply Qmult_le_0_compat; [exact HRpos | exact Hinvpos]).
    apply (pa_le_qeq_r 0%Q
             (((Z.of_nat (4*j+1) # 1)%Q * (Z.of_nat (4*j+3) # 1)%Q
               * (lp_pair j - aA_term j x))
              * ((/ (Z.of_nat (4*j+1) # 1))%Q * (/ (Z.of_nat (4*j+3) # 1))%Q)) _);
       [exact Hm
       | field; split;
          [ intros Hc; apply HA3ne; exact Hc
          | intros Hc; apply HA1ne; exact Hc ]]. }
  apply leibsep_qle_of_minus.
  exact HRfinal.
Qed.

(* ================= Section 3c. The forward-difference bound family
   (stepping supply, one-sided upper-bound form) ================= *)

(** Basic lemmas on powers of two. *)
Lemma pa_two_pow_S : forall n : nat, (2 ^ Datatypes.S n = 2 * 2 ^ n)%nat.
Proof.
  intro n.
  simpl.
  lia.
Qed.

Lemma pa_two_pow_ge : forall n : nat, (Datatypes.S n <= 2 ^ n)%nat.
Proof.
  intro n.
  induction n as [| p IH].
  - simpl. lia.
  - rewrite pa_two_pow_S.
    lia.
Qed.

(** The recursion bound constant [E_q := 2^{q+1} - (q+1) - 1] (it
    exactly satisfies [E_{q+1} = 2 * E_q + (q+1)]). *)
Definition pa_E (q : nat) : Q :=
  ((Z.of_nat ((2 ^ (Datatypes.S q))%nat) # 1)
   - (Z.of_nat (Datatypes.S q) # 1) - 1)%Q.

(** Scaling of powers: [0 <= y <= 1] implies [y^q <= 1]. *)
Lemma pa_qpow_le_one : forall (q : nat) (y : Q),
  Qle 0 y -> Qle y 1 -> Qle (q_pow y q) 1.
Proof.
  intros q y H0 H1.
  induction q as [| p IH].
  - rewrite pa_qpow_0. apply Qle_refl.
  - change (q_pow y (Datatypes.S p)) with (y * q_pow y p).
    apply (Qle_trans _ (y * 1%Q) _).
    + apply (pa_Qmult_le_l (q_pow y p) 1%Q y); [exact IH | exact H0].
    + apply (Qle_trans _ y 1%Q);
        [apply qeq_le; apply Qmult_1_r | exact H1].
Qed.

(** Nonnegativity of the forward difference: [y, h >= 0] implies
    [(y+h)^{q+1} - y^{q+1} - (q+1) y^q h >= 0]
    (by [pa_pow_diff] and [pa_gsum_lower]:
    [(y+h)^{q+1} - y^{q+1} == h * gsum >= (q+1) y^q h]). *)
Lemma pa_D_pos : forall (q : nat) (y h : Q),
  Qle 0 y -> Qle 0 h ->
  Qle 0 (q_pow (y + h) (Datatypes.S q) - q_pow y (Datatypes.S q)
         - (Z.of_nat (Datatypes.S q) # 1) * q_pow y q * h).
Proof.
  intros q y h H0 Hh.
  assert (Hyh : Qle 0 (y + h)) by (apply (Qplus_le_compat 0 y 0 h); assumption).
  assert (Hyhy : Qle y (y + h)).
  { apply (Qle_trans _ (y + 0%Q) _).
    - apply qeq_le. ring.
    - apply Qplus_le_compat; [apply Qle_refl | exact Hh]. }
  rewrite (pa_pow_diff (Datatypes.S q) y (y + h)).
  assert (Hhy : ((y + h) - y)%Q == h%Q) by ring.
  rewrite Hhy.
  assert (Hgl := pa_gsum_lower q y (y + h) H0 Hyh Hyhy).
  assert (Hmul : Qle ((Z.of_nat (Datatypes.S q) # 1) * q_pow y q * h)
                     (h * gsum (Datatypes.S q) y (y + h))).
  { apply (Qle_trans _ (h * ((Z.of_nat (Datatypes.S q) # 1) * q_pow y q)) _).
    - apply qeq_le. ring.
    - apply (pa_Qmult_le_l ((Z.of_nat (Datatypes.S q) # 1) * q_pow y q)
               (gsum (Datatypes.S q) y (y + h)) h); [exact Hgl | exact Hh]. }
  apply leibsep_qle_minus.
  exact Hmul.
Qed.

(* ================= Section 3d. Upper bounds from the difference family (the [E] recursion, stepping supply) ================= *)

(** [lp_a <= 1]: from [lp_a k == 1/(2k+1)] and [1 <= 2k+1]. *)
Lemma pa_lpa_le_1 : forall k : nat, Qle (lp_a k) 1.
Proof.
  intro k.
  rewrite pa_lp_a_val.
  assert (Hd : Qle 1 ((Z.of_nat (2*k+1) # 1)%Q)) by (unfold Qle; simpl; lia).
  assert (Hdpos : Qlt 0 ((Z.of_nat (2*k+1) # 1)%Q)) by (unfold Qlt; simpl; lia).
  apply (Qle_trans _ ((/ (Z.of_nat (2*k+1) # 1))%Q * 1%Q) _).
  - apply qeq_le. ring.
  - apply (pa_le_qeq_r _ ((/ (Z.of_nat (2*k+1) # 1))%Q * (Z.of_nat (2*k+1) # 1)%Q) _).
    + apply (pa_Qmult_le_l 1%Q (Z.of_nat (2*k+1) # 1)%Q (/ (Z.of_nat (2*k+1) # 1))).
      * exact Hd.
      * apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hdpos.
    + rewrite Qmult_comm.
      apply Qmult_inv_r.
      apply pa_qpos_neq0.
      exact Hdpos.
Qed.

(** Upper bound for [E]: [pa_E q <= 2^{q+1}]. *)
Lemma pa_E_le : forall q : nat,
  Qle (pa_E q) ((Z.of_nat (2 ^ (Datatypes.S q))%nat # 1)%Q).
Proof.
  intro q.
  unfold pa_E.
  unfold Qle; simpl; lia.
Qed.

(** Nonnegativity of [E]: [2^{q+1} > q+1]. *)
Lemma pa_E_pos : forall q : nat, Qle 0 (pa_E q).
Proof.
  intro q.
  unfold pa_E.
  assert (Hn : (Datatypes.S q < 2 * 2 ^ q)%nat).
  { assert (Hg := pa_two_pow_ge q).
    lia. }
  assert (HZ : (Z.of_nat (Datatypes.S q) < Z.of_nat (2 * 2 ^ q))%Z)
    by (apply Nat2Z.inj_lt; exact Hn).
  unfold Qle; simpl; lia.
Qed.

(** The [E] recursion: [pa_E (S q) == 2 * pa_E q + (S q)#1]. *)
Lemma pa_E_step : forall q : nat,
  pa_E (Datatypes.S q) == 2%Q * pa_E q + (Z.of_nat (Datatypes.S q) # 1)%Q.
Proof.
  intro q.
  unfold pa_E.
  replace (2 ^ Datatypes.S (Datatypes.S q))%nat
    with (2 * 2 ^ Datatypes.S q)%nat by (rewrite pa_two_pow_S; reflexivity).
  change (Datatypes.S (Datatypes.S q)) with (1 + Datatypes.S q)%nat.
  rewrite Nat2Z.inj_add.
  unfold Qeq.
  cbn [Qnum Qden Qminus Qplus Qmult Qopp].
  lia.
Qed.

(** Forward-difference upper bound: [0 <= y <= 1] and [0 <= h <= 1]
    imply [D_{S q} <= pa_E q * h^2]
    (by the recursion
    [D_{S(S q)} == (y+h) * D_{S q} + h * ((S q)#1 * y^q * h) - y^{S q} * h],
    whose last term is nonnegative and dropped; [y+h <= 2] and
    [y^q <= 1], balanced with the [pa_E] recursion). *)
Lemma pa_D_le : forall (q : nat) (y h : Q),
  Qle 0 y -> Qle y 1 -> Qle 0 h -> Qle h 1 ->
  Qle (q_pow (y + h) (Datatypes.S q) - q_pow y (Datatypes.S q)
       - (Z.of_nat (Datatypes.S q) # 1) * q_pow y q * h)
      (pa_E q * (h * h)).
Proof.
  intro q.
  induction q as [| p IH].
  - intros y h H0 H1 Hh Hh1.
    rewrite (pa_qpow_1 (y + h)).
    rewrite (pa_qpow_1 y).
    rewrite pa_qpow_0.
    assert (H1c : (Z.of_nat (Datatypes.S 0) # 1)%Q == 1%Q) by apply Qeq_refl.
    rewrite H1c.
    assert (HD : (y + h - y - 1%Q * 1%Q * h)%Q == 0%Q) by ring.
    assert (HE0 : pa_E 0 == 0%Q) by (unfold pa_E; reflexivity).
    apply qeq_le.
    rewrite HD.
    rewrite HE0.
    ring.
  - intros y h H0 H1 Hh Hh1.
    change (q_pow (y + h) (Datatypes.S (Datatypes.S p)))
      with ((y + h) * q_pow (y + h) (Datatypes.S p)).
    change (q_pow y (Datatypes.S (Datatypes.S p)))
      with (y * q_pow y (Datatypes.S p)).
    change (q_pow y (Datatypes.S p)) with (y * q_pow y p).
    assert (Hz : (Z.of_nat (Datatypes.S (Datatypes.S p)) # 1)%Q
                 == ((Z.of_nat (Datatypes.S p) # 1) + 1)%Q) by apply pa_zsucc_qmake.
    rewrite Hz.
    assert (Hcore : ((y + h) * q_pow (y + h) (Datatypes.S p)
                     - y * (y * q_pow y p)
                     - ((Z.of_nat (Datatypes.S p) # 1)%Q + 1) * (y * q_pow y p) * h)
                    == (y + h) * (q_pow (y + h) (Datatypes.S p)
                                  - y * q_pow y p
                                  - (Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p * h)
                    + (Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p * h * h) by ring.
    rewrite Hcore.
    assert (Hyh : Qle 0 (y + h)) by (apply (Qplus_le_compat 0 y 0 h); assumption).
    assert (Hyh2 : Qle (y + h) 2%Q).
    { apply (Qle_trans _ (1%Q + 1%Q) _).
      - apply Qplus_le_compat; [exact H1 | exact Hh1].
      - apply qeq_le. ring. }
    assert (Hhh : Qle 0 (h * h)) by exact (Qmult_le_0_compat h h Hh Hh).
    assert (HXpos : Qle 0 (pa_E p * (h * h)))
      by exact (Qmult_le_0_compat (pa_E p) (h * h) (pa_E_pos p) Hhh).
    assert (HT0 : Qle 0 ((Z.of_nat (Datatypes.S p) # 1)%Q)) by (unfold Qle; simpl; lia).
    assert (Hyy1 : Qle (q_pow y p) 1) by exact (pa_qpow_le_one p y H0 H1).
    assert (HT : Qle ((Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p)
                     ((Z.of_nat (Datatypes.S p) # 1)%Q * 1%Q))
      by exact (pa_Qmult_le_l (q_pow y p) 1%Q (Z.of_nat (Datatypes.S p) # 1)%Q Hyy1 HT0).
    assert (HT2 : Qle ((Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p)
                      ((Z.of_nat (Datatypes.S p) # 1)%Q))
      by (apply (pa_le_qeq_r _ ((Z.of_nat (Datatypes.S p) # 1)%Q * 1%Q) _);
          [exact HT | ring]).
    assert (Hsum2 : Qle ((Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p * h * h)
                        ((h * h) * (Z.of_nat (Datatypes.S p) # 1)%Q)).
    { apply (Qle_trans _ ((h * h) * ((Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p)) _).
      - apply qeq_le. ring.
      - exact (pa_Qmult_le_l ((Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p)
                 ((Z.of_nat (Datatypes.S p) # 1)%Q) (h * h) HT2 Hhh). }
    assert (HP1 : Qle ((y + h) * (q_pow (y + h) (Datatypes.S p)
                                 - q_pow y (Datatypes.S p)
                                 - (Z.of_nat (Datatypes.S p) # 1) * q_pow y p * h))
                      ((pa_E p * (h * h)) * 2%Q)).
    { apply (Qle_trans _ ((y + h) * (pa_E p * (h * h))) _).
      - exact (pa_Qmult_le_l (q_pow (y + h) (Datatypes.S p)
                                - q_pow y (Datatypes.S p)
                                - (Z.of_nat (Datatypes.S p) # 1) * q_pow y p * h)
                 (pa_E p * (h * h)) (y + h) (IH y h H0 H1 Hh Hh1) Hyh).
      - apply (Qle_trans _ ((pa_E p * (h * h)) * (y + h)) _).
        + apply qeq_le. ring.
        + exact (pa_Qmult_le_l (y + h) 2%Q (pa_E p * (h * h)) Hyh2 HXpos). }
    apply (pa_le_qeq_r
             _ ((pa_E p * (h * h)) * 2%Q
                + (h * h) * (Z.of_nat (Datatypes.S p) # 1)%Q) _).
    + apply Qplus_le_compat; [exact HP1 | exact Hsum2].
    + rewrite pa_E_step.
      ring.
Qed.

(* ================= Section 3e. The step envelope (per-j difference identities and the 2^{4m+4} band) ================= *)

(** The per-j differences:
    [D1 := (x+h)^{S(4j)} - x^{S(4j)} - (S(4j))#1 * x^{4j} * h] and
    [D3] of the same shape at [4j+2] (the [S]-forms align verbatim
    with the consumption forms of the Section 3c nonnegativity and
    upper-bound lemmas). *)
Definition pa_D1 (j : nat) (x h : Q) : Q :=
  q_pow (x + h) (Datatypes.S (4 * j)) - q_pow x (Datatypes.S (4 * j))
  - (Z.of_nat (Datatypes.S (4 * j)) # 1) * q_pow x (4 * j) * h.

Definition pa_D3 (j : nat) (x h : Q) : Q :=
  q_pow (x + h) (Datatypes.S (4 * j + 2)) - q_pow x (Datatypes.S (4 * j + 2))
  - (Z.of_nat (Datatypes.S (4 * j + 2)) # 1) * q_pow x (4 * j + 2) * h.

(** The per-j identity: the step difference equals
    [lp_a(2j) * D1 - lp_a(2j+1) * D3]
    (a rationalization balanced against [lp_a k == 1/(2k+1)]; the
    nonzero-denominator side goals are discharged by the positivity
    of the odd denominators). *)
Lemma pa_aA_term_step_D : forall (j : nat) (x h : Q),
  aA_term j (x + h) - aA_term j x - aG_term j x * h
  == lp_a (2 * j) * pa_D1 j x h - lp_a (2 * j + 1) * pa_D3 j x h.
Proof.
  intros j x h.
  unfold aA_term, aG_term.
  rewrite (pa_lp_a_val (2 * j)).
  rewrite (pa_lp_a_val (2 * j + 1)).
  replace (2 * (2 * j) + 1)%nat with (4 * j + 1)%nat by lia.
  replace (2 * (2 * j + 1) + 1)%nat with (4 * j + 3)%nat by lia.
  unfold pa_D1, pa_D3.
  replace (Datatypes.S (4 * j))%nat with (4 * j + 1)%nat by lia.
  replace (Datatypes.S (4 * j + 2))%nat with (4 * j + 3)%nat by lia.
  assert (HA1ne : ~ ((Z.of_nat (4 * j + 1) # 1)%Q == 0)%Q).
  { apply pa_qpos_neq0.
    replace (4 * j + 1)%nat with (2 * (2 * j) + 1)%nat by lia.
    apply (q_lt_0_odd_den (2 * j)). }
  assert (HA3ne : ~ ((Z.of_nat (4 * j + 3) # 1)%Q == 0)%Q).
  { apply pa_qpos_neq0.
    replace (4 * j + 3)%nat with (2 * (2 * j + 1) + 1)%nat by lia.
    apply (q_lt_0_odd_den (2 * j + 1)). }
  field; split; assumption.
Qed.

(** Per-j upper bound: [Delta_j <= 2^{4j+3}#1 * h^2]
    (the [- lp_a(2j+1) * D3] term is dropped since [D3 >= 0];
    [lp_a(2j) * D1 <= lp_a(2j) * 2^{S(4j)}#1 * h^2] holds via
    [lp_a(2j) <= 1], then is scaled up by 4 into [2^{4j+3}]). *)
Lemma pa_aA_term_step_le : forall (j : nat) (x h : Q),
  Qle 0 x -> Qle x 1 -> Qle 0 h -> Qle h 1 ->
  Qle (aA_term j (x + h) - aA_term j x - aG_term j x * h)
      ((Z.of_nat (2 ^ (4 * j + 3))%nat # 1) * (h * h)).
Proof.
  intros j x h H0 H1 Hh Hh1.
  assert (Hhh0 : Qle 0 (h * h)) by exact (Qmult_le_0_compat h h Hh Hh).
  assert (Hpos3 : Qle 0 (lp_a (2 * j + 1) * pa_D3 j x h)).
  { apply Qmult_le_0_compat.
    - apply Qlt_le_weak. exact (pa_lpa_pos (2 * j + 1)).
    - unfold pa_D3. exact (pa_D_pos (4 * j + 2) x h H0 Hh). }
  rewrite (pa_aA_term_step_D j x h).
  apply (Qle_trans _ (lp_a (2 * j) * pa_D1 j x h) _).
  - apply (pa_le_qeq_r (lp_a (2 * j) * pa_D1 j x h - lp_a (2 * j + 1) * pa_D3 j x h)
             (lp_a (2 * j) * pa_D1 j x h - 0%Q) (lp_a (2 * j) * pa_D1 j x h)).
    + apply (pa_Qminus_le (lp_a (2 * j) * pa_D1 j x h) 0%Q
               (lp_a (2 * j + 1) * pa_D3 j x h)).
      exact Hpos3.
    + ring.
  - assert (Hpow : (2 ^ (Datatypes.S (4 * j)) * 4 = 2 ^ (4 * j + 3))%nat).
    { replace (4 * j + 3)%nat with (Datatypes.S (4 * j) + 2)%nat by lia.
      rewrite Nat.pow_add_r. reflexivity. }
    assert (Hsq : Qle ((Z.of_nat (2 ^ (Datatypes.S (4 * j)))%nat # 1))
                       ((Z.of_nat (2 ^ (4 * j + 3))%nat # 1))).
    { replace (2 ^ (4 * j + 3))%nat with (2 ^ (Datatypes.S (4 * j)) * 4)%nat
        by (rewrite <- Hpow; reflexivity).
      unfold Qle. simpl. lia. }
    apply (Qle_trans _ (lp_a (2 * j)
                          * ((Z.of_nat (2 ^ (Datatypes.S (4 * j)))%nat # 1) * (h * h))) _).
    + apply (pa_Qmult_le_l (pa_D1 j x h)
               ((Z.of_nat (2 ^ (Datatypes.S (4 * j)))%nat # 1) * (h * h))
               (lp_a (2 * j))).
      * apply (Qle_trans _ (pa_E (4 * j) * (h * h)) _).
        -- unfold pa_D1. exact (pa_D_le (4 * j) x h H0 H1 Hh Hh1).
        -- apply (Qmult_le_compat_r (pa_E (4 * j))
                     (Z.of_nat (2 ^ (Datatypes.S (4 * j)))%nat # 1) (h * h)).
           ++ exact (pa_E_le (4 * j)).
           ++ exact Hhh0.
      * apply Qlt_le_weak. exact (pa_lpa_pos (2 * j)).
    + apply (Qle_trans _ ((Z.of_nat (2 ^ (Datatypes.S (4 * j)))%nat # 1) * (h * h)) _).
      * apply (pa_le_qeq_r (lp_a (2 * j)
                              * ((Z.of_nat (2 ^ (Datatypes.S (4 * j)))%nat # 1)
                                   * (h * h)))
                 (1%Q * ((Z.of_nat (2 ^ (Datatypes.S (4 * j)))%nat # 1) * (h * h)))
                 ((Z.of_nat (2 ^ (Datatypes.S (4 * j)))%nat # 1) * (h * h))).
        -- apply (Qmult_le_compat_r (lp_a (2 * j)) 1%Q
                     ((Z.of_nat (2 ^ (Datatypes.S (4 * j)))%nat # 1) * (h * h))).
           ++ exact (pa_lpa_le_1 (2 * j)).
           ++ apply Qmult_le_0_compat.
              ** unfold Qle. simpl. lia.
              ** exact Hhh0.
        -- ring.
      * apply (Qmult_le_compat_r _ _ (h * h)); [exact Hsq | exact Hhh0].
Qed.

(** Per-j lower bound (symmetric): [- 2^{4j+3}#1 * h^2 <= Delta_j]
    (the [lp_a(2j) * D1 >= 0] summand is discarded;
    [- lp_a(2j+1) * D3 >= - lp_a(2j+1) * E(4j+2) * h^2
    >= - 2^{S(4j+2)}#1 * h^2 = - 2^{4j+3}#1 * h^2]). *)
Lemma pa_aA_term_step_ge : forall (j : nat) (x h : Q),
  Qle 0 x -> Qle x 1 -> Qle 0 h -> Qle h 1 ->
  Qle ((- (Z.of_nat (2 ^ (4 * j + 3))%nat # 1)) * (h * h))
      (aA_term j (x + h) - aA_term j x - aG_term j x * h).
Proof.
  intros j x h H0 H1 Hh Hh1.
  assert (Hhh0 : Qle 0 (h * h)) by exact (Qmult_le_0_compat h h Hh Hh).
  assert (Hpos1 : Qle 0 (lp_a (2 * j) * pa_D1 j x h)).
  { apply Qmult_le_0_compat.
    - apply Qlt_le_weak. exact (pa_lpa_pos (2 * j)).
    - unfold pa_D1. exact (pa_D_pos (4 * j) x h H0 Hh). }
  assert (Hneg3 : Qle (lp_a (2 * j + 1) * pa_D3 j x h)
                       ((Z.of_nat (2 ^ (4 * j + 3))%nat # 1) * (h * h))).
  { pose proof (pa_E_le (4 * j + 2)) as HEb.
    replace (Datatypes.S (4 * j + 2))%nat with (4 * j + 3)%nat in HEb by lia.
    apply (Qle_trans _ (lp_a (2 * j + 1) * (pa_E (4 * j + 2) * (h * h))) _).
    - apply (pa_Qmult_le_l (pa_D3 j x h) (pa_E (4 * j + 2) * (h * h))
               (lp_a (2 * j + 1))).
      + unfold pa_D3. exact (pa_D_le (4 * j + 2) x h H0 H1 Hh Hh1).
      + apply Qlt_le_weak. exact (pa_lpa_pos (2 * j + 1)).
    - apply (Qle_trans _ (1%Q * (pa_E (4 * j + 2) * (h * h))) _).
      + apply (Qmult_le_compat_r (lp_a (2 * j + 1)) 1%Q
                   (pa_E (4 * j + 2) * (h * h))).
        * exact (pa_lpa_le_1 (2 * j + 1)).
        * apply Qmult_le_0_compat; [exact (pa_E_pos (4 * j + 2)) | exact Hhh0].
      + apply (Qle_trans _ (pa_E (4 * j + 2) * (h * h)) _).
        * apply qeq_le. ring.
        * apply (Qmult_le_compat_r _ _ (h * h)); [exact HEb | exact Hhh0]. }
  rewrite (pa_aA_term_step_D j x h).
  apply (Qle_trans _ (- (lp_a (2 * j + 1) * pa_D3 j x h)) _).
  - apply (Qle_trans _ (- ((Z.of_nat (2 ^ (4 * j + 3))%nat # 1) * (h * h))) _).
    + apply qeq_le. ring.
    + apply Qopp_le_compat. exact Hneg3.
  - change (lp_a (2 * j) * pa_D1 j x h - lp_a (2 * j + 1) * pa_D3 j x h)
      with (lp_a (2 * j) * pa_D1 j x h + - (lp_a (2 * j + 1) * pa_D3 j x h)).
    apply (Qle_trans _ (0%Q + - (lp_a (2 * j + 1) * pa_D3 j x h)) _).
    + apply qeq_le. ring.
    + apply (Qplus_le_compat 0%Q (lp_a (2 * j) * pa_D1 j x h)
               (- (lp_a (2 * j + 1) * pa_D3 j x h))
               (- (lp_a (2 * j + 1) * pa_D3 j x h))).
      * exact Hpos1.
      * apply Qle_refl.
Qed.

(** Envelope step: [Delta_m <= 2^{4m+4}#1 * h^2]
    (induction with [Delta_{Sp} == Delta_p + Deltaterm_{Sp}]; the
    constant bridge [2^{4p+4} + 2^{4p+7} <= 2^{4p+8}]; base case
    [8h^2 <= 16h^2]). *)
Lemma pa_aA_step_le : forall (m : nat) (x h : Q),
  Qle 0 x -> Qle x 1 -> Qle 0 h -> Qle h 1 ->
  Qle (aA m (x + h) - aA m x - aG m x * h)
      ((Z.of_nat (2 ^ (4 * m + 4))%nat # 1) * (h * h)).
Proof.
  intro m.
  induction m as [| p IH].
  - intros x h H0 H1 Hh Hh1.
    change (aA 0%nat (x + h)) with (aA_term 0%nat (x + h)).
    change (aA 0%nat x) with (aA_term 0%nat x).
    change (aG 0%nat x) with (aG_term 0%nat x).
    pose proof (pa_aA_term_step_le 0%nat x h H0 H1 Hh Hh1) as Hj.
    replace (4 * 0 + 3)%nat with 3%nat in Hj by lia.
    replace (2 ^ 3)%nat with 8%nat in Hj by reflexivity.
    replace (4 * 0 + 4)%nat with 4%nat by lia.
    replace (2 ^ 4)%nat with 16%nat by reflexivity.
    apply (Qle_trans _ ((Z.of_nat 8 # 1)%Q * (h * h)) _).
    + exact Hj.
    + apply (Qmult_le_compat_r (Z.of_nat 8 # 1) (Z.of_nat 16 # 1) (h * h)).
      * unfold Qle. simpl. lia.
      * exact (Qmult_le_0_compat h h Hh Hh).
  - intros x h H0 H1 Hh Hh1.
    replace (4 * Datatypes.S p + 4)%nat with (4 * p + 8)%nat by lia.
    assert (Hdecomp : aA (Datatypes.S p) (x + h) - aA (Datatypes.S p) x
                      - aG (Datatypes.S p) x * h
                      == (aA p (x + h) - aA p x - aG p x * h)
                       + (aA_term (Datatypes.S p) (x + h) - aA_term (Datatypes.S p) x
                          - aG_term (Datatypes.S p) x * h)).
    { change (aA (Datatypes.S p) (x + h))
        with (aA p (x + h) + aA_term (Datatypes.S p) (x + h)).
      change (aA (Datatypes.S p) x) with (aA p x + aA_term (Datatypes.S p) x).
      change (aG (Datatypes.S p) x) with (aG p x + aG_term (Datatypes.S p) x).
      ring. }
    rewrite Hdecomp.
    pose proof (IH x h H0 H1 Hh Hh1) as HIH.
    pose proof (pa_aA_term_step_le (Datatypes.S p) x h H0 H1 Hh Hh1) as Hj.
    replace (4 * Datatypes.S p + 3)%nat with (4 * p + 7)%nat in Hj by lia.
    assert (Hhh0 : Qle 0 (h * h)) by exact (Qmult_le_0_compat h h Hh Hh).
    apply (Qle_trans _ ((Z.of_nat (2 ^ (4 * p + 4))%nat # 1)%Q * (h * h)
                       + (Z.of_nat (2 ^ (4 * p + 7))%nat # 1)%Q * (h * h)) _).
    + apply (Qplus_le_compat _ _ _ _); [exact HIH | exact Hj].
    + assert (Hn : (2 ^ (4 * p + 4) + 2 ^ (4 * p + 7) <= 2 ^ (4 * p + 8))%nat).
      { assert (Hf8 : (2 ^ (4 * p + 7) = 2 ^ (4 * p + 4) * 8)%nat).
        { replace (4 * p + 7)%nat with (4 * p + 4 + 3)%nat by lia.
          rewrite Nat.pow_add_r. reflexivity. }
        assert (Hf16 : (2 ^ (4 * p + 8) = 2 ^ (4 * p + 4) * 16)%nat).
        { replace (4 * p + 8)%nat with (4 * p + 4 + 4)%nat by lia.
          rewrite Nat.pow_add_r. reflexivity. }
        rewrite Hf8. rewrite Hf16. lia. }
      assert (HZle : Qle ((Z.of_nat (2 ^ (4 * p + 4) + 2 ^ (4 * p + 7))%nat # 1))
                          ((Z.of_nat (2 ^ (4 * p + 8))%nat # 1))).
      { apply Nat2Z.inj_le in Hn.
        unfold Qle. cbn [Qnum Qden]. lia. }
      apply (Qle_trans _ ((Z.of_nat (2 ^ (4 * p + 4) + 2 ^ (4 * p + 7))%nat # 1)%Q
                            * (h * h)) _).
      * apply qeq_le.
        unfold Qeq.
        cbn [Qnum Qden Qplus Qmult Qopp Qminus].
        lia.
      * apply (Qmult_le_compat_r _ _ (h * h)); [exact HZle | exact Hhh0].
Qed.

(** Envelope step (symmetric): [- 2^{4m+4}#1 * h^2 <= Delta_m]. *)
Lemma pa_aA_step_ge : forall (m : nat) (x h : Q),
  Qle 0 x -> Qle x 1 -> Qle 0 h -> Qle h 1 ->
  Qle ((- (Z.of_nat (2 ^ (4 * m + 4))%nat # 1)) * (h * h))
      (aA m (x + h) - aA m x - aG m x * h).
Proof.
  intro m.
  induction m as [| p IH].
  - intros x h H0 H1 Hh Hh1.
    change (aA 0%nat (x + h)) with (aA_term 0%nat (x + h)).
    change (aA 0%nat x) with (aA_term 0%nat x).
    change (aG 0%nat x) with (aG_term 0%nat x).
    pose proof (pa_aA_term_step_ge 0%nat x h H0 H1 Hh Hh1) as Hj.
    replace (4 * 0 + 3)%nat with 3%nat in Hj by lia.
    replace (2 ^ 3)%nat with 8%nat in Hj by reflexivity.
    replace (4 * 0 + 4)%nat with 4%nat by lia.
    replace (2 ^ 4)%nat with 16%nat by reflexivity.
    apply (Qle_trans _ ((- (Z.of_nat 8 # 1)) * (h * h)) _).
    + apply (Qmult_le_compat_r (- (Z.of_nat 16 # 1)) (- (Z.of_nat 8 # 1)) (h * h)).
      * apply Qopp_le_compat. unfold Qle. simpl. lia.
      * exact (Qmult_le_0_compat h h Hh Hh).
    + exact Hj.
  - intros x h H0 H1 Hh Hh1.
    replace (4 * Datatypes.S p + 4)%nat with (4 * p + 8)%nat by lia.
    assert (Hdecomp : aA (Datatypes.S p) (x + h) - aA (Datatypes.S p) x
                      - aG (Datatypes.S p) x * h
                      == (aA p (x + h) - aA p x - aG p x * h)
                       + (aA_term (Datatypes.S p) (x + h) - aA_term (Datatypes.S p) x
                          - aG_term (Datatypes.S p) x * h)).
    { change (aA (Datatypes.S p) (x + h))
        with (aA p (x + h) + aA_term (Datatypes.S p) (x + h)).
      change (aA (Datatypes.S p) x) with (aA p x + aA_term (Datatypes.S p) x).
      change (aG (Datatypes.S p) x) with (aG p x + aG_term (Datatypes.S p) x).
      ring. }
    rewrite Hdecomp.
    pose proof (IH x h H0 H1 Hh Hh1) as HIH.
    pose proof (pa_aA_term_step_ge (Datatypes.S p) x h H0 H1 Hh Hh1) as Hj.
    replace (4 * Datatypes.S p + 3)%nat with (4 * p + 7)%nat in Hj by lia.
    assert (Hhh0 : Qle 0 (h * h)) by exact (Qmult_le_0_compat h h Hh Hh).
    assert (Hsum : Qle ((Z.of_nat (2 ^ (4 * p + 4))%nat # 1)%Q * (h * h)
                       + (Z.of_nat (2 ^ (4 * p + 7))%nat # 1)%Q * (h * h))
                       ((Z.of_nat (2 ^ (4 * p + 8))%nat # 1)%Q * (h * h))).
    { assert (Hn : (2 ^ (4 * p + 4) + 2 ^ (4 * p + 7) <= 2 ^ (4 * p + 8))%nat).
      { assert (Hf8 : (2 ^ (4 * p + 7) = 2 ^ (4 * p + 4) * 8)%nat).
        { replace (4 * p + 7)%nat with (4 * p + 4 + 3)%nat by lia.
          rewrite Nat.pow_add_r. reflexivity. }
        assert (Hf16 : (2 ^ (4 * p + 8) = 2 ^ (4 * p + 4) * 16)%nat).
        { replace (4 * p + 8)%nat with (4 * p + 4 + 4)%nat by lia.
          rewrite Nat.pow_add_r. reflexivity. }
        rewrite Hf8. rewrite Hf16. lia. }
      assert (HZle : Qle ((Z.of_nat (2 ^ (4 * p + 4) + 2 ^ (4 * p + 7))%nat # 1))
                          ((Z.of_nat (2 ^ (4 * p + 8))%nat # 1))).
      { apply Nat2Z.inj_le in Hn.
        unfold Qle. cbn [Qnum Qden]. lia. }
      apply (Qle_trans _ ((Z.of_nat (2 ^ (4 * p + 4) + 2 ^ (4 * p + 7))%nat # 1)%Q
                            * (h * h)) _).
      - apply qeq_le.
        unfold Qeq.
        cbn [Qnum Qden Qplus Qmult Qopp Qminus].
        lia.
      - apply (Qmult_le_compat_r _ _ (h * h)); [exact HZle | exact Hhh0]. }
    apply (Qle_trans _ (- ((Z.of_nat (2 ^ (4 * p + 4))%nat # 1)%Q * (h * h)
                          + (Z.of_nat (2 ^ (4 * p + 7))%nat # 1)%Q * (h * h))) _).
    + apply (Qle_trans _ (- ((Z.of_nat (2 ^ (4 * p + 8))%nat # 1)%Q * (h * h))) _).
      * apply qeq_le. ring.
      * apply Qopp_le_compat. exact Hsum.
    + apply (Qle_trans _ (((- (Z.of_nat (2 ^ (4 * p + 4))%nat # 1)) * (h * h))
                         + ((- (Z.of_nat (2 ^ (4 * p + 7))%nat # 1)) * (h * h))) _).
      * apply qeq_le.
        assert (Hsplit : (- ((Z.of_nat (2 ^ (4 * p + 4))%nat # 1)%Q * (h * h)
                              + (Z.of_nat (2 ^ (4 * p + 7))%nat # 1)%Q * (h * h)))
                       == (((- (Z.of_nat (2 ^ (4 * p + 4))%nat # 1)) * (h * h))
                          + ((- (Z.of_nat (2 ^ (4 * p + 7))%nat # 1)) * (h * h))))
          by ring.
        exact Hsplit.
      * apply (Qplus_le_compat _ _ _ _); [exact HIH | exact Hj].
Qed.
(* ================= Section 3f. Stepping of the sin/cos partial sums (supply for [aF_step]) ================= *)

(** Absorption of squares into absolute values:
    [|t| * |t| == t * t]. *)
Lemma pa_sq_abs_eq : forall t : Q, Qabs t * Qabs t == t * t.
Proof.
  intro t.
  apply (Qabs_case t (fun _ : Q => Qabs t * Qabs t == t * t)).
  - intros H0. rewrite (Qabs_pos t H0). apply Qeq_refl.
  - intros H0. rewrite (Qabs_neg t H0). ring.
Qed.

(** Squares are nonnegative. *)
Lemma pa_sq_pos : forall t : Q, Qle 0 (t * t).
Proof.
  intro t.
  rewrite <- (pa_sq_abs_eq t).
  apply Qmult_le_0_compat; apply Qabs_nonneg.
Qed.

(** Cross-division comparison: [X * W <= Y * Z] with [Z > 0] and
    [W > 0] implies [X * (/Z) <= Y * (/W)]. *)
Lemma pa_div_le : forall X Y Z W : Q,
  Qle (X * W) (Y * Z) -> Qlt 0 Z -> Qlt 0 W ->
  Qle (X * (/ Z)) (Y * (/ W)).
Proof.
  intros X Y Z W H HZ HW.
  assert (HWne : ~ (W == 0)) by (apply pa_qpos_neq0; exact HW).
  assert (HZne : ~ (Z == 0)) by (apply pa_qpos_neq0; exact HZ).
  assert (Hpos : Qle 0 ((/ Z) * (/ W))).
  { apply Qlt_le_weak. apply Qmult_lt_0_compat.
    - apply Qinv_lt_0_compat. exact HZ.
    - apply Qinv_lt_0_compat. exact HW. }
  assert (Ekey : X * (/ Z) == (X * W) * ((/ Z) * (/ W))).
  { assert (Hid : W * ((/ Z) * (/ W)) == (W * (/ W)) * (/ Z)) by ring.
    rewrite <- (Qmult_assoc X W ((/ Z) * (/ W))).
    rewrite Hid.
    rewrite (Qmult_inv_r W HWne).
    rewrite Qmult_1_l.
    apply Qeq_refl. }
  assert (Ekey2 : Y * (/ W) == (Y * Z) * ((/ Z) * (/ W))).
  { assert (Hid2 : Z * ((/ Z) * (/ W)) == (Z * (/ Z)) * (/ W)) by ring.
    rewrite <- (Qmult_assoc Y Z ((/ Z) * (/ W))).
    rewrite Hid2.
    rewrite (Qmult_inv_r Z HZne).
    rewrite Qmult_1_l.
    apply Qeq_refl. }
  rewrite Ekey.
  apply (Qle_trans _ ((Y * Z) * ((/ Z) * (/ W))) _).
  - apply (Qmult_le_compat_r (X * W) (Y * Z) ((/ Z) * (/ W)));
      [exact H | exact Hpos].
  - apply (pa_le_qeq_r ((Y * Z) * ((/ Z) * (/ W)))
             ((Y * Z) * ((/ Z) * (/ W))) (Y * (/ W))).
    + apply Qle_refl.
    + symmetry. exact Ekey2.
Qed.

(** Order preservation under inversion (the stdlib 9.1 [QArith]
    exported interface has no [Qinv_le_compat]; route through
    [pa_div_le]). *)
Lemma pa_inv_le_compat : forall a b : Q,
  Qlt 0 a -> Qle a b -> Qle (/ b) (/ a).
Proof.
  intros a b Ha Hab.
  assert (Hmain : Qle (1%Q * (/ b)) (1%Q * (/ a))).
  { apply (pa_div_le 1%Q 1%Q b a).
    - apply (pa_Qmult_le_l a b 1%Q); [exact Hab | unfold Qle; simpl; lia].
    - apply (Qlt_le_trans 0 a b); [exact Ha | exact Hab].
    - exact Ha. }
  apply (Qle_trans _ (1%Q * (/ b)) _).
  - apply qeq_le. ring.
  - apply (pa_le_qeq_r (1%Q * (/ b)) (1%Q * (/ a)) (/ a)).
    + exact Hmain.
    + ring.
Qed.

(** The [D] form as a definition (same shape as the consumption side
    of [pa_D_pos]/[pa_D_le], written with [Datatypes.S]). *)
Definition pa_Df (q : nat) (y e : Q) : Q :=
  q_pow (y + e) (Datatypes.S q) - q_pow y (Datatypes.S q)
  - (Z.of_nat (Datatypes.S q) # 1) * q_pow y q * e.

(** [|y| <= 1] and [|e| <= 1] imply [|D_{Sq}(y,e)| <= E_q * e^2]
    (the two-sided form tolerating negative [y]). *)
Lemma pa_D_abs_le : forall (q : nat) (y e : Q),
  Qle (Qabs y) 1 -> Qle (Qabs e) 1 ->
  Qle (Qabs (pa_Df q y e)) (pa_E q * (e * e)).
Proof.
  intro q.
  induction q as [| p IH].
  - intros y e Hy He.
    unfold pa_Df.
    change (Datatypes.S 0)%nat with 1%nat.
    rewrite (pa_qpow_1 (y + e)).
    rewrite (pa_qpow_1 y).
    rewrite pa_qpow_0.
    assert (H1c : (Z.of_nat 1 # 1)%Q == 1%Q) by apply Qeq_refl.
    rewrite H1c.
    assert (HD : (y + e - y - 1%Q * 1%Q * e)%Q == 0%Q) by ring.
    assert (HE0 : pa_E 0 == 0%Q) by (unfold pa_E; reflexivity).
    rewrite HD.
    rewrite HE0.
    change (Qabs 0%Q) with 0%Q.
    apply qeq_le. ring.
  - intros y e Hy He.
    unfold pa_Df.
    change (q_pow (y + e) (Datatypes.S (Datatypes.S p)))
      with ((y + e) * q_pow (y + e) (Datatypes.S p)).
    change (q_pow y (Datatypes.S (Datatypes.S p)))
      with (y * q_pow y (Datatypes.S p)).
    change (q_pow y (Datatypes.S p)) with (y * q_pow y p).
    assert (Hz : (Z.of_nat (Datatypes.S (Datatypes.S p)) # 1)%Q
                 == ((Z.of_nat (Datatypes.S p) # 1) + 1)%Q) by apply pa_zsucc_qmake.
    rewrite Hz.
    assert (Hcore : ((y + e) * q_pow (y + e) (Datatypes.S p)
                     - y * (y * q_pow y p)
                     - ((Z.of_nat (Datatypes.S p) # 1)%Q + 1) * (y * q_pow y p) * e)
                    == (y + e) * (q_pow (y + e) (Datatypes.S p)
                                  - y * q_pow y p
                                  - (Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p * e)
                    + (Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p * e * e) by ring.
    rewrite Hcore.
    assert (Hye : Qle (Qabs (y + e)) 2).
    { apply (Qle_trans _ (Qabs y + Qabs e) _).
      - apply Qabs_triangle.
      - apply (Qle_trans _ (1%Q + 1%Q) _).
        + apply Qplus_le_compat; assumption.
        + apply qeq_le. ring. }
    assert (HT0 : Qle 0 ((Z.of_nat (Datatypes.S p) # 1)%Q))
      by (unfold Qle; simpl; lia).
    assert (HEnonneg : Qle 0 (pa_E p * (e * e)))
      by (apply Qmult_le_0_compat; [apply pa_E_pos | apply pa_sq_pos]).
    assert (HL1 : Qle (Qabs ((y + e) * (q_pow (y + e) (Datatypes.S p)
                                         - y * q_pow y p
                                         - (Z.of_nat (Datatypes.S p) # 1)%Q
                                           * q_pow y p * e)))
                      ((2%Q * pa_E p) * (e * e))).
    { rewrite Qabs_Qmult.
      apply (Qle_trans _ ((Qabs (y + e)) * (pa_E p * (e * e))) _).
      - apply (pa_Qmult_le_l (Qabs (q_pow (y + e) (Datatypes.S p)
                                        - y * q_pow y p
                                        - (Z.of_nat (Datatypes.S p) # 1)%Q
                                          * q_pow y p * e))
                 (pa_E p * (e * e)) (Qabs (y + e)));
          [exact (IH y e Hy He) | apply Qabs_nonneg].
      - apply (pa_le_qeq_r (Qabs (y + e) * (pa_E p * (e * e)))
                 (2%Q * (pa_E p * (e * e)))
                 ((2%Q * pa_E p) * (e * e))).
        + apply (Qmult_le_compat_r (Qabs (y + e)) 2 (pa_E p * (e * e)));
            [exact Hye | exact HEnonneg].
        + ring. }
    assert (HL2 : Qle (Qabs ((Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p * e * e))
                      (((Z.of_nat (Datatypes.S p) # 1)%Q) * (e * e))).
    { rewrite Qabs_Qmult.
      rewrite Qabs_Qmult.
      rewrite Qabs_Qmult.
      rewrite <- (pa_sq_abs_eq e).
      assert (HTabs : Qabs ((Z.of_nat (Datatypes.S p) # 1)%Q)
                      == ((Z.of_nat (Datatypes.S p) # 1)%Q))
        by (apply Qabs_pos; exact HT0).
      rewrite HTabs.
      assert (Hpow1 : Qle (Qabs (q_pow y p)) 1).
      { rewrite q_pow_abs.
        apply (pa_qpow_le_one p (Qabs y)); [apply Qabs_nonneg | exact Hy]. }
      assert (HA : ((Z.of_nat (Datatypes.S p) # 1)%Q * Qabs (q_pow y p)
                    * Qabs e * Qabs e)
                   == (((Z.of_nat (Datatypes.S p) # 1)%Q * Qabs (q_pow y p))
                       * (Qabs e * Qabs e))) by ring.
      rewrite HA.
      assert (HC : Qle ((Z.of_nat (Datatypes.S p) # 1)%Q * Qabs (q_pow y p))
                       (((Z.of_nat (Datatypes.S p) # 1)%Q) * 1%Q)).
      { apply (pa_Qmult_le_l (Qabs (q_pow y p)) 1%Q ((Z.of_nat (Datatypes.S p) # 1)%Q));
          [exact Hpow1 | exact HT0]. }
      rewrite Qmult_1_r in HC.
      apply (Qmult_le_compat_r _ _ (Qabs e * Qabs e));
        [exact HC | apply pa_sq_pos]. }
    assert (Hfin : Qle (Qabs ((y + e) * (q_pow (y + e) (Datatypes.S p)
                                         - y * q_pow y p
                                         - (Z.of_nat (Datatypes.S p) # 1)%Q
                                           * q_pow y p * e))
                        + Qabs ((Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p * e * e))
                       ((2%Q * pa_E p) * (e * e)
                        + ((Z.of_nat (Datatypes.S p) # 1)%Q) * (e * e))).
    { apply Qplus_le_compat; [exact HL1 | exact HL2]. }
    assert (Hfin2 : ((2%Q * pa_E p) * (e * e)
                     + ((Z.of_nat (Datatypes.S p) # 1)%Q) * (e * e))
                    == ((2%Q * pa_E p + (Z.of_nat (Datatypes.S p) # 1)%Q) * (e * e))) by ring.
    rewrite Hfin2 in Hfin.
    assert (Hfin3 : (pa_E (Datatypes.S p)) * (e * e)
                    == ((2%Q * pa_E p + (Z.of_nat (Datatypes.S p) # 1)%Q) * (e * e))).
    { rewrite pa_E_step. apply Qeq_refl. }
    rewrite <- Hfin3 in Hfin.
    apply (Qle_trans _ (Qabs ((y + e) * (q_pow (y + e) (Datatypes.S p)
                                         - y * q_pow y p
                                         - (Z.of_nat (Datatypes.S p) # 1)%Q
                                           * q_pow y p * e))
                        + Qabs ((Z.of_nat (Datatypes.S p) # 1)%Q * q_pow y p * e * e)) _).
    + apply Qabs_triangle.
    + exact Hfin.
Qed.

(* ---- The sin stepping chain ---- *)

(** The per-j identity: the sin step residual equals
    [sign * D_{2j} * /(2j+1)!]. *)
Lemma pa_sterm_step : forall (j : nat) (y e : Q),
  sin_term j (y + e) - sin_term j y - cos_term j y * e
  == q_pow (-1) j * (pa_Df (2 * j) y e * (/ q_fact (Datatypes.S (2 * j)))).
Proof.
  intros j y e.
  unfold sin_term, cos_term, pa_Df.
  assert (Hqf : q_fact (Datatypes.S (2 * j))
                == (Z.of_nat (Datatypes.S (2 * j)) # 1) * q_fact (2 * j))
    by (apply q_fact_succ).
  rewrite Hqf.
  assert (Hqf2 : ~ (q_fact (2 * j) == 0%Q)).
  { intro Hc.
    assert (Hp := q_fact_pos (2 * j)).
    rewrite Hc in Hp.
    unfold Qlt in Hp. simpl in Hp. lia. }
  assert (Hd1 : ~ ((Z.of_nat (Datatypes.S (2 * j)) # 1)%Q == 0%Q)).
  { apply pa_qpos_neq0. unfold Qlt. simpl. lia. }
  assert (Hprod : ~ (((Z.of_nat (Datatypes.S (2 * j)) # 1)%Q * q_fact (2 * j))%Q == 0%Q)).
  { intro Hc.
    apply Qmult_integral in Hc.
    destruct Hc as [Hc | Hc].
    - apply Hd1. exact Hc.
    - apply Hqf2. exact Hc. }
  field. split; [exact Hqf2 | exact Hd1].
Qed.

(** The [pa_sT] denomination of the per-j bound. *)
Definition pa_sT (j : nat) : Q :=
  (Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1) * (/ q_fact (Datatypes.S (2 * j))).

Lemma pa_sT_pos : forall j : nat, Qle 0 (pa_sT j).
Proof.
  intro j.
  unfold pa_sT.
  apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply Qlt_le_weak. apply Qinv_lt_0_compat.
    exact (q_fact_pos (Datatypes.S (2 * j))).
Qed.

Lemma pa_sterm_step_le : forall (j : nat) (y e : Q),
  Qle (Qabs y) 1 -> Qle (Qabs e) 1 ->
  Qle (Qabs (sin_term j (y + e) - sin_term j y - cos_term j y * e))
      (pa_sT j * (e * e)).
Proof.
  intros j y e Hy He.
  rewrite (pa_sterm_step j y e).
  rewrite Qabs_Qmult.
  rewrite (sc_abs_sign j).
  rewrite Qmult_1_l.
  rewrite Qabs_Qmult.
  assert (Hqfpos : Qabs ((/ q_fact (Datatypes.S (2 * j)))%Q)
                   == ((/ q_fact (Datatypes.S (2 * j)))%Q)).
  { apply Qabs_pos. apply Qlt_le_weak. apply Qinv_lt_0_compat.
    exact (q_fact_pos (Datatypes.S (2 * j))). }
  rewrite Hqfpos.
  apply (Qle_trans _ ((pa_E (2 * j) * (e * e)) * (/ q_fact (Datatypes.S (2 * j)))) _).
  - apply (Qmult_le_compat_r (Qabs (pa_Df (2 * j) y e))
             (pa_E (2 * j) * (e * e)) (/ q_fact (Datatypes.S (2 * j))));
      [exact (pa_D_abs_le (2 * j) y e Hy He)
      | apply Qlt_le_weak; apply Qinv_lt_0_compat;
          exact (q_fact_pos (Datatypes.S (2 * j)))].
  - apply (pa_le_qeq_r
             ((pa_E (2 * j) * (e * e)) * (/ q_fact (Datatypes.S (2 * j))))
             ((Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1)
              * ((e * e) * (/ q_fact (Datatypes.S (2 * j)))))
             (pa_sT j * (e * e))).
    + rewrite <- Qmult_assoc.
      apply (Qmult_le_compat_r (pa_E (2 * j))
               ((Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1))
               (e * e * (/ q_fact (Datatypes.S (2 * j)))));
      [exact (pa_E_le (2 * j))
      | apply Qmult_le_0_compat;
          [apply pa_sq_pos
          | apply Qlt_le_weak; apply Qinv_lt_0_compat;
              exact (q_fact_pos (Datatypes.S (2 * j)))]].
    + unfold pa_sT. ring.
Qed.

Fixpoint pa_srhow (k : nat) : Q :=
  match k with
  | 0%nat => pa_sT 0%nat
  | Datatypes.S p => pa_srhow p + pa_sT (Datatypes.S p)
  end.

Lemma pa_srhow_pos : forall k : nat, Qle 0 (pa_srhow k).
Proof.
  intro k.
  induction k as [| p IH].
  - exact (pa_sT_pos 0).
  - change (pa_srhow (Datatypes.S p)) with (pa_srhow p + pa_sT (Datatypes.S p)).
    apply (Qplus_le_compat 0%Q (pa_srhow p) 0%Q (pa_sT (Datatypes.S p))).
    + exact IH.
    + exact (pa_sT_pos (Datatypes.S p)).
Qed.

(** Ratio decrease: [j >= 1] implies [T_{j+1} <= T_j/4]. *)
Lemma pa_sT_ratio : forall j : nat,
  (1 <= j)%nat -> Qle (pa_sT (Datatypes.S j)) ((1 # 4) * pa_sT j).
Proof.
  intros j Hj.
  unfold pa_sT.
  rewrite (q_fact_succ (2 * Datatypes.S j)).
  replace (2 * Datatypes.S j)%nat with (Datatypes.S (Datatypes.S (2 * j)))%nat by lia.
  rewrite (q_fact_succ (Datatypes.S (2 * j))).
(* Denominator shape:
   [(S (S (S (2j))))#1 * ((S (S (2j)))#1 * q_fact (S (2j)))]. *)
  assert (HAeq : (Z.of_nat (2 ^ (Datatypes.S (S (S (2 * j)))))%nat # 1)%Q
                 == ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1))%Q).
  { replace (Datatypes.S (S (S (2 * j))))%nat
      with ((Datatypes.S (2 * j)) + 2)%nat by lia.
    rewrite Nat.pow_add_r.
    change (2 ^ 2)%nat with 4%nat.
    rewrite Nat2Z.inj_mul.
    change (Z.of_nat 4) with 4%Z.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp]. lia. }
  apply (Qle_trans _ ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1)
                      * (/ ((16 # 1) * q_fact (Datatypes.S (2 * j))))) _).
  - rewrite HAeq.
    apply (pa_Qmult_le_l
             ((/ ((Z.of_nat (Datatypes.S (S (S (2 * j)))) # 1)
                  * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)
                     * q_fact (Datatypes.S (2 * j))))))
             ((/ ((16 # 1) * q_fact (Datatypes.S (2 * j)))))
             ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1))).
    + apply pa_inv_le_compat.
      { apply Qmult_lt_0_compat.
        - unfold Qlt. simpl. lia.
        - apply Qmult_lt_0_compat.
          ++ unfold Qlt. simpl. lia.
          ++ exact (q_fact_pos (2 * j)). }
      { (* 16 * q <= (2j+3) * ((2j+2) * q) *)
        apply (Qle_trans _ ((4 # 1) * (((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))
                                        * q_fact (Datatypes.S (2 * j)))) _).
        - apply (Qle_trans _ ((4 # 1) * ((4 # 1) * q_fact (Datatypes.S (2 * j)))) _).
          + apply qeq_le. ring.
          + apply (pa_Qmult_le_l ((4 # 1) * q_fact (Datatypes.S (2 * j)))
                     (((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))
                      * q_fact (Datatypes.S (2 * j))) (4 # 1)).
             * apply (Qmult_le_compat_r (4 # 1)
                         ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))
                         (q_fact (Datatypes.S (2 * j)))).
                -- unfold Qle. simpl. lia.
                -- apply Qlt_le_weak. exact (q_fact_pos (Datatypes.S (2 * j))).
             * unfold Qle. simpl. lia.
        - apply (Qmult_le_compat_r (4 # 1)
                    ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) # 1))
                    (((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))
                     * q_fact (Datatypes.S (2 * j)))).
          + unfold Qle. simpl. lia.
          + apply Qmult_le_0_compat.
             * unfold Qle. simpl. lia.
             * apply Qlt_le_weak. exact (q_fact_pos (Datatypes.S (2 * j))). }
    + apply Qmult_le_0_compat.
      * unfold Qle. simpl. lia.
      * unfold Qle. simpl. lia.
  - apply (pa_le_qeq_r
             ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1)
              * (/ ((16 # 1) * q_fact (Datatypes.S (2 * j)))))
             (((1 # 4) * (Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1))
              * (/ q_fact (Datatypes.S (2 * j))))
             ((1 # 4) * ((Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1)
                         * (/ q_fact (Datatypes.S (2 * j)))))).
    + apply (pa_div_le
               ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1))
               ((1 # 4) * (Z.of_nat (2 ^ (Datatypes.S (2 * j)))%nat # 1))
               ((16 # 1) * q_fact (Datatypes.S (2 * j)))
               (q_fact (Datatypes.S (2 * j)))).
       * apply qeq_le. ring.
       * apply Qmult_lt_0_compat.
         -- unfold Qlt. simpl. lia.
         -- exact (q_fact_pos (Datatypes.S (2 * j))).
       * exact (q_fact_pos (Datatypes.S (2 * j))).
    + ring.
Qed.

(** The partial-sum tail-ratio invariant:
    [srhow k + (4/3) * T_{S k} <= 4]. *)
Lemma pa_srhow_tail4 : forall k : nat,
  Qle (pa_srhow k + (4 # 3) * pa_sT (Datatypes.S k)) 4.
Proof.
  intro k.
  induction k as [| p IH].
  - change (pa_srhow 0) with (pa_sT 0).
    assert (H0 : pa_sT 0 == 2%Q).
    { unfold pa_sT.
      change (Datatypes.S (2 * 0))%nat with 1%nat.
      change (2 ^ 1)%nat with 2%nat.
      change (Z.of_nat 2) with 2%Z.
      change (q_fact 1) with 1%Q.
      unfold Qeq. cbn [Qnum Qden Qminus Qplus Qmult Qopp Qinv]. lia. }
    assert (H1 : pa_sT (Datatypes.S 0) == (4 # 3)%Q).
    { unfold pa_sT.
      change (Datatypes.S (2 * Datatypes.S 0))%nat with 3%nat.
      change (2 ^ 3)%nat with 8%nat.
      change (Z.of_nat 8) with 8%Z.
      change (q_fact 3) with (6 # 1)%Q.
      unfold Qeq. cbn [Qnum Qden Qminus Qplus Qmult Qopp Qinv]. lia. }
    rewrite H0.
    rewrite H1.
    unfold Qle. cbn [Qnum Qden Qminus Qplus Qmult]. lia.
  - change (pa_srhow (Datatypes.S (Datatypes.S p)))
      with (pa_srhow (Datatypes.S p) + pa_sT (Datatypes.S (Datatypes.S p))).
    change (pa_srhow (Datatypes.S p)) with (pa_srhow p + pa_sT (Datatypes.S p)).
    assert (Hratio : Qle (pa_sT (Datatypes.S (Datatypes.S p)))
                         ((1 # 4) * pa_sT (Datatypes.S p)))
      by (apply pa_sT_ratio; lia).
    assert (Hsub : Qle ((4 # 3) * pa_sT (Datatypes.S (Datatypes.S p)))
                       ((1 # 3) * pa_sT (Datatypes.S p))).
    { apply (pa_le_qeq_r
               ((4 # 3) * pa_sT (Datatypes.S (Datatypes.S p)))
               ((4 # 3) * ((1 # 4) * pa_sT (Datatypes.S p)))
               ((1 # 3) * pa_sT (Datatypes.S p))).
      - apply (pa_Qmult_le_l (pa_sT (Datatypes.S (Datatypes.S p)))
                 ((1 # 4) * pa_sT (Datatypes.S p)) (4 # 3));
          [exact Hratio | unfold Qle; simpl; lia].
      - ring. }
    assert (Hcomb : Qle ((pa_srhow p + pa_sT (Datatypes.S p))
                         + (4 # 3) * pa_sT (Datatypes.S (Datatypes.S p)))
                        (pa_srhow p + (4 # 3) * pa_sT (Datatypes.S p))).
    { apply (Qle_trans _ (pa_srhow p
                + (pa_sT (Datatypes.S p)
                   + (4 # 3) * pa_sT (Datatypes.S (Datatypes.S p)))) _).
      - apply qeq_le. ring.
      - apply (Qplus_le_compat (pa_srhow p) (pa_srhow p)
                 ((pa_sT (Datatypes.S p)
                   + (4 # 3) * pa_sT (Datatypes.S (Datatypes.S p))))
                 ((4 # 3) * pa_sT (Datatypes.S p))).
        + apply Qle_refl.
        + apply (pa_le_qeq_r
                   (pa_sT (Datatypes.S p)
                    + (4 # 3) * pa_sT (Datatypes.S (Datatypes.S p)))
                   (pa_sT (Datatypes.S p) + (1 # 3) * pa_sT (Datatypes.S p))
                   ((4 # 3) * pa_sT (Datatypes.S p))).
          * apply Qplus_le_compat;
              [apply Qle_refl | exact Hsub].
          * ring. }
    apply (Qle_trans _ (pa_srhow p + (4 # 3) * pa_sT (Datatypes.S p)) _).
    + exact Hcomb.
    + exact IH.
Qed.

Lemma pa_srhow_le : forall k : nat, Qle (pa_srhow k) 4.
Proof.
  intro k.
  pose proof (pa_srhow_tail4 k) as H.
  apply (Qle_trans _ (pa_srhow k + (4 # 3) * pa_sT (Datatypes.S k)) _).
  - apply (Qle_trans _ (pa_srhow k + 0%Q)).
    + apply qeq_le. ring.
    + apply (Qplus_le_compat (pa_srhow k) (pa_srhow k) 0%Q
               ((4 # 3) * pa_sT (Datatypes.S k))).
      * apply Qle_refl.
      * apply Qmult_le_0_compat.
        -- unfold Qle. simpl. lia.
        -- exact (pa_sT_pos (Datatypes.S k)).
  - exact H.
Qed.

Lemma pa_ssum_le : forall (k : nat) (y e : Q),
  Qle (Qabs y) 1 -> Qle (Qabs e) 1 ->
  Qle (Qabs (sin_partial k (y + e) - sin_partial k y - cos_partial k y * e))
      (pa_srhow k * (e * e)).
Proof.
  intro k.
  induction k as [| p IH].
  - intros y e Hy He.
    change (sin_partial 0 (y + e)) with (sin_term 0 (y + e)).
    change (sin_partial 0 y) with (sin_term 0 y).
    change (cos_partial 0 y) with (cos_term 0 y).
    change (pa_srhow 0) with (pa_sT 0).
    exact (pa_sterm_step_le 0 y e Hy He).
  - intros y e Hy He.
    change (sin_partial (Datatypes.S p) (y + e))
      with (sin_partial p (y + e) + sin_term (Datatypes.S p) (y + e)).
    change (sin_partial (Datatypes.S p) y)
      with (sin_partial p y + sin_term (Datatypes.S p) y).
    change (cos_partial (Datatypes.S p) y)
      with (cos_partial p y + cos_term (Datatypes.S p) y).
    change (pa_srhow (Datatypes.S p)) with (pa_srhow p + pa_sT (Datatypes.S p)).
    assert (Hre : (sin_partial p (y + e) + sin_term (Datatypes.S p) (y + e)
             - (sin_partial p y + sin_term (Datatypes.S p) y)
             - (cos_partial p y + cos_term (Datatypes.S p) y) * e)
             == ((sin_partial p (y + e) - sin_partial p y - cos_partial p y * e)
            + (sin_term (Datatypes.S p) (y + e) - sin_term (Datatypes.S p) y
               - cos_term (Datatypes.S p) y * e))) by ring.
    rewrite Hre.
    apply (Qle_trans _ (Qabs
             (sin_partial p (y + e) - sin_partial p y - cos_partial p y * e)
             + Qabs (sin_term (Datatypes.S p) (y + e) - sin_term (Datatypes.S p) y
                    - cos_term (Datatypes.S p) y * e)) _).
    + apply Qabs_triangle.
    + apply (Qle_trans _ (pa_srhow p * (e * e)
                           + pa_sT (Datatypes.S p) * (e * e)) _).
      * apply Qplus_le_compat.
        -- exact (IH y e Hy He).
        -- exact (pa_sterm_step_le (Datatypes.S p) y e Hy He).
      * apply qeq_le. ring.
Qed.

(** The main sin stepping lemma: [srho_k <= 4]. *)
Lemma pa_sin_step : forall (k : nat) (y e : Q),
  Qle (Qabs y) 1 -> Qle (Qabs e) 1 ->
  Qle (Qabs (sin_partial k (y + e) - sin_partial k y - cos_partial k y * e))
      ((4 # 1) * (e * e)).
Proof.
  intros k y e Hy He.
  apply (Qle_trans _ (pa_srhow k * (e * e)) _).
  - exact (pa_ssum_le k y e Hy He).
  - apply (Qmult_le_compat_r (pa_srhow k) 4%Q (e * e)).
    + exact (pa_srhow_le k).
    + exact (pa_sq_pos e).
Qed.

(* ---- The cos stepping chain ---- *)

(** The per-j identity: the cos step residual equals
    [sign' * D_{2j+1} * /(2j+2)!]. *)
Lemma pa_cterm_step : forall (k : nat) (y e : Q),
  cos_term (Datatypes.S k) (y + e) - cos_term (Datatypes.S k) y
  + sin_term k y * e
  == q_pow (-1) (Datatypes.S k)
     * (pa_Df (Datatypes.S (2 * k)) y e
        * (/ q_fact (Datatypes.S (Datatypes.S (2 * k))))).
Proof.
  intros k y e.
  unfold cos_term, sin_term, pa_Df.
  replace (2 * Datatypes.S k)%nat with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
  change (q_pow (-1) (Datatypes.S k)) with ((-1)%Q * q_pow (-1) k).
  assert (Hqf : q_fact (Datatypes.S (Datatypes.S (2 * k)))
                == (Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1)
                   * q_fact (Datatypes.S (2 * k)))
    by (apply q_fact_succ).
  rewrite Hqf.
  assert (Hqf2 : ~ (q_fact (Datatypes.S (2 * k)) == 0%Q)).
  { intro Hc.
    assert (Hp := q_fact_pos (Datatypes.S (2 * k))).
    rewrite Hc in Hp.
    unfold Qlt in Hp. simpl in Hp. lia. }
  assert (Hd1 : ~ ((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1)%Q == 0%Q)).
  { apply pa_qpos_neq0. unfold Qlt. simpl. lia. }
  assert (Hprod : ~ (((Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1)%Q
                      * q_fact (Datatypes.S (2 * k)))%Q == 0%Q)).
  { intro Hc.
    apply Qmult_integral in Hc.
    destruct Hc as [Hc | Hc].
    - apply Hd1. exact Hc.
    - apply Hqf2. exact Hc. }
  field. split; [exact Hqf2 | exact Hd1].
Qed.

(** The [pa_sT2] denomination of the per-j bound. *)
Definition pa_sT2 (k : nat) : Q :=
  (Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1)
  * (/ q_fact (Datatypes.S (Datatypes.S (2 * k)))).

Lemma pa_sT2_pos : forall k : nat, Qle 0 (pa_sT2 k).
Proof.
  intro k.
  unfold pa_sT2.
  apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply Qlt_le_weak. apply Qinv_lt_0_compat.
    exact (q_fact_pos (Datatypes.S (Datatypes.S (2 * k)))).
Qed.

(** The remaining [pa_cos_step] pieces ([pa_cterm_step_le],
    [pa_sT2_ratio], the [pa_crhow] family and the sum chain) are cast
    by mirroring the [pa_sT] family: the cterm bound chain mirrors the
    sterm chain verbatim ([Df] index [S(2k)], denomination [pa_sT2],
    direct rewriting with [sc_abs_sign (Datatypes.S k)]); the ratio
    chain has premise [(1 <= k)] and denominator chain
    [(2k+4)#1 * ((2k+3)#1 * q_fact (S (S (2k)))) >= 16 * W] with
    numerator bridge
    [2^{S (S (2 * Datatypes.S k))} == 4 * 2^{S (S (2 * k))}]; the
    tail-ratio base cases are [pa_sT2 0 == 2] ([2^2/2!]) and
    [pa_sT2 1 == (2#3)] ([2^4/4!]). *)

(* ---- The cos stepping chain, continued (mirroring the [pa_sT]
   family: cterm bound chain with [Df] index [S(2k)], denomination
   [pa_sT2], [sc_abs_sign (Datatypes.S k)]; ratio-chain premise
   [(1 <= k)]; tail-ratio base cases [pa_sT2 0 == 2] ([2^2/2!]) and
   [pa_sT2 1 == (2#3)] ([2^4/4!])) ---- *)

Lemma pa_cterm_step_le : forall (k : nat) (y e : Q),
  Qle (Qabs y) 1 -> Qle (Qabs e) 1 ->
  Qle (Qabs (cos_term (Datatypes.S k) (y + e) - cos_term (Datatypes.S k) y
             + sin_term k y * e))
      (pa_sT2 k * (e * e)).
Proof.
  intros k y e Hy He.
  rewrite (pa_cterm_step k y e).
  rewrite Qabs_Qmult.
  rewrite (sc_abs_sign (Datatypes.S k)).
  rewrite Qmult_1_l.
  rewrite Qabs_Qmult.
  assert (Hqfpos : Qabs ((/ q_fact (Datatypes.S (Datatypes.S (2 * k))))%Q)
                   == ((/ q_fact (Datatypes.S (Datatypes.S (2 * k))))%Q)).
  { apply Qabs_pos. apply Qlt_le_weak. apply Qinv_lt_0_compat.
    exact (q_fact_pos (Datatypes.S (Datatypes.S (2 * k)))). }
  rewrite Hqfpos.
  apply (Qle_trans _ ((pa_E (Datatypes.S (2 * k)) * (e * e))
                      * (/ q_fact (Datatypes.S (Datatypes.S (2 * k))))) _).
  - apply (Qmult_le_compat_r (Qabs (pa_Df (Datatypes.S (2 * k)) y e))
             (pa_E (Datatypes.S (2 * k)) * (e * e))
             (/ q_fact (Datatypes.S (Datatypes.S (2 * k)))));
      [exact (pa_D_abs_le (Datatypes.S (2 * k)) y e Hy He)
      | apply Qlt_le_weak; apply Qinv_lt_0_compat;
          exact (q_fact_pos (Datatypes.S (Datatypes.S (2 * k))))].
  - apply (pa_le_qeq_r
             ((pa_E (Datatypes.S (2 * k)) * (e * e))
              * (/ q_fact (Datatypes.S (Datatypes.S (2 * k)))))
             ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1)
              * ((e * e) * (/ q_fact (Datatypes.S (Datatypes.S (2 * k))))))
             (pa_sT2 k * (e * e))).
    + rewrite <- Qmult_assoc.
      apply (Qmult_le_compat_r (pa_E (Datatypes.S (2 * k)))
               ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1))
               (e * e * (/ q_fact (Datatypes.S (Datatypes.S (2 * k))))));
      [exact (pa_E_le (Datatypes.S (2 * k)))
      | apply Qmult_le_0_compat;
          [apply pa_sq_pos
          | apply Qlt_le_weak; apply Qinv_lt_0_compat;
              exact (q_fact_pos (Datatypes.S (Datatypes.S (2 * k))))]].
    + unfold pa_sT2. ring.
Qed.

(** Ratio decrease: [k >= 1] implies [T'_{k+1} <= T'_k/4]. *)
Lemma pa_sT2_ratio : forall k : nat,
  (1 <= k)%nat -> Qle (pa_sT2 (Datatypes.S k)) ((1 # 4) * pa_sT2 k).
Proof.
  intros k Hk.
  unfold pa_sT2.
  rewrite (q_fact_succ (Datatypes.S (2 * Datatypes.S k))).
  replace (2 * Datatypes.S k)%nat with (Datatypes.S (Datatypes.S (2 * k)))%nat by lia.
  rewrite (q_fact_succ (Datatypes.S (Datatypes.S (2 * k)))).
  assert (HAeq : (Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * k))))))%nat # 1)%Q
                 == ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1))%Q).
  { replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * k)))))%nat
      with ((Datatypes.S (Datatypes.S (2 * k))) + 2)%nat by lia.
    rewrite Nat.pow_add_r.
    change (2 ^ 2)%nat with 4%nat.
    rewrite Nat2Z.inj_mul.
    change (Z.of_nat 4) with 4%Z.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp]. lia. }
  apply (Qle_trans _ ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1)
                      * (/ ((16 # 1) * q_fact (Datatypes.S (Datatypes.S (2 * k)))))) _).
  - rewrite HAeq.
    apply (pa_Qmult_le_l
             ((/ ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * k))))) # 1)
                  * ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * k)))) # 1)
                     * q_fact (Datatypes.S (Datatypes.S (2 * k)))))))
             ((/ ((16 # 1) * q_fact (Datatypes.S (Datatypes.S (2 * k))))))
             ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1))).
    + apply pa_inv_le_compat.
      { rewrite (q_fact_succ (Datatypes.S (2 * k))).
        apply Qmult_lt_0_compat.
        - unfold Qlt. simpl. lia.
        - rewrite (q_fact_succ (2 * k)).
          apply Qmult_lt_0_compat.
          + unfold Qlt. simpl. lia.
          + apply Qmult_lt_0_compat.
            * unfold Qlt. simpl. lia.
            * exact (q_fact_pos (2 * k)). }
      { apply (Qle_trans _ ((4 # 1) * ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * k)))) # 1)
                                        * q_fact (Datatypes.S (Datatypes.S (2 * k))))) _).
        - apply (Qle_trans _ ((4 # 1) * ((4 # 1) * q_fact (Datatypes.S (Datatypes.S (2 * k))))) _).
          + apply qeq_le. ring.
          + apply (pa_Qmult_le_l ((4 # 1) * q_fact (Datatypes.S (Datatypes.S (2 * k))))
                     (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * k)))) # 1))
                      * q_fact (Datatypes.S (Datatypes.S (2 * k)))) (4 # 1)).
             * apply (Qmult_le_compat_r (4 # 1)
                         ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * k)))) # 1))
                         (q_fact (Datatypes.S (Datatypes.S (2 * k))))).
                -- unfold Qle. simpl. lia.
                -- apply Qlt_le_weak.
                   exact (q_fact_pos (Datatypes.S (Datatypes.S (2 * k)))).
             * unfold Qle. simpl. lia.
        - apply (Qmult_le_compat_r (4 # 1)
                    ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * k)))))) # 1)
                    (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * k)))) # 1))
                     * q_fact (Datatypes.S (Datatypes.S (2 * k))))).
          + unfold Qle. simpl. lia.
          + apply Qmult_le_0_compat.
             * unfold Qle. simpl. lia.
             * apply Qlt_le_weak.
                exact (q_fact_pos (Datatypes.S (Datatypes.S (2 * k)))). }
    + apply Qmult_le_0_compat.
      * unfold Qle. simpl. lia.
      * unfold Qle. simpl. lia.
  - apply (pa_le_qeq_r
             ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1)
              * (/ ((16 # 1) * q_fact (Datatypes.S (Datatypes.S (2 * k))))))
             (((1 # 4) * (Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1))
              * (/ q_fact (Datatypes.S (Datatypes.S (2 * k)))))
             ((1 # 4) * ((Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1)
                         * (/ q_fact (Datatypes.S (Datatypes.S (2 * k))))))).
    + apply (pa_div_le
               ((4 # 1) * (Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1))
               ((1 # 4) * (Z.of_nat (2 ^ (Datatypes.S (Datatypes.S (2 * k))))%nat # 1))
               ((16 # 1) * q_fact (Datatypes.S (Datatypes.S (2 * k))))
               (q_fact (Datatypes.S (Datatypes.S (2 * k))))).
       * apply qeq_le. ring.
       * apply Qmult_lt_0_compat.
         -- unfold Qlt. simpl. lia.
         -- exact (q_fact_pos (Datatypes.S (Datatypes.S (2 * k)))).
       * exact (q_fact_pos (Datatypes.S (Datatypes.S (2 * k)))).
    + ring.
Qed.


Fixpoint pa_crhow (k : nat) : Q :=
  match k with
  | 0%nat => pa_sT2 0%nat
  | Datatypes.S p => pa_crhow p + pa_sT2 (Datatypes.S p)
  end.

Lemma pa_crhow_pos : forall k : nat, Qle 0 (pa_crhow k).
Proof.
  intro k.
  induction k as [| p IH].
  - exact (pa_sT2_pos 0).
  - change (pa_crhow (Datatypes.S p)) with (pa_crhow p + pa_sT2 (Datatypes.S p)).
    apply (Qplus_le_compat 0%Q (pa_crhow p) 0%Q (pa_sT2 (Datatypes.S p))).
    + exact IH.
    + exact (pa_sT2_pos (Datatypes.S p)).
Qed.

(** The partial-sum tail-ratio invariant:
    [crhow k + (4/3) * T'_{S k} <= 4]. *)
Lemma pa_crhow_tail4 : forall k : nat,
  Qle (pa_crhow k + (4 # 3) * pa_sT2 (Datatypes.S k)) 4.
Proof.
  intro k.
  induction k as [| p IH].
  - change (pa_crhow 0) with (pa_sT2 0).
    assert (H0 : pa_sT2 0 == 2%Q).
    { unfold pa_sT2.
      change (Datatypes.S (Datatypes.S (2 * 0)))%nat with 2%nat.
      change (2 ^ 2)%nat with 4%nat.
      change (Z.of_nat 4) with 4%Z.
      change (q_fact 2) with 2%Q.
      unfold Qeq. cbn [Qnum Qden Qminus Qplus Qmult Qopp Qinv]. lia. }
    assert (H1 : pa_sT2 (Datatypes.S 0) == (2 # 3)%Q).
    { unfold pa_sT2.
      change (Datatypes.S (Datatypes.S (2 * Datatypes.S 0)))%nat with 4%nat.
      change (2 ^ 4)%nat with 16%nat.
      change (Z.of_nat 16) with 16%Z.
      change (q_fact 4) with (24 # 1)%Q.
      unfold Qeq. cbn [Qnum Qden Qminus Qplus Qmult Qopp Qinv]. lia. }
    rewrite H0.
    rewrite H1.
    unfold Qle. cbn [Qnum Qden Qminus Qplus Qmult]. lia.
  - change (pa_crhow (Datatypes.S (Datatypes.S p)))
      with (pa_crhow (Datatypes.S p) + pa_sT2 (Datatypes.S (Datatypes.S p))).
    change (pa_crhow (Datatypes.S p)) with (pa_crhow p + pa_sT2 (Datatypes.S p)).
    assert (Hratio : Qle (pa_sT2 (Datatypes.S (Datatypes.S p)))
                         ((1 # 4) * pa_sT2 (Datatypes.S p)))
      by (apply pa_sT2_ratio; lia).
    assert (Hsub : Qle ((4 # 3) * pa_sT2 (Datatypes.S (Datatypes.S p)))
                       ((1 # 3) * pa_sT2 (Datatypes.S p))).
    { apply (pa_le_qeq_r
               ((4 # 3) * pa_sT2 (Datatypes.S (Datatypes.S p)))
               ((4 # 3) * ((1 # 4) * pa_sT2 (Datatypes.S p)))
               ((1 # 3) * pa_sT2 (Datatypes.S p))).
      - apply (pa_Qmult_le_l (pa_sT2 (Datatypes.S (Datatypes.S p)))
                 ((1 # 4) * pa_sT2 (Datatypes.S p)) (4 # 3));
          [exact Hratio | unfold Qle; simpl; lia].
      - ring. }
    assert (Hcomb : Qle ((pa_crhow p + pa_sT2 (Datatypes.S p))
                         + (4 # 3) * pa_sT2 (Datatypes.S (Datatypes.S p)))
                        (pa_crhow p + (4 # 3) * pa_sT2 (Datatypes.S p))).
    { apply (Qle_trans _ (pa_crhow p
                + (pa_sT2 (Datatypes.S p)
                   + (4 # 3) * pa_sT2 (Datatypes.S (Datatypes.S p)))) _).
      - apply qeq_le. ring.
      - apply (Qplus_le_compat (pa_crhow p) (pa_crhow p)
                 ((pa_sT2 (Datatypes.S p)
                   + (4 # 3) * pa_sT2 (Datatypes.S (Datatypes.S p))))
                 ((4 # 3) * pa_sT2 (Datatypes.S p))).
        + apply Qle_refl.
        + apply (pa_le_qeq_r
                   (pa_sT2 (Datatypes.S p)
                    + (4 # 3) * pa_sT2 (Datatypes.S (Datatypes.S p)))
                   (pa_sT2 (Datatypes.S p) + (1 # 3) * pa_sT2 (Datatypes.S p))
                   ((4 # 3) * pa_sT2 (Datatypes.S p))).
          * apply Qplus_le_compat;
              [apply Qle_refl | exact Hsub].
          * ring. }
    apply (Qle_trans _ (pa_crhow p + (4 # 3) * pa_sT2 (Datatypes.S p)) _).
    + exact Hcomb.
    + exact IH.
Qed.

Lemma pa_crhow_le : forall k : nat, Qle (pa_crhow k) 4.
Proof.
  intro k.
  pose proof (pa_crhow_tail4 k) as H.
  apply (Qle_trans _ (pa_crhow k + (4 # 3) * pa_sT2 (Datatypes.S k)) _).
  - apply (Qle_trans _ (pa_crhow k + 0%Q)).
    + apply qeq_le. ring.
    + apply (Qplus_le_compat (pa_crhow k) (pa_crhow k) 0%Q
               ((4 # 3) * pa_sT2 (Datatypes.S k))).
      * apply Qle_refl.
      * apply Qmult_le_0_compat.
        -- unfold Qle. simpl. lia.
        -- exact (pa_sT2_pos (Datatypes.S k)).
  - exact H.
Qed.

(** The cos sum bound: for [k >= 1],
    [|cos residual_k| <= crhow_{k-1} * e^2]. *)
Lemma pa_csum_le_S : forall (p : nat) (y e : Q),
  Qle (Qabs y) 1 -> Qle (Qabs e) 1 ->
  Qle (Qabs (cos_partial (Datatypes.S p) (y + e) - cos_partial (Datatypes.S p) y
             + sin_partial (Nat.pred (Datatypes.S p)) y * e))
      (pa_crhow p * (e * e)).
Proof.
  intro p.
  induction p as [| q IH].
  - intros y e Hy He.
    assert (HC0a : cos_term 0 (y + e) == 1%Q) by apply Qeq_refl.
    assert (HC0b : cos_term 0 y == 1%Q) by apply Qeq_refl.
    change (cos_partial (Datatypes.S 0) (y + e))
      with (cos_partial 0 (y + e) + cos_term (Datatypes.S 0) (y + e)).
    change (cos_partial (Datatypes.S 0) y)
      with (cos_partial 0 y + cos_term (Datatypes.S 0) y).
    change (cos_partial 0 (y + e)) with (cos_term 0 (y + e)).
    change (cos_partial 0 y) with (cos_term 0 y).
    change (pa_crhow 0) with (pa_sT2 0).
    rewrite HC0a. rewrite HC0b.
    assert (Hc0 : (1%Q + cos_term (Datatypes.S 0) (y + e)
                   - (1%Q + cos_term (Datatypes.S 0) y)
                   + sin_partial 0 y * e)
                  == (cos_term (Datatypes.S 0) (y + e)
                      - cos_term (Datatypes.S 0) y + sin_partial 0 y * e)) by ring.
    rewrite Hc0.
    apply (pa_cterm_step_le 0 y e Hy He).
  - intros y e Hy He.
    change (sin_partial (Nat.pred (Datatypes.S (Datatypes.S q))) y)
      with (sin_partial (Datatypes.S q) y).
    change (pa_crhow (Datatypes.S q)) with (pa_crhow q + pa_sT2 (Datatypes.S q)).
    assert (Hsp : sin_partial (Datatypes.S q) y * e
                  == sin_partial q y * e + sin_term (Datatypes.S q) y * e).
    { change (sin_partial (Datatypes.S q) y)
        with (sin_partial q y + sin_term (Datatypes.S q) y).
      ring. }
    rewrite Hsp.
    change (cos_partial (Datatypes.S (Datatypes.S q)) (y + e))
      with (cos_partial (Datatypes.S q) (y + e)
            + cos_term (Datatypes.S (Datatypes.S q)) (y + e)).
    change (cos_partial (Datatypes.S (Datatypes.S q)) y)
      with (cos_partial (Datatypes.S q) y
            + cos_term (Datatypes.S (Datatypes.S q)) y).
    assert (Hre : (cos_partial (Datatypes.S q) (y + e)
             + cos_term (Datatypes.S (Datatypes.S q)) (y + e)
             - (cos_partial (Datatypes.S q) y
                + cos_term (Datatypes.S (Datatypes.S q)) y)
             + (sin_partial q y * e + sin_term (Datatypes.S q) y * e))
             == ((cos_partial (Datatypes.S q) (y + e) - cos_partial (Datatypes.S q) y
             + sin_partial q y * e)
            + (cos_term (Datatypes.S (Datatypes.S q)) (y + e)
               - cos_term (Datatypes.S (Datatypes.S q)) y
               + sin_term (Datatypes.S q) y * e))) by ring.
    rewrite Hre.
    apply (Qle_trans _ (Qabs
             (cos_partial (Datatypes.S q) (y + e) - cos_partial (Datatypes.S q) y
             + sin_partial q y * e)
             + Qabs (cos_term (Datatypes.S (Datatypes.S q)) (y + e)
               - cos_term (Datatypes.S (Datatypes.S q)) y
               + sin_term (Datatypes.S q) y * e)) _).
    + apply Qabs_triangle.
    + apply (Qle_trans _ (pa_crhow q * (e * e)
                           + pa_sT2 (Datatypes.S q) * (e * e)) _).
      * apply Qplus_le_compat.
        -- exact (IH y e Hy He).
        -- exact (pa_cterm_step_le (Datatypes.S q) y e Hy He).
      * apply qeq_le. ring.
Qed.

Lemma pa_cos_step : forall (k : nat) (y e : Q),
  (1 <= k)%nat ->
  Qle (Qabs y) 1 -> Qle (Qabs e) 1 ->
  Qle (Qabs (cos_partial k (y + e) - cos_partial k y
             + sin_partial (Nat.pred k) y * e))
      ((4 # 1) * (e * e)).
Proof.
  intros k y e Hk Hy He.
  destruct k as [| p].
  - exfalso. lia.
  - apply (Qle_trans _ (pa_crhow (Nat.pred (Datatypes.S p)) * (e * e)) _).
    + apply (pa_csum_le_S p y e Hy He).
    + apply (Qmult_le_compat_r (pa_crhow (Nat.pred (Datatypes.S p))) 4%Q (e * e)).
      * apply pa_crhow_le.
      * exact (pa_sq_pos e).
Qed.


(* ============================================================ *)
(** ** The step bound for [aF] (division-free form)

    Mathematical mission.  An explicit step bound for [aF].  For
    [F k m x := sin_partial k (aA m x) - x * cos_partial k (aA m x)],
    prove, under [k >= 1], [0 <= x <= 1], [0 <= h] and [x + h <= 1],
    the bound
    [|(1+x^2) F(x+h) - (1+x^2+hx) F(x) + h * Dens k m x|
      <= h^2 (1+x^2) * 2^{8m+16}],
    where [Dens k m x := x^{4m+4} * (cos_partial k (aA m x)
    + x * sin_partial (pred k) (aA m x)) + x * sin_term k (aA m x)].
    The core of the ring identity is
    [x * F - Dens == (1+x^2) * (C * (G-1) + x * S_pred * G)]
    (obtained by [ring] after substituting the core geometric
    identity [gG_one_x2] in the form [x^{4m+4} = 1 - (1+x^2) G]); the
    residual decomposition is
    [T == (1+x^2) * (C * epsA + (x+h) * S_pred * epsA + h^2 * S_pred * G
    + epsS - (x+h) * epsC)], where [epsA]/[epsS]/[epsC] are the three
    step residuals of [aA]/sin/cos, collected term by term through the
    triangle inequality into [2^{8m+16}].
    Dependencies: the earlier parts of this file (all of
    Sections 0-3c) plus the three stepping supply lemmas
    ([pa_aA_step_le]/[pa_sin_step]/[pa_cos_step]).
    References.  [S10_KVQuantTrig.v], the arctan-truncation ODE
    residual band family; the core geometric identity [gG_one_x2]
    (Section 3 of this file).
    Constructivity.  All statements live on the stdlib
    [Qle]/[Qlt]/[Qeq] side; assumption-free and fully proved;
    [lia]/[ring]/[field] only in auxiliary bookkeeping steps.
    Build.  [coqc -native-compiler no -q -Q . "" PiArctanFixedQ.v]. *)
(* ============================================================ *)

(* ---- The wd trio: rewriting under [Qeq] contexts
   ([sin_term]/[sin_partial]/[cos_partial] are not [Proper]) ---- *)

Lemma pa_sin_term_wd : forall (j : nat) (x y : Q),
  x == y -> sin_term j x == sin_term j y.
Proof.
  intros j x y Hxy.
  unfold sin_term.
  rewrite (q_pow_wd x y (Datatypes.S (2 * j)) Hxy).
  reflexivity.
Qed.

Lemma pa_cos_term_wd : forall (j : nat) (x y : Q),
  x == y -> cos_term j x == cos_term j y.
Proof.
  intros j x y Hxy.
  unfold cos_term.
  rewrite (q_pow_wd x y (2 * j) Hxy).
  reflexivity.
Qed.

Lemma pa_sin_wd : forall (k : nat) (x y : Q),
  x == y -> sin_partial k x == sin_partial k y.
Proof.
  intros k x y Hxy.
  induction k as [| p IH].
  - change (sin_partial 0 x) with (sin_term 0 x).
    change (sin_partial 0 y) with (sin_term 0 y).
    apply (pa_sin_term_wd 0 x y Hxy).
  - change (sin_partial (Datatypes.S p) x)
      with (sin_partial p x + sin_term (Datatypes.S p) x).
    change (sin_partial (Datatypes.S p) y)
      with (sin_partial p y + sin_term (Datatypes.S p) y).
    rewrite IH.
    rewrite (pa_sin_term_wd (Datatypes.S p) x y Hxy).
    reflexivity.
Qed.

Lemma pa_cos_wd : forall (k : nat) (x y : Q),
  x == y -> cos_partial k x == cos_partial k y.
Proof.
  intros k x y Hxy.
  induction k as [| p IH].
  - change (cos_partial 0 x) with (cos_term 0 x).
    change (cos_partial 0 y) with (cos_term 0 y).
    apply (pa_cos_term_wd 0 x y Hxy).
  - change (cos_partial (Datatypes.S p) x)
      with (cos_partial p x + cos_term (Datatypes.S p) x).
    change (cos_partial (Datatypes.S p) y)
      with (cos_partial p y + cos_term (Datatypes.S p) y).
    rewrite IH.
    rewrite (pa_cos_term_wd (Datatypes.S p) x y Hxy).
    reflexivity.
Qed.

(* ---- Bookkeeping helpers on powers and absolute values ---- *)

(** [0 <= x <= 1] and [n <= m] imply [x^m <= x^n]. *)
Lemma pa_qpow_exp_mono : forall (x : Q) (n m : nat),
  Qle 0 x -> Qle x 1 -> (n <= m)%nat -> Qle (q_pow x m) (q_pow x n).
Proof.
  intros x n m H0 H1 Hnm.
  replace m with (n + (m - n))%nat by lia.
  rewrite pa_qpow_add.
  apply (Qle_trans _ (q_pow x n * 1%Q) _).
  + apply (pa_Qmult_le_l (q_pow x (m - n)) 1%Q (q_pow x n));
      [ apply (pa_qpow_le_one (m - n) x H0 H1) | apply (q_pow_nonneg x n); exact H0 ].
  + apply qeq_le; apply Qmult_1_r.
Qed.

(** Two-sided bounds imply an absolute-value upper bound. *)
Lemma pa_two_side_abs : forall d t : Q,
  Qle d t -> Qle (- t) d -> Qle (Qabs d) t.
Proof.
  intros d t H1 H2.
  apply (Qabs_case d (fun v => Qle (Qabs d) t)).
  - intros H0. rewrite (Qabs_pos d H0). exact H1.
  - intros H0. rewrite (Qabs_neg d H0).
    apply (pa_le_qeq_r (- d) (- (- t)) t).
    + apply Qopp_le_compat. exact H2.
    + assert (Hinv : - (- t) == t) by ring. exact Hinv.
Qed.

(* [|t| <= B] implies [t^2 <= B^2]. *)
Lemma pa_abs_sq_le : forall t B : Q,
  Qle (Qabs t) B -> Qle (t * t) (B * B).
Proof.
  intros t B H.
  assert (HB0 : Qle 0 B)
    by (apply (Qle_trans 0 (Qabs t) B); [apply Qabs_nonneg | exact H]).
  assert (Ht2 : t * t == Qabs t * Qabs t).
  { apply (Qabs_case t (fun v => t * t == v * v)).
    - intros _. apply Qeq_refl.
    - intros _. ring. }
  rewrite Ht2.
  apply Qmult_le_compat_nonneg.
  - split; [apply Qabs_nonneg | exact H].
  - split; [apply Qabs_nonneg | exact H].
Qed.

(* ---- Three bookkeeping lemmas on powers of two ([nat]) ---- *)

Lemma pa_two_pow_mono : forall a b : nat, (a <= b)%nat -> (2 ^ a <= 2 ^ b)%nat.
Proof.
  intros a b.
  induction b as [| p IH].
  - intro H. replace a with 0%nat by lia. apply Nat.le_refl.
  - intro H.
    destruct (Nat.le_gt_cases a p) as [Hle | Hgt].
    + rewrite pa_two_pow_S.
      apply (Nat.le_trans _ (2 ^ p) _); [apply IH; exact Hle | lia].
    + replace a with (Datatypes.S p) by lia. apply Nat.le_refl.
Qed.

Lemma pa_two_pow_add : forall a b : nat, (2 ^ (a + b) = 2 ^ a * 2 ^ b)%nat.
Proof.
  intros a b.
  induction b as [| p IH].
  - rewrite Nat.add_0_r. simpl. lia.
  - replace (a + Datatypes.S p)%nat with (Datatypes.S (a + p))%nat by lia.
    rewrite pa_two_pow_S.
    rewrite IH.
    rewrite pa_two_pow_S.
    rewrite (Nat.mul_assoc 2 (2 ^ a) (2 ^ p)).
    rewrite (Nat.mul_comm 2 (2 ^ a)).
    rewrite (Nat.mul_assoc (2 ^ a) 2 (2 ^ p)).
    reflexivity.
Qed.

(* ---- The geometric series [(1/4)^k] and its partial sums (the
   bookkeeping skeleton for [|partial sums| <= 3]) ---- *)

Fixpoint pa_gp4 (k : nat) : Q :=
  match k with
  | 0%nat => 1%Q
  | Datatypes.S p => (1 # 4)%Q * pa_gp4 p
  end.

Fixpoint pa_gp4sum (k : nat) : Q :=
  match k with
  | 0%nat => 1%Q
  | Datatypes.S p => pa_gp4sum p + pa_gp4 (Datatypes.S p)
  end.

Lemma pa_gp4_pos : forall k : nat, Qlt 0 (pa_gp4 k).
Proof.
  intro k.
  induction k as [| p IH].
  - unfold Qlt. simpl. lia.
  - change (pa_gp4 (Datatypes.S p)) with ((1 # 4)%Q * pa_gp4 p).
    apply Qmult_lt_0_compat.
    + unfold Qlt. simpl. lia.
    + exact IH.
Qed.

(** [q_fact(2j+1) >= 4^j]:
    [q_fact(2j+3) = (2j+3)#1 * (2j+2)#1 * q_fact(2j+1)
    >= 2#1 * 2#1 * q_fact(2j+1) >= 4 * 4^j]. *)
Lemma pa_qfact_ge_gp4 : forall j : nat, Qle (pa_gp4 j) (q_fact (Datatypes.S (2 * j))).
Proof.
  intro j.
  induction j as [| p IH].
  - change (q_fact (Datatypes.S 0)) with ((Z.of_nat 1 # 1) * q_fact 0).
    change (q_fact 0) with 1%Q.
    change (pa_gp4 0) with 1%Q.
    apply Qle_refl.
  - replace (2 * Datatypes.S p)%nat
      with (Datatypes.S (Datatypes.S (2 * p)))%nat by lia.
    change (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))))
      with ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
            * q_fact (Datatypes.S (Datatypes.S (2 * p)))).
    change (q_fact (Datatypes.S (Datatypes.S (2 * p))))
      with ((Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
            * q_fact (Datatypes.S (2 * p))).
    change (pa_gp4 (Datatypes.S p)) with ((1 # 4)%Q * pa_gp4 p).
    apply (Qle_trans _ ((1 # 4) * q_fact (Datatypes.S (2 * p))) _).
    + apply (pa_Qmult_le_l (pa_gp4 p) (q_fact (Datatypes.S (2 * p))) (1 # 4));
        [exact IH | unfold Qle; simpl; lia].
    + assert (Hf3 : Qle (1 # 4)
                         ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
                          * (Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)))
        by (unfold Qle; cbn [Qnum Qden Qminus Qplus Qmult Qopp]; lia).
      apply (pa_le_qeq_r ((1 # 4) * q_fact (Datatypes.S (2 * p)))
               (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
                 * (Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1))
                * q_fact (Datatypes.S (2 * p)))
               ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
                * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
                   * q_fact (Datatypes.S (2 * p))))).
      * apply (Qmult_le_compat_r (1 # 4)
                 ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
                  * (Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1))
                 (q_fact (Datatypes.S (2 * p))));
          [exact Hf3 | apply Qlt_le_weak; apply q_fact_pos].
      * ring.
Qed.



(** [4^j <= (2j+1)!] (the stronger supply for the [sin_term]
    envelope; same skeleton as [pa_qfact_ge_gp4]). *)
Lemma pa_qfact_ge_qpow4 : forall j : nat,
  Qle (q_pow (4 # 1)%Q j) (q_fact (Datatypes.S (2 * j))).
Proof.
  intro j.
  induction j as [| p IH].
  - change (q_pow (4 # 1)%Q 0) with 1%Q.
    change (q_fact (Datatypes.S 0)) with ((Z.of_nat 1 # 1) * q_fact 0).
    change (q_fact 0) with 1%Q.
    apply Qle_refl.
  - replace (2 * Datatypes.S p)%nat
      with (Datatypes.S (Datatypes.S (2 * p)))%nat by lia.
    change (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))))
      with ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
            * q_fact (Datatypes.S (Datatypes.S (2 * p)))).
    change (q_fact (Datatypes.S (Datatypes.S (2 * p))))
      with ((Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
            * q_fact (Datatypes.S (2 * p))).
    change (q_pow (4 # 1)%Q (Datatypes.S p))
      with ((4 # 1)%Q * q_pow (4 # 1)%Q p).
    apply (Qle_trans _ ((4 # 1) * q_fact (Datatypes.S (2 * p))) _).
    + apply (pa_Qmult_le_l (q_pow (4 # 1)%Q p) (q_fact (Datatypes.S (2 * p))) (4 # 1));
        [exact IH | unfold Qle; simpl; lia].
    + assert (Hf3 : Qle (4 # 1)
                         ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
                          * (Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)))
        by (unfold Qle; cbn [Qnum Qden Qminus Qplus Qmult]; lia).
      apply (pa_le_qeq_r ((4 # 1) * q_fact (Datatypes.S (2 * p)))
               (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
                 * (Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1))
                * q_fact (Datatypes.S (2 * p)))
               ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
                * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
                   * q_fact (Datatypes.S (2 * p))))).
      * apply (Qmult_le_compat_r (4 # 1)
                 ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * p)))) # 1)
                  * (Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1))
                 (q_fact (Datatypes.S (2 * p))));
          [exact Hf3 | apply Qlt_le_weak; apply q_fact_pos].
      * ring.
Qed.

(** [(1/4)^j * 4^j == 1] (the product-one bridge between [pa_gp4]
    and [q_pow (4#1)]). *)
Lemma pa_gp4_qpow4_prod : forall j : nat,
  pa_gp4 j * q_pow (4 # 1)%Q j == 1%Q.
Proof.
  intro j.
  induction j as [| p IHj].
  - apply Qeq_refl.
  - change (pa_gp4 (Datatypes.S p)) with ((1 # 4)%Q * pa_gp4 p).
    change (q_pow (4 # 1)%Q (Datatypes.S p)) with ((4 # 1)%Q * q_pow (4 # 1)%Q p).
    assert (Hs : ((1 # 4)%Q * pa_gp4 p) * ((4 # 1)%Q * q_pow (4 # 1)%Q p)
                 == (1 # 4)%Q * (4 # 1)%Q * (pa_gp4 p * q_pow (4 # 1)%Q p)) by ring.
    rewrite Hs.
    rewrite IHj.
    ring.
Qed.

(* ---- Auxiliary chain 1: the successor form of [/pa_gp4]
   ([1/4^(S p) = 4 * (1/4^p)]) ---- *)

Lemma piu1596_gp4_inv_S : forall p : nat,
  (/ pa_gp4 (Datatypes.S p)) == ((4 # 1) * (/ pa_gp4 p)).
Proof.
  intro p.
  change (pa_gp4 (Datatypes.S p)) with ((1 # 4)%Q * pa_gp4 p).
  rewrite Qinv_mult_distr.
  change (/ (1 # 4)) with (4 # 1).
  apply Qeq_refl.
Qed.

(* ---- Auxiliary chain 2: the two-step factorial monotonicity step ---- *)
(* [(2(S p))! = (2p+2) * (2p+1) * (2p)!] with [(2p+2) >= 2] and
   [(2p+1) >= 2] (for [p >= 1]), *)
(* so [4^p <= 2 * (2p)!] carries over to
   [4^{S p} = 4 * 4^p <= 4 * (2p)! <= (2(S p))!]. *)

Lemma piu1596_qfact2j_step : forall p : nat, (1 <= p)%nat ->
  Qle ((1 # 2) * (/ pa_gp4 p)) (q_fact (2 * p)) ->
  Qle ((1 # 2) * (/ pa_gp4 (Datatypes.S p))) (q_fact (2 * Datatypes.S p)).
Proof.
  intros p Hp IH.
  replace (2 * Datatypes.S p)%nat
    with (Datatypes.S (Datatypes.S (2 * p)))%nat by lia.
  rewrite piu1596_gp4_inv_S.
  change (q_fact (Datatypes.S (Datatypes.S (2 * p))))
    with ((Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
          * ((Z.of_nat (Datatypes.S (2 * p)) # 1) * q_fact (2 * p))).
  assert (HfA : Qle (2 # 1) (Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1))
    by (unfold Qle; simpl; lia).
  assert (HfB : Qle (2 # 1) (Z.of_nat (Datatypes.S (2 * p)) # 1))
    by (unfold Qle; simpl; lia).
  assert (Hpos : Qle 0 (q_fact (2 * p)))
    by (apply Qlt_le_weak; exact (q_fact_pos (2 * p))).
  assert (Hstep1 : Qle ((2 # 1) * ((1 # 2) * (/ pa_gp4 p)))
                        ((2 # 1) * q_fact (2 * p))).
  { apply (pa_Qmult_le_l ((1 # 2) * (/ pa_gp4 p)) (q_fact (2 * p)) (2 # 1));
      [exact IH | unfold Qle; simpl; lia]. }
  assert (Hstep2 : Qle ((2 # 1) * ((2 # 1) * ((1 # 2) * (/ pa_gp4 p))))
                        ((2 # 1) * ((2 # 1) * q_fact (2 * p)))).
  { apply (pa_Qmult_le_l ((2 # 1) * ((1 # 2) * (/ pa_gp4 p)))
             ((2 # 1) * q_fact (2 * p)) (2 # 1));
      [exact Hstep1 | unfold Qle; simpl; lia]. }
  assert (Hinner : Qle ((2 # 1) * q_fact (2 * p))
                        ((Z.of_nat (Datatypes.S (2 * p)) # 1)
                         * q_fact (2 * p))).
  { apply (Qmult_le_compat_r (2 # 1)
             (Z.of_nat (Datatypes.S (2 * p)) # 1) (q_fact (2 * p)));
      [exact HfB | exact Hpos]. }
  assert (Houter1 : Qle ((2 # 1) * ((2 # 1) * q_fact (2 * p)))
                         ((Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
                          * ((2 # 1) * q_fact (2 * p)))).
  { apply (Qmult_le_compat_r (2 # 1)
             (Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
             ((2 # 1) * q_fact (2 * p)));
      [exact HfA
      | apply Qmult_le_0_compat;
        [unfold Qle; simpl; lia | exact Hpos]]. }
  assert (Houter2 : Qle ((Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
                          * ((2 # 1) * q_fact (2 * p)))
                         ((Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
                          * ((Z.of_nat (Datatypes.S (2 * p)) # 1)
                             * q_fact (2 * p)))).
  { apply (pa_Qmult_le_l ((2 # 1) * q_fact (2 * p))
             ((Z.of_nat (Datatypes.S (2 * p)) # 1) * q_fact (2 * p))
             (Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1));
      [exact Hinner | unfold Qle; simpl; lia]. }
  apply (Qle_trans _ ((2 # 1) * ((2 # 1) * ((1 # 2) * (/ pa_gp4 p)))) _).
  - apply qeq_le. ring.
  - apply (Qle_trans _ ((2 # 1) * ((2 # 1) * q_fact (2 * p))) _).
    + exact Hstep2.
    + apply (Qle_trans _ ((Z.of_nat (Datatypes.S (Datatypes.S (2 * p))) # 1)
                           * ((2 # 1) * q_fact (2 * p))) _).
      * exact Houter1.
      * exact Houter2.
Qed.

(* ---- Auxiliary chain 3 (the main chain): the reciprocal carrier
   form of [(2j)! >= 4^j/2] ---- *)
(* [4^j <= 2 * (2j)!] iff [(1/2) * 4^j <= (2j)!]; two base cases
   ([j = 0], [j = 1]) plus the auxiliary-chain-2 step. *)

Lemma piu1596_qfact2j_ge_half : forall j : nat,
  Qle ((1 # 2) * (/ pa_gp4 j)) (q_fact (2 * j)).
Proof.
  intro j.
  induction j as [| p IH].
  - unfold Qle. simpl. lia.
  - destruct p as [| p'].
    + unfold Qle. simpl. lia.
    + apply (piu1596_qfact2j_step (Datatypes.S p')); [lia | exact IH].
Qed.

(* ---- Slot donor: [1/(2j)! <= 2 * (1/4)^j] (composed through the
   [pa_div_le] route) ---- *)
(* With [X = 1], [Y = 2#1], [Z = q_fact (2*j)] and [W = /pa_gp4 j]: *)
(* premise one, [Qle (1*W) (Y*Z)], is [4^j <= 2 * (2j)!] (supplied
   by the main chain); *)
(* the conclusion [Qle (1*/Z) (Y*/W)], switched via
   [Qinv_involutive], gives the slot form. *)

Lemma piu1596_cos_hinv : forall j : nat,
  Qle (/ q_fact (2 * j)) ((2 # 1) * pa_gp4 j).
Proof.
  intro j.
  assert (Hraw : Qle (1%Q * (/ q_fact (2 * j))) ((2 # 1) * (/ (/ pa_gp4 j)))).
  { apply (pa_div_le 1%Q (2 # 1) (q_fact (2 * j)) (/ pa_gp4 j)).
    - assert (Hs1 : Qle ((2 # 1) * ((1 # 2) * (/ pa_gp4 j)))
                         ((2 # 1) * q_fact (2 * j)))
        by (apply (pa_Qmult_le_l ((1 # 2) * (/ pa_gp4 j))
                    (q_fact (2 * j)) (2 # 1));
            [exact (piu1596_qfact2j_ge_half j) | unfold Qle; simpl; lia]).
      apply (Qle_trans _ ((2 # 1) * ((1 # 2) * (/ pa_gp4 j))) _).
      + apply qeq_le. ring.
      + exact Hs1.
    - exact (q_fact_pos (2 * j)).
    - apply Qinv_lt_0_compat. exact (pa_gp4_pos j). }
  rewrite Qinv_involutive in Hraw.
  apply (Qle_trans _ (1%Q * (/ q_fact (2 * j))) _).
  - apply qeq_le. ring.
  - exact Hraw.
Qed.


(** [|sin_term j y| <= (1/4)^j] (for [|y| <= 1]). *)
Lemma pa_sin_term_abs_le : forall (j : nat) (y : Q),
  Qle (Qabs y) 1 -> Qle (Qabs (sin_term j y)) (pa_gp4 j).
Proof.
  intros j y Hy.
  unfold sin_term.
  assert (Hdiv : q_pow y (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))
                 == q_pow y (Datatypes.S (2 * j)) * (/ q_fact (Datatypes.S (2 * j)))).
  { unfold Qdiv. reflexivity. }
  rewrite Hdiv.
  rewrite Qabs_Qmult.
  rewrite Qabs_Qmult.
  rewrite (sc_abs_sign j).
  rewrite (q_pow_abs y (Datatypes.S (2 * j))).
  assert (Hinva : Qabs (/ q_fact (Datatypes.S (2 * j))) == (/ q_fact (Datatypes.S (2 * j)))).
  { apply Qabs_pos.
    apply Qlt_le_weak.
    apply Qinv_lt_0_compat.
    exact (q_fact_pos (Datatypes.S (2 * j))). }
  rewrite Hinva.
  assert (Hpow1 : Qle (q_pow (Qabs y) (Datatypes.S (2 * j))) 1).
  { apply (pa_qpow_le_one (Datatypes.S (2 * j)) (Qabs y));
      [apply Qabs_nonneg | exact Hy]. }
  assert (Hinv : Qle (/ q_fact (Datatypes.S (2 * j))) (pa_gp4 j)).
  { apply (Qle_trans _ (1%Q * / q_fact (Datatypes.S (2 * j))) _).
    - apply qeq_le. symmetry. apply Qmult_1_l.
    - apply (pa_le_qeq_r (1%Q * / q_fact (Datatypes.S (2 * j)))
               (pa_gp4 j * / 1%Q) (pa_gp4 j)).
      + apply (pa_div_le 1%Q (pa_gp4 j) (q_fact (Datatypes.S (2 * j))) 1%Q).
        * apply (Qle_trans _ (pa_gp4 j * q_pow (4 # 1)%Q j) _).
          -- apply qeq_le. rewrite (pa_gp4_qpow4_prod j). apply Qmult_1_l.
          -- apply (pa_Qmult_le_l (q_pow (4 # 1)%Q j)
                     (q_fact (Datatypes.S (2 * j))) (pa_gp4 j));
              [exact (pa_qfact_ge_qpow4 j) | apply Qlt_le_weak; exact (pa_gp4_pos j)].
        * exact (q_fact_pos (Datatypes.S (2 * j))).
        * unfold Qlt. simpl. lia.
      + apply Qmult_1_r. }
  apply (Qle_trans _ (q_pow (Qabs y) (Datatypes.S (2 * j))
                                * (/ q_fact (Datatypes.S (2 * j)))) _).
  { apply qeq_le. apply Qmult_1_l. }
  assert (Hcomm : q_pow (Qabs y) (Datatypes.S (2 * j)) * (/ q_fact (Datatypes.S (2 * j)))
                  == (/ q_fact (Datatypes.S (2 * j)))
                     * q_pow (Qabs y) (Datatypes.S (2 * j))) by ring.
  rewrite Hcomm.
  apply (Qle_trans _ ((/ q_fact (Datatypes.S (2 * j))) * 1%Q) _).
  { apply (pa_Qmult_le_l (q_pow (Qabs y) (Datatypes.S (2 * j))) 1%Q
             (/ q_fact (Datatypes.S (2 * j))));
      [exact Hpow1
      | apply Qlt_le_weak; apply Qinv_lt_0_compat;
          exact (q_fact_pos (Datatypes.S (2 * j)))]. }
  apply (Qle_trans _ (/ q_fact (Datatypes.S (2 * j))) _).
  { apply qeq_le. apply Qmult_1_r. }
  exact Hinv.
Qed.

(** [|cos_term j y| <= 2 * (1/4)^j] (for [|y| <= 1]):
    [1/(2j)! <= 2/4^j]. *)
Lemma pa_cos_term_abs_le : forall (j : nat) (y : Q),
  Qle (Qabs y) 1 -> Qle (Qabs (cos_term j y)) ((2 # 1) * pa_gp4 j).
Proof.
  intros j y Hy.
  unfold cos_term.
  assert (Hdiv : q_pow y (2 * j) / q_fact (2 * j)
                 == q_pow y (2 * j) * (/ q_fact (2 * j))).
  { unfold Qdiv. reflexivity. }
  rewrite Hdiv.
  rewrite Qabs_Qmult.
  rewrite Qabs_Qmult.
  rewrite (sc_abs_sign j).
  rewrite (q_pow_abs y (2 * j)).
  assert (Hinva : Qabs (/ q_fact (2 * j)) == (/ q_fact (2 * j))).
  { apply Qabs_pos.
    apply Qlt_le_weak.
    apply Qinv_lt_0_compat.
    exact (q_fact_pos (2 * j)). }
  rewrite Hinva.
  assert (Hpow1 : Qle (q_pow (Qabs y) (2 * j)) 1).
  { apply (pa_qpow_le_one (2 * j) (Qabs y));
      [apply Qabs_nonneg | exact Hy]. }
  assert (Hinv : Qle (/ q_fact (2 * j)) ((2 # 1) * pa_gp4 j))
    by (apply (piu1596_cos_hinv j)).
  apply (Qle_trans _ (q_pow (Qabs y) (2 * j) * (/ q_fact (2 * j))) _).
  { apply qeq_le. apply Qmult_1_l. }
  apply (Qle_trans _ ((q_pow (Qabs y) (2 * j)) * ((2 # 1) * pa_gp4 j)) _).
  { apply (pa_Qmult_le_l (/ q_fact (2 * j)) ((2 # 1) * pa_gp4 j)
             (q_pow (Qabs y) (2 * j)));
      [exact Hinv
      | apply (q_pow_nonneg (Qabs y) (2 * j)); apply Qabs_nonneg]. }
  apply (Qle_trans _ (1%Q * ((2 # 1) * pa_gp4 j)) _).
  { apply (Qmult_le_compat_r (q_pow (Qabs y) (2 * j)) 1%Q ((2 # 1) * pa_gp4 j));
      [exact Hpow1
      | apply Qlt_le_weak; apply Qmult_lt_0_compat;
          [unfold Qlt; simpl; lia | exact (pa_gp4_pos j)]]. }
  apply qeq_le. ring.
Qed.

(** [|S_k(y)| <= sum_{j <= k} (1/4)^j] and
    [|C_k(y)| <= 2 * sum_{j <= k} (1/4)^j] (for [|y| <= 1]). *)
Lemma pa_sin_partial_le_sum : forall (k : nat) (y : Q),
  Qle (Qabs y) 1 -> Qle (Qabs (sin_partial k y)) (pa_gp4sum k).
Proof.
  intros k y Hy.
  induction k as [| p IH].
  - change (sin_partial 0 y) with (sin_term 0 y).
    change (pa_gp4sum 0) with (pa_gp4 0).
    apply (pa_sin_term_abs_le 0 y Hy).
  - change (sin_partial (Datatypes.S p) y)
      with (sin_partial p y + sin_term (Datatypes.S p) y).
    change (pa_gp4sum (Datatypes.S p))
      with (pa_gp4sum p + pa_gp4 (Datatypes.S p)).
    apply (Qle_trans _ (Qabs (sin_partial p y) + Qabs (sin_term (Datatypes.S p) y)) _).
    + apply Qabs_triangle.
    + apply Qplus_le_compat.
      * exact IH.
      * apply (pa_sin_term_abs_le (Datatypes.S p) y Hy).
Qed.

Lemma pa_cos_partial_le_sum : forall (k : nat) (y : Q),
  Qle (Qabs y) 1 -> Qle (Qabs (cos_partial k y)) ((2 # 1) * pa_gp4sum k).
Proof.
  intros k y Hy.
  induction k as [| p IH].
  - change (cos_partial 0 y) with (cos_term 0 y).
    change (pa_gp4sum 0) with (pa_gp4 0).
    apply (pa_cos_term_abs_le 0 y Hy).
  - change (cos_partial (Datatypes.S p) y)
      with (cos_partial p y + cos_term (Datatypes.S p) y).
    change (pa_gp4sum (Datatypes.S p))
      with (pa_gp4sum p + pa_gp4 (Datatypes.S p)).
    apply (Qle_trans _ (Qabs (cos_partial p y) + Qabs (cos_term (Datatypes.S p) y)) _).
    + apply Qabs_triangle.
    + apply (Qle_trans _ ((2 # 1) * pa_gp4sum p + (2 # 1) * pa_gp4 (Datatypes.S p)) _).
      * apply Qplus_le_compat.
        -- exact IH.
        -- apply (pa_cos_term_abs_le (Datatypes.S p) y Hy).
      * apply qeq_le. ring.
Qed.

(** The telescoping identity:
    [sum_{j <= k} (1/4)^j + (1/4)^k * (1/3) == 4/3]. *)
Lemma pa_gp4sum_trip : forall k : nat,
  pa_gp4sum k + pa_gp4 k * (1 # 3) == (4 # 3)%Q.
Proof.
  intro k.
  induction k as [| p IH].
  - change (pa_gp4sum 0) with 1%Q.
    change (pa_gp4 0) with 1%Q.
    ring.
  - change (pa_gp4sum (Datatypes.S p))
      with (pa_gp4sum p + pa_gp4 (Datatypes.S p)).
    change (pa_gp4 (Datatypes.S p)) with ((1 # 4)%Q * pa_gp4 p).
    rewrite <- IH.
    ring.
Qed.

(* [sum_{j <= k} (1/4)^j <= 4/3 <= 3]. *)
Lemma pa_gp4sum_le43 : forall k : nat, Qle (pa_gp4sum k) (4 # 3).
Proof.
  intro k.
  assert (Ht := pa_gp4sum_trip k).
  assert (H03 : Qle 0 (pa_gp4 k * (1 # 3)%Q)).
  { apply Qmult_le_0_compat.
    - apply Qlt_le_weak. exact (pa_gp4_pos k).
    - unfold Qle. simpl. lia. }
  assert (Hsum : pa_gp4sum k == (4 # 3)%Q - pa_gp4 k * (1 # 3)%Q)
    by (rewrite <- Ht; ring).
  apply (Qle_trans _ ((4 # 3)%Q - pa_gp4 k * (1 # 3)%Q) _).
  - rewrite Hsum. apply Qle_refl.
  - apply (pa_Qminus_le (4 # 3)%Q 0%Q (pa_gp4 k * (1 # 3)%Q)). exact H03.
Qed.

Lemma pa_gp4sum_le3 : forall k : nat, Qle (pa_gp4sum k) 3.
Proof.
  intro k.
  apply (Qle_trans _ (4 # 3)).
  - apply pa_gp4sum_le43.
  - unfold Qle. simpl. lia.
Qed.

(** [|S_k(y)| <= 3] and [|C_k(y)| <= 3] (for [|y| <= 1]). *)
Lemma pa_sin_partial_le3 : forall (k : nat) (y : Q),
  Qle (Qabs y) 1 -> Qle (Qabs (sin_partial k y)) 3.
Proof.
  intros k y Hy.
  apply (Qle_trans _ (pa_gp4sum k)).
  - apply (pa_sin_partial_le_sum k y Hy).
  - apply pa_gp4sum_le3.
Qed.

Lemma pa_cos_partial_le3 : forall (k : nat) (y : Q),
  Qle (Qabs y) 1 -> Qle (Qabs (cos_partial k y)) 3.
Proof.
  intros k y Hy.
  apply (Qle_trans _ ((2 # 1) * pa_gp4sum k)).
  - apply (pa_cos_partial_le_sum k y Hy).
  - apply (Qle_trans _ ((2 # 1) * (4 # 3))).
    + apply (pa_Qmult_le_l (pa_gp4sum k) (4 # 3) (2 # 1));
        [apply pa_gp4sum_le43 | unfold Qle; simpl; lia].
    + unfold Qle. simpl. lia.
Qed.

(* ---- Final-value bands for [aA]/[aG] (on [0 <= x <= 1]:
   [aA m x <= 1] and [0 <= aG m x <= m+1]) ---- *)

Lemma pa_aA_le_one : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> Qle (aA m x) 1.
Proof.
  intros m x H0 H1.
  assert (Hmono : Qle (aA m x) (aA m 1)).
  { induction m as [| p IH].
    - apply (pa_le_qeq_r (aA_term 0 x) (lp_pair 0) (aA_term 0 1)).
      + apply (pa_aA_term_le_lp_pair 0 x H0 H1).
      + apply (pa_aA_term_one 0).
    - change (aA (Datatypes.S p) x) with (aA p x + aA_term (Datatypes.S p) x).
      change (aA (Datatypes.S p) 1) with (aA p 1 + aA_term (Datatypes.S p) 1).
      apply (Qle_trans _ (aA p 1 + lp_pair (Datatypes.S p)) _).
      + apply Qplus_le_compat;
          [exact IH | apply (pa_aA_term_le_lp_pair (Datatypes.S p) x H0 H1)].
      + apply (pa_le_qeq_r (aA p 1 + lp_pair (Datatypes.S p))
                 (aA p 1 + lp_pair (Datatypes.S p))
                 (aA p 1 + aA_term (Datatypes.S p) 1)).
        * apply Qle_refl.
        * assert (Ht : lp_pair (Datatypes.S p) == aA_term (Datatypes.S p) 1)
            by (rewrite <- (pa_aA_term_one (Datatypes.S p)); reflexivity).
          rewrite Ht. apply Qeq_refl. }
  apply (Qle_trans _ (aA m 1) _).
  - exact Hmono.
  - rewrite (aA_one_lp_odd m).
    apply pa_lp_odd_le_1.
Qed.

Lemma pa_aG_term_nonneg : forall (j : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> Qle 0 (aG_term j x).
Proof.
  intros j x H0 H1.
  unfold aG_term.
  apply leibsep_qle_of_minus.
  apply leibsep_qle_minus.
  apply leibsep_qle_minus.
  apply (pa_qpow_exp_mono x (4 * j) (4 * j + 2) H0 H1).
  lia.
Qed.

Lemma pa_aG_term_le_one : forall (j : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> Qle (aG_term j x) 1.
Proof.
  intros j x H0 H1.
  unfold aG_term.
  apply (Qle_trans _ (q_pow x (4 * j) - 0%Q) _).
  - apply (pa_Qminus_le (q_pow x (4 * j)) 0%Q (q_pow x (4 * j + 2))).
    apply (q_pow_nonneg x (4 * j + 2)). exact H0.
  - apply (Qle_trans _ (q_pow x (4 * j)) _).
    + apply qeq_le. ring.
    + exact (pa_qpow_le_one (4 * j) x H0 H1).
Qed.

Lemma pa_aG_nonneg : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> Qle 0 (aG m x).
Proof.
  intros m x H0 H1.
  induction m as [| p IH].
  - apply (pa_aG_term_nonneg 0 x H0 H1).
  - change (aG (Datatypes.S p) x) with (aG p x + aG_term (Datatypes.S p) x).
    apply (Qplus_le_compat 0%Q (aG p x) 0%Q (aG_term (Datatypes.S p) x)).
    + exact IH.
    + apply (pa_aG_term_nonneg (Datatypes.S p) x H0 H1).
Qed.

Lemma pa_aG_le : forall (m : nat) (x : Q),
  Qle 0 x -> Qle x 1 -> Qle (aG m x) ((Z.of_nat (Datatypes.S m)) # 1).
Proof.
  intros m x H0 H1.
  induction m as [| p IH].
  - change (aG 0 x) with (aG_term 0 x).
    apply (Qle_trans _ 1%Q).
    + apply (pa_aG_term_le_one 0 x H0 H1).
    + apply qeq_le. unfold Qeq. simpl. lia.
  - change (aG (Datatypes.S p) x) with (aG p x + aG_term (Datatypes.S p) x).
    apply (Qle_trans _ ((Z.of_nat (Datatypes.S p) # 1) + 1%Q)).
    + apply Qplus_le_compat.
      * exact IH.
      * apply (pa_aG_term_le_one (Datatypes.S p) x H0 H1).
    + apply (pa_le_qeq_r ((Z.of_nat (Datatypes.S p) # 1) + 1%Q)
               ((Z.of_nat (Datatypes.S p) # 1) + 1%Q)
               ((Z.of_nat (Datatypes.S (Datatypes.S p))) # 1)).
      * apply Qle_refl.
      * symmetry. apply pa_zsucc_qmake.
Qed.

(* ---- The constant chain (purely arithmetic power bookkeeping) ---- *)

(** [2^{4m+5} == 2 * 2^{4m+4}] (the [Q] form). *)
Lemma pa_rho5_q : forall m : nat,
  ((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1)
  == ((2 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1))%Q.
Proof.
  intro m.
  replace (4 * m + 5)%nat with (Datatypes.S (4 * m + 4))%nat by lia.
  rewrite pa_two_pow_S.
  rewrite Nat2Z.inj_mul.
  unfold Qeq. cbn [Qnum Qden Qminus Qplus Qmult Qopp]. lia.
Qed.

(** [2^{8m+12} == 2 * (2^{4m+5})^2] (the [Q] form). *)
(** Distributivity of [Qmake] multiplication (the [#1] form):
    [(a*b)#1 == (a#1)*(b#1)]. *)
Lemma pa_qmake_mult_distr : forall a b : Z, (a * b) # 1 == (a # 1) * (b # 1).
Proof.
  intros a b.
  unfold Qeq, Qmult. cbn [Qnum Qden].
  rewrite !Zmult_1_r. reflexivity.
Qed.

Lemma pa_kappa_q : forall m : nat,
  ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1)
  == ((4 # 1) * (((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1)
                 * ((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1)))%Q.
Proof.
  intro m.
  replace (8 * m + 12)%nat with ((4 * m + 6) + (4 * m + 6))%nat by lia.
  rewrite pa_two_pow_add.
  replace (4 * m + 6)%nat with (Datatypes.S (4 * m + 5))%nat by lia.
  rewrite (pa_two_pow_S (4 * m + 5)).
  rewrite (Nat2Z.inj_mul (2 * 2 ^ (4 * m + 5)) (2 * 2 ^ (4 * m + 5))).
  rewrite (pa_qmake_mult_distr (Z.of_nat (2 * 2 ^ (4 * m + 5)))
             (Z.of_nat (2 * 2 ^ (4 * m + 5)))).
  rewrite (Nat2Z.inj_mul 2 (2 ^ (4 * m + 5))).
  rewrite (pa_qmake_mult_distr (Z.of_nat 2) (Z.of_nat (2 ^ (4 * m + 5)))).
  replace (Z.of_nat 2%nat) with 2%Z by reflexivity.
  ring.
Qed.

(** [6 * 2^{4m+4} + 3(m+1) + 2 * 2^{8m+12} <= 2^{8m+14}]
    (the [Q] form). *)
Lemma pa_pow_chain_le : forall m : nat,
  Qle ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
       + (3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
       + (3 # 1) * ((Z.of_nat (Datatypes.S m) # 1))
       + (2 # 1) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1))
      (((Z.of_nat (2 ^ (8 * m + 14))%nat) # 1)).
Proof.
  intro m.
  assert (Ha : (Datatypes.S m <= 2 ^ (4 * m + 4))%nat).
  { pose proof (pa_two_pow_ge (4 * m + 4)) as H. lia. }
  assert (Hrel : (4 * 2 ^ (8 * m + 12) <= 2 ^ (8 * m + 14))%nat).
  { replace (8 * m + 14)%nat
      with (Datatypes.S (Datatypes.S (8 * m + 12)))%nat by lia.
    rewrite pa_two_pow_S. rewrite pa_two_pow_S. lia. }
  assert (HZ : ((Z.of_nat (4 * 2 ^ (8 * m + 12)))
                <= (Z.of_nat (2 ^ (8 * m + 14))))%Z)
    by (apply Nat2Z.inj_le; exact Hrel).
  rewrite Nat2Z.inj_mul in HZ.
  assert (Hx : (2 ^ (4 * m + 4) <= 2 ^ (8 * m + 8))%nat)
    by (apply pa_two_pow_mono; lia).
  assert (Hy : (16 * 2 ^ (8 * m + 8) = 2 ^ (8 * m + 12))%nat).
  { replace (8 * m + 12)%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (8 * m + 8)))))%nat
      by lia.
    rewrite !pa_two_pow_S. lia. }
  unfold Qle. cbn [Qnum Qden Qplus Qmult]. lia.
Qed.

(** [2^{8m+14} <= 2^{8m+16}] (the [Q] form). *)
Lemma pa_pow_mono_le : forall m : nat,
  Qle ((Z.of_nat (2 ^ (8 * m + 14))%nat) # 1)
      ((Z.of_nat (2 ^ (8 * m + 16))%nat) # 1).
Proof.
  intro m.
  assert (Hn : (2 ^ (8 * m + 14) <= 2 ^ (8 * m + 16))%nat)
    by (apply pa_two_pow_mono; lia).
  pose proof (proj1 (Nat2Z.inj_le _ _) Hn) as HZ.
  unfold Qle. cbn [Qnum Qden Qplus Qmult]. lia.
Qed.

(* ---- The definition of [Dens] ---- *)

Definition pa_Dens (k m : nat) (x : Q) : Q :=
  q_pow x (4 * m + 4)
    * (cos_partial k (aA m x)
       + x * sin_partial (Nat.pred k) (aA m x))
  + x * sin_term k (aA m x).

(* ---- The main lemma: the step bound for [aF] ---- *)
(* The interfaces of the consumed supply lemmas (statements quoted
   verbatim):
   pa_aA_step_le : forall (m : nat) (x h : Q),
     Qle 0 x -> Qle x 1 -> Qle 0 h ->
     Qle (aA m (x + h) - aA m x - aG m x * h)
         (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h)).
   pa_aA_step_ge : forall (m : nat) (x h : Q),
     Qle 0 x -> Qle x 1 -> Qle 0 h ->
     Qle (- (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h)))
         (aA m (x + h) - aA m x - aG m x * h).
   (The envelope statements come as the [Qle]/[Qge] pair without
     [Qabs]; this lemma bridges to the [Qabs] consumption form via
     [pa_two_side_abs]; [2^{4(m+1)} = 2^{4m+4}].)
   pa_sin_step : forall (k : nat) (y e : Q),
     Qle (Qabs y) 1 -> Qle (Qabs e) 1 ->
     Qle (Qabs (sin_partial k (y + e) - sin_partial k y
                - cos_partial k y * e))
         ((4 # 1) * (e * e)).
   pa_cos_step : forall (k : nat) (y e : Q),
     (1 <= k)%nat ->
     Qle (Qabs y) 1 -> Qle (Qabs e) 1 ->
     Qle (Qabs (cos_partial k (y + e) - cos_partial k y
                + sin_partial (Nat.pred k) y * e))
         ((4 # 1) * (e * e)). *)

Lemma pa_aF_step : forall (k m : nat) (x h : Q),
  (1 <= k)%nat ->
  Qle 0 x -> Qle x 1 -> Qle 0 h -> Qle (x + h) 1 ->
  Qle (Qabs ((1 + x * x) * aF k m (x + h)
             - (1 + x * x + h * x) * aF k m x
             + h * pa_Dens k m x))
      ((h * h * (1 + x * x))
       * ((Z.of_nat (2 ^ (8 * m + 16))%nat) # 1)).
Proof.
  intros k m x h Hk Hx0 Hx1 Hh0 Hxh1.
  assert (H01 : Qle 0 1) by (unfold Qle; simpl; lia).
  assert (Hh1 : Qle h 1).
  { assert (Hhx : Qle h (x + h)).
    { assert (Hid : h == h + 0%Q) by ring.
      apply (pa_le_qeq_r h (h + x) (x + h)).
      - rewrite Hid at 1.
        apply (Qplus_le_compat h h 0%Q x).
        + apply Qle_refl.
        + exact Hx0.
      - ring. }
    apply (Qle_trans h (x + h) 1%Q Hhx Hxh1). }
  assert (Hxp : Qle 0 (x + h)) by (apply (Qplus_le_compat 0 x 0 h); assumption).
  assert (Habxh : Qabs (x + h) == x + h) by (apply Qabs_pos; exact Hxp).
  assert (Hxh2 : Qle (h * h) h).
  { apply (pa_le_qeq_r (h * h) (h * 1%Q) h).
    - apply (pa_Qmult_le_l h 1%Q h); [exact Hh1 | exact Hh0].
    - apply Qmult_1_r. }
  assert (Hx2p : Qle 0 (1 + x * x)).
  { apply (Qplus_le_compat 0%Q 1%Q 0%Q (x * x));
      [exact H01 | apply Qmult_le_0_compat; assumption]. }
  assert (Habx2 : Qabs (1 + x * x) == 1 + x * x) by (apply Qabs_pos; exact Hx2p).
  assert (HA0 : Qle 0 (aA m x)) by (apply (pa_aA_nonneg m x Hx0 Hx1)).
  assert (HA1 : Qle (aA m x) 1) by (apply (pa_aA_le_one m x Hx0 Hx1)).
  assert (HAa0 : Qle 0 (aA m (x + h))) by (apply (pa_aA_nonneg m (x + h) Hxp Hxh1)).
  assert (HAa1 : Qle (aA m (x + h)) 1) by (apply (pa_aA_le_one m (x + h) Hxp Hxh1)).
  assert (HabA : Qabs (aA m x) == aA m x) by (apply Qabs_pos; exact HA0).
  assert (HabA' : Qabs (aA m (x + h)) == aA m (x + h)) by (apply Qabs_pos; exact HAa0).
  assert (HabA1 : Qle (Qabs (aA m x)) 1) by (rewrite HabA; exact HA1).
(* Substitution from the core ring identity:
   [x^{4m+4} = 1 - (1+x^2) * G]. *)
  assert (Hg2 : q_pow x (4 * m + 4) == 1 - (1 + x * x) * aG m x).
  { assert (Hg := gG_one_x2 m x).
    rewrite Hg.
    ring. }
(* Residual decomposition: [T == (1+x^2) * U]. *)
  assert (Hdec : (1 + x * x) * aF k m (x + h)
                 - (1 + x * x + h * x) * aF k m x
                 + h * pa_Dens k m x
                 == (1 + x * x)
                    * (cos_partial k (aA m x)
                       * (aA m (x + h) - aA m x - aG m x * h)
                       + (x + h) * sin_partial (Nat.pred k) (aA m x)
                         * (aA m (x + h) - aA m x - aG m x * h)
                       + h * h * sin_partial (Nat.pred k) (aA m x) * aG m x
                       + (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                          - cos_partial k (aA m x) * (aA m (x + h) - aA m x))
                       - (x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                          + sin_partial (Nat.pred k) (aA m x)
                            * (aA m (x + h) - aA m x)))).
  { destruct k as [| p].
    - exfalso. lia.
    - unfold aF, pa_Dens.
      change (sin_partial (Datatypes.S p) (aA m x))
        with (sin_partial p (aA m x) + sin_term (Datatypes.S p) (aA m x)).
      change (sin_partial (Datatypes.S p) (aA m (x + h)))
        with (sin_partial p (aA m (x + h)) + sin_term (Datatypes.S p) (aA m (x + h))).
      change (sin_partial (Nat.pred (Datatypes.S p)) (aA m x))
        with (sin_partial p (aA m x)).
      rewrite Hg2.
      ring. }
(* [|Delta| <= 1] (both [A] and [A'] lie in [0,1]). *)
  set (dA := aA m (x + h) - aA m x) in *.
  assert (Hd1 : Qle dA (aA m (x + h))).
  { apply (pa_le_qeq_r dA (aA m (x + h) - 0%Q) (aA m (x + h))).
    - apply (pa_Qminus_le (aA m (x + h)) 0%Q (aA m x)); exact HA0.
    - assert (Hid : aA m (x + h) - 0%Q == aA m (x + h)) by ring. exact Hid. }
  assert (Hd2 : Qle (- 1)%Q dA).
  { assert (Hm : Qle (0 - aA m x) dA).
    { change (0 - aA m x) with (0 + (- aA m x)).
      change dA with (aA m (x + h) + (- aA m x)).
      apply Qplus_le_compat.
      - exact HAa0.
      - apply Qle_refl. }
    apply (Qle_trans _ (0 - aA m x)).
    - apply (pa_le_qeq_r (- 1)%Q (- aA m x) (0 - aA m x)).
      + apply (Qopp_le_compat (aA m x) 1%Q). exact HA1.
      + assert (Hid : - aA m x == 0 - aA m x) by ring. exact Hid.
    - exact Hm. }
  assert (HabdA1 : Qle (Qabs dA) 1).
  { apply (pa_two_side_abs dA 1).
    - apply (Qle_trans _ (aA m (x + h)) _).
      + exact Hd1.
      + exact HAa1.
    - exact Hd2. }
(* The three supply-lemma step bounds (interface forms) plus the
   wd transport. *)
  assert (HeqA : aA m x + dA == aA m (x + h)) by (change (aA m x + (aA m (x + h) - aA m x) == aA m (x + h)); ring).
  assert (HsA : Qle (Qabs (dA - aG m x * h))
                    (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h))).
  { change (dA - aG m x * h) with (aA m (x + h) - aA m x - aG m x * h).
    apply (pa_two_side_abs (aA m (x + h) - aA m x - aG m x * h)
             (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h))).
    - apply (pa_aA_step_le m x h Hx0 Hx1 Hh0 Hh1).
    - apply (Qle_trans _ ((- (Z.of_nat (2 ^ (4 * m + 4))%nat # 1)) * (h * h)) _).
      + apply qeq_le. ring.
      + apply (pa_aA_step_ge m x h Hx0 Hx1 Hh0 Hh1). }
  assert (HGle : Qle (aG m x) ((Z.of_nat (Datatypes.S m)) # 1))
    by (apply (pa_aG_le m x Hx0 Hx1)).
  assert (HGb : Qabs (aG m x) == aG m x)
    by (apply Qabs_pos; apply (pa_aG_nonneg m x Hx0 Hx1)).
(* [|Delta| <= rho_A h^2 + (m+1) h <= 2^{4m+5} * h]. *)
  assert (HdA : Qle (Qabs dA) (((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1) * h)).
  { assert (Htr : Qle (Qabs dA) (Qabs (dA - aG m x * h) + Qabs (aG m x * h))).
    { assert (Hsplit : dA == (dA - aG m x * h) + aG m x * h).
      { change (aA m (x + h) - aA m x
                == (aA m (x + h) - aA m x - aG m x * h) + aG m x * h).
        ring. }
      rewrite Hsplit at 1.
      apply Qabs_triangle. }
    assert (HGabs : Qle (Qabs (aG m x * h))
                        (((Z.of_nat (Datatypes.S m)) # 1) * h)).
    { assert (Habh : Qabs h == h)
        by (apply Qabs_pos; exact Hh0).
      rewrite Qabs_Qmult. rewrite HGb. rewrite Habh.
      apply (Qmult_le_compat_r (aG m x) ((Z.of_nat (Datatypes.S m)) # 1) h
               HGle Hh0). }
    assert (HrhoA0 : Qle 0 ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1))
      by (unfold Qle; simpl; lia).
    apply (Qle_trans _ ((((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h))
                        + (((Z.of_nat (Datatypes.S m)) # 1) * h)) _).
    - apply (Qle_trans _
               (Qabs (dA - aG m x * h) + Qabs (aG m x * h)) _).
      + exact Htr.
      + apply Qplus_le_compat; [exact HsA | exact HGabs].
    - assert (HSml : Qle ((Z.of_nat (Datatypes.S m)) # 1)
             ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)).
      { assert (Hn : (Datatypes.S m <= 2 ^ (4 * m + 4))%nat).
        { pose proof (pa_two_pow_ge (4 * m + 4)) as Hp. lia. }
        pose proof (proj1 (Nat2Z.inj_le _ _) Hn) as HZ.
        unfold Qle. cbn [Qnum Qden]. lia. }
      assert (Hple : Qle (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                          + ((Z.of_nat (Datatypes.S m)) # 1))
                     ((2 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1))).
      { apply (Qle_trans _ (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                            + ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1))).
        - apply Qplus_le_compat; [apply Qle_refl | exact HSml].
        - apply qeq_le. ring. }
      rewrite pa_rho5_q.
      apply (Qle_trans _ (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * h
                          + ((Z.of_nat (Datatypes.S m)) # 1) * h)).
      + apply Qplus_le_compat.
        * apply (pa_Qmult_le_l (h * h) h ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1));
            [exact Hxh2 | exact HrhoA0].
        * apply Qle_refl.
      + apply (Qle_trans _ ((((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                            + ((Z.of_nat (Datatypes.S m)) # 1)) * h)).
        * apply qeq_le. ring.
        * apply (Qmult_le_compat_r (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                                    + ((Z.of_nat (Datatypes.S m)) # 1))
                   ((2 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)) h);
            [exact Hple | exact Hh0]. }
(* The [kappa * h^2] forms of [epsS] and [epsC]. *)
  assert (Hkapow := pa_kappa_q m).
  assert (HsSq : Qle (Qabs (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                      - cos_partial k (aA m x) * dA))
                     (((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1) * (h * h))).
  { assert (Hraw : Qle (Qabs (sin_partial k (aA m x + dA) - sin_partial k (aA m x)
                       - cos_partial k (aA m x) * dA))
                      ((4 # 1) * (dA * dA)))
      by (apply (pa_sin_step k (aA m x) dA HabA1 HabdA1)).
    assert (Hbound : Qle (Qabs (sin_partial k (aA m x + dA) - sin_partial k (aA m x)
                          - cos_partial k (aA m x) * dA))
                         (((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1) * (h * h))).
    { apply (Qle_trans _ ((4 # 1) * (dA * dA)) _).
      - exact Hraw.
      - assert (Hsq : Qle (dA * dA)
                         ((((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1) * h)
                          * (((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1) * h)))
          by (apply (pa_abs_sq_le dA _); exact HdA).
        apply (Qle_trans _
                 ((4 # 1) * ((((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1) * h)
                             * (((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1) * h))) _).
        + apply (pa_Qmult_le_l (dA * dA) _ (4 # 1));
            [exact Hsq | unfold Qle; simpl; lia].
        + rewrite Hkapow.
          apply qeq_le. ring. }
    rewrite <- (pa_sin_wd k (aA m x + dA) (aA m (x + h)) HeqA).
    exact Hbound. }
  assert (HsCq : Qle (Qabs (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                      + sin_partial (Nat.pred k) (aA m x) * dA))
                     (((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1) * (h * h))).
  { assert (Hraw : Qle (Qabs (cos_partial k (aA m x + dA) - cos_partial k (aA m x)
                       + sin_partial (Nat.pred k) (aA m x) * dA))
                      ((4 # 1) * (dA * dA)))
      by (apply (pa_cos_step k (aA m x) dA Hk HabA1 HabdA1)).
    assert (Hbound : Qle (Qabs (cos_partial k (aA m x + dA) - cos_partial k (aA m x)
                          + sin_partial (Nat.pred k) (aA m x) * dA))
                         (((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1) * (h * h))).
    { apply (Qle_trans _ ((4 # 1) * (dA * dA)) _).
      - exact Hraw.
      - assert (Hsq : Qle (dA * dA)
                         ((((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1) * h)
                          * (((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1) * h)))
          by (apply (pa_abs_sq_le dA _); exact HdA).
        apply (Qle_trans _
                 ((4 # 1) * ((((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1) * h)
                             * (((Z.of_nat (2 ^ (4 * m + 5))%nat) # 1) * h))) _).
        + apply (pa_Qmult_le_l (dA * dA) _ (4 # 1));
            [exact Hsq | unfold Qle; simpl; lia].
        + rewrite Hkapow.
          apply qeq_le. ring. }
    rewrite <- (pa_cos_wd k (aA m x + dA) (aA m (x + h)) HeqA).
    exact Hbound. }
(* The five absolute-value bounds for [U]. *)
  assert (HbC : Qle (Qabs (cos_partial k (aA m x))) 3)
    by (apply (pa_cos_partial_le3 k (aA m x) HabA1)).
  assert (HbSp : Qle (Qabs (sin_partial (Nat.pred k) (aA m x))) 3)
    by (apply (pa_sin_partial_le3 (Nat.pred k) (aA m x) HabA1)).
  assert (HrhoA0 : Qle 0 ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1))
    by (unfold Qle; simpl; lia).
  assert (Hkapow0 : Qle 0 ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1))
    by (unfold Qle; simpl; lia).
  assert (HPc1 : Qle (Qabs (cos_partial k (aA m x) * (dA - aG m x * h)))
                     ((h * h) * ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)))).
  { rewrite Qabs_Qmult.
    apply (Qle_trans _
             ((Qabs (cos_partial k (aA m x)))
              * (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h))) _).
    - apply (pa_Qmult_le_l (Qabs (dA - aG m x * h))
               (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h))
               (Qabs (cos_partial k (aA m x))));
        [exact HsA | apply Qabs_nonneg].
    - apply (pa_le_qeq_r
               ((Qabs (cos_partial k (aA m x)))
                * (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h)))
               ((3 # 1) * (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h)))
               ((h * h) * ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)))).
      + apply (Qmult_le_compat_r (Qabs (cos_partial k (aA m x))) 3
                 (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h)));
          [exact HbC
          | apply Qmult_le_0_compat;
              [exact HrhoA0 | apply Qmult_le_0_compat; exact Hh0]].
      + ring. }
  assert (HPc2 : Qle (Qabs ((x + h) * sin_partial (Nat.pred k) (aA m x)
                            * (dA - aG m x * h)))
                     ((h * h) * ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)))).
  { rewrite Qabs_Qmult. rewrite Qabs_Qmult. rewrite Habxh.
    assert (Hcom2 : Qle 0 (Qabs (sin_partial (Nat.pred k) (aA m x))))
      by apply Qabs_nonneg.
    assert (Hc3 : Qle ((x + h) * Qabs (sin_partial (Nat.pred k) (aA m x))) (3 # 1)).
    { apply (Qle_trans _ (1%Q * Qabs (sin_partial (Nat.pred k) (aA m x)))).
      - apply (Qmult_le_compat_r (x + h) 1
                 (Qabs (sin_partial (Nat.pred k) (aA m x))));
          [exact Hxh1 | exact Hcom2].
      - rewrite Qmult_1_l. exact HbSp. }
    assert (Hcom : Qle 0 ((x + h) * Qabs (sin_partial (Nat.pred k) (aA m x))))
      by (apply Qmult_le_0_compat; [exact Hxp | exact Hcom2]).
    apply (Qle_trans _
             (((x + h) * Qabs (sin_partial (Nat.pred k) (aA m x)))
              * (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h))) _).
    - apply (pa_Qmult_le_l (Qabs (dA - aG m x * h))
               (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h))
               ((x + h) * Qabs (sin_partial (Nat.pred k) (aA m x))));
        [exact HsA | exact Hcom].
    - apply (Qle_trans _
               ((3 # 1) * (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h))) _).
      + apply (Qmult_le_compat_r
                 ((x + h) * Qabs (sin_partial (Nat.pred k) (aA m x))) (3 # 1)
                 (((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1) * (h * h)));
          [exact Hc3
          | apply Qmult_le_0_compat;
              [exact HrhoA0 | apply Qmult_le_0_compat; [exact Hh0 | exact Hh0]]].
      + apply qeq_le. ring. }
  assert (HPc3 : Qle (Qabs (h * h * sin_partial (Nat.pred k) (aA m x) * aG m x))
                     ((h * h) * ((3 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)))).
  { assert (HsaG : Qle (Qabs (sin_partial (Nat.pred k) (aA m x)) * Qabs (aG m x))
                       ((3 # 1) * ((Z.of_nat (Datatypes.S m)) # 1))).
    { apply (Qle_trans _ ((3 # 1) * Qabs (aG m x))).
      - apply (Qmult_le_compat_r (Qabs (sin_partial (Nat.pred k) (aA m x))) (3 # 1)
                 (Qabs (aG m x))); [exact HbSp | apply Qabs_nonneg].
      - apply (pa_Qmult_le_l (Qabs (aG m x)) ((Z.of_nat (Datatypes.S m)) # 1)
                 (3 # 1));
          [rewrite HGb; exact HGle | unfold Qle; simpl; lia]. }
    rewrite Qabs_Qmult. rewrite Qabs_Qmult. rewrite Qabs_Qmult.
    assert (Hh0b : Qabs h == h) by (apply Qabs_pos; exact Hh0).
    rewrite Hh0b.
    apply (Qle_trans _
             ((h * h) * (Qabs (sin_partial (Nat.pred k) (aA m x))
                         * Qabs (aG m x)))).
    - apply qeq_le. ring.
    - apply (pa_Qmult_le_l (Qabs (sin_partial (Nat.pred k) (aA m x))
                            * Qabs (aG m x))
               ((3 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)) (h * h));
        [exact HsaG | apply Qmult_le_0_compat; [exact Hh0 | exact Hh0]]. }
  assert (HPc4 : Qle (Qabs (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                            - cos_partial k (aA m x) * dA))
                     ((h * h) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1))).
  { apply (Qle_trans _ (((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1) * (h * h)) _).
    - exact HsSq.
    - apply qeq_le. ring. }
  assert (HPc5 : Qle (Qabs ((x + h) * (cos_partial k (aA m (x + h))
                                      - cos_partial k (aA m x)
                                      + sin_partial (Nat.pred k) (aA m x) * dA)))
                     ((h * h) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1))).
  { rewrite Qabs_Qmult. rewrite Habxh.
    apply (Qle_trans _
             ((x + h) * (((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1) * (h * h))) _).
    - apply (pa_Qmult_le_l (Qabs (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                          + sin_partial (Nat.pred k) (aA m x) * dA))
               (((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1) * (h * h)) (x + h));
        [exact HsCq | exact Hxp].
    - apply (Qle_trans _ (1%Q * (((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1) * (h * h))) _).
      + apply (Qmult_le_compat_r (x + h) 1
                 (((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1) * (h * h)));
          [exact Hxh1
          | apply Qmult_le_0_compat;
              [exact Hkapow0 | apply Qmult_le_0_compat; [exact Hh0 | exact Hh0]]].
      + apply qeq_le. ring. }
(* Collecting the five bounds:
   [|U| <= h^2 * (6 rho_A + 3(m+1) + 2 kappa)]. *)
  assert (HU : Qle (Qabs (cos_partial k (aA m x) * (dA - aG m x * h)
                     + (x + h) * sin_partial (Nat.pred k) (aA m x)
                       * (dA - aG m x * h)
                     + h * h * sin_partial (Nat.pred k) (aA m x) * aG m x
                     + (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                        - cos_partial k (aA m x) * dA)
                     - (x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                        + sin_partial (Nat.pred k) (aA m x) * dA)))
           ((h * h) * ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                       + (3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                       + (3 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)
                       + (2 # 1) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1)))).
  { apply (pa_le_qeq_r
             (Qabs (cos_partial k (aA m x) * (dA - aG m x * h)
                    + (x + h) * sin_partial (Nat.pred k) (aA m x)
                      * (dA - aG m x * h)
                    + h * h * sin_partial (Nat.pred k) (aA m x) * aG m x
                    + (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                       - cos_partial k (aA m x) * dA)
                    - (x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                       + sin_partial (Nat.pred k) (aA m x) * dA)))
             ((h * h) * ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1))
              + (h * h) * ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1))
              + (h * h) * ((3 # 1) * ((Z.of_nat (Datatypes.S m)) # 1))
              + (h * h) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1)
              + (h * h) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1))
             ((h * h) * ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                         + (3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                         + (3 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)
                         + (2 # 1) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1)))).
    - apply (Qle_trans _
               (Qabs (cos_partial k (aA m x) * (dA - aG m x * h)
                      + (x + h) * sin_partial (Nat.pred k) (aA m x)
                        * (dA - aG m x * h)
                      + h * h * sin_partial (Nat.pred k) (aA m x) * aG m x
                      + (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                         - cos_partial k (aA m x) * dA))
                + Qabs (- ((x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                           + sin_partial (Nat.pred k) (aA m x) * dA))))).
      + apply Qabs_triangle.
      + apply (Qle_trans _
                 (Qabs (cos_partial k (aA m x) * (dA - aG m x * h)
                        + (x + h) * sin_partial (Nat.pred k) (aA m x)
                          * (dA - aG m x * h)
                        + h * h * sin_partial (Nat.pred k) (aA m x) * aG m x
                        + (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                           - cos_partial k (aA m x) * dA))
                  + Qabs ((x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                            + sin_partial (Nat.pred k) (aA m x) * dA)))).
        * apply Qplus_le_compat;
            [apply Qle_refl
            | apply (pa_le_qeq_r
                       (Qabs (- ((x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                                 + sin_partial (Nat.pred k) (aA m x) * dA))))
                       (Qabs ((x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                                + sin_partial (Nat.pred k) (aA m x) * dA)))
                       (Qabs ((x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                                + sin_partial (Nat.pred k) (aA m x) * dA))));
               [apply qeq_le; apply Qabs_opp | ring]].
        * apply Qplus_le_compat.
          { apply (Qle_trans _
                     (Qabs (cos_partial k (aA m x) * (dA - aG m x * h)
                            + (x + h) * sin_partial (Nat.pred k) (aA m x)
                              * (dA - aG m x * h)
                            + h * h * sin_partial (Nat.pred k) (aA m x) * aG m x)
                      + Qabs (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                              - cos_partial k (aA m x) * dA))).
            - apply Qabs_triangle.
            - apply Qplus_le_compat.
              { apply (Qle_trans _
                         (Qabs (cos_partial k (aA m x) * (dA - aG m x * h)
                                + (x + h) * sin_partial (Nat.pred k) (aA m x)
                                  * (dA - aG m x * h))
                          + Qabs (h * h * sin_partial (Nat.pred k) (aA m x) * aG m x))).
                - apply Qabs_triangle.
                - apply Qplus_le_compat.
                  { apply (Qle_trans _
                             (Qabs (cos_partial k (aA m x) * (dA - aG m x * h))
                              + Qabs ((x + h) * sin_partial (Nat.pred k) (aA m x)
                                      * (dA - aG m x * h)))).
                    - apply Qabs_triangle.
                    - apply Qplus_le_compat; [exact HPc1 | exact HPc2]. }
                  exact HPc3. }
              exact HPc4. }
          exact HPc5.
    - ring. }
(* Final assembly:
   [|T| == (1+x^2) * |U| <= h^2 (1+x^2) * 2^{8m+16}]. *)
  apply (Qle_trans _
           ((1 + x * x)
            * Qabs (cos_partial k (aA m x) * (dA - aG m x * h)
                    + (x + h) * sin_partial (Nat.pred k) (aA m x)
                      * (dA - aG m x * h)
                    + h * h * sin_partial (Nat.pred k) (aA m x) * aG m x
                    + (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                       - cos_partial k (aA m x) * dA)
                    - (x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                       + sin_partial (Nat.pred k) (aA m x) * dA)))).
  - rewrite Hdec.
    rewrite Qabs_Qmult.
    rewrite Habx2.
    apply Qle_refl.
  - assert (Hk14 : Qle ((h * h) * ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                                  + (3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                                  + (3 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)
                                  + (2 # 1) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1)))
                        ((h * h) * ((Z.of_nat (2 ^ (8 * m + 14))%nat) # 1))).
    { apply (pa_Qmult_le_l
               ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                + (3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                + (3 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)
                + (2 # 1) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1))
               ((Z.of_nat (2 ^ (8 * m + 14))%nat) # 1) (h * h));
        [apply pa_pow_chain_le
        | apply Qmult_le_0_compat; [exact Hh0 | exact Hh0]]. }
    assert (Hk16 : Qle ((h * h) * ((Z.of_nat (2 ^ (8 * m + 14))%nat) # 1))
                        ((h * h) * ((Z.of_nat (2 ^ (8 * m + 16))%nat) # 1))).
    { apply (pa_Qmult_le_l ((Z.of_nat (2 ^ (8 * m + 14))%nat) # 1)
               ((Z.of_nat (2 ^ (8 * m + 16))%nat) # 1) (h * h));
        [apply pa_pow_mono_le
        | apply Qmult_le_0_compat; [exact Hh0 | exact Hh0]]. }
    apply (pa_le_qeq_r
             ((1 + x * x)
              * Qabs (cos_partial k (aA m x) * (dA - aG m x * h)
                      + (x + h) * sin_partial (Nat.pred k) (aA m x)
                        * (dA - aG m x * h)
                      + h * h * sin_partial (Nat.pred k) (aA m x) * aG m x
                      + (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                         - cos_partial k (aA m x) * dA)
                      - (x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                         + sin_partial (Nat.pred k) (aA m x) * dA)))
             ((1 + x * x)
              * ((h * h) * ((Z.of_nat (2 ^ (8 * m + 16))%nat) # 1)))
             ((h * h * (1 + x * x)) * ((Z.of_nat (2 ^ (8 * m + 16))%nat) # 1))).
    + apply (pa_Qmult_le_l
               (Qabs (cos_partial k (aA m x) * (dA - aG m x * h)
                      + (x + h) * sin_partial (Nat.pred k) (aA m x)
                        * (dA - aG m x * h)
                      + h * h * sin_partial (Nat.pred k) (aA m x) * aG m x
                      + (sin_partial k (aA m (x + h)) - sin_partial k (aA m x)
                         - cos_partial k (aA m x) * dA)
                      - (x + h) * (cos_partial k (aA m (x + h)) - cos_partial k (aA m x)
                         + sin_partial (Nat.pred k) (aA m x) * dA)))
               ((h * h) * ((Z.of_nat (2 ^ (8 * m + 16))%nat) # 1)) (1 + x * x));
        [apply (Qle_trans _
                   ((h * h) * ((Z.of_nat (2 ^ (8 * m + 14))%nat) # 1)));
           [apply (Qle_trans _
                      ((h * h) * ((3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                       + (3 # 1) * ((Z.of_nat (2 ^ (4 * m + 4))%nat) # 1)
                       + (3 # 1) * ((Z.of_nat (Datatypes.S m)) # 1)
                       + (2 # 1) * ((Z.of_nat (2 ^ (8 * m + 12))%nat) # 1))));
             [exact HU | exact Hk14]
           | exact Hk16]
        | exact Hx2p].
    + ring.
Qed.
(* ============================================================
   Discrete Gronwall invariant, the assembly of [K], and the main
   statement [piL_arctan_fixed_sc] (the [Q] side).

   Mathematical mission.  The discrete-Gronwall final bound
     [|aF k m 1| <= (12/(4m+5) + 1/64/(4m+5)) * Q
                    + (9/4)/q_fact(2k+1) * Q],
   from which, for any [e > 0], a threshold [K] is constructively
   produced (the half-power Archimedean property [pa_q_half_arch])
   such that
   [|sin_partial k (lp_odd m) - cos_partial k (lp_odd m)| < e]
   for all [k, m >= K] (switching along the fixed-value bridge
   [aA m 1 == lp_odd m]).

   Dependencies.  The earlier results of [PiArctanFixedQ]
   ([aF]/[aA]/[aG]/[pa_D_pos]/[pa_qpow_le_one]/[pa_aA_nonneg]/
   [pa_aA_le_one]/[pa_aF_step], etc.) plus [PiKernelSlack]
   ([q_pow]/[q_fact]/[sin_partial]/[cos_partial]/[sin_term]/
   [qeq_le]/[lw0_Qabs_pos_eq]/[leibsep_qlt_1]/
   [lw0_pitB_pair_conv_qabs_wd]).
   Statements.  Stdlib [Qle]/[Qlt]/[Qeq] (purely constructive); the
   main statement is carried by a [sig] (at [Set]); [lia]/[field]/
   [cbn] only in auxiliary bookkeeping steps.  The step-inequality
   premise is [pa_aF_step].
   References.  The discrete-Gronwall invariant recursion (the
   grid-weighted accumulator [pa_accF]) and the Archimedean property
   of the half powers [(1/2)^t] (for every positive [e] a threshold
   [t] with [(1/2)^t < e] exists).
   Constructivity.  Fully proved, with no non-constructive
   principles; all premises except [pa_aF_step] are discharged
   inside the proofs.
   Build.  [coqc -native-compiler no -q -Q . "" PiArctanFixedQ.v].
   ============================================================ *)

(* ---------- C0. Bookkeeping basics ---------- *)

Lemma pa_nat_pow2_pos : forall n : nat, (0 < 2 ^ n)%nat.
Proof.
  intro n.
  induction n as [| p IH].
  - simpl. lia.
  - rewrite pa_two_pow_S. lia.
Qed.

Lemma pa_qle_add_pos : forall (a X : Q), Qle 0 X -> Qle a (a + X).
Proof.
  intros a X HX.
  apply leibsep_qle_of_minus.
  apply (pa_le_qeq_r 0%Q X ((a + X) - a)%Q); [exact HX | ring].
Qed.

Lemma pa_qlt_qeq_lr : forall x y u v : Q, Qlt x y -> x == u -> y == v -> Qlt u v.
Proof.
  intros x y u v Hlt Hx Hy.
  rewrite <- Hx, <- Hy.
  exact Hlt.
Qed.

Lemma pa_qpow_half_inv : forall t : nat,
  q_pow (1 # 2)%Q t == (1 # 1) / (Z.of_nat (2 ^ t) # 1).
Proof.
  intro t.
  induction t as [| p IH].
  - reflexivity.
  - change (q_pow (1 # 2)%Q (Datatypes.S p)) with ((1 # 2) * q_pow (1 # 2)%Q p).
    rewrite IH.
    rewrite pa_two_pow_S.
    rewrite Nat2Z.inj_mul.
    change (Z.of_nat 2) with 2%Z.
    destruct (Z.of_nat (2 ^ p)) as [| w' | w'] eqn:Ew;
    unfold Qdiv, Qeq; cbn; lia.
Qed.


Lemma pa_abs_nonneg : forall x : Q, Qle 0 (Qabs x).
Proof.
  intro x.
  destruct (Qlt_le_dec 0 x) as [Hx | Hx].
  - rewrite (lw0_Qabs_pos_eq x (Qle_to_QleT' 0 x (Qlt_le_weak 0 x Hx))).
    exact (Qlt_le_weak 0 x Hx).
  - assert (Hnx : Qle 0 (- x)%Q).
    { apply (pa_le_qeq_r 0%Q (0 - x)%Q (- x)%Q).
      - apply leibsep_qle_minus. exact Hx.
      - ring. }
    assert (Hax : (Qabs x == - x)%Q).
    { assert (H1 : (Qabs (- x) == - x)%Q)
        by (apply lw0_Qabs_pos_eq; exact (Qle_to_QleT' 0 (- x) Hnx)).
      rewrite Qabs_opp in H1. exact H1. }
    rewrite Hax. exact Hnx.
Qed.

Lemma pa_abs_scale_unit : forall (k : nat) (z : Q),
  Qabs (q_pow (-1) k * z) == Qabs z.
Proof.
  intro k. induction k as [| p IH]; intro z.
  - change (q_pow (-1) 0) with 1%Q.
    rewrite Qmult_1_l. apply Qeq_refl.
  - change (q_pow (-1) (Datatypes.S p)) with ((-1) * q_pow (-1) p).
    assert (Hmv : (-1) * q_pow (-1) p * z == - (q_pow (-1) p * z)) by ring.
    rewrite Hmv. rewrite Qabs_opp. apply IH.
Qed.

Lemma pa_abs_mul_pos : forall (c w : Q),
  Qle 0 c -> Qabs (c * w) == c * Qabs w.
Proof.
  intros c w Hc.
  destruct (Qlt_le_dec 0 w) as [Hw | Hw].
  - assert (Hcw : Qle 0 (c * w))
      by (apply Qmult_le_0_compat; [ exact Hc | apply Qlt_le_weak; exact Hw ]).
    rewrite (lw0_Qabs_pos_eq (c * w) (Qle_to_QleT' _ _ Hcw)).
    rewrite (lw0_Qabs_pos_eq w (Qle_to_QleT' 0 w (Qlt_le_weak 0 w Hw))).
    reflexivity.
  - assert (Hcw0 : Qle (c * w) 0).
    { assert (Hcwr : c * w == w * c) by ring.
      rewrite Hcwr.
      apply (Qle_trans _ (0 * c)%Q _).
      + apply Qmult_le_compat_r; [ exact Hw | exact Hc ].
      + rewrite Qmult_0_l. apply Qle_refl. }
    assert (H0cw : Qle 0 (- (c * w))%Q)
      by (apply (pa_le_qeq_r 0%Q (0 - c * w)%Q (- (c * w))%Q);
          [ apply leibsep_qle_minus; exact Hcw0 | ring ]).
    assert (Hwabs : (Qabs w == - w)%Q).
    { assert (Hnw : Qle 0 (- w)%Q).
      { apply (pa_le_qeq_r 0%Q (0 - w)%Q (- w)%Q);
          [ apply leibsep_qle_minus; exact Hw | ring ]. }
      assert (H1 : (Qabs (- w) == - w)%Q)
        by (apply lw0_Qabs_pos_eq; exact (Qle_to_QleT' 0 (- w) Hnw)).
      rewrite Qabs_opp in H1. exact H1. }
    rewrite <- (Qabs_opp (c * w)).
    rewrite (lw0_Qabs_pos_eq (- (c * w)) (Qle_to_QleT' 0 (- (c * w)) H0cw)).
    rewrite Hwabs. ring.
Qed.

(** Monotonicity of the factorial and its lower bound against [2^n]
    (entirely on the [Q] side, with no [nat] factorial). *)
Lemma pa_qfact_mono : forall n m : nat, (n <= m)%nat -> Qle (q_fact n) (q_fact m).
Proof.
  intros n m Hnm.
  induction m as [| p IH].
  - replace n with 0%nat by lia. apply Qle_refl.
  - destruct (Nat.eq_dec n (Datatypes.S p)) as [Heq | Hne].
    + rewrite Heq. apply Qle_refl.
    + assert (Hn : (n <= p)%nat) by lia.
      apply (Qle_trans _ (q_fact p) _).
      * apply IH. exact Hn.
      * change (q_fact (Datatypes.S p)) with ((Z.of_nat (Datatypes.S p) # 1) * q_fact p).
        apply (Qle_trans _ (q_fact p * 1)%Q).
        -- rewrite Qmult_1_r. apply Qle_refl.
        -- rewrite (Qmult_comm (Z.of_nat (Datatypes.S p) # 1)%Q (q_fact p)).
           apply (pa_Qmult_le_l (1 # 1)%Q (Z.of_nat (Datatypes.S p) # 1)%Q (q_fact p)).
           ++ unfold Qle. simpl. lia.
           ++ apply Qlt_le_weak. apply q_fact_pos.
Qed.

Lemma pa_qfact_ge_pow2Q : forall n : nat,
  Qle (q_pow (2 # 1)%Q n) (q_fact (Datatypes.S n)).
Proof.
  intro n.
  induction n as [| p IH].
  - change (q_pow (2 # 1)%Q 0) with 1%Q.
    change (q_fact 1) with ((Z.of_nat 1 # 1) * q_fact 0)%Q.
    unfold Qle, Qmult. simpl. lia.
  - change (q_pow (2 # 1)%Q (Datatypes.S p)) with ((2 # 1) * q_pow (2 # 1)%Q p).
    change (q_fact (Datatypes.S (Datatypes.S p)))
      with ((Z.of_nat (Datatypes.S (Datatypes.S p)) # 1) * q_fact (Datatypes.S p))%Q.
    apply (Qle_trans _ ((2 # 1) * q_fact (Datatypes.S p)) _).
    + apply (pa_Qmult_le_l (q_pow (2 # 1)%Q p) (q_fact (Datatypes.S p)) (2 # 1)%Q);
        [exact IH | unfold Qle; simpl; lia].
    + apply Qmult_le_compat_r.
      * unfold Qle. simpl. lia.
      * apply Qlt_le_weak. apply q_fact_pos.
Qed.

(** The coherence bridge between powers of two and [Q] powers. *)
Lemma pa_qpow2_coherence : forall n : nat,
  q_pow (2 # 1)%Q n == (Z.of_nat (2 ^ n))%nat # 1.
Proof.
  intro n.
  induction n as [| p IH].
  - reflexivity.
  - change (q_pow (2 # 1)%Q (Datatypes.S p)) with ((2 # 1) * q_pow (2 # 1)%Q p).
    rewrite pa_two_pow_S. rewrite IH.
    rewrite (Nat2Z.inj_mul 2 (2 ^ p)).
    change (Z.of_nat 2) with 2%Z. reflexivity.
Qed.

Lemma pa_qpow_half_coherence : forall t : nat,
  q_pow (1 # 2)%Q t == (1 # 1) * ((1 # 1) / ((Z.of_nat (2 ^ t))%nat # 1)).
Proof.
  intro t.
  induction t as [| p IH].
  - reflexivity.
  - change (q_pow (1 # 2)%Q (Datatypes.S p)) with ((1 # 2) * q_pow (1 # 2)%Q p).
    rewrite pa_two_pow_S. rewrite IH.
    replace (Z.of_nat (2 * 2 ^ p)) with (2 * Z.of_nat (2 ^ p))%Z
      by (rewrite Nat2Z.inj_mul; reflexivity).
    destruct (Z.of_nat (2 ^ p)) as [| w' | w'] eqn:Ew;
      unfold Qdiv, Qeq; cbn; lia.
Qed.

(** Antitonicity of the reciprocal. *)
Lemma pa_inv_mono : forall a b : Q,
  Qlt 0 a -> Qle a b -> Qle ((1 # 1) / b) ((1 # 1) / a).
Proof.
  intros a b Ha Hab.
  assert (Hab0 : Qlt 0 b) by (apply (Qlt_le_trans 0 a b); [exact Ha | exact Hab]).
  assert (Habp : Qlt 0 (a * b)) by (apply Qmult_lt_0_compat; assumption).
  assert (Hl : ((1 # 1) / b) * (a * b) == a).
  { field; apply pa_qpos_neq0; exact Hab0. }
  assert (Hr : ((1 # 1) / a) * (a * b) == b).
  { field; apply pa_qpos_neq0; exact Ha. }
  apply (proj1 (Qmult_le_r ((1 # 1) / b) ((1 # 1) / a) (a * b) Habp)).
  rewrite Hl, Hr. exact Hab.
Qed.

(** Basic lemmas for [h := 1/N]. *)
Lemma pa_h_pos : forall N : nat, (0 < N)%nat ->
  Qlt 0 ((1 # 1) / (Z.of_nat N # 1))%Q.
Proof.
  intros N HN.
  assert (Hz : Qlt 0 ((Z.of_nat N) # 1)).
  { unfold Qlt. simpl. lia. }
  change ((1 # 1) / (Z.of_nat N # 1))%Q with ((1 # 1) * (/ ((Z.of_nat N) # 1)))%Q.
  apply Qmult_lt_0_compat; [exact leibsep_qlt_1 | apply Qinv_lt_0_compat; exact Hz].
Qed.

Lemma pa_hN : forall N : nat, (0 < N)%nat ->
  (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1)) == 1.
Proof.
  intros N HN.
  assert (Hz : ~ ((Z.of_nat N # 1) == 0)%Q).
  { apply pa_qpos_neq0. unfold Qlt. simpl. lia. }
  field; assumption.
Qed.

(* ---------- C1. Zeros and the [|A| <= 1] chain ---------- *)

Lemma pa_qA_pos_zero : forall n : nat, (1 <= n)%nat -> q_pow 0 n == 0.
Proof.
  intro n. induction n as [| p IH]; intro Hn.
  - exfalso. lia.
  - change (q_pow 0 (Datatypes.S p)) with (0 * q_pow 0 p). ring.
Qed.

Lemma pa_aA_zero : forall m : nat, aA m 0 == 0.
Proof.
  intro m.
  induction m as [| p IH].
  - change (aA 0 0) with (aA_term 0 0).
    unfold aA_term.
    replace (4 * 0 + 1)%nat with 1%nat by lia.
    replace (4 * 0 + 3)%nat with 3%nat by lia.
    rewrite (pa_qA_pos_zero 1) by lia.
    rewrite (pa_qA_pos_zero 3) by lia.
    ring.
  - change (aA (Datatypes.S p) 0) with (aA p 0 + aA_term (Datatypes.S p) 0).
    rewrite IH.
    unfold aA_term.
    rewrite (pa_qA_pos_zero (4 * Datatypes.S p + 1)) by lia.
    replace (4 * Datatypes.S p + 3)%nat with (Datatypes.S (4 * Datatypes.S p + 2))%nat by lia.
    rewrite (pa_qA_pos_zero (Datatypes.S (4 * Datatypes.S p + 2))) by lia.
    ring.
Qed.

Lemma pa_sin_partial_zero : forall k : nat, sin_partial k 0 == 0.
Proof.
  intro k.
  induction k as [| p IH].
  - change (sin_partial 0 0) with (sin_term 0 0).
    unfold sin_term.
    replace (Datatypes.S (2 * 0))%nat with 1%nat by lia.
    rewrite (pa_qA_pos_zero 1) by lia.
    assert (Hz : 0 / q_fact 1 == 0) by (unfold Qdiv; ring).
    rewrite Hz. ring.
  - change (sin_partial (Datatypes.S p) 0) with (sin_partial p 0 + sin_term (Datatypes.S p) 0).
    rewrite IH.
    unfold sin_term.
    rewrite (pa_qA_pos_zero (Datatypes.S (2 * Datatypes.S p))) by lia.
    assert (Hz : 0 / q_fact (S (2 * Datatypes.S p)) == 0)
      by (unfold Qdiv; ring).
    rewrite Hz. ring.
Qed.

Lemma pa_mult_aA_zero : forall (m : nat) (z : Q), aA m 0 * z == 0.
Proof.
  intros m z.
  apply (Qeq_trans (aA m 0 * z) (0 * z) 0).
  - exact (Qmult_comp (aA m 0) 0 (pa_aA_zero m) z z (Qeq_refl z)).
  - apply Qmult_0_l.
Qed.

Lemma pa_sin_partial_aA_zero : forall (k m : nat), sin_partial k (aA m 0) == 0.
Proof.
  intros k m.
  induction k as [| p IH].
  - change (sin_partial 0 (aA m 0)) with (sin_term 0 (aA m 0)).
    unfold sin_term.
    change (q_pow (aA m 0) (Datatypes.S (2 * 0))) with (aA m 0 * q_pow (aA m 0) (2 * 0)).
    rewrite (pa_mult_aA_zero m).
    assert (Hz : 0 / q_fact (Datatypes.S (2 * 0)) == 0) by (unfold Qdiv; ring).
    rewrite Hz. ring.
  - change (sin_partial (Datatypes.S p) (aA m 0))
      with (sin_partial p (aA m 0) + sin_term (Datatypes.S p) (aA m 0)).
    rewrite IH.
    unfold sin_term.
    change (q_pow (aA m 0) (Datatypes.S (2 * Datatypes.S p)))
      with (aA m 0 * q_pow (aA m 0) (2 * Datatypes.S p)).
    rewrite (pa_mult_aA_zero m).
    assert (Hz : 0 / q_fact (Datatypes.S (2 * Datatypes.S p)) == 0)
      by (unfold Qdiv; ring).
    rewrite Hz. ring.
Qed.

Lemma pa_aF_zero : forall (k m : nat), aF k m 0 == 0.
Proof.
  intros k m.
  unfold aF.
  transitivity (sin_partial k (aA m 0)).
  - ring.
  - apply pa_sin_partial_aA_zero.
Qed.

(* ---------- C2. The grid ---------- *)

Definition pa_grid (N i : nat) : Q :=
  (Z.of_nat i # 1) * ((1 # 1) / (Z.of_nat N # 1))%Q.

Lemma pa_grid_zero : forall N : nat, pa_grid N 0 == 0.
Proof. intro N. unfold pa_grid. ring. Qed.

Lemma pa_grid_S : forall (N p : nat), (0 < N)%nat ->
  pa_grid N (Datatypes.S p) == pa_grid N p + ((1 # 1) / (Z.of_nat N # 1))%Q.
Proof.
  intros N p HN.
  unfold pa_grid.
  replace (Z.of_nat (Datatypes.S p)) with (Z.of_nat p + 1)%Z
    by lia.
  change ((Z.of_nat p + 1) # 1) with (inject_Z (Z.of_nat p + 1)).
  rewrite inject_Z_plus.
  change (inject_Z 1) with 1%Q.
  rewrite Qmult_plus_distr_l.
  rewrite Qmult_1_l.
  change (inject_Z (Z.of_nat p)) with (Z.of_nat p # 1).
  reflexivity.
Qed.

Lemma pa_grid_nonneg : forall (N i : nat), (0 < N)%nat -> Qle 0 (pa_grid N i).
Proof.
  intros N i HN.
  unfold pa_grid.
  apply Qmult_le_0_compat.
  - unfold Qle. simpl. lia.
  - apply Qlt_le_weak. apply pa_h_pos. exact HN.
Qed.

Lemma pa_grid_le_1 : forall (N i : nat), (0 < N)%nat -> (i <= N)%nat ->
  Qle (pa_grid N i) 1.
Proof.
  intros N i HN Hi.
  apply (pa_le_qeq_r _ ((Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))) 1%Q).
  - unfold pa_grid.
    apply Qmult_le_compat_r.
    + unfold Qle. simpl. rewrite !Z.mul_1_r.
      apply (proj1 (Nat2Z.inj_le i N)). exact Hi.
    + apply Qlt_le_weak. apply pa_h_pos. exact HN.
  - apply pa_hN. exact HN.
Qed.

Lemma pa_grid_one : forall N : nat, (0 < N)%nat -> pa_grid N N == 1.
Proof.
  intros N HN.
  assert (Hz : ~ ((Z.of_nat N # 1) == 0)%Q).
  { apply pa_qpos_neq0. unfold Qlt. simpl. lia. }
  unfold pa_grid. field; assumption.
Qed.

(* ---------- C3. The weighted accumulator (a generic telescope) ---------- *)

Fixpoint pa_wsumG (N : nat) (g : nat -> Q) (i : nat) : Q :=
  match i with
  | 0%nat => 0%Q
  | Datatypes.S p => pa_wsumG N g p + ((1 # 1) / (Z.of_nat N # 1))%Q * g p
  end.

Lemma pa_wsumG_nonneg : forall (N i : nat) (g : nat -> Q),
  (0 < N)%nat -> (forall j, (j < i)%nat -> Qle 0 (g j)) ->
  Qle 0 (pa_wsumG N g i).
Proof.
  intros N i g HN Hg.
  induction i as [| p IH].
  - apply Qle_refl.
  - change (pa_wsumG N g (Datatypes.S p))
      with (pa_wsumG N g p + ((1 # 1) / (Z.of_nat N # 1))%Q * g p).
    apply (Qplus_le_compat 0%Q (pa_wsumG N g p) 0%Q
             (((1 # 1) / (Z.of_nat N # 1))%Q * g p)).
    + apply IH. intros j Hj. apply Hg. lia.
    + apply Qmult_le_0_compat.
      * apply Qlt_le_weak. apply pa_h_pos. exact HN.
      * apply Hg. lia.
Qed.

Lemma pa_wsumG_scal_add : forall (N i : nat) (a : Q) (f g : nat -> Q),
  pa_wsumG N (fun j => a * f j + g j) i
  == a * pa_wsumG N f i + pa_wsumG N g i.
Proof.
  intros N i a f g.
  induction i as [| p IH].
  - cbn [pa_wsumG]. ring.
  - change (pa_wsumG N (fun j => a * f j + g j) (Datatypes.S p))
      with (pa_wsumG N (fun j => a * f j + g j) p
            + ((1 # 1) / (Z.of_nat N # 1))%Q * (a * f p + g p)).
    change (pa_wsumG N f (Datatypes.S p))
      with (pa_wsumG N f p + ((1 # 1) / (Z.of_nat N # 1))%Q * f p).
    change (pa_wsumG N g (Datatypes.S p))
      with (pa_wsumG N g p + ((1 # 1) / (Z.of_nat N # 1))%Q * g p).
    rewrite IH. ring.
Qed.

Lemma pa_wsumG_telescope : forall (N i : nat) (g Phi : nat -> Q),
  (forall j, (j < i)%nat ->
     Qle (((1 # 1) / (Z.of_nat N # 1))%Q * g j) (Phi (Datatypes.S j) - Phi j)) ->
  Qle (pa_wsumG N g i) (Phi i - Phi 0%nat).
Proof.
  intros N i g Phi Hstep.
  induction i as [| p IH].
  - cbn [pa_wsumG].
    assert (Hz : Phi 0%nat - Phi 0%nat == 0) by ring.
    rewrite Hz. apply Qle_refl.
  - assert (Hp : (p < Datatypes.S p)%nat) by lia.
    pose proof (Hstep p Hp) as Hpstep.
    change (pa_wsumG N g (Datatypes.S p))
      with (pa_wsumG N g p + ((1 # 1) / (Z.of_nat N # 1))%Q * g p).
    apply (pa_le_qeq_r
             (pa_wsumG N g p + ((1 # 1) / (Z.of_nat N # 1))%Q * g p)
             ((Phi p - Phi 0%nat) + (Phi (Datatypes.S p) - Phi p))
             (Phi (Datatypes.S p) - Phi 0%nat)).
    + apply Qplus_le_compat;
        [apply IH; intros j Hj; apply Hstep; lia | exact Hpstep].
    + ring.
Qed.

(* ---------- C4. The residual rate and the accumulator ---------- *)

Definition pa_gCst (m : nat) : Q := (Z.of_nat (2 ^ (8 * m + 16))%nat) # 1.

Definition pa_r (k m : nat) (x : Q) : Q :=
  (6 # 1)%Q * q_pow x (4 * m + 4) + Qabs (sin_term k (aA m x)).

Lemma pa_r_nonneg : forall (k m : nat) (x : Q),
  Qle 0 x -> Qle 0 (pa_r k m x).
Proof.
  intros k m x Hx.
  unfold pa_r.
  apply (Qplus_le_compat 0%Q ((6 # 1)%Q * q_pow x (4 * m + 4)) 0%Q
           (Qabs (sin_term k (aA m x)))).
  - apply Qmult_le_0_compat; [unfold Qle; simpl; lia | apply (q_pow_nonneg x (4 * m + 4) Hx)].
  - apply pa_abs_nonneg.
Qed.


Definition pa_accF (k m N : nat) (i : nat) : Q :=
  pa_wsumG N (fun j => pa_r k m (pa_grid N j)) i
  + ((1 # 1) / (Z.of_nat N # 1))%Q * ((1 # 1) / (Z.of_nat N # 1))%Q
    * pa_gCst m * (Z.of_nat i # 1).

Lemma pa_accF_nonneg : forall (k m N i : nat), (0 < N)%nat ->
  Qle 0 (pa_accF k m N i).
Proof.
  intros k m N i HN.
  unfold pa_accF.
  apply (Qplus_le_compat 0%Q
           (pa_wsumG N (fun j => pa_r k m (pa_grid N j)) i) 0%Q
           (((1 # 1) / (Z.of_nat N # 1))%Q * ((1 # 1) / (Z.of_nat N # 1))%Q
              * pa_gCst m * (Z.of_nat i # 1))).
  - apply (pa_wsumG_nonneg N i (fun j => pa_r k m (pa_grid N j))).
    + exact HN.
    + intros j Hj. apply pa_r_nonneg. apply pa_grid_nonneg. exact HN.
  - apply Qmult_le_0_compat.
    + apply Qmult_le_0_compat.
      * apply Qmult_le_0_compat;
          apply Qlt_le_weak; apply pa_h_pos; exact HN.
      * unfold pa_gCst, Qle. cbn [Qnum Qden].
        pose proof (pa_nat_pow2_pos (8 * m + 16)). lia.
    + unfold Qle. cbn [Qnum Qden]. lia.
Qed.


Lemma pa_accF_S : forall (k m N p : nat), (0 < N)%nat ->
  pa_accF k m N (Datatypes.S p)
  == pa_accF k m N p
     + ((1 # 1) / (Z.of_nat N # 1))%Q
       * (pa_r k m (pa_grid N p)
          + ((1 # 1) / (Z.of_nat N # 1))%Q * pa_gCst m).
Proof.
  intros k m N p HN.
  unfold pa_accF.
  change (pa_wsumG N (fun j => pa_r k m (pa_grid N j)) (Datatypes.S p))
    with (pa_wsumG N (fun j => pa_r k m (pa_grid N j)) p
          + ((1 # 1) / (Z.of_nat N # 1))%Q * pa_r k m (pa_grid N p)).
  replace (Z.of_nat (Datatypes.S p)) with (Z.of_nat p + 1)%Z
    by lia.
  change ((Z.of_nat p + 1) # 1) with (inject_Z (Z.of_nat p + 1)).
  rewrite inject_Z_plus.
  change (inject_Z 1) with 1%Q.
  change (inject_Z (Z.of_nat p)) with (Z.of_nat p # 1).
  ring.
Qed.

(** [|Dens| <= pa_r] (consuming [pa_sin_partial_le3],
    [pa_cos_partial_le3] and [pa_aA_le_one]). *)
Lemma pa_Dens_abs_le : forall (k m : nat) (x : Q),
  (1 <= k)%nat -> Qle 0 x -> Qle x 1 ->
  Qle (Qabs (pa_Dens k m x)) (pa_r k m x).
Proof.
  intros k m x Hk Hx0 Hx1.
  assert (HA1 : Qle (Qabs (aA m x)) 1).
  { assert (HA0 : Qle 0 (aA m x)) by (apply (pa_aA_nonneg m x Hx0 Hx1)).
    assert (HAle : Qle (aA m x) 1) by (apply (pa_aA_le_one m x Hx0 Hx1)).
    rewrite (lw0_Qabs_pos_eq (aA m x) (Qle_to_QleT' _ _ HA0)).
    exact HAle. }
  unfold pa_Dens, pa_r.
  assert (Hpow0 : Qle 0 (q_pow x (4 * m + 4))) by (apply (q_pow_nonneg x (4 * m + 4) Hx0)).
(* |x^{4m+4}(C+xS_pred)+x*st| <= |x^{4m+4}(C+xS_pred)| + |x*st| *)
  apply (Qle_trans _
           (Qabs (q_pow x (4 * m + 4)
                  * (cos_partial k (aA m x)
                     + x * sin_partial (Nat.pred k) (aA m x)))
            + Qabs (x * sin_term k (aA m x)))).
  { apply Qabs_triangle. }
  apply (Qle_trans _
           (q_pow x (4 * m + 4)
            * Qabs (cos_partial k (aA m x)
                    + x * sin_partial (Nat.pred k) (aA m x))
            + x * Qabs (sin_term k (aA m x)))).
  { apply Qplus_le_compat.
    - rewrite (pa_abs_mul_pos (q_pow x (4 * m + 4)) _ Hpow0). apply Qle_refl.
    - rewrite (pa_abs_mul_pos x _ Hx0). apply Qle_refl. }
  apply (Qle_trans _
           ((6 # 1)%Q * q_pow x (4 * m + 4) + Qabs (sin_term k (aA m x)))).
  { apply Qplus_le_compat.
    - rewrite (Qmult_comm (6 # 1)%Q (q_pow x (4 * m + 4))).
      apply (pa_Qmult_le_l
               (Qabs (cos_partial k (aA m x)
                      + x * sin_partial (Nat.pred k) (aA m x)))
               ((6 # 1)%Q) (q_pow x (4 * m + 4))).
      + (* |C_k(A) + x*S_pred k(A)| <= 6 *)
        apply (Qle_trans _ (Qabs (cos_partial k (aA m x))
                            + Qabs (x * sin_partial (Nat.pred k) (aA m x)))).
        { apply Qabs_triangle. }
        apply (Qle_trans _ (3 + 1 * Qabs (sin_partial (Nat.pred k) (aA m x)))).
        { apply Qplus_le_compat.
          { apply (pa_cos_partial_le3 k). exact HA1. }
          { apply (Qle_trans _
                     (Qabs x * Qabs (sin_partial (Nat.pred k) (aA m x)))).
            { rewrite Qabs_Qmult. apply Qle_refl. }
            { apply (pa_le_qeq_r (Qabs x * Qabs (sin_partial (Nat.pred k) (aA m x)))
                       (1 * Qabs (sin_partial (Nat.pred k) (aA m x))) _).
              { apply (Qmult_le_compat_r (Qabs x) 1
                         (Qabs (sin_partial (Nat.pred k) (aA m x))));
                  [rewrite (lw0_Qabs_pos_eq x (Qle_to_QleT' _ _ Hx0)); exact Hx1
                  |apply pa_abs_nonneg]. }
              { rewrite Qmult_1_l. apply Qeq_refl. } } } }
        apply (pa_le_qeq_r
                 (3 + 1 * Qabs (sin_partial (Nat.pred k) (aA m x)))
                 (3 + 3) ((6 # 1)%Q)).
        { apply Qplus_le_compat; [apply Qle_refl |].
          { apply (Qle_trans (1 * Qabs (sin_partial (Nat.pred k) (aA m x)))
                     (Qabs (sin_partial (Nat.pred k) (aA m x))) 3).
            - rewrite Qmult_1_l. apply Qle_refl.
            - apply (pa_sin_partial_le3 (Nat.pred k)). exact HA1. } }
        { apply Qeq_refl. }
      + exact Hpow0.
    - apply (pa_le_qeq_r (x * Qabs (sin_term k (aA m x)))
               (1 * Qabs (sin_term k (aA m x))) _).
      { apply Qmult_le_compat_r; [exact Hx1 | apply pa_abs_nonneg]. }
      { rewrite Qmult_1_l. apply Qeq_refl. } }
  { apply Qle_refl. }
Qed.

(* ---------- C5. The Gronwall invariant (the sole external premise
   slot: the [pa_aF_step] form) ---------- *)

Lemma pa_q_pow_G0 : forall (N : nat) (n : nat),
  q_pow (pa_grid N 0) n == q_pow 0 n.
Proof.
  intros N n. induction n as [| p IH].
  - reflexivity.
  - change (q_pow (pa_grid N 0) (Datatypes.S p))
      with (pa_grid N 0 * q_pow (pa_grid N 0) p).
    change (q_pow 0 (Datatypes.S p)) with (0 * q_pow 0 p).
    apply (Qeq_trans (pa_grid N 0 * q_pow (pa_grid N 0) p)
                     (0 * q_pow (pa_grid N 0) p) (0 * q_pow 0 p)).
    + exact (Qmult_comp (pa_grid N 0) 0 (pa_grid_zero N)
               (q_pow (pa_grid N 0) p) (q_pow (pa_grid N 0) p)
               (Qeq_refl (q_pow (pa_grid N 0) p))).
    + apply (Qeq_trans (0 * q_pow (pa_grid N 0) p) 0 (0 * q_pow 0 p)).
      * apply Qmult_0_l.
      * symmetry. apply Qmult_0_l.
Qed.

Lemma pa_Qopp_comp : forall x y : Q, x == y -> Qopp x == Qopp y.
Proof.
  intros x y H.
  transitivity ((-1)%Q * x).
  - ring.
  - exact (Qmult_comp (-1)%Q (-1)%Q (Qeq_refl (-1)%Q) x y H).
Qed.

Lemma pa_Qminus_comp : forall a b c d : Q, a == c -> b == d -> a - b == c - d.
Proof.
  intros a b c d H1 H2.
  unfold Qminus.
  exact (Qplus_comp a c H1 (Qopp b) (Qopp d) (pa_Qopp_comp b d H2)).
Qed.

Lemma pa_aA_term_G0 : forall (j N : nat), aA_term j (pa_grid N 0) == aA_term j 0.
Proof.
  intros j N. unfold aA_term.
  apply (pa_Qminus_comp
           (q_pow (pa_grid N 0) (4 * j + 1) * lp_a (2 * j))
           (q_pow (pa_grid N 0) (4 * j + 3) * lp_a (2 * j + 1))
           (q_pow 0 (4 * j + 1) * lp_a (2 * j))
           (q_pow 0 (4 * j + 3) * lp_a (2 * j + 1))).
  - exact (Qmult_comp (q_pow (pa_grid N 0) (4 * j + 1)) (q_pow 0 (4 * j + 1))
             (pa_q_pow_G0 N (4 * j + 1))
             (lp_a (2 * j)) (lp_a (2 * j)) (Qeq_refl (lp_a (2 * j)))).
  - exact (Qmult_comp (q_pow (pa_grid N 0) (4 * j + 3)) (q_pow 0 (4 * j + 3))
             (pa_q_pow_G0 N (4 * j + 3))
             (lp_a (2 * j + 1)) (lp_a (2 * j + 1)) (Qeq_refl (lp_a (2 * j + 1)))).
Qed.

Lemma pa_aA_G0 : forall (m N : nat), aA m (pa_grid N 0) == aA m 0.
Proof.
  intros m N. induction m as [| p IH].
  - apply pa_aA_term_G0.
  - change (aA (Datatypes.S p) (pa_grid N 0))
      with (aA p (pa_grid N 0) + aA_term (Datatypes.S p) (pa_grid N 0)).
    change (aA (Datatypes.S p) 0)
      with (aA p 0 + aA_term (Datatypes.S p) 0).
    exact (Qplus_comp (aA p (pa_grid N 0)) (aA p 0) IH
             (aA_term (Datatypes.S p) (pa_grid N 0)) (aA_term (Datatypes.S p) 0)
             (pa_aA_term_G0 (Datatypes.S p) N)).
Qed.

Lemma pa_q_pow_ext : forall (n : nat) (x y : Q), x == y -> q_pow x n == q_pow y n.
Proof.
  intro n. induction n as [| p IH]; intros x y H.
  - reflexivity.
  - change (q_pow x (Datatypes.S p)) with (x * q_pow x p).
    change (q_pow y (Datatypes.S p)) with (y * q_pow y p).
    apply (Qeq_trans (x * q_pow x p) (y * q_pow x p) (y * q_pow y p)).
    + exact (Qmult_comp x y H (q_pow x p) (q_pow x p) (Qeq_refl (q_pow x p))).
    + exact (Qmult_comp y y (Qeq_refl y) (q_pow x p) (q_pow y p) (IH x y H)).
Qed.

Lemma pa_Qdiv_r_ext : forall (x y q : Q), x == y -> x / q == y / q.
Proof.
  intros x y q H.
  unfold Qdiv.
  exact (Qmult_comp x y H (Qinv q) (Qinv q) (Qeq_refl (Qinv q))).
Qed.

Lemma pa_sin_term_ext : forall (k : nat) (x y : Q), x == y ->
  sin_term k x == sin_term k y.
Proof.
  intros k x y H. unfold sin_term.
  exact (Qmult_comp (q_pow (-1) k) (q_pow (-1) k) (Qeq_refl (q_pow (-1) k))
           (q_pow x (S (2 * k)) / q_fact (S (2 * k)))
           (q_pow y (S (2 * k)) / q_fact (S (2 * k)))
           (pa_Qdiv_r_ext (q_pow x (S (2 * k))) (q_pow y (S (2 * k)))
              (q_fact (S (2 * k))) (pa_q_pow_ext (S (2 * k)) x y H))).
Qed.

Lemma pa_sin_partial_ext : forall (k : nat) (x y : Q), x == y ->
  sin_partial k x == sin_partial k y.
Proof.
  intro k. induction k as [| p IH]; intros x y H.
  - change (sin_partial 0 x) with (sin_term 0 x).
    change (sin_partial 0 y) with (sin_term 0 y).
    apply pa_sin_term_ext. exact H.
  - change (sin_partial (Datatypes.S p) x)
      with (sin_partial p x + sin_term (Datatypes.S p) x).
    change (sin_partial (Datatypes.S p) y)
      with (sin_partial p y + sin_term (Datatypes.S p) y).
    exact (Qplus_comp (sin_partial p x) (sin_partial p y) (IH x y H)
             (sin_term (Datatypes.S p) x) (sin_term (Datatypes.S p) y)
             (pa_sin_term_ext (Datatypes.S p) x y H)).
Qed.

Lemma pa_aF_G0_ext : forall (k m N : nat), aF k m (pa_grid N 0) == aF k m 0.
Proof.
  intros k m N. unfold aF.
  apply (pa_Qminus_comp (sin_partial k (aA m (pa_grid N 0)))
           (pa_grid N 0 * cos_partial k (aA m (pa_grid N 0)))
           (sin_partial k (aA m 0))
           (0 * cos_partial k (aA m 0))).
  - apply pa_sin_partial_ext. apply pa_aA_G0.
  - transitivity 0%Q.
    + apply Qmult_0_l.
    + symmetry. apply Qmult_0_l.
Qed.

Lemma pa_aA_term_wd : forall (j : nat) (x y : Q), x == y -> aA_term j x == aA_term j y.
Proof.
  intros j x y Hxy. unfold aA_term.
  apply pa_Qminus_comp.
  - exact (Qmult_comp (q_pow x (4 * j + 1)) (q_pow y (4 * j + 1))
             (pa_q_pow_ext (4 * j + 1) x y Hxy)
             (lp_a (2 * j)) (lp_a (2 * j)) (Qeq_refl (lp_a (2 * j)))).
  - exact (Qmult_comp (q_pow x (4 * j + 3)) (q_pow y (4 * j + 3))
             (pa_q_pow_ext (4 * j + 3) x y Hxy)
             (lp_a (2 * j + 1)) (lp_a (2 * j + 1)) (Qeq_refl (lp_a (2 * j + 1)))).
Qed.

Lemma pa_aA_wd : forall (m : nat) (x y : Q), x == y -> aA m x == aA m y.
Proof.
  intros m x y Hxy. induction m as [| p IH].
  - apply pa_aA_term_wd. exact Hxy.
  - change (aA (Datatypes.S p) x) with (aA p x + aA_term (Datatypes.S p) x).
    change (aA (Datatypes.S p) y) with (aA p y + aA_term (Datatypes.S p) y).
    exact (Qplus_comp (aA p x) (aA p y) IH
             (aA_term (Datatypes.S p) x) (aA_term (Datatypes.S p) y)
             (pa_aA_term_wd (Datatypes.S p) x y Hxy)).
Qed.

Lemma pa_aF_wd : forall (k m : nat) (x y : Q), x == y -> aF k m x == aF k m y.
Proof.
  intros k m x y Hxy. unfold aF.
  apply pa_Qminus_comp.
  - apply pa_sin_wd. apply pa_aA_wd. exact Hxy.
  - exact (Qmult_comp x y Hxy
             (cos_partial k (aA m x)) (cos_partial k (aA m y))
             (pa_cos_wd k (aA m x) (aA m y) (pa_aA_wd m x y Hxy))).
Qed.

Lemma pa_gronwall_inv : forall (k m N i : nat),
  (1 <= k)%nat -> (0 < N)%nat -> (i <= N)%nat ->
  (forall x h : Q, Qle 0 x -> Qle x 1 -> Qle 0 h -> Qle (x + h) 1 ->
     Qle (Qabs ((1 + x * x) * aF k m (x + h)
                - (1 + x * x + h * x) * aF k m x
                + h * pa_Dens k m x))
         (h * h * (1 + x * x) * pa_gCst m)) ->
  Qle (Qabs (aF k m (pa_grid N i)))
      ((1 + q_pow (pa_grid N i) 2) * pa_accF k m N i).
Proof.
  intros k m N i Hk HN Hi Hstep.
  induction i as [| p IH].
  - apply (pa_le_qeq_r (Qabs (aF k m (pa_grid N 0))) (Qabs (aF k m 0))
             ((1 + q_pow (pa_grid N 0) 2) * pa_accF k m N 0)).
    + rewrite (pa_aF_G0_ext k m N).
      apply Qle_refl.
    + rewrite pa_aF_zero.
      assert (Hz : Qabs 0 == 0) by reflexivity.
      rewrite Hz.
      assert (Ha0 : pa_accF k m N 0 == 0) by (unfold pa_accF, pa_wsumG; ring).
      rewrite Ha0.
      rewrite Qmult_0_r.
      reflexivity.
  - assert (HpN : (p <= N)%nat) by lia.
    specialize (IH HpN).
    assert (Hxp : Qle 0 (pa_grid N p)) by (apply pa_grid_nonneg; exact HN).
    assert (Hxl : Qle (pa_grid N p) 1) by (apply pa_grid_le_1; [exact HN | exact HpN]).
    assert (Hh0 : Qle 0 ((1 # 1) / (Z.of_nat N # 1)))
      by (apply Qlt_le_weak; apply pa_h_pos; exact HN).
    assert (Hh1 : Qle ((1 # 1) / (Z.of_nat N # 1)) 1).
    { apply (pa_le_qeq_r _ ((Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))) 1%Q).
      - apply (Qle_trans _ (1%Q * ((1 # 1) / (Z.of_nat N # 1)))).
        + rewrite Qmult_1_l. apply Qle_refl.
        + apply Qmult_le_compat_r.
          * unfold Qle. simpl. lia.
          * exact Hh0.
      - apply pa_hN. exact HN. }
    assert (Hxh : Qle (pa_grid N (Datatypes.S p)) 1)
      by (apply pa_grid_le_1; [exact HN | lia]).
    assert (HgS : pa_grid N (Datatypes.S p)
                  == pa_grid N p + ((1 # 1) / (Z.of_nat N # 1)))
      by (apply pa_grid_S; exact HN).
    rewrite HgS in Hxh.
(* Instance of the step inequality. *)
    pose proof (Hstep (pa_grid N p) ((1 # 1) / (Z.of_nat N # 1))
                       Hxp Hxl Hh0 Hxh) as Hs.
(* The positivity facts [(1+x^2) > 0] and [1+x^2+h*x >= 0]. *)
    assert (Hc1 : Qle 0 (1 + pa_grid N p * pa_grid N p)).
    { apply (Qplus_le_compat 0%Q 1%Q 0%Q (pa_grid N p * pa_grid N p));
        [ unfold Qle; cbn [Qnum Qden]; lia
        | apply Qmult_le_0_compat; [exact Hxp | exact Hxp] ]. }
    assert (Hc1h : Qle 0 (1 + pa_grid N p * pa_grid N p
                          + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p)).
    { apply (Qplus_le_compat 0%Q (1 + pa_grid N p * pa_grid N p) 0%Q
               ((1 # 1) / (Z.of_nat N # 1) * pa_grid N p));
        [ exact Hc1 | apply Qmult_le_0_compat; assumption ]. }
    assert (Hc1pos : Qlt 0 (1 + pa_grid N p * pa_grid N p)).
    { apply (Qlt_le_trans 0%Q 1%Q (1 + pa_grid N p * pa_grid N p)).
      + unfold Qlt. cbn [Qnum Qden]. lia.
      + apply (Qplus_le_compat 1%Q 1%Q 0%Q (pa_grid N p * pa_grid N p));
          [apply Qle_refl | apply Qmult_le_0_compat; exact Hxp]. }
    assert (HFext : aF k m (pa_grid N (Datatypes.S p))
                  == aF k m (pa_grid N p + (1 # 1) / (Z.of_nat N # 1)))
      by (apply pa_aF_wd; exact HgS).
(* |(1+x^2)F(x+h)| <= (1+x^2+hx)|F(x)| + h*pa_r + h^2(1+x^2)Cst *)
    assert (Htri : Qle
      (Qabs ((1 + pa_grid N p * pa_grid N p) * aF k m (pa_grid N (Datatypes.S p))))
      ((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p)
       * ((1 + pa_grid N p * pa_grid N p) * pa_accF k m N p)
       + ((1 # 1) / (Z.of_nat N # 1)) * pa_r k m (pa_grid N p)
       + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
         * (1 + pa_grid N p * pa_grid N p) * pa_gCst m)).
    { assert (Hid : (1 + pa_grid N p * pa_grid N p) * aF k m (pa_grid N (Datatypes.S p))
                 == (1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p) * aF k m (pa_grid N p)
                    + (- ((1 # 1) / (Z.of_nat N # 1) * pa_Dens k m (pa_grid N p)))
                    + ((1 + pa_grid N p * pa_grid N p) * aF k m (pa_grid N (Datatypes.S p))
                       - (1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p) * aF k m (pa_grid N p)
                       + (1 # 1) / (Z.of_nat N # 1) * pa_Dens k m (pa_grid N p))) by ring.
      rewrite Hid.
      apply (Qle_trans _
               (Qabs ((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p) * aF k m (pa_grid N p)
                      + (- ((1 # 1) / (Z.of_nat N # 1) * pa_Dens k m (pa_grid N p))))
                + Qabs ((1 + pa_grid N p * pa_grid N p) * aF k m (pa_grid N (Datatypes.S p))
                        - (1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p) * aF k m (pa_grid N p)
                        + (1 # 1) / (Z.of_nat N # 1) * pa_Dens k m (pa_grid N p)))).
      { apply Qabs_triangle. }
      apply (Qle_trans _
               (Qabs ((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p) * aF k m (pa_grid N p)
                      + (- ((1 # 1) / (Z.of_nat N # 1) * pa_Dens k m (pa_grid N p))))
                + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
                  * (1 + pa_grid N p * pa_grid N p) * pa_gCst m)).
      { apply Qplus_le_compat.
        - apply Qle_refl.
        - rewrite HFext. exact Hs. }
      apply (Qle_trans _
               (Qabs ((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p) * aF k m (pa_grid N p))
                + Qabs ((- ((1 # 1) / (Z.of_nat N # 1) * pa_Dens k m (pa_grid N p))))
                + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
                  * (1 + pa_grid N p * pa_grid N p) * pa_gCst m)).
      { apply Qplus_le_compat.
        - apply Qabs_triangle.
        - apply Qle_refl. }
      apply (Qle_trans _
               (Qabs ((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p) * aF k m (pa_grid N p))
                + Qabs ((1 # 1) / (Z.of_nat N # 1) * pa_Dens k m (pa_grid N p))
                + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
                  * (1 + pa_grid N p * pa_grid N p) * pa_gCst m)).
      { rewrite (Qabs_opp ((1 # 1) / (Z.of_nat N # 1) * pa_Dens k m (pa_grid N p))).
        apply Qplus_le_compat.
        - apply Qplus_le_compat; [apply Qle_refl | apply Qle_refl].
        - apply Qle_refl. }
      apply (Qle_trans _
               ((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p)
                * Qabs (aF k m (pa_grid N p))
                + ((1 # 1) / (Z.of_nat N # 1)) * Qabs (pa_Dens k m (pa_grid N p))
                + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
                  * (1 + pa_grid N p * pa_grid N p) * pa_gCst m)).
      { apply Qplus_le_compat.
        - apply Qplus_le_compat.
          + rewrite (pa_abs_mul_pos _ _ Hc1h). apply Qle_refl.
          + rewrite (pa_abs_mul_pos _ _ Hh0). apply Qle_refl.
        - apply Qle_refl. }
      apply (Qle_trans _
               ((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p)
                * ((1 + pa_grid N p * pa_grid N p) * pa_accF k m N p)
                + ((1 # 1) / (Z.of_nat N # 1)) * pa_r k m (pa_grid N p)
                + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
                  * (1 + pa_grid N p * pa_grid N p) * pa_gCst m)).
      { apply Qplus_le_compat.
        - apply Qplus_le_compat.
          + assert (Hq2p : (1 + pa_grid N p * pa_grid N p)%Q
                           == (1 + q_pow (pa_grid N p) 2)%Q).
            { change (q_pow (pa_grid N p) 2)
                with (pa_grid N p * (pa_grid N p * 1))%Q.
              ring. }
            apply (pa_Qmult_le_l (Qabs (aF k m (pa_grid N p))) _ _).
            * apply (pa_le_qeq_r (Qabs (aF k m (pa_grid N p)))
                       ((1 + q_pow (pa_grid N p) 2) * pa_accF k m N p)
                       ((1 + pa_grid N p * pa_grid N p) * pa_accF k m N p)).
              -- exact IH.
              -- rewrite Hq2p. reflexivity.
            * exact Hc1h.
          + apply (pa_Qmult_le_l (Qabs (pa_Dens k m (pa_grid N p))) (pa_r k m (pa_grid N p)) _).
            * apply (pa_Dens_abs_le k m (pa_grid N p) Hk Hxp Hxl).
            * exact Hh0.
        - apply Qle_refl. }
      apply Qle_refl. }
(* [|(1+x^2)F| == (1+x^2)|F|]: scale up to
   [(1+(x+h)^2) accF_{S p}] and cancel. *)
    assert (HabsL : Qabs ((1 + pa_grid N p * pa_grid N p) * aF k m (pa_grid N (Datatypes.S p)))
                    == (1 + pa_grid N p * pa_grid N p)
                       * Qabs (aF k m (pa_grid N (Datatypes.S p))))
      by (apply pa_abs_mul_pos; exact Hc1).
    assert (Hgrow : Qle
      ((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p)
       * ((1 + pa_grid N p * pa_grid N p) * pa_accF k m N p)
       + ((1 # 1) / (Z.of_nat N # 1)) * pa_r k m (pa_grid N p)
       + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
         * (1 + pa_grid N p * pa_grid N p) * pa_gCst m)
      ((1 + pa_grid N p * pa_grid N p)
       * ((1 + q_pow (pa_grid N (Datatypes.S p)) 2) * pa_accF k m N (Datatypes.S p)))).
    { rewrite (pa_accF_S k m N p HN).
      assert (HqS2 : q_pow (pa_grid N (Datatypes.S p)) 2
                     == (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                        * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))).
      { change (q_pow (pa_grid N (Datatypes.S p)) 2)
          with (pa_grid N (Datatypes.S p)
                * (pa_grid N (Datatypes.S p) * 1))%Q.
        rewrite HgS. ring. }
      rewrite HqS2.
      assert (Hxh0 : Qle 0 (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))).
      { apply (Qplus_le_compat 0%Q (pa_grid N p) 0%Q ((1 # 1) / (Z.of_nat N # 1)));
          [exact Hxp | exact Hh0]. }
      assert (Hdiff0 : Qle 0 (pa_grid N p * ((1 # 1) / (Z.of_nat N # 1))
                              + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1)))).
      { apply (Qplus_le_compat 0%Q (pa_grid N p * ((1 # 1) / (Z.of_nat N # 1))) 0%Q
                 ((1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))));
          [apply Qmult_le_0_compat; assumption | apply Qmult_le_0_compat; assumption]. }
      assert (Hone1 : Qle 1 (1 + pa_grid N p * pa_grid N p)).
      { apply (Qplus_le_compat 1%Q 1%Q 0%Q (pa_grid N p * pa_grid N p));
          [apply Qle_refl | apply Qmult_le_0_compat; exact Hxp]. }
      assert (Hone2 : Qle 1 (1 + (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                                  * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1)))).
      { apply (Qplus_le_compat 1%Q 1%Q 0%Q
                 ((pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                  * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))));
          [apply Qle_refl | apply Qmult_le_0_compat; exact Hxh0]. }
      assert (Hprod1 : Qle 1 ((1 + pa_grid N p * pa_grid N p)
                              * (1 + (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                                      * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))))).
      { apply (Qle_trans 1%Q
                 ((1 # 1) * (1 + (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                                 * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))))).
        - apply (pa_le_qeq_r 1%Q
                   (1 + (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                        * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1)))
                   ((1 # 1) * (1 + (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                                   * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))))).
          + exact Hone2.
          + ring.
        - apply (Qmult_le_compat_r 1%Q (1 + pa_grid N p * pa_grid N p)
                   (1 + (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                    * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1)))).
          + exact Hone1.
          + apply (Qle_trans 0%Q 1%Q _);
              [unfold Qle; cbn [Qnum Qden]; lia | exact Hone2]. }
      assert (HA0 : Qle 0 (pa_accF k m N p)) by (apply pa_accF_nonneg; exact HN).
      assert (HR0 : Qle 0 (pa_r k m (pa_grid N p))) by (apply pa_r_nonneg; exact Hxp).
      assert (HC0 : Qle 0 (pa_gCst m)).
      { unfold pa_gCst, Qle. cbn [Qnum Qden].
        pose proof (pa_nat_pow2_pos (8 * m + 16)). lia. }
      remember (pa_accF k m N p) as Aeq.
      remember (pa_r k m (pa_grid N p)) as Req.
      remember (pa_gCst m) as Ceq.
      apply (pa_le_qeq_r
               ((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p)
                * ((1 + pa_grid N p * pa_grid N p) * Aeq)
                + (1 # 1) / (Z.of_nat N # 1) * Req
                + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
                  * (1 + pa_grid N p * pa_grid N p) * Ceq)
               (((1 + pa_grid N p * pa_grid N p + (1 # 1) / (Z.of_nat N # 1) * pa_grid N p)
                 * ((1 + pa_grid N p * pa_grid N p) * Aeq)
                 + (1 # 1) / (Z.of_nat N # 1) * Req
                 + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
                   * (1 + pa_grid N p * pa_grid N p) * Ceq)
                + ((1 + pa_grid N p * pa_grid N p)
                   * (pa_grid N p * ((1 # 1) / (Z.of_nat N # 1))
                      + (1 # 1) / (Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1)))
                   * Aeq
                   + (((1 + pa_grid N p * pa_grid N p)
                       * (1 + (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                               * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))))
                      - 1)
                     * ((1 # 1) / (Z.of_nat N # 1) * Req)
                   + (1 + pa_grid N p * pa_grid N p)
                     * ((pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                        * ((1 # 1) / (Z.of_nat N # 1)))
                     * ((pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                        * ((1 # 1) / (Z.of_nat N # 1)))
                     * Ceq))
               ((1 + pa_grid N p * pa_grid N p)
                * ((1 + (pa_grid N p + (1 # 1) / (Z.of_nat N # 1))
                        * (pa_grid N p + (1 # 1) / (Z.of_nat N # 1)))
                   * (Aeq + (1 # 1) / (Z.of_nat N # 1)
                             * (Req + (1 # 1) / (Z.of_nat N # 1) * Ceq))))).
      + apply pa_qle_add_pos.
        apply (Qplus_le_compat 0%Q _ 0%Q _).
        * apply (Qplus_le_compat 0%Q _ 0%Q _).
          { apply (Qmult_le_0_compat _ Aeq).
            apply (Qmult_le_0_compat _ _); [exact Hc1 | exact Hdiff0].
            exact HA0. }
          { apply (Qmult_le_0_compat _ _).
            exact (leibsep_qle_minus _ _ Hprod1).
            apply (Qmult_le_0_compat _ Req); [exact Hh0 | exact HR0]. }
        * { apply (Qmult_le_0_compat _ Ceq).
            apply (Qmult_le_0_compat _ _);
              [apply (Qmult_le_0_compat _ _);
                 [exact Hc1 | apply (Qmult_le_0_compat _ _); [exact Hxh0 | exact Hh0]]
              |apply (Qmult_le_0_compat _ _); [exact Hxh0 | exact Hh0]].
            exact HC0. }
      + ring.
    }
    assert (Hfin : Qle
      ((1 + pa_grid N p * pa_grid N p) * Qabs (aF k m (pa_grid N (Datatypes.S p))))
      ((1 + pa_grid N p * pa_grid N p)
       * ((1 + q_pow (pa_grid N (Datatypes.S p)) 2) * pa_accF k m N (Datatypes.S p)))).
    { rewrite <- HabsL.
      exact (Qle_trans _ _ _ Htri Hgrow). }
    assert (Hfin2 : Qabs (aF k m (pa_grid N (Datatypes.S p)))
                    * (1 + pa_grid N p * pa_grid N p)
                <= ((1 + q_pow (pa_grid N (Datatypes.S p)) 2)
                    * pa_accF k m N (Datatypes.S p))
                   * (1 + pa_grid N p * pa_grid N p)).
    { rewrite (Qmult_comm (Qabs (aF k m (pa_grid N (Datatypes.S p))))).
      rewrite (Qmult_comm ((1 + q_pow (pa_grid N (Datatypes.S p)) 2)
                             * pa_accF k m N (Datatypes.S p))).
      exact Hfin. }
    exact (proj1 (Qmult_le_r (Qabs (aF k m (pa_grid N (Datatypes.S p))))
                   ((1 + q_pow (pa_grid N (Datatypes.S p)) 2)
                    * pa_accF k m N (Datatypes.S p))
                   (1 + pa_grid N p * pa_grid N p) Hc1pos) Hfin2).
Qed.

(* ---------- C6. The final bound ---------- *)

Lemma pa_F_one_bound : forall (k m N : nat),
  (1 <= k)%nat -> (0 < N)%nat ->
  (forall x h : Q, Qle 0 x -> Qle x 1 -> Qle 0 h -> Qle (x + h) 1 ->
     Qle (Qabs ((1 + x * x) * aF k m (x + h)
                - (1 + x * x + h * x) * aF k m x
                + h * pa_Dens k m x))
         (h * h * (1 + x * x) * pa_gCst m)) ->
  Qle (Qabs (aF k m 1))
      ((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
       + (9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1))
       + (2 # 1)%Q * ((1 # 1) / (Z.of_nat N # 1)) * pa_gCst m).
Proof.
  intros k m N Hk HN Hstep.
  pose proof (pa_gronwall_inv k m N N Hk HN (Nat.le_refl N) Hstep) as Hinv.
  rewrite (pa_aF_wd k m (pa_grid N N) 1 (pa_grid_one N HN)) in Hinv.
  assert (HqNN : q_pow (pa_grid N N) 2 == q_pow 1 2)
    by (apply pa_q_pow_ext; apply pa_grid_one; exact HN).
  rewrite HqNN in Hinv.
  assert (Hq2 : q_pow 1 2 == 1) by (apply sc_q_pow_one).
  rewrite Hq2 in Hinv.
  assert (HhN1 : ((1 # 1) / (Z.of_nat N # 1)) * (Z.of_nat N # 1) == 1).
  { assert (Ht := pa_hN N HN). rewrite (Qmult_comm _ _) in Ht. exact Ht. }
  assert (Hqone : forall n : nat, q_pow 1 n == 1).
  { intro n. induction n as [| p IH].
    - reflexivity.
    - change (q_pow 1 (Datatypes.S p)) with (1 * q_pow 1 p)%Q.
      rewrite IH. apply Qmult_1_l. }
(* Telescoping upper bound for the endpoint power sum. *)
  assert (Hte1 : Qle (pa_wsumG N (fun j => q_pow (pa_grid N j) (4 * m + 4)) N)
                     ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))).
  { apply (pa_le_qeq_r
             (pa_wsumG N (fun j => q_pow (pa_grid N j) (4 * m + 4)) N)
             (q_pow (pa_grid N N) (Datatypes.S (4 * m + 4))
              * ((1 # 1) / (Z.of_nat (Datatypes.S (4 * m + 4)) # 1))
              - q_pow (pa_grid N 0) (Datatypes.S (4 * m + 4))
                * ((1 # 1) / (Z.of_nat (Datatypes.S (4 * m + 4)) # 1)))
             ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))).
    - apply (pa_wsumG_telescope N N
                (fun j => q_pow (pa_grid N j) (4 * m + 4))
                (fun j => q_pow (pa_grid N j) (Datatypes.S (4 * m + 4))
                          * ((1 # 1) / (Z.of_nat (Datatypes.S (4 * m + 4)) # 1)))).
        { intros j Hj.
        assert (Hg0 : Qle 0 (pa_grid N j)) by (apply pa_grid_nonneg; exact HN).
        assert (Hh0 : Qle 0 ((1 # 1) / (Z.of_nat N # 1)))
          by (apply Qlt_le_weak; apply pa_h_pos; exact HN).
        pose proof (pa_D_pos (4 * m + 4) (pa_grid N j) ((1 # 1) / (Z.of_nat N # 1)) Hg0 Hh0) as Hdp.
        assert (Hgs : pa_grid N (Datatypes.S j)
                      == pa_grid N j + ((1 # 1) / (Z.of_nat N # 1)))
          by (apply pa_grid_S; exact HN).
        rewrite (pa_q_pow_ext (Datatypes.S (4 * m + 4)) (pa_grid N (Datatypes.S j))
                   (pa_grid N j + ((1 # 1) / (Z.of_nat N # 1))) Hgs).
        assert (Hscaled : Qle 0
                   (((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1))
                    * (q_pow (pa_grid N j + ((1 # 1) / (Z.of_nat N # 1))) (Datatypes.S (4 * m + 4))
                       - q_pow (pa_grid N j) (Datatypes.S (4 * m + 4))
                       - (Z.of_nat (S (4 * m + 4)) # 1) * q_pow (pa_grid N j) (4 * m + 4)
                         * ((1 # 1) / (Z.of_nat N # 1))))).
        { apply (Qmult_le_0_compat _ _).
          - apply Qlt_le_weak. apply (pa_h_pos (S (4 * m + 4))). lia.
          - exact Hdp. }
        assert (Hkey : (Z.of_nat (S (4 * m + 4)) # 1) * q_pow (pa_grid N j) (4 * m + 4)
                       * ((1 # 1) / (Z.of_nat N # 1))
                       * ((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1))
                       == ((1 # 1) / (Z.of_nat N # 1)) * q_pow (pa_grid N j) (4 * m + 4)).
        { assert (Hh45 : (Z.of_nat (S (4 * m + 4)) # 1)
                         * ((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1)) == 1)
            by (apply pa_hN; lia).
          transitivity (((Z.of_nat (S (4 * m + 4)) # 1)
                         * ((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1)))
                        * (q_pow (pa_grid N j) (4 * m + 4) * ((1 # 1) / (Z.of_nat N # 1)))).
          - ring.
          - rewrite Hh45. rewrite Qmult_1_l. ring. }
        apply (leibsep_qle_of_minus ((1 # 1) / (Z.of_nat N # 1) * q_pow (pa_grid N j) (4 * m + 4))).
        apply (pa_le_qeq_r 0%Q
                 (((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1))
                  * q_pow (pa_grid N j + ((1 # 1) / (Z.of_nat N # 1))) (Datatypes.S (4 * m + 4))
                  - (1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1)
                    * q_pow (pa_grid N j) (Datatypes.S (4 * m + 4))
                  - (Z.of_nat (S (4 * m + 4)) # 1) * q_pow (pa_grid N j) (4 * m + 4)
                    * ((1 # 1) / (Z.of_nat N # 1))
                    * ((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1)))
                 (q_pow (pa_grid N j + ((1 # 1) / (Z.of_nat N # 1))) (Datatypes.S (4 * m + 4))
                  * ((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1))
                  - q_pow (pa_grid N j) (Datatypes.S (4 * m + 4))
                    * ((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1))
                  - ((1 # 1) / (Z.of_nat N # 1)) * q_pow (pa_grid N j) (4 * m + 4))).
        { apply (pa_le_qeq_r 0%Q
                   (((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1))
                    * (q_pow (pa_grid N j + ((1 # 1) / (Z.of_nat N # 1))) (Datatypes.S (4 * m + 4))
                       - q_pow (pa_grid N j) (Datatypes.S (4 * m + 4))
                       - (Z.of_nat (S (4 * m + 4)) # 1) * q_pow (pa_grid N j) (4 * m + 4)
                         * ((1 # 1) / (Z.of_nat N # 1))))
                   (((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1))
                    * q_pow (pa_grid N j + ((1 # 1) / (Z.of_nat N # 1))) (Datatypes.S (4 * m + 4))
                    - (1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1)
                      * q_pow (pa_grid N j) (Datatypes.S (4 * m + 4))
                    - (Z.of_nat (S (4 * m + 4)) # 1) * q_pow (pa_grid N j) (4 * m + 4)
                      * ((1 # 1) / (Z.of_nat N # 1))
                      * ((1 # 1) / (Z.of_nat (S (4 * m + 4)) # 1)))).
          { exact Hscaled. }
          { ring. } }
        { rewrite Hkey. ring. } }
    - assert (HqN5 : q_pow (pa_grid N N) (Datatypes.S (4 * m + 4))
                     == q_pow 1 (Datatypes.S (4 * m + 4)))
        by (apply pa_q_pow_ext; apply pa_grid_one; exact HN).
      rewrite HqN5.
      rewrite (Hqone (Datatypes.S (4 * m + 4))).
      replace (Datatypes.S (4 * m + 4))%nat with (4 * m + 5)%nat by lia.
      rewrite (pa_q_pow_G0 N (4 * m + 5)).
      rewrite (pa_qA_pos_zero (4 * m + 5)) by lia.
      ring. }
  assert (Hte2 : Qle (pa_wsumG N (fun j => Qabs (sin_term k (aA m (pa_grid N j)))) N)
                     ((1 # 1) / q_fact (2 * k + 1))).
  { assert (Hgp : forall j : nat, (j <= N)%nat ->
      Qle (Qabs (sin_term k (aA m (pa_grid N j)))) ((1 # 1) / q_fact (2 * k + 1))).
    { intros j HjN.
      assert (HA1 : Qle (Qabs (aA m (pa_grid N j))) 1).
      { assert (HA0 : Qle 0 (aA m (pa_grid N j)))
          by (apply (pa_aA_nonneg m (pa_grid N j));
                [apply pa_grid_nonneg; exact HN | apply pa_grid_le_1; [exact HN | lia]]).
        assert (HAle : Qle (aA m (pa_grid N j)) 1)
          by (apply (pa_aA_le_one m (pa_grid N j));
                [apply pa_grid_nonneg; exact HN | apply pa_grid_le_1; [exact HN | lia]]).
        rewrite (lw0_Qabs_pos_eq (aA m (pa_grid N j)) (Qle_to_QleT' _ _ HA0)).
        exact HAle. }
      assert (HpowA : Qle (q_pow (Qabs (aA m (pa_grid N j))) (Datatypes.S (2 * k)))
                          (Qabs (aA m (pa_grid N j)))).
      { change (q_pow (Qabs (aA m (pa_grid N j))) (Datatypes.S (2 * k)))
          with (Qabs (aA m (pa_grid N j)) * q_pow (Qabs (aA m (pa_grid N j))) (2 * k)).
        apply (pa_le_qeq_r
                 (Qabs (aA m (pa_grid N j)) * q_pow (Qabs (aA m (pa_grid N j))) (2 * k))
                 (Qabs (aA m (pa_grid N j)) * 1%Q) (Qabs (aA m (pa_grid N j)))).
        - apply (pa_Qmult_le_l (q_pow (Qabs (aA m (pa_grid N j))) (2 * k)) 1%Q
                   (Qabs (aA m (pa_grid N j))));
            [apply (pa_qpow_le_one (2 * k) _); [apply pa_abs_nonneg | exact HA1]
            | apply pa_abs_nonneg].
        - ring. }
      assert (Hfinv : Qle 0 (/ q_fact (Datatypes.S (2 * k)))).
      { apply Qlt_le_weak. apply Qinv_lt_0_compat. apply q_fact_pos. }
      assert (Hsteq : Qabs (sin_term k (aA m (pa_grid N j)))
                      == ((1 # 1) / q_fact (2 * k + 1))
                         * q_pow (Qabs (aA m (pa_grid N j))) (Datatypes.S (2 * k))).
      { replace (2 * k + 1)%nat with (Datatypes.S (2 * k))%nat by lia.
        unfold sin_term.
        change (q_pow (aA m (pa_grid N j)) (Datatypes.S (2 * k))
                / q_fact (Datatypes.S (2 * k)))
          with ((q_pow (aA m (pa_grid N j)) (Datatypes.S (2 * k)))
                * (/ q_fact (Datatypes.S (2 * k))))%Q.
        rewrite (pa_abs_scale_unit k
                   ((q_pow (aA m (pa_grid N j)) (Datatypes.S (2 * k)))
                    * (/ q_fact (Datatypes.S (2 * k))))).
        rewrite (Qmult_comm (q_pow (aA m (pa_grid N j)) (Datatypes.S (2 * k)))
                   (/ q_fact (Datatypes.S (2 * k)))).
        rewrite (pa_abs_mul_pos (/ q_fact (Datatypes.S (2 * k)))
                   (q_pow (aA m (pa_grid N j)) (Datatypes.S (2 * k))) Hfinv).
        rewrite (q_pow_abs (aA m (pa_grid N j)) (Datatypes.S (2 * k))).
        unfold Qdiv. ring. }
      apply (Qle_trans (Qabs (sin_term k (aA m (pa_grid N j))))
                       (Qabs (aA m (pa_grid N j)) * ((1 # 1) / q_fact (2 * k + 1)))
                       ((1 # 1) / q_fact (2 * k + 1))).
      - rewrite Hsteq.
        apply (Qle_trans
                 (((1 # 1) / q_fact (2 * k + 1))
                  * q_pow (Qabs (aA m (pa_grid N j))) (Datatypes.S (2 * k)))
                 (((1 # 1) / q_fact (2 * k + 1)) * Qabs (aA m (pa_grid N j)))
                 (Qabs (aA m (pa_grid N j)) * ((1 # 1) / q_fact (2 * k + 1)))).
        + apply (pa_Qmult_le_l (q_pow (Qabs (aA m (pa_grid N j))) (Datatypes.S (2 * k)))
                   (Qabs (aA m (pa_grid N j))) ((1 # 1) / q_fact (2 * k + 1)));
            [exact HpowA
            | apply (pa_le_qeq_r 0%Q (/ q_fact (2 * k + 1)) (1 / q_fact (2 * k + 1)));
               [apply Qlt_le_weak; apply Qinv_lt_0_compat; apply q_fact_pos | unfold Qdiv; symmetry; apply Qmult_1_l]].
        + apply qeq_le. ring.
      - apply (pa_le_qeq_r
                 (Qabs (aA m (pa_grid N j)) * ((1 # 1) / q_fact (2 * k + 1)))
                 (1%Q * ((1 # 1) / q_fact (2 * k + 1)))
                 ((1 # 1) / q_fact (2 * k + 1))).
        + apply (Qmult_le_compat_r (Qabs (aA m (pa_grid N j))) 1%Q
                   ((1 # 1) / q_fact (2 * k + 1)));
            [exact HA1
            | apply (pa_le_qeq_r 0%Q (/ q_fact (2 * k + 1)) (1 / q_fact (2 * k + 1)));
               [apply Qlt_le_weak; apply Qinv_lt_0_compat; apply q_fact_pos | unfold Qdiv; symmetry; apply Qmult_1_l]].
        + rewrite Qmult_1_l. apply Qeq_refl. }
    apply (pa_le_qeq_r
             (pa_wsumG N (fun j => Qabs (sin_term k (aA m (pa_grid N j)))) N)
             (((Z.of_nat N # 1) * ((1 # 1) / (Z.of_nat N # 1))
               * ((1 # 1) / q_fact (2 * k + 1)))
              - ((Z.of_nat 0 # 1) * ((1 # 1) / (Z.of_nat N # 1))
                 * ((1 # 1) / q_fact (2 * k + 1))))
             ((1 # 1) / q_fact (2 * k + 1))).
    - apply (pa_wsumG_telescope N N
                (fun j => Qabs (sin_term k (aA m (pa_grid N j))))
                (fun j => (Z.of_nat j # 1) * ((1 # 1) / (Z.of_nat N # 1))
                          * ((1 # 1) / q_fact (2 * k + 1)))).
      intros j Hj.
      apply (pa_le_qeq_r
               (((1 # 1) / (Z.of_nat N # 1)) * Qabs (sin_term k (aA m (pa_grid N j))))
               (((1 # 1) / (Z.of_nat N # 1)) * ((1 # 1) / q_fact (2 * k + 1)))
               ((Z.of_nat (Datatypes.S j) # 1) * ((1 # 1) / (Z.of_nat N # 1))
                * ((1 # 1) / q_fact (2 * k + 1))
                - (Z.of_nat j # 1) * ((1 # 1) / (Z.of_nat N # 1))
                  * ((1 # 1) / q_fact (2 * k + 1)))).
      + apply (pa_Qmult_le_l (Qabs (sin_term k (aA m (pa_grid N j))))
                 ((1 # 1) / q_fact (2 * k + 1)) ((1 # 1) / (Z.of_nat N # 1)));
          [apply Hgp; lia | apply Qlt_le_weak; apply pa_h_pos; exact HN].
      + assert (Hij : (Z.of_nat (Datatypes.S j) = (Z.of_nat j + 1))%Z).
        { assert (Hjs : Datatypes.S j = (j + 1)%nat) by lia.
          rewrite Hjs, Nat2Z.inj_add. reflexivity. }
        rewrite Hij.
        change ((Z.of_nat j + 1) # 1) with (inject_Z (Z.of_nat j + 1)).
        rewrite inject_Z_plus.
        change (inject_Z 1) with 1%Q.
        change (inject_Z (Z.of_nat j)) with ((Z.of_nat j) # 1).
        ring.
    - rewrite (pa_hN N HN). rewrite Qmult_1_l.
      change ((Z.of_nat 0) # 1) with 0%Q.
      rewrite Qmult_0_l. ring. }
  assert (Hdec : pa_accF k m N N
                 == (6 # 1)%Q * pa_wsumG N (fun j => q_pow (pa_grid N j) (4 * m + 4)) N
                    + pa_wsumG N (fun j => Qabs (sin_term k (aA m (pa_grid N j)))) N
                    + ((1 # 1) / (Z.of_nat N # 1)) * pa_gCst m).
  { unfold pa_accF, pa_r.
    rewrite (pa_wsumG_scal_add N N (6 # 1)%Q
               (fun j => q_pow (pa_grid N j) (4 * m + 4))
               (fun j => Qabs (sin_term k (aA m (pa_grid N j))))).
    rewrite <- (Qmult_comm (Z.of_nat N # 1)
                  (((1 # 1) / (Z.of_nat N # 1)) * ((1 # 1) / (Z.of_nat N # 1))
                   * pa_gCst m)).
    rewrite <- (Qmult_assoc ((1 # 1) / (Z.of_nat N # 1))
                  ((1 # 1) / (Z.of_nat N # 1)) (pa_gCst m)).
    rewrite (Qmult_assoc (Z.of_nat N # 1) ((1 # 1) / (Z.of_nat N # 1))
               (((1 # 1) / (Z.of_nat N # 1)) * pa_gCst m)).
    rewrite (pa_hN N HN). ring. }
  rewrite Hdec in Hinv.
  apply (Qle_trans (Qabs (aF k m 1))
           ((1 + 1)%Q * ((6 # 1)%Q
                         * pa_wsumG N (fun j => q_pow (pa_grid N j) (4 * m + 4)) N
                         + pa_wsumG N (fun j => Qabs (sin_term k (aA m (pa_grid N j)))) N
                         + ((1 # 1) / (Z.of_nat N # 1)) * pa_gCst m))
           ((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
            + (9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1))
            + (2 # 1)%Q * ((1 # 1) / (Z.of_nat N # 1)) * pa_gCst m)).
  - exact Hinv.
  - assert (Hring : (1 + 1)%Q
                    * ((6 # 1)%Q * pa_wsumG N (fun j => q_pow (pa_grid N j) (4 * m + 4)) N
                       + pa_wsumG N (fun j => Qabs (sin_term k (aA m (pa_grid N j)))) N
                       + ((1 # 1) / (Z.of_nat N # 1)) * pa_gCst m)
                    == (12 # 1)%Q * pa_wsumG N (fun j => q_pow (pa_grid N j) (4 * m + 4)) N
                       + (2 # 1)%Q * pa_wsumG N (fun j => Qabs (sin_term k (aA m (pa_grid N j)))) N
                       + (2 # 1)%Q * ((1 # 1) / (Z.of_nat N # 1)) * pa_gCst m) by ring.
    rewrite Hring.
    apply Qplus_le_compat.
    + apply Qplus_le_compat.
      * apply (pa_Qmult_le_l
                 (pa_wsumG N (fun j => q_pow (pa_grid N j) (4 * m + 4)) N)
                 ((1 # 1) / (Z.of_nat (4 * m + 5) # 1)) (12 # 1)%Q);
          [exact Hte1 | unfold Qle; cbn [Qnum Qden]; lia].
      * apply (Qle_trans _
                 ((2 # 1)%Q * ((1 # 1) / q_fact (2 * k + 1))) _).
        -- apply (pa_Qmult_le_l
                     (pa_wsumG N (fun j => Qabs (sin_term k (aA m (pa_grid N j)))) N)
                     ((1 # 1) / q_fact (2 * k + 1)) (2 # 1)%Q);
             [exact Hte2 | unfold Qle; cbn [Qnum Qden]; lia].
        -- apply (Qmult_le_compat_r (2 # 1)%Q (9 # 4)%Q
                     ((1 # 1) / q_fact (2 * k + 1)));
             [unfold Qle; cbn [Qnum Qden]; lia
             | apply (pa_le_qeq_r 0%Q (/ q_fact (2 * k + 1)) (1 / q_fact (2 * k + 1)));
                  [apply Qlt_le_weak; apply Qinv_lt_0_compat; apply q_fact_pos | unfold Qdiv; symmetry; apply Qmult_1_l]].
    + apply Qle_refl.
Qed.

(** F1. Folding the [2hCst] factor (the [field] route with [Nat2Z]
    coherence rewriting). *)
Lemma pa_Cst_h_le : forall m : nat,
  (2 # 1)%Q * ((1 # 1) / (Z.of_nat (8 * 2 ^ (8 * m + 20) * (4 * m + 5)) # 1)) * pa_gCst m
  == (1 # 1) / (Z.of_nat (64 * (4 * m + 5)) # 1).
Proof.
  intro m.
  assert (Hs : (8 * 2 ^ (8 * m + 20) = 128 * 2 ^ (8 * m + 16))%nat).
  { replace (8 * m + 20)%nat with ((8 * m + 16) + 4)%nat by lia.
    rewrite pa_two_pow_add.
    replace (2 ^ 4)%nat with 16%nat by reflexivity.
    lia. }
  unfold pa_gCst.
  rewrite Hs.
  rewrite (Nat2Z.inj_mul (128 * 2 ^ (8 * m + 16)) (4 * m + 5)).
  rewrite (Nat2Z.inj_mul 128 (2 ^ (8 * m + 16))).
  change (Z.of_nat 128) with 128%Z.
  assert (Hpw : (0 < 2 ^ (8 * m + 16))%nat) by apply pa_nat_pow2_pos.
  assert (Hpn : (0 < 4 * m + 5)%nat) by lia.
  assert (H64 : (Z.of_nat (64 * (4 * m + 5)) = 64 * Z.of_nat (4 * m + 5))%Z).
  { rewrite (Nat2Z.inj_mul 64 (4 * m + 5)).
    change (Z.of_nat 64) with 64%Z. reflexivity. }
  rewrite H64.
  destruct (Z.of_nat (2 ^ (8 * m + 16))) as [| w' | w'] eqn:Ew;
    destruct (Z.of_nat (4 * m + 5)) as [| u' | u'] eqn:Eu;
    unfold Qdiv, Qeq; cbn; lia.
Qed.

(** F2. The half-power Archimedean property (final leg via
    [pa_inv_mono] and a [change] reduction to the constructor form). *)
Lemma pa_q_half_arch : forall e : Q, Qlt 0 e -> { t : nat | Qlt (q_pow (1 # 2)%Q t) e }.
Proof.
  intros e He.
  assert (Hnum : (0 < Qnum e)%Z).
  { unfold Qlt in He. cbn [Qnum Qden] in He.
    rewrite Z.mul_0_l, Z.mul_1_r in He. exact He. }
  assert (Hdpos : (0 < Z.pos (Qden e))%Z) by lia.
  set (t := Z.to_nat (Z.pos (Qden e))).
  assert (Htid : Z.pos (Qden e) = Z.of_nat t).
  { unfold t. symmetry. apply Z2Nat.id. apply Zle_0_pos. }
  assert (Hpow : (t < 2 ^ t)%nat)
    by (apply (Nat.pow_gt_lin_r 2 t (Nat.lt_succ_diag_r 1)); lia).
  assert (Hden : (Z.pos (Qden e) < Z.of_nat (2 ^ t))%Z).
  { rewrite Htid. apply (proj1 (Nat2Z.inj_lt t (2 ^ t))). exact Hpow. }
  exists t.
  rewrite pa_qpow_half_inv.
  assert (Hrpos : Qlt 0 (Z.pos (Qden e) # 1)) by (unfold Qlt; cbn [Qnum Qden]; lia).
  pose proof (pa_nat_pow2_pos t) as Hpw.
  apply (proj1 (Qmult_lt_r ((1 # 1) / (Z.of_nat (2 ^ t) # 1)) e
                    (Z.pos (Qden e) # 1) Hrpos)).
  apply (pa_qlt_qeq_lr
           (((1 # 1) / (Z.of_nat (2 ^ t) # 1)) * (Z.pos (Qden e) # 1))
           (Qnum e # 1)
           (((1 # 1) / (Z.of_nat (2 ^ t) # 1)) * (Z.pos (Qden e) # 1))
           (e * (Z.pos (Qden e) # 1))).
  - unfold Qlt, Qdiv.
    destruct (Z.of_nat (2 ^ t)) as [| w' | w'] eqn:Ew;
      destruct (Z.pos (Qden e)) as [| u' | u'] eqn:Eu.
    all: cbn.
    all: rewrite ?Pos.mul_1_r in *.
    all: try lia.
    all: assert (Hn1 : (1 <= Qnum e)%Z) by lia;
         assert (H0w : (0 <= Z.pos w')%Z) by lia;
         assert (Hbw : (Z.pos w' <= Qnum e * Z.pos w')%Z)
           by (pose proof (Zmult_le_compat_l 1 (Qnum e) (Z.pos w') Hn1 H0w) as Hx;
               rewrite Z.mul_1_r, Z.mul_comm in Hx; exact Hx);
         lia.
  - reflexivity.
  - destruct e as [n d]; unfold Qeq; cbn; rewrite ?Pos.mul_1_r; lia.
Qed.

(** F3. Full assembly of the main statement (the [k]-side leg and
    the final assembly of the three-part sum). *)
Theorem piL_arctan_fixed_sc : forall e : Q, Qlt 0 e ->
  { K : nat | forall k m : nat, (1 <= k)%nat -> (K <= k)%nat -> (K <= m)%nat ->
      Qlt (Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m))) e }.
Proof.
  intros e He.
  assert (Hhalf : Qlt 0 ((1 # 2) * e))
    by (apply Qmult_lt_0_compat; [exact leibsep_qlt_1 | exact He]).
  destruct (pa_q_half_arch ((2 # 13) * e)) as [t1 Ht1].
  { apply Qmult_lt_0_compat; [unfold Qlt; cbn [Qnum Qden]; lia | exact He]. }
  destruct (pa_q_half_arch ((4 # 9) * (1 # 2) * e)) as [t2 Ht2].
  { apply (Qmult_lt_0_compat ((4 # 9) * (1 # 2)) e);
      [unfold Qlt; cbn [Qnum Qden Qmult]; lia | exact He]. }
  exists (Nat.max (2 ^ t1) t2).
  intros k m Hk1 HkK HmK.
  assert (Habs : Qabs (aF k m 1)
                 == Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m))).
  { apply lw0_pitB_pair_conv_qabs_wd.
    unfold aF.
    rewrite (pa_sin_wd k (aA m 1) (lp_odd m) (aA_one_lp_odd m)).
    rewrite (pa_cos_wd k (aA m 1) (lp_odd m) (aA_one_lp_odd m)).
    ring. }
  rewrite <- Habs.
  assert (HN : (0 < 8 * 2 ^ (8 * m + 20) * (4 * m + 5))%nat).
  { pose proof (pa_nat_pow2_pos (8 * m + 20)). lia. }
  pose proof (pa_F_one_bound k m (8 * 2 ^ (8 * m + 20) * (4 * m + 5)) Hk1 HN
                (fun x h Hx0 Hx1 Hh0 Hxh1 =>
                   pa_aF_step k m x h Hk1 Hx0 Hx1 Hh0 Hxh1)) as Hb.
  rewrite (pa_Cst_h_le m) in Hb.
  assert (Hb2 : Qle (Qabs (aF k m 1))
                 (((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
                   + (1 # 1) / (Z.of_nat (64 * (4 * m + 5)) # 1))
                  + (9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1)))).
  { apply (pa_le_qeq_r (Qabs (aF k m 1))
             ((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
              + (9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1))
              + (1 # 1) / (Z.of_nat (64 * (4 * m + 5)) # 1))
             (((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
               + (1 # 1) / (Z.of_nat (64 * (4 * m + 5)) # 1))
              + (9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1)))).
    - exact Hb.
    - ring. }
  assert (Hstep : Qlt (((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
                        + (1 # 1) / (Z.of_nat (64 * (4 * m + 5)) # 1))
                       + (9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1))) e).
  { assert (Hs0 : Qlt 0 ((1 # 1) / (Z.of_nat (4 * m + 5) # 1)))
      by (apply (pa_h_pos (4 * m + 5)); lia).
    assert (Hw64s : Qle ((1 # 1) / (Z.of_nat (64 * (4 * m + 5)) # 1))
                        ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))).
    { apply (pa_inv_mono (Z.of_nat (4 * m + 5) # 1) (Z.of_nat (64 * (4 * m + 5)) # 1)).
      - unfold Qlt. cbn [Qnum Qden]. lia.
      - unfold Qle. cbn [Qnum Qden]. lia. }
    assert (Hc134 : Qlt 0 (13 # 4)%Q) by (unfold Qlt; cbn [Qnum Qden]; lia).
    assert (Hc943 : Qlt 0 (9 # 4)%Q) by (unfold Qlt; cbn [Qnum Qden]; lia).
    assert (Hm : Qlt ((13 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))) ((1 # 2) * e)).
    { assert (Hs4 : Qle ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
                        ((1 # 1) / (Z.of_nat (4 * 2 ^ t1) # 1))).
      { apply (pa_inv_mono (Z.of_nat (4 * 2 ^ t1) # 1) (Z.of_nat (4 * m + 5) # 1)).
        - unfold Qlt. cbn [Qnum Qden]. pose proof (pa_nat_pow2_pos t1). lia.
        - unfold Qle. cbn [Qnum Qden]. lia. }
      assert (Hq4 : ((1 # 1) / (Z.of_nat (4 * 2 ^ t1) # 1))
                    == ((1 # 4)%Q * q_pow (1 # 2)%Q t1)).
      { apply (Qeq_trans _ ((1 # 4)%Q * ((1 # 1) / (Z.of_nat (2 ^ t1) # 1)))).
        - rewrite (Nat2Z.inj_mul 4 (2 ^ t1)).
          change (Z.of_nat 4) with 4%Z.
          destruct (Z.of_nat (2 ^ t1)) as [| w' | w'] eqn:Ew;
            unfold Qdiv, Qeq; cbn; lia.
        - rewrite <- (pa_qpow_half_inv t1). apply Qeq_refl. }
      rewrite Hq4 in Hs4.
      assert (Hsc : Qlt ((13 # 4)%Q * q_pow (1 # 2)%Q t1) ((1 # 2) * e)).
      { apply (pa_qlt_qeq_lr _ _ _ _
                 (Qmult_lt_compat_r (q_pow (1 # 2)%Q t1) ((2 # 13) * e) (13 # 4)%Q
                    Hc134 Ht1)); ring. }
      apply (Qle_lt_trans _ ((13 # 1)%Q * ((1 # 4)%Q * q_pow (1 # 2)%Q t1))).
      - apply (pa_Qmult_le_l _ _ (13 # 1)%Q).
        + exact Hs4.
        + unfold Qle. cbn [Qnum Qden]. lia.
      - apply (pa_qlt_qeq_lr _ _ _ _ Hsc); ring. }
    assert (Hk2 : Qlt ((9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1))) ((1 # 2) * e)).
    { assert (Hq2pos : Qlt 0 (q_pow (2 # 1)%Q t2)).
      { rewrite (pa_qpow2_coherence t2).
        unfold Qlt. cbn [Qnum Qden]. pose proof (pa_nat_pow2_pos t2). lia. }
      assert (Hcq : Qle (q_pow (2 # 1)%Q t2) (q_fact (2 * t2 + 1))).
      { pose proof (pa_qfact_ge_pow2Q t2) as Hcq0.
        replace (Datatypes.S t2) with (t2 + 1)%nat in Hcq0 by lia.
        apply (Qle_trans _ (q_fact (t2 + 1))); [exact Hcq0 |].
        apply (pa_qfact_mono (t2 + 1) (2 * t2 + 1)). lia. }
      assert (Hcq1 : Qle (q_pow (2 # 1)%Q t2) (q_fact (2 * k + 1))).
      { apply (Qle_trans _ (q_fact (2 * t2 + 1)) _); [exact Hcq |].
        apply (pa_qfact_mono (2 * t2 + 1) (2 * k + 1)). lia. }
      assert (Hwinv : Qle ((1 # 1) / q_fact (2 * k + 1)) (q_pow (1 # 2)%Q t2)).
      { apply (pa_le_qeq_r ((1 # 1) / q_fact (2 * k + 1))
                 ((1 # 1) / q_pow (2 # 1)%Q t2) (q_pow (1 # 2)%Q t2)).
        - apply (pa_inv_mono (q_pow (2 # 1)%Q t2) (q_fact (2 * k + 1))); assumption.
        - rewrite (pa_qpow2_coherence t2).
          rewrite <- (pa_qpow_half_inv t2).
          apply Qeq_refl. }
      apply (Qle_lt_trans _ ((9 # 4)%Q * q_pow (1 # 2)%Q t2)).
      - apply (pa_Qmult_le_l ((1 # 1) / q_fact (2 * k + 1))
                 (q_pow (1 # 2)%Q t2) (9 # 4)%Q);
          [exact Hwinv | apply Qlt_le_weak; exact Hc943].
      - apply (pa_qlt_qeq_lr _ _ _ _
                 (Qmult_lt_compat_r (q_pow (1 # 2)%Q t2)
                    ((4 # 9)%Q * (1 # 2) * e) (9 # 4)%Q Hc943 Ht2)); ring. }
    apply (Qle_lt_trans
             (((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
               + (1 # 1) / (Z.of_nat (64 * (4 * m + 5)) # 1))
              + (9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1)))
             ((13 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
              + (9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1)))).
    - apply Qplus_le_compat.
      + apply (pa_le_qeq_r
                 ((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
                  + (1 # 1) / (Z.of_nat (64 * (4 * m + 5)) # 1))
                 ((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
                  + ((1 # 1) / (Z.of_nat (4 * m + 5) # 1)))
                 ((13 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1)))).
        * apply Qplus_le_compat; [apply Qle_refl | exact Hw64s].
        * ring.
      + apply Qle_refl.
    - apply (pa_qlt_qeq_lr _ _ _ _ (Qplus_lt_compat _ _ _ _ Hm Hk2)); ring. }
  apply (Qle_lt_trans (Qabs (aF k m 1))
           (((12 # 1)%Q * ((1 # 1) / (Z.of_nat (4 * m + 5) # 1))
             + (1 # 1) / (Z.of_nat (64 * (4 * m + 5)) # 1))
            + (9 # 4)%Q * ((1 # 1) / q_fact (2 * k + 1)))).
  - exact Hb2.
  - exact Hstep.
Qed.


(* ================= Section 4. Audit ([Print Assumptions], anchored at line starts) ================= *)

Print Assumptions aA_one_lp_odd.
Print Assumptions gG_one_x2.
Print Assumptions pa_aA_term_le_lp_pair.
Print Assumptions pa_D_le.
Print Assumptions pa_aA_term_step_D.
Print Assumptions pa_aA_term_step_le.
Print Assumptions pa_aA_term_step_ge.
Print Assumptions pa_aA_step_le.
Print Assumptions pa_aA_step_ge.

Print Assumptions pa_sin_step.
Print Assumptions pa_cos_step.
Print Assumptions pa_aF_step.
Print Assumptions piL_arctan_fixed_sc.
