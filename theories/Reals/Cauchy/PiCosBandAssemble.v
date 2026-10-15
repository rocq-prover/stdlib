(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** * PiCosBandAssemble.v: band assembly for the cos double-angle identity

    Mission.  Partial-sum stratification of the cos double-angle
    identity [cos(2x) = cos^2 - sin^2]: the absolute-value upper bound
    of the offset band [k+1,2k+1] of the truncation remainder
    [piL_cos_dres], the band row controlling term
    [t'_m(B) = (2B)^(2m)/(2m)!], and monotonicity.  Contents:
    (1) closed forms of the even and odd half-sums of the Pascal rows
    (the even half-row == the odd half-row == 2^(2m)/2) and the
    double-angle row identity [cos_term N (2x) == even half-row - odd
    half-row]; (2) row majorants and the main band bound,
    monotonicity, and truncation-length selection (continued in the
    later sections).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [QArith.Qround], [ZArith.ZArith], [Arith.PeanoNat], [Lia];
    [PiKernelSlack] ([q_pow]/[q_fact], [sin_term]/[cos_term], the
    [QleT']/[QltT] bridges, the [q_pow] family);
    [PiKernelSlack_D1_identity] ([piL_cos_dres],
    [piL_cos_partial_double]); [PiKernelSlack_D2_remainder]
    (term-level absolute-value bounds); [PiKernelSlack_D3_prereq]
    ([d3p_quarter_pow_lt], [d3p_inject_ceiling_ge]);
    [PiPascalMachine] (the [piLsb_sumR] row-sum machine, the binomial
    row family); [PiPascalResidue] ([piLc_sumR_rev]);
    [PiRowIdentity] ([piLrowB_row_scal] scalar extraction).

    References.  The partial-sum band expansion of
    [cos(2x) = cos^2 - sin^2] (the even half-row C(2m,2i) and the odd
    half-row C(2m,2i+1) take equal values); the geometric tail bound
    [sum_{i<n}(1/4)^i + (4/3)(1/4)^n == 4/3]; the row-by-row
    controlling-term method for truncation-remainder bands.

    Constructivity.  Statements live entirely on the stdlib
    [Qeq]/[Qle]/[Qlt] with [Set]-level [sigT] carriers; zero axioms,
    no abandoned proofs, no classical logic; induction with
    explicit algebraic chains and zero solvers on the [Q] side
    ([Lia] only for [nat] bookkeeping); [Print Assumptions] at the
    end of the file checks each item [Closed].

    WARNING: this file is experimental and likely to change in future releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs QArith.Qround.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.
Require Import PiPascalMachine.
Require Import PiPascalResidue.
Require Import PiRowIdentity.

(* ================= Section 1. Row-sum machine glue supplements ================= *)

(** Band-sum splitting: [Σ_{i<a+p} f i == Σ_{i<a} f i + Σ_{j<p} f (a+j)]. *)
Lemma piLe_sumR_split : forall (f : nat -> Q) (a p : nat),
  piLsb_sumR f (a + p)%nat
  == piLsb_sumR f a + piLsb_sumR (fun u => f (a + u)%nat) p.
Proof.
  intros f a p. revert f. induction a as [| a IH]; intros f.
  - replace (0 + p)%nat with p%nat by lia.
    assert (Hext : piLsb_sumR (fun u => f (0 + u)%nat) p == piLsb_sumR f p).
    { apply piLsb_sumR_ext. intros i _. replace (0 + i)%nat with i%nat by lia.
      apply Qeq_refl. }
    rewrite Hext. cbn [piLsb_sumR]. ring.
  - replace (S a + p)%nat with (S (a + p))%nat by lia.
    rewrite piLsb_sumR_head with (f := f) (n := a).
    rewrite piLsb_sumR_head.
    rewrite (IH (fun i => f (S i))).
    assert (Hz : piLsb_sumR (fun u => f (S a + u)%nat) p
                 == piLsb_sumR (fun i => f (S (a + i))%nat) p).
    { apply piLsb_sumR_ext. intros i _.
      replace (S a + i)%nat with (S (a + i))%nat by lia. apply Qeq_refl. }
    rewrite Hz. ring.
Qed.

(** Order under right addition: [0 <= y] implies [x <= x + y]. *)
Lemma piLe_qle_add_rw : forall x y : Q, Qle 0 y -> Qle x (x + y).
Proof.
  intros x y Hy.
  assert (He : x%Q == (x + 0%Q)%Q) by ring.
  rewrite He at 1.
  apply (proj2 (Qplus_le_r 0%Q y x)).
  exact Hy.
Qed.

(** Nonnegative row sums: pointwise nonnegativity implies a nonnegative row sum. *)
Lemma piLe_sumR_nonneg : forall (f : nat -> Q) (n : nat),
  (forall i : nat, (i < n)%nat -> Qle 0 (f i)) ->
  Qle 0 (piLsb_sumR f n).
Proof.
  intros f n. induction n as [| n IH]; intros Hf.
  - cbn [piLsb_sumR]. apply Qle_refl.
  - cbn [piLsb_sumR].
    apply (Qle_trans _ (0%Q + piLsb_sumR f n)%Q).
    + apply piLe_qle_add_rw.
      apply IH. intros i Hi. apply Hf. lia.
    + rewrite Qplus_0_l.
      apply piLe_qle_add_rw.
      apply Hf. lia.
Qed.

(** Row-sum monotonicity: pointwise [<=] implies [<=] for the row sums. *)
Lemma piLe_sumR_le : forall (f g : nat -> Q) (n : nat),
  (forall i : nat, (i < n)%nat -> Qle (f i) (g i)) ->
  Qle (piLsb_sumR f n) (piLsb_sumR g n).
Proof.
  intros f g n. induction n as [| n IH]; intros Hf.
  - cbn [piLsb_sumR]. apply Qle_refl.
  - cbn [piLsb_sumR].
    apply (Qle_trans _ (piLsb_sumR g n + f n)%Q).
    + apply (proj2 (Qplus_le_l (piLsb_sumR f n) (piLsb_sumR g n) (f n)%Q)).
      * apply IH. intros i Hi. apply Hf. lia.
    + apply (proj2 (Qplus_le_r (f n)%Q (g n)%Q (piLsb_sumR g n))).
      * apply Hf. lia.
Qed.

(** Triangle inequality for row sums: [|Σ f| <= Σ |f|]. *)
Lemma piLe_abs_sumR_le : forall (f : nat -> Q) (n : nat),
  Qle (Qabs (piLsb_sumR f n)) (piLsb_sumR (fun i => Qabs (f i)) n).
Proof.
  intros f n. induction n as [| n IH].
  - cbn [piLsb_sumR Qabs Qnum Qden]. apply Qle_refl.
  - cbn [piLsb_sumR].
    apply (Qle_trans _ (Qabs (piLsb_sumR f n) + Qabs (f n))).
    + apply Qabs_triangle.
    + apply (proj2 (Qplus_le_l (Qabs (piLsb_sumR f n))
                   (piLsb_sumR (fun i => Qabs (f i)) n) (Qabs (f n)))).
      exact IH.
Qed.

(** Sub-row-sum bound: if the window [a, a+n) is contained in [0, m) and the row is nonnegative, then the shifted row sum is at most the full row sum. *)
Lemma piLe_sumR_shift_le : forall (f : nat -> Q) (a n m : nat),
  (a + n <= m)%nat ->
  (forall i : nat, Qle 0 (f i)) ->
  Qle (piLsb_sumR (fun u => f (a + u)%nat) n) (piLsb_sumR f m).
Proof.
  intros f a n m Hle Hpos.
  assert (HmEq : m%nat = (a + n + (m - (a + n)))%nat) by lia.
  rewrite HmEq.
  rewrite piLe_sumR_split.
  rewrite (piLe_sumR_split f a n).
  assert (Hpre : Qle 0 (piLsb_sumR f a)) by (apply piLe_sumR_nonneg; intros i _; apply Hpos).
  assert (Htail : Qle 0 (piLsb_sumR (fun u => f (a + n + u)%nat) (m - (a + n))))
    by (apply piLe_sumR_nonneg; intros i _; apply Hpos).
  rewrite (Qplus_comm (piLsb_sumR f a)
             (piLsb_sumR (fun u => f (a + u)%nat) n)).
  apply (Qle_trans _ (piLsb_sumR (fun u => f (a + u)%nat) n + piLsb_sumR f a)%Q).
  - apply piLe_qle_add_rw. exact Hpre.
  - apply piLe_qle_add_rw. exact Htail.
Qed.

(** [Q]-order cancellation: [0 < c] and [a·c <= b·c] imply [a <= b]. *)
Lemma piLe_qle_mul_pos_cancel : forall (a b c : Q),
  Qlt 0 c -> Qle (a * c) (b * c) -> Qle a b.
Proof.
  intros a b c Hc H.
  assert (Hc0 : ~ (c == 0)%Q) by (apply q_neq_of_lt; exact Hc).
  assert (Ha : a == a * c * / c).
  { symmetry. transitivity (a * (c * / c))%Q.
    - ring.
    - rewrite (Qmult_inv_r c Hc0). ring. }
  assert (Hb : b == b * c * / c).
  { symmetry. transitivity (b * (c * / c))%Q.
    - ring.
    - rewrite (Qmult_inv_r c Hc0). ring. }
  rewrite Ha, Hb.
  apply (Qmult_le_compat_r (a * c) (b * c) (/ c)).
  - exact H.
  - apply Qinv_le_0_compat. apply Qlt_le_weak. exact Hc.
Qed.

(** [Qeq] right-division cancellation: [c] nonzero and [a·c == b] imply [a == b/c]. *)
Lemma piLe_qeq_mul_div_r : forall (a b c : Q),
  ~ (c == 0)%Q -> a * c == b -> a == b / c.
Proof.
  intros a b c Hc H.
  unfold Qdiv.
  assert (Hz : b * / c == a * (c * / c)) by (rewrite <- H; ring).
  rewrite Hz, (Qmult_inv_r c Hc). ring.
Qed.

(** Multiplicativity of [Qinv]: for nonzero [a] and [d], [/a·/d == /(a·d)]. *)
Lemma piLe_qinv_distr : forall a d : Q,
  ~ (a == 0)%Q -> ~ (d == 0)%Q -> / a * / d == / (a * d)%Q.
Proof.
  intros a d Ha Hd.
  assert (Had : ~ ((a * d)%Q == 0)).
  { intro H0. apply Ha.
    apply (piLrowB_qeq_cancel_l a 0%Q d Hd).
    rewrite H0. symmetry. apply Qmult_0_l. }
  apply (piLrowB_qeq_cancel_l (/ a * / d) (/ (a * d)) (a * d) Had).
  assert (Hr : / (a * d) * (a * d) == 1).
  { rewrite (Qmult_comm (/ (a * d)) (a * d)).
    apply Qmult_inv_r. exact Had. }
  transitivity 1%Q.
  - transitivity (a * / a * (d * / d))%Q.
    + ring.
    + rewrite (Qmult_inv_r a Ha), (Qmult_inv_r d Hd). reflexivity.
  - symmetry. exact Hr.
Qed.

(** Embedding order: [a <= b] implies [(Z.of_nat a # 1) <= (Z.of_nat b # 1)]. *)
Lemma piLe_inject_le : forall a b : nat, (a <= b)%nat ->
  Qle (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b H. unfold Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_r. apply Nat2Z.inj_le. exact H.
Qed.

(** Embedding positivity: [0 < (Z.of_nat (S n) # 1)] (at [n = 0], [Z.of_nat 0 # 1 == 0], hence [S n]). *)
Lemma piLe_inject_pos : forall n : nat, Qlt 0 (Z.of_nat (S n) # 1).
Proof.
  intros n. unfold Qlt. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  exact (proj1 (Nat2Z.inj_lt 0 (S n)) (Nat.lt_0_succ n)).
Qed.

(** The embedding is nonzero. *)
Lemma piLe_inject_neq0 : forall n : nat, ~ ((Z.of_nat (S n) # 1)%Q == 0).
Proof.
  intros n H. apply Qeq_sym in H.
  exact (Qlt_not_eq 0 (Z.of_nat (S n) # 1) (piLe_inject_pos n) H).
Qed.

(** Factorial pairs are nonzero. *)
Lemma piLe_qfact_pair_neq0 : forall i j : nat,
  ~ (q_fact i * q_fact j == 0)%Q.
Proof.
  intros i j H.
  exact (q_neq_of_lt (q_fact i * q_fact j)
           (Qmult_lt_0_compat (q_fact i) (q_fact j)
              (q_fact_pos i) (q_fact_pos j)) H).
Qed.

(** Positive powers: [0 < x] implies [0 < q_pow x n]. *)
Lemma piLe_q_pow_pos : forall (x : Q) (n : nat),
  Qlt 0 x -> Qlt 0 (q_pow x n).
Proof.
  intros x n Hx. induction n as [| n IH].
  - unfold Qlt. cbn [q_pow Qnum Qden]. lia.
  - rewrite q_pow_succ. apply Qmult_lt_0_compat; [exact Hx | exact IH].
Qed.

(* ================= Section 2. Group alpha: cos band carriers ================= *)

(** The cos band row controlling term: [t'_m(B) = (2B)^(2m)/(2m)!]. *)
Definition piLe_tc_term (m : nat) (B : Q) : Q :=
  q_pow (2 * B) (2 * m)%nat / q_fact (2 * m)%nat.

(** The cos band bound: [Σ_{m=k+1}^{2k+1} t'_m] over the row range [k+1,2k+1] (one row more than the sin side: the [s_k^2] term of row [m = 2k+1]). *)

Definition piLe_band_bound (k : nat) (B : Q) : Q :=
  piLsb_sumR (fun u => piLe_tc_term (S (k + u))%nat B) (S (S k)).

(** The two row families of the cos band (retained windows): [ccrow] is the C^2 family with [i+j=m] over the window [m-k,k]; [ssrow] is the S^2 family with [i+j=m-1] over the window [m-1-k,k] (the indices are shifted by one). *)

Definition piLe_ccrow (k m : nat) (x : Q) : Q :=
  piLsb_sumR (fun u => cos_term (m - k + u)%nat x * cos_term (k - u)%nat x)
             (2 * k + 1 - m)%nat.

Definition piLe_ssrow (k m : nat) (x : Q) : Q :=
  piLsb_sumR (fun u => sin_term (m - 1 - k + u)%nat x * sin_term (k - u)%nat x)
             (2 * k + 2 - m)%nat.

(** Nonnegativity and positivity of the [t'] terms. *)
Lemma piLe_tc_term_nonneg : forall (B : Q) (m : nat),
  Qle 0 B -> Qle 0 (piLe_tc_term m B).
Proof.
  intros B m H0B. unfold piLe_tc_term.
  assert (H02B : Qle 0 (2 * B)).
  { apply Qmult_le_0_compat;
      [ unfold Qle; cbn [Qnum Qden]; lia | exact H0B ]. }
  apply (Qle_trans _ (0 / q_fact (2 * m)%nat)%Q).
  - assert (Hz : 0 / q_fact (2 * m)%nat == 0%Q) by (unfold Qdiv; ring).
    rewrite Hz. apply Qle_refl.
  - apply Qle_div_same_denom; [apply q_fact_pos | apply q_pow_nonneg; exact H02B].
Qed.

Lemma piLe_tc_term_pos : forall (B : Q) (m : nat),
  Qlt 0 B -> Qlt 0 (piLe_tc_term m B).
Proof.
  intros B m HB. unfold piLe_tc_term. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - apply piLe_q_pow_pos.
    apply (Qmult_lt_0_compat 2%Q B).
    + unfold Qlt; cbn [Qnum Qden]; lia.
    + exact HB.
  - apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* ================= Section 3. Group beta: closed forms of the even and odd half-sums of Pascal rows ================= *)

(** Even-odd half-sum equality: [Σ_{i<=m} C(2m,2i) == Σ_{i<m} C(2m,2i+1)]. *)
Lemma piLe_row_half_eq : forall m : nat, (1 <= m)%nat ->
  piLsb_sumR (fun i => bpa_binom (2 * m)%nat (2 * i)%nat) (S m)
  == piLsb_sumR (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat)) m.
Proof.
  intros m Hm.
  assert (H2m : (1 <= 2 * m)%nat) by lia.
  assert (Halt := piLsb_row_alt (2 * m)%nat H2m).
  rewrite piLsb_sumR_even_odd_S in Halt.
  assert (Hev : piLsb_sumR
                  (fun i => bpa_binom (2 * m)%nat (2 * i)%nat * lw0_alt (2 * i)%nat) (S m)
                == piLsb_sumR (fun i => bpa_binom (2 * m)%nat (2 * i)%nat) (S m)).
  { apply piLsb_sumR_ext. intros i _. rewrite piLsb_lw0_alt_even. ring. }
  assert (Hod : piLsb_sumR
                  (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat) * lw0_alt (S (2 * i)%nat)) m
                == - piLsb_sumR (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat)) m).
  { rewrite <- piLsb_sumR_opp. apply piLsb_sumR_ext. intros i _.
    rewrite piLsb_lw0_alt_odd. ring. }
  rewrite Hev, Hod in Halt.
  assert (Hswap : piLsb_sumR (fun i => bpa_binom (2 * m)%nat (2 * i)%nat) (S m)
                  + (- piLsb_sumR (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat)) m)%Q
                  == piLsb_sumR (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat)) m
                     + (- piLsb_sumR (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat)) m)%Q)
    by (rewrite Halt; ring).
  apply (piLsb_eq_cancel_r _ _ (- piLsb_sumR (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat)) m)%Q).
  exact Hswap.
Qed.

(** Value of the even half-row: [Σ_{i<=m} C(2m,2i) == 2^(2m)·1/2]. *)
Lemma piLe_row_half_even_val : forall m : nat, (1 <= m)%nat ->
  piLsb_sumR (fun i => bpa_binom (2 * m)%nat (2 * i)%nat) (S m)
  == q_pow 2%Q (2 * m)%nat * (1 # 2)%Q.
Proof.
  intros m Hm.
  assert (Heq := piLe_row_half_eq m Hm).
  assert (Htot : piLsb_sumR (fun i => bpa_binom (2 * m)%nat (2 * i)%nat) (S m)
                 + piLsb_sumR (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat)) m
                 == q_pow 2%Q (2 * m)%nat).
  { rewrite <- (piLsb_sumR_even_odd_S (bpa_binom (2 * m)%nat) m).
    exact (proj1 (piLsb_bpa_row_tot (2 * m)%nat)). }
  rewrite <- Heq in Htot.
  assert (Hh : q_pow 2%Q (2 * m)%nat * (1 # 2)%Q + q_pow 2%Q (2 * m)%nat * (1 # 2)%Q
               == q_pow 2%Q (2 * m)%nat) by ring.
  rewrite <- Hh in Htot.
  apply piLsb_eq_cancel_dbl. exact Htot.
Qed.

(** Value of the odd half-row: [Σ_{i<m} C(2m,2i+1) == 2^(2m)·1/2]. *)
Lemma piLe_row_half_odd_val : forall m : nat, (1 <= m)%nat ->
  piLsb_sumR (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat)) m
  == q_pow 2%Q (2 * m)%nat * (1 # 2)%Q.
Proof.
  intros m Hm.
  assert (Heq := piLe_row_half_eq m Hm).
  assert (Htot : piLsb_sumR (fun i => bpa_binom (2 * m)%nat (2 * i)%nat) (S m)
                 + piLsb_sumR (fun i => bpa_binom (2 * m)%nat (S (2 * i)%nat)) m
                 == q_pow 2%Q (2 * m)%nat).
  { rewrite <- (piLsb_sumR_even_odd_S (bpa_binom (2 * m)%nat) m).
    exact (proj1 (piLsb_bpa_row_tot (2 * m)%nat)). }
  rewrite Heq in Htot.
  assert (Hh : q_pow 2%Q (2 * m)%nat * (1 # 2)%Q + q_pow 2%Q (2 * m)%nat * (1 # 2)%Q
               == q_pow 2%Q (2 * m)%nat) by ring.
  rewrite <- Hh in Htot.
  apply piLsb_eq_cancel_dbl. exact Htot.
Qed.

(** Even-split closed form: [Σ_{i<=m} 1/((2i)!(2(m-i))!) == 2^(2m)/(2m)!·1/2] for [m >= 1]. *)
Lemma piLe_row_even_full : forall m : nat, (1 <= m)%nat ->
  piLsb_sumR (fun i => 1 / (q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat))
             (S m)
  == q_pow 2%Q (2 * m)%nat / q_fact (2 * m)%nat * (1 # 2)%Q.
Proof.
  intros m Hm.
  assert (HD0 : ~ (q_fact (2 * m)%nat == 0)%Q) by apply piLrowB_qfact_neq0.
  assert (Hkey : piLsb_sumR
                   (fun i => 1 / (q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat)) (S m)
                 * q_fact (2 * m)%nat
                 == q_pow 2%Q (2 * m)%nat * (1 # 2)%Q).
  { rewrite (piLrowB_row_scal_r (q_fact (2 * m)%nat)
                  (fun i => 1 / (q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat)) (S m)).
    rewrite <- (piLe_row_half_even_val m Hm).
    apply piLsb_sumR_ext. intros i Hi.
    assert (Hbm : (2 * i <= 2 * m)%nat) by (apply Nat.mul_le_mono_l; lia).
    assert (Hbr := piLsb_bpa_bridge (2 * m)%nat (2 * i)%nat Hbm).
    replace (2 * m - 2 * i)%nat with (2 * (m - i))%nat in Hbr by lia.
    assert (Hd0 : ~ ((q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat) == 0)%Q)
      by (apply piLe_qfact_pair_neq0).
    assert (Hbr2 : bpa_binom (2 * m)%nat (2 * i)%nat
                   * (q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat)
                   == q_fact (2 * m)).
    { transitivity (bpa_binom (2 * m)%nat (2 * i)%nat * q_fact (2 * i)%nat
                    * q_fact (2 * (m - i))%nat)%Q.
      - ring.
      - exact Hbr. }
    symmetry.
    apply (piLrowB_qeq_cancel_l (bpa_binom (2 * m)%nat (2 * i)%nat)
             (1 / (q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat)
              * q_fact (2 * m))
             (q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat) Hd0).
    rewrite Hbr2. symmetry.
    transitivity (q_fact (2 * m)
                  * (q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat
                     * / (q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat)))%Q.
    - unfold Qdiv. ring.
    - rewrite (Qmult_inv_r (q_fact (2 * i)%nat * q_fact (2 * (m - i))%nat) Hd0).
      ring. }
  rewrite (piLe_qeq_mul_div_r _ _ _ HD0 Hkey).
  unfold Qdiv. ring.
Qed.

(** Odd-split closed form: [Σ_{i<m} 1/((2i+1)!(2(m-1-i)+1)!) == 2^(2m)/(2m)!·1/2] for [m >= 1]. *)
Lemma piLe_row_odd_full : forall m : nat, (1 <= m)%nat ->
  piLsb_sumR (fun i => 1 / (q_fact (S (2 * i))%nat
                                * q_fact (S (2 * (m - 1 - i))%nat))) m
  == q_pow 2%Q (2 * m)%nat / q_fact (2 * m)%nat * (1 # 2)%Q.
Proof.
  intros m Hm.
  assert (HD0 : ~ (q_fact (2 * m)%nat == 0)%Q) by apply piLrowB_qfact_neq0.
  assert (Hkey : piLsb_sumR
                   (fun i => 1 / (q_fact (S (2 * i))%nat
                                   * q_fact (S (2 * (m - 1 - i))%nat))) m
                 * q_fact (2 * m)%nat
                 == q_pow 2%Q (2 * m)%nat * (1 # 2)%Q).
  { rewrite (piLrowB_row_scal_r (q_fact (2 * m)%nat)
                  (fun i => 1 / (q_fact (S (2 * i))%nat
                                  * q_fact (S (2 * (m - 1 - i))%nat))) m).
    rewrite <- (piLe_row_half_odd_val m Hm).
    apply piLsb_sumR_ext. intros i Hi.
    assert (Hbm : (S (2 * i) <= 2 * m)%nat) by lia.
    assert (Hbr := piLsb_bpa_bridge (2 * m)%nat (S (2 * i))%nat Hbm).
    replace (2 * m - S (2 * i))%nat with (S (2 * (m - 1 - i)))%nat in Hbr by lia.
    assert (Hd0 : ~ ((q_fact (S (2 * i))%nat
                      * q_fact (S (2 * (m - 1 - i)))%nat) == 0)%Q)
      by (apply piLe_qfact_pair_neq0).
    assert (Hbr2 : bpa_binom (2 * m)%nat (S (2 * i))%nat
                   * (q_fact (S (2 * i))%nat * q_fact (S (2 * (m - 1 - i)))%nat)
                   == q_fact (2 * m)).
    { transitivity (bpa_binom (2 * m)%nat (S (2 * i))%nat * q_fact (S (2 * i))%nat
                    * q_fact (S (2 * (m - 1 - i)))%nat)%Q.
      - ring.
      - exact Hbr. }
    symmetry.
    apply (piLrowB_qeq_cancel_l (bpa_binom (2 * m)%nat (S (2 * i))%nat)
             (1 / (q_fact (S (2 * i))%nat * q_fact (S (2 * (m - 1 - i)))%nat)
              * q_fact (2 * m))
             (q_fact (S (2 * i))%nat * q_fact (S (2 * (m - 1 - i)))%nat) Hd0).
    rewrite Hbr2. symmetry.
    transitivity (q_fact (2 * m)
                  * (q_fact (S (2 * i))%nat * q_fact (S (2 * (m - 1 - i)))%nat
                     * / (q_fact (S (2 * i))%nat
                          * q_fact (S (2 * (m - 1 - i)))%nat)))%Q.
    - unfold Qdiv. ring.
    - rewrite (Qmult_inv_r (q_fact (S (2 * i))%nat
                              * q_fact (S (2 * (m - 1 - i)))%nat) Hd0).
      ring. }
  rewrite (piLe_qeq_mul_div_r _ _ _ HD0 Hkey).
  unfold Qdiv. ring.
Qed.

(* ================= Section 4. Group gamma: the cos double-angle row identity ================= *)

(** Even row-piece denominator cancellation: [c_t·c_{m-t}·(2m)! == (-1)^m·x^(2m)·C(2m,2t)] for [t <= m]. *)
Lemma piLe_rowpiece_cc : forall (m t : nat) (x : Q), (t <= m)%nat ->
  cos_term t x * cos_term (m - t)%nat x * q_fact (2 * m)%nat
  == q_pow (-1)%Q m * q_pow x (2 * m)%nat * bpa_binom (2 * m)%nat (2 * t)%nat.
Proof.
  intros m t x Htm.
  assert (Hbm : (2 * t <= 2 * m)%nat) by (apply Nat.mul_le_mono_l; exact Htm).
  assert (Hbr := piLsb_bpa_bridge (2 * m)%nat (2 * t)%nat Hbm).
  replace (2 * m - 2 * t)%nat with (2 * (m - t))%nat in Hbr by lia.
  assert (Hs1 : q_pow (-1)%Q t * q_pow (-1)%Q (m - t)%nat == q_pow (-1)%Q m).
  { replace (q_pow (-1)%Q m) with (q_pow (-1)%Q (t + (m - t))%nat)
      by (f_equal; lia).
    rewrite (lw0_q_pow_add (-1)%Q t (m - t)%nat). reflexivity. }
  assert (Hs2 : q_pow x (2 * t)%nat * q_pow x (2 * (m - t))%nat == q_pow x (2 * m)%nat).
  { replace (q_pow x (2 * m)%nat) with (q_pow x (2 * t + (2 * (m - t)))%nat)
      by (f_equal; lia).
    rewrite (lw0_q_pow_add x (2 * t)%nat (2 * (m - t))%nat). reflexivity. }
  assert (Hne : ~ (q_fact (2 * t)%nat * q_fact (2 * (m - t))%nat == 0)%Q)
    by (apply piLe_qfact_pair_neq0).
  assert (Hmul : cos_term t x * cos_term (m - t)%nat x * q_fact (2 * m)%nat
                 * (q_fact (2 * t)%nat * q_fact (2 * (m - t))%nat)
                 == q_pow (-1)%Q m * q_pow x (2 * m)%nat
                    * bpa_binom (2 * m)%nat (2 * t)%nat
                    * (q_fact (2 * t)%nat * q_fact (2 * (m - t))%nat)).
  { unfold cos_term, Qdiv.
    transitivity (q_pow (-1)%Q t * q_pow (-1)%Q (m - t)%nat
                  * (q_pow x (2 * t)%nat * q_pow x (2 * (m - t))%nat)
                  * q_fact (2 * m)%nat
                  * ((q_fact (2 * t)%nat * / q_fact (2 * t)%nat)
                     * (q_fact (2 * (m - t))%nat
                        * / q_fact (2 * (m - t))%nat)))%Q.
    - ring.
    - rewrite (Qmult_inv_r (q_fact (2 * t)%nat)
                 (q_neq_of_lt _ (q_fact_pos (2 * t)%nat))).
      rewrite (Qmult_inv_r (q_fact (2 * (m - t))%nat)
                 (q_neq_of_lt _ (q_fact_pos (2 * (m - t))%nat))).
      rewrite Hs1, Hs2, <- Hbr. ring. }
  apply (piLrowB_qeq_cancel_l
           (cos_term t x * cos_term (m - t)%nat x * q_fact (2 * m)%nat)
           (q_pow (-1)%Q m * q_pow x (2 * m)%nat
            * bpa_binom (2 * m)%nat (2 * t)%nat)
           (q_fact (2 * t)%nat * q_fact (2 * (m - t))%nat) Hne).
  exact Hmul.
Qed.

(** Odd row-piece denominator cancellation: [s_t·s_{m-1-t}·(2m)! == (-1)^(m-1)·x^(2m)·C(2m,2t+1)] for [t < m]. *)
Lemma piLe_rowpiece_ss : forall (m t : nat) (x : Q), (t < m)%nat ->
  sin_term t x * sin_term (m - 1 - t)%nat x * q_fact (2 * m)%nat
  == q_pow (-1)%Q (m - 1)%nat * q_pow x (2 * m)%nat
     * bpa_binom (2 * m)%nat (S (2 * t))%nat.
Proof.
  intros m t x Htm.
  assert (Hbm : (S (2 * t) <= 2 * m)%nat) by lia.
  assert (Hbr := piLsb_bpa_bridge (2 * m)%nat (S (2 * t))%nat Hbm).
  replace (2 * m - S (2 * t))%nat with (S (2 * (m - 1 - t)))%nat in Hbr by lia.
  assert (Hs1 : q_pow (-1)%Q t * q_pow (-1)%Q (m - 1 - t)%nat
                == q_pow (-1)%Q (m - 1)%nat).
  { replace (q_pow (-1)%Q (m - 1)%nat)
      with (q_pow (-1)%Q (t + (m - 1 - t))%nat) by (f_equal; lia).
    rewrite (lw0_q_pow_add (-1)%Q t (m - 1 - t)%nat). reflexivity. }
  assert (Hs2 : q_pow x (S (2 * t))%nat * q_pow x (S (2 * (m - 1 - t)))%nat
                == q_pow x (2 * m)%nat).
  { replace (q_pow x (2 * m)%nat)
      with (q_pow x (S (2 * t) + S (2 * (m - 1 - t)))%nat) by (f_equal; lia).
    rewrite (lw0_q_pow_add x (S (2 * t))%nat (S (2 * (m - 1 - t)))%nat).
    reflexivity. }
  assert (Hne : ~ (q_fact (S (2 * t))%nat * q_fact (S (2 * (m - 1 - t)))%nat == 0)%Q)
    by (apply piLe_qfact_pair_neq0).
  assert (Hmul : sin_term t x * sin_term (m - 1 - t)%nat x * q_fact (2 * m)%nat
                 * (q_fact (S (2 * t))%nat * q_fact (S (2 * (m - 1 - t)))%nat)
                 == q_pow (-1)%Q (m - 1)%nat * q_pow x (2 * m)%nat
                    * bpa_binom (2 * m)%nat (S (2 * t))%nat
                    * (q_fact (S (2 * t))%nat * q_fact (S (2 * (m - 1 - t)))%nat)).
  { unfold sin_term, Qdiv.
    transitivity (q_pow (-1)%Q t * q_pow (-1)%Q (m - 1 - t)%nat
                  * (q_pow x (S (2 * t))%nat * q_pow x (S (2 * (m - 1 - t)))%nat)
                  * q_fact (2 * m)%nat
                  * ((q_fact (S (2 * t))%nat * / q_fact (S (2 * t))%nat)
                     * (q_fact (S (2 * (m - 1 - t)))%nat
                        * / q_fact (S (2 * (m - 1 - t)))%nat)))%Q.
    - ring.
    - rewrite (Qmult_inv_r (q_fact (S (2 * t))%nat)
                 (q_neq_of_lt _ (q_fact_pos (S (2 * t))%nat))).
      rewrite (Qmult_inv_r (q_fact (S (2 * (m - 1 - t)))%nat)
                 (q_neq_of_lt _ (q_fact_pos (S (2 * (m - 1 - t)))%nat))).
      rewrite Hs1, Hs2, <- Hbr. ring. }
  apply (piLrowB_qeq_cancel_l
           (sin_term t x * sin_term (m - 1 - t)%nat x * q_fact (2 * m)%nat)
           (q_pow (-1)%Q (m - 1)%nat * q_pow x (2 * m)%nat
            * bpa_binom (2 * m)%nat (S (2 * t))%nat)
           (q_fact (S (2 * t))%nat * q_fact (S (2 * (m - 1 - t)))%nat) Hne).
  exact Hmul.
Qed.

(** The cos double-angle row identity: [Σ_{i<=N} c_i c_{N-i} - Σ_{i<N} s_i s_{N-1-i} == cos_term N (2x)] for [N >= 1]; the closing steps are the row-piece denominator cancellation, the even-odd half-row values, and the power-of-2 split. *)

Lemma piLe_rowC_cross : forall (N : nat) (x : Q), (1 <= N)%nat ->
  piLsb_sumR (fun i => cos_term i x * cos_term (N - i)%nat x) (S N)
  - piLsb_sumR (fun i => sin_term i x * sin_term (N - 1 - i)%nat x) N
  == cos_term N (2 * x)%Q.
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
  assert (Hpx : q_pow (2 * x) (2 * N)%nat
                == q_pow 2%Q (2 * N)%nat * q_pow x (2 * N)%nat)
    by (rewrite (lw0_q_pow_mult 2%Q x (2 * N)%nat); reflexivity).
  assert (Hsg : q_pow (-1)%Q (N - 1)%nat == - q_pow (-1)%Q N).
  { replace (q_pow (-1)%Q N) with (q_pow (-1)%Q (S (N - 1))%nat)
      by (f_equal; lia).
    rewrite q_pow_succ. ring. }
  unfold cos_term, Qdiv.
  rewrite Hpx, Hsg. ring.
Qed.

(* ================= Section 7. Row-sum tools and the 1/4 geometric sum ================= *)

(** Left multiplication in [Q]: [0 <= z] and [x <= y] imply [z*x <= z*y]. *)
Lemma piLe_qmult_le_l : forall z x y : Q,
  Qle 0 z -> Qle x y -> Qle (z * x) (z * y).
Proof.
  intros z x y Hz Hxy.
  rewrite (Qmult_comm z x), (Qmult_comm z y).
  apply (Qmult_le_compat_r x y z Hxy Hz).
Qed.

(** Nonnegative products: [0 <= x] and [0 <= y] imply [0 <= x*y]. *)
Lemma piLe_qmult_nonneg_r : forall x y : Q,
  Qle 0 x -> Qle 0 y -> Qle 0 (x * y).
Proof.
  intros x y Hx Hy. apply (Qle_trans _ (0 * y)%Q).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply (Qmult_le_compat_r 0 x y Hx Hy).
Qed.

(** Right subtraction bound: [0 <= x] implies [a - x <= a]. *)
Lemma piLe_qle_sub_r : forall a x : Q, Qle 0 x -> Qle (a - x) a.
Proof.
  intros a x Hx.
  apply (Qle_trans _ ((a - x) + x)%Q).
  - apply (Qle_trans (a - x) ((a - x) + 0)%Q ((a - x) + x)%Q).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (Qplus_le_compat (a - x) (a - x) 0%Q x); [apply Qle_refl | exact Hx].
  - assert (Heq : (a - x) + x == a + 0) by ring.
    rewrite Heq, Qplus_0_r. apply Qle_refl.
Qed.

(** Antitonicity of subtraction: [y <= x] implies [a - x <= a - y]. *)
Lemma piLe_qle_sub_l : forall a x y : Q, Qle y x -> Qle (a - x) (a - y).
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

(** Nonnegative embedding: [0 <= (Z.of_nat n # 1)]. *)
Lemma piLe_inject_nonneg : forall n : nat, Qle 0 (Z.of_nat n # 1).
Proof.
  intros n. apply (Qle_trans 0 (Z.of_nat 0 # 1) (Z.of_nat n # 1)).
  - apply Qle_refl.
  - apply piLe_inject_le. apply Nat.le_0_l.
Qed.

(** Monotone product of four nonnegative factors: [0<=a], [a<=b], [0<=c], [c<=d] imply [a*c <= b*d]. *)
Lemma piLe_qmult_le_nonneg4 : forall a b c d : Q,
  Qle 0 a -> Qle a b -> Qle 0 c -> Qle c d -> Qle (a * c) (b * d).
Proof.
  intros a b c d Ha Hab Hc Hcd.
  apply (Qle_trans _ (b * c)%Q).
  - apply (Qmult_le_compat_r a b c Hab Hc).
  - rewrite (Qmult_comm b c), (Qmult_comm b d).
    apply (Qmult_le_compat_r c d b Hcd (Qle_trans 0 a b Ha Hab)).
Qed.

(** Double-sum expansion of a product of row sums: [sum_i f i * sum_j g j == sum_i sum_j f i * g j]. *)
Lemma piLe_sumR_prod : forall (n1 n2 : nat) (f g : nat -> Q),
  piLsb_sumR f n1 * piLsb_sumR g n2
  == piLsb_sumR (fun i => piLsb_sumR (fun j => f i * g j) n2) n1.
Proof.
  intros n1 n2 f g.
  rewrite (piLrowB_row_scal_r (piLsb_sumR g n2) f n1).
  apply piLsb_sumR_ext. intros i _.
  rewrite (Qmult_comm (f i) (piLsb_sumR g n2)).
  rewrite (piLrowB_row_scal_r (f i) g n2).
  apply piLsb_sumR_ext. intros j _. apply Qmult_comm.
Qed.

(** Extending the row sum by one entry on the right: [sum_{u<n} h (S u) == sum_{w<S n} h w] (with [h 0 == 0]). *)
Lemma piLe_sumR_shift_succ : forall (n : nat) (h : nat -> Q),
  h 0%nat == 0%Q ->
  piLsb_sumR (fun w => h (S w)) n == piLsb_sumR h (S n).
Proof.
  intros n h H0. induction n as [| n IH].
  - cbn [piLsb_sumR]. rewrite H0. ring.
  - rewrite (piLsb_sumR_snoc (fun w => h (S w)) n).
    rewrite (piLsb_sumR_snoc h (S n)).
    rewrite IH. cbv beta. ring.
Qed.

(** One-term row sum: [sum_{i<1} f i == f 0]. *)
Lemma piLe_sumR_1 : forall (f : nat -> Q), piLsb_sumR f 1%nat == f 0%nat.
Proof.
  intros f. cbn [piLsb_sumR]. cbv beta. ring.
Qed.

(** Full-triangle anti-diagonal regrouping: [sum_{u<K} sum_{v<K-u} F u v == sum_{w<K} sum_{v<S w} F v (w-v)]. *)
Lemma piLe_sumR_flatten_full : forall (K : nat) (F : nat -> nat -> Q),
  piLsb_sumR (fun u => piLsb_sumR (fun v => F u v) (K - u)%nat) K
  == piLsb_sumR (fun w => piLsb_sumR (fun v => F v (w - v)%nat) (S w)) K.
Proof.
  intros K F. induction K as [| K IH].
  - reflexivity.
  - assert (Hrowext : forall u : nat, (u < K)%nat ->
      piLsb_sumR (fun v => F u v) (K - u)%nat + F u (K - u)%nat
      == piLsb_sumR (fun v => F u v) (S K - u)%nat).
    { intros u Hu. replace (S K - u)%nat with (S (K - u))%nat by lia.
      rewrite piLsb_sumR_snoc. cbv beta. apply Qeq_refl. }
    assert (Hl : piLsb_sumR (fun u => piLsb_sumR (fun v => F u v) (S K - u)%nat) (S K)
                 == piLsb_sumR (fun u => piLsb_sumR (fun v => F u v) (K - u)%nat) K
                    + piLsb_sumR (fun u => F u (K - u)%nat) K
                    + F K 0%nat).
    { rewrite (piLsb_sumR_snoc (fun u => piLsb_sumR (fun v => F u v) (S K - u)%nat) K).
      cbv beta.
      rewrite (piLsb_sumR_ext
                 (fun u => piLsb_sumR (fun v => F u v) (S K - u)%nat)
                 (fun u => piLsb_sumR (fun v => F u v) (K - u)%nat + F u (K - u)%nat)
                 K (fun u Hu => eq_sym (Hrowext u Hu))).
      rewrite <- (piLsb_sumR_plus (fun u => piLsb_sumR (fun v => F u v) (K - u)%nat)
                    (fun u => F u (K - u)%nat) K).
      replace (S K - K)%nat with 1%nat by lia.
      rewrite (piLe_sumR_1 (fun v => F K v)).
      apply Qeq_refl. }
    rewrite Hl.
    rewrite (piLsb_sumR_snoc (fun w => piLsb_sumR (fun v => F v (w - v)%nat) (S w)) K).
    cbv beta.
    rewrite (piLsb_sumR_snoc (fun v => F v (K - v)%nat) K).
    cbv beta.
    replace (K - K)%nat with 0%nat by lia.
    rewrite IH. ring.
Qed.

(** Row-by-row splitting of the square array: at the per-row split point [a i], the square double sum splits into a triangle and a remainder band. *)
Lemma piLe_sumR_square_split_gen : forall (N : nat) (a p : nat -> nat)
                                          (F : nat -> nat -> Q),
  (forall i : nat, (i < N)%nat -> (a i + p i)%nat = N) ->
  piLsb_sumR (fun i => piLsb_sumR (fun j => F i j) N) N
  == piLsb_sumR (fun i => piLsb_sumR (fun j => F i j) (a i)) N
     + piLsb_sumR (fun i => piLsb_sumR (fun u => F i (a i + u)%nat) (p i)) N.
Proof.
  intros N a p F Hap.
  transitivity (piLsb_sumR (fun i => piLsb_sumR (fun j => F i j) (a i)
                                    + piLsb_sumR (fun u => F i (a i + u)%nat) (p i)) N).
  { apply piLsb_sumR_ext. intros i Hi.
    rewrite <- (Hap i Hi).
    rewrite (piLe_sumR_split (fun j => F i j) (a i) (p i)).
    apply Qeq_refl. }
  rewrite (piLsb_sumR_plus (fun i => piLsb_sumR (fun j => F i j) (a i))
             (fun i => piLsb_sumR (fun u => F i (a i + u)%nat) (p i)) N).
  apply Qeq_refl.
Qed.

(** Empty row sum: [sum_{i<0} f i == 0]. *)
Lemma piLe_sumR_0 : forall (f : nat -> Q), piLsb_sumR f 0%nat == 0%Q.
Proof.
  intros f. cbn [piLsb_sumR]. ring.
Qed.

(** Upper-triangle transposition: [sum_{i<S K} sum_{u<i} G i u == sum_{u<K} sum_{i'<K-u} G (S(u+i')) u]. *)
Lemma piLe_sumR_trapswap_lt : forall (K : nat) (G : nat -> nat -> Q),
  piLsb_sumR (fun i => piLsb_sumR (fun u => G i u) i) (S K)
  == piLsb_sumR (fun u => piLsb_sumR (fun i => G (S (u + i)%nat) u) (K - u)%nat) (S K).
Proof.
  intros K G. induction K as [| K IH].
  - cbn [piLsb_sumR]. cbv beta. cbn [piLsb_sumR]. cbv beta. reflexivity.
  - rewrite (piLsb_sumR_snoc (fun i => piLsb_sumR (fun u => G i u) i) (S K)).
    cbv beta.
    rewrite (piLsb_sumR_snoc
               (fun u => piLsb_sumR (fun i => G (S (u + i)%nat) u) (S K - u)%nat) (S K)).
    cbv beta.
    replace (S K - S K)%nat with 0%nat by lia.
    rewrite (piLe_sumR_0 (fun i => G (S (S K + i)%nat) (S K))).
    assert (Hgrow : piLsb_sumR
                      (fun u => piLsb_sumR (fun i => G (S (u + i)%nat) u) (S K - u)%nat)
                      (S K)
                    == piLsb_sumR
                         (fun u => piLsb_sumR (fun i => G (S (u + i)%nat) u) (K - u)%nat)
                         (S K)
                       + piLsb_sumR (fun u => G (S K) u) (S K)).
    { rewrite <- (piLsb_sumR_plus
                    (fun u => piLsb_sumR (fun i => G (S (u + i)%nat) u) (K - u)%nat)
                    (fun u => G (S K) u) (S K)).
      apply piLsb_sumR_ext. intros u Hu.
      replace (S K - u)%nat with (S (K - u))%nat by lia.
      rewrite piLsb_sumR_snoc. cbv beta.
      replace (S (u + (K - u)))%nat with (S K)%nat by lia.
      apply Qeq_refl. }
    rewrite Hgrow. rewrite IH. cbv beta. ring.
Qed.

(* ================= Section 8. The band machine: quarter-step descent for the [t'] terms and the geometric tail bound ================= *)

(** The 1/4 geometric-sum identity: [sum_{i<n} (1/4)^i + (4/3)(1/4)^n == 4/3]. *)
Lemma piLe_quarter_sum_identity : forall n : nat,
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

(** Quarter-step descent for the [t'] terms: [t'_{m+1} <= (1/4) t'_m] for [0 <= B] and [2*ceil(B) <= m]. *)
Lemma piLe_tc_term_quarter_step : forall (B : Q) (m : nat),
  Qle 0 B -> (2 * Z.to_nat (Qceiling B) <= m)%nat ->
  Qle (piLe_tc_term (Datatypes.S m) B) ((1 # 4)%Q * piLe_tc_term m B).
Proof.
  intros B m H0B Hm.
  assert (H02 : Qle 0 2%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (HBceil : Qle B (Z.of_nat (Z.to_nat (Qceiling B)) # 1))
    by exact (QleT'_to_Qle B (d3p_inject_nat (Z.to_nat (Qceiling B)))
                (d3p_inject_ceiling_ge B H0B)).
  assert (HBB : Qle (B * B)
                  ((Z.of_nat (Z.to_nat (Qceiling B)) # 1)
                   * (Z.of_nat (Z.to_nat (Qceiling B)) # 1))).
  { exact (piLe_qmult_le_nonneg4 B (Z.of_nat (Z.to_nat (Qceiling B)) # 1)
             B (Z.of_nat (Z.to_nat (Qceiling B)) # 1)
             H0B HBceil H0B HBceil). }
  assert (Hreg : (2 * B) * (2 * B) == 4%Q * (B * B)) by ring.
  assert (Hs16 : 4%Q * ((2 * B) * (2 * B)) == 16%Q * (B * B))
    by (rewrite Hreg; ring).
  assert (H016 : Qle 0 16%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (Hstep1 : Qle (16%Q * (B * B))
                     (16%Q * ((Z.of_nat (Z.to_nat (Qceiling B)) # 1)
                              * (Z.of_nat (Z.to_nat (Qceiling B)) # 1)))).
  { exact (piLe_qmult_le_nonneg4 16%Q 16%Q (B * B)
             ((Z.of_nat (Z.to_nat (Qceiling B)) # 1)
              * (Z.of_nat (Z.to_nat (Qceiling B)) # 1))
             H016 (Qle_refl 16%Q) (piLe_qmult_nonneg_r B B H0B H0B) HBB). }
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
                     (Z.of_nat (Datatypes.S (2 * m)) # 1))
    by (apply piLe_inject_le; lia).
  assert (H4i2 : Qle (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1)
                     (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))
    by (apply piLe_inject_le; lia).
  assert (Hnn4 : Qle 0 (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1))
    by (apply piLe_inject_nonneg).
  assert (HR : Qle (4%Q * ((2 * B) * (2 * B)))
                   ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                    * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))).
  { rewrite Hs16.
    apply (Qle_trans _ (16%Q * ((Z.of_nat (Z.to_nat (Qceiling B)) # 1)
                                * (Z.of_nat (Z.to_nat (Qceiling B)) # 1)))).
    - exact Hstep1.
    - rewrite Hconv, <- H4q.
      exact (piLe_qmult_le_nonneg4
               (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1)
               (Z.of_nat (Datatypes.S (2 * m)) # 1)
               (Z.of_nat (4 * Z.to_nat (Qceiling B)) # 1)
               (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
               Hnn4 H4i1 Hnn4 H4i2). }
  assert (HDne : ~ (((Z.of_nat (Datatypes.S (2 * m)) # 1)
                     * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q == 0)).
  { intro H0.
    exact (q_neq_of_lt
             ((Z.of_nat (Datatypes.S (2 * m)) # 1)
              * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q
             (Qmult_lt_0_compat
                (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
                (Z.of_nat (Datatypes.S (2 * m)) # 1)
                (piLe_inject_pos (Datatypes.S (2 * m)))
                (piLe_inject_pos (2 * m))) H0). }
  assert (H0D : Qle 0 (/ ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                          * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)).
  { apply (Qlt_le_weak 0 _).
    apply Qinv_lt_0_compat.
    apply Qmult_lt_0_compat; apply piLe_inject_pos. }
  assert (HHD : Qle (4%Q * ((2 * B) * (2 * B)
                            * / ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                                 * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q))
                    1%Q).
  { assert (Hreg2 : 4%Q * ((2 * B) * (2 * B)
                            * / ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                                 * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)
                    == (4%Q * ((2 * B) * (2 * B)))
                       * / ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                            * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q) by ring.
    rewrite Hreg2, <- (Qmult_inv_r ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                                    * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q HDne).
    apply (Qmult_le_compat_r (4%Q * ((2 * B) * (2 * B)))
               ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q
               (/ ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                  * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q) HR H0D). }
  assert (H0q4 : Qle 0 (1 # 4)%Q) by (unfold Qle; cbn [Qnum Qden]; lia).
  assert (Hcore : Qle ((2 * B) * (2 * B)
                       * / ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                            * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)
                      (1 # 4)%Q).
  { assert (Hq1 : (2 * B) * (2 * B)
                  * / ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                       * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q
                  == (1 # 4)%Q * (4%Q * ((2 * B) * (2 * B)
                                          * / ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                                               * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)))
      by ring.
    rewrite Hq1.
    apply (Qle_trans _ ((1 # 4)%Q * 1%Q)%Q).
    + apply piLe_qmult_le_l; [exact H0q4 | exact HHD].
    + assert (Hc14 : (1 # 4)%Q * 1%Q == (1 # 4)%Q) by ring.
      rewrite Hc14. apply Qle_refl. }
  assert (HneZF : ~ ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
                     * q_fact (Datatypes.S (2 * m))%nat == 0)%Q).
  { apply q_neq_of_lt. apply Qmult_lt_0_compat;
      [apply piLe_inject_pos | apply q_fact_pos]. }
  assert (Hratio : piLe_tc_term (Datatypes.S m) B
    == (2 * B) * (2 * B)
       * / ((Z.of_nat (Datatypes.S (2 * m)) # 1)
            * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q
       * piLe_tc_term m B).
  { unfold piLe_tc_term at 1. unfold Qdiv.
    replace (2 * Datatypes.S m)%nat
      with (Datatypes.S (Datatypes.S (2 * m)))%nat by lia.
    rewrite (q_pow_succ (2 * B) (Datatypes.S (2 * m))).
    rewrite (q_pow_succ (2 * B) (2 * m)).
    rewrite (q_fact_succ (Datatypes.S (2 * m))).
    rewrite (q_fact_succ (2 * m)).
    rewrite <- (piLe_qinv_distr
                  (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
                  ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                   * q_fact (2 * m)%nat)
                  (piLe_inject_neq0 (Datatypes.S (2 * m)))
                  (q_neq_of_lt ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                                * q_fact (2 * m)%nat)
                     (Qmult_lt_0_compat (Z.of_nat (Datatypes.S (2 * m)) # 1)
                        (q_fact (2 * m)%nat)
                        (piLe_inject_pos (2 * m)) (q_fact_pos (2 * m))))).
    rewrite <- (piLe_qinv_distr
                  (Z.of_nat (Datatypes.S (2 * m)) # 1)
                  (q_fact (2 * m)%nat)
                  (piLe_inject_neq0 (2 * m))
                  (piLrowB_qfact_neq0 (2 * m))).
    unfold piLe_tc_term. unfold Qdiv.
    rewrite <- (piLe_qinv_distr
                  (Z.of_nat (Datatypes.S (2 * m)) # 1)
                  (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1)
                  (piLe_inject_neq0 (2 * m))
                  (piLe_inject_neq0 (Datatypes.S (2 * m)))).
    ring. }
  assert (Htm : piLe_tc_term m B
                == q_pow (2 * B) (2 * m)%nat * / q_fact (2 * m)%nat)
    by (unfold piLe_tc_term, Qdiv; reflexivity).
  assert (H0PF : Qle 0 (q_pow (2 * B) (2 * m)%nat * / q_fact (2 * m)%nat)).
  { apply (Qle_trans _ ((0 * / q_fact (2 * m))%Q)).
    - rewrite Qmult_0_l. apply Qle_refl.
    - exact (piLe_qmult_le_nonneg4 0%Q (q_pow (2 * B) (2 * m)%nat)
               (/ q_fact (2 * m)%nat) (/ q_fact (2 * m)%nat)
               (Qle_refl 0%Q) (q_pow_nonneg (2 * B) (2 * m)%nat
                                 (piLe_qmult_nonneg_r 2%Q B H02 H0B))
               (Qlt_le_weak 0%Q (/ q_fact (2 * m)%nat)
                  (Qinv_lt_0_compat (q_fact (2 * m)%nat) (q_fact_pos (2 * m))))
               (Qle_refl (/ q_fact (2 * m)%nat))). }
  rewrite Hratio, Htm.
  apply (Qmult_le_compat_r ((2 * B) * (2 * B)
                            * / ((Z.of_nat (Datatypes.S (2 * m)) # 1)
                                 * (Z.of_nat (Datatypes.S (Datatypes.S (2 * m))) # 1))%Q)
             (1 # 4)%Q
             (q_pow (2 * B) (2 * m)%nat * / q_fact (2 * m)%nat) Hcore H0PF).
Qed.

(** Chain form for the [t'] terms: [t'_{m+p} <= (1/4)^p t'_m]. *)
Lemma piLe_tc_term_quarter_chain : forall (B : Q) (m p : nat),
  Qle 0 B -> (2 * Z.to_nat (Qceiling B) <= m)%nat ->
  Qle (piLe_tc_term (m + p)%nat B) (q_pow (1 # 4)%Q p * piLe_tc_term m B).
Proof.
  intros B m p H0B Hm. induction p as [| p IH].
  - replace (m + 0)%nat with m%nat by lia.
    cbn [q_pow]. rewrite Qmult_1_l. apply Qle_refl.
  - replace (m + Datatypes.S p)%nat with (Datatypes.S (m + p))%nat by lia.
    apply (Qle_trans _ ((1 # 4)%Q * piLe_tc_term (m + p) B)).
    + apply (piLe_tc_term_quarter_step B (m + p)%nat H0B).
      apply (Nat.le_trans _ m); [exact Hm | lia].
    + rewrite (q_pow_succ (1 # 4)%Q p).
      apply (Qle_trans _ ((1 # 4)%Q * (q_pow (1 # 4)%Q p * piLe_tc_term m B))).
      * apply piLe_qmult_le_l; [(unfold Qle; cbn [Qnum Qden]; lia) | exact IH].
      * rewrite Qmult_assoc. apply Qle_refl.
Qed.

(** Geometric tail bound: [band_bound k B <= (4/3) t'_{k+1}(B)] for [0 <= B] and [2*ceil(B) < k]. *)
Lemma piLe_band_bound_geometric : forall (B : Q) (k : nat),
  Qle 0 B -> (2 * Z.to_nat (Qceiling B) < k)%nat ->
  Qle (piLe_band_bound k B) ((4 # 3)%Q * piLe_tc_term (Datatypes.S k) B).
Proof.
  intros B k H0B Hk. unfold piLe_band_bound.
  apply (Qle_trans _
           (piLsb_sumR (fun u => q_pow (1 # 4)%Q u * piLe_tc_term (Datatypes.S k) B)
                       (S (S k)))).
  - apply piLe_sumR_le. intros u Hu.
    apply (piLe_tc_term_quarter_chain B (Datatypes.S k) u H0B). lia.
  - rewrite <- (piLrowB_row_scal_r (piLe_tc_term (Datatypes.S k) B)
                  (fun u => q_pow (1 # 4)%Q u) (S (S k))).
    assert (Hsumle : Qle (piLsb_sumR (fun u => q_pow (1 # 4)%Q u) (S (S k)))
                       (4 # 3)%Q).
    { pose proof (piLe_quarter_sum_identity (S (S k))) as Hid.
      assert (Hqpos : Qle 0 ((4 # 3)%Q * q_pow (1 # 4)%Q (S (S k)))).
      { apply piLe_qmult_nonneg_r.
        - unfold Qle; cbn [Qnum Qden]; lia.
        - apply q_pow_nonneg. unfold Qle; cbn [Qnum Qden]; lia. }
      assert (H2 : piLsb_sumR (fun u => q_pow (1 # 4)%Q u) (S (S k))
                   == (4 # 3)%Q - (4 # 3)%Q * q_pow (1 # 4)%Q (S (S k))).
      { transitivity (piLsb_sumR (fun u => q_pow (1 # 4)%Q u) (S (S k))
                      + (4 # 3)%Q * q_pow (1 # 4)%Q (S (S k))
                      - (4 # 3)%Q * q_pow (1 # 4)%Q (S (S k))).
        - ring.
        - rewrite Hid. ring. }
      rewrite H2. apply piLe_qle_sub_r. exact Hqpos. }
    assert (Htpos : Qle 0 (piLe_tc_term (Datatypes.S k) B))
      by (apply piLe_tc_term_nonneg; exact H0B).
    apply (Qmult_le_compat_r (piLsb_sumR (fun u => q_pow (1 # 4)%Q u) (S (S k)))
               (4 # 3)%Q (piLe_tc_term (Datatypes.S k) B) Hsumle Htpos).
Qed.

(** Truncation-length selection: there is a [j] such that [band_bound k B < dt] whenever [k >= j]. *)
Lemma piLe_band_small : forall (B dt : Q),
  Qlt 0 B -> Qlt 0 dt ->
  sigT (fun j : nat => forall k : nat, (j <= k)%nat -> Qlt (piLe_band_bound k B) dt).
Proof.
  intros B dt HB Hdt.
  assert (HBpos : Qle 0 B) by (apply (Qlt_le_weak 0%Q B); exact HB).
  assert (Hc : Qlt 0 ((4 # 3)%Q
                      * piLe_tc_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)).
  { apply Qmult_lt_0_compat.
    - unfold Qlt; cbn [Qnum Qden]; lia.
    - unfold piLe_tc_term. apply Qmult_lt_0_compat.
      + apply piLe_q_pow_pos. apply Qmult_lt_0_compat;
          [unfold Qlt; cbn [Qnum Qden]; lia | exact HB].
      + apply Qinv_lt_0_compat. apply q_fact_pos. }
  destruct (d3p_quarter_pow_lt ((4 # 3)%Q
                                * piLe_tc_term
                                    (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)
                  dt Hc Hdt) as [d0 Hd0].
  exists (Datatypes.S (2 * Z.to_nat (Qceiling B)) + d0)%nat.
  intros k Hk.
  apply (Qle_lt_trans _
           (((4 # 3)%Q
             * piLe_tc_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)
            * q_pow (1 # 4)%Q d0)).
  - apply (Qle_trans _
             (((4 # 3)%Q
               * piLe_tc_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)
              * q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))).
    + apply (Qle_trans _
               ((4 # 3)%Q * piLe_tc_term (Datatypes.S k) B)).
      * apply piLe_band_bound_geometric; [exact HBpos | lia].
      * assert (Hpre2 : (2 * Z.to_nat (Qceiling B) <= k)%nat) by lia.
        assert (Hq : Qle (piLe_tc_term (Datatypes.S k) B)
                         (piLe_tc_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B
                          * q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))).
        { apply (Qle_trans _ ((1 # 4)%Q * piLe_tc_term k B)).
          - apply (piLe_tc_term_quarter_step B k HBpos Hpre2).
          - apply (Qle_trans _
                     ((1 # 4)%Q
                      * (q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B)))
                         * piLe_tc_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B))).
            + apply piLe_qmult_le_l.
              * unfold Qle; cbn [Qnum Qden]; lia.
              * pose proof (piLe_tc_term_quarter_chain B
                              (Datatypes.S (2 * Z.to_nat (Qceiling B)))
                              (k - Datatypes.S (2 * Z.to_nat (Qceiling B)))
                              HBpos (Nat.le_succ_diag_r _)) as Hqc.
                replace (Datatypes.S (2 * Z.to_nat (Qceiling B))
                         + (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))%nat
                  with k%nat in Hqc by lia.
                exact Hqc.
            + apply (Qle_trans _ (1%Q * (q_pow (1 # 4)%Q
                                            (k - Datatypes.S (2 * Z.to_nat (Qceiling B)))
                                         * piLe_tc_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B))).
              * apply (Qmult_le_compat_r (1 # 4)%Q 1%Q
                           (q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B)))
                            * piLe_tc_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B));
                   [unfold Qle; cbn [Qnum Qden]; lia
                   | apply piLe_qmult_nonneg_r;
                       [apply q_pow_nonneg; unfold Qle; cbn [Qnum Qden]; lia
                       | apply piLe_tc_term_nonneg; exact HBpos]].
              * rewrite Qmult_1_l,
                  (Qmult_comm (q_pow (1 # 4)%Q
                                (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))
                              (piLe_tc_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)).
                apply Qle_refl. }
        rewrite <- (Qmult_assoc (4 # 3)%Q
                      (piLe_tc_term (Datatypes.S (2 * Z.to_nat (Qceiling B))) B)
                      (q_pow (1 # 4)%Q (k - Datatypes.S (2 * Z.to_nat (Qceiling B))))).
        apply piLe_qmult_le_l;
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
               | rewrite sc_q_pow_one; apply Qle_refl]
            | apply q_pow_nonneg; unfold Qle; cbn [Qnum Qden]; lia].
        - rewrite Qmult_1_l. apply Qle_refl. }
      apply piLe_qmult_le_l.
      * apply piLe_qmult_nonneg_r.
        -- unfold Qle; cbn [Qnum Qden]; lia.
        -- apply piLe_tc_term_nonneg; exact HBpos.
      * exact Hp.
  - exact Hd0.
Qed.

(* ================= Section 12. Weak triangular transposition and the row-sum form of partial sums (continuation) ================= *)

(** Weak triangular transposition: [sum_{i<S K} sum_{u<S i} G i u == sum_{u<S K} sum_{i'<S(K-u)} G (u+i') u]. *)
Lemma piLe_sumR_trapswap_le : forall (K : nat) (G : nat -> nat -> Q),
  piLsb_sumR (fun i => piLsb_sumR (fun u => G i u) (S i)) (S K)
  == piLsb_sumR (fun u => piLsb_sumR (fun i => G (u + i)%nat u) (S (K - u))%nat) (S K).
Proof.
  intros K G. induction K as [| K IH].
  - cbn [piLsb_sumR]. cbv beta. cbn [piLsb_sumR]. cbv beta. reflexivity.
  - rewrite (piLsb_sumR_snoc (fun i => piLsb_sumR (fun u => G i u) (S i)) (S K)).
    cbv beta.
    rewrite (piLsb_sumR_snoc (fun u => G (S K) u) (S K)).
    cbv beta.
    rewrite (piLsb_sumR_snoc
               (fun u => piLsb_sumR (fun i => G (u + i)%nat u) (S (S K - u))%nat) (S K)).
    cbv beta.
    replace (S (S K - S K))%nat with 1%nat by lia.
    rewrite (piLe_sumR_1 (fun i => G (S K + i)%nat (S K))).
    cbv beta.
    replace (S K + 0)%nat with (S K)%nat by lia.
    assert (Hgrow : piLsb_sumR
                      (fun u => piLsb_sumR (fun i => G (u + i)%nat u) (S (S K - u))%nat)
                      (S K)
                    == piLsb_sumR
                         (fun u => piLsb_sumR (fun i => G (u + i)%nat u) (S (K - u))%nat)
                         (S K)
                       + piLsb_sumR (fun u => G (S K) u) (S K)).
    { rewrite <- (piLsb_sumR_plus
                    (fun u => piLsb_sumR (fun i => G (u + i)%nat u) (S (K - u))%nat)
                    (fun u => G (S K) u) (S K)).
      apply piLsb_sumR_ext. intros u Hu.
      replace (S (S K - u))%nat with (S (S (K - u)))%nat by lia.
      rewrite piLsb_sumR_snoc. cbv beta.
      replace (u + S (K - u))%nat with (S K)%nat by lia.
      apply Qeq_refl. }
    rewrite Hgrow. rewrite IH. ring.
Qed.

(** Row-sum form of the partial sums: [C_k(x)] equals [sum_{i<S k}] of the cos terms. *)
Lemma piLe_partial_cos_sumR : forall (k : nat) (x : Q),
  cos_partial k x == piLsb_sumR (fun i => cos_term i x) (S k).
Proof.
  intros k x. induction k as [| k IH].
  - cbn [cos_partial piLsb_sumR]. cbv beta. ring.
  - cbn [cos_partial]. rewrite IH.
    rewrite (piLsb_sumR_snoc (fun i => cos_term i x) (S k)). cbv beta. ring.
Qed.

(** Row-sum form of the partial sums: [S_k(x)] equals [sum_{i<S k}] of the sin terms. *)
Lemma piLe_partial_sin_sumR : forall (k : nat) (x : Q),
  sin_partial k x == piLsb_sumR (fun i => sin_term i x) (S k).
Proof.
  intros k x. induction k as [| k IH].
  - cbn [sin_partial piLsb_sumR]. cbv beta. ring.
  - cbn [sin_partial]. rewrite IH.
    rewrite (piLsb_sumR_snoc (fun i => sin_term i x) (S k)). cbv beta. ring.
Qed.

(** Full row families: the even row [sum_{i<S w} c_i c_{w-i}] and the odd row [sum_{i<w} s_i s_{w-1-i}]. *)
Definition piLe_rowc_full (w : nat) (x : Q) : Q :=
  piLsb_sumR (fun i => cos_term i x * cos_term (w - i)%nat x) (S w).

Definition piLe_rows_full (w : nat) (x : Q) : Q :=
  piLsb_sumR (fun i => sin_term i x * sin_term (w - 1 - i)%nat x) w.

(** Row-identity telescope: [sum_{w<T}(even row - odd row) == sum_{w<T} cos w (2x)]. *)
Lemma piLe_rowC_telescope : forall (T : nat) (x : Q),
  piLsb_sumR (fun w => piLe_rowc_full w x - piLe_rows_full w x) T
  == piLsb_sumR (fun w => cos_term w (2 * x)%Q) T.
Proof.
  intros T x. apply piLsb_sumR_ext. intros w _.
  destruct w as [| w].
  - unfold piLe_rowc_full, piLe_rows_full.
    cbn [piLsb_sumR]. cbv beta.
    vm_compute. reflexivity.
  - unfold piLe_rowc_full, piLe_rows_full.
    apply (piLe_rowC_cross (Datatypes.S w) x). lia.
Qed.

(* ================= Section 13. Exact band representation (the top-row identity) ================= *)

(** Band representation theorem: the truncation remainder equals the exact sum of [ssrow - ccrow] over the row range [k+1, 2k+2] (in the last row [m = 2k+2] both windows are empty and the contribution is zero). *)

Lemma piLe_dcos_band_rows : forall (k : nat) (x : Q),
  piL_cos_dres k x
  == piLsb_sumR (fun u => piLe_ssrow k (S (k + u))%nat x - piLe_ccrow k (S (k + u))%nat x)
                (S (S k)).
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
  pose proof (piL_cos_partial_double k x) as Hd0.
  assert (Hd : piL_cos_dres k x == cos_partial k (2 * x)%Q
                                 - cos_partial k x * cos_partial k x
                                 + sin_partial k x * sin_partial k x).
  { transitivity (cos_partial k x * cos_partial k x
                  - sin_partial k x * sin_partial k x + piL_cos_dres k x
                  - (cos_partial k x * cos_partial k x
                     - sin_partial k x * sin_partial k x)).
    - ring.
    - rewrite Hd0. ring. }
  rewrite Hd.
  rewrite (piLe_partial_cos_sumR k (2 * x)%Q).
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
  rewrite <- (piLe_rowC_telescope (S k) x).
  assert (Hml : piLsb_sumR
                  (fun w : nat => piLe_rowc_full w x - piLe_rows_full w x) (S k)
                == piLsb_sumR (fun w : nat => piLe_rowc_full w x) (S k)
                   + - piLsb_sumR (fun w : nat => piLe_rows_full w x) (S k)).
  { rewrite <- (piLsb_sumR_opp (fun w => piLe_rows_full w x) (S k)).
    apply (piLsb_sumR_plus (fun w => piLe_rowc_full w x)
             (fun w => - piLe_rows_full w x) (S k)). }
  rewrite Hml.
  rewrite (piLsb_sumR_snoc
             (fun u => piLe_ssrow k (S (k + u))%nat x - piLe_ccrow k (S (k + u))%nat x)
             (S k)).
  cbv beta.
  assert (Hz : piLe_ssrow k (S (k + S k))%nat x - piLe_ccrow k (S (k + S k))%nat x == 0%Q).
  { unfold piLe_ssrow, piLe_ccrow.
    replace (2 * k + 2 - S (k + S k))%nat with 0%nat by lia.
    replace (2 * k + 1 - S (k + S k))%nat with 0%nat by lia.
    rewrite (piLe_sumR_0 (fun u : nat => sin_term (S (k + S k) - 1 - k + u) x * sin_term (k - u) x)).
    rewrite (piLe_sumR_0 (fun u : nat => cos_term (S (k + S k) - k + u) x * cos_term (k - u) x)).
    ring. }
  rewrite Hz.
  assert (Hmr : piLsb_sumR
                  (fun u : nat => piLe_ssrow k (S (k + u))%nat x
                                  - piLe_ccrow k (S (k + u))%nat x) (S k)
                == piLsb_sumR (fun u : nat => piLe_ssrow k (S (k + u))%nat x) (S k)
                   + - piLsb_sumR (fun u : nat => piLe_ccrow k (S (k + u))%nat x) (S k)).
  { rewrite <- (piLsb_sumR_opp (fun u => piLe_ccrow k (S (k + u))%nat x) (S k)).
    apply (piLsb_sumR_plus (fun u => piLe_ssrow k (S (k + u))%nat x)
             (fun u => - piLe_ccrow k (S (k + u))%nat x) (S k)). }
  rewrite Hmr.
  ring.
Qed.

(* ================= Section 14. Row majorants: |ccrow|, |ssrow| <= t'_m/2 ================= *)

(** Closed form of the even-denominator full row sum: [sum_j B^(2m)/((2j)!(2(m-j))!) == t'_m/2]. *)
Lemma piLe_pointrow_even_closed : forall (m : nat) (B : Q),
  (1 <= m)%nat -> Qle 0 B ->
  piLsb_sumR (fun j => q_pow B (2 * m)%nat
                       / (q_fact (2 * j)%nat * q_fact (2 * (m - j))%nat)) (S m)
  == (1 # 2)%Q * piLe_tc_term m B.
Proof.
  intros m B Hm H0B.
  assert (Hscal : forall j : nat,
    q_pow B (2 * m)%nat / (q_fact (2 * j)%nat * q_fact (2 * (m - j))%nat)
    == 1 / (q_fact (2 * j)%nat * q_fact (2 * (m - j))%nat) * q_pow B (2 * m)%nat).
  { intros j. unfold Qdiv. ring. }
  rewrite (piLsb_sumR_ext
             (fun j => q_pow B (2 * m)%nat
                       / (q_fact (2 * j)%nat * q_fact (2 * (m - j))%nat))
             (fun j => 1 / (q_fact (2 * j)%nat * q_fact (2 * (m - j))%nat)
                       * q_pow B (2 * m)%nat)
             (S m) (fun j _ => Hscal j)).
  transitivity (piLsb_sumR
                  (fun j => 1 / (q_fact (2 * j)%nat * q_fact (2 * (m - j))%nat)) (S m)
                * q_pow B (2 * m)%nat).
  - symmetry. apply (piLrowB_row_scal_r (q_pow B (2 * m)%nat)
                      (fun j => 1 / (q_fact (2 * j)%nat * q_fact (2 * (m - j))%nat))
                      (S m)).
  - rewrite (piLe_row_even_full m Hm).
    assert (Hz : q_pow (2 * B) (2 * m)%nat
                 == q_pow 2%Q (2 * m)%nat * q_pow B (2 * m)%nat)
      by (rewrite (lw0_q_pow_mult 2%Q B (2 * m)%nat); reflexivity).
    unfold piLe_tc_term.
    assert (Heq : q_pow 2%Q (2 * m)%nat / q_fact (2 * m)%nat * (1 # 2)%Q
                  * q_pow B (2 * m)%nat
                  == (1 # 2)%Q * (q_pow (2 * B) (2 * m)%nat / q_fact (2 * m)%nat)).
    { rewrite Hz. unfold Qdiv. ring. }
    rewrite Heq. apply Qeq_refl.
Qed.

(** The cos row majorant: [|ccrow k m x| <= t'_m(B)/2] for [k < m] and [|x| <= B]. *)
Lemma piLe_ccrow_abs_le : forall (k m : nat) (x B : Q),
  (k < m)%nat -> Qle (Qabs x) B ->
  Qle (Qabs (piLe_ccrow k m x)) ((1 # 2)%Q * piLe_tc_term m B).
Proof.
  intros k m x B Hkm Hx.
  assert (Hm1 : (1 <= m)%nat) by lia.
  assert (H0B : Qle 0 B)
    by (apply (Qle_trans 0 (Qabs x) B); [apply Qabs_nonneg | exact Hx]).
  assert (Hqdiv : forall e d : nat, Qle 0 (q_pow B e / q_fact d)).
  { intros e d. unfold Qdiv.
    apply (piLe_qmult_nonneg_r (q_pow B e) (/ q_fact d)).
    - apply q_pow_nonneg; exact H0B.
    - apply (Qlt_le_weak 0 _). apply Qinv_lt_0_compat. apply q_fact_pos. }
  assert (Hpt : forall j : nat, (j <= m)%nat ->
    Qle (Qabs (cos_term j x)) (q_pow B (2 * j)%nat / q_fact (2 * j)%nat)).
  { intros j Hj.
    exact (QleT'_to_Qle (Qabs (cos_term j x))
             (q_pow B (2 * j)%nat / q_fact (2 * j)%nat)
             (piL_cos_term_abs_bound j x B (Qle_to_QleT' (Qabs x) B Hx))). }
  assert (Hreidx : forall u : nat, (u < 2 * k + 1 - m)%nat ->
    q_pow B (2 * m)%nat / (q_fact (2 * (m - k + u))%nat * q_fact (2 * (k - u))%nat)
    == q_pow B (2 * m)%nat
       / (q_fact (2 * (m - k + u))%nat * q_fact (2 * (m - (m - k + u))%nat))).
  { intros u Hu.
    replace (2 * (k - u))%nat with (2 * (m - (m - k + u)))%nat by lia.
    apply Qeq_refl. }
  assert (Hpowext : forall u : nat, (u < 2 * k + 1 - m)%nat ->
    (q_pow B (2 * (m - k + u))%nat / q_fact (2 * (m - k + u))%nat)
    * (q_pow B (2 * (k - u))%nat / q_fact (2 * (k - u))%nat)
    == q_pow B (2 * m)%nat
       / (q_fact (2 * (m - k + u))%nat * q_fact (2 * (k - u))%nat)).
  { intros u Hu.
    assert (Hpow : q_pow B (2 * m)%nat
                   == q_pow B (2 * (m - k + u))%nat * q_pow B (2 * (k - u))%nat).
    { replace (2 * m)%nat with (2 * (m - k + u) + 2 * (k - u))%nat by lia.
      rewrite <- (lw0_q_pow_add B (2 * (m - k + u)) (2 * (k - u))).
      apply Qeq_refl. }
    rewrite Hpow. unfold Qdiv.
    rewrite <- (piLe_qinv_distr (q_fact (2 * (m - k + u))%nat)
                  (q_fact (2 * (k - u))%nat)
                  (piLrowB_qfact_neq0 (2 * (m - k + u)))
                  (piLrowB_qfact_neq0 (2 * (k - u)))).
    unfold Qdiv. ring. }
  unfold piLe_ccrow.
  apply (Qle_trans _
           (piLsb_sumR (fun u => Qabs (cos_term (m - k + u)%nat x * cos_term (k - u)%nat x))
                       (2 * k + 1 - m)%nat)).
  { apply (piLe_abs_sumR_le
             (fun u => cos_term (m - k + u)%nat x * cos_term (k - u)%nat x)
             (2 * k + 1 - m)%nat). }
  apply (Qle_trans _
           (piLsb_sumR (fun u => Qabs (cos_term (m - k + u)%nat x)
                                * Qabs (cos_term (k - u)%nat x))
                       (2 * k + 1 - m)%nat)).
  { apply piLe_sumR_le. intros u _.
    rewrite Qabs_Qmult. apply Qle_refl. }
  apply (Qle_trans _
           (piLsb_sumR (fun u => (q_pow B (2 * (m - k + u))%nat / q_fact (2 * (m - k + u))%nat)
                                 * (q_pow B (2 * (k - u))%nat / q_fact (2 * (k - u))%nat))
                       (2 * k + 1 - m)%nat)).
  { apply piLe_sumR_le. intros u Hu.
    apply (Qle_trans _ ((q_pow B (2 * (m - k + u))%nat / q_fact (2 * (m - k + u))%nat)
                        * Qabs (cos_term (k - u)%nat x))).
    - apply (Qmult_le_compat_r (Qabs (cos_term (m - k + u)%nat x))
               (q_pow B (2 * (m - k + u))%nat / q_fact (2 * (m - k + u))%nat)
               (Qabs (cos_term (k - u)%nat x))).
      + apply Hpt. lia.
      + apply Qabs_nonneg.
    - rewrite (Qmult_comm (q_pow B (2 * (m - k + u))%nat / q_fact (2 * (m - k + u))%nat)
                 (Qabs (cos_term (k - u)%nat x))).
      rewrite (Qmult_comm (q_pow B (2 * (m - k + u))%nat / q_fact (2 * (m - k + u))%nat)
                 (q_pow B (2 * (k - u))%nat / q_fact (2 * (k - u))%nat)).
      apply (Qmult_le_compat_r (Qabs (cos_term (k - u)%nat x))
               (q_pow B (2 * (k - u))%nat / q_fact (2 * (k - u))%nat)
               (q_pow B (2 * (m - k + u))%nat / q_fact (2 * (m - k + u))%nat)).
      + apply Hpt. lia.
      + apply Hqdiv. }
  apply (Qle_trans _
           (piLsb_sumR (fun u => q_pow B (2 * m)%nat
                                 / (q_fact (2 * (m - k + u))%nat * q_fact (2 * (k - u))%nat))
                       (2 * k + 1 - m)%nat)).
  { apply piLe_sumR_le. intros u Hu. cbv beta.
    rewrite (Hpowext u Hu). apply Qle_refl. }
  rewrite (piLsb_sumR_ext
             (fun u => q_pow B (2 * m)%nat
                       / (q_fact (2 * (m - k + u))%nat * q_fact (2 * (k - u))%nat))
             (fun u => q_pow B (2 * m)%nat
                       / (q_fact (2 * (m - k + u))%nat
                          * q_fact (2 * (m - (m - k + u))%nat)))
             (2 * k + 1 - m)%nat Hreidx).
  apply (Qle_trans _
           (piLsb_sumR (fun j => q_pow B (2 * m)%nat
                                 / (q_fact (2 * j)%nat * q_fact (2 * (m - j))%nat))
                       (S m))).
  { apply (piLe_sumR_shift_le
             (fun j => q_pow B (2 * m)%nat
                       / (q_fact (2 * j)%nat * q_fact (2 * (m - j))%nat))
             (m - k) (2 * k + 1 - m) (S m)).
    - lia.
    - intros j. unfold Qdiv.
      apply piLe_qmult_nonneg_r.
      + apply q_pow_nonneg; exact H0B.
      + apply (Qlt_le_weak 0 _). apply Qinv_lt_0_compat.
        apply (Qmult_lt_0_compat (q_fact (2 * j)%nat)
                 (q_fact (2 * (m - j))%nat)); apply q_fact_pos. }
  rewrite (piLe_pointrow_even_closed m B Hm1 H0B).
  apply Qle_refl.
Qed.

(** The sin row majorant: [|ssrow k m x| <= t'_m(B)/2] for [k < m] and [|x| <= B]. *)
Lemma piLe_ssrow_abs_le : forall (k m : nat) (x B : Q),
  (k < m)%nat -> Qle (Qabs x) B ->
  Qle (Qabs (piLe_ssrow k m x)) ((1 # 2)%Q * piLe_tc_term m B).
Proof.
  intros k m x B Hkm Hx.
  assert (Hm1 : (1 <= m)%nat) by lia.
  assert (H0B : Qle 0 B)
    by (apply (Qle_trans 0 (Qabs x) B); [apply Qabs_nonneg | exact Hx]).
  assert (Hqdiv : forall e d : nat, Qle 0 (q_pow B e / q_fact d)).
  { intros e d. unfold Qdiv.
    apply (piLe_qmult_nonneg_r (q_pow B e) (/ q_fact d)).
    - apply q_pow_nonneg; exact H0B.
    - apply (Qlt_le_weak 0 _). apply Qinv_lt_0_compat. apply q_fact_pos. }
  assert (Hpt : forall j : nat, (j < m)%nat ->
    Qle (Qabs (sin_term j x))
        (q_pow B (Datatypes.S (2 * j))%nat / q_fact (Datatypes.S (2 * j))%nat)).
  { intros j Hj.
    exact (QleT'_to_Qle (Qabs (sin_term j x))
             (q_pow B (Datatypes.S (2 * j))%nat / q_fact (Datatypes.S (2 * j))%nat)
             (piL_sin_term_abs_bound j x B (Qle_to_QleT' (Qabs x) B Hx))). }
  assert (Hreidx : forall u : nat, (u < 2 * k + 2 - m)%nat ->
    q_pow B (2 * m)%nat
    / (q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat * q_fact (Datatypes.S (2 * (k - u)))%nat)
    == q_pow B (2 * m)%nat
       / (q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat
          * q_fact (Datatypes.S (2 * (m - 1 - (m - 1 - k + u))))%nat)).
  { intros u Hu.
    replace (2 * (k - u))%nat
      with (2 * (m - 1 - (m - 1 - k + u)))%nat by lia.
    apply Qeq_refl. }
  assert (Hpowext : forall u : nat, (u < 2 * k + 2 - m)%nat ->
    (q_pow B (Datatypes.S (2 * (m - 1 - k + u)))%nat
     / q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat)
    * (q_pow B (Datatypes.S (2 * (k - u)))%nat / q_fact (Datatypes.S (2 * (k - u)))%nat)
    == q_pow B (2 * m)%nat
       / (q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat
          * q_fact (Datatypes.S (2 * (k - u)))%nat)).
  { intros u Hu.
    assert (Hpow : q_pow B (2 * m)%nat
                   == q_pow B (Datatypes.S (2 * (m - 1 - k + u)))%nat
                      * q_pow B (Datatypes.S (2 * (k - u)))%nat).
    { replace (2 * m)%nat
        with (Datatypes.S (2 * (m - 1 - k + u))
              + Datatypes.S (2 * (k - u)))%nat by lia.
      rewrite <- (lw0_q_pow_add B (Datatypes.S (2 * (m - 1 - k + u)))
                    (Datatypes.S (2 * (k - u)))).
      apply Qeq_refl. }
    rewrite Hpow. unfold Qdiv.
    rewrite <- (piLe_qinv_distr
                  (q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat)
                  (q_fact (Datatypes.S (2 * (k - u)))%nat)
                  (piLrowB_qfact_neq0 (Datatypes.S (2 * (m - 1 - k + u))))
                  (piLrowB_qfact_neq0 (Datatypes.S (2 * (k - u))))).
    unfold Qdiv. ring. }
  assert (Hclosed : piLsb_sumR (fun j => q_pow B (2 * m)%nat
                                          / (q_fact (Datatypes.S (2 * j))%nat
                                             * q_fact (Datatypes.S (2 * (m - 1 - j)))%nat)) m
    == (1 # 2)%Q * piLe_tc_term m B).
  { assert (Hscal : forall j : nat,
      q_pow B (2 * m)%nat
      / (q_fact (Datatypes.S (2 * j))%nat * q_fact (Datatypes.S (2 * (m - 1 - j)))%nat)
      == 1 / (q_fact (Datatypes.S (2 * j))%nat * q_fact (Datatypes.S (2 * (m - 1 - j)))%nat)
         * q_pow B (2 * m)%nat).
    { intros j. unfold Qdiv. ring. }
    rewrite (piLsb_sumR_ext
               (fun j => q_pow B (2 * m)%nat
                         / (q_fact (Datatypes.S (2 * j))%nat
                            * q_fact (Datatypes.S (2 * (m - 1 - j)))%nat))
               (fun j => 1 / (q_fact (Datatypes.S (2 * j))%nat
                              * q_fact (Datatypes.S (2 * (m - 1 - j)))%nat)
                         * q_pow B (2 * m)%nat)
               m (fun j _ => Hscal j)).
    transitivity (piLsb_sumR
                    (fun j => 1 / (q_fact (Datatypes.S (2 * j))%nat
                                   * q_fact (Datatypes.S (2 * (m - 1 - j)))%nat)) m
                  * q_pow B (2 * m)%nat).
    - symmetry. apply (piLrowB_row_scal_r (q_pow B (2 * m)%nat)
                         (fun j => 1 / (q_fact (Datatypes.S (2 * j))%nat
                                        * q_fact (Datatypes.S (2 * (m - 1 - j)))%nat)) m).
    - rewrite (piLe_row_odd_full m Hm1).
      assert (Hz : q_pow (2 * B) (2 * m)%nat
                   == q_pow 2%Q (2 * m)%nat * q_pow B (2 * m)%nat)
        by (rewrite (lw0_q_pow_mult 2%Q B (2 * m)%nat); reflexivity).
      unfold piLe_tc_term.
      assert (Heq : q_pow 2%Q (2 * m)%nat / q_fact (2 * m)%nat * (1 # 2)%Q
                    * q_pow B (2 * m)%nat
                    == (1 # 2)%Q * (q_pow (2 * B) (2 * m)%nat / q_fact (2 * m)%nat)).
      { rewrite Hz. unfold Qdiv. ring. }
      rewrite Heq. apply Qeq_refl. }
  unfold piLe_ssrow.
  apply (Qle_trans _
           (piLsb_sumR (fun u => Qabs (sin_term (m - 1 - k + u)%nat x * sin_term (k - u)%nat x))
                       (2 * k + 2 - m)%nat)).
  { apply (piLe_abs_sumR_le
             (fun u => sin_term (m - 1 - k + u)%nat x * sin_term (k - u)%nat x)
             (2 * k + 2 - m)%nat). }
  apply (Qle_trans _
           (piLsb_sumR (fun u => Qabs (sin_term (m - 1 - k + u)%nat x)
                                * Qabs (sin_term (k - u)%nat x))
                       (2 * k + 2 - m)%nat)).
  { apply piLe_sumR_le. intros u _.
    rewrite Qabs_Qmult. apply Qle_refl. }
  apply (Qle_trans _
           (piLsb_sumR (fun u => (q_pow B (Datatypes.S (2 * (m - 1 - k + u)))%nat
                                  / q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat)
                                 * (q_pow B (Datatypes.S (2 * (k - u)))%nat
                                    / q_fact (Datatypes.S (2 * (k - u)))%nat))
                       (2 * k + 2 - m)%nat)).
  { apply piLe_sumR_le. intros u Hu.
    apply (Qle_trans _ ((q_pow B (Datatypes.S (2 * (m - 1 - k + u)))%nat
                         / q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat)
                        * Qabs (sin_term (k - u)%nat x))).
    - apply (Qmult_le_compat_r (Qabs (sin_term (m - 1 - k + u)%nat x))
               (q_pow B (Datatypes.S (2 * (m - 1 - k + u)))%nat
                / q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat)
               (Qabs (sin_term (k - u)%nat x))).
      + apply Hpt. lia.
      + apply Qabs_nonneg.
    - rewrite (Qmult_comm (q_pow B (Datatypes.S (2 * (m - 1 - k + u)))%nat
                           / q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat)
                 (Qabs (sin_term (k - u)%nat x))).
      rewrite (Qmult_comm (q_pow B (Datatypes.S (2 * (m - 1 - k + u)))%nat
                           / q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat)
                 (q_pow B (Datatypes.S (2 * (k - u)))%nat
                  / q_fact (Datatypes.S (2 * (k - u)))%nat)).
      apply (Qmult_le_compat_r (Qabs (sin_term (k - u)%nat x))
               (q_pow B (Datatypes.S (2 * (k - u)))%nat
                / q_fact (Datatypes.S (2 * (k - u)))%nat)
               (q_pow B (Datatypes.S (2 * (m - 1 - k + u)))%nat
                / q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat)).
      + apply Hpt. lia.
      + apply Hqdiv. }
  apply (Qle_trans _
           (piLsb_sumR (fun u => q_pow B (2 * m)%nat
                                 / (q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat
                                    * q_fact (Datatypes.S (2 * (k - u)))%nat))
                       (2 * k + 2 - m)%nat)).
  { apply piLe_sumR_le. intros u Hu. cbv beta.
    rewrite (Hpowext u Hu). apply Qle_refl. }
  rewrite (piLsb_sumR_ext
             (fun u => q_pow B (2 * m)%nat
                       / (q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat
                          * q_fact (Datatypes.S (2 * (k - u)))%nat))
             (fun u => q_pow B (2 * m)%nat
                       / (q_fact (Datatypes.S (2 * (m - 1 - k + u)))%nat
                          * q_fact (Datatypes.S (2 * (m - 1 - (m - 1 - k + u))))%nat))
             (2 * k + 2 - m)%nat Hreidx).
  apply (Qle_trans _
           (piLsb_sumR (fun j => q_pow B (2 * m)%nat
                                 / (q_fact (Datatypes.S (2 * j))%nat
                                    * q_fact (Datatypes.S (2 * (m - 1 - j)))%nat)) m)).
  { apply (piLe_sumR_shift_le
             (fun j => q_pow B (2 * m)%nat
                       / (q_fact (Datatypes.S (2 * j))%nat
                          * q_fact (Datatypes.S (2 * (m - 1 - j)))%nat))
             (m - 1 - k) (2 * k + 2 - m) m).
    - lia.
    - intros j. unfold Qdiv.
      apply piLe_qmult_nonneg_r.
      + apply q_pow_nonneg; exact H0B.
      + apply (Qlt_le_weak 0 _). apply Qinv_lt_0_compat.
        apply (Qmult_lt_0_compat (q_fact (Datatypes.S (2 * j))%nat)
                 (q_fact (Datatypes.S (2 * (m - 1 - j)))%nat)); apply q_fact_pos. }
  rewrite Hclosed. apply Qle_refl.
Qed.

(* ================= Section 15. The main band-bound theorem (capstone) and the consumer side of monotonicity ================= *)

(** The main cos band-bound theorem: [|dcos k x| <= band_bound k B] for all [k] with [|x| <= B]. *)
Theorem piLe_dcos_band_le : forall (k : nat) (x B : Q),
  Qle (Qabs x) B -> Qle (Qabs (piL_cos_dres k x)) (piLe_band_bound k B).
Proof.
  intros k x B Hx.
  assert (H0B : Qle 0 B)
    by (apply (Qle_trans 0 (Qabs x) B); [apply Qabs_nonneg | exact Hx]).
  rewrite piLe_dcos_band_rows.
  apply (Qle_trans _
           (piLsb_sumR (fun u => Qabs (piLe_ssrow k (S (k + u))%nat x
                                       - piLe_ccrow k (S (k + u))%nat x))
                       (S (S k)))).
  { apply piLe_abs_sumR_le. }
  apply (Qle_trans _
           (piLsb_sumR (fun u => Qabs (piLe_ssrow k (S (k + u))%nat x)
                                 + Qabs (piLe_ccrow k (S (k + u))%nat x))
                       (S (S k)))).
  { apply piLe_sumR_le. intros u _.
    apply (Qle_trans _ (Qabs (piLe_ssrow k (S (k + u))%nat x)
                        + Qabs (- piLe_ccrow k (S (k + u))%nat x))).
    - change (piLe_ssrow k (S (k + u))%nat x - piLe_ccrow k (S (k + u))%nat x)
        with (piLe_ssrow k (S (k + u))%nat x
              + - piLe_ccrow k (S (k + u))%nat x).
      apply Qabs_triangle.
    - rewrite Qabs_opp. apply Qle_refl. }
  apply (Qle_trans _
           (piLsb_sumR (fun u => (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B
                                 + (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)
                       (S (S k)))).
  { apply piLe_sumR_le. intros u Hu.
    apply (Qplus_le_compat
             (Qabs (piLe_ssrow k (S (k + u))%nat x))
             ((1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)
             (Qabs (piLe_ccrow k (S (k + u))%nat x))
             ((1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)).
    - apply (piLe_ssrow_abs_le k (S (k + u)) x B); [lia | exact Hx].
    - apply (piLe_ccrow_abs_le k (S (k + u)) x B); [lia | exact Hx]. }
  assert (Hdouble : forall u : nat,
    ((1 # 2)%Q * piLe_tc_term (S (k + u))%nat B
     + (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)
    == piLe_tc_term (S (k + u))%nat B) by (intros u; ring).
  unfold piLe_band_bound.
  rewrite <- (piLsb_sumR_ext
                (fun u => (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B
                          + (1 # 2)%Q * piLe_tc_term (S (k + u))%nat B)
                (fun u => piLe_tc_term (S (k + u))%nat B)
                (S (S k)) (fun u _ => Hdouble u)).
  apply Qle_refl.
Qed.


(* ================= Section 16. The sigma3 vanishing supply and the slot-face transfer ================= *)

(** The sigma3 vanishing supply: there is a [j] such that [|dcos k x| < dt] whenever [k >= j] and [|x| <= B]. *)
Lemma piLe_dcos_small : forall (B dt : Q),
  Qlt 0 B -> Qlt 0 dt ->
  sigT (fun j : nat => forall (k : nat) (x : Q),
    (j <= k)%nat -> Qle (Qabs x) B -> Qlt (Qabs (piL_cos_dres k x)) dt).
Proof.
  intros B dt HB Hdt.
  destruct (piLe_band_small B dt HB Hdt) as [j Hj].
  exists j. intros k x Hkx HxB.
  apply (Qle_lt_trans _ (piLe_band_bound k B)).
  - apply (piLe_dcos_band_le k x B HxB).
  - apply (Hj k Hkx).
Qed.

(** The slot-face supply theorem: [piLd3_seed_dcos] (transferring the stdlib [Qlt]/[Qle] face onto the [QltT]/[QleT'] slot face). *)
Theorem piLe_seed_dcos : piLd3_seed_dcos.
Proof.
  unfold piLd3_seed_dcos. intros B dt HB Hdt.
  destruct (piLe_dcos_small B dt (QltT_to_Qlt 0 B HB) (QltT_to_Qlt 0 dt Hdt)) as [j Hj].
  exists j. intros k x Hkx HxB.
  apply Qlt_to_QltT. apply (Hj k x Hkx).
  exact (QleT'_to_Qle (Qabs x) B HxB).
Qed.

Print Assumptions piLe_sumR_trapswap_le.
Print Assumptions piLe_partial_cos_sumR.
Print Assumptions piLe_partial_sin_sumR.
Print Assumptions piLe_rowC_telescope.
Print Assumptions piLe_dcos_band_rows.
Print Assumptions piLe_pointrow_even_closed.
Print Assumptions piLe_ccrow_abs_le.
Print Assumptions piLe_ssrow_abs_le.
Print Assumptions piLe_dcos_band_le.
Print Assumptions piLe_dcos_small.
Print Assumptions piLe_seed_dcos.


(* ================= Section 16. The sigma2 vanishing supply (the double-angle sin truncation remainder) ================= *)

(** The vanishing supply for the double-angle sin truncation remainder [piL_sin_dres]: there is a depth [j] such that [|piL_sin_dres k x| < dt] whenever [k >= j] and [|x| <= B]; the conclusion is carried at the [Set] level as a [sigT] witness.  The statement face takes the original shape of the [PiKernelSlack_D3_synth] seed slot statement [piLd3_seed_dres]; the stdlib [Qlt] face is carried by [piLd_dres_small] of [PiBandBound] (the chain of the band-machine length selection and the main band bound), and the [QltT]/[QleT'] slot face is reached through the bridge lemmas of [PiKernelSlack]. *)




Require Import PiBandBound.
Theorem piLe_seed_dres : piLd3_seed_dres.
Proof.
  unfold piLd3_seed_dres.
  intros B dt HB Hdte.
  destruct (piLd_dres_small B dt (QltT_to_Qlt 0 B HB) (QltT_to_Qlt 0 dt Hdte))
    as [j Hj].
  exists j. intros k x Hk HxB.
  apply Qlt_to_QltT.
  exact (Hj k x Hk (QleT'_to_Qle (Qabs x) B HxB)).
Qed.
Print Assumptions piLe_seed_dres.
