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
(** * PiCosTailScan.v

    Mission.  Alternating tail bounds for the cosine partial sums and
    the location of a root interval, over the rational arithmetic of
    [Q]:
    (1) tail bound: for [0 <= x <= 2] and [2 <= m <= k],
        [|cos_partial k x - cos_partial m x| <=
         (3/2) * x^{2(m+1)} / (2(m+1))!]
        (the term decay ratio [x^2 / ((2j+1) * (2j+2)) <= 1/3] is
        controlled through a geometric series);
    (2) explicit endpoint sign certificates: for every [k >= 5],
        [cos_partial k (3/2) > 0] and [cos_partial k (5/3) < 0] (the
        margins are concrete rationals, evaluated by [vm_compute]);
    (3) bisection [vt_bisect]: with [K >= 2] fixed, bisection of the
        sign of [cos_partial K] inside [[a,b]] subset of [[0,2]], with
        interval length [(b-a)/2^n] and the endpoint sign certificates
        preserved along the nesting; [vt_scan_bracket] returns, carried
        as a two-level [sigT], the step-[n] bracketing interval on
        [[3/2, 5/3]];
    (4) downstream interfaces: the upper bound [vt_bisect_left_val_le]
        on the function value at the left endpoint of the bracket (the
        Lipschitz constant [leibsep_abssum_cos] times the interval
        length, shrinking with [n]), and the strictly decreasing lower
        bound [vt_cos_decr_half] (consuming the difference-bound lemma
        [sc_cos_partial_diff_le], the pointwise uniqueness core).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [ZArith.ZArith], [Arith.PeanoNat], [Setoid], [Morphisms], [Lia];
    this development, [PiCompareT] ([QltT]/[QleT']), [PiKernelSlack]
    ([cos_term]/[cos_partial]/[q_pow]/[q_fact]/
    [leibsep_cos_partial_lipschitz]/[leibsep_abssum_cos]),
    [PiVertexPolyDiff] ([sc_cos_partial_diff_le] and the [sum_upto]
    infrastructure).

    References.  [S10_KVQuantTrig.v], the [cos_scan] family
    ([:7679]-[:7812]) and [cos_root_pt_bound] ([:8156]), restated over
    the rationals [Q]; the pure-cos alternating tail bound is new (the
    pointwise root bounds of [S10] are obtained jointly through the
    Lipschitz, Cauchy and [log_eps] machinery, with no standalone
    tail-bound lemma).

    Constructivity.  The auxiliary lemmas conclude in [Qle]/[Qlt] (the
    stdlib [Q] order predicates, purely constructive); the top-level
    certificates and the scanning specification conclude in
    [QltT]/[QleT'] (carried at the [Set] level); assumption-free and
    fully proved, with no non-constructive principles.

    Build.  [coqc -native-compiler no -q -Q . "" PiCosTailScan.v]
    (Rocq 9.1.0).

    WARNING: this file is experimental and likely to change in future releases. *)
(* ============================================================ *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.
Require Import PiCompareT.
Require Import PiKernelSlack.
Require Import PiVertexPolyDiff.

(* ============================================================ *)
(* Section 1. The term absolute-value machine (decay ratio and geometric tail) *)
(* ============================================================ *)

(* The absolute value of the j-th cos term: x^{2j}/(2j)! (through the [x^2] power form) *)
Definition cos_abs_term (x : Q) (j : nat) : Q :=
  q_pow (x * x) j / q_fact (2 * j).

(* Nonnegativity of the term absolute value *)
Lemma vt_abs_term_nonneg : forall (x : Q) (j : nat),
  Qle 0 x -> Qle 0 (cos_abs_term x j).
Proof.
  intros x j Hx. unfold cos_abs_term. unfold Qdiv.
  apply Qmult_le_0_compat.
  - apply q_pow_nonneg. apply Qmult_le_0_compat; exact Hx.
  - apply (Qlt_le_weak 0 (Qinv (q_fact (2 * j)))).
    apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

(* The term absolute value == the absolute value of the cos term ([0 <= x]; the even and odd cases) *)
Lemma vt_cos_term_abs : forall (j : nat) (x : Q),
  Qle 0 x -> Qabs (cos_term j x) == cos_abs_term x j.
Proof.
  intros j x Hx. destruct (vt_parity j) as [[m Hm] | [m Hm]].
  - (* j = 2m *)
    rewrite Hm. unfold cos_term, cos_abs_term.
    rewrite (q_pow_neg1_even m). rewrite Qmult_1_l.
    assert (Hsq : q_pow x (2 * (2 * m)) == q_pow (x * x) (2 * m))
      by (apply Qeq_sym; apply (sc_qpow_sq x (2 * m))).
    setoid_rewrite Hsq.
    replace (2 * (2 * m))%nat with (4 * m)%nat by lia.
    assert (Hnn : Qle 0 (q_pow (x * x) (2 * m) / q_fact (4 * m))).
    { unfold Qdiv. apply Qmult_le_0_compat.
      - apply q_pow_nonneg. apply Qmult_le_0_compat; exact Hx.
      - apply (Qlt_le_weak 0 (Qinv (q_fact (4 * m)))).
        apply Qinv_lt_0_compat. apply q_fact_pos. }
    apply Qabs_pos. exact Hnn.
  - (* j = 2m+1 *)
    rewrite Hm. unfold cos_term, cos_abs_term.
    rewrite (q_pow_neg1_odd m).
    assert (Hm1 : forall w : Q, -1 * w == -w) by (intro w; ring).
    rewrite Hm1. rewrite Qabs_opp.
    assert (Hsq : q_pow x (2 * (2 * m + 1)) == q_pow (x * x) (2 * m + 1))
      by (apply Qeq_sym; apply (sc_qpow_sq x (2 * m + 1))).
    setoid_rewrite Hsq.
    replace (2 * (2 * m + 1))%nat with (4 * m + 2)%nat by lia.
    assert (Hnn : Qle 0 (q_pow (x * x) (2 * m + 1) / q_fact (4 * m + 2))).
    { unfold Qdiv. apply Qmult_le_0_compat.
      - apply q_pow_nonneg. apply Qmult_le_0_compat; exact Hx.
      - apply (Qlt_le_weak 0 (Qinv (q_fact (4 * m + 2)))).
        apply Qinv_lt_0_compat. apply q_fact_pos. }
    apply Qabs_pos. exact Hnn.
Qed.

(* Adjacent decay ratio: for [j >= 1] and [0 <= x <= 2], t_{j+1} <= (1/3) * t_j *)
Lemma vt_abs_term_step : forall (x : Q) (j : nat),
  Qle 0 x -> Qle x 2 -> (1 <= j)%nat ->
  Qle (cos_abs_term x (Datatypes.S j)) ((1#3) * cos_abs_term x j).
Proof.
  intros x j Hx0 Hx2 Hj. unfold cos_abs_term.
  setoid_rewrite (q_pow_succ (x * x) j).
  setoid_rewrite (sc_qfact_2succ j).
  assert (Hn1 : (Datatypes.S (Datatypes.S (2 * j)) = 2 * j + 2)%nat) by lia.
  assert (Hn2 : (Datatypes.S (2 * j) = 2 * j + 1)%nat) by lia.
  rewrite Hn1. rewrite Hn2.
  assert (H3F : Qlt 0 (3 * q_fact (2 * j))).
  { apply Qmult_lt_0_compat; [unfold Qlt; simpl; lia | apply q_fact_pos]. }
  assert (HR : (1#3) * (q_pow (x * x) j / q_fact (2 * j)) ==
               q_pow (x * x) j / (3 * q_fact (2 * j))).
  { field.
    all: intro Hfx;
         (exact (vt_qpos_neq (q_fact (2 * j)) (q_fact_pos (2 * j)) Hfx)
          || exact (vt_qpos_neq (3 * q_fact (2 * j)) H3F Hfx)). }
  rewrite HR.
  (* The decay-ratio core: 3 * x^2 <= (2j+2) * (2j+1); for [j >= 1], bridged through 12 *)
  assert (Hc02 : Qle 0 2) by (unfold Qle; simpl; lia).
  assert (Hxx : Qle (x * x) (2 * 2)).
  { apply (Qle_trans (x * x) (2 * x) (2 * 2)).
    - exact (Qmult_le_compat_r x 2 x Hx2 Hx0).
    - apply (Qle_trans (2 * x) (x * 2) (2 * 2)).
      + apply qeq_le. apply Qmult_comm.
      + exact (Qmult_le_compat_r x 2 2 Hx2 Hc02). }
  assert (Hmq : (Z.of_nat (2 * j + 2) # 1) * (Z.of_nat (2 * j + 1) # 1)
                == (Z.of_nat (2 * j + 2) * Z.of_nat (2 * j + 1)) # 1)
    by (unfold Qeq; simpl; ring).
  assert (Hc31 : Qle 0 (3#1)) by (unfold Qle; simpl; lia).
  assert (Hcore : Qle ((3#1) * (x * x))
                      ((Z.of_nat (2 * j + 2) # 1) * (Z.of_nat (2 * j + 1) # 1))).
  { apply (Qle_trans _ 12).
    - apply (Qle_trans _ ((3#1) * (2 * 2))).
      + apply (sc_qmult_le_l (x * x) (2 * 2) (3#1) Hxx Hc31).
      + unfold Qle; simpl; lia.
    - rewrite Hmq. unfold Qle. simpl.
      rewrite ?Z.mul_1_r.
      apply (Z.mul_le_mono_nonneg 4 (Z.of_nat (2 * j + 2)) 3 (Z.of_nat (2 * j + 1))).
      all: lia. }
  assert (HM1 : Qlt 0 ((Z.of_nat (2 * j + 1) # 1))) by (unfold Qlt; simpl; lia).
  assert (HM2 : Qlt 0 ((Z.of_nat (2 * j + 2) # 1))) by (unfold Qlt; simpl; lia).
  assert (Hpf0 : Qle 0 (q_pow (x * x) j * q_fact (2 * j)))
    by (apply Qmult_le_0_compat;
        [apply q_pow_nonneg; apply Qmult_le_0_compat; exact Hx0
        | apply (Qlt_le_weak 0 (q_fact (2 * j))); apply q_fact_pos]).
  apply (sc_qle_div_cross ((x * x) * q_pow (x * x) j) (q_pow (x * x) j)
          (((Z.of_nat (2 * j + 2) # 1) * (Z.of_nat (2 * j + 1) # 1)) * q_fact (2 * j))
          (3 * q_fact (2 * j))).
  - apply Qmult_lt_0_compat.
    + apply Qmult_lt_0_compat; [exact HM2 | exact HM1].
    + apply q_fact_pos.
  - exact H3F.
  - apply (Qle_trans _ (q_pow (x * x) j * q_fact (2 * j) * ((3#1) * (x * x)))).
    + apply qeq_le. ring.
    + apply (Qle_trans _ (q_pow (x * x) j * q_fact (2 * j) *
             ((Z.of_nat (2 * j + 2) # 1) * (Z.of_nat (2 * j + 1) # 1)))).
      * exact (sc_qmult_le_l ((3#1) * (x * x))
                ((Z.of_nat (2 * j + 2) # 1) * (Z.of_nat (2 * j + 1) # 1))
                (q_pow (x * x) j * q_fact (2 * j)) Hcore Hpf0).
      * apply qeq_le. ring.
Qed.

(* Step decay: t_{m+i} <= (1/3)^i * t_m *)
Lemma vt_abs_term_decay : forall (x : Q) (m i : nat),
  Qle 0 x -> Qle x 2 -> (1 <= m)%nat ->
  Qle (cos_abs_term x (m + i)) (q_pow (1#3) i * cos_abs_term x m).
Proof.
  intros x m i Hx0 Hx2 Hm.
  assert (Hc13 : Qle 0 (1#3)) by (unfold Qle; simpl; lia).
  induction i as [| i' IH].
  - rewrite Nat.add_0_r.
    assert (Hp03 : q_pow (1#3) 0 == 1) by reflexivity.
    rewrite Hp03, Qmult_1_l. apply Qle_refl.
  - assert (Hs : ((m + Datatypes.S i') = Datatypes.S (m + i'))%nat) by lia.
    rewrite Hs.
    rewrite q_pow_succ.
    apply (Qle_trans _ ((1#3) * cos_abs_term x (m + i'))).
    + apply vt_abs_term_step; [exact Hx0 | exact Hx2 | lia].
    + apply (Qle_trans _ ((1#3) * (q_pow (1#3) i' * cos_abs_term x m))).
      * exact (sc_qmult_le_l (cos_abs_term x (m + i'))
                (q_pow (1#3) i' * cos_abs_term x m) (1#3) IH Hc13).
      * apply qeq_le. ring.
Qed.

(* Closed form of the geometric sum: sum_{i<n} (1/3)^i == (3/2) * (1 - (1/3)^n) *)
Lemma vt_geom_closed : forall n : nat,
  sum_upto n (fun i : nat => q_pow (1#3) i) == (3#2) * (1 - q_pow (1#3) n).
Proof.
  intro n. induction n as [| n' IH].
  - simpl. unfold Qeq. simpl. lia.
  - cbn [sum_upto]. rewrite IH. rewrite q_pow_succ.
    assert (Hc : (1#3) * (3#2) == (1#2)) by (unfold Qeq; simpl; lia).
    assert (Hcv : (3#2) * (1#3) == (1#2))
      by (rewrite (Qmult_comm (3#2) (1#3)); exact Hc).
    assert (Hv : (3#2) - 1 == (1#2)) by (unfold Qeq; simpl; lia).
    transitivity ((3#2) - (1#2) * q_pow (1#3) n').
    + rewrite <- Hv. ring.
    + rewrite <- Hcv. rewrite <- Qmult_assoc. ring.
Qed.

(* Upper bound on the geometric sum: sum_{i<n} (1/3)^i <= 3/2 *)
Lemma vt_geom_le : forall n : nat,
  Qle (sum_upto n (fun i : nat => q_pow (1#3) i)) (3#2).
Proof.
  intro n. rewrite vt_geom_closed.
  apply (Qle_trans _ ((3#2) * 1)).
  - apply (sc_qmult_le_l (1 - q_pow (1#3) n) 1 (3#2)).
    + apply (proj2 (Qle_minus_iff (1 - q_pow (1#3) n) 1)).
      assert (Hr : 1 - (1 - q_pow (1#3) n) == q_pow (1#3) n) by ring.
      rewrite Hr. apply q_pow_nonneg. unfold Qle; simpl; lia.
    + unfold Qle; simpl; lia.
  - apply qeq_le. apply Qmult_1_r.
Qed.

(* Sums preserve the pointwise order *)
Lemma vt_sum_upto_le : forall (f g : nat -> Q) (d : nat),
  (forall i : nat, Qle (f i) (g i)) -> Qle (sum_upto d f) (sum_upto d g).
Proof.
  intros f g d H. induction d as [| d' IH]; cbn [sum_upto].
  - unfold Qle; simpl; lia.
  - apply Qplus_le_compat; [exact IH | exact (H d')].
Qed.

(* Triangle inequality for the absolute value of a sum *)
Lemma vt_sum_abs_le : forall (g : nat -> Q) (d : nat),
  Qle (Qabs (sum_upto d g)) (sum_upto d (fun i : nat => Qabs (g i))).
Proof.
  intros g d. induction d as [| d' IH]; cbn [sum_upto].
  - unfold Qle; simpl; lia.
  - apply (Qle_trans _ (Qabs (sum_upto d' g) + Qabs (g d'))).
    + apply Qabs_triangle.
    + apply Qplus_le_compat; [exact IH | apply Qle_refl].
Qed.

(* The shift identity for sums (difference of shifted sums) *)
Lemma vt_sum_upto_shift : forall (f : nat -> Q) (p d : nat),
  sum_upto (p + d) f - sum_upto p f == sum_upto d (fun i : nat => f ((p + i)%nat)).
Proof.
  intros f p d. induction d as [| d' IH].
  - rewrite Nat.add_0_r. cbn [sum_upto]. ring.
  - assert (Hs : ((p + Datatypes.S d') = Datatypes.S (p + d'))%nat) by lia.
    rewrite Hs.
    cbn [sum_upto].
    assert (H1 : sum_upto (Datatypes.S (p + d')) f - sum_upto p f ==
                 (sum_upto (p + d') f - sum_upto p f) + f ((p + d')%nat)).
    { change (sum_upto (Datatypes.S (p + d')) f)
        with (sum_upto (p + d') f + f ((p + d')%nat)).
      ring. }
    rewrite H1. setoid_rewrite IH. reflexivity.
Qed.

(* ============================================================ *)
(* Section 2. Main tail bound: |cos_partial k x - cos_partial m x| <= (3/2) * t_{m+1} *)
(* ============================================================ *)

Lemma vt_cos_partial_tail_bound : forall (x : Q) (m k : nat),
  Qle 0 x -> Qle x 2 -> (2 <= m)%nat -> (m <= k)%nat ->
  Qle (Qabs (cos_partial k x - cos_partial m x))
      ((3#2) * cos_abs_term x (Datatypes.S m)).
Proof.
  intros x m k Hx0 Hx2 Hm Hmk.
  assert (Hd : (Datatypes.S k = Datatypes.S m + (k - m))%nat) by lia.
  rewrite (sc_cos_partial_upto k x). rewrite (sc_cos_partial_upto m x).
  rewrite Hd.
  setoid_rewrite (vt_sum_upto_shift (fun j : nat => cos_term j x)
                    (Datatypes.S m) ((k - m)%nat)).
  apply (Qle_trans _ (sum_upto (k - m)
           (fun i : nat => cos_abs_term x ((Datatypes.S m + i)%nat)))).
  - apply (Qle_trans _ (sum_upto (k - m)
           (fun i : nat => Qabs (cos_term ((Datatypes.S m + i)%nat) x)))).
    + exact (vt_sum_abs_le (fun i : nat => cos_term ((Datatypes.S m + i)%nat) x) (k - m)).
    + assert (Habs : sum_upto (k - m)
             (fun i : nat => Qabs (cos_term ((Datatypes.S m + i)%nat) x)) ==
             sum_upto (k - m) (fun i : nat => cos_abs_term x ((Datatypes.S m + i)%nat))).
      { apply sum_upto_ext. intro i. apply vt_cos_term_abs. exact Hx0. }
      rewrite Habs. apply Qle_refl.
  - assert (Hm0 : (1 <= Datatypes.S m)%nat) by lia.
    assert (Hpt : forall i : nat,
      Qle (cos_abs_term x (Datatypes.S m + i))
          (cos_abs_term x (Datatypes.S m) * q_pow (1#3) i)).
    { intro i.
      apply (Qle_trans _ (q_pow (1#3) i * cos_abs_term x (Datatypes.S m))).
      - exact (vt_abs_term_decay x (Datatypes.S m) i Hx0 Hx2 Hm0).
      - apply qeq_le. apply Qmult_comm. }
    assert (Ht0 : Qle 0 (cos_abs_term x (Datatypes.S m)))
      by (apply vt_abs_term_nonneg; exact Hx0).
    apply (Qle_trans _ (cos_abs_term x (Datatypes.S m) *
              sum_upto (k - m) (fun i : nat => q_pow (1#3) i))).
    + rewrite <- (sum_upto_scale (k - m) (cos_abs_term x (Datatypes.S m))
                    (fun i : nat => q_pow (1#3) i)).
      apply vt_sum_upto_le. exact Hpt.
    + apply (Qle_trans _ (cos_abs_term x (Datatypes.S m) * (3#2))).
      * exact (sc_qmult_le_l (sum_upto (k - m) (fun i : nat => q_pow (1#3) i))
                (3#2) (cos_abs_term x (Datatypes.S m)) (vt_geom_le (k - m)) Ht0).
      * apply qeq_le. apply Qmult_comm.
Qed.

(* Lower edge of the tail bound: [P m - B <= P k] (for [k >= m]) *)
Lemma vt_cos_tail_shift_le : forall (x : Q) (m k : nat),
  Qle 0 x -> Qle x 2 -> (2 <= m)%nat -> (m <= k)%nat ->
  Qle (cos_partial m x - (3#2) * cos_abs_term x (Datatypes.S m)) (cos_partial k x).
Proof.
  intros x m k Hx0 Hx2 Hm Hmk.
  assert (HB := vt_cos_partial_tail_bound x m k Hx0 Hx2 Hm Hmk).
  apply (proj1 (Qabs_Qle_condition (cos_partial k x - cos_partial m x)
          ((3#2) * cos_abs_term x (Datatypes.S m)))) in HB.
  destruct HB as [HB1 HB2].
  apply (Qle_trans _ (cos_partial m x + (cos_partial k x - cos_partial m x))).
  - exact (Qplus_le_compat (cos_partial m x) (cos_partial m x)
             (- ((3#2) * cos_abs_term x (Datatypes.S m)))
             (cos_partial k x - cos_partial m x) (Qle_refl _) HB1).
  - apply qeq_le. ring.
Qed.

(* Upper edge of the tail bound: [P k <= P m + B] *)
Lemma vt_cos_tail_shift_ub : forall (x : Q) (m k : nat),
  Qle 0 x -> Qle x 2 -> (2 <= m)%nat -> (m <= k)%nat ->
  Qle (cos_partial k x) (cos_partial m x + (3#2) * cos_abs_term x (Datatypes.S m)).
Proof.
  intros x m k Hx0 Hx2 Hm Hmk.
  assert (HB := vt_cos_partial_tail_bound x m k Hx0 Hx2 Hm Hmk).
  apply (proj1 (Qabs_Qle_condition (cos_partial k x - cos_partial m x)
          ((3#2) * cos_abs_term x (Datatypes.S m)))) in HB.
  destruct HB as [HB1 HB2].
  apply (Qle_trans _ ((cos_partial k x - cos_partial m x) + cos_partial m x)).
  - apply qeq_le. ring.
  - apply (Qle_trans _ ((3#2) * cos_abs_term x (Datatypes.S m) + cos_partial m x)).
    + exact (Qplus_le_compat (cos_partial k x - cos_partial m x)
               ((3#2) * cos_abs_term x (Datatypes.S m)) (cos_partial m x)
               (cos_partial m x) HB2 (Qle_refl _)).
    + apply qeq_le. ring.
Qed.

(* ============================================================ *)
(* Section 3. Explicit endpoint sign certificates (fixed point K = 5) *)
(* ============================================================ *)

(* [cos_partial 5 (3/2) - (3/2) * t_6] is positive (a concrete rational margin) *)
Lemma vt_three_halves_pos : forall k : nat, (5 <= k)%nat -> Qlt 0 (cos_partial k (3#2)).
Proof.
  intros k Hk.
  assert (Hc1 : Qle 0 (3#2)) by (unfold Qle; simpl; lia).
  assert (Hc2 : Qle (3#2) 2) by (unfold Qle; simpl; lia).
  assert (Hc3 : (2 <= 5)%nat) by lia.
  assert (Hlow := vt_cos_tail_shift_le (3#2) 5 k Hc1 Hc2 Hc3 Hk).
  assert (Hpos : Qlt 0 (cos_partial 5 (3#2)
    - (3#2) * cos_abs_term (3#2) (Datatypes.S 5)))
    by (vm_compute; reflexivity).
  apply (Qlt_le_trans 0 (cos_partial 5 (3#2)
    - (3#2) * cos_abs_term (3#2) (Datatypes.S 5)) (cos_partial k (3#2))
    Hpos Hlow).
Qed.

(* [cos_partial 5 (5/3) + (3/2) * t_6] is negative (a concrete rational margin) *)
Lemma vt_five_thirds_neg : forall k : nat, (5 <= k)%nat -> Qlt (cos_partial k (5#3)) 0.
Proof.
  intros k Hk.
  assert (Hc1 : Qle 0 (5#3)) by (unfold Qle; simpl; lia).
  assert (Hc2 : Qle (5#3) 2) by (unfold Qle; simpl; lia).
  assert (Hc3 : (2 <= 5)%nat) by lia.
  assert (Hup := vt_cos_tail_shift_ub (5#3) 5 k Hc1 Hc2 Hc3 Hk).
  assert (Hneg : Qlt (cos_partial 5 (5#3)
    + (3#2) * cos_abs_term (5#3) (Datatypes.S 5)) 0)
    by (vm_compute; reflexivity).
  apply (Qle_lt_trans (cos_partial k (5#3))
    (cos_partial 5 (5#3) + (3#2) * cos_abs_term (5#3) (Datatypes.S 5)) 0
    Hup Hneg).
Qed.

(* Top-level certificates carried at the [Set] level *)
Lemma vt_three_halves_pos_T : forall k : nat, (5 <= k)%nat -> QltT 0 (cos_partial k (3#2)).
Proof. intros k Hk. apply Qlt_to_QltT. apply vt_three_halves_pos. exact Hk. Qed.

Lemma vt_five_thirds_neg_T : forall k : nat, (5 <= k)%nat -> QltT (cos_partial k (5#3)) 0.
Proof. intros k Hk. apply Qlt_to_QltT. apply vt_five_thirds_neg. exact Hk. Qed.

(* ============================================================ *)
(* Section 4. The bisection body *)
(* ============================================================ *)

Definition vt_mid (a b : Q) : Q := (a + b) * (1#2).

Lemma vt_mid_lt_r : forall a b : Q, Qlt a b -> Qlt (vt_mid a b) b.
Proof.
  intros a b Hab. apply (proj2 (Qlt_minus_iff (vt_mid a b) b)).
  assert (Hbm : b - vt_mid a b == (b - a) * (1#2))
    by (unfold vt_mid; field; try (unfold Qeq; simpl; lia)).
  rewrite Hbm. apply Qmult_lt_0_compat.
  - apply (proj1 (Qlt_minus_iff a b)). exact Hab.
  - compute; reflexivity.
Qed.

Lemma vt_mid_gt_l : forall a b : Q, Qlt a b -> Qlt a (vt_mid a b).
Proof.
  intros a b Hab. apply (proj2 (Qlt_minus_iff a (vt_mid a b))).
  assert (Hma : vt_mid a b - a == (b - a) * (1#2))
    by (unfold vt_mid; field; try (unfold Qeq; simpl; lia)).
  rewrite Hma. apply Qmult_lt_0_compat.
  - apply (proj1 (Qlt_minus_iff a b)). exact Hab.
  - compute; reflexivity.
Qed.

(* Transport of a Boolean equality to a Set-valued [Id] *)
Lemma vt_eq_to_Id : forall (x y : bool), x = y -> Id x y.
Proof. intros x y H. destruct H. exact (@id_refl bool x). Qed.

(* The negated branch of the non-strict order Boolean: the strict-order face *)
Lemma vt_Qle_bool_false : forall x y : Q, Qle_bool x y = false -> Qlt y x.
Proof.
  intros x y H.
  assert (Hnot : ~ Qle x y).
  { intro Hle. rewrite (proj2 (Qle_bool_iff x y) Hle) in H. discriminate H. }
  apply Qnot_le_lt. exact Hnot.
Qed.

Fixpoint vt_bisect (K : nat) (a b : Q) (Hab : Qlt a b) (n : nat) : Q * Q :=
  match n with
  | 0%nat => (a, b)
  | Datatypes.S n' =>
      if Qle_bool (cos_partial K (vt_mid a b)) 0
      then vt_bisect K a (vt_mid a b) (vt_mid_gt_l a b Hab) n'
      else vt_bisect K (vt_mid a b) b (vt_mid_lt_r a b Hab) n'
  end.

Lemma vt_bisect_S : forall (K : nat) (a b : Q) (Hab : Qlt a b) (n : nat),
  vt_bisect K a b Hab (Datatypes.S n) =
  (if Qle_bool (cos_partial K (vt_mid a b)) 0
   then vt_bisect K a (vt_mid a b) (vt_mid_gt_l a b Hab) n
   else vt_bisect K (vt_mid a b) b (vt_mid_lt_r a b Hab) n).
Proof. intros. reflexivity. Qed.

(* The five-part scanning invariant: nested lower bound / nested upper bound / closed form of the length / left endpoint strictly positive / right endpoint nonpositive *)
Lemma vt_bisect_spec : forall (n K : nat) (a b : Q) (Hab : Qlt a b),
  Qle 0 a -> Qle b 2 -> (2 <= K)%nat ->
  QltT 0 (cos_partial K a) -> QleT' (cos_partial K b) 0 ->
  And (Qle a (fst (vt_bisect K a b Hab n)))
      (And (Qle (snd (vt_bisect K a b Hab n)) b)
      (And (Qeq ((b - a) * q_pow (1#2) n)
                (snd (vt_bisect K a b Hab n) - fst (vt_bisect K a b Hab n)))
      (And (QltT 0 (cos_partial K (fst (vt_bisect K a b Hab n))))
           (QleT' (cos_partial K (snd (vt_bisect K a b Hab n))) 0)))).
Proof.
  induction n as [| n IH]; intros K a b Hab H0a Hb2 HK Hpa Hpb.
  - split; [apply Qle_refl | ]. split; [apply Qle_refl | ].
    split.
    + assert (Hp0 : q_pow (1#2) 0 == 1) by reflexivity.
      rewrite Hp0. apply Qmult_1_r.
    + split; assumption.
  - rewrite vt_bisect_S. destruct (Qle_bool (cos_partial K (vt_mid a b)) 0) eqn:EQ.
    + (* midpoint nonpositive: left half *)
      destruct (IH K a (vt_mid a b) (vt_mid_gt_l a b Hab) H0a
        (Qle_trans (vt_mid a b) b 2
          (Qlt_le_weak (vt_mid a b) b (vt_mid_lt_r a b Hab)) Hb2) HK Hpa
        (vt_eq_to_Id _ _ EQ)) as [I1 [I2 [I3 [I4 I5]]]].
      split; [exact I1 | ].
      split.
      * apply (Qle_trans (snd (vt_bisect K a (vt_mid a b) (vt_mid_gt_l a b Hab) n))
              (vt_mid a b) b);
          [exact I2 | apply Qlt_le_weak; apply vt_mid_lt_r; exact Hab].
      * split.
        -- setoid_rewrite <- I3. rewrite q_pow_succ.
           assert (Hma : vt_mid a b - a == (b - a) * (1#2))
             by (unfold vt_mid; field; try (unfold Qeq; simpl; lia)).
           setoid_rewrite Hma. ring.
        -- split; [exact I4 | exact I5].
    + (* midpoint strictly positive: right half *)
      destruct (IH K (vt_mid a b) b (vt_mid_lt_r a b Hab)
        (Qle_trans 0 a (vt_mid a b) H0a
          (Qlt_le_weak a (vt_mid a b) (vt_mid_gt_l a b Hab)))
        Hb2 HK (Qlt_to_QltT 0 (cos_partial K (vt_mid a b))
                  (vt_Qle_bool_false (cos_partial K (vt_mid a b)) 0 EQ)) Hpb)
        as [I1 [I2 [I3 [I4 I5]]]].
      split.
      * apply (Qle_trans a (vt_mid a b)
              (fst (vt_bisect K (vt_mid a b) b (vt_mid_lt_r a b Hab) n))).
        -- apply Qlt_le_weak. apply vt_mid_gt_l. exact Hab.
        -- exact I1.
      * split.
        -- exact I2.
        -- split.
           ++ setoid_rewrite <- I3. rewrite q_pow_succ.
              assert (Hbm : b - vt_mid a b == (b - a) * (1#2))
                by (unfold vt_mid; field; try (unfold Qeq; simpl; lia)).
              setoid_rewrite Hbm. ring.
           ++ split; [exact I4 | exact I5].
Qed.

(* ============================================================ *)
(* Section 5. Fixed-point assembly on [3/2, 5/3] and downstream interfaces *)
(* ============================================================ *)

(* The step-[n] bracketing interval, carried as a two-level [sigT] *)
Lemma vt_scan_bracket : forall n : nat,
  sigT (fun iv : Q * Q =>
    And (QleT' (3#2) (fst iv))
      (And (QleT' (fst iv) (snd iv))
        (And (QleT' (snd iv) (5#3))
          (And (Qeq ((((5#3) - (3#2))) * q_pow (1#2) n) (snd iv - fst iv))
            (And (QltT 0 (cos_partial 5 (fst iv)))
                 (QleT' (cos_partial 5 (snd iv)) 0)))))).
Proof.
  intro n.
  assert (Hab35 : Qlt (3#2) (5#3)) by (compute; reflexivity).
  assert (H0a : Qle 0 (3#2)) by (unfold Qle; simpl; lia).
  assert (Hb2 : Qle (5#3) 2) by (unfold Qle; simpl; lia).
  assert (HK : (2 <= 5)%nat) by lia.
  assert (Hap : QltT 0 (cos_partial 5 (3#2)))
    by (apply Qlt_to_QltT; apply vt_three_halves_pos; lia).
  assert (Hbn : QleT' (cos_partial 5 (5#3)) 0)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply vt_five_thirds_neg; lia).
  destruct (vt_bisect_spec n 5 (3#2) (5#3) Hab35 H0a Hb2 HK Hap Hbn)
    as [S1 [S2 [S3 [S4 S5]]]].
  assert (Hfs : Qle (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
                    (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))).
  { apply (proj2 (Qle_minus_iff (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
                   (snd (vt_bisect 5 (3#2) (5#3) Hab35 n)))).
    rewrite <- S3. apply Qmult_le_0_compat.
    - unfold Qle; simpl; lia.
    - apply q_pow_nonneg. unfold Qle; simpl; lia. }
  exists (vt_bisect 5 (3#2) (5#3) Hab35 n).
  split; [apply Qle_to_QleT'; exact S1 | ].
  split; [apply Qle_to_QleT'; exact Hfs | ].
  split; [apply Qle_to_QleT'; exact S2 | ].
  split; [exact S3 | ].
  split; [exact S4 | exact S5].
Qed.

(* The function value at the left endpoint of the bracket is at most the Lipschitz constant times the interval length (shrinking to zero with [n]) *)
Lemma vt_bisect_left_val_le : forall (n : nat) (Hab35 : Qlt (3#2) (5#3)),
  Qle (cos_partial 5 (fst (vt_bisect 5 (3#2) (5#3) Hab35 n)))
      (leibsep_abssum_cos (5#3) 5 * ((((5#3) - (3#2))) * q_pow (1#2) n)).
Proof.
  intros n Hab35.
  assert (H0a : Qle 0 (3#2)) by (unfold Qle; simpl; lia).
  assert (Hb2 : Qle (5#3) 2) by (unfold Qle; simpl; lia).
  assert (HK : (2 <= 5)%nat) by lia.
  assert (Hap : QltT 0 (cos_partial 5 (3#2)))
    by (apply Qlt_to_QltT; apply vt_three_halves_pos; lia).
  assert (Hbn : QleT' (cos_partial 5 (5#3)) 0)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply vt_five_thirds_neg; lia).
  destruct (vt_bisect_spec n 5 (3#2) (5#3) Hab35 H0a Hb2 HK Hap Hbn)
    as [S1 [S2 [S3 [S4 S5]]]].
  assert (Hfs : Qle (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
                    (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))).
  { apply (proj2 (Qle_minus_iff (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
                   (snd (vt_bisect 5 (3#2) (5#3) Hab35 n)))).
    rewrite <- S3. apply Qmult_le_0_compat.
    - unfold Qle; simpl; lia.
    - apply q_pow_nonneg. unfold Qle; simpl; lia. }
  assert (Habsf : Qabs (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
                  == fst (vt_bisect 5 (3#2) (5#3) Hab35 n)).
  { apply Qabs_pos. apply (Qle_trans 0 (3#2)
      (fst (vt_bisect 5 (3#2) (5#3) Hab35 n)));
      [unfold Qle; simpl; lia | exact S1]. }
  assert (Habss : Qabs (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))
                  == snd (vt_bisect 5 (3#2) (5#3) Hab35 n)).
  { apply Qabs_pos. apply (Qle_trans 0
      (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
      (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))).
    - apply (Qle_trans 0 (3#2)
        (fst (vt_bisect 5 (3#2) (5#3) Hab35 n)));
        [unfold Qle; simpl; lia | exact S1].
    - exact Hfs. }
  assert (Habsd : Qabs (snd (vt_bisect 5 (3#2) (5#3) Hab35 n)
                        - fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
                  == snd (vt_bisect 5 (3#2) (5#3) Hab35 n)
                     - fst (vt_bisect 5 (3#2) (5#3) Hab35 n)).
  { apply Qabs_pos. exact (proj1 (Qle_minus_iff
      (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
      (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))) Hfs). }
  assert (HB0 : QleT' 0 (5#3)) by (apply Qle_to_QleT'; unfold Qle; simpl; lia).
  assert (HB1 : QleT' (Qabs (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))) (5#3)).
  { apply Qle_to_QleT'. rewrite Habsf.
    apply (Qle_trans (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
            (snd (vt_bisect 5 (3#2) (5#3) Hab35 n)) (5#3));
      [exact Hfs | exact S2]. }
  assert (HB2 : QleT' (Qabs (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))) (5#3)).
  { apply Qle_to_QleT'. rewrite Habss. exact S2. }
  assert (HL : Qle (Qabs (cos_partial 5 (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
                          - cos_partial 5 (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))))
                   (Qabs (fst (vt_bisect 5 (3#2) (5#3) Hab35 n)
                        - snd (vt_bisect 5 (3#2) (5#3) Hab35 n))
                     * leibsep_abssum_cos (5#3) 5)).
  { apply QleT'_to_Qle.
    exact (leibsep_cos_partial_lipschitz
            (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
            (snd (vt_bisect 5 (3#2) (5#3) Hab35 n)) (5#3) 5 HB0 HB1 HB2). }
  assert (Habsd2 : Qabs (fst (vt_bisect 5 (3#2) (5#3) Hab35 n)
                         - snd (vt_bisect 5 (3#2) (5#3) Hab35 n))
                   == snd (vt_bisect 5 (3#2) (5#3) Hab35 n)
                      - fst (vt_bisect 5 (3#2) (5#3) Hab35 n)).
  { rewrite (Qabs_Qminus (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
              (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))).
    exact Habsd. }
  rewrite Habsd2 in HL. rewrite <- S3 in HL.
  (* P(fst) <= P(fst) - P(snd) (since P(snd) <= 0); then <= |...| <= L * interval length *)
  assert (Hneg : Qle 0 (- cos_partial 5 (snd (vt_bisect 5 (3#2) (5#3) Hab35 n)))).
  { apply (Qle_trans _ (- 0)); [unfold Qle; simpl; lia | ].
    apply Qopp_le_compat. apply QleT'_to_Qle. exact S5. }
  apply (Qle_trans _ (cos_partial 5 (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
        - cos_partial 5 (snd (vt_bisect 5 (3#2) (5#3) Hab35 n)))).
  - apply (Qle_trans _ (cos_partial 5 (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
          + (- cos_partial 5 (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))))).
    + apply Qle_plus_nonneg_r. exact Hneg.
    + apply qeq_le. ring.
  - apply (Qle_trans _ (Qabs (cos_partial 5 (fst (vt_bisect 5 (3#2) (5#3) Hab35 n))
          - cos_partial 5 (snd (vt_bisect 5 (3#2) (5#3) Hab35 n))))).
    + apply Qle_Qabs.
    + apply (Qle_trans _ (((((5#3) - (3#2))) * q_pow (1#2) n)
            * leibsep_abssum_cos (5#3) 5)).
      * exact HL.
      * apply qeq_le. ring.
Qed.

  (* Strictly decreasing lower bound: inside the interval, [v - u] is at least half of [(v^2 - u^2)/6] (direct consumption of the difference-bound lemma [sc_cos_partial_diff_le]) *)
Lemma vt_cos_decr_half : forall (K : nat) (u v : Q),
  (2 <= K)%nat -> Qle (3#2) u -> Qle u v -> Qle v (5#3) ->
  Qle (cos_partial K v) (cos_partial K u - (v - u) * (1#2)).
Proof.
  intros K u v HK Hu Huv Hv.
  assert (H032 : Qle 0 (3#2)) by (unfold Qle; simpl; lia).
  assert (H52 : Qle (5#3) 2) by (unfold Qle; simpl; lia).
  assert (HD := sc_cos_partial_diff_le K u v
    (Qle_trans 0 (3#2) u H032 Hu) Huv (Qle_trans v (5#3) 2 Hv H52) HK).
  (* (v - u) * 3 <= v^2 - u^2 (for [u, v >= 3/2], so [v + u >= 3]) *)
  assert (Hvu3 : Qle ((v - u) * 3) (v * v - u * u)).
  { apply (proj2 (Qle_minus_iff ((v - u) * 3) (v * v - u * u))).
    assert (He : (v * v - u * u) - (v - u) * 3 == (v - u) * (v + u - 3)) by ring.
    rewrite He. apply Qmult_le_0_compat.
    - apply (proj1 (Qle_minus_iff u v)). exact Huv.
    - assert (Huv3 : Qle ((3#2) + (3#2)) (u + v)).
      { apply Qplus_le_compat; [exact Hu | exact (Qle_trans (3#2) u v Hu Huv)]. }
      assert (Hc33 : ((3#2) + (3#2)) == 3) by (unfold Qeq; simpl; lia).
      apply (Qle_trans _ ((u + v) - ((3#2) + (3#2)))).
      + apply (proj1 (Qle_minus_iff ((3#2) + (3#2)) (u + v))). exact Huv3.
      + apply qeq_le. rewrite Hc33. ring. }
  assert (Hc16 : Qle 0 (1#6)) by (unfold Qle; simpl; lia).
  assert (Hc61 : (1#6) * 3 == (1#2)) by (unfold Qeq; simpl; lia).
  assert (Hhalf : Qle ((v - u) * (1#2)) ((v * v - u * u) * (1#6))).
  { assert (Hs1 := sc_qmult_le_l ((v - u) * 3) (v * v - u * u) (1#6) Hvu3 Hc16).
    apply (Qle_trans _ ((v - u) * ((1#6) * 3))).
    - apply qeq_le. rewrite Hc61. reflexivity.
    - apply (Qle_trans _ ((1#6) * ((v - u) * 3))).
      + apply qeq_le. ring.
      + apply (Qle_trans _ ((1#6) * (v * v - u * u))).
        * exact Hs1.
        * apply qeq_le. ring. }
  apply (Qle_trans _ (cos_partial K u - (v * v - u * u) * (1#6))).
  - exact HD.
  - apply (Qle_trans _ (cos_partial K u + (- ((v * v - u * u) * (1#6))))).
    + apply qeq_le. ring.
    + apply Qplus_le_compat; [apply Qle_refl | ].
      exact (Qopp_le_compat ((v - u) * (1#2)) ((v * v - u * u) * (1#6)) Hhalf).
Qed.

(* ============================================================ *)
(* Assumption audit (anchored at line starts) *)
(* ============================================================ *)

Print Assumptions vt_cos_partial_tail_bound.
Print Assumptions vt_three_halves_pos_T.
Print Assumptions vt_five_thirds_neg_T.
Print Assumptions vt_cos_decr_half.
Print Assumptions vt_bisect_spec.
Print Assumptions vt_scan_bracket.
Print Assumptions vt_bisect_left_val_le.
