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
(** * PiCosApproxRoot.v

    Mission.  The main existence theorem for a zero of the cosine, over
    the rational arithmetic of [Q]: for every [eps > 0], an explicit
    [x] in [(3/2, 5/3)] together with a truncation index [N] are
    produced such that [|cos_partial k x| < eps] whenever [N <= k].
    Proof route: the five-part bisection invariant ([vt_bisect_spec])
    is instantiated at the exponent [A], yielding the bracketing
    interval together with the endpoint signs; the strictly decreasing
    lower bound ([vt_cos_decr_half]) presses the function value at the
    interval midpoint into the endpoint span; the span contracts with
    the interval length through [leibsep_cos_partial_lipschitz]; the
    truncation drift is controlled by the alternating tail bound
    ([vt_cos_partial_tail_bound]) at the same anchor exponent; and the
    tail term is dispatched, through the step decay
    ([vt_abs_term_decay]), to the half-power Archimedean witness.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [ZArith.ZArith], [Arith.PeanoNat], [Setoid], [Morphisms], [Lia];
    this development, [PiCompareT] ([QltT]/[QleT']), [PiKernelSlack]
    ([cos_partial]/[q_pow]/[q_fact]/
    [leibsep_cos_partial_lipschitz]/[And]), [PiVertexPolyDiff]
    ([vt_qpos_neq]), [PiCosTailScan] (the [vt_*] family).

    References.  [S10_KVQuantTrig.v], [approx_root_cos] ([:7982]),
    restated over the rationals [Q], with the return face carried as a
    [sig] (the consumption form of [S10] [cos_zero_seq] at [:8119]).

    Constructivity.  The main theorem statement is carried as a [sig]
    (at the [Set] level); within proofs the predicates are the stdlib
    [Qle]/[Qlt], purely constructive [Prop]; assumption-free and fully
    proved, with no non-constructive principles.

    Build.  [coqc -native-compiler no -q -Q . "" PiCosApproxRoot.v]
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
Require Import PiCosTailScan.

(* ============================================================ *)
(* Section 1. The half-power machine (positivity, monotonicity, reciprocal bounds and the Archimedean witness) and small [Q]-order lemmas *)
(* ============================================================ *)

(* The half power is strictly positive: [0 < (1/2)^n] *)
Lemma vt_pos_half_pow : forall n : nat, Qlt 0 (q_pow (1#2) n).
Proof.
  intro n. induction n as [| m IH].
  - unfold Qlt. simpl. reflexivity.
  - apply (Qmult_lt_0_compat (1#2) (q_pow (1#2) m)).
    + unfold Qlt. simpl. reflexivity.
    + exact IH.
Qed.

(* Subtracting a nonnegative term: [0 <= t] implies [u - t <= u] *)
Lemma vt_sub_le_r : forall (u t : Q), Qle 0 t -> Qle (u - t) u.
Proof.
  intros u t Ht.
  assert (Hneg : Qle (- t) 0)
    by (apply (Qle_trans _ (- 0));
        [apply (Qopp_le_compat 0 t Ht) | unfold Qle; simpl; lia]).
  apply (Qle_trans _ (u + - t)).
  - apply qeq_le. reflexivity.
  - apply (Qle_trans _ (u + 0)).
    + apply (Qplus_le_compat u u (- t) 0 (Qle_refl u) Hneg).
    + apply qeq_le. apply (Qplus_0_r u).
Qed.

(* Adding a nonnegative term: [0 <= t] implies [u <= u + t] *)
Lemma vt_add_le_r : forall (u t : Q), Qle 0 t -> Qle u (u + t).
Proof.
  intros u t Ht. apply (Qle_trans _ (u + 0)).
  - apply qeq_le. symmetry. apply (Qplus_0_r u).
  - apply (Qplus_le_compat u u 0 t (Qle_refl u) Ht).
Qed.

(* Monotonicity under left multiplication: [0 <= z] implies [z * x <= z * y] *)
Lemma vt_qmult_le_compat_l : forall (x y z : Q), Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z Hxy H0z.
  apply (Qle_trans _ (x * z)).
  - apply qeq_le. apply Qmult_comm.
  - apply (Qle_trans _ (y * z)).
    + exact (Qmult_le_compat_r x y z Hxy H0z).
    + apply qeq_le. apply Qmult_comm.
Qed.

(* One nonincreasing step of the half power: (1/2)^(S n) <= (1/2)^n (same derivation as [S07_RealSetoidExpLog.v:4190]) *)
Lemma vt_q_pow_half_le : forall n : nat, Qle (q_pow (1#2) (Datatypes.S n)) (q_pow (1#2) n).
Proof.
  intro n.
  apply (Qle_trans _ ((1#2) * q_pow (1#2) n) _).
  - apply qeq_le. reflexivity.
  - apply (Qle_trans _ (1 * q_pow (1#2) n) _).
    + apply (Qmult_le_compat_r (1#2) 1 (q_pow (1#2) n)).
      * change (Qle (1#2) 1). unfold Qle. simpl. lia.
      * apply (q_pow_nonneg (1#2) n).
        change (Qle 0 (1#2)). unfold Qle. simpl. lia.
    + apply qeq_le. ring.
Qed.

(* Monotonicity of the half power: [m <= n] implies [(1/2)^n <= (1/2)^m] (same derivation as [S07_RealSetoidExpLog.v:5095]) *)
Lemma vt_q_pow_half_mono : forall m n : nat,
  (m <= n)%nat -> Qle (q_pow (1#2) n) (q_pow (1#2) m).
Proof.
  intros m n Hmn. induction Hmn as [| n' Hrec IH]; [apply Qle_refl | ].
  apply (Qle_trans _ (q_pow (1#2) n') _).
  - apply vt_q_pow_half_le.
  - exact IH.
Qed.

(* Base monotonicity: [0 <= a <= b] implies [a^n <= b^n] *)
Lemma vt_q_pow_base_mono : forall (a b : Q) (n : nat),
  Qle 0 a -> Qle a b -> Qle (q_pow a n) (q_pow b n).
Proof.
  intros a b n H0a Hab. induction n as [| m IH].
  - apply Qle_refl.
  - assert (H0b : Qle 0 b) by (apply (Qle_trans 0 a b); assumption).
    rewrite (q_pow_succ a m). rewrite (q_pow_succ b m).
    apply (Qle_trans _ (b * q_pow a m)).
    + exact (Qmult_le_compat_r a b (q_pow a m) Hab (q_pow_nonneg a m H0a)).
    + apply (Qle_trans _ (q_pow a m * b)).
      * apply qeq_le. apply Qmult_comm.
      * apply (Qle_trans _ (q_pow b m * b)).
        -- exact (Qmult_le_compat_r (q_pow a m) (q_pow b m) b IH H0b).
        -- apply qeq_le. apply Qmult_comm.
Qed.

(* The half-power reciprocal product bound: (1/2)^(S n) * (S n) <= 1 *)
Lemma vt_half_pow_mul_le : forall n : nat,
  Qle (q_pow (1#2) (Datatypes.S n) * (Z.of_nat (Datatypes.S n) # 1)) 1.
Proof.
  intro n. induction n as [| m IH].
  - unfold Qle. simpl. lia.
  - assert (Hstep : Qle ((1#2) * (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1))
                        (Z.of_nat (Datatypes.S m) # 1)).
    { unfold Qle. simpl. rewrite ?Z.mul_1_r. lia. }
    assert (Hnn : Qle 0 (q_pow (1#2) (Datatypes.S m)))
      by (apply q_pow_nonneg; change (Qle 0 (1#2)); unfold Qle; simpl; lia).
    rewrite (q_pow_succ (1#2) (Datatypes.S m)).
    apply (Qle_trans _
      (((1#2) * (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1))
        * q_pow (1#2) (Datatypes.S m))).
    + apply qeq_le. ring.
    + apply (Qle_trans _
        (((Z.of_nat (Datatypes.S m) # 1)) * q_pow (1#2) (Datatypes.S m))).
      * exact (Qmult_le_compat_r _ _ _ Hstep Hnn).
      * apply (Qle_trans _
          (q_pow (1#2) (Datatypes.S m) * (Z.of_nat (Datatypes.S m) # 1))).
        -- apply qeq_le. apply Qmult_comm.
        -- exact IH.
Qed.

(* The half-power reciprocal bound: (1/2)^(S n) <= 1/(S n) *)
Lemma vt_half_pow_inv : forall n : nat,
  Qle (q_pow (1#2) (Datatypes.S n)) (/ (Z.of_nat (Datatypes.S n) # 1)).
Proof.
  intro n.
  assert (Hcpos : Qlt 0 (Z.of_nat (Datatypes.S n) # 1)) by (unfold Qlt; simpl; lia).
  assert (Hcc : (Z.of_nat (Datatypes.S n) # 1) * (/ (Z.of_nat (Datatypes.S n) # 1)) == 1)
    by (apply (Qmult_inv_r (Z.of_nat (Datatypes.S n) # 1) (vt_qpos_neq _ Hcpos))).
  assert (Hcpos' : Qle 0 (/ (Z.of_nat (Datatypes.S n) # 1)))
    by (apply (Qlt_le_weak 0 (/ (Z.of_nat (Datatypes.S n) # 1)));
        apply (Qinv_lt_0_compat (Z.of_nat (Datatypes.S n) # 1)); exact Hcpos).
  assert (HA1 : q_pow (1#2) (Datatypes.S n)
              == q_pow (1#2) (Datatypes.S n) * (Z.of_nat (Datatypes.S n) # 1)
                     * (/ (Z.of_nat (Datatypes.S n) # 1))).
  { rewrite <- Qmult_assoc. rewrite Hcc. symmetry. apply Qmult_1_r. }
  apply (Qle_trans _ (q_pow (1#2) (Datatypes.S n) * (Z.of_nat (Datatypes.S n) # 1)
        * (/ (Z.of_nat (Datatypes.S n) # 1)))).
  - apply qeq_le. exact HA1.
  - apply (Qle_trans _ (1 * (/ (Z.of_nat (Datatypes.S n) # 1)))).
    + apply (Qmult_le_compat_r _ _ _ (vt_half_pow_mul_le n) Hcpos').
    + apply qeq_le. apply Qmult_1_l.
Qed.

(* The half-power Archimedean witness: [D >= 0] and [0 < eps] imply that some [n] satisfies [D * (1/2)^n < eps] *)
Lemma vt_pow_half_arch : forall (D eps : Q),
  Qle 0 D -> Qlt 0 eps -> { n : nat | Qlt (D * q_pow (1#2) n) eps }.
Proof.
  intros D eps HD Heps.
  destruct (Qarchimedean (D / eps)) as [p Hp].
  assert (Hf : (D / eps) * eps == D).
  { unfold Qdiv. rewrite <- Qmult_assoc. rewrite (Qmult_comm (/ eps) eps).
    rewrite (Qmult_inv_r eps (vt_qpos_neq eps Heps)).
    rewrite Qmult_1_r. reflexivity. }
  pose proof (Qmult_lt_compat_r (D / eps) (Z.pos p # 1) eps Heps Hp) as Hm.
  rewrite Hf in Hm.
  assert (Hcpos : Qlt 0 (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1))
    by (unfold Qlt; simpl; lia).
  assert (Hcpos' : Qlt 0 (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)))
    by (apply (Qinv_lt_0_compat (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1));
        exact Hcpos).
  assert (HpnS : Qlt (Z.pos p # 1) (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1))
    by (rewrite <- (positive_nat_Z p); unfold Qlt; simpl; rewrite ?Z.mul_1_r; lia).
  assert (Hcc : (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)
              * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)) == 1)
    by (apply (Qmult_inv_r (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)
               (vt_qpos_neq _ Hcpos))).
  assert (Hinv := vt_half_pow_inv (Pos.to_nat p)).
  assert (T1 : Qle (D * q_pow (1#2) (Datatypes.S (Pos.to_nat p)))
                   (D * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)))).
  { pose proof (Qmult_le_compat_r _ _ _ Hinv HD) as T1x.
    rewrite (Qmult_comm (q_pow (1#2) (Datatypes.S (Pos.to_nat p))) D) in T1x.
    rewrite (Qmult_comm (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)) D) in T1x.
    exact T1x. }
  assert (T2 : Qlt (D * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)))
                   ((Z.pos p # 1) * eps * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1))))
    by exact (Qmult_lt_compat_r _ _ _ Hcpos' Hm).
  assert (T3 : Qlt ((Z.pos p # 1) * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1))) 1).
  { apply (Qlt_le_trans _ ((Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)
              * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)))).
    - exact (Qmult_lt_compat_r _ _ _ Hcpos' HpnS).
    - apply qeq_le. exact Hcc. }
  assert (T4 : Qlt ((Z.pos p # 1) * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)) * eps)
                   (1 * eps))
    by exact (Qmult_lt_compat_r _ _ eps Heps T3).
  assert (Hring1 : (Z.pos p # 1) * eps * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1))
                 == (Z.pos p # 1) * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)) * eps)
    by ring.
  assert (T5 : Qlt ((Z.pos p # 1) * eps * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1))) eps).
  { rewrite Hring1. apply (Qlt_le_trans _ (1 * eps)).
    - exact T4.
    - apply qeq_le. apply Qmult_1_l. }
  exists (Datatypes.S (Pos.to_nat p)).
  apply (Qlt_trans _ ((Z.pos p # 1) * eps * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)))).
  - apply (Qle_lt_trans _ (D * (/ (Z.of_nat (Datatypes.S (Pos.to_nat p)) # 1)))).
    + exact T1.
    + exact T2.
  - exact T5.
Qed.

(* ============================================================ *)
(* Section 2. The machines for terms and sums *)
(* ============================================================ *)

(* Monotonicity of the term absolute value in x: [0 <= x <= y] implies [t_j(x) <= t_j(y)] *)
Lemma vt_abs_term_mono_x : forall (x y : Q) (j : nat),
  Qle 0 x -> Qle x y -> Qle (cos_abs_term x j) (cos_abs_term y j).
Proof.
  intros x y j Hx0 Hxy.
  assert (Hxy0 : Qle 0 y) by (apply (Qle_trans 0 x y); assumption).
  assert (Hxx : Qle (x * x) (y * y)).
  { apply (Qle_trans _ (y * x)).
    - exact (Qmult_le_compat_r x y x Hxy Hx0).
    - apply (Qle_trans _ (x * y)).
      + apply qeq_le. apply Qmult_comm.
      + exact (Qmult_le_compat_r x y y Hxy Hxy0). }
  assert (Hnum : Qle (q_pow (x * x) j) (q_pow (y * y) j))
    by exact (vt_q_pow_base_mono (x * x) (y * y) j (Qmult_le_0_compat x x Hx0 Hx0) Hxx).
  assert (Hden : Qle 0 (/ q_fact (2 * j)))
    by (apply (Qlt_le_weak 0 (/ q_fact (2 * j)));
        apply (Qinv_lt_0_compat (q_fact (2 * j))); apply q_fact_pos).
  unfold cos_abs_term. unfold Qdiv.
  exact (Qmult_le_compat_r _ _ _ Hnum Hden).
Qed.

(* Nonnegativity of the leibsep sum *)
Lemma vt_leibsep35_pos : forall n : nat, Qle 0 (leibsep_abssum_cos (5#3) n).
Proof.
  intro n. induction n as [| m IH].
  - apply Qle_refl.
  - assert (Hterm : Qle 0 (q_pow (5#3) (Datatypes.S (2 * m))
                     / q_fact (Datatypes.S (2 * m)))).
    { unfold Qdiv. apply Qmult_le_0_compat.
      - apply q_pow_nonneg. unfold Qle. simpl. lia.
      - apply (Qlt_le_weak 0 (/ q_fact (Datatypes.S (2 * m)))).
        apply (Qinv_lt_0_compat (q_fact (Datatypes.S (2 * m)))). apply q_fact_pos. }
    simpl leibsep_abssum_cos.
    apply (Qle_trans _ (0 + 0)).
    + unfold Qle. simpl. lia.
    + apply (Qplus_le_compat 0 (leibsep_abssum_cos (5#3) m) 0
               (q_pow (5#3) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)))).
      * exact IH.
      * exact Hterm.
Qed.

(* ============================================================ *)
(* Section 3. Main theorem: existence of a zero of the cosine (carried as a [sig]) *)
(* ============================================================ *)

Lemma approx_root_cos : forall eps : Q,
  Qlt 0 eps ->
  { x : Q | Qlt (3#2) x /\ Qlt x (5#3) /\
    (exists N : nat, forall k : nat, (N <= k)%nat -> Qlt (Qabs (cos_partial k x)) eps) }.
Proof.
  intros eps Heps.
  assert (Heps2 : Qlt 0 (eps * (1#2)))
    by (apply (Qmult_lt_0_compat eps (1#2));
        [exact Heps | unfold Qlt; simpl; reflexivity]).
  assert (H032 : Qle 0 (3#2)) by (unfold Qle; simpl; lia).
  assert (H532 : Qle (5#3) 2) by (unfold Qle; simpl; lia).
  assert (H053 : Qle 0 (5#3)) by (unfold Qle; simpl; lia).
  assert (HD1 : Qle 0 ((3#2) * cos_abs_term (5#3) 1))
    by (apply Qmult_le_0_compat;
        [unfold Qle; simpl; lia | apply (vt_abs_term_nonneg (5#3) 1 H053)]).
  destruct (vt_pow_half_arch ((3#2) * cos_abs_term (5#3) 1) (eps * (1#2)) HD1 Heps2)
    as [N Harch1].
  assert (HAN5 : (5 <= N + 5)%nat) by lia.
  assert (HAGE : (N <= N + 5)%nat) by lia.
  assert (HA2 : (2 <= N + 5)%nat) by lia.
  assert (Hleib0 : Qle 0 (leibsep_abssum_cos (5#3) (N + 5))) by (apply vt_leibsep35_pos).
  assert (HD2 : Qle 0 ((1#6) * leibsep_abssum_cos (5#3) (N + 5)))
    by (apply Qmult_le_0_compat; [unfold Qle; simpl; lia | exact Hleib0]).
  destruct (vt_pow_half_arch ((1#6) * leibsep_abssum_cos (5#3) (N + 5)) (eps * (1#2)) HD2 Heps2)
    as [n Harch2].
  set (A := (N + 5)%nat).
  assert (Hab35 : Qlt (3#2) (5#3)) by (compute; reflexivity).
  assert (Hpa : QltT 0 (cos_partial A (3#2)))
    by (apply Qlt_to_QltT; apply vt_three_halves_pos; exact HAN5).
  assert (Hpb : QleT' (cos_partial A (5#3)) 0)
    by (apply Qle_to_QleT'; apply Qlt_le_weak; apply vt_five_thirds_neg; exact HAN5).
  destruct (vt_bisect_spec n A (3#2) (5#3) Hab35 H032 H532 HA2 Hpa Hpb)
    as [S1 [S2 [S3 [S4 S5]]]].
  assert (HSA : Qle (3#2) (fst (vt_bisect A (3#2) (5#3) Hab35 n)))
    by exact S1.
  assert (HSB : Qle (snd (vt_bisect A (3#2) (5#3) Hab35 n)) (5#3))
    by exact S2.
  assert (Hlen0 : Qlt 0 (((5#3) - (3#2)) * q_pow (1#2) n))
    by (apply (Qmult_lt_0_compat ((5#3) - (3#2)) (q_pow (1#2) n));
        [unfold Qlt; simpl; lia | apply vt_pos_half_pow]).
  assert (Habab : Qlt (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                      (snd (vt_bisect A (3#2) (5#3) Hab35 n))).
  { apply (proj2 (Qlt_minus_iff (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                  (snd (vt_bisect A (3#2) (5#3) Hab35 n)))).
    change (Qlt 0 (snd (vt_bisect A (3#2) (5#3) Hab35 n)
                 - fst (vt_bisect A (3#2) (5#3) Hab35 n))).
    rewrite <- S3. exact Hlen0. }
  assert (HabUP : Qle (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                      (snd (vt_bisect A (3#2) (5#3) Hab35 n)))
    by (apply Qlt_le_weak; exact Habab).
  assert (H0a : Qle 0 (fst (vt_bisect A (3#2) (5#3) Hab35 n)))
    by (apply (Qle_trans 0 (3#2) (fst (vt_bisect A (3#2) (5#3) Hab35 n)));
        [exact H032 | exact HSA]).
  assert (H0b : Qle 0 (snd (vt_bisect A (3#2) (5#3) Hab35 n)))
    by (apply (Qle_trans 0 (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                  (snd (vt_bisect A (3#2) (5#3) Hab35 n)));
        [exact H0a | exact HabUP]).
  set (x := vt_mid (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                   (snd (vt_bisect A (3#2) (5#3) Hab35 n))).
  assert (Hxlo : Qlt (3#2) x).
  { apply (Qle_lt_trans (3#2) (fst (vt_bisect A (3#2) (5#3) Hab35 n)) x).
    - exact HSA.
    - apply (vt_mid_gt_l _ _ Habab). }
  assert (Hxhi : Qlt x (5#3)).
  { apply (Qlt_le_trans x (snd (vt_bisect A (3#2) (5#3) Hab35 n)) (5#3)).
    - apply (vt_mid_lt_r _ _ Habab).
    - exact HSB. }
  assert (Hxlole : Qle (3#2) x) by (apply Qlt_le_weak; exact Hxlo).
  assert (Hxhile : Qle x (5#3)) by (apply Qlt_le_weak; exact Hxhi).
  exists x. split; [exact Hxlo | split; [exact Hxhi | ]].
  exists A. intros k Hk.
  assert (Hx0 : Qle 0 x)
    by (apply (Qle_trans 0 (3#2) x); [exact H032 | exact Hxlole]).
  assert (Hx2 : Qle x 2)
    by (apply (Qle_trans x (5#3) 2); [exact Hxhile | exact H532]).
  assert (HT := vt_cos_partial_tail_bound x A k Hx0 Hx2 HA2 Hk).
  assert (Hax : Qle (fst (vt_bisect A (3#2) (5#3) Hab35 n)) x)
    by (apply Qlt_le_weak; apply (vt_mid_gt_l _ _ Habab)).
  assert (Hxb : Qle x (snd (vt_bisect A (3#2) (5#3) Hab35 n)))
    by (apply Qlt_le_weak; apply (vt_mid_lt_r _ _ Habab)).
  assert (Hxa0 : Qle 0 ((x - fst (vt_bisect A (3#2) (5#3) Hab35 n)) * (1#2))).
  { apply Qmult_le_0_compat.
    - exact (proj1 (Qle_minus_iff (fst (vt_bisect A (3#2) (5#3) Hab35 n)) x) Hax).
    - unfold Qle. simpl. lia. }
  assert (Hbx0 : Qle 0 ((snd (vt_bisect A (3#2) (5#3) Hab35 n) - x) * (1#2))).
  { apply Qmult_le_0_compat.
    - exact (proj1 (Qle_minus_iff x (snd (vt_bisect A (3#2) (5#3) Hab35 n))) Hxb).
    - unfold Qle. simpl. lia. }
  assert (Hupper : Qle (cos_partial A x)
                   (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n)))).
  { assert (Hdec := vt_cos_decr_half A (fst (vt_bisect A (3#2) (5#3) Hab35 n)) x
                      HA2 HSA Hax Hxhile).
    apply (Qle_trans _ (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
              - (x - fst (vt_bisect A (3#2) (5#3) Hab35 n)) * (1#2))).
    - exact Hdec.
    - apply vt_sub_le_r. exact Hxa0. }
  assert (Hlower : Qle (cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n)))
                   (cos_partial A x)).
  { assert (Hdec := vt_cos_decr_half A x (snd (vt_bisect A (3#2) (5#3) Hab35 n))
                      HA2 Hxlole Hxb HSB).
    apply (Qle_trans _ (cos_partial A x
              - (snd (vt_bisect A (3#2) (5#3) Hab35 n) - x) * (1#2))).
    - exact Hdec.
    - apply vt_sub_le_r. exact Hbx0. }
  assert (Hpa4 : Qlt 0 (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))))
    by exact (QltT_to_Qlt _ _ S4).
  assert (Hpb4 : Qle (cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n))) 0)
    by exact (QleT'_to_Qle _ _ S5).
  assert (Hnegb : Qle 0 (- (cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n))))).
  { apply (Qle_trans _ (- 0));
      [unfold Qle; simpl; lia | apply (Qopp_le_compat _ _ Hpb4)]. }
  assert (Hsq : Qle (Qabs (cos_partial A x))
                (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
              - cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n)))).
  { apply (proj2 (Qabs_Qle_condition (cos_partial A x)
              (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
            - cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n))))). split.
    - assert (Hcomm1 : - (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                 - cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n)))
               == cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n))
                - cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))) by ring.
      rewrite Hcomm1.
      apply (Qle_trans _ (cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n)))).
      + apply vt_sub_le_r. apply (Qlt_le_weak 0 _). exact Hpa4.
      + exact Hlower.
    - apply (Qle_trans _ (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n)))).
      + exact Hupper.
      + apply (Qle_trans _ (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                  + - (cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n))))).
        * apply vt_add_le_r. exact Hnegb.
        * apply qeq_le. reflexivity. }
  assert (Hlip : Qle (Qabs (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                          - cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n))))
                     (Qabs (fst (vt_bisect A (3#2) (5#3) Hab35 n)
                          - snd (vt_bisect A (3#2) (5#3) Hab35 n))
                   * leibsep_abssum_cos (5#3) A)).
  { apply QleT'_to_Qle.
    apply (leibsep_cos_partial_lipschitz (fst (vt_bisect A (3#2) (5#3) Hab35 n))
             (snd (vt_bisect A (3#2) (5#3) Hab35 n)) (5#3) A).
    - apply Qle_to_QleT'. unfold Qle. simpl. lia.
    - apply Qle_to_QleT'.
      rewrite (Qabs_pos (fst (vt_bisect A (3#2) (5#3) Hab35 n)) H0a).
      apply (Qle_trans _ (snd (vt_bisect A (3#2) (5#3) Hab35 n)));
        [exact HabUP | exact HSB].
    - apply Qle_to_QleT'.
      rewrite (Qabs_pos (snd (vt_bisect A (3#2) (5#3) Hab35 n)) H0b). exact HSB. }
  assert (Hablen : Qabs (fst (vt_bisect A (3#2) (5#3) Hab35 n)
                       - snd (vt_bisect A (3#2) (5#3) Hab35 n))
                 == snd (vt_bisect A (3#2) (5#3) Hab35 n)
                  - fst (vt_bisect A (3#2) (5#3) Hab35 n)).
  { rewrite (Qabs_Qminus (fst (vt_bisect A (3#2) (5#3) Hab35 n))
              (snd (vt_bisect A (3#2) (5#3) Hab35 n))).
    apply Qabs_pos.
    exact (proj1 (Qle_minus_iff (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                  (snd (vt_bisect A (3#2) (5#3) Hab35 n))) HabUP). }
  rewrite Hablen in Hlip.
  assert (Hc16 : ((5#3) - (3#2)) == (1#6)) by (unfold Qeq; simpl; lia).
  assert (Hspanlip2 : Qle (Qabs (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                              - cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n))))
                     (eps * (1#2))).
  { apply (Qle_trans _ ((snd (vt_bisect A (3#2) (5#3) Hab35 n)
              - fst (vt_bisect A (3#2) (5#3) Hab35 n)) * leibsep_abssum_cos (5#3) A)).
    - exact Hlip.
    - apply (Qle_trans _ (((1#6) * leibsep_abssum_cos (5#3) A) * q_pow (1#2) n)).
      + apply qeq_le. rewrite <- S3. rewrite Hc16. ring.
      + apply Qlt_le_weak. exact Harch2. }
  assert (Hspansmall : Qle (Qabs (cos_partial A x))
                       (Qabs (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                            - cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n))))).
  { apply (Qle_trans _ (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
              - cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n)))).
    - exact Hsq.
    - apply Qle_Qabs. }
  assert (Hmono53 : Qle (cos_abs_term x (Datatypes.S A))
                        (cos_abs_term (5#3) (Datatypes.S A)))
    by exact (vt_abs_term_mono_x x (5#3) (Datatypes.S A) Hx0 Hxhile).
  assert (HSA1 : Datatypes.S A = (1 + A)%nat) by lia.
  assert (H11 : (1 <= 1)%nat) by lia.
  assert (Hc13 : Qle (q_pow (1#3) A) (q_pow (1#2) A))
    by (apply (vt_q_pow_base_mono (1#3) (1#2) A); unfold Qle; simpl; lia).
  assert (Htaillt : Qlt ((3#2) * cos_abs_term x (Datatypes.S A)) (eps * (1#2))).
  { apply (Qle_lt_trans _ (((3#2) * cos_abs_term (5#3) 1) * q_pow (1#2) N)).
    - apply (Qle_trans _ ((3#2) * cos_abs_term (5#3) (Datatypes.S A))).
      + apply (Qle_trans _ (cos_abs_term x (Datatypes.S A) * (3#2))).
        * apply qeq_le. apply Qmult_comm.
        * apply (Qle_trans _ (cos_abs_term (5#3) (Datatypes.S A) * (3#2))).
          -- exact (Qmult_le_compat_r _ _ _ Hmono53 H032).
          -- apply qeq_le. apply Qmult_comm.
      + apply (Qle_trans _ ((3#2) * (q_pow (1#3) A * cos_abs_term (5#3) 1))).
        * rewrite HSA1.
          apply (Qle_trans _ (cos_abs_term (5#3) (1 + A) * (3#2))).
          -- apply qeq_le. apply Qmult_comm.
          -- apply (Qle_trans _ ((q_pow (1#3) A * cos_abs_term (5#3) 1) * (3#2))).
             ++ exact (Qmult_le_compat_r _ _ _
                    (vt_abs_term_decay (5#3) 1 A H053 H532 H11) H032).
             ++ apply qeq_le. apply Qmult_comm.
        * apply (Qle_trans _ (((3#2) * cos_abs_term (5#3) 1) * q_pow (1#3) A)).
          -- apply qeq_le. ring.
          -- apply (Qle_trans _ (((3#2) * cos_abs_term (5#3) 1) * q_pow (1#2) A)).
             ++ exact (vt_qmult_le_compat_l _ _ _ Hc13 HD1).
             ++ exact (vt_qmult_le_compat_l _ _ _
                       (vt_q_pow_half_mono N A HAGE) HD1).
    - exact Harch1. }
  assert (Hdc := proj1 (Qabs_Qle_condition (cos_partial k x - cos_partial A x)
              (Qabs (cos_partial k x - cos_partial A x))) (Qle_refl _)).
  destruct Hdc as [Hdc1 Hdc2].
  assert (Hxc := proj1 (Qabs_Qle_condition (cos_partial A x)
              (Qabs (cos_partial A x))) (Qle_refl _)).
  destruct Hxc as [Hxc1 Hxc2].
  assert (Hsid : cos_partial k x
               == cos_partial k x - cos_partial A x + cos_partial A x) by ring.
  assert (Hsid' : cos_partial k x - cos_partial A x + cos_partial A x
                == cos_partial k x) by ring.
  assert (Htri : Qle (Qabs (cos_partial k x))
                 (Qabs (cos_partial k x - cos_partial A x) + Qabs (cos_partial A x))).
  { apply (proj2 (Qabs_Qle_condition (cos_partial k x)
              (Qabs (cos_partial k x - cos_partial A x) + Qabs (cos_partial A x)))).
    split.
    - apply (Qle_trans _ (-(Qabs (cos_partial k x - cos_partial A x))
              + - (Qabs (cos_partial A x)))).
      + apply qeq_le. ring.
      + apply (Qle_trans _ (cos_partial k x - cos_partial A x
                  + cos_partial A x)).
        * apply (Qplus_le_compat _ _ _ _ Hdc1 Hxc1).
        * apply qeq_le. exact Hsid'.
    - apply (Qle_trans _ (cos_partial k x - cos_partial A x
                + cos_partial A x)).
      + apply qeq_le. exact Hsid.
      + apply (Qplus_le_compat _ _ _ _ Hdc2 Hxc2). }
  assert (Hepsadd : eps * (1#2) + eps * (1#2) == eps) by ring.
  apply (Qle_lt_trans (Qabs (cos_partial k x))
           ((3#2) * cos_abs_term x (Datatypes.S A)
              + Qabs (cos_partial A (fst (vt_bisect A (3#2) (5#3) Hab35 n))
                    - cos_partial A (snd (vt_bisect A (3#2) (5#3) Hab35 n)))) eps).
  - apply (Qle_trans _ (Qabs (cos_partial k x - cos_partial A x)
              + Qabs (cos_partial A x))).
    + exact Htri.
    + apply (Qplus_le_compat _ _ _ _ HT Hspansmall).
  - rewrite <- Hepsadd. apply (Qplus_lt_le_compat _ _ _ _ Htaillt Hspanlip2).
Qed.

Print Assumptions approx_root_cos.
Print Assumptions vt_pow_half_arch.
Print Assumptions vt_abs_term_mono_x.
