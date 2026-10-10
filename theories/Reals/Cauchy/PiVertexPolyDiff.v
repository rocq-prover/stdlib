(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The polynomial difference bound for the cosine partial sums

    Mission.  A supply fragment of the Leibniz vertex half-window
    pair certificate -- the polynomial difference bound for the
    cosine partial sums (the strict-decrease skeleton on the
    half-window interval): for [0 <= x <= y <= 2] and [n >= 2],
    [cos_partial n y <= cos_partial n x - (y^2 - x^2) * (1/6)].  The
    proof uses no derivatives and no mean value theorem, only
    polynomial arithmetic over [Q]: the factorization of the
    difference ([sc_qpow_diff_factor]) together with the lower-bound
    mechanism for the explicit alternating sum [sc_P] ([P_2 >= 1/6]
    and the step-term decrease [sc_t_dec]).  This difference bound is
    the core machinery behind the zero scan, the uniqueness of the
    zero, and the assembly of the vertex window pair.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [ZArith.ZArith], [Arith.PeanoNat], [Setoid], [Morphisms], [Lia];
    [PiCompareT] ([QltT]/[QleT'] carried at the [Set] level);
    [PiKernelSlack] ([cos_term]/[cos_partial]/[q_pow]/[q_fact]/
    [qeq_le]/[q_fact_pos]/[q_pow_nonneg]/[q_pow_succ]/
    [Qle_plus_nonneg_r]).

    References.  [S10_KVQuantTrig.v], the [sc_P] family and
    [sc_cos_partial_diff_le] (the [sum_upto] bridge
    [S03_QExp.v@2516]; the statement faces and the proofs are taken
    over verbatim, with the four dependency-simplification reworks
    listed at the individual statements).

    Constructivity.  Auxiliary lemmas conclude at [Qle]/[Qlt] (the
    stdlib [Q] order predicates, purely constructive); the top-level
    supply lemma [piVx_cos_diff_le_T] concludes at [QleT'] (carried
    at the [Set] level); assumption-free and fully proved, with no
    non-constructive principles; [lia]/[field] only for auxiliary
    bookkeeping steps.

    Build.  [coqc -native-compiler no -q -Q . "" PiVertexPolyDiff.v]
    (Rocq 9.1.0).

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.
Require Import PiCompareT.
Require Import PiKernelSlack.

(* ============================================================ *)
(* Section 1. Bounded-sum infrastructure (the [sum_upto] bridge,  *)
(* the same shape as [S03_QExp.v@2516])                         *)
(* ============================================================ *)

Fixpoint sum_upto (n : nat) (f : nat -> Q) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S n' => sum_upto n' f + f n'
  end.

Lemma sum_upto_ext : forall (n : nat) (f g : nat -> Q),
  (forall i, f i == g i) -> sum_upto n f == sum_upto n g.
Proof.
  intros n f g H.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. setoid_rewrite IH. setoid_rewrite (H n'). reflexivity.
Qed.

Lemma sum_upto_ext_below : forall (n : nat) (f g : nat -> Q),
  (forall i : nat, (i < n)%nat -> f i == g i) -> sum_upto n f == sum_upto n g.
Proof.
  intros n f g H.
  induction n as [| n' IH].
  - reflexivity.
  - simpl.
    setoid_rewrite (IH (fun i : nat => fun Hi : (i < n')%nat =>
                        H i (Nat.lt_trans i n' (Datatypes.S n') Hi (Nat.lt_succ_diag_r n')))).
    setoid_rewrite (H n' (Nat.lt_succ_diag_r n')).
    reflexivity.
Qed.

(* Term-by-term subtraction (the same shape as [S03_QExp.v@3576];
   proved by direct induction) *)
Lemma sum_upto_minus : forall (n : nat) (f g : nat -> Q),
  sum_upto n (fun i => f i - g i) == sum_upto n f - sum_upto n g.
Proof.
  intros n f g.
  induction n as [| n' IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma sum_upto_scale : forall (n : nat) (c : Q) (f : nat -> Q),
  sum_upto n (fun j => c * f j) == c * sum_upto n f.
Proof.
  intros n. induction n as [| n' IH]; intros c f; simpl.
  - ring.
  - setoid_rewrite IH. ring.
Qed.

Lemma sc_sum_nonneg : forall (n : nat) (f : nat -> Q),
  (forall m : nat, Qle 0 (f m)) -> Qle 0 (sum_upto n f).
Proof.
  intros n f Hf.
  induction n as [| n' IH]; simpl.
  - unfold Qle; simpl; lia.
  - apply (Qle_trans _ (0 + 0) _).
    + apply qeq_le. ring.
    + apply (Qplus_le_compat 0 (sum_upto n' f) 0 (f n')).
      * exact IH.
      * exact (Hf n').
Qed.

(* Lower bound by extracting the last term (a simplified form
   written for this file: [sum_upto (S n) f >= f n], from the
   nonnegativity of every term; replaces the shift chain
   [sc_sum_shift_sub_le] of [S10_KVQuantTrig.v]) *)
Lemma sc_sum_last_le : forall (n : nat) (f : nat -> Q),
  (forall m : nat, Qle 0 (f m)) -> Qle (f n) (sum_upto (Datatypes.S n) f).
Proof.
  intros n f Hf.
  change (sum_upto (Datatypes.S n) f) with (sum_upto n f + f n).
  apply (Qle_trans _ (f n + sum_upto n f)).
  - apply (Qle_plus_nonneg_r (f n) (sum_upto n f)).
    apply sc_sum_nonneg. exact Hf.
  - apply qeq_le. ring.
Qed.

(* ============================================================ *)
(* Section 2. Power tools (the [-1] powers by direct induction;   *)
(* the factorization of power differences)                      *)
(* ============================================================ *)

(* Separation of positive [Q] from zero ([Qlt 0 x] implies
   [x <> 0]; an auxiliary lemma written for this file) *)
Lemma vt_qpos_neq : forall x : Q, Qlt 0 x -> Qeq x 0 -> False.
Proof.
  intros x H Hx. rewrite Hx in H. exact (Qlt_irrefl 0 H).
Qed.

(* Left form of order preservation under multiplication by a
   nonnegative scalar ([S10_KVQuantTrig.v@6418]) *)
Lemma sc_qmult_le_l : forall (a b c : Q), Qle a b -> Qle 0 c -> Qle (c * a) (c * b).
Proof.
  intros a b c Hab Hc0.
  exact (Qle_trans (c * a) (a * c) (c * b)
    (qeq_le (c * a) (a * c) (Qmult_comm c a))
    (Qle_trans (a * c) (b * c) (c * b)
      (Qmult_le_compat_r a b c Hab Hc0)
      (qeq_le (b * c) (c * b) (Qmult_comm b c)))).
Qed.

(* The statement of [S03_QExp.v@4210] in the same shape (proved by
   direct induction) *)
Lemma q_pow_neg1_even : forall n, q_pow (-1) (2 * n) == 1.
Proof.
  intro n. induction n as [| n' IH].
  - reflexivity.
  - replace (2 * Datatypes.S n')%nat with (Datatypes.S (Datatypes.S (2 * n')))%nat by lia.
    simpl. rewrite IH. ring.
Qed.

(* The statement of [S03_QExp.v@4217] in the same shape (proved by
   direct induction) *)
Lemma q_pow_neg1_odd : forall n, q_pow (-1) (2 * n + 1) == -1.
Proof.
  intro n.
  replace (2 * n + 1)%nat with (Datatypes.S (2 * n))%nat by lia.
  change (q_pow (-1) (Datatypes.S (2 * n))) with ((-1)%Q * q_pow (-1) (2 * n)).
  rewrite q_pow_neg1_even. ring.
Qed.

(* [S10_KVQuantTrig.v@6726] *)
Lemma sc_qpow_sq : forall (x : Q) (k : nat), q_pow (x * x) k == q_pow x (2 * k).
Proof.
  intros x k.
  induction k as [| k' IH].
  - simpl. reflexivity.
  - rewrite q_pow_succ. rewrite IH.
    assert (H : (2 * Datatypes.S k' = Datatypes.S (Datatypes.S (2 * k')))%nat) by lia.
    rewrite H.
    rewrite q_pow_succ. rewrite q_pow_succ.
    ring.
Qed.

(* [S10_KVQuantTrig.v@6769] *)
Lemma sc_qpow_diff_factor : forall (p q : Q) (k : nat),
  q_pow q k - q_pow p k ==
  (q - p) * sum_upto k (fun i : nat => q_pow q (k - 1 - i) * q_pow p i).
Proof.
  intros p q k.
  induction k as [| k' IH].
  - simpl. ring.
  - rewrite q_pow_succ. rewrite q_pow_succ.
    transitivity (q * q_pow q k' - p * q_pow p k').
    + reflexivity.
    + assert (Hsum : sum_upto (Datatypes.S k') (fun i : nat => q_pow q (Datatypes.S k' - 1 - i) * q_pow p i) ==
                     q_pow p k' + q * sum_upto k' (fun i : nat => q_pow q (k' - 1 - i) * q_pow p i)).
      { change (sum_upto (Datatypes.S k') (fun i : nat => q_pow q (Datatypes.S k' - 1 - i) * q_pow p i))
          with (sum_upto k' (fun i : nat => q_pow q (Datatypes.S k' - 1 - i) * q_pow p i) +
                (q_pow q (Datatypes.S k' - 1 - k') * q_pow p k')).
        assert (H0 : q_pow q (Datatypes.S k' - 1 - k') * q_pow p k' == q_pow p k').
        { assert (Hz : (Datatypes.S k' - 1 - k' = 0)%nat) by lia.
          rewrite Hz. simpl. ring. }
        rewrite H0.
        rewrite (sum_upto_ext_below k'
          (fun i : nat => q_pow q (Datatypes.S k' - 1 - i) * q_pow p i)
          (fun i : nat => q * (q_pow q (k' - 1 - i) * q_pow p i))).
        2: { intros i Hi.
             assert (Hidx : (Datatypes.S k' - 1 - i = Datatypes.S (k' - 1 - i))%nat) by lia.
             rewrite Hidx. rewrite q_pow_succ. ring. }
        rewrite (sum_upto_scale k' q (fun i : nat => q_pow q (k' - 1 - i) * q_pow p i)).
        ring. }
      rewrite Hsum.
      assert (Hdist : (q - p) * (q_pow p k' + q * sum_upto k' (fun i : nat => q_pow q (k' - 1 - i) * q_pow p i)) ==
                      (q - p) * q_pow p k' + q * ((q - p) * sum_upto k' (fun i : nat => q_pow q (k' - 1 - i) * q_pow p i))).
      { ring. }
      rewrite Hdist. rewrite <- IH. ring.
Qed.

(* ============================================================ *)
(* Section 3. The [A_k] family (the numerator machine of the      *)
(* binomial-type alternating sum)                               *)
(* ============================================================ *)

(* [A_k := sum_{i<k} q^(k-1-i) * p^i] ([S10_KVQuantTrig.v@6805]) *)
Definition sc_A (p q : Q) (k : nat) : Q :=
  sum_upto k (fun i : nat => q_pow q (k - 1 - i) * q_pow p i).

(* C0: [0 <= p] and [0 <= q] imply [0 <= A_k]
   ([S10_KVQuantTrig.v@6809]) *)
Lemma sc_A_nonneg : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle 0 q -> Qle 0 (sc_A p q k).
Proof.
  intros p q k Hp0 Hq0. unfold sc_A. apply sc_sum_nonneg. intro m.
  exact (Qmult_le_0_compat (q_pow q (k - 1 - m)) (q_pow p m)
    (q_pow_nonneg q (k - 1 - m) Hq0) (q_pow_nonneg p m Hp0)).
Qed.

(* [A_1 == 1] (the region of [S10_KVQuantTrig.v@7218]) *)
Lemma sc_A_1 : forall (p q : Q), sc_A p q 1 == 1.
Proof.
  intros p q. unfold sc_A.
  change (sum_upto 1 (fun i : nat => q_pow q (1 - 1 - i) * q_pow p i)) with
         (sum_upto 0 (fun i : nat => q_pow q (1 - 1 - i) * q_pow p i) + q_pow q (1 - 1 - 0) * q_pow p 0).
  simpl. ring.
Qed.

(* [A_2 == p+q] (the region of [S10_KVQuantTrig.v@7226]) *)
Lemma sc_A_2 : forall (p q : Q), sc_A p q 2 == p + q.
Proof.
  intros p q. unfold sc_A.
  change (sum_upto 2 (fun i : nat => q_pow q (2 - 1 - i) * q_pow p i)) with
         (sum_upto 1 (fun i : nat => q_pow q (2 - 1 - i) * q_pow p i) + q_pow q (2 - 1 - 1) * q_pow p 1).
  change (sum_upto 1 (fun i : nat => q_pow q (2 - 1 - i) * q_pow p i)) with
         (sum_upto 0 (fun i : nat => q_pow q (2 - 1 - i) * q_pow p i) + q_pow q (2 - 1 - 0) * q_pow p 0).
  simpl. ring.
Qed.

(* C3: the recursion [A (S k) == q * A_k + p^k]
   ([S10_KVQuantTrig.v@6872]) *)
Lemma sc_A_succ : forall (p q : Q) (k : nat),
  sc_A p q (Datatypes.S k) == q * sc_A p q k + q_pow p k.
Proof.
  intros p q k.
  unfold sc_A.
  change (sum_upto (Datatypes.S k) (fun i : nat => q_pow q (Datatypes.S k - 1 - i) * q_pow p i))
    with (sum_upto k (fun i : nat => q_pow q (Datatypes.S k - 1 - i) * q_pow p i) +
          (q_pow q (Datatypes.S k - 1 - k) * q_pow p k)).
  assert (H0 : q_pow q (Datatypes.S k - 1 - k) * q_pow p k == q_pow p k).
  { assert (Hz : (Datatypes.S k - 1 - k = 0)%nat) by lia.
    rewrite Hz. simpl. ring. }
  rewrite H0.
  rewrite (sum_upto_ext_below k
    (fun i : nat => q_pow q (Datatypes.S k - 1 - i) * q_pow p i)
    (fun i : nat => q * (q_pow q (k - 1 - i) * q_pow p i))).
  2: { intros i Hi.
       assert (Hidx : (Datatypes.S k - 1 - i = Datatypes.S (k - 1 - i))%nat) by lia.
       rewrite Hidx. rewrite q_pow_succ. ring. }
  rewrite (sum_upto_scale k q (fun i : nat => q_pow q (k - 1 - i) * q_pow p i)).
  ring.
Qed.

(* C1': [k >= 1] implies [A_k >= p^(k-1)] (statement in the same
   shape as [S10_KVQuantTrig.v@6850]; the proof is reworked into the
   last-term extraction form via [sc_sum_last_le]) *)
Lemma sc_A_ge_p : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle 0 q -> (1 <= k)%nat -> Qle (q_pow p (k - 1)) (sc_A p q k).
Proof.
  intros p q k Hp0 Hq0 Hk.
  destruct k as [| k']; [lia|].
  unfold sc_A.
  replace (Datatypes.S k' - 1)%nat with k'%nat by lia.
  apply (Qle_trans _ (q_pow q (k' - k') * q_pow p k')).
  - replace (k' - k')%nat with 0%nat by lia.
    replace (q_pow q 0)%Q with 1%Q by reflexivity.
    rewrite Qmult_1_l. apply Qle_refl.
  - apply (sc_sum_last_le k' (fun i : nat => q_pow q (k' - i) * q_pow p i)).
    intro m.
    exact (Qmult_le_0_compat (q_pow q (k' - m)) (q_pow p m)
      (q_pow_nonneg q (k' - m) Hq0) (q_pow_nonneg p m Hp0)).
Qed.

(* C4a: [8 <= (2k+1)(2k+2)] for [k >= 1] ([S10_KVQuantTrig.v@6895]) *)
Lemma sc_M_ge8 : forall (k : nat), (1 <= k)%nat ->
  Qle 8 ((Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1).
Proof.
  intros k Hk. unfold Qle. simpl.
  change (8 <= Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2) * 1)%Z.
  rewrite (Z.mul_1_r (Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2))).
  apply (Z.le_trans _ 12 _); [lia | ].
  apply (Z.mul_le_mono_nonneg 3 (Z.of_nat (2 * k + 1)) 4 (Z.of_nat (2 * k + 2))).
  all: lia.
Qed.

(* C4b: the double successor step of [q_fact] (the [S] shape) (the
   region of [S10_KVQuantTrig.v@6905]) *)
Lemma sc_qfact_2succ : forall (k : nat),
  q_fact (2 * Datatypes.S k) ==
  (Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) *
  (Z.of_nat (Datatypes.S (2 * k)) # 1) * q_fact (2 * k).
Proof.
  intro k.
  assert (Hn : (2 * Datatypes.S k = Datatypes.S (Datatypes.S (2 * k)))%nat) by lia.
  rewrite Hn.
  rewrite q_fact_succ. rewrite q_fact_succ.
  ring.
Qed.

Lemma sc_M_qmult : forall (k : nat),
  (Z.of_nat (Datatypes.S (Datatypes.S (2 * k))) # 1) *
  (Z.of_nat (Datatypes.S (2 * k)) # 1) ==
  (Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1.
Proof.
  intro k.
  assert (Ha : (Datatypes.S (Datatypes.S (2 * k)) = 2 * k + 2)%nat) by lia.
  assert (Hb : (Datatypes.S (2 * k) = 2 * k + 1)%nat) by lia.
  rewrite Ha. rewrite Hb.
  unfold Qeq. simpl. ring.
Qed.

(* Two division-times-product identities (auxiliary lemmas written
   for this file; a [Qmult_inv_r] rewrite chain) *)
Lemma vt_div_mul_eq_l : forall (a c d : Q), Qlt 0 d -> a / c == (a * d) * (Qinv c * Qinv d).
Proof.
  intros a c d Hd.
  unfold Qdiv.
  transitivity ((a * Qinv c) * (d * Qinv d)).
  - rewrite (Qmult_inv_r d (vt_qpos_neq d Hd)). ring.
  - ring.
Qed.

Lemma vt_div_mul_eq_r : forall (b c d : Q), Qlt 0 c -> b / d == (b * c) * (Qinv c * Qinv d).
Proof.
  intros b c d Hc.
  unfold Qdiv.
  transitivity ((b * Qinv d) * (c * Qinv c)).
  - rewrite (Qmult_inv_r c (vt_qpos_neq c Hc)). ring.
  - ring.
Qed.

(* Division cross law: [0 < c], [0 < d], and [a * d <= b * c] imply
   [a/c <= b/d] (statement in the same shape as
   [S10_KVQuantTrig.v@6942]; the proof is reworked into an explicit
   chain of identities) *)
Lemma sc_qle_div_cross : forall (a b c d : Q), Qlt 0 c -> Qlt 0 d ->
  Qle (a * d) (b * c) -> Qle (a / c) (b / d).
Proof.
  intros a b c d Hc Hd H.
  assert (Hcd : Qle 0 (Qinv c * Qinv d)).
  { apply Qmult_le_0_compat.
    - apply (Qlt_le_weak 0 (Qinv c)). apply Qinv_lt_0_compat. exact Hc.
    - apply (Qlt_le_weak 0 (Qinv d)). apply Qinv_lt_0_compat. exact Hd. }
  apply (Qle_trans _ ((a * d) * (Qinv c * Qinv d))).
  - apply qeq_le. apply vt_div_mul_eq_l. exact Hd.
  - rewrite (vt_div_mul_eq_r b c d Hc).
    apply (Qmult_le_compat_r (a * d) (b * c) (Qinv c * Qinv d) H Hcd).
Qed.

(* C4c: [q * A_k + p^k <= M_k * A_k] ([S10_KVQuantTrig.v@6956]) *)
Lemma sc_A_succ_bound : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle p q -> Qle q 4 -> (1 <= k)%nat ->
  Qle (q * sc_A p q k + q_pow p k)
      (((Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1) * sc_A p q k).
Proof.
  intros p q k Hp0 Hpq Hq4 Hk.
  set (M := (Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1).
  assert (Hq0 : Qle 0 q) by (apply (Qle_trans _ p _); [exact Hp0 | exact Hpq]).
  assert (HM8 : Qle 8 M) by (unfold M; apply sc_M_ge8; exact Hk).
  assert (HpqM : Qle (p + q) M).
  { apply (Qle_trans _ (4 + 4) _).
    - apply Qplus_le_compat.
      + apply (Qle_trans _ q _); [exact Hpq | exact Hq4].
      + exact Hq4.
    - unfold Qle. simpl. lia. }
  assert (HpMq : Qle p (M - q)).
  { apply (proj2 (Qle_minus_iff p (M - q))).
    assert (Hr : (M - q) - p == M - (p + q)) by ring.
    rewrite Hr.
    apply (proj1 (Qle_minus_iff (p + q) M)). exact HpqM. }
  assert (HqM : Qle q M) by (apply (Qle_trans _ 4 _); [exact Hq4 | apply (Qle_trans _ 8 _); [unfold Qle; simpl; lia | exact HM8]]).
  assert (H1 : Qle (q * sc_A p q k) (M * sc_A p q k)).
  { apply (Qmult_le_compat_r q M (sc_A p q k)).
    - exact HqM.
    - apply (sc_A_nonneg p q k Hp0 Hq0). }
  assert (H2 : Qle (q_pow p k) ((M - q) * sc_A p q k)).
  { assert (Hk1 : (k = Datatypes.S (k - 1))%nat) by lia.
    rewrite Hk1. rewrite q_pow_succ.
    apply (Qle_trans _ ((M - q) * q_pow p (k - 1)) _).
    - apply (Qmult_le_compat_r p (M - q) (q_pow p (k - 1))).
      + exact HpMq.
      + apply q_pow_nonneg. exact Hp0.
    - apply (sc_qmult_le_l (q_pow p (k - 1)) (sc_A p q (Datatypes.S (k - 1))) (M - q)).
      + assert (He : q_pow p (k - 1) == q_pow p (Datatypes.S (k - 1) - 1)).
        { assert (Hn : (Datatypes.S (k - 1) - 1 = k - 1)%nat) by lia. rewrite Hn. reflexivity. }
        apply (Qle_trans _ (q_pow p (Datatypes.S (k - 1) - 1)) _).
        * apply qeq_le. exact He.
        * apply (sc_A_ge_p p q (Datatypes.S (k - 1)) Hp0 Hq0). lia.
      + apply (proj1 (Qle_minus_iff q M)).
        apply (Qle_trans _ 4 _); [exact Hq4 | apply (Qle_trans _ 8 _); [unfold Qle; simpl; lia | exact HM8]]. }
  apply (Qle_trans _ (q * sc_A p q k + (M - q) * sc_A p q k) _).
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + exact H2.
  - apply qeq_le. unfold M. ring.
Qed.

(* C4 main: [t_{k+1} <= t_k] (the region of [S10_KVQuantTrig.v@7082]) *)
Lemma sc_t_dec : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle p q -> Qle q 4 -> (1 <= k)%nat ->
  Qle (sc_A p q (Datatypes.S k) / q_fact (2 * Datatypes.S k))
      (sc_A p q k / q_fact (2 * k)).
Proof.
  intros p q k Hp0 Hpq Hq4 Hk.
  rewrite (sc_A_succ p q k).
  apply (sc_qle_div_cross (q * sc_A p q k + q_pow p k) (sc_A p q k)
                          (q_fact (2 * Datatypes.S k)) (q_fact (2 * k))).
  - apply q_fact_pos.
  - apply q_fact_pos.
  - assert (Hsb := sc_A_succ_bound p q k Hp0 Hpq Hq4 Hk).
    apply (Qle_trans _ (((Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1) *
                        sc_A p q k * q_fact (2 * k)) _).
    + apply (Qmult_le_compat_r (q * sc_A p q k + q_pow p k)
             (((Z.of_nat (2 * k + 1) * Z.of_nat (2 * k + 2)) # 1) * sc_A p q k)
             (q_fact (2 * k))).
      * exact Hsb.
      * apply (Qlt_le_weak 0 (q_fact (2 * k))). apply q_fact_pos.
    + rewrite (sc_qfact_2succ k).
      rewrite (sc_M_qmult k).
      apply qeq_le. unfold Qdiv. ring.
Qed.

(* [t_k >= 0] (the region of [S10_KVQuantTrig.v@7105]) *)
Lemma sc_t_nonneg : forall (p q : Q) (k : nat),
  Qle 0 p -> Qle 0 q -> Qle 0 (sc_A p q k / q_fact (2 * k)).
Proof.
  intros p q k Hp0 Hq0.
  unfold Qdiv.
  exact (Qmult_le_0_compat (sc_A p q k) (Qinv (q_fact (2 * k)))
    (sc_A_nonneg p q k Hp0 Hq0)
    (Qlt_le_weak 0 (Qinv (q_fact (2 * k)))
      (Qinv_lt_0_compat (q_fact (2 * k)) (q_fact_pos (2 * k))))).
Qed.

(* ============================================================ *)
(* Section 4. The [P] family (the normalized alternating sum of   *)
(* the cos difference and its lower bound)                      *)
(* ============================================================ *)

(* [P_N := sum_{k<N} (-1)^(k-1) * A_k/(2k)!] (the [t_0] term is
   [0], which is harmless) ([S10_KVQuantTrig.v@7131]) *)
Definition sc_P (p q : Q) (N : nat) : Q :=
  sum_upto N (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))).

(* The one-step identity (the region of [S10_KVQuantTrig.v@7117]) *)
Lemma sc_P_step1 : forall (p q : Q) (N : nat),
  sc_P p q (Datatypes.S N) ==
  sc_P p q N + q_pow (-1) (N - 1) * (sc_A p q N / q_fact (2 * N)).
Proof.
  intros p q N.
  unfold sc_P.
  set (f := fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))).
  change (sum_upto (Datatypes.S N) f) with (sum_upto N f + f N).
  unfold f. reflexivity.
Qed.

(* The two-step identity (the region of [S10_KVQuantTrig.v@7129]) *)
Lemma sc_P_step2 : forall (p q : Q) (N : nat),
  sc_P p q (Datatypes.S (Datatypes.S N)) ==
  sc_P p q N +
  q_pow (-1) (N - 1) * (sc_A p q N / q_fact (2 * N)) +
  q_pow (-1) (Datatypes.S N - 1) * (sc_A p q (Datatypes.S N) / q_fact (2 * Datatypes.S N)).
Proof.
  intros p q N.
  unfold sc_P.
  set (f := fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))).
  change (sum_upto (Datatypes.S (Datatypes.S N)) f) with (sum_upto (Datatypes.S N) f + f (Datatypes.S N)).
  change (sum_upto (Datatypes.S N) f) with (sum_upto N f + f N).
  unfold f. reflexivity.
Qed.

(* The increment: [P(S(S(S(2m)))) >= P(S(2m))] (the added part
   [t_{S(2m)} - t_{S(S(2m))}] is nonnegative) (the region of
   [S10_KVQuantTrig.v@7151]) *)
Lemma sc_P_inc : forall (p q : Q) (m : nat),
  Qle 0 p -> Qle 0 q -> Qle p q -> Qle q 4 ->
  Qle (sc_P p q (Datatypes.S (2 * m)))
      (sc_P p q (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))).
Proof.
  intros p q m Hp0 Hq0 Hpq Hq4.
  rewrite (sc_P_step2 p q (Datatypes.S (2 * m))).
  assert (Ha : (Datatypes.S (2 * m) - 1 = 2 * m)%nat) by lia.
  rewrite Ha.
  rewrite (q_pow_neg1_even m).
  assert (Ho : q_pow (-1) (Datatypes.S (Datatypes.S (2 * m)) - 1) == -1).
  { assert (Hbo : (Datatypes.S (Datatypes.S (2 * m)) - 1 = Datatypes.S (2 * m))%nat) by lia.
    rewrite Hbo.
    assert (Hbo2 : (Datatypes.S (2 * m) = 2 * m + 1)%nat) by lia.
    rewrite Hbo2. exact (q_pow_neg1_odd m). }
  rewrite Ho.
  set (T1 := sc_A p q (Datatypes.S (2 * m)) / q_fact (2 * Datatypes.S (2 * m))).
  set (T2 := sc_A p q (Datatypes.S (Datatypes.S (2 * m))) / q_fact (2 * Datatypes.S (Datatypes.S (2 * m)))).
  apply (Qle_trans _ (sc_P p q (Datatypes.S (2 * m)) + (T1 - T2)) _).
  - apply (Qle_plus_nonneg_r (sc_P p q (Datatypes.S (2 * m))) (T1 - T2)).
    apply (proj1 (Qle_minus_iff T2 T1)).
    unfold T1, T2.
    apply (sc_t_dec p q (Datatypes.S (2 * m)) Hp0 Hpq Hq4). lia.
  - apply qeq_le. unfold T1, T2, Qdiv. ring.
Qed.

(* The odd extension: [P(S(S(2m))) >= P(S(2m))] (the added term
   [t_{S(2m)}] is nonnegative) (the region of
   [S10_KVQuantTrig.v@7193]) *)
Lemma sc_P_odd_ge : forall (p q : Q) (m : nat),
  Qle 0 p -> Qle 0 q ->
  Qle (sc_P p q (Datatypes.S (2 * m)))
      (sc_P p q (Datatypes.S (Datatypes.S (2 * m)))).
Proof.
  intros p q m Hp0 Hq0.
  rewrite (sc_P_step1 p q (Datatypes.S (2 * m))).
  assert (Ha : (Datatypes.S (2 * m) - 1 = 2 * m)%nat) by lia.
  rewrite Ha.
  rewrite (q_pow_neg1_even m).
  rewrite (Qmult_1_l (sc_A p q (Datatypes.S (2 * m)) / q_fact (2 * Datatypes.S (2 * m)))).
  apply (Qle_plus_nonneg_r (sc_P p q (Datatypes.S (2 * m)))
          (sc_A p q (Datatypes.S (2 * m)) / q_fact (2 * Datatypes.S (2 * m)))).
  apply (sc_t_nonneg p q (Datatypes.S (2 * m)) Hp0 Hq0).
Qed.

(* The even subsequence: [P_{2m} >= P_2] (the region of
   [S10_KVQuantTrig.v@7211]) *)
Lemma sc_P_even_ge : forall (p q : Q) (m : nat),
  Qle 0 p -> Qle 0 q -> Qle p q -> Qle q 4 ->
  Qle (sc_P p q 3) (sc_P p q (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))).
Proof.
  intros p q m Hp0 Hq0 Hpq Hq4.
  induction m as [| m' IH].
  - replace (Datatypes.S (Datatypes.S (Datatypes.S (2 * 0)))) with 3%nat by lia.
    apply Qle_refl.
  - apply (Qle_trans _ (sc_P p q (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'))))) _).
    + exact IH.
    + replace (Datatypes.S (Datatypes.S (Datatypes.S (2 * m')))) with (Datatypes.S (2 * Datatypes.S m')) by lia.
      apply (sc_P_inc p q (Datatypes.S m') Hp0 Hq0 Hpq Hq4).
Qed.

(* The even-odd dichotomy of natural numbers (written for this
   file, as a [Prop] disjunction; replaces the
   dependent-induction-type [sc_nat_split] of [S10_KVQuantTrig.v]) *)
Lemma vt_parity : forall n : nat,
  (exists m : nat, n = 2 * m)%nat \/ (exists m : nat, n = 2 * m + 1)%nat.
Proof.
  intro n. induction n as [| n' IH].
  - left. exists 0%nat. reflexivity.
  - destruct IH as [[m Hm] | [m Hm]].
    + right. exists m. rewrite Hm. lia.
    + left. exists (Datatypes.S m). rewrite Hm. lia.
Qed.

(* The total lower bound: [N >= 3] implies [P_2 <= P_N] (statement
   in the same shape as [S10_KVQuantTrig.v@7234]; the case analysis
   goes through [vt_parity]) *)
Lemma sc_P_ge_P2 : forall (p q : Q) (N : nat),
  Qle 0 p -> Qle 0 q -> Qle p q -> Qle q 4 -> (3 <= N)%nat ->
  Qle (sc_P p q 3) (sc_P p q N).
Proof.
  intros p q N Hp0 Hq0 Hpq Hq4 HN.
  destruct (vt_parity (N - 1)) as [[m Hm] | [m Hm]].
  - (* [N-1 = 2m]: [N = S(2m) = S(S(S(2m'')))] with [m = S m'']; *)
    (* [N >= 3] forces [m''] to exist *)
    destruct m as [| m''].
    + assert (Hz : (3 <= Datatypes.S (2 * 0))%nat -> False) by lia.
      exfalso. apply Hz. lia.
    + assert (HN' : (N = Datatypes.S (2 * Datatypes.S m''))%nat) by lia.
      rewrite HN'.
      replace (Datatypes.S (2 * Datatypes.S m'')) with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'')))) by lia.
      apply (sc_P_even_ge p q m'' Hp0 Hq0 Hpq Hq4).
  - (* [N-1 = 2m+1]: [N = S(S(2m))] with [m >= 1] (since [N >= 4]) *)
    assert (Hm1 : (1 <= m)%nat) by lia.
    assert (HN' : (N = Datatypes.S (Datatypes.S (2 * m)))%nat) by lia.
    rewrite HN'.
    apply (Qle_trans _ (sc_P p q (Datatypes.S (2 * m))) _).
    + destruct m as [| m''].
      * assert (Hz : (3 <= Datatypes.S (Datatypes.S (2 * 0)))%nat -> False) by lia.
        exfalso. apply Hz. lia.
      * replace (Datatypes.S (2 * Datatypes.S m'')) with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m'')))) by lia.
        apply (sc_P_even_ge p q m'' Hp0 Hq0 Hpq Hq4).
    + apply (sc_P_odd_ge p q m Hp0 Hq0).
Qed.

(* [P_2 == 1/2 - (p+q)/24] (the region of [S10_KVQuantTrig.v@7246]) *)
Lemma sc_P2_val : forall (p q : Q), sc_P p q 3 == 1 / 2 - (p + q) / 24.
Proof.
  intros p q. unfold sc_P.
  change (sum_upto 3 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k)))) with
         (sum_upto 2 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))) + q_pow (-1) 1 * (sc_A p q 2 / q_fact 4)).
  change (sum_upto 2 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k)))) with
         (sum_upto 1 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))) + q_pow (-1) 0 * (sc_A p q 1 / q_fact 2)).
  change (sum_upto 1 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k)))) with
         (sum_upto 0 (fun k : nat => q_pow (-1) (k - 1) * (sc_A p q k / q_fact (2 * k))) + q_pow (-1) 0 * (sc_A p q 0 / q_fact 0)).
  simpl.
  rewrite (sc_A_1 p q). rewrite (sc_A_2 p q).
  assert (Hf2 : q_fact 2 == 2) by (vm_compute; reflexivity).
  assert (Hf4 : q_fact 4 == 24) by (vm_compute; reflexivity).
  rewrite Hf2. rewrite Hf4.
  assert (H0 : sc_A p q 0 == 0) by (unfold sc_A; simpl; ring).
  rewrite H0.
  unfold Qdiv. ring.
Qed.

(* [P_2 >= 1/6] (the region of [S10_KVQuantTrig.v@7268]) *)
Lemma sc_P2_ge_sixth : forall (p q : Q),
  Qle 0 p -> Qle p q -> Qle q 4 -> Qle (1 / 6) (sc_P p q 3).
Proof.
  intros p q Hp0 Hpq Hq4.
  rewrite (sc_P2_val p q).
  apply (proj2 (Qle_minus_iff (1 / 6) (1 / 2 - (p + q) / 24))).
  assert (Hpq8 : Qle (p + q) 8).
  { apply (Qle_trans _ (4 + 4) _).
    - apply Qplus_le_compat.
      + apply (Qle_trans _ q _); [exact Hpq | exact Hq4].
      + exact Hq4.
    - unfold Qle. simpl. lia. }
  apply (proj1 (Qle_minus_iff (p + q) 8)) in Hpq8.
  assert (He : (1 / 2 - (p + q) / 24) - 1 / 6 == (8 - (p + q)) / 24).
  { field. all: try (unfold Qeq; simpl; lia). }
  rewrite He.
  unfold Qdiv.
  apply Qmult_le_0_compat.
  - exact Hpq8.
  - apply (Qlt_le_weak 0 (Qinv 24)).
    apply Qinv_lt_0_compat. change (Qlt 0 24). compute. reflexivity.
Qed.

(* ============================================================ *)
(* Section 5. The main cos-difference chain                      *)
(* ============================================================ *)

(* The power-difference factor (bridging to the [x^(2k)] form,
   with [p := x*x] and [q := y*y]) ([S10_KVQuantTrig.v@7296]) *)
Lemma sc_qpow2_diff : forall (x y : Q) (k : nat),
  q_pow x (2 * k) - q_pow y (2 * k) ==
  - ((y * y - x * x) * sum_upto k (fun i : nat => q_pow (y * y) (k - 1 - i) * q_pow (x * x) i)).
Proof.
  intros x y k.
  assert (H1 : q_pow x (2 * k) == q_pow (x * x) k) by (apply Qeq_sym; apply (sc_qpow_sq x k)).
  assert (H2 : q_pow y (2 * k) == q_pow (y * y) k) by (apply Qeq_sym; apply (sc_qpow_sq y k)).
  rewrite H1. rewrite H2.
  rewrite <- (sc_qpow_diff_factor (x * x) (y * y) k).
  ring.
Qed.

(* The sign bridge: [k >= 1] implies [(-1)^k * (-1) == (-1)^(k-1)]
   ([S10_KVQuantTrig.v@7310]) *)
Lemma sc_q_pow_pred : forall (k : nat), (1 <= k)%nat ->
  q_pow (-1) k * -1 == q_pow (-1) (k - 1).
Proof.
  intros k Hk.
  destruct k as [| k'].
  - lia.
  - assert (Hn : (Datatypes.S k' - 1 = k')%nat) by lia.
    rewrite Hn.
    rewrite q_pow_succ. ring.
Qed.

(* The bridge: the partial sums in [sum_upto] form
   ([S10_KVQuantTrig.v@5232]) *)
Lemma sc_cos_partial_upto : forall (n : nat) (x : Q),
  cos_partial n x == sum_upto (Datatypes.S n) (fun j : nat => cos_term j x).
Proof.
  intros n x. induction n as [| n' IH]; simpl.
  - ring.
  - rewrite IH. reflexivity.
Qed.

(* Term by term: [cos_term k x - cos_term k y ==
   (y^2-x^2) * (-1)^(k-1) * A_k/(2k)!] (for every [k]) (the region
   of [S10_KVQuantTrig.v@7324]) *)
Lemma sc_cos_diff_term : forall (x y : Q) (k : nat),
  cos_term k x - cos_term k y ==
  (y * y - x * x) * (q_pow (-1) (k - 1) * (sc_A (x * x) (y * y) k / q_fact (2 * k))).
Proof.
  intros x y k.
  destruct k as [| k'].
    - (* [k = 0]: both sides are [0] (since [A_0 = 0]) *)
    unfold sc_A, cos_term. simpl. unfold Qdiv.
    field. all: try (unfold Qeq; simpl; lia).
    all: try (unfold Qeq; simpl; discriminate).
  - (* [k = S k' >= 1]: the main path *)
    unfold cos_term, sc_A.
    (* 1. Combine over the common denominator *)
    assert (Hc : q_pow (-1) (Datatypes.S k') * (q_pow x (2 * Datatypes.S k') / q_fact (2 * Datatypes.S k')) -
                 q_pow (-1) (Datatypes.S k') * (q_pow y (2 * Datatypes.S k') / q_fact (2 * Datatypes.S k')) ==
                 q_pow (-1) (Datatypes.S k') * (q_pow x (2 * Datatypes.S k') - q_pow y (2 * Datatypes.S k')) / q_fact (2 * Datatypes.S k')).
    { unfold Qdiv. field.
      + exact (vt_qpos_neq (q_fact (2 * Datatypes.S k')) (q_fact_pos (2 * Datatypes.S k'))). }
    rewrite Hc.
    (* 2. Factor the power difference *)
    rewrite (sc_qpow2_diff x y (Datatypes.S k')).
    (* 3. Pull out the minus sign with the sign bridge *)
    set (X := (y * y - x * x) * sum_upto (Datatypes.S k') (fun i : nat => q_pow (y * y) (Datatypes.S k' - 1 - i) * q_pow (x * x) i)).
    assert (Hsg : q_pow (-1) (Datatypes.S k') * - X == q_pow (-1) (Datatypes.S k' - 1) * X).
    { assert (Hneg : - X == -1 * X) by ring.
      rewrite Hneg.
      rewrite <- (sc_q_pow_pred (Datatypes.S k')); [ring | lia]. }
    rewrite Hsg.
    unfold X. unfold Qdiv. ring.
Qed.

(* The sum identity: [cos_partial n x - cos_partial n y ==
   (y^2-x^2) * sc_P (x*x) (y*y) (S n)] (the region of
   [S10_KVQuantTrig.v@7290]) *)
Lemma sc_cos_partial_diff_eq : forall (n : nat) (x y : Q),
  cos_partial n x - cos_partial n y ==
  (y * y - x * x) * sc_P (x * x) (y * y) (Datatypes.S n).
Proof.
  intros n x y.
  rewrite (sc_cos_partial_upto n x). rewrite (sc_cos_partial_upto n y).
  rewrite <- (sum_upto_minus (Datatypes.S n) (fun j : nat => cos_term j x) (fun j : nat => cos_term j y)).
  rewrite (sum_upto_ext (Datatypes.S n)
    (fun j : nat => cos_term j x - cos_term j y)
    (fun j : nat => (y * y - x * x) * (q_pow (-1) (j - 1) * (sc_A (x * x) (y * y) j / q_fact (2 * j))))).
  2: { intro j. apply (sc_cos_diff_term x y j). }
  rewrite (sum_upto_scale (Datatypes.S n) (y * y - x * x)
            (fun j : nat => q_pow (-1) (j - 1) * (sc_A (x * x) (y * y) j / q_fact (2 * j)))).
  unfold sc_P. reflexivity.
Qed.

(* The main lemma: [0 <= x <= y <= 2] and [n >= 2] imply
   [cos_partial n y <= cos_partial n x - (y^2-x^2)/6] (the region
   of [S10_KVQuantTrig.v@7316]) *)
Lemma sc_cos_partial_diff_le : forall (n : nat) (x y : Q),
  Qle 0 x -> Qle x y -> Qle y 2 -> (2 <= n)%nat ->
  Qle (cos_partial n y) (cos_partial n x - (y * y - x * x) * (1 / 6)).
Proof.
  intros n x y Hx0 Hxy Hy2 Hn.
  set (p := x * x). set (q := y * y).
  assert (Hp0 : Qle 0 p) by (unfold p; apply Qmult_le_0_compat; [exact Hx0 | exact Hx0]).
  assert (Hq0 : Qle 0 q).
  { unfold q. apply Qmult_le_0_compat.
    - apply (Qle_trans _ x _); [exact Hx0 | exact Hxy].
    - apply (Qle_trans _ x _); [exact Hx0 | exact Hxy]. }
  assert (Hy0 : Qle 0 y) by (apply (Qle_trans _ x _); [exact Hx0 | exact Hxy]).
  assert (Hpq : Qle p q).
  { unfold p, q.
    apply (Qle_trans _ (y * x) _).
    - apply (Qmult_le_compat_r x y x).
      + exact Hxy.
      + exact Hx0.
    - apply (sc_qmult_le_l x y y).
      + exact Hxy.
      + exact Hy0. }
  assert (Hq4 : Qle q 4).
  { unfold q.
    apply (Qle_trans _ (2 * y) _).
    - apply (Qmult_le_compat_r y 2 y).
      + exact Hy2.
      + exact Hy0.
    - apply (Qle_trans _ (2 * 2) _).
      + apply (sc_qmult_le_l y 2 2).
        * exact Hy2.
        * unfold Qle. simpl. lia.
      + apply qeq_le. ring. }
  assert (Hpq0 : Qle 0 (q - p)).
  { apply (proj1 (Qle_minus_iff p q)). exact Hpq. }
  assert (Hsix : Qle (1 / 6) (sc_P p q (Datatypes.S n))).
  { apply (Qle_trans _ (sc_P p q 3) _).
    - apply (sc_P2_ge_sixth p q Hp0 Hpq Hq4).
    - apply (sc_P_ge_P2 p q (Datatypes.S n) Hp0 Hq0 Hpq Hq4).
      lia. }
  assert (Hge : Qle ((q - p) * (1 / 6)) (cos_partial n x - cos_partial n y)).
  { rewrite (sc_cos_partial_diff_eq n x y).
    apply (sc_qmult_le_l (1 / 6) (sc_P p q (Datatypes.S n)) (q - p)).
    - exact Hsix.
    - exact Hpq0. }
  apply (proj2 (Qle_minus_iff (cos_partial n y) (cos_partial n x - (q - p) * (1 / 6)))).
  assert (Hr : (cos_partial n x - (q - p) * (1 / 6)) + - cos_partial n y ==
               (cos_partial n x - cos_partial n y) - (q - p) * (1 / 6)) by ring.
  rewrite Hr.
  apply (proj1 (Qle_minus_iff ((q - p) * (1 / 6)) (cos_partial n x - cos_partial n y))).
  exact Hge.
Qed.

(* ============================================================ *)
(* Section 6. The top-level supply lemma (conclusion carried at   *)
(* the [Set] level, in the [QleT'] face)                        *)
(* ============================================================ *)

Lemma piVx_cos_diff_le_T : forall (n : nat) (x y : Q),
  QleT' 0 x -> QleT' x y -> QleT' y 2 -> (2 <= n)%nat ->
  QleT' (cos_partial n y) (cos_partial n x - (y * y - x * x) * (1 # 6)%Q).
Proof.
  intros n x y Hx0 Hxy Hy2 Hn.
  apply Qle_to_QleT'.
  apply (sc_cos_partial_diff_le n x y).
  - apply QleT'_to_Qle. exact Hx0.
  - apply QleT'_to_Qle. exact Hxy.
  - apply QleT'_to_Qle. exact Hy2.
  - exact Hn.
Qed.
