(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Bounds, inverse bounds, and the Cauchy property of the cosine
    zero sequence

    Mission.  Nine statements about the cosine zero sequence
    [cos_zero_seq]: the five interval and magnitude bounds (lower
    bound, upper bound, nonnegativity, bound by two, absolute-value
    bound); the three inverse bounds (the pointwise root bound, and
    the inverse bound in pointwise form and in distance form); and the
    Cauchy property of the sequence.  The n-th term of the zero
    sequence is taken from [PiCosZeroSeqProbe.cos_zero_seq] (the
    localization point with tolerance [eps_n = (1/2)^(n+1)]); the root
    localization is supplied by [PiCosApproxRoot.approx_root_cos]; the
    [log_eps] lemma family is supplied by [QCauchyZeroCos]; the
    term-wise difference bound is supplied by
    [PiVertexPolyDiff.sc_cos_partial_diff_le].

    Dependencies.  Stdlib [QArith] ([QArith]/[Qabs]/[Qfield]);
    [PiKernelSlack] ([q_pow]/[cos_partial] and the bridge lemmas);
    [QCauchyZeroCos]; [PiCosTailScan]; [PiVertexPolyDiff];
    [PiCosApproxRoot]; [PiCosZeroSeqProbe].

    References.  [S10_KVQuantTrig.v :8123/:8131/:8139/:8146/:8413]
    ([cos_zero_lower]/[cos_zero_upper]/[cos_zero_nonneg]/
    [cos_zero_le_two]/[cos_zero_abs_le_two]), [:8156/:8184/:8243]
    ([cos_root_pt_bound]/[cos_inv_pt]/[cos_inv_dist]), and [:8296]
    ([cos_seq_cauchy]): the [Q]-level restatements.

    Constructivity.  Statements carried at the [Set] level ([sig]
    witnesses, [Q] values); within proofs the constructive stdlib
    [Qlt]/[Qle]/[Qeq] predicates are used; assumption-free and fully
    proved, with no non-constructive principles (the closing
    [Print Assumptions] lines all report closed).

    Build.  [rocq c -native-compiler no -q -Q . ""
    PiCosZeroSeqConv.v]; the first eight bytes of the artifact are
    [436f7121 00015ff4].

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

(* ============================================================ *)
(* Section 1. Interval bounds of the zero sequence *)
(* ============================================================ *)

(* Lower bound: [z_n > 3/2] (first component of the [approx_root_cos]
   witness). *)
Lemma cos_zero_lower : forall n : nat, Qlt (3#2)%Q (cos_zero_seq n).
Proof.
  intros n.
  unfold cos_zero_seq.
  destruct (approx_root_cos (log_eps n) (log_eps_pos n)) as [x [Hlo [Hhi HN]]].
  exact Hlo.
Qed.

(* Upper bound: [z_n < 5/3] (second component of the [approx_root_cos]
   witness). *)
Lemma cos_zero_upper : forall n : nat, Qlt (cos_zero_seq n) (5#3)%Q.
Proof.
  intros n.
  unfold cos_zero_seq.
  destruct (approx_root_cos (log_eps n) (log_eps_pos n)) as [x [Hlo [Hhi HN]]].
  exact Hhi.
Qed.

(* Nonnegativity: [0 <= z_n] (transitivity through [0 < 3/2] and the
   lower bound). *)
Lemma cos_zero_nonneg : forall n : nat, Qle 0 (cos_zero_seq n).
Proof.
  intros n.
  apply (Qlt_le_weak 0 (cos_zero_seq n)).
  apply (Qlt_trans 0 (3#2)%Q).
  - change (Qlt 0 (3#2)%Q). unfold Qlt. simpl. lia.
  - apply cos_zero_lower.
Qed.

(* Second upper bound: [z_n <= 2] (transitivity through the upper
   bound [5/3 < 2]). *)
Lemma cos_zero_le_two : forall n : nat, Qle (cos_zero_seq n) 2.
Proof.
  intros n.
  apply (Qlt_le_weak (cos_zero_seq n) 2).
  apply (Qlt_trans (cos_zero_seq n) (5#3)%Q).
  - apply cos_zero_upper.
  - change (Qlt (5#3)%Q 2). unfold Qlt. simpl. lia.
Qed.

(* Absolute-value bound: [|z_n| <= 2] (composed from
   [Qabs_Qle_condition] and the previous two statements). *)
Lemma cos_zero_abs_le_two : forall n : nat, Qle (Qabs (cos_zero_seq n)) 2.
Proof.
  intros n.
  apply (proj2 (Qabs_Qle_condition (cos_zero_seq n) 2)).
  split.
  - apply (Qle_trans _ 0 _).
    + change (Qle (- 2) 0). unfold Qle. simpl. lia.
    + apply cos_zero_nonneg.
  - apply cos_zero_le_two.
Qed.

(* ============================================================ *)
(* Section 2. Pointwise root bound and inverse bounds *)
(* ============================================================ *)

(* Pointwise root bound: [|cos_k(z_n)| < eps_n] for [k] large enough
   (supplied directly by the third component of [approx_root_cos]; a
   strengthened [Q]-level form with all five [Real]-layer bridges
   removed).  The existence witness is carried by [exists]: the
   upstream third component of [approx_root_cos] is itself the
   [exists] form, this form is verbatim same-shaped with it, and its
   consumption sites (the pairing orders of the Cauchy statement)
   eliminate it at [exists] goals, with no [Set] elimination. *)
Lemma cos_root_pt_bound : forall n : nat,
  exists N : nat, forall k : nat, (N <= k)%nat ->
    Qlt (Qabs (cos_partial k (cos_zero_seq n))) (log_eps n).
Proof.
  intros n.
  unfold cos_zero_seq.
  destruct (approx_root_cos (log_eps n) (log_eps_pos n)) as [x [Hlo [Hhi HN]]].
  destruct HN as [N HN].
  exists N.
  exact HN.
Qed.

(* Inverse bound (pointwise form): [k >= 2], [0 <= u <= v <= 2],
   [|cos_k(u)| < du], [|cos_k(v)| < dv] imply
   [(v^2 - u^2)/6 < du + dv].  Main chain: [sc_cos_partial_diff_le]
   gives [cos_k(v) <= cos_k(u) - (v^2-u^2)/6], while
   [cos_k(u) - cos_k(v) <= |cos_k(u)| + |cos_k(v)| < du + dv]. *)
Lemma cos_inv_pt : forall (u v : Q) (k : nat) (du dv : Q),
  (2 <= k)%nat -> Qle 0 u -> Qle u v -> Qle v 2 ->
  Qlt (Qabs (cos_partial k u)) du ->
  Qlt (Qabs (cos_partial k v)) dv ->
  Qlt ((v * v - u * u) * (1 / 6)) (du + dv).
Proof.
  intros u v k du dv Hk Hu0 Huv Hv2 Hdu Hdv.
  assert (Hmain : Qle (cos_partial k v)
                      (cos_partial k u - (v * v - u * u) * (1 / 6))).
  { apply (sc_cos_partial_diff_le k u v Hu0 Huv Hv2 Hk). }
(* [(v^2-u^2)/6 <= cos_k(u) - cos_k(v)]. *)
  assert (Hd : Qle ((v * v - u * u) * (1 / 6))
                   (cos_partial k u - cos_partial k v)).
  { apply (proj2 (Qle_minus_iff ((v * v - u * u) * (1 / 6))
                                (cos_partial k u - cos_partial k v))).
    assert (Hr : (cos_partial k u - cos_partial k v) - (v * v - u * u) * (1 / 6) ==
                 (cos_partial k u - (v * v - u * u) * (1 / 6)) - cos_partial k v) by ring.
    rewrite Hr.
    apply (proj1 (Qle_minus_iff (cos_partial k v)
                                (cos_partial k u - (v * v - u * u) * (1 / 6)))).
    exact Hmain. }
(* [cos_k(u) - cos_k(v) <= |cos_k(u)| + |cos_k(v)| < du + dv]. *)
  assert (Htri : Qle (Qabs (cos_partial k u - cos_partial k v))
                     (Qabs (cos_partial k u) + Qabs (cos_partial k v))).
  { apply (Qle_trans _ (Qabs (cos_partial k u + - cos_partial k v)) _).
    - apply qeq_le. apply Qabs_wd. ring.
    - apply (Qle_trans _ (Qabs (cos_partial k u) + Qabs (- cos_partial k v)) _).
      + apply Qabs_triangle.
      + apply qeq_le.
        assert (Hn1 : - cos_partial k v == 0 - cos_partial k v) by ring.
        rewrite (Qabs_wd _ _ Hn1).
        rewrite (Qabs_Qminus 0%Q (cos_partial k v)).
        assert (Hz0 : cos_partial k v - 0 == cos_partial k v) by ring.
        rewrite (Qabs_wd _ _ Hz0).
        reflexivity. }
  apply (Qle_lt_trans ((v * v - u * u) * (1 / 6))
                      (cos_partial k u - cos_partial k v)
                      (du + dv)).
  - exact Hd.
  - apply (Qle_lt_trans (cos_partial k u - cos_partial k v)
                        (Qabs (cos_partial k u) + Qabs (cos_partial k v))
                        (du + dv)).
    + apply (Qle_trans _ (Qabs (cos_partial k u - cos_partial k v)) _).
      * apply Qle_Qabs.
      * exact Htri.
    + apply (Qplus_lt_compat (Qabs (cos_partial k u)) du
                             (Qabs (cos_partial k v)) dv).
      * exact Hdu.
      * exact Hdv.
Qed.

(* Inverse bound (distance form): [3/2 <= u <= v <= 5/3], pointwise
   [|cos_k(u)| < du], [|cos_k(v)| < dv] imply [v - u < 2*(du + dv)].
   From [v^2-u^2 == (v-u)(v+u)] and [v+u >= 3] one gets
   [3*(v-u) <= v^2-u^2]; compose with the pointwise form. *)
Lemma cos_inv_dist : forall (u v du dv : Q) (k : nat),
  (2 <= k)%nat -> Qle (3#2)%Q u -> Qle u v -> Qle v (5#3)%Q ->
  Qlt (Qabs (cos_partial k u)) du ->
  Qlt (Qabs (cos_partial k v)) dv ->
  Qlt (v - u) (2 * (du + dv)).
Proof.
  intros u v du dv k Hk Hu3 Huv Hv53 Hdu Hdv.
(* [0 <= u] and [v <= 2] (premises of the pointwise form). *)
  assert (Hu0 : Qle 0 u).
  { apply (Qle_trans _ (3#2)%Q _).
    - change (Qle 0 (3#2)%Q). unfold Qle. simpl. lia.
    - exact Hu3. }
  assert (Hv2 : Qle v 2).
  { apply (Qle_trans _ (5#3)%Q _).
    - exact Hv53.
    - change (Qle (5#3)%Q 2). unfold Qle. simpl. lia. }
(* [(v^2-u^2)/6 < du + dv]. *)
  assert (Hq : Qlt ((v * v - u * u) * (1 / 6)) (du + dv)).
  { apply (cos_inv_pt u v k du dv Hk Hu0 Huv Hv2 Hdu Hdv). }
(* [v^2-u^2 == (v-u)(v+u)] and [v+u >= 3] imply
   [3*(v-u) <= v^2-u^2]. *)
  assert (Hprod : (v - u) * (v + u) == v * v - u * u) by ring.
  assert (Hvu3 : Qle ((v - u) * 3) ((v - u) * (v + u))).
  { apply (Qmult_le_compat_nonneg (v - u) (v - u) 3 (v + u)).
    - split; [apply (proj1 (Qle_minus_iff u v)); exact Huv | apply Qle_refl].
    - split; [change (Qle 0 3); unfold Qle; simpl; lia | ].
      assert (H3 : Qle 3 (v + u)).
      { apply (Qle_trans _ ((3#2)%Q + (3#2)%Q) _).
        - apply qeq_le. unfold Qdiv. field.
        - apply (Qplus_le_compat (3#2)%Q v (3#2)%Q u).
          + apply (Qle_trans _ u _); [exact Hu3 | exact Huv].
          + exact Hu3. }
      exact H3. }
(* Chain: [v-u <= (v^2-u^2)/3 < 2*(du+dv)]. *)
  apply (Qle_lt_trans (v - u) ((v * v - u * u) * (1 / 3)) (2 * (du + dv))).
  - apply (Qle_trans _ (((v - u) * 3) * (1 / 3)) _).
    + apply qeq_le.
      assert (Hr3 : ((v - u) * 3) * (1 / 3) == v - u)
        by (unfold Qdiv; field; unfold Qeq; simpl; lia).
      apply Qeq_sym. exact Hr3.
    + apply (Qmult_le_compat_r ((v - u) * 3) (v * v - u * u) (1 / 3)).
      * apply (Qle_trans _ ((v - u) * (v + u)) _).
        -- exact Hvu3.
        -- apply qeq_le. exact Hprod.
      * apply (Qlt_le_weak 0 (1 / 3)).
        change (Qlt 0 (1 / 3)). unfold Qdiv. compute. reflexivity.
  - assert (Hm : (v * v - u * u) * (1 / 3) == ((v * v - u * u) * (1 / 6)) * 2)
      by (unfold Qdiv; field; unfold Qeq; simpl; lia).
    assert (Hm2 : (du + dv) * 2 == 2 * (du + dv)) by ring.
    apply (Qlt_le_trans ((v * v - u * u) * (1 / 3)) ((du + dv) * 2) (2 * (du + dv))).
    + apply (Qle_lt_trans ((v * v - u * u) * (1 / 3))
                          (((v * v - u * u) * (1 / 6)) * 2) ((du + dv) * 2)).
      * apply qeq_le. exact Hm.
      * apply (Qmult_lt_compat_r ((v * v - u * u) * (1 / 6)) (du + dv) 2).
        -- change (Qlt 0 2). compute. reflexivity.
        -- exact Hq.
    + apply qeq_le. exact Hm2.
Qed.

(* ============================================================ *)
(* Section 3. The Cauchy property of the sequence *)
(* ============================================================ *)

(* Cauchy property: [|z_m - z_n| -> 0].  Eighth-of-eps budget:
   [eps_m, eps_n < eps/8] and the tail chain [2*(eps_n + eps_m) < eps];
   at a common pairing order [k0 >= 2] the distance-form inverse bound
   gives [|z_m - z_n| < 2*(eps_n + eps_m)]. *)
Lemma cos_seq_cauchy : forall eps : Q, Qlt 0 eps ->
  { N : nat | forall m n : nat, (N <= m)%nat -> (N <= n)%nat ->
      Qlt (Qabs (cos_zero_seq m - cos_zero_seq n)) eps }.
Proof.
  intros eps Heps.
  assert (Heps8 : Qlt 0 (eps / 8)).
  { apply (Qlt_shift_div_l 0 eps 8).
    - change (Qlt 0 8). compute. reflexivity.
    - simpl. exact Heps. }
  assert (H01 : Qle 0 1).
  { apply Qlt_le_weak. change (Qlt 0 1). compute. reflexivity. }
  destruct (vt_pow_half_arch 1 (eps / 8) H01 Heps8) as [t Ht].
  exists (Datatypes.S t).
  intros m n Hm Hn.
  assert (Heps_m_lt : Qlt (log_eps m) (eps / 8)).
  { apply (log_eps_lt_delta (eps / 8) t m).
    - exact Ht.
    - exact Hm. }
  assert (Heps_n_lt : Qlt (log_eps n) (eps / 8)).
  { apply (log_eps_lt_delta (eps / 8) t n).
    - exact Ht.
    - exact Hn. }
(* Tail chain: [2*(eps_n + eps_m) < eps]. *)
  assert (Htail : Qlt (2 * (log_eps n + log_eps m)) eps).
  { assert (Hcom : 2 * (log_eps n + log_eps m) == (log_eps n + log_eps m) * 2) by ring.
    rewrite Hcom.
    assert (Hsum : Qlt (log_eps n + log_eps m) (eps / 4)).
    { apply (Qlt_le_trans (log_eps n + log_eps m) (eps / 8 + eps / 8) (eps / 4)).
      - apply (Qplus_lt_compat (log_eps n) (eps / 8) (log_eps m) (eps / 8));
          [exact Heps_n_lt | exact Heps_m_lt].
      - apply qeq_le. unfold Qdiv. field. }
    apply (Qle_lt_trans ((log_eps n + log_eps m) * 2) ((eps / 4) * 2) eps).
    - apply (Qmult_le_compat_r (log_eps n + log_eps m) (eps / 4) 2).
      + apply Qlt_le_weak. exact Hsum.
      + apply Qlt_le_weak. change (Qlt 0 2). compute. reflexivity.
    - assert (He : (eps / 4) * 2 == eps / 2) by (unfold Qdiv; field).
      apply (Qle_lt_trans ((eps / 4) * 2) (eps / 2) eps).
      + apply qeq_le. exact He.
      + apply (proj2 (Qlt_minus_iff (eps / 2) eps)).
        apply (Qlt_le_trans 0 (eps / 2) (eps - eps / 2)).
        * apply (Qlt_shift_div_l 0 eps 2).
          -- change (Qlt 0 2). compute. reflexivity.
          -- simpl. exact Heps.
        * apply qeq_le. unfold Qminus. field. }
  destruct (Qlt_le_dec (cos_zero_seq n) (cos_zero_seq m)) as [Hnm_lt | Hmn].
  - (* [z_n < z_m]: take [u := z_n], [v := z_m]. *)
    destruct (cos_root_pt_bound n) as [Nn HNn].
    destruct (cos_root_pt_bound m) as [Nm HMm].
    set (k0 := Nat.max 2 (Nat.max Nn Nm)).
    assert (Hk0n : (Nn <= k0)%nat).
    { unfold k0. apply (Nat.le_trans _ (Nat.max Nn Nm) _);
        [apply Nat.le_max_l | apply Nat.le_max_r]. }
    assert (Hk0m : (Nm <= k0)%nat).
    { unfold k0. apply (Nat.le_trans _ (Nat.max Nn Nm) _);
        [apply Nat.le_max_r | apply Nat.le_max_r]. }
    assert (Hd : Qlt (cos_zero_seq m - cos_zero_seq n)
                     (2 * (log_eps n + log_eps m))).
    { apply (cos_inv_dist (cos_zero_seq n) (cos_zero_seq m)
                          (log_eps n) (log_eps m) k0).
      - unfold k0. apply Nat.le_max_l.
      - apply Qlt_le_weak. apply cos_zero_lower.
      - apply Qlt_le_weak. exact Hnm_lt.
      - apply Qlt_le_weak. apply cos_zero_upper.
      - apply (HNn k0). exact Hk0n.
      - apply (HMm k0). exact Hk0m. }
    apply (Qle_lt_trans (Qabs (cos_zero_seq m - cos_zero_seq n))
                        (cos_zero_seq m - cos_zero_seq n) eps).
    + apply qeq_le. apply Qabs_pos.
      apply (proj1 (Qle_minus_iff (cos_zero_seq n) (cos_zero_seq m))).
      apply Qlt_le_weak. exact Hnm_lt.
    + apply (Qle_lt_trans (cos_zero_seq m - cos_zero_seq n)
                          (2 * (log_eps n + log_eps m)) eps).
      * apply Qlt_le_weak. exact Hd.
      * exact Htail.
  - (* [z_m <= z_n]: take [u := z_m], [v := z_n] (symmetric case). *)
    destruct (cos_root_pt_bound m) as [Nm HMm].
    destruct (cos_root_pt_bound n) as [Nn HNn].
    set (k0 := Nat.max 2 (Nat.max Nm Nn)).
    assert (Hk0m : (Nm <= k0)%nat).
    { unfold k0. apply (Nat.le_trans _ (Nat.max Nm Nn) _);
        [apply Nat.le_max_l | apply Nat.le_max_r]. }
    assert (Hk0n : (Nn <= k0)%nat).
    { unfold k0. apply (Nat.le_trans _ (Nat.max Nm Nn) _);
        [apply Nat.le_max_r | apply Nat.le_max_r]. }
    assert (Hd : Qlt (cos_zero_seq n - cos_zero_seq m)
                     (2 * (log_eps m + log_eps n))).
    { apply (cos_inv_dist (cos_zero_seq m) (cos_zero_seq n)
                          (log_eps m) (log_eps n) k0).
      - unfold k0. apply Nat.le_max_l.
      - apply Qlt_le_weak. apply cos_zero_lower.
      - exact Hmn.
      - apply Qlt_le_weak. apply cos_zero_upper.
      - apply (HMm k0). exact Hk0m.
      - apply (HNn k0). exact Hk0n. }
    apply (Qle_lt_trans (Qabs (cos_zero_seq m - cos_zero_seq n))
                        (cos_zero_seq n - cos_zero_seq m) eps).
    + rewrite (Qabs_Qminus (cos_zero_seq m) (cos_zero_seq n)).
      apply qeq_le. apply Qabs_pos.
      apply (proj1 (Qle_minus_iff (cos_zero_seq m) (cos_zero_seq n))).
      exact Hmn.
    + apply (Qle_lt_trans (cos_zero_seq n - cos_zero_seq m)
                          (2 * (log_eps m + log_eps n)) eps).
      * apply Qlt_le_weak. exact Hd.
      * assert (Hcom : 2 * (log_eps m + log_eps n) == 2 * (log_eps n + log_eps m)) by ring.
        rewrite Hcom. exact Htail.
Qed.

(* Assumption audit for all mission statements of this file. *)
Print Assumptions cos_zero_lower.
Print Assumptions cos_zero_upper.
Print Assumptions cos_zero_nonneg.
Print Assumptions cos_zero_le_two.
Print Assumptions cos_zero_abs_le_two.
Print Assumptions cos_root_pt_bound.
Print Assumptions cos_inv_pt.
Print Assumptions cos_inv_dist.
Print Assumptions cos_seq_cauchy.
