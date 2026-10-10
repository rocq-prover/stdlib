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
(* PiHalfwinSeed.v                                              *)
(*                                                              *)
(* Module mission: assembly of the sigma-1 half-window seed       *)
(*   consumption faces -- the supply assembly theorem for the     *)
(*   half-window slot type piLd3_seed_halfwin (merged segment of  *)
(*   PiKernelSlack), the fixed-point arctan consumption face (the *)
(*   sig face of |S_k(lp_odd m) - C_k(lp_odd m)| -> 0, consumed   *)
(*   at the canonical shared instance e := 2dt/13), the cos       *)
(*   zero-sequence signature face, and the fixed-point partial-sum *)
(*   order-Cauchy signature face; once the half-window pair of    *)
(*   witnesses (the cos and sin pieces) is available, the main    *)
(*   statement reaches the premise-free closed form by a one-step *)
(*   assembly.                                                    *)
(* Dependencies: Stdlib QArith (QArith/Qabs), Arith.PeanoNat, Lia; *)
(*       PiKernelSlack (cos_partial/sin_partial, the QltT bridges, *)
(*       and the slot type from its merged segment);              *)
(*       PiLeibnizCReal (lp_odd); QCauchyZeroCos; PiCosZeroSeqConv; *)
(*       PiCosZeroSeqProbe; PiCosPartialSeqCauchy; PiBandBound;   *)
(*       PiCosBandAssemble; PiPythBandDonor; PiArctanFixedQ.      *)
(* References: the piLd3_seed_halfwin slot of the merged          *)
(*       PiKernelSlack segment; PiCosZeroSeqConv (the zero-sequence *)
(*       face); PiCosPartialSeqCauchy (the fixed-point partial-sum *)
(*       order-Cauchy face, orthogonal to the Cauchy property of  *)
(*       the zero-localization sequence).                         *)
(* Constructivity: all consumption faces carried by sig/sigT      *)
(*   (K : nat witnesses); the fixed-point arctan consumption site *)
(*   is carried by an explicitly named premise (piLh_seed_t5alpha) *)
(*   in the faces below; the premise-free closed-form name        *)
(*   piLh_seed_halfwin is closed by a one-line assembly once the  *)
(*   paired witnesses are available (realized at the end of this  *)
(*   file);                                                       *)
(*   positivity in Q goes through the manual chain unfold Qdiv +  *)
(*   Qmult_lt_0_compat + Qinv_lt_0_compat (positivity of Q        *)
(*   division without a nonzero premise), literal positive steps  *)
(*   go unfold Qlt then simpl + lia; nat bookkeeping goes         *)
(*   Nat.le_trans/Nat.le_max_l, no solver.                        *)
(* Zero axioms, zero classical logic, nothing admitted (the     *)
(*   closing Print Assumptions lines at the end of the file are  *)
(*   all Closed).                                                *)
(* Build: coqc -native-compiler no -q -Q . "" PiHalfwinSeed.v     *)
(*   (Rocq 9.1.0).                                                *)
(* ============================================================ *)

(* WARNING: this file is experimental and likely to change in future *)
(* releases.                                                        *)
From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.
Require Import PiLeibnizCReal.
Require Import QCauchyZeroCos.
Require Import PiCosZeroSeqConv.
Require Import PiCosZeroSeqProbe.
Require Import PiCosPartialSeqCauchy.
Require Import PiBandBound.
Require Import PiCosBandAssemble.
Require Import PiPythBandDonor.
Require PiArctanFixedQ.

(* ============================================================ *)
(* ==== §1 The cos zero-sequence consumption signature face (pinned verbatim; ascription = same-source certificate) ==== *)
(* ============================================================ *)

Definition piLh_port_cos_zero_seq : nat -> Q := cos_zero_seq.

Definition piLh_port_cos_zero_lower :
  forall n : nat, Qlt (3#2)%Q (cos_zero_seq n) := cos_zero_lower.

Definition piLh_port_cos_zero_upper :
  forall n : nat, Qlt (cos_zero_seq n) (5#3)%Q := cos_zero_upper.

Definition piLh_port_cos_zero_abs_le_two :
  forall n : nat, Qle (Qabs (cos_zero_seq n)) 2 := cos_zero_abs_le_two.

Definition piLh_port_cos_inv_dist :
  forall (u v du dv : Q) (k : nat),
    (2 <= k)%nat -> Qle (3#2)%Q u -> Qle u v -> Qle v (5#3)%Q ->
    Qlt (Qabs (cos_partial k u)) du ->
    Qlt (Qabs (cos_partial k v)) dv ->
    Qlt (v - u) (2 * (du + dv)) := cos_inv_dist.

(* ============================================================ *)
(* ==== §2 The half-power family consumption signature faces (group G, six pieces) ==== *)
(* ============================================================ *)

Definition piLh_port_log_eps : nat -> Q := log_eps.

Definition piLh_port_q_pow_half_le :
  forall n : nat, Qle (q_pow (1 / 2) (Datatypes.S n)) (q_pow (1 / 2) n) :=
  q_pow_half_le.

Definition piLh_port_q_pow_half_lt_self :
  forall n : nat, Qlt (q_pow (1 / 2) (Datatypes.S n)) (q_pow (1 / 2) n) :=
  q_pow_half_lt_self.

Definition piLh_port_q_pow_half_mono :
  forall m n : nat, (m <= n)%nat -> Qle (q_pow (1 / 2) n) (q_pow (1 / 2) m) :=
  q_pow_half_mono.

Definition piLh_port_log_eps_pos :
  forall n : nat, Qlt 0 (log_eps n) := log_eps_pos.

Definition piLh_port_log_eps_lt_delta :
  forall (delta : Q) (t m : nat),
    Qlt (1 * q_pow (1 / 2) t) delta ->
    (Datatypes.S t <= m)%nat ->
    Qlt (log_eps m) delta := log_eps_lt_delta.

(* ============================================================ *)
(* ==== §3 The fixed-point partial-sum order-Cauchy consumption signature face ==== *)
(* (The orthogonal complement of the paired witness faces: for the fixed point *)
(*   z_m and tolerance dt > 0 it gives K such that all k >= K satisfy          *)
(*   |P_k(z_m) - P_K(z_m)| < dt; consumption pattern                           *)
(*   destruct (cos_partial_seq_cauchy m dt Hdt) as [K HK].)                   *)
(* ============================================================ *)

Definition piLh_port_cos_partial_seq_cauchy :
  forall (m : nat) (dt : Q), Qlt 0 dt ->
    {K : nat | forall k : nat, (K <= k)%nat ->
       Qlt (Qabs (cos_partial k (cos_zero_seq m) - cos_partial K (cos_zero_seq m)))
           dt} :=
  cos_partial_seq_cauchy.

(* ============================================================ *)
(* ==== §4 The fixed-point arctan consumption face (explicitly named premise) and the instance e := 2dt/13 ==== *)
(* ============================================================ *)

(* The premise of the consumption face (named premise slot; the sole fixed-point *)
(*   input of the paired witness faces): for every e > 0 there is K such that   *)
(*   1 <= k, K <= k, K <= m imply |S_k(lp_odd m) - C_k(lp_odd m)| < e.          *)
Definition piLh_seed_t5alpha :=
  forall e : Q, Qlt 0 e ->
    {K : nat | forall (k m : nat), (1 <= k)%nat -> (K <= k)%nat -> (K <= m)%nat ->
       Qlt (Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m))) e}.

Lemma piLh_seed_qtwo_pos : Qlt 0 (2#1)%Q.
Proof. unfold Qlt. simpl. lia. Qed.

Lemma piLh_seed_qthirteen_pos : Qlt 0 (13#1)%Q.
Proof. unfold Qlt. simpl. lia. Qed.

(* Positivity of the canonical shared instance e := 2dt/13 (the 2/13 share of the tolerance dt): *)
(*   2dt/13 = 2dt * (1/13), both factors positive.                              *)
Lemma piLh_seed_qlt_share : forall dt : Q, Qlt 0 dt -> Qlt 0 (Qdiv (2 * dt) 13).
Proof.
  intros dt Hdt. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - rewrite Qmult_comm. change (0 * (2#1)%Q < dt * (2#1)%Q)%Q.
    exact (Qmult_lt_compat_r 0 dt (2#1)%Q piLh_seed_qtwo_pos Hdt).
  - exact (Qinv_lt_0_compat (13#1)%Q piLh_seed_qthirteen_pos).
Qed.

(* Instance consumption form: the fixed-point value of the premise face at      *)
(*   e := 2dt/13 -- the form directly consumable by the paired witnesses        *)
(*   (half-window cos / half-window sin).                                       *)
Definition piLh_seed_share :
  piLh_seed_t5alpha ->
  forall dt : Q, Qlt 0 dt ->
    {K : nat | forall (k m : nat), (1 <= k)%nat -> (K <= k)%nat -> (K <= m)%nat ->
       Qlt (Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m)))
           (Qdiv (2 * dt) 13)} :=
  fun Halpha dt Hdt => Halpha (Qdiv (2 * dt) 13) (piLh_seed_qlt_share dt Hdt).

(* Binding of the fixed-point arctan partial-sum agreement supply theorem
   (PiArctanFixedQ): the consumption entry piLh_seed_share is connected to
   the supply through it (the shared instance e := 2dt/13). *)
Definition piLh_seed_t5alpha_supply : piLh_seed_t5alpha :=
  PiArctanFixedQ.piL_arctan_fixed_sc.

(* ============================================================ *)
(* ==== §5 The half-window pair witness faces and the slot assembly ==== *)
(* ============================================================ *)

Definition piLh_seed_halfwin_cos_face :=
  forall dt : Q, Qlt 0 dt ->
    {K : nat | forall (k m : nat), (K <= k)%nat -> (K <= m)%nat ->
       Qlt (Qabs (cos_partial k (2 * lp_odd m))) dt}.

Definition piLh_seed_halfwin_sin_face :=
  forall dt : Q, Qlt 0 dt ->
    {K : nat | forall (k m : nat), (K <= k)%nat -> (K <= m)%nat ->
       Qlt (Qabs (sin_partial k (2 * lp_odd m) - (1 # 1)%Q)) dt}.

(* Slot assembly: the K of the half-window pair of witnesses (same instance of *)
(*   dt) is taken as the max; the two components enter the Set-level product   *)
(*   through the Qlt -> QltT bridges.                                          *)
Theorem piLh_seed_halfwin_pair :
  piLh_seed_halfwin_cos_face -> piLh_seed_halfwin_sin_face -> piLd3_seed_halfwin.
Proof.
  intros Hc Hs dt Hdt.
  apply QltT_to_Qlt in Hdt.
  destruct (Hc dt Hdt) as [Kc HKc].
  destruct (Hs dt Hdt) as [Ks HKs].
  exists (Nat.max Kc Ks).
  intros k m Hk Hm.
  split.
  - apply Qlt_to_QltT. apply HKc.
    + exact (Nat.le_trans Kc (Nat.max Kc Ks) k (Nat.le_max_l Kc Ks) Hk).
    + exact (Nat.le_trans Kc (Nat.max Kc Ks) m (Nat.le_max_l Kc Ks) Hm).
  - apply Qlt_to_QltT. apply HKs.
    + exact (Nat.le_trans Ks (Nat.max Kc Ks) k (Nat.le_max_r Kc Ks) Hk).
    + exact (Nat.le_trans Ks (Nat.max Kc Ks) m (Nat.le_max_r Kc Ks) Hm).
Defined.

(* ============================================================ *)
(* Gate assembly (realized at the end of this file): the paired witnesses close  *)
(*   the slot in one line:                                                       *)
(*     Definition piLh_seed_halfwin : piLd3_seed_halfwin :=                      *)
(*       piLh_seed_halfwin_pair <half-window cos witness> <half-window sin witness>. *)
(*   A witness face taking piLh_seed_t5alpha as a premise is instantiated        *)
(*   through piLh_seed_share (the shared instance e := 2dt/13).                  *)
(* ============================================================ *)

(* ============================================================ *)
(* ==== §6 The half-window pair of witnesses (cos_face/sin_face, machine assembly) ==== *)
(* ============================================================ *)

Lemma piLw_q26_pos : Qlt 0 (26#1)%Q.
Proof. unfold Qlt. simpl. lia. Qed.

Lemma piLw_q1_pos : Qlt 0 (1#1)%Q.
Proof. unfold Qlt. simpl. lia. Qed.

Lemma piLw_sq_nonneg : forall x : Q, Qle 0 (x * x).
Proof.
  intros x.
  destruct (Qlt_le_dec 0 x) as [Hpos | Hneg].
  - apply piLe_qmult_nonneg_r; apply Qlt_le_weak; exact Hpos.
  - assert (Hn : Qle 0 (- x)).
    { rewrite <- (Qplus_0_l (- x)).
      exact (proj1 (Qle_minus_iff x 0) Hneg). }
    assert (Heq : x * x == (- x) * (- x)) by ring.
    rewrite Heq.
    apply piLe_qmult_nonneg_r; exact Hn.
Qed.

Lemma piLw_opp_le_0 : forall x : Q, Qle 0 x -> Qle (- x) 0.
Proof.
  intros x H.
  assert (Hstep : Qle ((- (1#1)%Q) * x) (0 * x))
    by (apply Qmult_le_compat_r;
        [ (change (Qle (- (1#1)%Q) 0); unfold Qle; simpl; lia)
        | exact H ]).
  rewrite Qmult_0_l in Hstep.
  apply (Qle_trans (- x) ((- (1#1)%Q) * x) 0).
  - apply qeq_le. ring.
  - exact Hstep.
Qed.

Lemma piLw_abs_nonpos : forall a : Q, Qle a 0 -> Qabs a == - a.
Proof.
  intros a Ha.
  rewrite <- Qabs_opp.
  apply Qabs_pos.
  rewrite <- (Qplus_0_l (- a)).
  exact (proj1 (Qle_minus_iff a 0) Ha).
Qed.

Lemma piLw_le_abs : forall x : Q, Qle x (Qabs x).
Proof.
  intros x.
  destruct (Qlt_le_dec 0 x) as [Hpos | Hneg].
  - rewrite (Qabs_pos x (Qlt_le_weak _ _ Hpos)). apply Qle_refl.
  - rewrite (piLw_abs_nonpos x Hneg).
    apply (Qle_trans x 0 (- x)).
    + exact Hneg.
    + rewrite <- (Qplus_0_l (- x)).
      exact (proj1 (Qle_minus_iff x 0) Hneg).
Qed.

Lemma piLw_plus_lt_same : forall x y z : Q, Qlt x y -> Qlt (z + x) (z + y).
Proof.
  intros x y z H.
  destruct (Qlt_le_dec (z + x) (z + y)) as [Hlt | Hge].
  - exact Hlt.
  - exfalso.
    assert (Hyx : Qle y x).
    { assert (Hz1 : y == (z + y) + (- z)) by field.
      assert (Hz2 : x == (z + x) + (- z)) by field.
      rewrite Hz1, Hz2.
      exact (Qplus_le_compat (z + y) (z + x) (- z) (- z) Hge
               (Qle_refl (- z))). }
    apply (Qlt_irrefl x).
    exact (Qlt_le_trans x y x H Hyx).
Qed.

Lemma piLw_abs_le_of_sq : forall a b : Q,
  Qlt 0 b -> Qle (a * a) (b * b) -> Qle (Qabs a) b.
Proof.
  intros a b Hb0 Hsq.
  destruct (Qlt_le_dec b (Qabs a)) as [Hlt | Hle].
  - exfalso.
    assert (Habsq : Qabs a * Qabs a == a * a).
    { destruct (Qlt_le_dec 0 a) as [Hap | Han].
      - rewrite (Qabs_pos a (Qlt_le_weak _ _ Hap)). apply Qeq_refl.
      - rewrite (piLw_abs_nonpos a Han). ring. }
    assert (Hlt2 : Qlt (b * b) (a * a)).
    { assert (H1 : Qlt (b * b) (Qabs a * b)).
      { apply (Qmult_lt_compat_r _ _ _ Hb0 Hlt). }
      assert (H2 : Qle (Qabs a * b) (Qabs a * Qabs a)).
      { apply (Qle_trans (Qabs a * b) (b * Qabs a) (Qabs a * Qabs a)).
        - apply qeq_le. ring.
        - exact (piLe_qmult_le_nonneg4 b (Qabs a) (Qabs a) (Qabs a)
                   (Qlt_le_weak _ _ Hb0) (Qlt_le_weak _ _ Hlt)
                   (Qabs_nonneg a) (Qle_refl (Qabs a))). }
      rewrite <- Habsq.
      exact (Qlt_le_trans _ _ _ H1 H2). }
    apply (Qlt_irrefl (b * b)).
    exact (Qlt_le_trans _ _ _ Hlt2 Hsq).
  - exact Hle.
Qed.

(* Individual square-sum bound machine: u^2+v^2==1+d and |d|<e imply |u|<=1+e (fully abstract, shared by the sin and cos pieces) *)
Lemma piLw_one_sq_bound : forall u v d e : Q,
  Qle 0 e ->
  (u * u + v * v == 1 + d) ->
  Qlt (Qabs d) e ->
  Qle (Qabs u) (1 + e).
Proof.
  intros u v d e He Huv Hde.
  assert (Hr : u * u == 1 + d - v * v).
  { rewrite <- Huv. ring. }
  assert (Huu : Qle (u * u) (1 + Qabs d)).
  { rewrite Hr.
    assert (Hv2 : Qle 0 (v * v)) by (apply piLw_sq_nonneg).
    apply (Qle_trans _ (1 + d)).
    - apply (Qle_trans _ ((1 + d) + (-(v * v)))).
      + apply qeq_le. ring.
      + apply (Qle_trans _ ((1 + d) + 0)).
        * apply (Qplus_le_compat (1 + d) (1 + d) (-(v * v)) 0).
          -- apply Qle_refl.
          -- apply (piLw_opp_le_0 (v * v) Hv2).
        * apply qeq_le. ring.
    - apply (Qplus_le_compat (1#1)%Q (1#1)%Q d (Qabs d)).
      + apply Qle_refl.
      + apply piLw_le_abs. }
  assert (Hb1 : Qle 0 (1 + e)).
  { apply (Qle_trans _ (1#1)%Q).
    - change (Qle 0 (1#1)%Q). unfold Qle. simpl. lia.
    - apply (Qplus_le_compat (1#1)%Q (1#1)%Q 0 e).
      + apply Qle_refl.
      + exact He. }
  apply (piLw_abs_le_of_sq u (1 + e)).
  - apply (Qlt_le_trans _ (1#1)%Q).
    + exact piLw_q1_pos.
    + apply (Qle_trans _ ((1#1)%Q + 0)).
      * apply qeq_le. ring.
      * apply (Qplus_le_compat (1#1)%Q (1#1)%Q 0 e).
        -- apply Qle_refl.
        -- exact He.
  - apply (Qle_trans _ (1 + e)).
    + apply (Qle_trans _ (1 + Qabs d)).
      * exact Huu.
      * apply (Qlt_le_weak (1 + Qabs d) (1 + e)).
        exact (piLw_plus_lt_same (Qabs d) e (1#1)%Q Hde).
    + assert (Hbb : (1 + e) * (1 + e) == (1 + e) + (1 + e) * e) by ring.
      rewrite Hbb.
      apply (Qle_trans _ ((1 + e) + 0)).
      * apply qeq_le. ring.
      * apply (Qplus_le_compat (1 + e) (1 + e) 0 ((1 + e) * e)).
        -- apply Qle_refl.
        -- apply piLe_qmult_nonneg_r; [ exact Hb1 | exact He ].
Qed.

(* Numeric closed form A (cos piece): (2t/13)(2+2t/13) + t/13 <= t, for 0 <= t <= 26 *)
Lemma piLw_cos_num : forall t : Q,
  Qle 0 t -> Qle t (26#1)%Q ->
  Qle (Qdiv (2 * t) 13 * (2 + Qdiv (2 * t) 13) + Qdiv t 13) t.
Proof.
  intros t Ht0 Ht26.
  assert (Hsq : Qle (t * t) ((26#1)%Q * t))
    by (apply Qmult_le_compat_r; assumption).
  assert (H4a : Qle ((4#1)%Q * (t * t)) ((104#1)%Q * t)).
  { apply (Qle_trans _ ((4#1)%Q * ((26#1)%Q * t))).
    - apply (piLe_qmult_le_nonneg4 (4#1)%Q (4#1)%Q (t * t) ((26#1)%Q * t)).
      + change (Qle 0 (4#1)%Q). unfold Qle. simpl. lia.
      + apply Qle_refl.
      + apply piLw_sq_nonneg.
      + exact Hsq.
    - apply qeq_le. ring. }
  assert (H4 : Qle ((4#1)%Q * (t * t) * / (169#1)%Q)
                   (((104#1)%Q * t) * / (169#1)%Q))
    by (apply Qmult_le_compat_r;
        [ exact H4a
        | (change (Qle 0 (/ (169#1)%Q)); unfold Qle; simpl; lia) ]).
  assert (H8 : ((104#1)%Q * t) * / (169#1)%Q
               == ((8#1)%Q * t) * / (13#1)%Q) by field.
  assert (H13 : ((5#1)%Q * t) * / (13#1)%Q + ((8#1)%Q * t) * / (13#1)%Q
                == ((13#1)%Q * t) * / (13#1)%Q) by field.
  assert (H1 : ((13#1)%Q * t) * / (13#1)%Q == t) by field.
  assert (Hexp : Qdiv (2 * t) 13 * (2 + Qdiv (2 * t) 13) + Qdiv t 13
                 == ((5#1)%Q * t) * / (13#1)%Q
                    + ((4#1)%Q * (t * t)) * / (169#1)%Q)
    by (unfold Qdiv; field).
  rewrite Hexp.
  apply (Qle_trans _ (((5#1)%Q * t) * / (13#1)%Q
                      + ((104#1)%Q * t) * / (169#1)%Q)).
  - apply Qplus_le_compat; [ apply Qle_refl | exact H4 ].
  - rewrite H8.
    apply (Qle_trans _ (((13#1)%Q * t) * / (13#1)%Q)).
    + rewrite <- H13. apply Qle_refl.
    + rewrite H1. apply Qle_refl.
Qed.

(* Numeric closed form B (sin piece): (2t/13)^2 + t/13 + t/13 <= t, for 0 <= t <= 26 *)
Lemma piLw_sin_num : forall t : Q,
  Qle 0 t -> Qle t (26#1)%Q ->
  Qle (Qdiv (2 * t) 13 * Qdiv (2 * t) 13 + Qdiv t 13 + Qdiv t 13) t.
Proof.
  intros t Ht0 Ht26.
  assert (Hsq : Qle (t * t) ((26#1)%Q * t))
    by (apply Qmult_le_compat_r; assumption).
  assert (H4a : Qle ((4#1)%Q * (t * t)) ((104#1)%Q * t)).
  { apply (Qle_trans _ ((4#1)%Q * ((26#1)%Q * t))).
    - apply (piLe_qmult_le_nonneg4 (4#1)%Q (4#1)%Q (t * t) ((26#1)%Q * t)).
      + change (Qle 0 (4#1)%Q). unfold Qle. simpl. lia.
      + apply Qle_refl.
      + apply piLw_sq_nonneg.
      + exact Hsq.
    - apply qeq_le. ring. }
  assert (H4 : Qle ((4#1)%Q * (t * t) * / (169#1)%Q)
                   (((8#1)%Q * t) * / (13#1)%Q)).
  { assert (H4b : Qle ((4#1)%Q * (t * t) * / (169#1)%Q)
                      (((104#1)%Q * t) * / (169#1)%Q))
      by (apply Qmult_le_compat_r;
          [ exact H4a
          | (change (Qle 0 (/ (169#1)%Q)); unfold Qle; simpl; lia) ]).
    apply (Qle_trans _ (((104#1)%Q * t) * / (169#1)%Q)).
    - exact H4b.
    - apply qeq_le. field. }
  assert (H10 : ((8#1)%Q * t) * / (13#1)%Q + Qdiv t 13 + Qdiv t 13
                == ((10#1)%Q * t) * / (13#1)%Q) by field.
  assert (H1 : ((13#1)%Q * t) * / (13#1)%Q == t) by field.
  assert (Hle : Qle (((10#1)%Q * t) * / (13#1)%Q) t).
  { assert (Hnorm : ((10#1)%Q * t) * / (13#1)%Q
                    == (10#1)%Q * (t * / (13#1)%Q)) by field.
    rewrite Hnorm.
    apply (Qle_trans _ ((13#1)%Q * (t * / (13#1)%Q))).
    - apply Qmult_le_compat_r.
      + change (Qle (10#1)%Q (13#1)%Q). unfold Qle. simpl. lia.
      + change (Qle 0 (t * / (13#1)%Q)).
        apply piLe_qmult_nonneg_r.
        * exact Ht0.
        * change (Qle 0 (/ (13#1)%Q)). unfold Qle. simpl. lia.
    - apply qeq_le. field. }
  assert (Hexp : Qdiv (2 * t) 13 * Qdiv (2 * t) 13
                 == ((4#1)%Q * (t * t)) * / (169#1)%Q)
    by (unfold Qdiv; field).
  rewrite Hexp.
  apply (Qle_trans _ (((8#1)%Q * t) * / (13#1)%Q + Qdiv t 13 + Qdiv t 13)).
  - apply Qplus_le_compat;
      [ apply Qplus_le_compat; [ exact H4 | apply Qle_refl ]
      | apply Qle_refl ].
  - rewrite H10. exact Hle.
Qed.

(* The cos half-window witness core: the three-machine assembly for the dt0 <= 26 tier *)
Lemma piLw_cos_core : forall dt0 : Q,
  Qlt 0 dt0 -> Qle dt0 (26#1)%Q ->
  {K : nat | forall (k m : nat), (K <= k)%nat -> (K <= m)%nat ->
     Qlt (Qabs (cos_partial k (2 * lp_odd m))) dt0}.
Proof.
  intros dt0 Hdt0 Ht26.
  assert (Hdivpos : Qlt 0 (Qdiv dt0 13)).
  { unfold Qdiv. apply Qmult_lt_0_compat.
    - exact Hdt0.
    - exact (Qinv_lt_0_compat (13#1)%Q piLh_seed_qthirteen_pos). }
  assert (Hpos13 : Qle 0 (Qdiv dt0 13)) by (apply Qlt_le_weak; exact Hdivpos).
  assert (Hpos2 : Qle 0 (2 + Qdiv (2 * dt0) 13)).
  { apply (Qle_trans _ (2#1)%Q).
    - change (Qle 0 (2#1)%Q). unfold Qle. simpl. lia.
    - apply (Qplus_le_compat (2#1)%Q (2#1)%Q 0 (Qdiv (2 * dt0) 13)).
      + apply Qle_refl.
      + change (Qle 0 (Qdiv (2 * dt0) 13)).
        unfold Qdiv.
        apply piLe_qmult_nonneg_r.
        * apply (piLe_qmult_nonneg_r (2#1)%Q dt0).
          -- change (Qle 0 (2#1)%Q). unfold Qle. simpl. lia.
          -- apply Qlt_le_weak. exact Hdt0.
        * change (Qle 0 (/ (13#1)%Q)). unfold Qle. simpl. lia. }
  destruct (piLh_seed_share piLh_seed_t5alpha_supply dt0 Hdt0) as [K1 HK1].
  destruct (piLh_pyth_small (lp_odd 2 + lp_a 6)%Q (Qdiv dt0 13)
                            piLd3_s6_pos Hdivpos) as [K2 HK2].
  destruct (piLe_dcos_small (lp_odd 2 + lp_a 6)%Q (Qdiv dt0 13)
                            piLd3_s6_pos Hdivpos) as [K3 HK3].
  exists (Datatypes.S (Nat.max K1 (Nat.max K2 K3))).
  intros k m Hk Hm.
  assert (HN : (Nat.max K1 (Nat.max K2 K3) <= k)%nat).
  { apply (Nat.le_trans _ (Datatypes.S (Nat.max K1 (Nat.max K2 K3)))).
    - apply Nat.le_succ_diag_r.
    - exact Hk. }
  assert (HNm : (Nat.max K1 (Nat.max K2 K3) <= m)%nat).
  { apply (Nat.le_trans _ (Datatypes.S (Nat.max K1 (Nat.max K2 K3)))).
    - apply Nat.le_succ_diag_r.
    - exact Hm. }
  assert (Hk1 : (1 <= k)%nat) by lia.
  assert (HK1k : (K1 <= k)%nat)
    by (apply (Nat.le_trans K1 (Nat.max K1 (Nat.max K2 K3)) k);
        [ apply Nat.le_max_l | exact HN ]).
  assert (HK1m : (K1 <= m)%nat)
    by (apply (Nat.le_trans K1 (Nat.max K1 (Nat.max K2 K3)) m);
        [ apply Nat.le_max_l | exact HNm ]).
  assert (HK2k : (K2 <= k)%nat).
  { apply (Nat.le_trans K2 (Nat.max K1 (Nat.max K2 K3)) k).
    - apply (Nat.le_trans K2 (Nat.max K2 K3)).
      + apply Nat.le_max_l.
      + apply Nat.le_max_r.
    - exact HN. }
  assert (HK3k : (K3 <= k)%nat).
  { apply (Nat.le_trans K3 (Nat.max K1 (Nat.max K2 K3)) k).
    - apply (Nat.le_trans K3 (Nat.max K2 K3)).
      + apply Nat.le_max_r.
      + apply Nat.le_max_r.
    - exact HN. }
  assert (HBm : Qle (Qabs (lp_odd m)) (lp_odd 2 + lp_a 6)%Q).
  { apply (QleT'_to_Qle (Qabs (lp_odd m)) (lp_odd 2 + lp_a 6)%Q).
    apply (piLd3_u_abs_le_s6 m). }
  pose proof (HK1 k m Hk1 HK1k HK1m) as Hsc.
  pose proof (HK2 k (lp_odd m) HK2k HBm) as Hpy.
  pose proof (HK3 k (lp_odd m) HK3k HBm) as Hdc.
  assert (Hsabs : Qle (Qabs (sin_partial k (lp_odd m))) (1 + Qdiv dt0 13)).
  { apply (piLw_one_sq_bound
             (sin_partial k (lp_odd m)) (cos_partial k (lp_odd m))
             (piL_pyth_dres k (lp_odd m)) (Qdiv dt0 13)).
    - exact Hpos13.
    - exact (piL_pythag_partial k (lp_odd m)).
    - exact Hpy. }
  assert (Hpythcs : cos_partial k (lp_odd m) * cos_partial k (lp_odd m)
                    + sin_partial k (lp_odd m) * sin_partial k (lp_odd m)
                    == 1 + piL_pyth_dres k (lp_odd m))
    by (rewrite <- (piL_pythag_partial k (lp_odd m)); ring).
  assert (Hcabs : Qle (Qabs (cos_partial k (lp_odd m))) (1 + Qdiv dt0 13)).
  { apply (piLw_one_sq_bound
             (cos_partial k (lp_odd m)) (sin_partial k (lp_odd m))
             (piL_pyth_dres k (lp_odd m)) (Qdiv dt0 13)).
    - exact Hpos13.
    - exact Hpythcs.
    - exact Hpy. }
  rewrite (piL_cos_partial_double k (lp_odd m)).
  apply (Qle_lt_trans _
    (Qdiv (2 * dt0) 13 * (2 + Qdiv (2 * dt0) 13)
     + Qabs (piL_cos_dres k (lp_odd m)))).
  { apply (Qle_trans _
      (Qabs (cos_partial k (lp_odd m) * cos_partial k (lp_odd m)
             - sin_partial k (lp_odd m) * sin_partial k (lp_odd m))
       + Qabs (piL_cos_dres k (lp_odd m)))).
    - apply Qabs_triangle.
    - assert (Hid : cos_partial k (lp_odd m) * cos_partial k (lp_odd m)
                    - sin_partial k (lp_odd m) * sin_partial k (lp_odd m)
                    == (cos_partial k (lp_odd m) - sin_partial k (lp_odd m))
                       * (cos_partial k (lp_odd m) + sin_partial k (lp_odd m)))
        by ring.
      rewrite (Qabs_wd _ _ Hid).
      rewrite Qabs_Qmult.
      apply Qplus_le_compat; [ | apply Qle_refl ].
      apply (piLe_qmult_le_nonneg4
               (Qabs (cos_partial k (lp_odd m) - sin_partial k (lp_odd m)))
               (Qdiv (2 * dt0) 13)
               (Qabs (cos_partial k (lp_odd m) + sin_partial k (lp_odd m)))
               (2 + Qdiv (2 * dt0) 13)).
      + apply Qabs_nonneg.
      + assert (Hidc : cos_partial k (lp_odd m) - sin_partial k (lp_odd m)
                       == - (sin_partial k (lp_odd m)
                             - cos_partial k (lp_odd m))) by ring.
        rewrite (Qabs_wd _ _ Hidc).
        rewrite Qabs_opp.
        apply (Qlt_le_weak _ _ Hsc).
      + apply Qabs_nonneg.
      + apply (Qle_trans _ (Qabs (cos_partial k (lp_odd m))
                             + Qabs (sin_partial k (lp_odd m)))).
        * apply Qabs_triangle.
        * apply (Qle_trans _ ((1 + Qdiv dt0 13) + (1 + Qdiv dt0 13))).
          -- apply Qplus_le_compat; assumption.
          -- assert (Hbb : (1 + Qdiv dt0 13) + (1 + Qdiv dt0 13)
                           == 2 + Qdiv (2 * dt0) 13)
               by (unfold Qdiv; ring).
             apply qeq_le. exact Hbb. }
  { apply (Qlt_le_trans _
      (Qdiv (2 * dt0) 13 * (2 + Qdiv (2 * dt0) 13) + Qdiv dt0 13)).
    - apply (piLw_plus_lt_same _ _ _). exact Hdc.
    - exact (piLw_cos_num dt0 (Qlt_le_weak _ _ Hdt0) Ht26). }
Qed.

(* The sin half-window witness core: the four-machine assembly for the dt0 <= 26 tier *)
Lemma piLw_sin_core : forall dt0 : Q,
  Qlt 0 dt0 -> Qle dt0 (26#1)%Q ->
  {K : nat | forall (k m : nat), (K <= k)%nat -> (K <= m)%nat ->
     Qlt (Qabs (sin_partial k (2 * lp_odd m) - (1#1)%Q)) dt0}.
Proof.
  intros dt0 Hdt0 Ht26.
  assert (Hdivpos : Qlt 0 (Qdiv dt0 13)).
  { unfold Qdiv. apply Qmult_lt_0_compat.
    - exact Hdt0.
    - exact (Qinv_lt_0_compat (13#1)%Q piLh_seed_qthirteen_pos). }
  assert (Hpos13 : Qle 0 (Qdiv dt0 13)) by (apply Qlt_le_weak; exact Hdivpos).
  destruct (piLh_seed_share piLh_seed_t5alpha_supply dt0 Hdt0) as [K1 HK1].
  destruct (piLh_pyth_small (lp_odd 2 + lp_a 6)%Q (Qdiv dt0 13)
                            piLd3_s6_pos Hdivpos) as [K2 HK2].
  destruct (piLd_dres_small (lp_odd 2 + lp_a 6)%Q (Qdiv dt0 13)
                            piLd3_s6_pos Hdivpos) as [K3 HK3].
  exists (Datatypes.S (Nat.max K1 (Nat.max K2 K3))).
  intros k m Hk Hm.
  assert (HN : (Nat.max K1 (Nat.max K2 K3) <= k)%nat).
  { apply (Nat.le_trans _ (Datatypes.S (Nat.max K1 (Nat.max K2 K3)))).
    - apply Nat.le_succ_diag_r.
    - exact Hk. }
  assert (HNm : (Nat.max K1 (Nat.max K2 K3) <= m)%nat).
  { apply (Nat.le_trans _ (Datatypes.S (Nat.max K1 (Nat.max K2 K3)))).
    - apply Nat.le_succ_diag_r.
    - exact Hm. }
  assert (Hk1 : (1 <= k)%nat) by lia.
  assert (HK1k : (K1 <= k)%nat)
    by (apply (Nat.le_trans K1 (Nat.max K1 (Nat.max K2 K3)) k);
        [ apply Nat.le_max_l | exact HN ]).
  assert (HK1m : (K1 <= m)%nat)
    by (apply (Nat.le_trans K1 (Nat.max K1 (Nat.max K2 K3)) m);
        [ apply Nat.le_max_l | exact HNm ]).
  assert (HK2k : (K2 <= k)%nat).
  { apply (Nat.le_trans K2 (Nat.max K1 (Nat.max K2 K3)) k).
    - apply (Nat.le_trans K2 (Nat.max K2 K3)).
      + apply Nat.le_max_l.
      + apply Nat.le_max_r.
    - exact HN. }
  assert (HK3k : (K3 <= k)%nat).
  { apply (Nat.le_trans K3 (Nat.max K1 (Nat.max K2 K3)) k).
    - apply (Nat.le_trans K3 (Nat.max K2 K3)).
      + apply Nat.le_max_r.
      + apply Nat.le_max_r.
    - exact HN. }
  assert (HBm : Qle (Qabs (lp_odd m)) (lp_odd 2 + lp_a 6)%Q).
  { apply (QleT'_to_Qle (Qabs (lp_odd m)) (lp_odd 2 + lp_a 6)%Q).
    apply (piLd3_u_abs_le_s6 m). }
  pose proof (HK1 k m Hk1 HK1k HK1m) as Hsc.
  pose proof (HK2 k (lp_odd m) HK2k HBm) as Hpy.
  pose proof (HK3 k (lp_odd m) HK3k HBm) as Hdres.
  rewrite (piL_sin_partial_double_at k (lp_odd m)).
  assert (Hid : 2 * sin_partial k (lp_odd m) * cos_partial k (lp_odd m)
                - piL_sin_dres k (lp_odd m) - (1#1)%Q
                == - ((sin_partial k (lp_odd m) - cos_partial k (lp_odd m))
                      * (sin_partial k (lp_odd m) - cos_partial k (lp_odd m)))
                     + piL_pyth_dres k (lp_odd m)
                     - piL_sin_dres k (lp_odd m)).
  { assert (Hd1 : piL_pyth_dres k (lp_odd m)
                  == sin_partial k (lp_odd m) * sin_partial k (lp_odd m)
                     + cos_partial k (lp_odd m) * cos_partial k (lp_odd m)
                     - 1).
    { rewrite piL_pythag_partial. ring. }
    rewrite Hd1. ring. }
  rewrite Hid.
  assert (Hsplit :
    (- ((sin_partial k (lp_odd m) - cos_partial k (lp_odd m))
        * (sin_partial k (lp_odd m) - cos_partial k (lp_odd m)))
     + piL_pyth_dres k (lp_odd m) - piL_sin_dres k (lp_odd m))
    == ((- ((sin_partial k (lp_odd m) - cos_partial k (lp_odd m))
            * (sin_partial k (lp_odd m) - cos_partial k (lp_odd m))))
        + (piL_pyth_dres k (lp_odd m)
           + (- (piL_sin_dres k (lp_odd m))))))
    by ring.
  rewrite Hsplit.
  apply (Qle_lt_trans _
    (Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m))
     * Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m))
     + (Qabs (piL_pyth_dres k (lp_odd m)) + Qabs (piL_sin_dres k (lp_odd m))))).
  { apply (Qle_trans _
      (Qabs (- ((sin_partial k (lp_odd m) - cos_partial k (lp_odd m))
                * (sin_partial k (lp_odd m) - cos_partial k (lp_odd m))))
       + Qabs (piL_pyth_dres k (lp_odd m)
               + (- (piL_sin_dres k (lp_odd m)))))).
    - apply Qabs_triangle.
    - rewrite Qabs_opp.
      rewrite Qabs_Qmult.
      apply (Qplus_le_compat _ _ _ _).
      + apply Qle_refl.
      + apply (Qle_trans _ (Qabs (piL_pyth_dres k (lp_odd m))
                             + Qabs (- (piL_sin_dres k (lp_odd m))))).
        * apply Qabs_triangle.
        * rewrite Qabs_opp. apply Qle_refl. }
  { apply (Qlt_le_trans _
      (Qdiv (2 * dt0) 13 * Qdiv (2 * dt0) 13
       + (Qdiv dt0 13 + Qdiv dt0 13))).
    - apply (Qle_lt_trans _
        (Qdiv (2 * dt0) 13 * Qdiv (2 * dt0) 13
         + (Qabs (piL_pyth_dres k (lp_odd m))
            + Qabs (piL_sin_dres k (lp_odd m))))).
      + apply (Qplus_le_compat _ _ _ _).
        * exact (piLe_qmult_le_nonneg4
                   (Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m)))
                   (Qdiv (2 * dt0) 13)
                   (Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m)))
                   (Qdiv (2 * dt0) 13)
                   (Qabs_nonneg _) (Qlt_le_weak _ _ Hsc)
                   (Qabs_nonneg _) (Qlt_le_weak _ _ Hsc)).
        * apply Qle_refl.
      + apply (piLw_plus_lt_same _ _ _).
        exact (Qplus_lt_compat _ _ _ _ Hpy Hdres).
    - apply (Qle_trans _ (Qdiv (2 * dt0) 13 * Qdiv (2 * dt0) 13
                          + Qdiv dt0 13 + Qdiv dt0 13)).
      + apply qeq_le. ring.
      + exact (piLw_sin_num dt0 (Qlt_le_weak _ _ Hdt0) Ht26). }
Qed.

(* The half-window pair of witnesses (face forms, the 26-tier split) *)
Theorem piLw_halfwin_cos : piLh_seed_halfwin_cos_face.
Proof.
  intros dt Hdt.
  destruct (Qlt_le_dec dt (26#1)%Q) as [Hle | Hgt].
  - destruct (piLw_cos_core dt Hdt (Qlt_le_weak _ _ Hle)) as [K HK].
    exists K. exact HK.
  - destruct (piLw_cos_core (26#1)%Q piLw_q26_pos (Qle_refl (26#1)%Q))
      as [K HK].
    exists K. intros k m Hk Hm.
    apply (Qlt_le_trans _ (26#1)%Q).
    + apply HK; assumption.
    + exact Hgt.
Qed.

Theorem piLw_halfwin_sin : piLh_seed_halfwin_sin_face.
Proof.
  intros dt Hdt.
  destruct (Qlt_le_dec dt (26#1)%Q) as [Hle | Hgt].
  - destruct (piLw_sin_core dt Hdt (Qlt_le_weak _ _ Hle)) as [K HK].
    exists K. exact HK.
  - destruct (piLw_sin_core (26#1)%Q piLw_q26_pos (Qle_refl (26#1)%Q))
      as [K HK].
    exists K. intros k m Hk Hm.
    apply (Qlt_le_trans _ (26#1)%Q).
    + apply HK; assumption.
    + exact Hgt.
Qed.

(* The one-line gate assembly (the assembly form announced at the head of this file; a transparent Definition) *)
Definition piLh_seed_halfwin : piLd3_seed_halfwin :=
  piLh_seed_halfwin_pair piLw_halfwin_cos piLw_halfwin_sin.

Print Assumptions piLh_seed_qlt_share.
Print Assumptions piLh_seed_share.
Print Assumptions piLh_seed_halfwin_pair.
Print Assumptions piLh_port_cos_inv_dist.
Print Assumptions piLh_port_cos_partial_seq_cauchy.
Print Assumptions piLh_seed_t5alpha_supply.
Print Assumptions piLw_halfwin_cos.
Print Assumptions piLw_halfwin_sin.
Print Assumptions piLh_seed_halfwin.
