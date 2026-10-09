(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Assembly of the half-window seed consumption faces

    Mission.  Assembly of the sigma-1 half-window seed consumption
    faces: the assembly theorem supplying the half-window slot
    [piLd3_seed_halfwin] (of [PiKernelSlack]), transcribed
    verbatim; the fixed-point arctan consumption face (the [sig] form
    of [|S_k(lp_odd m) - C_k(lp_odd m)| -> 0], consumable at the
    canonical shared instance [e := 2dt/13]); the cosine zero-sequence
    signature face; and the fixed-point partial-sum order-Cauchy
    signature face.  Once the half-window pair of witnesses (the
    cosine and sine pieces) is available, the main statement closes to
    the assumption-free form by a one-step assembly.

    Dependencies.  Stdlib [QArith] ([QArith]/[Qabs]),
    [Arith.PeanoNat], [Lia]; [PiKernelSlack] ([cos_partial]/
    [sin_partial] and the [QltT] bridges); [PiLeibnizCReal]
    ([lp_odd]); [PiKernelSlack] (the slot type, merged segment);
    [QCauchyZeroCos]; [PiCosZeroSeqConv]; [PiCosZeroSeqProbe];
    [PiCosPartialSeqCauchy].

    References.  [PiKernelSlack] (merged segment, slot at line 13968), [piLd3_seed_halfwin];
    [PiCosZeroSeqConv] (the zero-sequence face); [PiCosPartialSeqCauchy]
    (the fixed-point partial-sum order-Cauchy face, orthogonal to the
    Cauchy property of the zero-localization sequence).

    Constructivity.  All consumption faces are carried by
    [sig]/[sigT] ([K : nat] witnesses); the fixed-point arctan
    consumption site is carried by an explicitly named premise
    ([piLh_seed_t5alpha]); the assumption-free closed-form name
    [piLh_seed_halfwin] is deliberately not occupied in this file:
    one assembly line closes it once the paired witnesses are
    available (see the reserved-gate note at the end of the file);
    positivity in [Q] goes through the manual chain [unfold Qdiv] +
    [Qmult_lt_0_compat] + [Qinv_lt_0_compat] (positivity of [Q]
    division without a nonzero premise), literal positive-constant
    steps go [unfold Qlt] then [simpl] + [lia], and [nat] bookkeeping
    goes [Nat.le_trans]/[Nat.le_max_l] with no solver;
    assumption-free and fully proved, with no non-constructive
    principles (the closing [Print Assumptions] lines all report
    closed).

    Build.  [rocq c -native-compiler no -q -Q . "" PiHalfwinSeed.v];
    the first eight bytes of the artifact are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.
Require Import PiLeibnizCReal.
Require Import QCauchyZeroCos.
Require Import PiCosZeroSeqConv.
Require Import PiCosZeroSeqProbe.
Require Import PiCosPartialSeqCauchy.

(* ============================================================ *)
(* Section 1. Consumption signatures of the cosine zero sequence
   (bodies transcribed verbatim; the type ascription is the whole
   proof) *)
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
(* Section 2. Consumption signatures of the half-power family (six
   statements) *)
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
(* Section 3. Consumption signature of the fixed-point partial-sum
   order-Cauchy statement (the orthogonal complement of the paired
   witness face: for the fixed point [z_m] and tolerance [dt > 0] it
   gives [K] such that every [k >= K] satisfies
   [|P_k(z_m) - P_K(z_m)| < dt]; consumption pattern
   [destruct (cos_partial_seq_cauchy m dt Hdt) as [K HK]].) *)
(* ============================================================ *)

Definition piLh_port_cos_partial_seq_cauchy :
  forall (m : nat) (dt : Q), Qlt 0 dt ->
    {K : nat | forall k : nat, (K <= k)%nat ->
       Qlt (Qabs (cos_partial k (cos_zero_seq m) - cos_partial K (cos_zero_seq m)))
           dt} :=
  cos_partial_seq_cauchy.

(* ============================================================ *)
(* Section 4. The fixed-point arctan consumption face (carried by an
   explicitly named premise) and the [e := 2dt/13] instance *)
(* ============================================================ *)

(* Premise of the consumption face (named-premise position; the only
   fixed-point input of the paired witness face): for every [e > 0]
   there is a [K] such that [|S_k(lp_odd m) - C_k(lp_odd m)| < e]
   whenever [1 <= k], [K <= k], and [K <= m]. *)
Definition piLh_seed_t5alpha :=
  forall e : Q, Qlt 0 e ->
    {K : nat | forall (k m : nat), (1 <= k)%nat -> (K <= k)%nat -> (K <= m)%nat ->
       Qlt (Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m))) e}.

Lemma piLh_seed_qtwo_pos : Qlt 0 (2#1)%Q.
Proof. unfold Qlt. simpl. lia. Qed.

Lemma piLh_seed_qthirteen_pos : Qlt 0 (13#1)%Q.
Proof. unfold Qlt. simpl. lia. Qed.

(* Positivity of the canonical shared instance [e := 2dt/13] (the 2/13
   share of the tolerance [dt]): [2dt/13 = 2dt * (1/13)], and both
   factors are positive. *)
Lemma piLh_seed_qlt_share : forall dt : Q, Qlt 0 dt -> Qlt 0 (Qdiv (2 * dt) 13).
Proof.
  intros dt Hdt. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - rewrite Qmult_comm. change (0 * (2#1)%Q < dt * (2#1)%Q)%Q.
    exact (Qmult_lt_compat_r 0 dt (2#1)%Q piLh_seed_qtwo_pos Hdt).
  - exact (Qinv_lt_0_compat (13#1)%Q piLh_seed_qthirteen_pos).
Qed.

(* Instance consumption form: the fixed-point value of the premise face
   at [e := 2dt/13], the shape directly consumable by the two paired
   witnesses (the half-window cosine and the half-window sine). *)
Definition piLh_seed_share :
  piLh_seed_t5alpha ->
  forall dt : Q, Qlt 0 dt ->
    {K : nat | forall (k m : nat), (1 <= k)%nat -> (K <= k)%nat -> (K <= m)%nat ->
       Qlt (Qabs (sin_partial k (lp_odd m) - cos_partial k (lp_odd m)))
           (Qdiv (2 * dt) 13)} :=
  fun Halpha dt Hdt => Halpha (Qdiv (2 * dt) 13) (piLh_seed_qlt_share dt Hdt).

(* ============================================================ *)
(* Section 5. The half-window pair of witnesses and the slot assembly *)
(* ============================================================ *)

Definition piLh_seed_halfwin_cos_face :=
  forall dt : Q, Qlt 0 dt ->
    {K : nat | forall (k m : nat), (K <= k)%nat -> (K <= m)%nat ->
       Qlt (Qabs (cos_partial k (2 * lp_odd m))) dt}.

Definition piLh_seed_halfwin_sin_face :=
  forall dt : Q, Qlt 0 dt ->
    {K : nat | forall (k m : nat), (K <= k)%nat -> (K <= m)%nat ->
       Qlt (Qabs (sin_partial k (2 * lp_odd m) - (1 # 1)%Q)) dt}.

(* Slot assembly: take the [max] of the [K]s of the two half-window
   witnesses (instantiated at the same [dt]); the two components enter
   the [Set]-level product through the [Qlt]->[QltT] bridge. *)
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
(* Reserved gate (the final name is deliberately left unused in this
   file): one line closes it once the paired witnesses are available.
     Theorem piLh_seed_halfwin : piLd3_seed_halfwin :=
       piLh_seed_halfwin_pair <half-window cos witness>
                              <half-window sin witness>.
   If a witness face takes [piLh_seed_t5alpha] as a premise, it is
   instantiated at the fixed-point arctan face through
   [piLh_seed_share] ([e := 2dt/13]). *)
(* ============================================================ *)

Print Assumptions piLh_seed_qlt_share.
Print Assumptions piLh_seed_share.
Print Assumptions piLh_seed_halfwin_pair.
Print Assumptions piLh_port_cos_inv_dist.
Print Assumptions piLh_port_cos_partial_seq_cauchy.
