(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The Set-carried twin of the cosine-zero existence theorem

    Mission.  The [Set]-carried twin of the main existence theorem for
    cosine zeros: the truncation index [N] of the root is lifted from a
    mere existence statement to a [sig] witness in [Set], so that
    downstream files can consume the pointwise root bounds along the
    sequence term by term without crossing from an [exists] statement
    into [Set].  The return face is the ordered pair [xr : Q * nat]
    (first component the root point, second component the truncation
    index); the three-component predicate face (lower interval bound,
    upper interval bound, pointwise root bound) is verbatim
    same-shaped as [approx_root_cos]; the twin zero sequence
    [cos_zero_seq_set] (first component taken directly from the
    witness detail) and a [Set]-level supplier of the pointwise root
    bound accompany it.

    Dependencies.  [PiCompareT] ([QltT]/[QleT']); [PiKernelSlack]
    ([cos_partial]/[q_pow]/[leibsep_cos_partial_lipschitz]);
    [PiVertexPolyDiff]; [PiCosTailScan] (the [vt_*] lemma family);
    [PiCosApproxRoot] (the [vt_*] family); [QCauchyZeroCos]
    ([log_eps]/[log_eps_pos]); stdlib [QArith], [ZArith], [PeanoNat],
    [Setoid], [Morphisms], [Lia].

    References.  [PiCosApproxRoot.v], [approx_root_cos] (this file is
    the [Set]-carried twin restatement); [cos_zero_seq_set] mirrors
    [PiCosZeroSeqProbe.v], [cos_zero_seq] (the twin consumption form
    via direct [proj1_sig]).

    Constructivity.  Statements carried at the [Set] level (a [sig]
    ordered pair); the in-proof predicates are the pure constructive
    stdlib [Qle]/[Qlt]; assumption-free and fully proved, with no
    non-constructive principles.

    Build.  [rocq c -native-compiler no -q -Q . ""
    PiCosApproxRootSet.v]; the first eight bytes of the artifact are
    [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.
Require Import PiCompareT.
Require Import PiKernelSlack.
Require Import PiVertexPolyDiff.
Require Import PiCosTailScan.
Require Import PiCosApproxRoot.
Require Import QCauchyZeroCos.

(* The Set-carried twin of the main theorem: the same construction
   pattern as [approx_root_cos], with the return face a [sig] ordered
   pair of the root point and the truncation index.  Construction:
   the five-component bisection-localization invariant is instantiated
   at the exponent [A], giving the localization interval and the signs
   of the endpoints; the strictly decreasing half-step presses the
   function value at the interval midpoint into the endpoint span, and
   the span shrinks with the interval length through the Lipschitz
   bound; the truncation drift is controlled by the alternating tail
   bound at the same anchor exponent, and the tail term reduces, via
   the step-wise decay, to the half-power Archimedean witness. *)
Lemma approx_root_cos_set : forall eps : Q,
  Qlt 0 eps ->
  { xr : Q * nat | Qlt (3#2) (fst xr) /\ Qlt (fst xr) (5#3) /\
    (forall k : nat, (snd xr <= k)%nat -> Qlt (Qabs (cos_partial k (fst xr))) eps) }.
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
  assert (Hmain : forall k : nat, (A <= k)%nat -> Qlt (Qabs (cos_partial k x)) eps).
  { intros k Hk.
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
    - rewrite <- Hepsadd. apply (Qplus_lt_le_compat _ _ _ _ Htaillt Hspanlip2). }
  exists (x, A). split; [exact Hxlo | split; [exact Hxhi | exact Hmain]].
Qed.

(* The n-th term of the twin zero sequence: the first component of the
   [sig] witness detail of the Set-carried twin, taken directly
   (same-shaped as the [proj1_sig] direct consumption form of
   [cos_zero_seq]). *)
Definition cos_zero_seq_set (n : nat) : Q :=
  fst (proj1_sig (approx_root_cos_set (log_eps n) (log_eps_pos n))).

(* Set-level supply of the pointwise root bound: the second component
   of the twin witness detail is the truncation index, and the first
   component agrees definitionally with [cos_zero_seq_set m]. *)
Lemma cos_root_pt_bound_set : forall m : nat,
  { N2 : nat | forall k : nat, (N2 <= k)%nat ->
    Qlt (Qabs (cos_partial k (cos_zero_seq_set m))) (log_eps m) }.
Proof.
  intros m.
  unfold cos_zero_seq_set.
  destruct (approx_root_cos_set (log_eps m) (log_eps_pos m)) as [[x N] [Hlo [Hhi HN]]].
  exists N. exact HN.
Qed.

(* Interval bounds of the twin sequence: taken directly from the
   predicate face of the witness detail. *)
Lemma cos_zero_lower_set : forall n : nat, Qlt (3#2)%Q (cos_zero_seq_set n).
Proof.
  intros n. unfold cos_zero_seq_set.
  destruct (approx_root_cos_set (log_eps n) (log_eps_pos n)) as [[x N] [Hlo [Hhi HN]]].
  exact Hlo.
Qed.

Lemma cos_zero_upper_set : forall n : nat, Qlt (cos_zero_seq_set n) (5#3)%Q.
Proof.
  intros n. unfold cos_zero_seq_set.
  destruct (approx_root_cos_set (log_eps n) (log_eps_pos n)) as [[x N] [Hlo [Hhi HN]]].
  exact Hhi.
Qed.

Lemma cos_zero_nonneg_set : forall n : nat, Qle 0 (cos_zero_seq_set n).
Proof.
  intros n.
  apply (Qlt_le_weak 0 (cos_zero_seq_set n)).
  apply (Qlt_trans 0 (3#2)%Q).
  - change (Qlt 0 (3#2)%Q). unfold Qlt. simpl. lia.
  - apply cos_zero_lower_set.
Qed.

Lemma cos_zero_le_two_set : forall n : nat, Qle (cos_zero_seq_set n) 2.
Proof.
  intros n.
  apply (Qlt_le_weak (cos_zero_seq_set n) 2).
  apply (Qlt_trans (cos_zero_seq_set n) (5#3)%Q).
  - apply cos_zero_upper_set.
  - change (Qlt (5#3)%Q 2). unfold Qlt. simpl. lia.
Qed.

Lemma cos_zero_abs_le_two_set : forall n : nat, Qle (Qabs (cos_zero_seq_set n)) 2.
Proof.
  intros n.
  apply (proj2 (Qabs_Qle_condition (cos_zero_seq_set n) 2)).
  split.
  - apply (Qle_trans _ 0 _).
    + change (Qle (- 2) 0). unfold Qle. simpl. lia.
    + apply cos_zero_nonneg_set.
  - apply cos_zero_le_two_set.
Qed.

Print Assumptions approx_root_cos_set.
Print Assumptions cos_zero_seq_set.
Print Assumptions cos_root_pt_bound_set.
Print Assumptions cos_zero_abs_le_two_set.
