(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import Rbase.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import SeqSeries.
From Stdlib Require Import Rtrigo1.
From Stdlib Require Import Ranalysis1.
From Stdlib Require Import PSeries_reg.
From Stdlib Require Import Lia Lra.
From Stdlib Require Import Arith.Factorial.
#[local] Open Scope nat_scope.
#[local] Open Scope R_scope.

Definition E1 (x:R) (N:nat) : R :=
  sum_f_R0 (fun k:nat => / INR (fact k) * x ^ k) N.

Lemma E1_cvg : forall x:R, Un_cv (E1 x) (exp x).
Proof.
  intro; unfold exp; unfold projT1.
  case (exist_exp x); intro.
  unfold exp_in, Un_cv; unfold infinite_sum, E1; trivial.
Qed.

Definition Reste_E (x y:R) (N:nat) : R :=
  sum_f_R0
  (fun k:nat =>
    sum_f_R0
    (fun l:nat =>
      / INR (fact (S (l + k))) * x ^ S (l + k) *
      (/ INR (fact (N - l)) * y ^ (N - l))) (
        pred (N - k))) (pred N).

Lemma exp_form :
  forall (x y:R) (n:nat),
    (0 < n)%nat -> E1 x n * E1 y n - Reste_E x y n = E1 (x + y) n.
Proof.
  intros; unfold E1.
  rewrite cauchy_finite.
  - unfold Reste_E; unfold Rminus; rewrite Rplus_assoc;
      rewrite Rplus_opp_r; rewrite Rplus_0_r; apply sum_eq;
      intros.
    rewrite binomial.
    rewrite scal_sum; apply sum_eq; intros.
    unfold C; unfold Rdiv; repeat rewrite Rmult_assoc;
      rewrite (Rmult_comm (INR (fact i))); repeat rewrite Rmult_assoc;
      rewrite Rinv_l.
    + rewrite Rmult_1_r; rewrite Rinv_mult.
      ring.
    + apply INR_fact_neq_0.
  - apply H.
Qed.

Definition maj_Reste_E (x y:R) (N:nat) : R :=
  4 *
  (Rmax 1 (Rmax (Rabs x) (Rabs y)) ^ (2 * N) /
    Rsqr (INR (fact (Nat.div2 (pred N))))).

(**********)
Lemma div2_double : forall N:nat, Nat.div2 (2 * N) = N.
Proof. exact Nat.div2_double. Qed.

Lemma div2_S_double : forall N:nat, Nat.div2 (S (2 * N)) = N.
Proof.
  intro; induction  N as [| N HrecN].
  - reflexivity.
  - replace (2 * S N)%nat with (S (S (2 * N))).
    + simpl; simpl in HrecN; rewrite HrecN; reflexivity.
    + ring.
Qed.

Lemma div2_not_R0 : forall N:nat, (1 < N)%nat -> (0 < Nat.div2 N)%nat.
Proof.
  intros; induction N as [| N HrecN].
  - elim (Nat.nlt_0_r _ H).
  - cut ((1 < N)%nat \/ N = 1%nat).
    { intro; elim H0; intro.
      - destruct N; cbn; [ auto |  apply Nat.lt_0_succ ].
      - subst N; simpl; apply Nat.lt_0_succ. }
    inversion H.
    + right; reflexivity.
    + left; apply Nat.lt_le_trans with 2%nat; [ apply Nat.lt_succ_diag_r | assumption ].
Qed.

Lemma Reste_E_maj :
  forall (x y:R) (N:nat),
    (0 < N)%nat -> Rabs (Reste_E x y N) <= maj_Reste_E x y N.
Proof.
  intros; set (M := Rmax 1 (Rmax (Rabs x) (Rabs y))).
  assert (HM1 : 1 <= M) by apply RmaxLess1.
  assert (HMx : Rabs x <= M) by (eapply Rle_trans;[apply RmaxLess1|apply RmaxLess2]).
  assert (HMy : Rabs y <= M) by (eapply Rle_trans;[apply RmaxLess2|apply RmaxLess2]).
  pose proof (Rabs_pos x) as HPosAbsx.
  pose proof (Rabs_pos y) as HPosAbsy.
  apply Rle_trans with
    (M ^ (2 * N) *
      sum_f_R0
      (fun k:nat =>
        sum_f_R0 (fun l:nat => / Rsqr (INR (fact (Nat.div2 (S N)))))
                 (pred (N - k))) (pred N)).
  - unfold Reste_E.
    apply Rle_trans with
      (sum_f_R0
         (fun k:nat =>
            Rabs
              (sum_f_R0
                 (fun l:nat =>
                    / INR (fact (S (l + k))) * x ^ S (l + k) *
                                                     (/ INR (fact (N - l)) * y ^ (N - l))) (
                   pred (N - k)))) (pred N)).
    { apply
      (Rsum_abs
         (fun k:nat =>
            sum_f_R0
              (fun l:nat =>
                 / INR (fact (S (l + k))) * x ^ S (l + k) *
                                                  (/ INR (fact (N - l)) * y ^ (N - l))) (
                pred (N - k))) (pred N)). }
    apply Rle_trans with
      (sum_f_R0
         (fun k:nat =>
            sum_f_R0
              (fun l:nat =>
                 Rabs
                   (/ INR (fact (S (l + k))) * x ^ S (l + k) *
                                                     (/ INR (fact (N - l)) * y ^ (N - l)))) (
                pred (N - k))) (pred N)).
    { apply sum_Rle; intros.
      apply
      (Rsum_abs
         (fun l:nat =>
            / INR (fact (S (l + n))) * x ^ S (l + n) *
                                             (/ INR (fact (N - l)) * y ^ (N - l)))). }
    apply Rle_trans with
      (sum_f_R0
         (fun k:nat =>
            sum_f_R0
              (fun l:nat =>
                 M ^ (2 * N) * / INR (fact (S l)) * / INR (fact (N - l)))
              (pred (N - k))) (pred N)).
    + apply sum_Rle; intros.
      apply sum_Rle; intros.
      repeat rewrite Rabs_mult.
      do 2 rewrite <- RPow_abs.
      rewrite (Rabs_right (/ INR (fact (S (n0 + n))))).
      2:{ apply Rle_ge; left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
      rewrite (Rabs_right (/ INR (fact (N - n0)))).
      2:{ apply Rle_ge; left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
      replace
        (/ INR (fact (S (n0 + n))) * Rabs x ^ S (n0 + n) *
                                                (/ INR (fact (N - n0)) * Rabs y ^ (N - n0))) with
        (/ INR (fact (N - n0)) * / INR (fact (S (n0 + n))) * Rabs x ^ S (n0 + n) *
                                                                        Rabs y ^ (N - n0))
      by ring.
      rewrite <- (Rmult_comm (/ INR (fact (N - n0)))).
      repeat rewrite Rmult_assoc.
      apply Rmult_le_compat_l.
      { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
      apply Rle_trans with
        (/ INR (fact (S n0)) * Rabs x ^ S (n0 + n) * Rabs y ^ (N - n0)).
      { rewrite (Rmult_comm (/ INR (fact (S (n0 + n)))));
        rewrite (Rmult_comm (/ INR (fact (S n0)))); repeat rewrite Rmult_assoc;
        apply Rmult_le_compat_l.
        { apply pow_le; apply Rabs_pos. }
        rewrite (Rmult_comm (/ INR (fact (S n0)))); apply Rmult_le_compat_l.
        { apply pow_le; apply Rabs_pos. }
        apply Rinv_le_contravar.
        { apply INR_fact_lt_0. }
        apply le_INR; apply fact_le; lia. }
      rewrite (Rmult_comm (M ^ (2 * N))); rewrite Rmult_assoc;
        apply Rmult_le_compat_l.
      { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
      apply Rle_trans with (M ^ S (n0 + n) * Rabs y ^ (N - n0)).
      { do 2 rewrite <- (Rmult_comm (Rabs y ^ (N - n0))).
        apply Rmult_le_compat_l.
        { apply pow_le; apply Rabs_pos. }
        apply pow_incr; split;lra. }
      apply Rle_trans with (M ^ S (n0 + n) * M ^ (N - n0)).
      { apply Rmult_le_compat_l.
        { apply pow_le; lra. }
        apply pow_incr; split; lra. }
      rewrite <- pow_add; replace (S (n0 + n) + (N - n0))%nat with (N + S n)%nat by lia.
      apply Rle_pow.
      { assumption. }
      lia.
    + rewrite scal_sum.
      apply sum_Rle; intros.
      rewrite <- Rmult_comm.
      rewrite scal_sum.
      apply sum_Rle; intros.
      rewrite (Rmult_comm (/ Rsqr (INR (fact (Nat.div2 (S N)))))).
      rewrite Rmult_assoc; apply Rmult_le_compat_l.
      { apply pow_le. lra. }
      assert (H2 := even_odd_cor N).
      elim H2; intros N0 H3.
      elim H3; intro.
      * apply Rle_trans with (/ INR (fact n0) * / INR (fact (N - n0))).
        { do 2 rewrite <- (Rmult_comm (/ INR (fact (N - n0)))).
          apply Rmult_le_compat_l.
          { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
          apply Rinv_le_contravar.
          { apply INR_fact_lt_0. }
          apply le_INR.
          apply fact_le.
          apply Nat.le_succ_diag_r. }
        replace (/ INR (fact n0) * / INR (fact (N - n0))) with
          (C N n0 / INR (fact N)).
        2:{ unfold C, Rdiv.
            rewrite (Rmult_comm (INR (fact N))).
            repeat rewrite Rmult_assoc.
            rewrite Rinv_r.
            2:{ apply INR_fact_neq_0. }
            rewrite Rinv_mult.
            rewrite Rmult_1_r; ring. }
        pattern N at 1; rewrite H4.
        apply Rle_trans with (C N N0 / INR (fact N)).
        { unfold Rdiv; do 2 rewrite <- (Rmult_comm (/ INR (fact N))).
          apply Rmult_le_compat_l.
          { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
          rewrite H4.
          apply C_maj.
          lia. }
        replace (C N N0 / INR (fact N)) with (/ Rsqr (INR (fact N0))).
        { rewrite H4; rewrite div2_S_double; right; reflexivity. }
        unfold Rsqr, C, Rdiv.
        repeat rewrite Rinv_mult.
        rewrite (Rmult_comm (INR (fact N))).
        repeat rewrite Rmult_assoc.
        rewrite Rinv_r.
        2:apply INR_fact_neq_0.
        replace (N - N0)%nat with N0 by lia.
        ring.
      * replace (/ INR (fact (S n0)) * / INR (fact (N - n0))) with
          (C (S N) (S n0) / INR (fact (S N))).
        2:{ unfold C, Rdiv.
            rewrite (Rmult_comm (INR (fact (S N)))).
            rewrite Rmult_assoc; rewrite Rinv_r.
            2:{ apply INR_fact_neq_0. }
            rewrite Rmult_1_r; rewrite Rinv_mult.
            reflexivity. }
        apply Rle_trans with (C (S N) (S N0) / INR (fact (S N))).
        2:{ assert (S N = (2 * S N0)%nat) by lia.
            replace (C (S N) (S N0) / INR (fact (S N))) with (/ Rsqr (INR (fact (S N0)))).
            { rewrite H5; rewrite div2_double.
              right; reflexivity. }
            unfold Rsqr, C, Rdiv.
            repeat rewrite Rinv_mult.
            replace (S N - S N0)%nat with (S N0) by lia.
            rewrite (Rmult_comm (INR (fact (S N)))).
            repeat rewrite Rmult_assoc.
            rewrite Rinv_r.
            2:apply INR_fact_neq_0.
            ring. }
        unfold Rdiv; do 2 rewrite <- (Rmult_comm (/ INR (fact (S N)))).
        apply Rmult_le_compat_l.
        { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
        assert (S N = (2 * S N0)%nat) by (rewrite H4; ring).
        rewrite H5; apply C_maj.
        lia.
  - unfold maj_Reste_E. fold M.
    unfold Rdiv; rewrite (Rmult_comm 4).
    rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    { apply pow_le. lra. }
    apply Rle_trans with
      (sum_f_R0 (fun k:nat => INR (N - k) * / Rsqr (INR (fact (Nat.div2 (S N)))))
                (pred N)).
    { apply sum_Rle; intros.
      rewrite sum_cte.
      replace (S (pred (N - n))) with (N - n)%nat by lia.
      right; apply Rmult_comm. }
    apply Rle_trans with
      (sum_f_R0 (fun k:nat => INR N * / Rsqr (INR (fact (Nat.div2 (S N))))) (pred N)).
    { apply sum_Rle; intros.
      do 2 rewrite <- (Rmult_comm (/ Rsqr (INR (fact (Nat.div2 (S N)))))).
      apply Rmult_le_compat_l.
      { left; apply Rinv_0_lt_compat; apply Rsqr_pos_lt.
        apply INR_fact_neq_0. }
      apply le_INR.
      lia. }
    rewrite sum_cte; replace (S (pred N)) with N by lia.
    assert (Nat.div2 (S N) = S (Nat.div2 (pred N))). {
      assert (H0 := even_odd_cor N).
      elim H0; intros N0 H1.
      elim H1; intro.
      - assert (0 < N0)%nat by lia.
        rewrite H2.
        rewrite div2_S_double.
        replace (2 * N0)%nat with (S (S (2 * pred N0))) by lia.
        replace (pred (S (S (2 * pred N0)))) with (S (2 * pred N0)) by lia.
        rewrite div2_S_double.
        lia.
      - rewrite H2.
        change (pred (S (2 * N0))) with (2 * N0)%nat.
        replace (S (S (2 * N0))) with (2 * S N0)%nat by ring.
        do 2 rewrite div2_double.
        reflexivity.
    }
    rewrite H0.
    rewrite fact_simpl; rewrite Nat.mul_comm; rewrite mult_INR; rewrite Rsqr_mult.
    rewrite Rinv_mult.
    rewrite (Rmult_comm (INR N)); repeat rewrite Rmult_assoc;
      apply Rmult_le_compat_l.
    { left; apply Rinv_0_lt_compat; apply Rsqr_pos_lt; apply INR_fact_neq_0. }
    rewrite <- H0.
    assert (INR N <= INR (2 * Nat.div2 (S N))). {
      assert (H1 := even_odd_cor N).
      elim H1; intros N0 H2.
      elim H2; intro.
      - pattern N at 2; rewrite H3.
        rewrite div2_S_double.
        rewrite H3. apply Rle_refl.
      - pattern N at 2; rewrite H3.
        replace (S (S (2 * N0))) with (2 * S N0)%nat by lia.
        rewrite div2_double.
        apply le_INR. lia.
    }
    apply Rmult_le_reg_l with (Rsqr (INR (Nat.div2 (S N)))).
    { apply Rsqr_pos_lt.
      apply not_O_INR; red; intro.
      PreOmega.zify; PreOmega.Z.to_euclidean_division_equations; lia. }
    repeat rewrite <- Rmult_assoc.
    rewrite Rinv_r.
    2:{ unfold Rsqr; apply prod_neq_R0; apply not_O_INR;
      PreOmega.zify; PreOmega.Z.to_euclidean_division_equations; lia. }
    rewrite Rmult_1_l.
    change 4 with (Rsqr 2).
    rewrite <- Rsqr_mult.
    apply Rsqr_incr_1.
    { change 2 with (INR 2).
      rewrite Rmult_comm, <- mult_INR; apply H1. }
    { left; apply lt_INR_0; apply H. }
    change 2 with (INR 2).
    rewrite <- mult_INR.
    apply pos_INR.
Qed.

Lemma maj_Reste_cv_R0 : forall x y:R, Un_cv (maj_Reste_E x y) 0.
Proof.
  intros; assert (H := Majxy_cv_R0 x y).
  unfold Un_cv in H; unfold Un_cv; intros.
  cut (0 < eps / 4);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; prove_sup0 ] ].
  elim (H _ H1); intros N0 H2.
  exists (max (2 * S N0) 2); intros.
  unfold Rdist in H2; unfold Rdist; rewrite Rminus_0_r;
    unfold Majxy in H2; unfold maj_Reste_E.
  set (M := Rmax 1 (Rmax (Rabs x) (Rabs y))) in *.
  assert (HM1 : 1 <= M) by apply RmaxLess1.
  assert (HMx : Rabs x <= M) by (eapply Rle_trans;[apply RmaxLess1|apply RmaxLess2]).
  assert (HMy : Rabs y <= M) by (eapply Rle_trans;[apply RmaxLess2|apply RmaxLess2]).
  pose proof (Rabs_pos x) as HPosAbsx.
  pose proof (Rabs_pos y) as HPosAbsy.
  rewrite Rabs_right.
  2:{ apply Rle_ge.
      unfold Rdiv; apply Rmult_le_pos.
      { left; prove_sup0. }
      apply Rmult_le_pos.
      { apply pow_le. lra. }
      left; apply Rinv_0_lt_compat; apply Rsqr_pos_lt; apply INR_fact_neq_0. }
  apply Rle_lt_trans with
    (4 *
      (M ^ (4 * S (Nat.div2 (pred n))) /
        INR (fact (Nat.div2 (pred n))))).
  - apply Rmult_le_compat_l.
    { left; prove_sup0. }
    unfold Rdiv, Rsqr; rewrite Rinv_mult.
    rewrite (Rmult_comm (M ^ (2 * n)));
      rewrite
        (Rmult_comm (M ^ (4 * S (Nat.div2 (pred n)))))
    ; rewrite Rmult_assoc; apply Rmult_le_compat_l.
    { left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
    apply Rle_trans with (M ^ (2 * n)).
    { rewrite Rmult_comm;
        pattern (M ^ (2 * n)) at 2;
        rewrite <- Rmult_1_r; apply Rmult_le_compat_l.
      { apply pow_le; lra. }
      apply Rmult_le_reg_l with (INR (fact (Nat.div2 (pred n)))).
      { apply INR_fact_lt_0. }
      rewrite Rmult_1_r; rewrite Rinv_r.
      { apply (le_INR 1).
        apply Nat.le_succ_l.
        apply INR_lt.
        apply INR_fact_lt_0. }
      apply INR_fact_neq_0. }
    apply Rle_pow.
    { apply RmaxLess1. }
    assert (H4 := even_odd_cor n).
    elim H4; intros N1 H5.
    elim H5; intro.
    { assert (0 < N1)%nat by lia.
      rewrite H6.
      replace (pred (2 * N1)) with (S (2 * pred N1)) by lia.
      rewrite div2_S_double.
      lia. }
    rewrite H6.
    replace (pred (S (2 * N1))) with (2 * N1)%nat by lia.
    rewrite div2_double.
    lia.
  - apply Rmult_lt_reg_l with (/ 4).
    { apply Rinv_0_lt_compat; prove_sup0. }
    rewrite <- Rmult_assoc; rewrite Rinv_l.
    2:discrR.
    rewrite Rmult_1_l; rewrite Rmult_comm.
    replace
      (M ^ (4 * S (Nat.div2 (pred n))) /
                                       INR (fact (Nat.div2 (pred n)))) with
      (Rabs
         (M ^ (4 * S (Nat.div2 (pred n))) /
                                          INR (fact (Nat.div2 (pred n))) - 0)).
    2:{ rewrite Rminus_0_r; apply Rabs_right.
        apply Rle_ge.
        unfold Rdiv; apply Rmult_le_pos.
        { apply pow_le. lra. }
        left; apply Rinv_0_lt_compat; apply INR_fact_lt_0. }
    apply H2; unfold ge.
    assert (2 * S N0 <= n)%nat by lia.
    apply le_S_n.
    apply INR_le; apply Rmult_le_reg_l with (INR 2).
    { simpl; prove_sup0. }
    do 2 rewrite <- mult_INR; apply le_INR.
    apply Nat.le_trans with n.
    { apply H4. }
    assert (H5 := even_odd_cor n).
    elim H5; intros N1 H6.
    elim H6; intro.
    { assert (0 < N1)%nat by lia.
      rewrite H7.
      apply Nat.mul_le_mono_nonneg_l.
      { apply Nat.le_0_l. }
      replace (pred (2 * N1)) with (S (2 * pred N1)) by lia.
      rewrite div2_S_double.
      lia. }
    rewrite H7.
    change (pred (S (2 * N1))) with (2 * N1)%nat.
    rewrite div2_double.
    lia.
Qed.

(**********)
Lemma Reste_E_cv : forall x y:R, Un_cv (Reste_E x y) 0.
Proof.
  intros; assert (H := maj_Reste_cv_R0 x y).
  unfold Un_cv in H; unfold Un_cv; intros; elim (H _ H0); intros.
  exists (max x0 1); intros.
  unfold Rdist; rewrite Rminus_0_r.
  apply Rle_lt_trans with (maj_Reste_E x y n).
  - apply Reste_E_maj.
    apply Nat.lt_le_trans with 1%nat.
    + apply Nat.lt_0_succ.
    + apply Nat.le_trans with (max x0 1).
      * apply Nat.le_max_r.
      * apply H2.
  - replace (maj_Reste_E x y n) with (Rdist (maj_Reste_E x y n) 0).
    + apply H1.
      unfold ge; apply Nat.le_trans with (max x0 1).
      * apply Nat.le_max_l.
      * apply H2.
    + unfold Rdist; rewrite Rminus_0_r; apply Rabs_right.
      apply Rle_ge; apply Rle_trans with (Rabs (Reste_E x y n)).
      * apply Rabs_pos.
      * apply Reste_E_maj.
        apply Nat.lt_le_trans with 1%nat.
        -- apply Nat.lt_0_succ.
        -- apply Nat.le_trans with (max x0 1).
           ++ apply Nat.le_max_r.
           ++ apply H2.
Qed.

(**********)
Lemma exp_plus : forall x y:R, exp (x + y) = exp x * exp y.
Proof.
  intros; assert (H0 := E1_cvg x).
  assert (H := E1_cvg y).
  assert (H1 := E1_cvg (x + y)).
  eapply UL_sequence.
  - apply H1.
  - assert (H2 := CV_mult _ _ _ _ H0 H).
    assert (H3 := CV_minus _ _ _ _ H2 (Reste_E_cv x y)).
    unfold Un_cv; unfold Un_cv in H3; intros.
    elim (H3 _ H4); intros.
    exists (S x0); intros.
    rewrite <- (exp_form x y n).
    + rewrite Rminus_0_r in H5.
      apply H5.
      unfold ge; apply Nat.le_trans with (S x0).
      * apply Nat.le_succ_diag_r.
      * apply H6.
    + apply Nat.lt_le_trans with (S x0).
      * apply Nat.lt_0_succ.
      * apply H6.
Qed.

(**********)
Lemma exp_pos_pos : forall x:R, 0 < x -> 0 < exp x.
Proof.
  intros; set (An := fun N:nat => / INR (fact N) * x ^ N).
  cut (Un_cv (fun n:nat => sum_f_R0 An n) (exp x)).
  - intro; apply Rlt_le_trans with (sum_f_R0 An 0).
    + unfold An; simpl; rewrite Rinv_1; rewrite Rmult_1_r;
        apply Rlt_0_1.
    + apply sum_incr.
      * assumption.
      * intro; unfold An; left; apply Rmult_lt_0_compat.
        -- apply Rinv_0_lt_compat; apply INR_fact_lt_0.
        -- apply (pow_lt _ n H).
  - unfold exp; unfold projT1; case (exist_exp x); intro.
    unfold exp_in; unfold infinite_sum, Un_cv; trivial.
Qed.

(**********)
Lemma exp_pos : forall x:R, 0 < exp x.
Proof.
  intro; destruct (total_order_T 0 x) as [[Hlt|<-]|Hgt].
  - apply (exp_pos_pos _ Hlt).
  - rewrite exp_0; apply Rlt_0_1.
  - replace (exp x) with (1 / exp (- x)).
    + unfold Rdiv; apply Rmult_lt_0_compat.
      * apply Rlt_0_1.
      * apply Rinv_0_lt_compat; apply exp_pos_pos.
        apply (Ropp_0_gt_lt_contravar _ Hgt).
    + cut (exp (- x) <> 0).
      * intro; unfold Rdiv; apply Rmult_eq_reg_l with (exp (- x)).
        -- rewrite Rmult_1_l; rewrite Rinv_r.
           ++ rewrite <- exp_plus.
              rewrite Rplus_opp_l; rewrite exp_0; reflexivity.
           ++ apply H.
        -- apply H.
      * assert (H := exp_plus x (- x)).
        rewrite Rplus_opp_r in H; rewrite exp_0 in H.
        red; intro; rewrite H0 in H.
        rewrite Rmult_0_r in H.
        elim R1_neq_R0; assumption.
Qed.

(* ((exp h)-1)/h -> 0 quand h->0 *)
Lemma derivable_pt_lim_exp_0 : derivable_pt_lim exp 0 1.
Proof.
  unfold derivable_pt_lim; intros.
  set (fn := fun (N:nat) (x:R) => x ^ N / INR (fact (S N))).
  cut (CVN_R fn).
  - intro; assert (cv:forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l }) by apply (CVN_R_CVS _ X).
    assert (forall n:nat, continuity (fn n)). {
      intro; unfold fn.
      replace (fun x:R => x ^ n / INR (fact (S n))) with
        (pow_fct n / fct_cte (INR (fact (S n))))%F; [ idtac | reflexivity ].
      apply continuity_div.
      - apply derivable_continuous; apply (derivable_pow n).
      - apply derivable_continuous; apply derivable_const.
      - intro; unfold fct_cte; apply INR_fact_neq_0.
    }
    assert (continuity (SFL fn cv)) by (apply SFL_continuity; assumption).
    unfold continuity in H1.
    assert (H2 := H1 0).
    unfold continuity_pt in H2; unfold continue_in in H2; unfold limit1_in in H2;
      unfold limit_in in H2; simpl in H2; unfold Rdist in H2.
    elim (H2 _ H); intros alp H3.
    elim H3; intros.
    exists (mkposreal _ H4); intros.
    rewrite Rplus_0_l; rewrite exp_0.
    replace ((exp h - 1) / h) with (SFL fn cv h).
    + replace 1 with (SFL fn cv 0).
      { apply H5.
        split.
        - unfold D_x, no_cond; split.
          + trivial.
          + apply (not_eq_sym H6).
        - rewrite Rminus_0_r; apply H7. }
      unfold SFL.
      case (cv 0) as (x,Hu).
      eapply UL_sequence.
      { apply Hu. }
      unfold Un_cv, SP in |- *.
      intros; exists 1%nat; intros.
      unfold Rdist; rewrite decomp_sum.
      2:lia.
      rewrite Rplus_comm.
      replace (fn 0%nat 0) with 1.
      2:{ unfold fn; simpl.
          unfold Rdiv; rewrite Rinv_1; rewrite Rmult_1_r; reflexivity. }
      unfold Rminus; rewrite Rplus_assoc; rewrite Rplus_opp_r;
        rewrite Rplus_0_r.
      replace (sum_f_R0 (fun i:nat => fn (S i) 0) (pred n)) with 0.
      { rewrite Rabs_R0; apply H8. }
      symmetry ; apply sum_eq_R0; intros.
      unfold fn.
      simpl.
      unfold Rdiv; do 2 rewrite Rmult_0_l; reflexivity.
    + unfold SFL, exp.
      case (cv h) as (x0,Hu); case (exist_exp h) as (x,Hexp); simpl.
      eapply UL_sequence.
      { apply Hu. }
      unfold Un_cv; intros.
      unfold exp_in, infinite_sum in Hexp.
      assert (0 < eps0 * Rabs h). {
        apply Rmult_lt_0_compat.
        - apply H8.
        - apply Rabs_pos_lt; assumption.
      }
      elim (Hexp _ H9); intros N0 H10.
      exists N0; intros.
      unfold Rdist.
      apply Rmult_lt_reg_l with (Rabs h).
      { apply Rabs_pos_lt; assumption. }
      rewrite <- Rabs_mult.
      rewrite Rmult_minus_distr_l.
      replace (h * ((x - 1) / h)) with (x - 1).
      2:{ field. assumption. }
      unfold Rdist in H10.
      replace (h * SP fn n h - (x - 1)) with
        (sum_f_R0 (fun i:nat => / INR (fact i) * h ^ i) (S n) - x).
      { rewrite (Rmult_comm (Rabs h)).
        apply H10.
        unfold ge.
        apply Nat.le_trans with (S N0).
        - apply Nat.le_succ_diag_r.
        - apply -> Nat.succ_le_mono; apply H11. }
      rewrite decomp_sum.
      2:apply Nat.lt_0_succ.
      replace (/ INR (fact 0) * h ^ 0) with 1.
      2:simpl; rewrite Rinv_1; rewrite Rmult_1_r; reflexivity.
      unfold Rminus.
      rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      rewrite <- (Rplus_comm (- x)).
      rewrite <- (Rplus_comm (- x + 1)).
      rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l.
      replace (pred (S n)) with n; [ idtac | reflexivity ].
      unfold SP.
      rewrite scal_sum.
      apply sum_eq; intros.
      unfold fn.
      replace (h ^ S i) with (h * h ^ i) by (simpl;ring).
      unfold Rdiv; ring.
  - assert (H0 := Alembert_exp).
    unfold CVN_R.
    intro; unfold CVN_r.
    exists (fun N:nat => r ^ N / INR (fact (S N))).
    cut
      { l:R |
        Un_cv
          (fun n:nat =>
             sum_f_R0 (fun k:nat => Rabs (r ^ k / INR (fact (S k)))) n) l }.
    { intros (x,p).
      exists x; intros.
      split.
      { assumption. }
      unfold Boule; intros.
      rewrite Rminus_0_r in H1.
      unfold fn.
      unfold Rdiv; rewrite Rabs_mult.
      assert (0 < INR (fact (S n))).
      { apply INR_fact_lt_0. }
      rewrite (Rabs_right (/ INR (fact (S n)))).
      2:{ apply Rle_ge; left; apply Rinv_0_lt_compat; apply H2. }
      do 2 rewrite <- (Rmult_comm (/ INR (fact (S n)))).
      apply Rmult_le_compat_l.
      { left; apply Rinv_0_lt_compat; apply H2. }
      rewrite <- RPow_abs.
      apply pow_maj_Rabs.
      rewrite Rabs_Rabsolu; left; apply H1. }
    assert ((r:R) <> 0). {
      assert (H1 := cond_pos r); red; intro; rewrite H2 in H1;
        elim (Rlt_irrefl _ H1).
    }
    apply Alembert_C2.
    { intro; apply Rabs_no_R0.
      unfold Rdiv; apply prod_neq_R0.
      { apply pow_nonzero; assumption. }
      apply Rinv_neq_0_compat; apply INR_fact_neq_0. }
    unfold Un_cv in H0.
    unfold Un_cv; intros.
    cut (0 < eps0 / r);
      [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ assumption | apply Rinv_0_lt_compat; apply (cond_pos r) ] ].
    elim (H0 _ H3); intros N0 H4.
    exists N0; intros.
    assert (hyp_sn:(S n >= N0)%nat) by lia.
    assert (H6 := H4 _ hyp_sn).
    unfold Rdist in H6; rewrite Rminus_0_r in H6.
    rewrite Rabs_Rabsolu in H6.
    unfold Rdist; rewrite Rminus_0_r.
    rewrite Rabs_Rabsolu.
    replace
      (Rabs (r ^ S n / INR (fact (S (S n)))) / Rabs (r ^ n / INR (fact (S n))))
      with (r * / INR (fact (S (S n))) * / / INR (fact (S n))).
    { rewrite Rmult_assoc; rewrite Rabs_mult.
      rewrite (Rabs_right r).
      2:{ apply Rle_ge; left; apply (cond_pos r). }
      apply Rmult_lt_reg_l with (/ r).
      { apply Rinv_0_lt_compat; apply (cond_pos r). }
      rewrite <- Rmult_assoc; rewrite Rinv_l.
      2:assumption.
      rewrite Rmult_1_l; rewrite <- (Rmult_comm eps0).
      apply H6. }
    unfold Rdiv.
    repeat rewrite Rabs_mult.
    repeat rewrite Rabs_inv.
    rewrite Rinv_mult.
    repeat rewrite Rabs_right.
    2,4:match goal with |- context[fact ?x] => pose proof (INR_fact_lt_0 x) end;lra.
    2,3:apply Rle_ge; left; apply pow_lt; apply (cond_pos r).
    rewrite Rinv_inv.
    rewrite (Rmult_comm r).
    rewrite (Rmult_comm (r ^ S n)).
    repeat rewrite Rmult_assoc.
    apply Rmult_eq_compat_l.
    rewrite (Rmult_comm r).
    rewrite <- Rmult_assoc; rewrite <- (Rmult_comm (INR (fact (S n)))).
    apply Rmult_eq_compat_l.
    simpl.
    rewrite Rmult_assoc; rewrite Rinv_r.
    2:{ apply pow_nonzero; assumption. }
    ring.
Qed.

(**********)
Lemma derivable_pt_lim_exp : forall x:R, derivable_pt_lim exp x (exp x).
Proof.
  intro; assert (H0 := derivable_pt_lim_exp_0).
  unfold derivable_pt_lim in H0; unfold derivable_pt_lim; intros.
  cut (0 < eps / exp x);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ apply H | apply Rinv_0_lt_compat; apply exp_pos ] ].
  elim (H0 _ H1); intros del H2.
  exists del; intros.
  assert (H5 := H2 _ H3 H4).
  rewrite Rplus_0_l in H5; rewrite exp_0 in H5.
  replace ((exp (x + h) - exp x) / h - exp x) with
  (exp x * ((exp h - 1) / h - 1)).
  - rewrite Rabs_mult; rewrite (Rabs_right (exp x)).
    + apply Rmult_lt_reg_l with (/ exp x).
      * apply Rinv_0_lt_compat; apply exp_pos.
      * rewrite <- Rmult_assoc; rewrite Rinv_l.
        -- rewrite Rmult_1_l; rewrite <- (Rmult_comm eps).
           apply H5.
        -- assert (H6 := exp_pos x); red; intro; rewrite H7 in H6;
             elim (Rlt_irrefl _ H6).
    + apply Rle_ge; left; apply exp_pos.
  - rewrite Rmult_minus_distr_l.
    rewrite Rmult_1_r; unfold Rdiv; rewrite <- Rmult_assoc;
      rewrite Rmult_minus_distr_l.
    rewrite Rmult_1_r; rewrite exp_plus; reflexivity.
Qed.
