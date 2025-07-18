(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import Compare.
From Stdlib Require Import Rbase.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import Rseries.
From Stdlib Require Import PartSum.
From Stdlib Require Import Binomial.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Peano_dec.
#[local] Open Scope R_scope.

(** TT Ak; 0<=k<=N *)
Fixpoint prod_f_R0 (f:nat -> R) (N:nat) : R :=
  match N with
    | O => f O
    | S p => prod_f_R0 f p * f (S p)
  end.

Notation prod_f_SO := (fun An N => prod_f_R0 (fun n => An (S n)) N).

(**********)
Lemma prod_SO_split :
  forall (An:nat -> R) (n k:nat),
    (k < n)%nat ->
    prod_f_R0 An n =
    prod_f_R0 An k * prod_f_R0 (fun l:nat => An (k +1+l)%nat) (n - k -1).
Proof.
  intros; induction  n as [| n Hrecn].
  - absurd (k < 0)%nat; lia.
  - cut (k = n \/ (k < n)%nat);[intro; elim H0; intro|lia].
    + replace (S n - k - 1)%nat with O; [rewrite H1; simpl|lia].
      replace (n+1+0)%nat with (S n); ring.
    + replace (S n - k-1)%nat with (S (n - k-1));[idtac|lia].
      simpl; replace (k + S (n - k))%nat with (S n).
      * replace (k + 1 + S (n - k - 1))%nat with (S n).
        -- rewrite Hrecn; [ ring | assumption ].
        -- lia.
      * lia.
Qed.

(**********)
Lemma prod_SO_pos :
  forall (An:nat -> R) (N:nat),
    (forall n:nat, (n <= N)%nat -> 0 <= An n) -> 0 <= prod_f_R0 An N.
Proof.
  intros; induction  N as [| N HrecN].
  - simpl; apply H; trivial.
  - simpl; apply Rmult_le_pos.
    + apply HrecN; intros; apply H; apply Nat.le_trans with N;
        [ assumption | apply Nat.le_succ_diag_r ].
    + apply H; apply Nat.le_refl.
Qed.

(**********)
Lemma prod_SO_Rle :
  forall (An Bn:nat -> R) (N:nat),
    (forall n:nat, (n <= N)%nat -> 0 <= An n <= Bn n) ->
    prod_f_R0 An N <= prod_f_R0 Bn N.
Proof.
  intros; induction  N as [| N HrecN].
  - elim  H with O; trivial.
  - simpl; apply Rle_trans with (prod_f_R0 An N * Bn (S N)).
    + apply Rmult_le_compat_l.
      * apply prod_SO_pos; intros; elim (H n (Nat.le_trans _ _ _ H0 (Nat.le_succ_diag_r N))); intros;
          assumption.
      * elim (H (S N) (le_n (S N))); intros; assumption.
    + do 2 rewrite <- (Rmult_comm (Bn (S N))); apply Rmult_le_compat_l.
      * elim (H (S N) (le_n (S N))); intros.
        apply Rle_trans with (An (S N)); assumption.
      * apply HrecN; intros; elim (H n (Nat.le_trans _ _ _ H0 (Nat.le_succ_diag_r N))); intros;
          split; assumption.
Qed.

(** Application to factorial *)
Lemma fact_prodSO :
  forall n:nat, INR (fact n) = prod_f_R0 (fun k:nat =>
     (match (eq_nat_dec k 0) with
          | left   _ => 1%R
          | right _ => INR k
                        end)) n.
Proof.
  intro; induction  n as [| n Hrecn].
  - reflexivity.
  - simpl; rewrite <- Hrecn.
    case n; auto with real.
    intros; repeat rewrite plus_INR;rewrite mult_INR;ring.
Qed.

Lemma le_n_2n : forall n:nat, (n <= 2 * n)%nat.
Proof.
  simple induction n.
  - replace (2 * 0)%nat with 0%nat; [ apply le_n | ring ].
  - intros; replace (2 * S n0)%nat with (S (S (2 * n0))).
    + apply le_n_S; apply le_S; assumption.
    + replace (S (S (2 * n0))) with (2 * n0 + 2)%nat; [ idtac | ring ].
      replace (S n0) with (n0 + 1)%nat; [ idtac | ring ].
      ring.
Qed.

(** We prove that (N!)^2<=(2N-k)!*k! forall k in [|O;2N|] *)
Lemma RfactN_fact2N_factk :
  forall N k:nat,
    (k <= 2 * N)%nat ->
    Rsqr (INR (fact N)) <= INR (fact (2 * N - k)) * INR (fact k).
Proof.
  assert (forall (n:nat), 0 <= (if eq_nat_dec n 0 then 1 else INR n)). {
    intros; case (eq_nat_dec n 0); auto with real.
  }
  assert (forall (n:nat), (0 < n)%nat ->
                   (if eq_nat_dec n 0 then 1 else INR n) = INR n). {
    intros n; case (eq_nat_dec n 0); auto with real.
    intros; absurd (0 < n)%nat; lia.
  }
  intros; unfold Rsqr; repeat rewrite fact_prodSO.
  assert (H2:(k=N)%nat \/ (k < N)%nat \/ (N < k)%nat) by lia.
  elim H2; intro H3.
  { rewrite H3; replace (2*N-N)%nat with N by lia;right; ring. }
  case H3; intro; clear H2 H3.
  + rewrite (prod_SO_split (fun l:nat => if eq_nat_dec l 0 then 1 else INR l) (2 * N - k) N).
    2:{ lia. }
    rewrite Rmult_assoc; apply Rmult_le_compat_l.
    { apply prod_SO_pos; intros; auto. }
    replace (2 * N - k - N-1)%nat with (N - k-1)%nat by lia.
    rewrite Rmult_comm;
      rewrite (prod_SO_split (fun l:nat => if eq_nat_dec l 0 then 1 else INR l) N k).
    2:{ lia. }
    apply Rmult_le_compat_l.
    * apply prod_SO_pos; intros; auto.
    * apply prod_SO_Rle; intros; split; auto.
      rewrite H0.
      -- rewrite H0.
         ++ apply le_INR; lia.
         ++ lia.
      -- lia.
  + rewrite <- (Rmult_comm (prod_f_R0 (fun l:nat =>
                                        if eq_nat_dec l 0 then 1 else INR l) k));
      rewrite (prod_SO_split (fun l:nat => if eq_nat_dec l 0 then 1 else INR l) k N).
    2:{ lia. }
    rewrite Rmult_assoc; apply Rmult_le_compat_l.
    { apply prod_SO_pos; intros; auto. }
    rewrite Rmult_comm;
      rewrite (prod_SO_split (fun l:nat => if eq_nat_dec l 0 then 1 else INR l) N (2 * N - k)).
    2:{ lia. }
    apply Rmult_le_compat_l.
    { apply prod_SO_pos; intros; auto. }
    replace (N - (2 * N - k)-1)%nat with (k - N-1)%nat.
    2:{ lia. }
    apply prod_SO_Rle; intros; split; auto.
    rewrite H0.
    2:{ lia. }
    rewrite H0.
    2:{ lia. }
    apply le_INR; lia.
Qed.


(**********)
Lemma INR_fact_lt_0 : forall n:nat, 0 < INR (fact n).
Proof.
  intro; apply lt_INR_0; apply Nat.neq_0_lt_0; red; intro;
    elim (fact_neq_0 n); assumption.
Qed.

(** We have the following inequality : (C 2N k) <= (C 2N N) forall k in [|O;2N|] *)
Lemma C_maj : forall N k:nat, (k <= 2 * N)%nat -> C (2 * N) k <= C (2 * N) N.
Proof.
  intros; unfold C; unfold Rdiv; apply Rmult_le_compat_l.
  { apply pos_INR. }
  replace (2 * N - N)%nat with N.
  - apply Rmult_le_reg_l with (INR (fact N) * INR (fact N)).
    { apply Rmult_lt_0_compat; apply INR_fact_lt_0. }
    rewrite Rinv_r.
    + rewrite Rmult_comm;
        apply Rmult_le_reg_l with (INR (fact k) * INR (fact (2 * N - k))).
      { apply Rmult_lt_0_compat; apply INR_fact_lt_0. }
      rewrite Rmult_1_r; rewrite <- mult_INR; rewrite <- Rmult_assoc;
        rewrite Rinv_r.
      * rewrite Rmult_1_l; rewrite mult_INR; rewrite (Rmult_comm (INR (fact k)));
          replace (INR (fact N) * INR (fact N)) with (Rsqr (INR (fact N))).
        -- apply RfactN_fact2N_factk.
           assumption.
        -- reflexivity.
      * rewrite mult_INR; apply prod_neq_R0; apply INR_fact_neq_0.
    + apply prod_neq_R0; apply INR_fact_neq_0.
  - lia.
Qed.
