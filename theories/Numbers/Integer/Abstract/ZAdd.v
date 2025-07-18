(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

From Stdlib Require Export ZBase.

Module ZAddProp (Import Z : ZAxiomsMiniSig').
Include ZBaseProp Z.

(** Theorems that are either not valid on N or have different proofs
    on N and Z *)

#[global] Hint Rewrite opp_0 : nz.

Theorem add_pred_l n m : P n + m == P (n + m).
Proof.
rewrite <- (succ_pred n) at 2.
now rewrite add_succ_l, pred_succ.
Qed.

Theorem add_pred_r n m : n + P m == P (n + m).
Proof.
rewrite 2 (add_comm n); apply add_pred_l.
Qed.

Theorem add_opp_r n m : n + (- m) == n - m.
Proof.
nzinduct m.
- now nzsimpl.
- intro m. rewrite opp_succ, sub_succ_r, add_pred_r. now rewrite pred_inj_wd.
Qed.

Theorem sub_0_l n : 0 - n == - n.
Proof.
rewrite <- add_opp_r; now rewrite add_0_l.
Qed.

Theorem sub_succ_l n m : S n - m == S (n - m).
Proof.
rewrite <- 2 add_opp_r; now rewrite add_succ_l.
Qed.

Theorem sub_pred_l n m : P n - m == P (n - m).
Proof.
rewrite <- (succ_pred n) at 2.
rewrite sub_succ_l; now rewrite pred_succ.
Qed.

Theorem sub_pred_r n m : n - (P m) == S (n - m).
Proof.
rewrite <- (succ_pred m) at 2.
rewrite sub_succ_r; now rewrite succ_pred.
Qed.

Theorem opp_pred n : - (P n) == S (- n).
Proof.
rewrite <- (succ_pred n) at 2.
rewrite opp_succ. now rewrite succ_pred.
Qed.

Theorem sub_diag n : n - n == 0.
Proof.
nzinduct n.
- now nzsimpl.
- intro n. rewrite sub_succ_r, sub_succ_l; now rewrite pred_succ.
Qed.

Theorem add_opp_diag_l n : - n + n == 0.
Proof.
now rewrite add_comm, add_opp_r, sub_diag.
Qed.

Theorem add_opp_diag_r n : n + (- n) == 0.
Proof.
rewrite add_comm; apply add_opp_diag_l.
Qed.

Theorem add_opp_l n m : - m + n == n - m.
Proof.
rewrite <- add_opp_r; now rewrite add_comm.
Qed.

Theorem add_sub_assoc n m p : n + (m - p) == (n + m) - p.
Proof.
rewrite <- 2 add_opp_r; now rewrite add_assoc.
Qed.

Theorem opp_involutive n : - (- n) == n.
Proof.
nzinduct n.
- now nzsimpl.
- intro n. rewrite opp_succ, opp_pred. now rewrite succ_inj_wd.
Qed.

Theorem opp_add_distr n m : - (n + m) == - n + (- m).
Proof.
nzinduct n.
- now nzsimpl.
- intro n. rewrite add_succ_l; do 2 rewrite opp_succ; rewrite add_pred_l.
  now rewrite pred_inj_wd.
Qed.

Theorem opp_sub_distr n m : - (n - m) == - n + m.
Proof.
rewrite <- add_opp_r, opp_add_distr.
now rewrite opp_involutive.
Qed.

Theorem opp_inj n m : - n == - m -> n == m.
Proof.
intros H. apply opp_wd in H. now rewrite 2 opp_involutive in H.
Qed.

Theorem opp_inj_wd n m : - n == - m <-> n == m.
Proof.
split; [apply opp_inj | intros; now f_equiv].
Qed.

Theorem eq_opp_l n m : - n == m <-> n == - m.
Proof.
now rewrite <- (opp_inj_wd (- n) m), opp_involutive.
Qed.

Theorem eq_opp_r n m : n == - m <-> - n == m.
Proof.
symmetry; apply eq_opp_l.
Qed.

Theorem sub_add_distr n m p : n - (m + p) == (n - m) - p.
Proof.
rewrite <- add_opp_r, opp_add_distr, add_assoc.
now rewrite 2 add_opp_r.
Qed.

Theorem sub_sub_distr n m p : n - (m - p) == (n - m) + p.
Proof.
rewrite <- add_opp_r, opp_sub_distr, add_assoc.
now rewrite add_opp_r.
Qed.

Theorem sub_opp_l n m : - n - m == - m - n.
Proof.
rewrite <- 2 add_opp_r. now rewrite add_comm.
Qed.

Theorem sub_opp_r n m : n - (- m) == n + m.
Proof.
rewrite <- add_opp_r; now rewrite opp_involutive.
Qed.

Theorem add_sub_swap n m p : n + m - p == n - p + m.
Proof.
rewrite <- add_sub_assoc, <- (add_opp_r n p), <- add_assoc.
now rewrite add_opp_l.
Qed.

Theorem sub_cancel_l n m p : n - m == n - p <-> m == p.
Proof.
rewrite <- (add_cancel_l (n - m) (n - p) (- n)).
rewrite 2 add_sub_assoc. rewrite add_opp_diag_l; rewrite 2 sub_0_l.
apply opp_inj_wd.
Qed.

Theorem sub_cancel_r n m p : n - p == m - p <-> n == m.
Proof.
stepl (n - p + p == m - p + p) by apply add_cancel_r.
now do 2 rewrite <- sub_sub_distr, sub_diag, sub_0_r.
Qed.

(** The next several theorems are devoted to moving terms from one
    side of an equation to the other. The name contains the operation
    in the original equation ([add] or [sub]) and the indication
    whether the left or right term is moved. *)

Theorem add_move_l n m p : n + m == p <-> m == p - n.
Proof.
stepl (n + m - n == p - n) by apply sub_cancel_r.
now rewrite add_comm, <- add_sub_assoc, sub_diag, add_0_r.
Qed.

Theorem add_move_r n m p : n + m == p <-> n == p - m.
Proof.
rewrite add_comm; now apply add_move_l.
Qed.

(** The two theorems above do not allow rewriting subformulas of the
    form [n - m == p] to [n == p + m] since subtraction is in the
    right-hand side of the equation. Hence the following two
    theorems. *)

Theorem sub_move_l n m p : n - m == p <-> - m == p - n.
Proof.
rewrite <- (add_opp_r n m); apply add_move_l.
Qed.

Theorem sub_move_r n m p : n - m == p <-> n == p + m.
Proof.
rewrite <- (add_opp_r n m). now rewrite add_move_r, sub_opp_r.
Qed.

Theorem add_move_0_l n m : n + m == 0 <-> m == - n.
Proof.
now rewrite add_move_l, sub_0_l.
Qed.

Theorem add_move_0_r n m : n + m == 0 <-> n == - m.
Proof.
now rewrite add_move_r, sub_0_l.
Qed.

Theorem sub_move_0_l n m : n - m == 0 <-> - m == - n.
Proof.
now rewrite sub_move_l, sub_0_l.
Qed.

Theorem sub_move_0_r n m : n - m == 0 <-> n == m.
Proof.
now rewrite sub_move_r, add_0_l.
Qed.

(** The following section is devoted to cancellation of like
    terms. The name includes the first operator and the position of
    the term being canceled. *)

Theorem add_simpl_l n m : n + m - n == m.
Proof.
now rewrite add_sub_swap, sub_diag, add_0_l.
Qed.

Theorem add_simpl_r n m : n + m - m == n.
Proof.
now rewrite <- add_sub_assoc, sub_diag, add_0_r.
Qed.

Theorem sub_simpl_l n m : - n - m + n == - m.
Proof.
now rewrite <- add_sub_swap, add_opp_diag_l, sub_0_l.
Qed.

Theorem sub_simpl_r n m : n - m + m == n.
Proof.
now rewrite <- sub_sub_distr, sub_diag, sub_0_r.
Qed.

Theorem sub_add n m : m - n + n == m.
Proof.
now rewrite <- add_sub_swap, add_simpl_r.
Qed.

(** Now we have two sums or differences; the name includes the two
    operators and the position of the terms being canceled *)

Theorem add_add_simpl_l_l n m p : (n + m) - (n + p) == m - p.
Proof.
now rewrite (add_comm n m), <- add_sub_assoc,
sub_add_distr, sub_diag, sub_0_l, add_opp_r.
Qed.

Theorem add_add_simpl_l_r n m p : (n + m) - (p + n) == m - p.
Proof.
rewrite (add_comm p n); apply add_add_simpl_l_l.
Qed.

Theorem add_add_simpl_r_l n m p : (n + m) - (m + p) == n - p.
Proof.
rewrite (add_comm n m); apply add_add_simpl_l_l.
Qed.

Theorem add_add_simpl_r_r n m p : (n + m) - (p + m) == n - p.
Proof.
rewrite (add_comm p m); apply add_add_simpl_r_l.
Qed.

Theorem sub_add_simpl_r_l n m p : (n - m) + (m + p) == n + p.
Proof.
now rewrite <- sub_sub_distr, sub_add_distr, sub_diag,
sub_0_l, sub_opp_r.
Qed.

Theorem sub_add_simpl_r_r n m p : (n - m) + (p + m) == n + p.
Proof.
rewrite (add_comm p m); apply sub_add_simpl_r_l.
Qed.

(** Of course, there are many other variants *)

End ZAddProp.
