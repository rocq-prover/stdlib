(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import QArith_base.
From Stdlib Require Import Zdiv Zquot.

(************)

#[local] Coercion inject_Z : Z >-> Q.

(** [Qfloor x] returns the greatest integer [i] such that [i <= x].
    Put another way, this rounds [x] towards negative infinity. *)

Definition Qfloor (x:Q) := let (n,d) := x in Z.div n (Zpos d).

(** [Qfloor_frac_part x] returns a fraction [f] such that [0 <= f < 1] and
    [x = Qfloor x + f]. For example, [Qfloor_frac_part 1.6 = 0.6] and
    [Qfloor_frac_part (-1.6) = 0.4]. *)

Definition Qfloor_frac_part (x:Q) := let (n,d) := x in Z.modulo n (Zpos d) # d.

(** [Qceiling x] returns the smaller integer [i] such that [x <= i].
    Put another way, this rounds [x] towards positive infinity. *)

Definition Qceiling (x:Q) := (-(Qfloor (-x)))%Z.

(** [Qtruncate x] returns the nearest integer between [0] and [x].
    For non-negative [x] values, this is equivalent to [Qfloor x].
    For negative [x] values, this is equivalent to [Qceiling x].
    Put another way, this rounds [x] towards zero. *)

Definition Qtruncate (x:Q) :=
  if Qle_bool 0 x
    then Qfloor x
    else Qceiling x.

(** [Qtruncate_frac_part x] returns a fraction [f] such that [Z.abs f < 1] and
    [x = Qtruncate x + f]. For example, [Qtruncate_frac_part 1.6 = 0.6] and
    [Qtruncate_frac_part (-1.6) = -0.6]. *)

Definition Qtruncate_frac_part (x:Q) := let (n,d) := x in Z.rem n (Zpos d) # d.

(** An equivalent definition of [Qtruncate] in terms of [Z.quot]. *)

Lemma Qtruncate_quot : forall x, Qtruncate x = let (n,d) := x in Z.quot n (Zpos d).
Proof.
intros x.
destruct x as [n d].
unfold Qtruncate.
destruct (Qle_bool 0 (n # d)) eqn:H0.
- apply Qle_bool_imp_le in H0.
  change (0 <= n # d)%Q with (inject_Z 0 <= inject_Z n) in H0.
  rewrite <- (Zle_Qle 0 n) in H0.
  now rewrite (Z.quot_div_nonneg n (Z.pos d) H0 eq_refl).
- unfold Qceiling, Qfloor.
  simpl.
  rewrite (Z.quot_div n (Z.pos d) ltac:(discriminate)).
  simpl.
  rewrite (Z.mul_1_r (Z.sgn n)).
  change (Qle_bool 0 (n # d) = false) with (Qle_bool 0 (inject_Z n) = false) in H0.
  unfold Qle_bool in H0.
  simpl in H0.
  rewrite (Z.mul_1_r n) in H0.
  rewrite Z.leb_nle in H0.
  destruct (Z.abs_spec n) as [[H1 H2]|[H1 H2]].
  + contradiction.
  + rewrite H2.
    now rewrite (Z.sgn_neg n H1).
Qed.

(** [Qfloor_frac_part] and [Qtrunc_frac_part] properties *)

Lemma Qfloor_proper_fraction : forall x, x = inject_Z (Qfloor x) + Qfloor_frac_part x.
Proof.
intros [n d].
unfold Qfloor, Qfloor_frac_part, Qplus.
simpl.
rewrite (Z.mul_1_r (Z.modulo n (Z.pos d))).
rewrite (Z.mul_comm (Z.div n (Z.pos d)) (Z.pos d)).
now rewrite <- (Z.div_mod n (Z.pos d)).
Qed.

Lemma Qtruncate_proper_fraction : forall x, x = inject_Z (Qtruncate x) + Qtruncate_frac_part x.
Proof.
intros [n d].
rewrite Qtruncate_quot.
unfold Qtruncate_frac_part, Qplus.
simpl.
rewrite (Z.mul_1_r (Z.rem n (Z.pos d))).
rewrite (Z.mul_comm (Z.quot n (Z.pos d)) (Z.pos d)).
now rewrite <- (Z.quot_rem n (Z.pos d)).
Qed.

Lemma Qfloor_floor_frac_part : forall x, Qfloor (Qfloor_frac_part x) = 0%Z.
Proof.
intros [n d].
simpl.
apply Zmod_div.
Qed.

Lemma Qceiling_floor_frac_part : forall x, Qfloor_frac_part x == 0 \/ Qceiling (Qfloor_frac_part x) = 1%Z.
Proof.
intros x.
destruct (Qeq_dec (Qfloor_frac_part x) 0) as [Hl|Hr].
- left.
  exact Hl.
- right.
  destruct x as [n d].
  unfold Qceiling, Qfloor_frac_part, Qfloor in *.
  simpl in *.
  unfold Qeq in Hr.
  simpl in Hr.
  rewrite Z.mul_1_r in Hr.
  change 1%Z with (- - 1)%Z.
  f_equal.
  rewrite Z_div_nz_opp_full.
  + now rewrite Zmod_div.
  + discriminate.
  + rewrite Zmod_mod.
    exact Hr.
Qed.

Lemma Qfloor_frac_part_bounds : forall x, 0 <= Qfloor_frac_part x < 1.
Proof.
intros [n d].
unfold Qfloor_frac_part, Qle, Qlt.
simpl.
rewrite (Z.mul_1_r (Z.modulo n (Z.pos d))).
now apply Z.mod_pos_bound.
Qed.

Lemma Qtruncate_frac_part_bounds : forall x, -1 < Qtruncate_frac_part x < 1.
Proof.
intros [n d].
unfold Qtruncate_frac_part, Qlt.
simpl.
rewrite (Z.mul_1_r (Z.rem n (Z.pos d))).
destruct (ZArith_dec.Z_lt_le_dec n 0) as [H|H].
- apply Z.lt_le_incl in H.
  destruct (Zrem_lt_neg_pos n (Z.pos d) H eq_refl) as [X Y].
  split.
  + apply X.
  + apply (Z.le_lt_trans (Z.rem n (Z.pos d)) 0 (Z.pos d) Y eq_refl).
- destruct (Zrem_lt_pos_pos n (Z.pos d) H eq_refl) as [X Y].
  split.
  + apply (Z.lt_le_trans (Z.neg d) 0 (Z.rem n (Z.pos d)) eq_refl X).
  + apply Y.
Qed.

Lemma Qfloor_Z : forall z:Z, Qfloor z = z.
Proof.
intros z.
simpl.
auto with *.
Qed.

Lemma Qceiling_Z : forall z:Z, Qceiling z = z.
Proof.
intros z.
unfold Qceiling.
simpl.
rewrite Z.div_1_r.
apply Z.opp_involutive.
Qed.

Lemma Qtruncate_Z : forall z:Z, Qtruncate z = z.
Proof.
intros z.
unfold Qtruncate.
destruct (Qle_bool 0 z).
- apply Qfloor_Z.
- apply Qceiling_Z.
Qed.

Lemma Qfloor_le : forall x, Qfloor x <= x.
Proof.
intros [n d].
simpl.
unfold Qle.
simpl.
replace (n*1)%Z with n by ring.
rewrite Z.mul_comm.
now apply Z.mul_div_le.
Qed.

#[global]
Hint Resolve Qfloor_le : qarith.

Lemma Qle_ceiling : forall x, x <= Qceiling x.
Proof.
intros x.
apply Qle_trans with (- - x).
- rewrite Qopp_involutive.
  auto with *.
- change (Qceiling x:Q) with (-(Qfloor(-x))).
  auto with *.
Qed.

#[global]
Hint Resolve Qle_ceiling : qarith.

Lemma Qle_floor_ceiling : forall x, Qfloor x <= Qceiling x.
Proof.
eauto with qarith.
Qed.

Lemma Qle_floor_truncate : forall x, Qfloor x <= Qtruncate x.
Proof.
intros x.
unfold Qtruncate.
destruct (Qle_bool 0 x).
- apply Qle_refl.
- apply Qle_floor_ceiling.
Qed.

Lemma Qle_truncate_ceiling : forall x, Qtruncate x <= Qceiling x.
Proof.
intros x.
unfold Qtruncate.
destruct (Qle_bool 0 x).
- apply Qle_floor_ceiling.
- apply Qle_refl.
Qed.

Lemma Qlt_floor : forall x, x < (Qfloor x+1)%Z.
Proof.
intros [n d].
simpl.
unfold Qlt.
simpl.
replace (n*1)%Z with n by ring.
ring_simplify.
replace (n / Zpos d * Zpos d + Zpos d)%Z with
  ((Zpos d * (n / Zpos d) + n mod Zpos  d) + Zpos  d - n mod Zpos d)%Z by ring.
rewrite <- Z_div_mod_eq_full.
rewrite <- Z.lt_add_lt_sub_r.
apply Z.add_lt_mono_l, Z.mod_pos_bound, eq_refl.
Qed.

#[global]
Hint Resolve Qlt_floor : qarith.

Lemma Qceiling_lt : forall x, (Qceiling x-1)%Z < x.
Proof.
intros x.
unfold Qceiling.
replace (- Qfloor (- x) - 1)%Z with (-(Qfloor (-x) + 1))%Z by ring.
change ((- (Qfloor (- x) + 1))%Z:Q) with (-(Qfloor (- x) + 1)%Z).
apply Qlt_le_trans with (- - x); auto with *.
rewrite Qopp_involutive.
apply Qle_refl.
Qed.

#[global]
Hint Resolve Qceiling_lt : qarith.

Lemma Qfloor_resp_le : forall x y, x <= y -> (Qfloor x <= Qfloor y)%Z.
Proof.
intros [xn xd] [yn yd] Hxy.
unfold Qle in *.
simpl in *.
rewrite <- (Zdiv_mult_cancel_r xn (Zpos xd) (Zpos yd)); auto with *.
rewrite <- (Zdiv_mult_cancel_r yn (Zpos yd) (Zpos xd)); auto with *.
rewrite (Z.mul_comm (Zpos yd) (Zpos xd)).
apply Z.div_le_mono, Hxy; apply eq_refl.
Qed.

#[global]
Hint Resolve Qfloor_resp_le : qarith.

Lemma Qceiling_resp_le : forall x y, x <= y -> (Qceiling x <= Qceiling y)%Z.
Proof.
intros x y Hxy.
unfold Qceiling.
rewrite <- Z.opp_le_mono; auto with qarith.
Qed.

#[global]
Hint Resolve Qceiling_resp_le : qarith.

Lemma Qtruncate_resp_le : forall x y, x <= y -> (Qtruncate x <= Qtruncate y)%Z.
Proof.
intros x y Hxy.
unfold Qtruncate.
destruct (Qle_bool 0 x) eqn:Hx, (Qle_bool 0 y) eqn:Hy.
- now apply Qfloor_resp_le.
- apply Qle_bool_imp_le in Hx.
  apply Qle_bool_imp_gt in Hy.
  apply (Qle_trans 0 x y Hx) in Hxy.
  apply (Qle_lt_trans 0 y 0 Hxy) in Hy.
  discriminate Hy.
- apply Qle_bool_imp_gt in Hx.
  apply Qle_bool_imp_le in Hy.
  apply Qlt_le_weak in Hx.
  apply Qceiling_resp_le in Hx.
  apply Qfloor_resp_le in Hy.
  apply (Z.le_trans _ _ _ Hx Hy).
- now apply Qceiling_resp_le.
Qed.

#[global]
Hint Resolve Qtruncate_resp_le : qarith.

Add Morphism Qfloor with signature Qeq ==> eq as Qfloor_comp.
Proof.
intros x y H.
apply Z.le_antisymm.
- auto with *.
- symmetry in H; auto with *.
Qed.

Add Morphism Qceiling with signature Qeq ==> eq as Qceiling_comp.
Proof.
intros x y H.
apply Z.le_antisymm.
- auto with *.
- symmetry in H; auto with *.
Qed.

Add Morphism Qtruncate with signature Qeq ==> eq as Qtruncate_comp.
Proof.
intros x y H.
apply Z.le_antisymm.
- auto with *.
- symmetry in H; auto with *.
Qed.

Lemma Zdiv_Qdiv (n m: Z): (n / m)%Z = Qfloor (n / m).
Proof.
 unfold Qfloor. intros. simpl.
 destruct m as [ | | p]; simpl.
 - now rewrite Z.div_0_r, Z.mul_0_r.
 - now rewrite Z.mul_1_r.
 - rewrite <- Z.opp_eq_mul_m1.
   rewrite <- (Z.opp_involutive (Zpos p)).
   now rewrite Zdiv_opp_opp.
Qed.