(******************************************************************************)
(*                                                                            *)
(*  Zfloor x        == floor function : R -> Z                                *)
(*  Zceil x         == ceil function : R -> Z                                 *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Rbase Rfunctions Lra Lia.

Local Open Scope R_scope.

Definition Zfloor (x : R) := (up x - 1)%Z.

Lemma up_Zfloor x : up x = (Zfloor x + 1)%Z.
Proof. unfold Zfloor; lia. Qed.

Lemma IZR_up_Zfloor x : IZR (up x) = IZR (Zfloor x) + 1.
Proof. now rewrite up_Zfloor, plus_IZR. Qed.

Lemma Zfloor_bound x : IZR (Zfloor x) <= x < IZR (Zfloor x) + 1.
Proof.
unfold Zfloor; rewrite minus_IZR.
generalize (archimed x); lra.
Qed.

Lemma Zfloor_lub (z : Z) x : IZR z <= x -> (z <= Zfloor x)%Z.
Proof.
intro H.
assert (H1 : (z < Zfloor x + 1)%Z);[| lia].
apply lt_IZR; rewrite plus_IZR.
now generalize (Zfloor_bound x); lra.
Qed.

Lemma Zfloor_eq (z : Z) x :  IZR z <= x < IZR z + 1 -> Zfloor x = z.
Proof.
intro xB.
assert (ZxB := Zfloor_bound x).
assert (B : (Zfloor x < z + 1 /\ z <= Zfloor x)%Z) ; [| lia].
split; [|apply Zfloor_lub; lra].
apply lt_IZR; rewrite plus_IZR; lra.
Qed.

Lemma Zfloor_le x y : x <= y -> (Zfloor x <= Zfloor y)%Z.
Proof.
intro H; apply Zfloor_lub; generalize (Zfloor_bound x); lra.
Qed.

Lemma Zfloor_addz (z: Z) x : Zfloor (x + IZR z) = (Zfloor x + z)%Z.
Proof.
assert (ZB := Zfloor_bound x).
now apply Zfloor_eq; rewrite plus_IZR; lra.
Qed.

Lemma ZfloorZ (z : Z) : Zfloor (IZR z) = z.
Proof. now apply Zfloor_eq; lra. Qed.


Lemma ZfloorNZ (z : Z) : Zfloor (- IZR z) = (- z)%Z.
Proof. now rewrite <- opp_IZR, ZfloorZ. Qed.

Lemma ZfloorD_cond r1 r2 :
  if Rle_dec (IZR (Zfloor r1) + IZR (Zfloor r2) + 1) (r1 + r2)
  then Zfloor (r1 + r2) = (Zfloor r1 + Zfloor r2 + 1)%Z
  else  Zfloor (r1 + r2) = (Zfloor r1 + Zfloor r2)%Z.
Proof.
destruct (Zfloor_bound r1, Zfloor_bound r2) as [H1 H2].
case Rle_dec; intro H.
  now apply Zfloor_eq; rewrite plus_IZR, plus_IZR; lra.
now apply Zfloor_eq; rewrite plus_IZR; lra.
Qed.

Definition Zceil (x : R) := (- Zfloor (- x))%Z.

Theorem Zceil_bound x : (IZR (Zceil x) - 1 < x <= IZR (Zceil x))%R.
Proof.
now unfold Zceil; generalize (Zfloor_bound (- x)); rewrite !opp_IZR; lra.
Qed.

Theorem Zfloor_ceil_bound x : (IZR (Zfloor x) <= x <= IZR (Zceil x))%R.
Proof. now generalize (Zfloor_bound x) (Zceil_bound x); lra. Qed.

Theorem ZceilN x : (Zceil (- x) = - Zfloor x)%Z.
Proof. now unfold Zceil; rewrite Ropp_involutive. Qed.

Theorem ZfloorN x : (Zfloor (- x) = - Zceil x)%Z.
Proof. unfold Zceil; lia. Qed.

Lemma Zceil_eq (z : Z) x :  IZR z - 1 < x <= IZR z -> Zceil x = z.
Proof.
intro xB; assert (H : Zfloor (- x) = (- z)%Z); [|unfold Zceil; lia].
now apply Zfloor_eq; rewrite opp_IZR; lra.
Qed.

Lemma Zceil_le x y : x <= y -> (Zceil x <= Zceil y)%Z.
Proof.
intro xLy; apply Z.opp_le_mono; unfold Zceil; rewrite !Z.opp_involutive.
now apply Zfloor_le; lra.
Qed.

Lemma Zceil_addz (z: Z) x : Zceil (x + IZR z) = (Zceil x + z)%Z.
Proof.
now unfold Zceil; rewrite Ropp_plus_distr, <- opp_IZR, Zfloor_addz; lia.
Qed.

Lemma ZceilD_cond r1 r2 :
  if Rle_dec (r1 + r2) (IZR (Zceil r1) + IZR (Zceil r2) - 1)
  then Zceil (r1 + r2) = (Zceil r1 + Zceil r2 - 1)%Z
  else Zceil (r1 + r2) = (Zceil r1 + Zceil r2)%Z.
Proof.
generalize (ZfloorD_cond (- r1) (- r2)).
now unfold Zceil; rewrite !opp_IZR; do 2 case Rle_dec; try lra;
    rewrite Ropp_plus_distr; lia.
Qed.

Lemma ZfloorB_cond r1 r2 :
  if Rle_dec (IZR (Zfloor r1) - IZR (Zceil r2) + 1) (r1 - r2)
  then Zfloor (r1 - r2) = (Zfloor r1 - Zceil r2 + 1)%Z
  else  Zfloor (r1 - r2) = (Zfloor r1 - Zceil r2)%Z.
Proof.
now generalize (ZfloorD_cond r1 (- r2)); rewrite !ZfloorN, !opp_IZR.
Qed.

Lemma ZceilB_cond r1 r2 :
  if Rle_dec (r1 - r2) (IZR (Zceil r1) - IZR (Zfloor r2) - 1)
  then Zceil (r1 - r2) = (Zceil r1 - Zfloor r2 - 1)%Z
  else Zceil (r1 - r2) = (Zceil r1 - Zfloor r2)%Z.
Proof.
now generalize (ZceilD_cond r1 (- r2)); rewrite !ZceilN, !opp_IZR.
Qed.
