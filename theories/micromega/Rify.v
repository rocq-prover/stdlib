(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import Rbase Rbasic_fun.
From Stdlib Require Import isZ TifyClasses.
Declare ML Module "rocq-runtime.plugins.zify".
Local Open Scope Z_scope.
Open Scope R_scope.

Ltac rify := Tify.tify R.

(** Supported types [positive] [Z] [N] [nat] [R] *)

#[global]
Instance Inj_Z_R : InjTyp Z R.
Proof.
  apply (mkinj _ _ IZR isZ).
  - intros. unfold isZ. eexists. reflexivity.
Defined.
Add Tify InjTyp Inj_Z_R.


#[global] Instance Inj_P_R : InjTyp positive  R.
Proof.
  apply (mkinj _ _ IPR (fun x => isZ x /\ 1 <= x)).
  - intros. unfold isZ. split. eexists (Zpos x). reflexivity.
    apply IPR_ge_1.
Defined.
Add Tify InjTyp Inj_P_R.


#[global] Instance Inj_nat_R : InjTyp nat R.
Proof.
  apply (mkinj _ _ INR (fun x => isZ x /\ 0 <= x)).
  - intros. unfold isZ. split.
    exists (Z.of_nat x). symmetry. apply INR_IZR_INZ.
    apply pos_INR.
Defined.
Add Tify InjTyp Inj_nat_R.

Definition InjNR (n:N) : R :=
  match n with
    | N0 => IZR 0%Z
    | Npos p => IZR (Zpos p)
  end.

Lemma IZR_of_N : forall x, IZR (Z.of_N x) = InjNR x.
Proof.
  destruct x; simpl; reflexivity.
Qed.

Lemma InjNR_pos : forall x,
    0 <= InjNR x.
Proof.
  destruct x; simpl.
  apply Rle_refl.
  unfold IZR.
  apply Rle_trans with (r2:= R1).
  apply Rle_0_1.
  apply (IPR_ge_1 p).
Qed.

#[global]
Instance Inj_N_R : InjTyp N R.
Proof.
  apply (mkinj _ _ InjNR (fun x => isZ x /\ 0 <= x)).
  - intros. unfold isZ.
    split.
    exists (Z.of_N x). apply IZR_of_N. apply InjNR_pos.
Defined.
Add Tify InjTyp Inj_N_R.

#[global]
Instance Inj_R_R : InjTyp R R.
Proof.
  apply (mkinj _ _ (fun x => x) (fun x => True) (fun _ => I)).
Defined.

(** [R -> R -> Prop] :  [@eq R], [Rle], [Rge], [Rlt], [Rgt] *)

#[global]
Instance Op_eqR : BinRel (@eq R).
Proof.
apply mkbrel with (TR := @eq R).
simpl. tauto.
Defined.
Add Tify BinRel Op_eqR.

#[global]
Instance Op_Rle : BinRel (Rle).
Proof.
apply mkbrel with (TR := Rle).
simpl. tauto.
Defined.
Add Tify BinRel Op_Rle.

#[global]
Instance Op_Rlt : BinRel (Rlt).
Proof.
apply mkbrel with (TR := Rlt).
simpl. tauto.
Defined.
Add Tify BinRel Op_Rlt.

#[global]
Instance Op_Rgt : BinRel (Rgt).
Proof.
apply mkbrel with (TR := Rgt).
simpl. tauto.
Defined.
Add Tify BinRel Op_Rgt.

#[global]
Instance Op_Rge : BinRel (Rge).
Proof.
apply mkbrel with (TR := Rge).
simpl. tauto.
Defined.
Add Tify BinRel Op_Rge.

(*  [R -> R] : [Ropp], [Rabs], [sqrt], [Rinv] *)

#[global]
Instance Op_Ropp : UnOp Ropp.
Proof.
  apply mkuop with (TUOp := Ropp).
  simpl.   reflexivity.
Defined.
Add Tify UnOp Op_Ropp.

#[global]
Instance Op_Rabs : UnOp Rabs.
Proof.
  apply mkuop with (TUOp := Rabs).
  reflexivity.
Defined.
Add Tify UnOp Op_Rabs.

#[global]
Instance Op_Rinv : UnOp Rinv.
Proof.
  apply mkuop with (TUOp := Rinv).
  simpl.   reflexivity.
Defined.
Add Tify UnOp Op_Rinv.


(* [R -> R -> R] : [Rplus] [Rminus] [Rmult] [Rmin] [Rmax] [Rdiv] *)

#[global]
Instance Op_Rplus : BinOp Rplus.
Proof.
  apply mkbop with (TBOp := Rplus).
  reflexivity.
Defined.
Add Tify BinOp Op_Rplus.

#[global]
Instance Op_Rminus : BinOp Rminus.
Proof.
  apply mkbop with (TBOp := Rminus).
  reflexivity.
Defined.
Add Tify BinOp Op_Rminus.


#[global]
Instance Op_Rmult : BinOp Rmult.
Proof.
  apply mkbop with (TBOp := Rmult).
  reflexivity.
Defined.
Add Tify BinOp Op_Rmult.

#[global]
Instance Op_Rmin : BinOp Rmin.
Proof.
  apply mkbop with (TBOp := Rmin).
  reflexivity.
Defined.
Add Tify BinOp Op_Rmin.

#[global]
Instance Op_Rmax : BinOp Rmax.
Proof.
  apply mkbop with (TBOp := Rmax).
  reflexivity.
Defined.
Add Tify BinOp Op_Rmax.

#[global]
Instance Op_div : BinOp Rdiv.
Proof.
  apply mkbop with (TBOp := (fun x  y => x * / y)).
  reflexivity.
Defined.
Add Tify BinOp Op_div.

(** [Z -> Z -> Prop] : [@eq Z], [Z.le], [Z.gt],  *)

#[global]
Instance Op_eq : BinRel (@eq Z).
Proof.
apply mkbrel with (TR := @eq R).
simpl. split; intro. congruence.
apply eq_IZR; auto.
Defined.
Add Tify BinRel Op_eq.

#[global]
Instance Op_le : BinRel Z.le.
Proof.
  apply mkbrel with (TR := Rle).
  split;intros.
  apply IZR_le; auto.
  apply le_IZR;auto.
Defined.
Add Tify BinRel Op_le.

#[global]
Instance Op_ge : BinRel Z.ge.
Proof.
  apply mkbrel with (TR := Rge).
  split;intros.
  apply IZR_ge; auto.
  apply Z.le_ge.
  apply le_IZR;auto.
  now apply Rge_le.
Defined.
Add Tify BinRel Op_ge.


#[global]
Instance Op_gt : BinRel Z.gt.
Proof.
apply mkbrel with (TR := Rgt).
unfold Rgt.
intros. simpl. split. intro. apply IZR_lt.
rewrite <- Z.gt_lt_iff. auto.
intros. apply lt_IZR in H. rewrite <- Z.gt_lt_iff in H. auto.
Defined.
Add Tify BinRel Op_gt.

#[global]
Instance Op_lt : BinRel Z.lt.
Proof.
apply mkbrel with (TR := Rlt).
intros. simpl. split. intro. now apply IZR_lt.
intros. now apply lt_IZR in H.
Defined.
Add Tify BinRel Op_lt.

(* [Z -> R] : [IZR] *)

#[global] Instance UnOp_IZR : UnOp IZR.
Proof.
  apply mkuop with (TUOp:= (fun x => x)).
  reflexivity.
Defined.
Add Tify UnOp UnOp_IZR.

(* [R -> Z] : [up] *)

Definition Rup (x:R) := IZR (up x).

#[global]
Instance Op_up : UnOp up.
Proof.
apply mkuop with (TUOp := Rup).
unfold inj,Rup. simpl.
reflexivity.
Defined.
Add Tify UnOp Op_up.

(* [Z] : Z0 *)

#[global]
Instance Op_Z0 : CstOp Z0.
Proof.
  apply mkcst with (TCst := R0).
  simpl.   reflexivity.
Defined.
Add Tify CstOp Op_Z0.

(* [Z -> Z] : [Z.opp] [Z.abs] [Z.succ] [Z.pred] *)

#[global]
  Instance Op_Z_opp : UnOp Z.opp.
Proof.
apply mkuop with (TUOp := Ropp).
apply opp_IZR.
Defined.
Add Tify UnOp Op_Z_opp.

#[global]
  Instance Op_Z_abs : UnOp Z.abs.
Proof.
apply mkuop with (TUOp := Rabs).
apply abs_IZR.
Defined.
Add Tify UnOp Op_Z_abs.

#[global]
  Instance Op_Z_succ : UnOp Z.succ.
Proof.
  apply mkuop with (TUOp := Rplus R1).
  simpl. intros.
  rewrite succ_IZR.
  rewrite Rplus_comm.
  reflexivity.
Defined.
Add Tify UnOp Op_Z_succ.

#[global]
  Instance Op_Z_pred : UnOp Z.pred.
Proof.
  apply mkuop with (TUOp := fun x => x - R1).
  simpl. intros.
  apply pred_IZR.
Defined.
Add Tify UnOp Op_Z_pred.

(* [positive -> Z] : [Z.pos] [Z.neg] *)

#[global]
Instance Op_Zpos : UnOp Zpos.
Proof.
  apply mkuop with (TUOp := fun x => x).
  simpl.   reflexivity.
Defined.
Add Tify UnOp Op_Zpos.

#[global]
Instance Op_Zneg : UnOp Zneg.
Proof.
  apply mkuop with (TUOp := Ropp).
  simpl.   reflexivity.
Defined.
Add Tify UnOp Op_Zneg.

(* [Z -> Z -> Z] : [Z.add] [Z.sub] [Z.mul] [Z.max] [Z.min] *)

#[global]
Instance Op_Zadd : BinOp Z.add.
Proof.
  apply mkbop with (TBOp := Rplus).
  simpl. intros. rewrite plus_IZR.
  reflexivity.
Defined.
Add Tify BinOp Op_Zadd.

#[global]
Instance Op_Zsub : BinOp Z.sub.
Proof.
  apply mkbop with (TBOp := Rminus).
  simpl. intros. apply minus_IZR.
Defined.
Add Tify BinOp Op_Zsub.

#[global]
Instance Op_Zmul : BinOp Z.mul.
Proof.
  apply mkbop with (TBOp := Rmult).
  simpl. intros. apply mult_IZR.
Defined.
Add Tify BinOp Op_Zmul.

Lemma max_IZR : forall x y,
    IZR (Z.max x y) = Rmax (IZR x) (IZR y).
Proof.
  intros.
  apply Rmax_case_strong;
    intros H; apply le_IZR in H;
    f_equal.
  now apply Z.max_l.
  now apply Z.max_r.
Qed.

#[global]
Instance Op_Zmax : BinOp Z.max.
Proof.
  apply mkbop with (TBOp := Rmax).
  simpl. intros. apply max_IZR.
Defined.
Add Tify BinOp Op_Zmax.

Lemma min_IZR : forall x y,
    IZR (Z.min x y) = Rmin (IZR x) (IZR y).
Proof.
  intros.
  apply Rmin_case_strong;
    intros H; apply le_IZR in H;
    f_equal.
  now apply Z.min_l.
  now apply Z.min_r.
Qed.

#[global]
Instance Op_Zmin : BinOp Z.min.
Proof.
  apply mkbop with (TBOp := Rmin).
  simpl. intros. apply min_IZR.
Defined.
Add Tify BinOp Op_Zmin.


(** minimal support for positive [xH], [xO], [xI], [IPR] *)

#[global]
Instance Op_xH : CstOp xH.
Proof.
  apply mkcst with (TCst := R1).
  reflexivity.
Defined.
Add Tify CstOp Op_xH.

#[global]
Instance Op_xI : UnOp xI.
Proof.
  apply mkuop with (TUOp := fun x => 2 * x + 1).
  simpl. apply IPR_xI.
Defined.
Add Tify UnOp Op_xI.

#[global]
Instance Op_xO : UnOp xO.
Proof.
  apply mkuop with (TUOp := fun x => 2 * x).
  simpl. apply IPR_xO.
Defined.
Add Tify UnOp Op_xO.

#[global] Instance UnOp_IPR : UnOp IPR.
Proof.
  apply mkuop with (TUOp:= (fun x => x)).
  reflexivity.
Defined.
Add Tify UnOp UnOp_IPR.

(* [nat] : O *)

#[global]
Instance Op_O : CstOp O.
Proof.
  apply mkcst with (TCst := R0).
  reflexivity.
Defined.
Add Tify CstOp Op_O.

(* [nat -> nat] : S *)

#[global]
Instance Op_S : UnOp S.
Proof.
  apply mkuop with (TUOp := Rplus R1).
  intro.
  rewrite S_INR. rewrite Rplus_comm. reflexivity.
Defined.
Add Tify UnOp Op_S.

#[global]
Instance Op_pred : UnOp Init.Nat.pred.
Proof.
  apply mkuop with (TUOp := (fun x => Rmax 0 (x - R1))).
  intro. simpl.
  destruct x.
  - simpl. rewrite Rmax_left. reflexivity.
    rewrite Rminus_0_l.
    change 0 with (IZR (- 0)).
    rewrite Ropp_Ropp_IZR.
    apply Ropp_le_contravar.
    apply Rle_0_1.
  - rewrite S_INR.
    simpl.
    rewrite Rmax_right. ring.
    replace (INR x + 1 - R1) with (INR x) by ring.
    apply (pos_INR x).
Defined.
Add Tify UnOp Op_pred.

(* [Z -> nat] : [Z.to_nat] *)

Lemma INR_to_nat_Rmax : forall x,
    INR (Z.to_nat x) = Rmax (IZR x) 0.
Proof.
  intros.
  rewrite INR_IZR_INZ.
  rewrite ZifyInst.of_nat_to_nat_eq.
  now rewrite Z.max_comm, max_IZR.
Qed.

#[global]
Instance Op_Z_to_nat : UnOp Z.to_nat.
Proof.
  apply mkuop with (TUOp := fun x => Rmax x 0).
  apply INR_to_nat_Rmax.
Defined.
Add Tify UnOp Op_Z_to_nat.

(* [nat -> nat -> Prop] : [@eq nat], [le], [ge], [lt], [gt] *)

#[global]
Instance Op_nat_eq : BinRel (@eq nat).
Proof.
  apply mkbrel with (TR := (@eq R)).
  split;intros.
  congruence.
  now apply INR_eq.
Defined.
Add Tify BinRel Op_nat_eq.


#[global]
Instance Op_nat_le : BinRel Peano.le.
Proof.
  apply mkbrel with (TR := Rle).
  split;intros.
  simpl.
  apply le_INR; auto.
  apply INR_le;auto.
Defined.
Add Tify BinRel Op_nat_le.

#[global]
Instance Op_nat_ge : BinRel Peano.ge.
Proof.
  apply mkbrel with (TR := Rge).
  split;intros.
  simpl.
  apply Rle_ge.
  apply le_INR; auto.
  apply INR_le;auto.
  now apply Rge_le.
Defined.
Add Tify BinRel Op_nat_ge.


#[global]
Instance Op_nat_lt : BinRel Peano.lt.
Proof.
  apply mkbrel with (TR := Rlt).
  split;intros.
  simpl.
  apply lt_INR; auto.
  apply INR_lt;auto.
Defined.
Add Tify BinRel Op_nat_lt.

#[global]
Instance Op_nat_gt : BinRel Peano.gt.
Proof.
  apply mkbrel with (TR := Rgt).
  split;intros.
  simpl.
  apply Rlt_gt.
  apply lt_INR; auto.
  apply INR_lt;auto.
Defined.
Add Tify BinRel Op_nat_gt.

(** [nat -> nat -> nat] : [add], [mul] *)

#[global]
Instance Op_nat_add : BinOp Init.Nat.add.
Proof.
  apply mkbop with (TBOp := Rplus).
  simpl. intros. rewrite plus_INR.
  reflexivity.
Defined.
Add Tify BinOp Op_nat_add.

Lemma sub_INR : forall x y,
    INR (x - y) = Rmax 0 ((INR x) - (INR y)).
Proof.
  intros.
  apply Rmax_case_strong.
  - revert y.
    induction x.
    + intros. reflexivity.
    + intros. destruct y.
      * rewrite INR_0 in H.
        rewrite S_INR in H.
        exfalso.
        pose proof (pos_INR x) as Px.
        pose proof (Rplus_le_compat _ _ _ _ H Px) as A.
        apply Rplus_le_compat with (1 := Rle_refl (-(INR x))) in A.
        ring_simplify in A.
        revert A. apply Rlt_not_le.
        apply Rlt_0_1.
      * rewrite Nat.sub_succ.
        apply IHx.
        rewrite !S_INR in H.
        now replace (INR x + 1 - (INR y + 1)) with (INR x - INR y) in H by ring.
  - intros. rewrite minus_INR. reflexivity.
    apply INR_le.
    apply Rplus_le_reg_r with (r := - INR y).
    rewrite Rplus_opp_r.
    apply H.
Qed.

Instance Op_nat_sub : BinOp Init.Nat.sub.
Proof.
  apply mkbop with (TBOp := fun x y => Rmax 0 (Rminus x y)).
  simpl. intros. apply sub_INR.
Defined.
Add Tify BinOp Op_nat_sub.

#[global]
Instance Op_nat_mul : BinOp Init.Nat.mul.
Proof.
  apply mkbop with (TBOp := Rmult).
  simpl. intros. rewrite mult_INR.
  reflexivity.
Defined.
Add Tify BinOp Op_nat_mul.

(* [nat -> R] : [INR] *)

#[global]
Instance Op_INR : UnOp INR.
Proof.
  apply mkuop with (TUOp := fun x => x).
  simpl. reflexivity.
Defined.
Add Tify UnOp Op_INR.

(** Specification for operators over R *)


Lemma  Rup_Spec :  forall x : R, isZ (Rup x) /\   Rup x > x /\ Rup x - x <= 1%R.
Proof.
intros.
split. unfold isZ, Rup. eexists. reflexivity.
unfold Rup. apply  (archimed x).
Qed.

Instance RupSpec : UnOpSpec Rup.
Proof. apply mkuspec with (UPred := (fun n r => isZ r /\ r > n /\ r - n <= 1)%R).
       intros.
       split. unfold isZ, Rup. eexists. reflexivity.
       unfold Rup. apply  (archimed x).
Defined.
Add Tify UnOpSpec RupSpec.

#[global]
Instance RabsSpec : UnOpSpec Rabs.
Proof. apply mkuspec with (UPred := (fun n r => (n >= 0 -> r = n) /\ (n < 0 -> r = - n)%R)).
       split.
       apply Rabs_right.
       apply Rabs_left.
Defined.
Add Tify UnOpSpec RabsSpec.

#[global]
Instance RminSpec : BinOpSpec Rmin.
Proof. apply mkbspec with (BPred := (fun x y r => (x <= y -> r = x) /\ (y <= x -> r = y)%R)).
       split.
       apply Rmin_left.
       apply Rmin_right.
Defined.
Add Tify BinOpSpec RminSpec.

#[global]
Instance RmaxSpec : BinOpSpec Rmax.
Proof. apply mkbspec with (BPred := (fun x y r => (y <= x -> r = x) /\ (x <= y -> r = y)%R)).
       split.
       apply Rmax_left.
       apply Rmax_right.
Defined.
Add Tify BinOpSpec RmaxSpec.


#[global]
Instance RinvSpec : UnOpSpec Rinv.
Proof. apply mkuspec with (UPred := (fun x r => (x <> 0 -> r * x = 1)%R)).
       intros. now apply Rinv_l.
Defined.
Add Tify UnOpSpec RinvSpec.

#[global]
Instance RdivSpec : BinOpSpec Rdiv.
Proof. apply mkbspec with (BPred := (fun x y r => (y <> 0 -> r * y = x)%R)).
       intros. unfold Rdiv. rewrite Rmult_assoc.
       rewrite  Rinv_l by assumption. ring.
Defined.
Add Tify BinOpSpec RdivSpec.


From Stdlib Require Import Lra Zfloor R_sqrt.

(** Support for [Zfloor] and [sqrt] *)

Definition Rfloor (x:R) := IZR (Zfloor x).

#[global]
Instance Op_Zfloor : UnOp Zfloor.
Proof.
apply mkuop with (TUOp := Rfloor).
unfold inj,Rfloor. simpl.
reflexivity.
Defined.
Add Tify UnOp Op_Zfloor.


#[global]
Instance Op_sqrt : UnOp sqrt.
Proof.
  apply mkuop with (TUOp := sqrt).
  simpl.   reflexivity.
Defined.
Add Tify UnOp Op_sqrt.



Lemma sqrtSpec_complete : forall x r,
(( 0 <= r /\ (0 <= x -> r * r = x) /\ (x <= 0 -> r = 0)) <-> r = sqrt x).
Proof.
  split;intros.
  - destruct H as (H1 & H2 & H3).
    assert (C: 0 <= x \/ x <= 0).
    { destruct (Rle_gt_dec 0 x).
      tauto. right.
      apply Rlt_le. now apply Rgt_lt.
    }
    destruct C as [C | C].
    rewrite <- H2 by assumption.
    rewrite sqrt_square;auto.
    rewrite sqrt_neg_0;auto.
  - subst.
    split.
    apply sqrt_pos.
    split.
    intro. apply sqrt_def;auto.
    apply sqrt_neg_0.
Qed.

#[global]
Instance sqrtSpec : UnOpSpec sqrt.
Proof. apply mkuspec with (UPred := (fun x r => ( 0 <= r /\ (0 <= x -> r * r = x) /\ (x <= 0 -> r = 0)%R))).
       intros.
       rewrite sqrtSpec_complete. reflexivity.
Defined.
Add Tify UnOpSpec sqrtSpec.

Lemma  Rfloor_Spec :  forall x : R, isZ (Rfloor x) /\ (Rfloor x <= x < Rfloor x + 1)%R.
Proof.
intros.
split. unfold isZ, Rfloor. eexists. reflexivity.
unfold Rfloor.
apply Zfloor_bound.
Qed.

Lemma Rfloor_complete:  forall x y : R, (isZ y /\ y <= x < y + 1) <-> y = Rfloor x.
Proof.
  intros;unfold Rfloor; split;intros.
  destruct H as (isZ & C).
  destruct isZ.
  subst.
  f_equal.
  symmetry.
  apply Zfloor_eq.
  auto.
  subst.
  apply Rfloor_Spec.
Qed.

#[global]
Instance RfloorSpec : UnOpSpec Rfloor.
Proof. apply mkuspec with (UPred := (fun n r => isZ r /\ r <= n < r+1)%R).
       apply Rfloor_Spec.
Defined.
Add Tify UnOpSpec RfloorSpec.
