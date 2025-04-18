From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import ZifyClasses Tify.

(* Inject nat -> Z *)

Instance Inj_nat_Z : InjTyp nat Z.
Proof.
  apply (mkinj _ _ Z.of_nat (fun x => (0 <= x)%Z)).
  apply Nat2Z.is_nonneg.
Defined.
Add Tify InjTyp Inj_nat_Z.

Instance Op_nat_add_Z : BinOp Nat.add.
Proof.
  apply mkbop with (TBOp := Z.add).
  simpl. apply Nat2Z.inj_add.
Defined.
Add Tify BinOp Op_nat_add_Z.

Instance Op_eq_nat_eq_Z : BinRel (@eq nat).
Proof.
apply mkbrel with (TR := @eq Z).
simpl. split. congruence.
apply Nat2Z.inj.
Defined.
Add Tify BinRel Op_eq_nat_eq_Z.


(** Inject nat -> R *)

Definition isZ (r:R) := IZR (Zfloor r) = r.

Instance Inj_nat_R : InjTyp nat R.
Proof.
  apply (mkinj _ _ INR (fun r => isZ r /\ 0 <= r)%R).
  - intros. split. unfold isZ.
    rewrite INR_IZR_INZ.
    rewrite ZfloorZ. reflexivity.
    apply pos_INR.
Defined.
Add Tify InjTyp Inj_nat_R.

Instance Op_add_R : BinOp Nat.add.
Proof.
  apply mkbop with (TBOp := Rplus).
  simpl. intros. apply plus_INR.
Defined.
Add Tify BinOp Op_add_R.

Instance Op_eq_nat_eq_R : BinRel (@eq nat).
Proof.
apply mkbrel with (TR := @eq R).
simpl. split; intro. congruence.
apply INR_eq; auto.
Defined.
Add Tify BinRel Op_eq_nat_eq_R.


(* tify selects the right injection *)

Goal forall (x y:nat), (x + y = y + x)%nat.
Proof.
  intros.
  tify R.
  apply Rplus_comm.
Qed.

Goal forall (x y:nat), (x + y = y + x)%nat.
Proof.
  intros.
  tify Z.
  apply Zplus_comm.
Qed.

(* The R instances do not break lia. *)
From Stdlib Require Import Lia.
Goal forall (x y:nat), (x + y = y + x)%nat.
Proof.
  intros.
  lia.
Qed.
