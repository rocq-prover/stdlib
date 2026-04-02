From Stdlib Require Import Tify.
From Stdlib Require Import ZifyClasses.
From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
(*  [zify] instances are already loaded *)

Goal forall (y:nat),
    (Z.of_nat y + 1)%Z = Z.of_nat (y + 1).
Proof.
  tify Z.
  change ((Z.of_nat y + 1)%Z = (Z.of_nat y + 1)%Z).
  reflexivity.
Qed.

Goal forall (y:nat),
    (Z.of_nat y + 1)%Z = Z.of_nat (y + 1).
Proof.
  tify R. (* This is no known way to map to R, default to Z *)
  change ((Z.of_nat y + 1)%Z = (Z.of_nat y + 1)%Z).
  reflexivity.
Qed.

(* Define instances for R *)
Lemma inj_IZR_iff : forall n m, n = m <-> (IZR n = IZR m)%R.
Proof.
  split.
  apply f_equal.
  apply eq_IZR.
Qed.

(* For the test, we lose the information that Z is discrete *)
#[global]
Instance Inj_Z_R : InjTyp Z R :=
  mkinj _ _ IZR (fun x =>  True) (fun _ => I).
Add Tify InjTyp Inj_Z_R.

#[global]
Instance Inj_nat_R : InjTyp nat R :=
  mkinj _ _ INR (fun x =>  0 <= x)%R pos_INR.
Add Tify InjTyp Inj_nat_R.

#[global]
Instance Inj_R_R : InjTyp R R :=
  mkinj _ _ (fun x=> x) (fun x =>  True) (fun _ => I).
Add Tify InjTyp Inj_R_R.

#[global]
Instance Op_eq_Z_R : BinRel (T:=R) (@eq Z) :=
  { TR := @eq R ; TRInj := inj_IZR_iff }.
Add Tify BinRel Op_eq_Z_R.

#[global]
Instance Op_plus_R : BinOp Z.add :=
  { TBOp := Rplus; TBOpInj := plus_IZR }.
Add Tify BinOp Op_plus_R.

#[global]
Instance Op_plus_nat_R : BinOp Nat.add :=
  { TBOp := Rplus; TBOpInj := plus_INR }.
Add Tify BinOp Op_plus_nat_R.

#[global]
Instance Op_Z_of_nat_R : UnOp (T1:= R) (T2:=R) Z.of_nat:=
  { TUOp x := x ; TUOpInj x := eq_sym (INR_IZR_INZ x) }.
Add Tify UnOp Op_Z_of_nat_R.

#[global]
Instance Op_S_R : UnOp (T1:= R) (T2:=R) S :=
  { TUOp := (fun x => Rplus x 1) ; TUOpInj := S_INR  }.
Add Tify UnOp Op_S_R.

#[global]
Instance Op_O : CstOp (T:= R)  O:=
  { TCst := 0%R ; TCstInj := INR_0 }.
Add Tify CstOp Op_O.

Goal forall (y:nat),
    (Z.of_nat y + 1)%Z = Z.of_nat (y + 1).
Proof.
  intros.
  Fail lra. (* Does not reason over Z *)
  Fail (tify Z; change ((INR y + 1)%R = (INR y + R1)%R)).
  tify R.
  change ((INR y + 1)%R = (INR y + R1)%R).
  lra.
Qed.
