Require Import Rbase Rify isZ Lra Zfloor.
Local Open Scope R_scope.

Unset Lra Cache.

Lemma up0 : up 0%R = 1%Z.
Proof. intros. lra. Qed.

Lemma up_succ r : up (r + 1)%R = (up r + 1)%Z.
Proof. intros. lra. Qed.

Lemma up_IZR z : up (IZR z) = (z + 1)%Z.
Proof.
  lra.
Qed.

Lemma up_shiftz r z : up (r + IZR z)%R = (up r + z)%Z.
Proof.
  lra.
Qed.

Lemma div_inv : forall y  x,
   1 = 1 + (y - x) / x ->
   (y - x) * / x = 0.
Proof. intros. lra. Qed.

Goal forall (x1 : R) (x2 : R) (x3 : R) (x4 : R) (x5 : R) (x6 : R)
(H0 : -x2 + x6 = R0)
(H1 : x6 + -x4 = R0)
(H2 : x2*x3 + -x1*x3 = R0)
(H3 : x4 + -x2*x5 = R0)
(H5 : x2*x3 + -x1*x3 > R0)
, False
.
Proof.
  intros.
  lra.
Qed.

Goal forall (x1 : R) (x2 : R) (x3 : R) (x4 : R)
(H0 : x4 >= 0)
(H1 : 1 + -x4 > 0)
(H2 : -x4 + x1 > 0)
(H3 : 1 + -x1 > 0)
(H4 : x2 + -x3 = 0)
(H5 : -x1 > 0)
, False
.
Proof.
  intros.
  lra.
Qed.


Goal forall (x1 : R) (x2 : R) (x3 : R) (x4 : R)
(H0 : x4 >= 0)
(H1 : 1 + -x4 > 0)
(H2 : -x4 + x1 > 0)
(H3 : 1 + -x1 > 0)
(H4 : x2 + -x3 = 0)
(H5 : -x1 > 0)
, False
.
Proof.
  intros.
  lra.
Qed.




Goal forall (x1 : R) (x2 : R) (x3 : R) (x4 : R) (x5 : R) (x6 : R)
(H0 : -x2 + x6 = R0)
(H1 : x6 + -x4 = R0)
(H2 : x2*x3 + -x1*x3 = R0)
(H3 : x4 + -x2*x5 = R0)
(H5 : x2*x3 + -x1*x3 > R0)
, False
.
Proof.
  lra.
Qed.

Lemma up_succ2 r n : Zfloor (r + IZR n) = (Zfloor r + n)%Z.
Proof.
  lra.
Qed.

Goal forall x1 x2 x3  x5 x6
    (H: -x2 > 0)
    (H0: x3 >= 0)
    (H1: -x1 + x5 + x6 = 0)
    (H2: x1 + -x5 + x6 = 0)
    (H4: -x1 > 0)
    (H6: x2 + -x3 = 0)
    (H7: 3 + 3*x1 = 0),
    False.
Proof.
  intros.
  lra.
Qed.


Lemma spurious_isZ : forall
    (x l X : R)
    (delta : R)
    (iZ1    : isZ x)
    (H13 :  - (X - l) <= 0)
    (iZ2    : isZ X)
    (H4 : l > 0)
    (iZ2    : isZ X)
    (H9 : delta / 2 <> 0)
    (iZ2    : isZ X)
    (H11 : 0 < delta / 2)
    (iZ1    : isZ x)
    (H10 : (X <= 0)),
    False.
Proof.
  intros.
  lra.
Qed.

Goal forall (k x:R) (P:Prop)
            (Hyp : 0 <= k < 1)
            (H2 : k < x < 1 /\ P)
            (H3 : k < x < 1),
  0 < x.
Proof.
  intros.
  lra.
Qed.


  Ltac cnf := match goal with
              | |- Tauto.cnf_checker  _ ?F _ = true =>
                  let f:= fresh "f" in
                  set(f:=F); compute in f; unfold f;clear f
              end.

  Ltac collect :=
    match goal with
      | |- context [ RMicromega.xcollect_isZ ?A ?B ?F] =>
        let f := fresh "f" in
        set (f:= RMicromega.xcollect_isZ A B F) ; compute in f ; unfold f; clear f
    end.


Goal forall (x y:R)
    (H : x <= y)
    (Hlt : x < y),
    y - x = 0 -> False.
Proof.
  intros.
  lra.
Qed.

Lemma two_x_1 : forall (x:R)
            (IZ : isZ x)
            (H : 2 * x + 1 =  0),
    False.
Proof.
  intros.
  lra.
Qed.

Goal forall x1 x2 x3 x4,
    isZ x1 ->
    isZ x2 ->
    isZ x3 ->
    isZ x4 ->
    - x1 + x2 - x3 + x4 >= 0 ->
    x1 - x2 + x3 - x4 + 1 > 0 ->
    - x1 + x2 - x3 + x4  >  0 ->
    False.
Proof.
  intros. lra.
Qed.



Goal forall z1 z2 z3, Zfloor (IZR z1 - IZR z2 + IZR z3)%R = (z1 - z2 + z3)%Z.
Proof.
  intros.
  rify.
  (** Now, some work over isZ *)
  lra.
Qed.

Goal forall (z : Z) x, IZR z <= x -> (z <= Zfloor x)%Z.
Proof.
  rify.
  lra.
Qed.



Goal forall (z : Z) x,  IZR z <= x < IZR z + 1 -> Zfloor x = z.
Proof.
  intros.
  rify.
  lra.
Qed.


Goal R1 + (R1 + R1) = 3.
Proof.
  intros.
  rify.
  reflexivity.
Qed.

Goal forall x,
    x * 3 = 1 ->
    False.
Proof.
  intros.
  Fail lra.
Abort.

Goal forall x,
    isZ x ->
    x * 3 = 1 ->
    False.
Proof.
  intros.
  lra.
Qed.



Require Import Rfunctions R_sqrt.

Goal forall e x
            (He : 0 < e)
            (ef := Rmin (e / (3 * (Rabs (x) + 1))) (sqrt (e / 3)) : R)
            (H : sqrt (e / 3) > 0)
            (H0 : 3 * (Rabs ( x) + 1) >= 1),
            0 < ef.
Proof.
  intros.
  nra.
Qed.


Goal forall x v,
            v * (3  * x) = 1 ->
            x >= 1 ->
            v = 1 / (3 * x).
Proof.
  intros.
  nra.
Qed.

