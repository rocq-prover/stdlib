From Stdlib Require Import BinInt.
From Stdlib.micromega Require Import ZifyClasses ZifyInst.

#[local] Open Scope Z_scope.

#[local]
Lemma Z_div_nonneg_nonneg a b : 0 <= a -> 0 <= b -> 0 <= a / b.
Proof.
  intros H; pose proof Z.div_pos a b H.
  case (Z.ltb_spec 0 b); auto.
  intros A B; rewrite (Z.le_antisymm _ _ A B).
  case a; cbv; congruence.
Qed.

#[local]
Lemma Z_mod_nonneg_nonneg a b : 0 <= a -> 0 <= b -> 0 <= a mod b.
Proof.
  case (Z.ltb_spec 0 b); intros.
  { apply Z.mod_pos_bound; trivial. }
  rewrite <-(Z.le_antisymm 0 b); trivial.
  case a in *; cbv in *; congruence.
Qed.

#[global]
Instance SatDiv : Saturate Z.div :=
  {|
    PArg1 := fun x => 0 <= x;
    PArg2 := fun y => 0 <= y;
    PRes  := fun _ _ r => 0 <= r;
    SatOk := Z_div_nonneg_nonneg
  |}.
Add Zify Saturate SatDiv.

#[global]
Instance SatMod : Saturate Z.modulo :=
  {|
    PArg1 := fun x => 0 <= x;
    PArg2 := fun y => 0 <= y;
    PRes  := fun _ _ r => 0 <= r;
    SatOk := Z_mod_nonneg_nonneg
  |}.
Add Zify Saturate SatMod.
