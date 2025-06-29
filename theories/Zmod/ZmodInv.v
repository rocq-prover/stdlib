From Stdlib Require Import ZArith ZModOffset Zcong Lia Field_theory.
From Stdlib Require Import Bool.Bool Lists.List Lists.Finite Sorting.Permutation.
Import ListNotations.

From Stdlib Require Import Zmod.ZmodDef Zmod.ZstarDef Zmod.ZmodBase Zmod.ZstarBase.
#[local] Open Scope Z_scope.
#[local] Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
#[local] Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

#[local] Hint Extern 0 (?x <-> ?x) => reflexivity : core.

Module Zmod.
Import ZstarDef.Zstar ZstarBase.Zstar ZmodDef.Zmod ZmodBase.Zmod.

Lemma mdiv_same [m] (a : Zmod m) : mdiv a a = of_Z m (Z.gcd a m).
Proof.
  rewrite <-mul_inv_l. apply to_Z_inj. rewrite to_Z_mul, to_Z_inv,
    to_Z_of_Z, Z.invmod_ok; trivial.
Qed.

Lemma in_invertibles [m] (x : Zmod m) : List.In x (invertibles m) <-> Z.coprime x m.
Proof.
  rewrite <-Zstar.to_Zmod_elements, in_map_iff; split.
  { intros (?&?&?); subst. apply Zstar.coprime_to_Zmod. }
  { eexists; rewrite Zstar.to_Zmod_of_Zmod; auto using Zstar.in_elements. }
Qed.

Lemma NoDup_invertibles m : List.NoDup (invertibles m).
Proof.
  rewrite <-Zstar.to_Zmod_elements.
  eapply Injective_map_NoDup, Zstar.NoDup_elements.
  cbv [Injective]; auto using Zstar.to_Zmod_inj.
Qed.

Lemma mdiv_same_coprime [m] (a : Zmod m) (H : Z.gcd a m = 1) : mdiv a a = one.
Proof.
  case (Z.eqb_spec m 0) as [->|].
  { apply unsigned_inj; rewrite unsigned_mdiv; rewrite Z.gcd_0_r in *.
    assert (to_Z a = -1 \/ to_Z a = 1) as [->| ->] by lia; trivial. }
  rewrite mdiv_same, H; trivial. Qed.

Lemma mdiv_same_prime [m] (x : Zmod m) (Hm : Z.prime m) (H : x <> zero) : mdiv x x = one.
Proof.
  pose proof Z.prime_ge_2 _ Hm.
  apply mdiv_same_coprime. apply to_Z_nz in H. pose proof to_Z_range x.
  rewrite Z.gcd_comm; apply Z.coprime_prime_small; trivial; lia.
Qed.

Lemma mul_inv_same_l_coprime [m] (x : Zmod m) (H : Z.gcd x m = 1) :
  mul (inv x) x = one.
Proof.
  pose proof Zstar.mul_inv_same_l (Zstar.of_Zmod x) as E.
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite Zstar.to_Zmod_mul, Zstar.to_Zmod_inv, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1 in E by trivial; exact E.
Qed.

Lemma mul_inv_same_r_coprime [m] (x : Zmod m) (H : Z.gcd x m = 1) :
  mul x (inv x) = one.
Proof. rewrite mul_comm, mul_inv_same_l_coprime; trivial. Qed.

Lemma mul_inv_same_l_prime [m] (x : Zmod m) (Hm : Z.prime m) (H : x <> zero) :
  mul (inv x) x = one.
Proof. intros; rewrite ?mul_inv_l, ?mdiv_same_prime; trivial. Qed.

Lemma mul_inv_same_r_prime [m] (x : Zmod m) (Hm : Z.prime m) (H : x <> zero) :
  mul x (inv x) = one.
Proof. rewrite mul_comm, mul_inv_same_l_prime; trivial. Qed.

Lemma field_theory m (Hm : Z.prime m) :
  @field_theory (Zmod m) zero one add mul sub opp mdiv inv eq.
Proof.
  split; auto using ring_theory, Z.prime_ge_2, mul_inv_r, mul_inv_same_l_prime.
  apply one_neq_zero; pose proof Z.prime_ge_2 _ Hm; lia.
Qed.

Lemma inv_nz_prime [m] (x : Zmod m) (Hm : Z.prime m) (Hx : x <> zero) : inv x <> zero.
Proof.
  pose proof Z.prime_ge_2 _ Hm as Hm'.
  intro HX; exfalso; apply (@one_neq_zero m); [lia|].
  pose proof mul_inv_same_l_prime x Hm Hx as H; rewrite HX, mul_0_l in H; auto.
Qed.

Lemma inv_inv [m] (x : Zmod m) (H : Z.gcd x m = 1): inv (inv x) = x.
Proof.
  pose proof Zstar.inv_inv (Zstar.of_Zmod x) as E.
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite 2Zstar.to_Zmod_inv, Zstar.to_Zmod_of_Zmod in E by trivial; exact E.
Qed.

Lemma inv_inv_prime [m] (x : Zmod m) (Hm : Z.prime m): inv (inv x) = x.
Proof.
  case (eqb_spec x zero) as [|Hx]; subst.
  { apply to_Z_inj. rewrite !to_Z_inv, to_Z_0, Z.invmod_0_l; trivial. }
  pose proof to_Z_nz x ltac:(trivial); pose proof to_Z_range x.
  pose proof Z.prime_ge_2 _ Hm.
  apply inv_inv; rewrite Z.gcd_comm. apply Z.coprime_prime_small; trivial; lia.
Qed.

Lemma inv_1 m : @inv m one = one.
Proof.
  case (Z.eq_dec m 1); intros; subst; trivial.
  symmetry; rewrite <-mul_1_l, mul_inv_r, mdiv_same_coprime; trivial.
  apply Zmod.gcd_1_m.
Qed.

Lemma div_1_r [m] x : @mdiv m x one = x.
Proof. cbv [mdiv]. rewrite inv_1, mul_1_r; trivial. Qed.

Lemma mul_cancel_l_coprime [m] (a b c : Zmod m)
  (Ha : Z.gcd a m = 1) (H : mul a b = mul a c) : b = c.
Proof.
  apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l_coprime, !mul_1_l in H; trivial.
Qed.

Lemma mul_cancel_r_coprime [m] (a b c : Zmod m)
  (Ha : Z.gcd a m = 1) (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l_coprime in H; trivial. Qed.

Lemma mul_cancel_l_prime [m] (a b c : Zmod m) (Hm : Z.prime m) (Ha : a <> zero)
  (H : mul a b = mul a c) : b = c.
Proof.
  apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l_prime, !mul_1_l in H; trivial.
Qed.

Lemma mul_0_iff_prime [p] (Hp : Z.prime p) (a b : Zmod p) :
  mul a b = zero <-> a = zero \/ b = zero.
Proof.
  case (eqb_spec a zero) as [], (eqb_spec b zero) as [];
    split; (intros [|]||intros); subst; rewrite ?mul_0_l, ?mul_0_r in *; auto.
  case H. apply (f_equal (mul (inv b))) in H1; rewrite mul_0_r in H1.
  rewrite mul_comm, <-mul_assoc, mul_inv_same_r_prime, mul_1_r in H1; trivial.
Qed.

Lemma pow_succ_r_coprime [m] (x : Zmod m) z (H : Z.gcd x m = 1) : pow x (Z.succ z) = mul x (pow x z).
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_succ_r (Zstar.of_Zmod x) z) as E.
  rewrite Zstar.to_Zmod_mul, ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_pred_r_coprime [m] (x : Zmod m) z (H : Z.gcd x m = 1) : pow x (Z.pred z) = mdiv (pow x z) x.
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_pred_r (Zstar.of_Zmod x) z) as E.
  rewrite Zstar.to_Zmod_div, ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_add_r_coprime [m] (x : Zmod m) a b (H : Z.gcd x m = 1) : pow x (a + b) = mul (pow x a) (pow x b).
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_add_r (Zstar.of_Zmod x) a b) as E.
  rewrite Zstar.to_Zmod_mul, ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_mul_r_coprime [m] (x : Zmod m) a b (H : Z.gcd x m = 1) : pow x (a * b) = pow (pow x a) b.
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_mul_r (Zstar.of_Zmod x) a b) as E.
  rewrite ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_mul_l_coprime [m] (x y : Zmod m) z (Hx : Z.gcd x m = 1) (Hy : Z.gcd y m = 1) :
  pow (mul x y) z = mul (pow x z) (pow y z).
Proof.
  pose proof f_equal Zstar.to_Zmod (Zstar.pow_mul_l (Zstar.of_Zmod x) (Zstar.of_Zmod y) z) as E.
  rewrite ?Zstar.to_Zmod_mul, ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_mul, ?Zstar.to_Zmod_of_Zmod in E; trivial.
Qed.

Lemma pow_1_l [m] z : @pow m one z = one.
Proof.
  epose proof f_equal Zstar.to_Zmod (Zstar.pow_1_l (m:=m) z) as E.
  rewrite ?Zstar.to_Zmod_pow, ?Zstar.to_Zmod_1 in E; trivial.
Qed.

Lemma pow_mul_r_nonneg [m] (x : Zmod m) a b (Ha : 0 <= a) (Hb : 0 <= b) :
  pow x (a*b) = pow (pow x a) b.
Proof.
  generalize dependent b; generalize dependent a; refine (natlike_ind _ _ _).
  { intros. rewrite Z.mul_0_l, ?pow_0_r, pow_1_l; trivial. }
  intros a Ha IH b Hb; rewrite Z.mul_succ_l, Z.add_comm.
  rewrite pow_succ_r_nonneg, pow_add_r_nonneg, IH, pow_mul_l_nonneg; auto; nia.
Qed.

Lemma square_roots_opp_prime [p] (Hp : Z.prime p) (x y : Zmod p) :
  pow x 2 = pow y 2 <-> (x = y \/ x = opp y).
Proof.
  rewrite 2pow_2_r.
  intuition subst; rewrite ?mul_opp_opp; trivial; revert H.
  rewrite <-sub_eq_0_iff, ZmodBase.Zmod.square_roots_opp_prime_subproof.
  rewrite mul_0_iff_prime, 2sub_eq_0_iff ; intuition idtac.
Qed.

Lemma square_roots_1_prime [p] (Hp : Z.prime p) (x : Zmod p) :
  pow x 2 = one <-> (x = one \/ x = opp one).
Proof.
  rewrite <-(mul_1_l one) at 1. rewrite <-pow_2_r.
  rewrite square_roots_opp_prime; intuition idtac.
Qed.

Lemma mul_cancel_r_prime [m] (a b c : Zmod m) (Hm : Z.prime m) (Ha : a <> zero)
  (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l_prime in H; trivial. Qed.

Theorem fermat_nz [m] (a : Zmod m) (Ha : a <> zero) (H : Z.prime m) :
  pow a (Z.pred m) = one.
Proof.
  pose proof Z.prime_ge_2 _ H.
  rewrite <-to_Z_inj_iff, to_Z_0 in Ha; pose proof to_Z_range a as Ha'.
  pose proof Zstar.fermat (Zstar.of_Zmod a) H as G%(f_equal Zstar.to_Zmod).
  rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_of_Zmod, Zstar.to_Zmod_1 in G; trivial.
  symmetry; apply Z.coprime_prime_small; trivial; lia.
Qed.

Theorem fermat [m] (a : Zmod m) (H : Z.prime m) : pow a m = a.
Proof.
  pose proof Z.prime_ge_2 _ H.
  case (eqb_spec a zero); intros.
  { subst a. rewrite pow_0_l; trivial; lia. }
  { assert (m = Z.succ (Z.pred m)) as E by lia. rewrite E at 3.
    rewrite Zmod.pow_succ_nonneg_r, fermat_nz, mul_1_r; trivial; lia. }
Qed.

Theorem fermat_inv [m] (a : Zmod m) (Ha : a <> zero) (H : Z.prime m) :
  pow a (m-2) = inv a.
Proof.
  pose proof Z.prime_ge_2 _ H.
  pose proof Zstar.fermat_inv (Zstar.of_Zmod a) H as E.
  apply (f_equal Zstar.to_Zmod) in E.
  rewrite Zstar.to_Zmod_pow, Zstar.to_Zmod_inv, Zstar.to_Zmod_of_Zmod in *; trivial.
  pose proof to_Z_range a; apply to_Z_nz in Ha.
  symmetry; apply Z.coprime_prime_small; trivial; lia.
Qed.
End Zmod.

Module Z.
Import Znumtheory.

Theorem fermat_nz (m a : Z) (Hm : Z.prime m) (Ha : a mod m <> 0) :
  a^(m-1) mod m = 1.
Proof.
  pose proof Z.prime_ge_2 _ Hm.
  apply Zmod.of_Z_nz in Ha; pose (Zmod.fermat_nz (Zmod.of_Z m a) Ha Hm) as E.
  apply (f_equal Zmod.to_Z) in E.
  rewrite Zmod.to_Z_pow_nonneg_r, Zmod.to_Z_of_Z, Z.mod_pow_l, Zmod.to_Z_1_pos in E; try lia.
Qed.

Theorem fermat (m a : Z) (Hm : Z.prime m) : a^m mod m = a mod m.
Proof.
  pose proof Z.prime_ge_2 _ Hm.
  pose (Zmod.fermat (Zmod.of_Z m a) Hm) as E.
  apply (f_equal Zmod.to_Z) in E.
  rewrite Zmod.to_Z_pow_nonneg_r, Zmod.to_Z_of_Z, Z.mod_pow_l in E; lia.
Qed.
End Z.
