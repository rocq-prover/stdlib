From Stdlib Require Import ZArith ZModOffset Zcong Lia Zdivisibility.
From Stdlib Require Import Bool.Bool Lists.List Lists.Finite Sorting.Permutation.
Import ListNotations.

From Stdlib Require Import Zmod.ZmodDef Zmod.ZmodBase Zmod.ZstarDef.
#[local] Open Scope Z_scope.
#[local] Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.
#[local] Coercion Zstar.to_Zmod : Zstar.Zstar >-> Zmod.Zmod.

#[local] Hint Extern 0 (?x <-> ?x) => reflexivity : core.

Module Zstar.
Import ZmodDef.Zmod ZmodBase.Zmod ZstarDef.Zstar.

(** ** Conversions to [Zmod] *)

Lemma coprime_to_Zmod [m] (a : Zstar m) : Z.coprime (to_Zmod a) m.
Proof.
  case a as [a H]; revert H.
  cbv [Zmod.to_Z Zmod.Private_to_Z to_Zmod Private_to_Z Zmod.of_small_Z].
  case ZmodDef.Zmod.small, (Z.eqb_spec (Z.gcd a m) 1); cbn; intuition trivial.
Qed.
Notation to_Zmod_range := coprime_to_Zmod (only parsing).

Lemma to_Zmod_inj [m] (x y : Zstar m) : to_Zmod x = to_Zmod y -> x = y.
Proof.
  cbv [to_Zmod Private_to_Z]; case x as [a Ha], y as [b Hb] in *;
    cbv [Zmod.to_Z Zmod.mul Zmod.of_Z Zmod.of_small_Z Zmod.Private_to_Z];
  pose proof andb_prop_elim _ _ Ha as [A _];
  pose proof andb_prop_elim _ _ Hb as [B _].
  intros H%(f_equal Zmod.to_Z); cbn in H.
  erewrite (Is_true_eq_true _ A), (Is_true_eq_true _ B) in H by eauto.
  subst; apply f_equal, Is_true_hprop.
Qed.

Lemma to_Zmod_inj_iff [m] (x y : Zstar m) : to_Zmod x = to_Zmod y <-> x = y.
Proof. split; auto using to_Zmod_inj; congruence. Qed.

Lemma to_Zmod_of_coprime_Zmod [m] (x : Zmod m) pf : to_Zmod (of_coprime_Zmod_dep x pf) = x.
Proof.
  apply to_Z_inj; pose proof Zmod.to_Z_range x.
  cbv [to_Zmod of_coprime_Zmod_dep Private_to_Z].
  apply to_Z_of_small_Z, Z.mod_id_iff, H.
Qed.

Lemma to_Zmod_of_Zmod' [m] (x : Zmod m) :
  to_Zmod (of_Zmod x) = if Z.eqb (Z.gcd x m) 1 then x else Zmod.one.
Proof. apply to_Zmod_of_coprime_Zmod. Qed.

Lemma to_Zmod_of_Zmod [m] (x : Zmod m) (H : Z.coprime x m) : to_Zmod (of_Zmod x) = x.
Proof. rewrite to_Zmod_of_Zmod'; case (Z.eqb_spec (Z.gcd x m) 1); congruence. Qed.

Lemma of_Zmod_to_Zmod [m] x : @of_Zmod m (to_Zmod x) = x.
Proof. pose (to_Zmod_range x). apply to_Zmod_inj. rewrite to_Zmod_of_Zmod; auto. Qed.

Lemma to_Zmod_1 m : @to_Zmod m one = Zmod.one.
Proof. apply to_Zmod_of_Zmod, Zmod.gcd_1_m. Qed.

Lemma of_Zmod_inj [m] (x y : Zmod m) :
  Z.coprime x m -> Z.coprime y m -> of_Zmod x = of_Zmod y -> x = y.
Proof. intros ? ? H%(f_equal to_Zmod); rewrite 2 to_Zmod_of_Zmod in H; trivial. Qed.

Lemma to_Zmod_0_iff [m] (a : Zstar m) : to_Zmod a = zero <-> Z.abs m = 1.
Proof.
  rewrite <-to_Z_0_iff.
  pose proof to_Z_range a.
  case (Z.eq_dec a 0) as [E|]; try lia.
  pose proof to_Zmod_range a as X; cbv [Z.coprime] in *.
  rewrite E, Z.gcd_0_l in X; lia.
Qed.

Lemma to_Zmod_nz [m] (a : Zstar m) (Hm : 2 <= m) : to_Zmod a <> zero.
Proof. rewrite to_Zmod_0_iff; lia. Qed.

Lemma eqb_spec [m] (x y : Zstar m) : BoolSpec (x = y) (x <> y) (eqb x y).
Proof.
  cbv [eqb]. case (eqb_spec x y);
    constructor; auto using to_Zmod_inj; congruence.
Qed.

Lemma eqb_eq [m] (x y : Zstar m) : eqb x y = true <-> x = y.
Proof. destruct (eqb_spec x y); intuition congruence. Qed.

Lemma eqb_refl [m] (x : Zstar m) : eqb x x = true.
Proof. apply eqb_eq; trivial. Qed.

Lemma hprop_Zstar_1 (a b : Zstar 1) : a = b.
Proof. apply to_Zmod_inj,  hprop_Zmod_1. Qed.

Lemma hprop_Zstar_2 (a b : Zstar 2) : a = b.
Proof.
  pose proof to_Zmod_range a; pose proof to_Zmod_range b. cbv [Z.coprime] in *.
  pose proof Zmod.to_Z_range a; pose proof Zmod.to_Z_range b.
  apply to_Zmod_inj, Zmod.to_Z_inj;
  assert (to_Z a = 0 \/ to_Z a = 1) as [Ha|Ha] by lia;
  assert (to_Z b = 0 \/ to_Z b = 1) as [Hb|Hb] by lia;
  rewrite ?Ha, ?Hb in *; cbn in *; intuition try lia.
Qed.

Lemma wlog_eq_Zstar_3_pos [m] (a b : Zstar m) (Hm : 0 < m) (k : 3 <= m -> a = b) : a = b.
Proof.
  destruct (Z.eq_dec 1 m) as [e|].
  { destruct e; auto using hprop_Zstar_1. }
  destruct (Z.eq_dec 2 m) as [e'|].
  { destruct e'; auto using hprop_Zstar_2. }
  { apply k; lia. }
Qed.

Lemma of_Zmod_1 m : @of_Zmod m Zmod.one = one.
Proof. reflexivity. Qed.

Lemma to_Z_0_iff [m] (a : Zstar m) : to_Z a = 0 <-> Z.abs m = 1.
Proof. rewrite unsigned_0_iff, to_Zmod_0_iff; trivial. Qed.

Lemma to_Z_nz_iff [m] (a : Zstar m) : to_Z a <> 0 <-> Z.abs m <> 1.
Proof. rewrite to_Z_0_iff; trivial. Qed.

Lemma to_Z_nz [m] (a : Zstar m) : Z.abs m <> 1 -> to_Z a <> 0.
Proof. apply to_Z_nz_iff. Qed.

(** ** [opp] *)

Lemma to_Zmod_opp [m] (a : Zstar m) : to_Zmod (opp a) = Zmod.opp a.
Proof.
  apply to_Zmod_of_Zmod; cbv [Z.coprime].
  rewrite to_Z_opp, Z.gcd_mod_l, Z.gcd_opp_l.
  apply coprime_to_Zmod.
Qed.

Lemma opp_opp [m] (a : Zstar m) : opp (opp a) = a.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_opp. apply Zmod.opp_opp. Qed.

Lemma opp_inj [m] (a b : Zstar m) : opp a = opp b -> a = b.
Proof. rewrite <-2to_Zmod_inj_iff, 2to_Zmod_opp. apply opp_inj. Qed.

Lemma opp_distinct_odd [m] (Hm : m mod 2 = 1) (Hm' : 3 <= m) a :
  a <> opp a :> Zstar m.
Proof.
  intro X; pose proof to_Z_range a; pose proof to_Z_nz a ltac:(lia).
  apply to_Zmod_inj_iff, Zmod.to_Z_inj_iff in X.
  rewrite ?to_Zmod_opp, Zmod.to_Z_opp, Z_mod_nz_opp_full in *;
    rewrite ?mod_to_Z in *; Z.div_mod_to_equations; nia.
Qed.

Lemma opp_1_neq_1 [m] (Hm : 3 <= Z.abs m) : opp one <> one :> Zstar m.
Proof.
  intros H%(f_equal to_Zmod); rewrite to_Zmod_opp, to_Zmod_1 in H.
  apply (Zmod.opp_1_neq_1 Hm); trivial.
Qed.

(** ** [abs] *)

Lemma to_Zmod_abs [m] (a : Zstar m) : to_Zmod (abs a) = Zmod.abs a.
Proof.
  cbv [abs Zmod.abs]; case Z.ltb; fold (opp a);
  rewrite ?to_Zmod_opp, ?to_Zmod_of_Zmod; auto using coprime_to_Zmod.
Qed.

Lemma abs_1 m : @abs m one = one.
Proof. apply to_Zmod_inj. rewrite to_Zmod_abs, ?to_Zmod_1, Zmod.abs_1; trivial. Qed.

Lemma abs_nonneg [m] (x : Zstar m) : 0 <= @signed m x -> abs x = x.
Proof. intros. apply to_Zmod_inj. rewrite to_Zmod_abs, abs_nonneg; trivial. Qed.

Lemma abs_neg [m] (x : Zstar m) : @signed m x < 0 -> abs x = opp x.
Proof. intros. apply to_Zmod_inj. rewrite to_Zmod_abs, to_Zmod_opp, abs_neg; trivial. Qed.

Lemma abs_pos [m] (x : Zstar m) : 0 < @signed m x -> abs x = x.
Proof. intros. apply to_Zmod_inj. rewrite to_Zmod_abs, abs_pos; trivial. Qed.

Lemma abs_opp [m] x : @abs m (opp x) = abs x.
Proof. apply to_Zmod_inj. rewrite ?to_Zmod_abs, ?to_Zmod_opp, abs_opp; trivial. Qed.

Lemma abs_abs [m] (x : Zstar m) : abs (abs x) = abs x.
Proof. apply to_Zmod_inj. rewrite ?to_Zmod_abs, abs_abs; trivial. Qed.

Lemma abs_overflow [m] (Hm : m mod 2 = 0)
  (x : Zstar m) (Hx : signed x = -m/2) : abs x = x.
Proof. apply to_Zmod_inj. rewrite ?to_Zmod_abs, abs_overflow; trivial. Qed.

(** ** [mul] *)

Lemma to_Zmod_mul [m] (a b : Zstar m) : @to_Zmod m (mul a b) = Zmod.mul a b.
Proof. cbv [mul]. rewrite to_Zmod_of_coprime_Zmod; trivial. Qed.

Lemma of_Zmod_mul [m] (a b : Zmod m) (Ha : Z.coprime a m) (Hb : Z.coprime b m) :
  @of_Zmod m (Zmod.mul a b) = mul (of_Zmod a) (of_Zmod b).
Proof.
  apply to_Zmod_inj; rewrite to_Zmod_mul, ?to_Zmod_of_Zmod; trivial.
  rewrite to_Z_mul, Z.coprime_mod_l_iff; apply Z.coprime_mul_l; auto.
Qed.

Lemma mul_assoc [m] a b c : @mul m a (mul b c) = mul (mul a b) c.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul. apply Zmod.mul_assoc. Qed.
Lemma mul_comm [m] a b : @mul m a b = mul b a.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul; apply Zmod.mul_comm. Qed.
Lemma mul_1_l [m] a : @mul m one a = a. Proof.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul, to_Zmod_1. apply Zmod.mul_1_l. Qed.
Lemma mul_1_r [m] a : @mul m a one = a. Proof. rewrite <-mul_comm; apply mul_1_l. Qed.
Lemma mul_m1_l [m] a : @mul m (opp one) a = opp a.
Proof. apply to_Zmod_inj. rewrite ?to_Zmod_mul, ?to_Zmod_opp, ?to_Zmod_1, Zmod.mul_m1_l; trivial. Qed.
Lemma mul_m1_r [m] a : @mul m a (opp one) = opp a. Proof. rewrite mul_comm; apply mul_m1_l. Qed.

Lemma mul_opp_l [m] (a b : Zstar m) : mul (opp a) b = opp (mul a b).
Proof. apply to_Zmod_inj; repeat rewrite ?to_Zmod_mul, ?to_Zmod_opp. apply Zmod.mul_opp_l. Qed.
Lemma mul_opp_r [m] (a b : Zstar m) : mul a (opp b) = opp (mul a b).
Proof. apply to_Zmod_inj; repeat rewrite ?to_Zmod_mul, ?to_Zmod_opp. apply Zmod.mul_opp_r. Qed.
Lemma mul_opp_opp [m] a b : @mul m (opp a) (opp b) = mul a b.
Proof. apply to_Zmod_inj; rewrite ?to_Zmod_mul, ?to_Zmod_opp. apply Zmod.mul_opp_opp. Qed.

Lemma abs_mul_abs_l [m] (x y : Zstar m) : abs (mul (abs x) y) = abs (mul x y).
Proof.
  intros. apply to_Zmod_inj.
  repeat rewrite ?to_Zmod_abs, ?to_Zmod_mul, ?abs_mul_abs_l; trivial.
Qed.

Lemma abs_mul_abs_r [m] (x y : Zstar m) : abs (mul x (abs y)) = abs (mul x y).
Proof.
  intros. apply to_Zmod_inj.
  repeat rewrite ?to_Zmod_abs, ?to_Zmod_mul, ?abs_mul_abs_r; trivial.
Qed.

Lemma abs_mul_abs_abs [m] (x y : Zstar m) : abs (mul (abs x) (abs y)) = abs (mul x y).
Proof.
  intros. apply to_Zmod_inj.
  repeat rewrite ?to_Zmod_abs, ?to_Zmod_mul, ?abs_mul_abs_abs; trivial.
Qed.

(** ** [inv] and [div] *)

Lemma to_Zmod_inv [m] x : to_Zmod (@inv m x) = Zmod.inv x.
Proof.
  cbv [inv]. rewrite to_Zmod_of_Zmod; trivial.
  rewrite to_Z_inv; apply Z.coprime_invmod, to_Zmod_range.
Qed.

Lemma not_of_Zmod_inv (m := 6) (x := Zmod.of_Z _ 4) : of_Zmod (@Zmod.inv m x) <> inv (of_Zmod x).
Proof. inversion 1. Qed.

Lemma to_Zmod_div [m] x y : to_Zmod (@div m x y) = Zmod.mdiv x y.
Proof. cbv [div]. rewrite to_Zmod_mul, to_Zmod_inv, mul_inv_r; trivial. Qed.

Lemma mul_inv_l [m] x y : mul (@inv m y) x = div x y.
Proof. apply to_Zmod_inj. cbv [div inv]. rewrite mul_comm; trivial. Qed.

Lemma mul_inv_r [m] x y : mul x (@inv m y) = div x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

Lemma div_same [m] (a : Zstar m) : div a a = one.
Proof.
  apply to_Zmod_inj, to_Z_inj. pose proof coprime_to_Zmod a.
  rewrite to_Zmod_div, to_Z_mdiv, Z.mul_comm, Z.invmod_coprime', to_Zmod_1, to_Z_1; trivial.
Qed.

Lemma div_mul_l [m] (a b c : Zstar m) : div (mul a b) c = mul a (div b c).
Proof. rewrite <-mul_inv_l, mul_comm, <-mul_assoc, mul_inv_r; trivial. Qed.

Lemma mul_inv_same_l [m] x : mul (@inv m x) x = one.
Proof. rewrite mul_inv_l, div_same; trivial. Qed.

Lemma mul_inv_same_r [m] x : mul x (@inv m x) = one.
Proof. rewrite mul_comm; apply mul_inv_same_l; trivial. Qed.

Lemma inv_inv [m] x : inv (@inv m x) = x.
Proof.
  rewrite <-mul_1_r, <-(mul_inv_same_l (inv x)), (mul_comm _ (inv x)); auto.
  rewrite mul_assoc, (mul_comm x), (mul_inv_same_l x), mul_1_l; auto.
Qed.

Lemma inv_1 m : @inv m one = one.
Proof.
  case (Z.eq_dec m 0) as [->|]; trivial.
  symmetry; rewrite <-mul_1_l, mul_inv_r, div_same; trivial.
Qed.

Lemma div_1_r [m] x : @div m x one = x.
Proof. cbv [div]; rewrite inv_1, mul_1_r; trivial. Qed.

Lemma mul_cancel_l [m] (a b c : Zstar m) (H : mul a b = mul a c) : b = c.
Proof.
  case (Z.eq_dec m 0) as [->|]; trivial.
  { apply (f_equal (fun x => unsigned (to_Zmod x))) in H.
    rewrite !to_Zmod_mul, !to_Z_mul, !Z.mod_0_r in H.
    eapply to_Zmod_inj, to_Z_inj, Z.mul_cancel_l; eauto.
    pose proof to_Zmod_range a; rewrite Z.coprime_0_r_iff in *; lia. }
  apply (f_equal (fun x => mul (inv a) x)) in H.
  rewrite !mul_assoc, !mul_inv_same_l, !mul_1_l in H; trivial.
Qed.

Lemma mul_cancel_l_iff [m] (a b c : Zstar m) : mul a b = mul a c <-> b = c.
Proof. split. apply mul_cancel_l. congruence. Qed.

Lemma mul_cancel_r [m] (a b c : Zstar m) (H : mul b a = mul c a) : b = c.
Proof. rewrite 2(mul_comm _ a) in H; apply mul_cancel_l in H; trivial. Qed.

Lemma mul_cancel_r_iff [m] (a b c : Zstar m) : mul b a = mul c a <-> b = c.
Proof. split. apply mul_cancel_r. congruence. Qed.

Lemma mul_div_r_same_r [m] (a b : Zstar m) : mul a (div b a) = b.
Proof.
  rewrite <-mul_inv_r, (mul_comm b), mul_assoc, mul_inv_same_r, mul_1_l; auto.
Qed.

Lemma inv_mul [m] (a b : Zstar m) : inv (mul a b) = mul (inv a) (inv b).
Proof.
  pose proof mul_inv_same_r (mul a b) as H.
  apply (f_equal (mul (inv b))), (f_equal (mul (inv a))) in H; trivial.
  rewrite mul_1_r in H; rewrite <-H; clear H; set (inv (mul _ _)) as x.
  rewrite !mul_assoc, (mul_comm (inv _)), <-(mul_assoc (inv _)).
  repeat rewrite ?mul_inv_same_l, ?mul_1_r, ?mul_1_l; trivial.
Qed.

Lemma div_div_r_same [m] (a b : Zstar m) : div a (div a b) = b.
Proof. rewrite <-!mul_inv_r, inv_mul, mul_assoc, inv_inv, mul_inv_same_r, mul_1_l; trivial. Qed.

Lemma inv_div [m] (x y : Zstar m) : inv (div x y) = div y x.
Proof. rewrite <-!mul_inv_l, inv_mul, inv_inv, mul_comm; trivial. Qed.

Lemma eq_inv_iff [m] (x y : Zstar m) : inv x = y <-> mul x y = one.
Proof. rewrite <-mul_cancel_l_iff, mul_inv_same_r; intuition congruence. Qed.

Lemma inv_opp [m] (x : Zstar m) : inv (opp x) = opp (inv x).
Proof. apply eq_inv_iff; rewrite ?mul_opp_opp, ?mul_inv_same_r; trivial. Qed.

(** ** [prod] *)

Lemma prod_nil m : prod [] = @one m.
Proof. reflexivity. Qed.

Lemma prod_cons [m] (x : Zstar m) xs : prod (x::xs) = mul x (prod xs).
Proof. reflexivity. Qed.

Lemma prod_singleton [m] (x : Zstar m) : prod [x] = x. Proof. apply mul_1_r. Qed.

Lemma prod_Permutation [m] (xs ys : list (Zstar m)) (H : Permutation xs ys) :
  prod xs = prod ys.
Proof.
  induction H; rewrite ?prod_nil, ?prod_cons, ?mul_assoc, ?(mul_comm x); congruence.
Qed.

Lemma prod_app [m] xs ys : prod (xs ++ ys) = mul (prod xs) (prod ys) :> Zstar m.
Proof.
  induction xs; rewrite ?app_nil_l, <-?app_comm_cons, ?prod_nil, ?prod_cons,
    ?mul_1_l,?IHxs, ?mul_assoc; trivial.
Qed.

Lemma prod_flat_map [A] [m] (f : A -> _) (xs : list A) :
  prod (flat_map f xs) = prod (map (fun x => prod (f x)) xs) :> Zstar m.
Proof. induction xs; cbn [flat_map]; rewrite ?prod_nil, ?prod_app, ?IHxs; eauto. Qed.

Lemma prod_concat [m] (xss : list (list (Zstar m))) :
  prod (concat xss) = prod ((map (fun xs => prod xs)) xss) :> Zstar m.
Proof. induction xss; cbn [concat]; rewrite ?prod_app, ?IHxss; trivial. Qed.

Lemma prod_rev [m] (xs : list (Zstar m)) : prod (rev xs) = prod xs.
Proof.
  induction xs; cbn [rev]; rewrite ?prod_app, ?prod_cons, ?prod_singleton,
    ?prod_nil, ?IHxs, ?mul_1_r, ?(mul_comm a); trivial.
Qed.

(** ** [pow] *)

Lemma to_Zmod_pow [m] (a : Zstar m) z : @to_Zmod m (pow a z) = Zmod.pow a z.
Proof.
  pose proof coprime_to_Zmod a; apply to_Zmod_of_Zmod.
  case (ltac:(lia):z = 0 \/ z < 0 \/ 0 < z) as [->|[]].
  { rewrite pow_0_r; apply Zmod.gcd_1_m. }
  all : rewrite ?to_Z_pow_nonneg_r, ?to_Z_pow_neg_r by lia.
  { apply Z.coprime_invmod, Z.coprime_pow_l; trivial; lia. }
  { apply Z.coprime_mod_l_iff, Z.coprime_pow_l; trivial; lia. }
Qed.

Lemma pow_0_r [m] x : @pow m x 0 = one.
Proof. trivial. Qed.

Lemma pow_1_r [m] x : @pow m x 1 = x.
Proof. apply to_Zmod_inj. rewrite to_Zmod_pow, pow_1_r; trivial. Qed.

Lemma pow_2_r [m] x : @pow m x 2 = mul x x.
Proof. apply to_Zmod_inj. rewrite to_Zmod_pow, to_Zmod_mul, pow_2_r; trivial. Qed.

Lemma pow_opp_2 [m] (x : Zstar m) : pow (opp x) 2 = pow x 2.
Proof. apply to_Zmod_inj. rewrite !to_Zmod_pow, to_Zmod_opp, pow_opp_2; trivial. Qed.

Lemma pow_abs_2 [m] (x : Zstar m) : pow (abs x) 2 = pow x 2.
Proof. apply to_Zmod_inj. rewrite !to_Zmod_pow, to_Zmod_abs, pow_abs_2; trivial. Qed.

Lemma eq_abs_iff m (x y : Zstar m) : abs x = abs y <-> (y = x \/ y = opp x).
Proof.
  rewrite <-!to_Zmod_inj_iff, !to_Zmod_abs, !to_Zmod_opp. apply Zmod.eq_abs_iff.
Qed.

Lemma Private_coprime_Zmodpow [m] (a : Zstar m) z (H : 0 <= z ) : Z.coprime (Zmod.pow a z) m.
Proof.
  pose proof coprime_to_Zmod a.
  rewrite Zmod.to_Z_pow_nonneg_r by lia.
  apply Z.coprime_mod_l_iff, Z.coprime_pow_l; trivial.
Qed.

Lemma pow_opp_r [m] a (z : Z) : @pow m a (-z) = inv (pow a z).
Proof.
  pose proof Private_coprime_Zmodpow a as G.
  case (Z.ltb_spec (-z) 0) as [].
  { cbv [pow inv]; f_equal.
    rewrite pow_neg, Z.opp_involutive, to_Zmod_of_Zmod; trivial. apply G; lia. }
  case (Z.eqb_spec z 0) as [->|].
  { cbv [pow inv]; f_equal.
    rewrite !Zmod.pow_0_r, to_Zmod_of_Zmod, Zmod.inv_1; trivial using Zmod.gcd_1_m. }
  { symmetry; rewrite <-inv_inv; symmetry; f_equal. cbv [pow inv]; f_equal.
    rewrite (pow_neg _ z), to_Zmod_of_Zmod; trivial; try lia. apply G; lia. }
Qed.

#[local] Lemma Private_pow_succ_r_nonneg [m] (x : Zstar m) z (H : 0 <= z) :
  pow x (Z.succ z) = mul x (pow x z).
Proof.
  cbv [pow]; apply to_Zmod_inj.
  rewrite to_Zmod_mul, Zmod.pow_succ_nonneg_r, !to_Zmod_of_Zmod; trivial;
    try apply Private_coprime_Zmodpow; trivial.
  rewrite to_Z_mul, Z.coprime_mod_l_iff.
  apply Z.coprime_mul_l, Private_coprime_Zmodpow; trivial using coprime_to_Zmod.
Qed.

Lemma pow_succ_r [m] (x : Zstar m) z : pow x (Z.succ z) = mul x (pow x z).
Proof.
  pose proof coprime_to_Zmod x.
  case (Z.leb_spec 0 z) as []; try auto using Private_pow_succ_r_nonneg.
  case (Z.eqb_spec z (-1)) as [->|?N].
  { cbv [pow]; cbn. fold (@inv m x).
    case (Z.eqb_spec m 0) as [->|].
    2: rewrite of_Zmod_1, mul_inv_r, div_same by lia; trivial.
    assert (to_Z x = 1 \/ to_Z x = -1) by (rewrite Z.coprime_0_r_iff in H; lia).
    assert (x = of_Zmod (of_Z 0 1) \/ x = of_Zmod (of_Z 0 (-1))) as [->| ->].
    { case H1; [left|right]; apply to_Zmod_inj, to_Z_inj; rewrite H2; trivial. }
    trivial.
    trivial. }
  remember (Z.pred (- z)) as n.
  assert (0 < n) by lia.
  assert (Z.succ z = -n) as -> by lia; assert (z = -Z.succ n)  as -> by lia.
  rewrite !pow_opp_r, Private_pow_succ_r_nonneg by lia.
  case (Z.eqb_spec m 0) as [->|].
  2:rewrite inv_mul, !mul_assoc, mul_inv_same_r, mul_1_l by lia; trivial.
  apply to_Zmod_inj, to_Z_inj.
  repeat rewrite ?to_Zmod_inv, ?to_Zmod_mul, ?to_Z_mul, ?to_Z_inv, ?to_Zmod_pow, ?to_Z_pow, ?Z.mod_0_r, ?Z.invmod_0_r.
  rewrite Z.sgn_mul.
  assert (to_Z x = 1 \/ to_Z x = -1) as [->| ->] by (rewrite Z.coprime_0_r_iff in H; lia).
  all : cbn [Z.sgn]; lia.
Qed.

Lemma pow_pred_r [m] (x : Zstar m) z : pow x (Z.pred z) = div (pow x z) x.
Proof.
  remember (Z.pred z) as n. assert (z = Z.succ n) as -> by lia.
  rewrite pow_succ_r, div_mul_l, mul_div_r_same_r; trivial; try lia.
Qed.

Lemma pow_1_l [m] z : @pow m one z = one.
Proof.
  induction z using Z.peano_ind;
    rewrite ?pow_0_r, ?pow_succ_r, ?pow_pred_r, ?IHz, ?mul_1_r, ?div_1_r; trivial.
Qed.

Lemma pow_add_r [m] (x : Zstar m) a b : pow x (a+b) = mul (pow x a) (pow x b).
Proof.
  induction a using Z.peano_ind;
    rewrite ?Z.add_0_l, ?Z.add_succ_l, ?Z.add_pred_l;
    rewrite ?pow_0_r, ?mul_1_l, ?pow_succ_r, ?pow_pred_r, ?IHa,
      <-?mul_inv_r, ?mul_assoc by lia; trivial.
  rewrite <-(mul_assoc _ (inv _)), (mul_comm (inv _)), mul_assoc; trivial.
Qed.

Lemma pow_sub_r [m] (x : Zstar m) a b  : pow x (a-b) = div (pow x a) (pow x b).
Proof. rewrite <-Z.add_opp_r, pow_add_r, pow_opp_r, mul_inv_r; trivial. Qed.

Lemma pow_mul_r [m] (x : Zstar m) a b : pow x (a*b) = pow (pow x a) b.
Proof.
  induction b using Z.peano_ind; rewrite ?Z.mul_0_r, ?Z.mul_succ_r, ?Z.mul_pred_r,
    ?pow_0_r, ?pow_1_l, ?pow_pred_r, ?pow_succ_r, ?pow_add_r, ?pow_sub_r, ?IHb;
    auto using mul_comm.
Qed.

Lemma pow_mul_l [m] (x y : Zstar m) n : pow (mul x y) n = mul (pow x n) (pow y n).
Proof.
  induction n using Z.peano_ind; rewrite ?pow_0_r, ?mul_1_l,
    ?pow_pred_r, ?pow_succ_r, ?pow_sub_r, ?IHn, <-?mul_inv_r, ?inv_mul;
    rewrite ?mul_assoc; f_equal; rewrite <-?mul_assoc; f_equal; auto using mul_comm.
Qed.

Lemma inv_pow_m1 m n : @inv m (pow (opp one) n) = pow (opp one) n.
Proof.
  induction n using Z.peano_ind;
  repeat rewrite ?pow_0_r, ?inv_1, ?pow_pred_r, ?pow_succ_r, <-?mul_inv_r,
    ?inv_mul, ?inv_opp, ?IHn by lia; trivial.
Qed.

Lemma prod_repeat [m] (a : Zstar m) n : prod (repeat a n) = pow a (Z.of_nat n).
Proof.
  induction n as [|n]; cbn [List.fold_right List.repeat]; rewrite ?prod_cons;
    rewrite ?pow_0_r, ?mul_1_r, ?Nat2Z.inj_succ, ?pow_succ_r, ?IHn by lia; trivial.
Qed.

Lemma prod_map_mul [m] (a : Zstar m) xs :
  prod (List.map (mul a) xs) = mul (pow a (Z.of_nat (length xs))) (prod xs).
Proof.
  induction xs as [|x xs]; cbn [List.fold_right List.map length]; rewrite ?prod_cons;
    rewrite ?pow_0_r, ?mul_1_r, ?Nat2Z.inj_succ, ?pow_succ_r, ?IHxs by lia; trivial.
  repeat rewrite ?mul_assoc, ?(mul_comm _ x); trivial.
Qed.

Lemma prod_pow [m] z xs : prod (map (fun x => pow x z) xs) = pow (prod xs) z :> Zstar m.
Proof.
  induction xs; intros; cbn [fold_right map]; rewrite ?prod_cons, ?pow_1_l, ?IHxs, ?pow_mul_l; trivial.
Qed.

Lemma prod_opp [m] xs : prod (map (@opp m) xs) = mul (pow (opp one) (Z.of_nat (length xs))) (prod xs).
Proof.
  induction xs; cbn [map length]; rewrite ?prod_nil, ?prod_cons;
    rewrite ?Nat2Z.inj_succ, ?pow_0_r, ?pow_succ_r, ?mul_1_l by lia; trivial.
  rewrite  ?mul_m1_l, ?IHxs, ?mul_opp_l, ?(mul_comm a), ?mul_assoc; trivial.
Qed.

(** ** [elements] *)

Lemma in_of_Zmod_filter [m] x (l : list (Zmod m)) :
  In x (map of_Zmod (filter (fun y : Zmod m => Z.gcd y m =? 1) l)) <-> In (to_Zmod x) l.
Proof.
  rewrite in_map_iff; setoid_rewrite filter_In; setoid_rewrite Z.eqb_eq.
  split. { intros (?&?&?&?); subst; rewrite to_Zmod_of_Zmod; auto. }
  exists x; repeat split; trivial; try apply of_Zmod_to_Zmod;
    try apply Zmod.in_elements; try apply coprime_to_Zmod.
Qed.

Lemma in_elements [m] (x : Zstar m) : In x (elements m).
Proof.
  cbv [elements]; pose proof coprime_to_Zmod x.
  case Z.eqb_spec; intros.
  { subst m; rewrite Z.coprime_0_r_iff in H; cbv [In].
    rewrite <-2to_Zmod_inj_iff, !to_Zmod_opp, !to_Zmod_1.
    rewrite <-2unsigned_inj_iff, !unsigned_opp, !unsigned_1_neg, Z.mod_0_r; lia. }
  rewrite in_of_Zmod_filter. auto using in_elements.
Qed.

Lemma NoDup_elements m : NoDup (elements m).
Proof.
  cbv [elements].
  case Z.eqb_spec; intros.
  { subst m. repeat constructor; cbv [In]; inversion_clear 1; trivial.
    eapply eqb_eq in H0; cbv in H0; discriminate. }
  eapply Injective_map_NoDup_in, List.NoDup_filter, NoDup_elements.
  intros ?????%of_Zmod_inj; rewrite filter_In, ?Z.eqb_eq in *; intuition idtac.
Qed.

Lemma to_Zmod_elements m : List.map to_Zmod (elements m) = Zmod.invertibles m.
Proof.
  cbv [elements Zmod.invertibles].
  case Z.eqb_spec; intros; subst; trivial.
  erewrite map_map, map_ext_in, map_id; trivial.
  intros x [_ Hx%Z.eqb_eq]%List.filter_In; rewrite to_Zmod_of_Zmod; trivial.
Qed.

Lemma elements_by_sign [m] (Hm : 2 <= Z.abs m) : elements m = positives m ++ negatives m.
Proof.
  cbv [elements negatives positives]; case Z.eqb_spec; [lia|intros].
  rewrite elements_by_sign by trivial; cbn [map filter List.app].
  rewrite to_Z_0, Z.gcd_0_l.
  case Z.eqb eqn:?; try lia.
  rewrite filter_app, map_app; trivial.
Qed.

Lemma in_positives [m] (x : Zstar m) (Hm : m <> 0) : In x (positives m) <-> 0 < signed x.
Proof. cbv [positives]; rewrite in_of_Zmod_filter, <-in_positives; trivial. Qed.

Lemma in_negatives [m] (x : Zstar m) (Hm : m <> 0) : In x (negatives m) <-> signed x < 0.
Proof. cbv [negatives]; rewrite in_of_Zmod_filter, <-in_negatives; trivial. Qed.

Lemma negatives_as_positives_odd m (Hm : m mod 2 = 1) :
  negatives m = map opp (rev (positives m)).
Proof.
  cbv [positives negatives]; rewrite negatives_as_positives_odd by trivial.
  rewrite <-map_rev, <-filter_rev; set (rev _).
  erewrite map_map, map_ext_in with (f:=fun x => opp _), <-(map_map Zmod.opp of_Zmod).
  2: { intros ? [? ?%Z.eqb_eq]%filter_In.
    apply to_Zmod_inj; rewrite to_Zmod_opp, !to_Zmod_of_Zmod; trivial.
    rewrite to_Z_opp, Z.coprime_mod_l_iff, Z.coprime_opp_l; trivial. }
  rewrite filter_map_swap; f_equal; f_equal; apply filter_ext.
  intros. rewrite to_Z_opp, Z.gcd_mod_l, Z.gcd_opp_l; trivial.
Qed.

Lemma NoDup_positives m : NoDup (positives m).
Proof.
  eapply Injective_map_NoDup_in, List.NoDup_filter, NoDup_positives.
  intros ?????%of_Zmod_inj; rewrite filter_In, ?Z.eqb_eq in *; intuition idtac.
Qed.

Lemma NoDup_negatives m : NoDup (negatives m).
Proof.
  eapply Injective_map_NoDup_in, List.NoDup_filter, NoDup_negatives.
  intros ?????%of_Zmod_inj; rewrite filter_In, ?Z.eqb_eq in *; intuition idtac.
Qed.

#[local] Hint Unfold Injective List.incl : core.
Lemma Permutation_mul_elements [m] (a : Zstar m) :
  Permutation (List.map (mul a) (elements m)) (elements m).
Proof.
  eauto 6 using Permutation.Permutation_map_same_l, Injective_map_NoDup, NoDup_elements, mul_cancel_l, in_elements, of_Zmod_inj.
Qed.

Theorem euler [m] (a : Zstar m) : pow a (Z.of_nat (length (elements m))) = one.
Proof.
  epose proof prod_map_mul a (elements m) as P.
  erewrite prod_Permutation in P by eapply Permutation_mul_elements.
  rewrite <-mul_1_l in P at 1. eapply mul_cancel_r, eq_sym in P; trivial.
Qed.

Lemma to_Zmod_elements_prime p (H : Z.prime p) :
  List.map to_Zmod (elements p) = List.tl (Zmod.elements p).
Proof. rewrite to_Zmod_elements, Zmod.invertibles_prime; trivial. Qed.

Lemma length_elements_prime p (H : Z.prime p) : length (elements p) = Z.to_nat (p-1).
Proof.
  erewrite <-List.length_map, to_Zmod_elements, Zmod.length_invertibles_prime; trivial.
Qed.

Lemma length_positives_length_negatives_odd m (Hm : m mod 2 = 1) :
  length (positives m) = length (negatives m).
Proof.
  rewrite negatives_as_positives_odd by trivial.
  rewrite ?length_map, ?filter_rev, ?length_rev; trivial.
Qed.

Lemma length_positives_odd [m] (H : m mod 2 = 1) :
  length (positives m) = (length (elements m) / 2)%nat.
Proof.
  case (Z.eqb_spec m 0) as [->|]; [inversion H|].
  case (Z.eqb_spec m 1) as [->|]; trivial.
  case (Z.eqb_spec m (-1)) as [->|]; trivial.
  erewrite elements_by_sign, length_app, <-length_positives_length_negatives_odd by lia; trivial.
  zify. rewrite Nat2Z.inj_div, Nat2Z.inj_add. zify; Z.to_euclidean_division_equations; lia.
Qed.

Lemma length_negatives_odd [m] (H : m mod 2 = 1) :
  length (negatives m) = (length (elements m) / 2)%nat.
Proof.
  rewrite <-length_positives_length_negatives_odd, length_positives_odd; trivial.
Qed.

#[local] Lemma Private_odd_prime (p : Z) : Z.prime p -> 3 <= p -> p mod 2 = 1.
Proof.
  case (Z.mod_pos_bound p 2 eq_refl) as [[]%Zle_lt_or_eq ?]; trivial.
  { intros _ _; eapply Z.le_antisymm;
    solve [ eapply Z.lt_pred_le + eapply Zlt_succ_le; trivial ]. }
  intros [? A] B.
  case (A 2). { split. exact eq_refl. eapply Z.le_succ_l; trivial. }
  apply Z.mod_divide. inversion 1. congruence.
Qed.

Lemma length_positives_prime [m] (H : Z.prime m) :
  length (positives m) = Z.to_nat ((m-1) / 2).
Proof.
  pose proof @Z.prime_ge_2 _ H.
  case (Z.eq_dec m 2) as [->|]; trivial.
  pose proof Private_odd_prime _ H ltac:(lia).
  pose proof length_positives_length_negatives_odd m.
  pose proof @length_elements_prime _ H as L.
  rewrite elements_by_sign, ?length_app in L by lia.
  zify; Z.to_euclidean_division_equations; nia.
Qed.

Lemma length_negatives_prime [m] (H : Z.prime m) :
  length (negatives m) = Z.to_nat (m / 2).
Proof.
  pose proof @Z.prime_ge_2 _ H.
  case (Z.eq_dec m 2) as [->|]; trivial.
  pose proof Private_odd_prime _ H ltac:(lia).
  rewrite <-length_positives_length_negatives_odd, length_positives_prime  by trivial.
  zify; Z.to_euclidean_division_equations; nia.
Qed.

Theorem fermat [m] (a : Zstar m) (H : Z.prime m) : pow a (Z.pred m) = one.
Proof.
  pose proof Z.prime_ge_2 _ H.
  erewrite <-euler, length_elements_prime; trivial; f_equal. lia.
Qed.

Theorem fermat_inv [m] (a : Zstar m) (H : Z.prime m) : pow a (m-2) = inv a.
Proof.
  pose proof Z.prime_ge_2 _ H.
  eapply mul_cancel_l; rewrite mul_inv_same_r.
  erewrite <-pow_succ_r, <-euler, ?length_elements_prime; f_equal; trivial; lia.
Qed.

Theorem euler_criterion_square [p] (Hp : Z.prime p)
  (a sqrt_a : Zstar p) (Ha : pow sqrt_a 2 = a) : pow a ((p-1)/2) = one.
Proof.
  pose proof Z.prime_ge_2 _ Hp.
  eapply wlog_eq_Zstar_3_pos; try lia; intro Hp'; pose proof Private_odd_prime _ Hp Hp'.
  rewrite pow_2_r in Ha.
  rewrite <-(fermat sqrt_a Hp), <-Ha, <-pow_2_r, <-pow_mul_r; f_equal.
  Z.to_euclidean_division_equations; nia.
Qed.

End Zstar.
