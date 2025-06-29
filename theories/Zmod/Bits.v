From Stdlib Require Import ZArith ZModOffset Zcong Lia.
From Stdlib Require Import Bool.Bool Lists.List Sorting.Permutation.
Import ListNotations.

From Stdlib Require Export Zmod.ZmodDef Zmod.ZmodBase.
#[local] Open Scope Z_scope.
#[local] Coercion ZmodDef.Zmod.to_Z : Zmod >-> Z.

#[local] Hint Extern 0 (?x <-> ?x) => reflexivity : core.

Module bits.
Import ZmodDef.Zmod ZmodBase.Zmod ZmodDef.bits.

(** ** Specialized versions of [Zmod] lemmas *)

Notation to_Z_0 := to_Z_0 (only parsing).
Notation unsigned_0 := unsigned_0 (only parsing).

Lemma unsigned_1 [n : Z] (Hm : 1 <= n) : @to_Z (2^n) one = 1.
Proof. apply to_Z_1_pos; pose (Z.pow_le_mono_r 2 1 n); lia. Qed.
Notation to_Z_1 := unsigned_1 (only parsing).

Lemma signed_1 [n] (Hm : 2 <= n) : @signed (2^n) one = 1.
Proof. apply signed_1. transitivity (2^2); try apply Z.pow_le_mono_r; lia. Qed.

Lemma unsigned_m1 n : @to_Z (2^n) (opp one) = Z.ones n.
Proof.
  assert (2^n = 0 \/ 2^n = 1 \/ 2 <= 2^n) as [H|[H|H]] by lia.
  1,2 : rewrite to_Z_m1_cases; repeat case Z.eqb_spec;
    rewrite ?Bool.orb_false_r, ?Bool.orb_false_r, ?Z.ones_equiv, ?H; cbn; lia.
  rewrite to_Z_m1_pos, Z.ones_equiv; trivial.
Qed.
Notation to_Z_m1 := unsigned_m1 (only parsing).

Lemma signed_m1 [n] (Hm : 1 <= n) : @signed (2^n) (opp one) = -1.
Proof.
  apply signed_m1.
  apply (Z.pow_le_mono_r 2 1 n); trivial; exact eq_refl.
Qed.

Lemma one_neq_zero [n] (Hm : 1 <= n) : one <> zero :> bits n.
Proof. apply one_neq_zero. pose proof (Z.pow_le_mono_r 2 1 n); lia. Qed.

Lemma unsigned_of_Z [n] (z : Z) : to_Z (of_Z n z) = z mod 2^n.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_of_Z := unsigned_of_Z.

Lemma unsigned_of_Z_small [n] z (H : 0 <= z < 2^n) : to_Z (bits.of_Z n z) = z.
Proof. apply to_Z_of_Z_small, H. Qed.
Notation to_Z_of_Z_small := unsigned_of_Z_small (only parsing).

Lemma unsigned_of_Z_mod0 [n] (Hn : n < 0) x : unsigned (of_Z n x) = x.
Proof. rewrite Z.pow_neg_r; trivial using to_Z_of_Z_mod0. Qed.

Lemma unsigned_width [n] (Hn : 0 <= n) : unsigned (bits.of_Z n n) = n.
Proof. apply to_Z_of_Z_small. pose proof Z.pow_gt_lin_r 2 n; lia. Qed.
Notation to_Z_width := unsigned_width.

Lemma unsigned_range [n] (x : bits n) (Hn : 0 <= n) : 0 <= x < 2^n.
Proof. apply Zmod.unsigned_pos_bound. lia. Qed.
Notation to_Z_range := unsigned_range.

Lemma signed_of_Z [n] z : signed (of_Z n z) = Z.smodulo z (2^n).
Proof. apply signed_of_Z. Qed.

Lemma signed_range [n] (x : bits n) (Hn : 0 <= n) : -2^n <= 2*signed x < 2^n.
Proof. apply signed_pos_bound; lia. Qed.

Lemma signed_range' [n] (x : bits n) (Hn : 1 <= n) : -2^(n-1) <= signed x < 2^(n-1).
Proof.
  pose proof signed_range x ltac:(lia).
  rewrite <-(Z.succ_pred n) in H at 1 4; rewrite Z.pow_succ_r in H; lia.
Qed.

Lemma unsigned_width0 (a : bits 0) : to_Z a = 0.
Proof. pose proof to_Z_range a ltac:(lia); lia. Qed.
Notation to_Z_width0 := unsigned_width0 (only parsing).

Lemma signed_width0 (a : bits 0) : signed a = 0.
Proof. pose proof Zmod.signed_pos_bound a; lia. Qed.

Lemma of_Z_mod [n] x : bits.of_Z n (x mod 2^n) = bits.of_Z n x.
Proof. apply to_Z_inj. rewrite ?to_Z_of_Z, ?Zmod_mod; lia. Qed.

Lemma of_Z_inj [n] x y : bits.of_Z n x = bits.of_Z n y <-> x mod 2^n = y mod 2^n.
Proof. rewrite of_Z_inj. trivial. Qed.

Lemma mod_to_Z [n] (x : bits n) : to_Z x mod 2^n = to_Z x.
Proof.
  case (Z.ltb_spec n 0) as []. { rewrite Z.pow_neg_r at 2 by trivial. apply Zmod_0_r. }
  rewrite Z.mod_small; auto using to_Z_range.
Qed.

Lemma mod_signed [n] (x : bits n) : signed x mod 2^n = unsigned x.
Proof. apply mod_signed. Qed.

Lemma smod_unsigned [n] (x : bits n) : Z.smodulo (unsigned x) (2^n) = signed x.
Proof. apply smod_unsigned. Qed.

Lemma smod_signed [n] (x : bits n) : Z.smodulo (signed x) (2^n) = signed x.
Proof. rewrite <-smod_unsigned, Z.smod_smod; trivial. Qed.

Lemma signed_small [n] (x : bits n) (H : 0 <= 2*x < 2^n) : signed x = unsigned x.
Proof. apply signed_small, H. Qed.

Lemma signed_large [n] (x : bits n) (H : 2^n <= 2*x) : signed x = x-2^n.
Proof. rewrite signed_large; lia. Qed.

Lemma signed_neg_iff [n] (x : bits n) (Hn : 0 <= n) :
  signed x < 0 <-> 2^n <= 2 * unsigned x.
Proof. rewrite signed_neg_iff. lia. Qed.

Lemma signed_small_iff [n] (x : bits n) (Hn : 0 <= n) :
  signed x = unsigned x <-> 2 * unsigned x < 2^n.
Proof. rewrite signed_small_iff; lia. Qed.

Lemma signed_nonneg_iff [n] (x : bits n) (Hn : 0 <= n) :
  0 <= signed x <-> 2 * unsigned x < 2^n.
Proof. rewrite signed_nonneg_iff. pose proof unsigned_range x. lia. Qed.

Lemma signed_pos_iff [n] (x : bits n) (Hn : 0 <= n) :
  0 < signed x <-> 0 < 2 * unsigned x < 2^n.
Proof. rewrite signed_pos_iff; lia. Qed.

Lemma unsigned_opp [n] (x : bits n) : to_Z (opp x) = (- to_Z x) mod 2^n.
Proof. rewrite to_Z_opp; trivial. Qed.
Notation to_Z_opp := unsigned_opp (only parsing).
Lemma signed_opp [n] (x : bits n) : signed (opp x) = Z.smodulo (-signed x) (2^n).
Proof. rewrite signed_opp; trivial. Qed.
Lemma unsigned_add [n] (x y : bits n) : to_Z (add x y) = (to_Z x + to_Z y) mod 2^n.
Proof. rewrite to_Z_add; trivial. Qed.
Notation to_Z_add := unsigned_add (only parsing).
Lemma signed_add [n] (x y : bits n) : signed (add x y) = Z.smodulo (signed x+signed y) (2^n).
Proof. rewrite signed_add; trivial. Qed.
Lemma unsigned_sub [n] (x y : bits n) : to_Z (sub x y) = (to_Z x - to_Z y) mod 2^n.
Proof. rewrite to_Z_sub; trivial. Qed.
Notation to_Z_sub := unsigned_sub (only parsing).
Lemma signed_sub [n] (x y : bits n) : signed (sub x y) = Z.smodulo (signed x-signed y) (2^n).
Proof. rewrite signed_sub; trivial. Qed.
Lemma unsigned_mul [n] (x y : bits n) : to_Z (mul x y) = (to_Z x * to_Z y) mod 2^n.
Proof. rewrite to_Z_mul; trivial. Qed.
Notation to_Z_mul := unsigned_mul (only parsing).
Lemma signed_mul [n] (x y : bits n) : signed (mul x y) = Z.smodulo (signed x*signed y) (2^n).
Proof. rewrite signed_mul; trivial. Qed.
Lemma unsigned_slu [n] (x : bits n) y : to_Z (slu x y) = Z.shiftl x y mod 2^n.
Proof. rewrite to_Z_slu; trivial. Qed.
Notation to_Z_slu := unsigned_slu (only parsing).
Lemma unsigned_srs [n] (x : bits n) y (Hy : 0 <= y) : to_Z (srs x y) = Z.shiftr (signed x) y mod 2^n.
Proof. rewrite unsigned_srs; trivial. Qed.
Notation to_Z_srs := unsigned_srs (only parsing).
Lemma signed_srs [n] (x : bits n) y (Hy : 0 <= y) : signed (srs x y) = Z.shiftr (signed x) y.
Proof. apply signed_srs; trivial. Qed.
Lemma of_Z_div [n] (x y : Z) (Hx : 0 <= x < 2^n) (Hy : 0 < y < 2^n) :
  bits.of_Z n (x / y) = udiv (of_Z _ x) (of_Z _ y).
Proof. apply of_Z_div_small; trivial. Qed.
Lemma of_Z_umod [n] (x y : Z) (Hx : 0 <= x < 2^n) (Hy : 0 <= y < 2^n) :
  bits.of_Z n (x mod y) = umod (of_Z _ x) (of_Z _ y).
Proof. rewrite of_Z_umod_small; trivial. Qed.
Lemma unsigned_mdiv [n] (x y : bits n) : to_Z (mdiv x y) = x * Z.invmod y (2^n) mod 2^n.
Proof. rewrite to_Z_mdiv; trivial. Qed.
Notation to_Z_mdiv := unsigned_mdiv (only parsing).
Lemma unsigned_pow_nonneg_r [n] (x : bits n) z (Hz : 0 <= z) : to_Z (pow x z) = x^z mod 2^n.
Proof. rewrite to_Z_pow_nonneg_r; trivial. Qed.
Notation to_Z_pow_nonneg := unsigned_pow_nonneg_r (only parsing).
Lemma signed_pow_nonneg_r [n] (x z : bits n) (Hz : 0 <= z) : signed (pow x z) = Z.smodulo (signed x ^ z) (2^n).
Proof. rewrite signed_pow_nonneg_r; trivial. Qed.
Notation signed_pow_nonneg := signed_pow_nonneg_r.

Lemma of_Z_nz [n] (x : bits n) (H : (x mod 2^n <> 0)%Z) : bits.of_Z n x <> zero.
Proof. apply of_Z_nz. trivial. Qed.

Lemma opp_overflow [n] (x : bits n) (Hn : 0 <= n) (Hx : signed x = -2^(n-1)) : opp x = x.
Proof.
  case (Z.eqb_spec n 0) as [->|]; [apply hprop_Zmod_1|].
  pose proof Z.pow_succ_r 2 (n-1) ltac:(lia) as H.
    replace (Z.succ (n-1)) with (n) in H by lia.
  apply opp_overflow; rewrite ?Hx, ?H; Z.to_euclidean_division_equations; lia.
Qed.

Lemma abs_overflow [n] (x : bits n) (Hn : 0 <= n) (Hx : signed x = -2^(n-1)) : abs x = x.
Proof.
  cbv [abs]. rewrite Hx.
  case (Z.ltb_spec (-2^(n-1)) 0) as []; auto using opp_overflow.
Qed.

Lemma squot_overflow [n] (x y : bits n) (Hn : 0 <= n) (Hx : signed x = -2^(n-1)) (Hy : signed y = -1) :
  squot x y = x.
Proof.
  case (Z.eqb_spec n 0) as [->|]; [apply hprop_Zmod_1|].
  pose proof Z.pow_succ_r 2 (n-1) ltac:(lia) as H;
    replace (Z.succ (n-1)) with n in H by lia.
  apply squot_overflow; Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_squot_small [n] (x y : bits n) (Hn : 0 <= n) (Hy : signed y <> 0) :
  ~ (signed x = -2^(n-1) /\ signed y = -1) ->
  signed (squot x y) = signed x ÷ signed y.
Proof.
  intros; case (Z.eqb_spec n 0) as [->|]. { rewrite !signed_width0; trivial. }
  apply signed_squot_small; try lia.
  intros (X&Y&_); apply H; clear H; split; trivial.
  rewrite X.
  pose proof Z.pow_succ_r 2 (n-1) ltac:(lia) as H;
    replace (Z.succ (n-1)) with n in H by lia;
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_srem [n] (x y : bits n) : signed (srem x y) = Z.smodulo (Z.rem (signed x) (signed y)) (2^n).
Proof. apply signed_of_Z. Qed.

Lemma signed_squot [n] (x y : bits n) : signed (squot x y) =
  Z.smodulo (if signed y =? 0 then -1 else signed x ÷ signed y) (2^n).
Proof. apply signed_of_Z. Qed.

Lemma signed_squot_nz [n] (x y : bits n) : signed y <> 0 -> signed (squot x y) = Z.smodulo (signed x ÷ signed y) (2^n).
Proof. intros; rewrite signed_squot_nz; trivial. Qed.

(** ** Bitwise operations *)

Lemma testbit_high [n] (x : bits n) i (Hn : 0 <= n) (Hi : (n <= i)%Z) : Z.testbit x i = false.
Proof. rewrite <-mod_to_Z, Z.mod_pow2_bits_high; lia. Qed.

Lemma testbit_m1 [n] i (Hn : 0 <= n) : Z.testbit (@Zmod.opp (2^n) one) i = (0 <=? i) && (i <? n).
Proof. rewrite to_Z_m1, Z.testbit_ones; lia. Qed.

Lemma testbit_sign [n] (x : bits n) (Hn : 0 <= n) : Z.testbit x (n-1) = (signed x <? 0).
Proof.
  intros; case (Z.eqb_spec n 0) as [->|]. { rewrite !signed_width0; trivial. }
  apply eq_true_iff_eq. rewrite Z.testbit_true, Z.ltb_lt, signed_neg_iff by lia.
  pose proof Z.pow_succ_r 2 (n-1) ltac:(lia) as R;
    replace (Z.succ (n-1)) with n in R by lia.
  pose proof to_Z_range x.
  rewrite Z.mod_small; Z.to_euclidean_division_equations; nia.
Qed.

Lemma testbit_signed_high [n] (x : bits n) i (Hn : 0 <= n) (Hi : (n <= i)%Z) :
  Z.testbit (signed x) i = (signed x <? 0).
Proof.
  intros; case (Z.eqb_spec n 0) as [->|]. { rewrite !signed_width0, ?Z.testbit_0_l; trivial. }
  case (Z.eq_dec (signed x) 0) as [->|]; [case i; trivial|].
  pose proof signed_range x.
  apply eq_true_iff_eq. rewrite <-Z.bits_iff_neg, Z.ltb_lt; trivial.
  apply Z.log2_lt_pow2; try lia.
  eapply Z.lt_le_trans with (m:=2^n); [|apply Z.pow_le_mono_r]; lia.
Qed.

Lemma unsigned_and [n] (x y : bits n) : unsigned (and x y) = Z.land x y.
Proof. apply unsigned_and_small. lia. Qed.

Lemma unsigned_or [n] (x y : bits n) : to_Z (or x y) = Z.lor x y.
Proof.
  cbv [or]; rewrite to_Z_of_Z.
  case (Z.ltb_spec n 0) as []. { rewrite Z.pow_neg_r at 3 by trivial; apply Zmod_0_r. }
  apply Z.bits_inj; intros i; destruct (Z.ltb_spec i n);
  repeat rewrite ?Z.lor_spec, ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?testbit_high by lia; trivial.
Qed.
Notation to_Z_or := unsigned_or (only parsing).

Lemma unsigned_xor [n] (x y : bits n) : to_Z (xor x y) = Z.lxor x y.
Proof.
  cbv [xor]; rewrite to_Z_of_Z.
  case (Z.ltb_spec n 0) as []. { rewrite Z.pow_neg_r at 3 by trivial; apply Zmod_0_r. }
  apply Z.bits_inj; intros i; destruct (Z.ltb_spec i n);
  repeat rewrite ?Z.lxor_spec, ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?testbit_high by lia; trivial.
Qed.
Notation to_Z_xor := unsigned_xor (only parsing).

Lemma xor_zero_iff [n] (x y : bits n) : xor x y = zero <-> x = y.
Proof.
  rewrite <-2to_Z_inj_iff, to_Z_0, to_Z_xor, Z.lxor_eq_0_iff; trivial.
Qed.

Lemma eqb_xor_zero [n] (x y : bits n) : eqb (xor x y) zero = eqb x y.
Proof.
  pose proof xor_zero_iff x y.
  destruct (eqb_spec (xor x y) zero), (eqb_spec x y); intuition congruence.
Qed.

Module Z.
Lemma ones_neg n (Hn : n < 0) : Z.ones n = -1.
Proof. rewrite Z.ones_equiv, Z.pow_neg_r; trivial. Qed.
End Z.

Lemma unsigned_not [n] (x : bits n) : to_Z (not x) = Z.ldiff (Z.ones n) x.
Proof.
  cbv [not]; rewrite to_Z_of_Z; apply Z.bits_inj'; intros i Hi.
  case (Z.leb_spec 0 n) as []; case (Z.ltb_spec i n) as [];
  repeat rewrite ?Z.pow_neg_r (* does not work...*) ,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.ldiff_spec,
    ?Z.ones_spec_high, ?Z.ones_spec_low, ?testbit_high,
    ?Z.ones_neg, ?Z.bits_m1
    by lia; trivial; try lia.
  rewrite (Z.pow_neg_r 2 n) at 2 by lia; rewrite Zmod_0_r.
  repeat rewrite ?Z.pow_neg_r (* does not work...*) ,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.ldiff_spec,
    ?Z.ones_spec_high, ?Z.ones_spec_low, ?testbit_high,
    ?Z.ones_neg, ?Z.bits_m1
    by lia; trivial; try lia.
Qed.
#[local] Notation to_Z_not := unsigned_not (only parsing).

Lemma unsigned_not' [n] (x : bits n) : to_Z (not x) = Z.ones n - x.
Proof.
  rewrite to_Z_not, Z.sub_nocarry_ldiff; trivial.
  apply Z.bits_inj'; intros i Hi;
  case (Z.leb_spec 0 n) as []; case (Z.ltb_spec i n) as [];
    repeat rewrite ?andb_false_r,
    ?Z.ldiff_spec, ?Z.testbit_ones, ?Z.testbit_0_l, ?testbit_high,
    ?(proj2 (Z.ltb_lt _ _)), ?(proj2 (Z.leb_le _ _)), ?Z.ones_neg, ?Z.bits_m1
    by lia; trivial.
Qed.
#[local] Notation to_Z_not' := unsigned_not' (only parsing).

Lemma of_Z_lnot [n] z : bits.of_Z n (Z.lnot z) = not (bits.of_Z n z).
Proof.
  apply Zmod.to_Z_inj. rewrite to_Z_not, to_Z_of_Z, to_Z_of_Z.
  apply Z.bits_inj'; intros i Hi;
  case (Z.leb_spec 0 n) as []; case (Z.ltb_spec i n) as [];
  repeat rewrite ?Z.ldiff_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.testbit_ones,
    ?(proj2 (Z.ltb_lt _ _)), (proj2 (Z.leb_le _ _)), ?(proj2 (Z.ltb_nlt _ _))
    by lia; trivial.
  rewrite (Z.pow_neg_r 2 n) at 2 by lia; rewrite Zmod_0_r.
  rewrite (Z.pow_neg_r 2 n) at 1 by lia; rewrite Zmod_0_r.
  repeat rewrite ?Z.pow_neg_r (* does not work...*) ,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.lnot_spec,
    ?Z.mod_pow2_bits_low, ?Z.mod_pow2_bits_high, ?Z.ldiff_spec,
    ?Z.ones_spec_high, ?Z.ones_spec_low, ?testbit_high,
    ?Z.ones_neg, ?Z.bits_m1
    by lia; trivial; try lia.
Qed.

Lemma not_not [n] (x : bits n) : not (not x) = x.
Proof. apply to_Z_inj. rewrite !to_Z_not'; lia. Qed.

Lemma not_0 n : not zero = opp one :> bits n.
Proof. apply Zmod.to_Z_inj; rewrite to_Z_not', to_Z_0, Z.sub_0_r, to_Z_m1; trivial. Qed.

Lemma not_m1 n : not (opp one) = zero :> bits n.
Proof. rewrite <-not_0, not_not; trivial. Qed.

(** ** Bitvector operations that vary the modulus *)

(** This lemma holds with [~(-n <= m < 0)] but no use case is known. *)

Lemma unsigned_app [n m] a b (Hn : 0 <= n) (Hm : 0 <= m) :
  to_Z (@app n m a b) = Z.lor a (Z.shiftl b n).
Proof.
  cbv [app]. rewrite to_Z_of_Z, Z.shiftl_mul_pow2; trivial.
  case (Z.ltb_spec (n+m) 0) as []. { rewrite (Z.pow_neg_r 2 (_+_)), Zmod_0_r; lia. }
  apply Z.mod_small.
  rewrite Z.pow_add_r by lia.
  (* lor <= add *)
  pose proof to_Z_range a; pose proof to_Z_range b.
  pose proof Z.lor_nonneg a (b * 2^n). pose proof Z.land_nonneg a (b * 2^n).
  pose proof Z.add_lor_land a (b * 2^n). nia.
Qed.
Notation to_Z_app := unsigned_app (only parsing).

Lemma unsigned_firstn [n m] a : to_Z (@firstn n m a) = a mod 2^n.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_firstn := unsigned_firstn (only parsing).

Lemma unsigned_skipn [n m] a (Hn : 0 <= n) : to_Z (@skipn n m a) = a/2^n.
Proof.
  cbv [skipn]; rewrite to_Z_of_Z, Z.shiftr_div_pow2 by trivial.
  case (Z.ltb_spec m n) as []. { rewrite (Z.pow_neg_r 2 (_-_)), Zmod_0_r; lia. }
  pose proof to_Z_range a ltac:(lia).
  apply Z.mod_small; split. { Z.div_mod_to_equations; nia. }
  apply Zdiv_lt_upper_bound; [lia|].
  rewrite <-Z.pow_add_r, Z.sub_add; lia.
Qed.
Notation to_Z_skipn := unsigned_skipn (only parsing).

Lemma unsigned_slice start pastend [w] (a : bits w) (H : 0 <= start <= pastend) :
  to_Z (slice start pastend a) = a/2^start mod 2^(pastend-start).
Proof. cbv [slice]. rewrite to_Z_firstn, to_Z_skipn; lia. Qed.
Notation to_Z_slice := unsigned_slice (only parsing).

(** This lemma holds with [~(-n <= m < 0)] but no use case is known. *)

Lemma firstn_app [n m] a b (Hn : 0 <= n) (Hm : 0 <= m) :
  firstn n (@app n m a b) = a.
Proof.
  apply to_Z_inj; rewrite to_Z_firstn, to_Z_app; try lia.
  symmetry. rewrite <-mod_to_Z at 1; symmetry.
  rewrite <-!Z.land_ones by lia.
  apply Z.bits_inj'; intros i Hi.
  repeat rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.shiftl_spec, ?Z.testbit_ones,
    ?Z.mod_pow2_bits_high, ?testbit_high_pow2, ?(Z.testbit_neg_r(*workaround*)b),
    ?Zle_imp_le_bool, ?Bool.andb_true_l by lia; trivial.
  destruct (Z.ltb_spec i n); try Btauto.btauto.
  rewrite (Z.testbit_neg_r b) by lia; Btauto.btauto.
Qed.

(** These lemmas hold with [~ (- n <= m < 0)] but no use case is known. *)

Lemma skipn_app_dep [n m] a b (Hn : 0 <= n) (Hm : 0 <= m) :
  existT _ _ (skipn n (@app n m a b)) = existT _ _ b.
Proof.
  pose proof to_Z_range a. eapply to_Z_inj_dep. { f_equal. lia. }
  rewrite to_Z_skipn, <-Z.shiftr_div_pow2, to_Z_app, Z.shiftr_lor, Z.shiftr_shiftl_l; try lia.
  erewrite Z.shiftr_div_pow2, Z.sub_diag, Z.shiftl_0_r, Z.div_small, Z.lor_0_l; lia.
Qed.

Lemma skipn_app_ex [n m] a b (Hn : 0 <= n) (Hm : 0 <= m) :
  exists pf, skipn n (@app n m a b) = eq_rect _ Zmod b _ pf.
Proof.
  pose proof skipn_app_dep a b ltac:(lia) ltac:(lia) as E.
  symmetry in E; inversion_sigma. exists E1.
  apply to_Z_inj. rewrite to_Z_eq_rect, <-E2, to_Z_eq_rect; trivial.
Qed.

Lemma skipn_app [n m] a b (Hn : 0 <= n) (Hm : 0 <= m) :
  skipn n (@app n m a b) = of_Z _ (to_Z (skipn n (@app n m a b))).
Proof.
  case (skipn_app_ex a b) as [?->]; trivial.
  apply to_Z_inj; rewrite to_Z_eq_rect, to_Z_of_Z.
  rewrite Z.add_simpl_l, mod_to_Z; trivial.
Qed.

Lemma app_assoc_dep [n m l] (a : bits n) (b : bits m) (c : bits l)
  (Hn : 0 <= n) (Hm : 0 <= m) (Hl : 0 <= l) :
  existT _ _ (app a (app b c)) = existT _ _ (app (app a b) c).
Proof.
  pose proof to_Z_range a. eapply to_Z_inj_dep. { f_equal. lia. }
  rewrite ?to_Z_app by lia.
  apply Z.bits_inj'; intros i Hi; case (Z.leb_spec 0 (i - n)) as [];
  repeat rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.shiftl_spec, ?Z.testbit_ones,
    ?Z.sub_add_distr, ?N2Z.inj_add, ?Bool.orb_assoc,
    (*workaround:*) ?(Z.testbit_neg_r (Z.shiftl c m)), ?(Z.testbit_neg_r c)
    by lia; trivial.
Qed.

Lemma app_assoc_ex [n m l] (a : bits n) (b : bits m) (c : bits l)
  (Hn : 0 <= n) (Hm : 0 <= m) (Hl : 0 <= l) :
  exists pf, app a (app b c) = eq_rect _ _ (app (app a b) c) _ pf.
Proof.
  pose proof app_assoc_dep a b c Hn Hm Hl as E; symmetry in E; inversion_sigma.
  exists E1. apply to_Z_inj; rewrite <-E2, !to_Z_eq_rect; trivial.
Qed.

Lemma app_assoc [n m l] (a : bits n) (b : bits m) (c : bits l)
  (Hn : 0 <= n) (Hm : 0 <= m) (Hl : 0 <= l) :
  app a (app b c) = of_Z _ (to_Z (app (app a b) c)).
Proof.
  ecase (app_assoc_ex a b c) as [?->]; trivial. apply to_Z_inj;
    rewrite !to_Z_eq_rect, !to_Z_of_Z, ?Z.add_assoc, mod_to_Z; trivial.
Qed.

End bits.
