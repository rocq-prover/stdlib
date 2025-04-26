From Stdlib Require Import BinNat BinInt Znat PreOmega Lia Ring ZArith_dec.
From Stdlib Require Import Wf_Z Zdiv Zdiv_facts Zdivisibility ZModOffset Zcong.
From Stdlib Require Import Bool.Bool Lists.List Sorting.Permutation.
From Stdlib Require Import Zmod.ZmodDef.
Import ListNotations.

Local Open Scope Zmod_scope.
Local Open Scope Z_scope.

Local Hint Extern 0 (?x <-> ?x) => reflexivity : core.

Module Zmod.
Export ZmodDef.Zmod.

(** ** Unsigned conversions to [Z] *)

Local Lemma small_iff z m :
  Bool.Is_true (ZmodDef.Zmod.small z m) <-> z mod m = z.
Proof.
  rewrite Z.mod_id_iff.
  cbv [ZmodDef.Zmod.small Is_true]. case m as [|m|m], z as [|z|z];
   cbn; try case Z.ltb eqn:?; lia.
Qed.

Lemma mod_unsigned {m} (x : Zmod m) : x mod m = x.
Proof. case x as [x H]; apply small_iff, H. Qed.
Notation mod_to_Z := mod_unsigned (only parsing).

Lemma unsigned_range {m} (x : Zmod m) : 0 <= x < m \/ m = 0 \/ m < x <= 0.
Proof. apply Z.mod_id_iff, mod_to_Z. Qed.
Notation to_Z_range := unsigned_range (only parsing).

Lemma unsigned_pos_bound {m} (x : Zmod m) : 0 < m -> 0 <= x < m.
Proof. rewrite <-mod_to_Z. apply Z.mod_pos_bound. Qed.
Notation to_Z_pos_bound := unsigned_pos_bound (only parsing).

Lemma unsigned_neg_bound {m} (x : Zmod m) : m < 0 -> m < x <= 0.
Proof. rewrite <-mod_to_Z. apply Z.mod_neg_bound. Qed.
Notation to_Z_neg_bound := unsigned_neg_bound (only parsing).

Lemma unsigned_inj m (x y : Zmod m) : to_Z x = to_Z y -> x = y.
Proof. cbv [to_Z Private_to_Z]; destruct x, y, 1; apply f_equal, Is_true_hprop. Defined.
Notation to_Z_inj := unsigned_inj (only parsing).

Lemma unsigned_inj_iff {m} (x y : Zmod m) : to_Z x = to_Z y <-> x = y.
Proof. split; try apply to_Z_inj; congruence. Qed.
Notation to_Z_inj_iff := unsigned_inj_iff (only parsing).

Lemma unsigned_of_small_Z {m} z (H : z mod m = z) : to_Z (of_small_Z m z) = z.
Proof.
  cbv [to_Z Private_to_Z of_small_Z].
  specialize (small_iff z m); case ZmodDef.Zmod.small; intuition idtac.
  inversion H0.
Qed.
Notation to_Z_of_small_Z := unsigned_of_small_Z (only parsing).

Lemma unsigned_of_Z {m} z : to_Z (of_Z m z) = z mod m.
Proof. apply to_Z_of_small_Z, Zmod_mod. Qed.
Notation to_Z_of_Z := unsigned_of_Z (only parsing).

Lemma of_small_Z_ok {m} z (H : z mod m = z) : of_small_Z m z = of_Z m z.
Proof. apply to_Z_inj. rewrite to_Z_of_small_Z, to_Z_of_Z; auto. Qed.

Lemma of_Z_unsigned {m} x : of_Z m (unsigned x) = x.
Proof. apply to_Z_inj. rewrite to_Z_of_Z, mod_to_Z; trivial. Qed.
Notation of_Z_to_Z := of_Z_unsigned (only parsing).

Lemma unsigned_of_Z_id_iff {m} n :
  to_Z (of_Z m n) = n <-> 0 <= n < m \/ m = 0 \/ m < n <= 0.
Proof. rewrite to_Z_of_Z; apply Z.mod_id_iff. Qed.
Notation to_Z_of_Z_id_iff := unsigned_of_Z_id_iff.

Lemma unsigned_of_Z_id {m} n (H : 0 <= n < m \/ m = 0 \/ m < n <= 0) :
  to_Z (of_Z m n) = n.
Proof. apply to_Z_of_Z_id_iff, H. Qed.
Notation to_Z_of_Z_id := unsigned_of_Z_id .

Lemma unsigned_of_Z_mod0 n : to_Z (of_Z 0 n) = n.
Proof. apply to_Z_of_Z_id; intuition idtac. Qed.
Notation  to_Z_of_Z_mod0 := unsigned_of_Z_mod0 (only parsing).

Lemma unsigned_of_Z_small {m} n (H : 0 <= n < m) : to_Z (of_Z m n) = n.
Proof. rewrite to_Z_of_Z, Z.mod_small; trivial. Qed.
Notation to_Z_of_Z_small := unsigned_of_Z_small.

Lemma of_Z_mod {m} x : of_Z m (x mod m) = of_Z m x.
Proof. apply to_Z_inj. rewrite ?to_Z_of_Z, ?Zmod_mod; trivial. Qed.

Lemma of_Z_mod_abs {m} x : of_Z m (x mod (Z.abs m)) = of_Z m x.
Proof. rewrite <-of_Z_mod, Z.mod_mod_abs_r, of_Z_mod; trivial. Qed.

Lemma of_Z_inj {m} x y : of_Z m x = of_Z m y <-> x mod m = y mod m.
Proof.
  split.
  { intros H%(f_equal to_Z). rewrite 2to_Z_of_Z in *; trivial. }
  { rewrite <-of_Z_mod. rewrite <-(of_Z_mod y). congruence. }
Qed.

Lemma of_Z_inj_abs' {m} x y : of_Z m x = of_Z m y <-> x mod (Z.abs m) = y mod (Z.abs m).
Proof. rewrite Z.eq_mod_abs, of_Z_inj; trivial. Qed.

Lemma of_Z_inj_abs {m} x y : of_Z m x = of_Z m y <-> (Z.abs m <> 1 -> x mod (Z.abs m) = y mod (Z.abs m)).
Proof.
  rewrite of_Z_inj_abs'.
  case (Z.eq_dec (Z.abs m) 1) as [->|]; rewrite ?Z.mod_1_r; intuition idtac.
Qed.

Lemma of_Z_inj_cases {m} x y : of_Z m x = of_Z m y <->
  ((m = 0 -> x = y) /\ let m' := Z.abs m in 2 <= m' -> x mod m' = y mod m').
Proof.
  rewrite of_Z_inj_abs.
  split.
  { split.
    { intros ->. rewrite !Zmod_0_r in H; apply H; inversion 1. }
    { intros. subst. specialize (H ltac:(lia)).
      rewrite ?Z.abs_eq in * by lia; trivial. } }
  { intros [A B] ?.
    case (Z.eq_dec m 0) as [->|].
    { rewrite A; trivial. }
    apply B; lia. }
Qed.

(** ** Signed conversions to [Z] *)

Lemma smod_unsigned {m} (x : Zmod m) : Z.smodulo (unsigned x) m = signed x.
Proof.
  pose proof to_Z_range x. cbv [signed Z.smodulo Z.omodulo] in *.
  case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
  rewrite ?(Z.mod_diveq 0), ?(Z.mod_diveq 1) by (Z.quot_rem_to_equations; lia);
    Z.quot_rem_to_equations; try lia.
Qed.

Lemma smod_signed {m} (x : Zmod m) : Z.smodulo (signed x) m = signed x.
Proof. rewrite <-smod_unsigned, Z.smod_smod; trivial. Qed.

Lemma signed_inj m (x y : Zmod m) : signed x = signed y -> x = y.
Proof.
  rewrite <-2 smod_unsigned; intros H%Z.mod_inj_smod; rewrite ?mod_to_Z in *.
  apply to_Z_inj, H.
Qed.

Lemma signed_inj_iff {m} (x y : Zmod m) : signed x = signed y <-> x = y.
Proof. split; try apply signed_inj; congruence. Qed.

Lemma mod_signed {m} (x : Zmod m) : signed x mod m = unsigned x.
Proof. rewrite <-smod_unsigned, Z.mod_smod, mod_to_Z; trivial. Qed.

Lemma signed_of_Z {m} z : signed (of_Z m z) = Z.smodulo z m.
Proof. rewrite <-smod_unsigned, to_Z_of_Z, Z.smod_mod; trivial. Qed.

Lemma signed_eq_unsigned_iff {m} x :
  @signed m x = unsigned x <-> 2*Z.abs x < Z.abs m \/ m = 0.
Proof. cbv [signed]; case Z.ltb_spec; lia. Qed.

Lemma signed_eq_unsigned {m} (x : Zmod m) :
  2*Z.abs x < Z.abs m \/ m = 0 -> signed x = unsigned x.
Proof. apply signed_eq_unsigned_iff. Qed.

Lemma signed_of_Z_mod0 n : signed (of_Z 0 n) = n.
Proof. rewrite signed_eq_unsigned, unsigned_of_Z_mod0; lia. Qed.

Lemma signed_of_Z_id_iff m z :
  signed (of_Z m z) = z <->
  - m <= 2 * z - Z.rem m 2 < m \/ m = 0 \/ m < 2 * z - Z.rem m 2 <= - m.
Proof. rewrite signed_of_Z, <-Z.smod_small_iff; trivial. Qed.

Lemma signed_of_Z_id m z :
  - m <= 2 * z - Z.rem m 2 < m \/ m = 0 \/ m < 2 * z - Z.rem m 2 <= - m ->
  signed (of_Z m z) = z.
Proof. apply signed_of_Z_id_iff. Qed.

Lemma signed_cases {m} (x : Zmod m) :
  signed x = unsigned x     /\ 2*Z.abs x < Z.abs m \/
  signed x = unsigned x - m /\ Z.abs m <= 2*Z.abs x.
Proof. cbv [signed]; case Z.ltb_spec; lia. Qed.

Lemma signed_of_Z_small {m} z (H : - m <= 2 * z - Z.rem m 2 < m) :
  signed (of_Z m z) = z.
Proof. rewrite signed_of_Z; apply Z.smod_small, H. Qed.

Lemma signed_of_Z_even_small {m} (Hm : m mod 2 = 0)
  z (H : - m <= 2 * z < m) : signed (of_Z m z) = z.
Proof.
  rewrite signed_of_Z, Z.smod_even_small;
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma of_Z_signed {m} x : of_Z m (signed x) = x.
Proof. apply signed_inj. rewrite signed_of_Z, smod_signed; trivial. Qed.

Lemma signed_range {m} (x : Zmod m) :
  ltac:(let t := type of (Z.smod_small_iff (signed x) m) in
  match eval cbv zeta in t with ?P <-> _ => exact P end).
Proof. apply Z.smod_small_iff, smod_signed. Qed.

Lemma signed_pos_bound {m} (x : Zmod m) (Hm : 0 < m) : -m <= 2*signed x < m.
Proof. rewrite <-smod_unsigned. pose proof Z.smod_pos_bound x m; lia. Qed.

Lemma signed_neg_bound {m} (x : Zmod m) (Hm : m < 0) : m < 2*signed x <= - m.
Proof. rewrite <-smod_unsigned. pose proof Z.smod_neg_bound x m; lia. Qed.

Lemma signed_small {m} (x : Zmod m) (H : 0 <= 2*x < m) : signed x = unsigned x.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
    intuition try lia.
Qed.

Lemma signed_large {m} (x : Zmod m) (H : 0 <= m <= 2*x) : signed x = x-m.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
    intuition try lia.
Qed.

Lemma unsigned_pos {m} (x : Zmod m) (Hm : 0 <= m) (H : 0 <= signed x) : unsigned x = signed x.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
    intuition try lia.
Qed.
Notation to_Z_pos := unsigned_pos (only parsing).

Lemma unsigned_neg {m} (x : Zmod m) (Hm : 0 <= m) (H : signed x < 0) : unsigned x = m + signed x.
Proof.
  pose proof to_Z_range x.
  cbv [signed] in *; case (Z.ltb_spec (Z.double (Z.abs x)) (Z.abs m)) as [];
    intuition try lia.
Qed.
Notation to_Z_neg := unsigned_neg (only parsing).

Lemma signed_neg_iff {m} (x : Zmod m) :
  signed x < 0 <-> 0 < m <= 2*x \/ m = 0 /\ x < 0 \/ m < 2*x < 0.
Proof. pose proof unsigned_range x; pose proof signed_cases x; lia. Qed.

Lemma signed_pos_iff {m} (x : Zmod m) :
  0 < signed x <-> 0 < 2*x < m \/ m = 0 /\ 0 < x \/ 2*x <= m < 0.
Proof. pose proof unsigned_range x; pose proof signed_cases x; lia. Qed.

Lemma signed_nonneg_iff {m} (x : Zmod m) :
  0 <= signed x <-> 0 <= 2*x < m \/ m = 0 /\ 0 <= x \/ (m < 0 /\ (2*x <= m \/ 0 = x)).
Proof. pose proof unsigned_range x; pose proof signed_cases x; lia. Qed.

Lemma signed_small_iff {m} (x : Zmod m) (Hm : 0 < m) :
  signed x = x <-> 2*x < m.
Proof. pose proof to_Z_range x; rewrite signed_eq_unsigned_iff; lia. Qed.

(** ** Constants *)

Lemma unsigned_0 m : @to_Z m zero = 0. Proof. apply to_Z_of_Z. Qed.
Notation to_Z_0 := unsigned_0 (only parsing).

Lemma unsigned_0_iff {m} x : @to_Z m x = 0 <-> x = zero.
Proof. rewrite <-to_Z_inj_iff, to_Z_0; trivial. Qed.
Notation to_Z_0_iff := unsigned_0_iff (only parsing).

Lemma of_Z_0 {m} : of_Z m 0 = zero. Proof. apply of_small_Z_ok, Zmod_0_l. Qed.

Lemma signed_0 m : @signed m zero = 0.
Proof. rewrite <-smod_unsigned, to_Z_0, Z.smod_0_l; trivial. Qed.

Lemma signed_0_iff {m} x : @signed m x = 0 <-> x = zero.
Proof. rewrite <-signed_inj_iff, signed_0; trivial. Qed.

Lemma of_Z_1 {m} : of_Z m 1 = one. Proof. apply to_Z_inj. trivial. Qed.

Lemma unsigned_1 {m} : @to_Z m one = 1 mod m.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_1 := unsigned_1 (only parsing).

Lemma unsigned_1_pos {m} (Hm : 2 <= m) : @to_Z m one = 1.
Proof. cbv [one]; rewrite to_Z_of_Z_small; lia. Qed.
Notation to_Z_1_pos := unsigned_1_pos (only parsing).

Lemma unsigned_1_1 : @to_Z 1 one = 0. trivial. Qed.
Notation to_Z_1_1 := unsigned_1_1 (only parsing).

Lemma unsigned_1_neg {m} (Hm : m <= 0) : @to_Z m one = m+1.
Proof. cbv [one]; rewrite to_Z_of_Z, (Z.mod_diveq (-1)); try lia. Qed.
Notation to_Z_1_neg := unsigned_1_neg (only parsing).

Lemma unsigned_1_cases {m} : @to_Z m one =
  if 2 <=? m then 1 else if m =? 1 then 0 else m+1.
Proof.
  case (Z.leb_spec 2 m); auto using unsigned_1_pos.
  case (Z.eqb_spec m 1) as [->|]; auto using unsigned_1_pos.
  intros; rewrite unsigned_1_neg; lia.
Qed.
Notation to_Z_1_cases := unsigned_1_cases (only parsing).

Lemma gcd_1_m {m} : Z.coprime (@one m) m.
Proof. cbv [one]; rewrite Zmod.to_Z_of_Z. apply Z.coprime_mod_l_iff, Z.coprime_1_l. Qed.

Lemma signed_1 {m} (Hm : 3 <= m) : @signed m one = 1.
Proof.
  cbv [one]; rewrite signed_of_Z, Z.smod_small;
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_1_1 : @signed 1 one = 0. Proof. trivial. Qed.

Lemma signed_1_2 : @signed 2 one = -1. Proof. trivial. Qed.

Lemma unsigned_nz {m} (x : Zmod m) (H : x <> zero) : to_Z x <> 0.
Proof. intros X; apply H, to_Z_inj. rewrite to_Z_0; trivial. Qed.
Notation to_Z_nz := unsigned_nz (only parsing).

Lemma one_eq_zero_mod_1 : @one 1 = zero. Proof. trivial. Qed.

Lemma one_eq_zero_iff {m} : one = zero :> Zmod m <-> Z.abs m = 1.
Proof.
  cbv [one zero]; rewrite <-unsigned_inj_iff, !unsigned_of_Z.
  split; [|Z.to_euclidean_division_equations; lia]; intros H.
  rewrite ?Zmod_0_l in H; apply Z.mod_divide, Z.divide_1_r_abs in H;
    Z.to_euclidean_division_equations; lia.
Qed.

Lemma one_neq_zero {m} (Hm : 2 <= Z.abs m) : one <> zero :> Zmod m.
Proof. rewrite one_eq_zero_iff; lia. Qed.

Lemma of_Z_nz {m} x (H : x mod m <> 0) : of_Z m x <> zero.
Proof.
  intro Hx. apply (f_equal to_Z) in Hx. rewrite to_Z_of_Z, to_Z_0 in Hx; contradiction.
Qed.

Lemma hprop_Zmod_1 (a b : Zmod 1) : a = b.
Proof.
  pose proof to_Z_range a; pose proof to_Z_range b; apply to_Z_inj; lia.
Qed.

Lemma hprop_Zmod_m1 (a b : Zmod (-1)) : a = b.
Proof.
  pose proof to_Z_range a; pose proof to_Z_range b; apply to_Z_inj; lia.
Qed.

Lemma unsigned_Zmod1 (a : Zmod 1) : to_Z a = 0.
Proof. pose proof to_Z_range a; lia. Qed.
Notation to_Z_Zmod1 := unsigned_Zmod1 (only parsing).

Lemma unsigned_Zmodm1 (a : Zmod (-1)) : to_Z a = 0.
Proof. pose proof to_Z_range a; lia. Qed.
Notation to_Z_Zmodm1 := unsigned_Zmodm1 (only parsing).

Lemma signed_Zmod1 (a : Zmod 1) : signed a = 0.
Proof. pose proof signed_pos_bound a; lia. Qed.

Lemma signed_Zmodm1 (a : Zmod (-1)) : signed a = 0.
Proof. pose proof signed_neg_bound a; lia. Qed.

Lemma wlog_eq_Zmod_2_pos {m} (a b : Zmod m) (Hm : 0 < m) (k : 2 <= m -> a = b) : a = b.
Proof.
  destruct (Z.eq_dec 1 m) as [e|ne].
  { destruct e; auto using hprop_Zmod_1. }
  { apply k; lia. }
Qed.

Lemma wlog_eq_Zmod_2_neg {m} (a b : Zmod m) (Hm : m < 0) (k : m <= -2 -> a = b) : a = b.
Proof.
  destruct (Z.eq_dec (-1) m) as [e|ne].
  { destruct e; auto using hprop_Zmod_m1. }
  { apply k; lia. }
Qed.

Lemma wlog_eq_Zmod_2_abs {m} (a b : Zmod m) (k : m = 0 \/ 2 <= Z.abs m -> a = b) : a = b.
Proof.
  destruct (Z.eq_dec m 0) as [z|nz]; [apply k, or_introl, z|].
  destruct (Z.ltb_spec 0 m); [apply wlog_eq_Zmod_2_pos|apply wlog_eq_Zmod_2_neg];
    intros; try apply k; lia.
Qed.

(** ** Ring operations *)

Lemma unsigned_add {m} (x y : Zmod m) : to_Z (x + y) = (to_Z x + to_Z y) mod m.
Proof.
  pose proof to_Z_range x; pose proof to_Z_range y. cbv [add].
  rewrite of_small_Z_ok, to_Z_of_Z by (case Z.ltb eqn:?; rewrite Z.mod_id_iff; lia).
  case (Z.ltb_spec (Z.abs (x + y)) (Z.abs m)) as [?|?]; trivial.
  rewrite ?(Z.mod_diveq 0), ?(Z.mod_diveq 1) by lia; lia.
Qed.
Notation to_Z_add := unsigned_add (only parsing).

Lemma eqb_spec {m} (x y : Zmod m) : BoolSpec (x = y) (x <> y) (eqb x y).
Proof.
  cbv [eqb]. case (Z.eqb_spec (to_Z x) (to_Z y));
    constructor; auto using to_Z_inj; congruence.
Qed.

Lemma eqb_eq {m} (x y : Zmod m) : eqb x y = true <-> x = y.
Proof. destruct (eqb_spec x y); intuition congruence. Qed.

Lemma eqb_refl {m} (x : Zmod m) : eqb x x = true.
Proof. apply eqb_eq; trivial. Qed.

Lemma signed_add {m} x y : signed (@add m x y) = Z.smodulo (signed x+signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_add, Z.smod_mod, Z.smod_idemp_add; trivial. Qed.

Lemma of_Z_add {m} (x y : Z) : of_Z m (Z.add x y) = add (of_Z m x) (of_Z m y).
Proof.
  apply to_Z_inj.
  rewrite to_Z_add, ?to_Z_of_Z, ?Zplus_mod_idemp_r, ?Zplus_mod_idemp_l; auto.
Qed.

Lemma unsigned_sub {m} (x y : Zmod m) : to_Z (x - y) = (to_Z x - to_Z y) mod m.
Proof.
  pose proof to_Z_range x; pose proof to_Z_range y. cbv [sub].
  rewrite of_small_Z_ok, to_Z_of_Z by (case Z.eqb eqn:?; rewrite Z.mod_id_iff; lia).
  case Z.eqb eqn:?; rewrite ?(Z.mod_diveq 0), ?(Z.mod_diveq (-1)) by lia; lia.
Qed.
Notation to_Z_sub := unsigned_sub (only parsing).

Lemma signed_sub {m} x y : signed (@sub m x y) = Z.smodulo (signed x-signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_sub, Z.smod_mod, Z.smod_idemp_sub; trivial. Qed.

Lemma of_Z_sub {m} (x y : Z) : of_Z m (Z.sub x y) = sub (of_Z m x) (of_Z m y).
Proof.
  apply to_Z_inj.
  rewrite to_Z_sub, ?to_Z_of_Z, ?Zminus_mod_idemp_r, ?Zminus_mod_idemp_l; auto.
Qed.

Lemma unsigned_opp {m} (x : Zmod m) : to_Z (opp x) = (- to_Z x) mod m.
Proof. cbv [opp]. rewrite to_Z_sub, to_Z_0, Z.sub_0_l; trivial. Qed.
Notation to_Z_opp := unsigned_opp (only parsing).

Lemma signed_opp {m} x : signed (@opp m x) = Z.smodulo (-signed x) m.
Proof. rewrite <-!smod_unsigned, to_Z_opp, Z.smod_mod, Z.smod_idemp_opp; trivial. Qed.

Lemma unsigned_m1 {m : Z} : @to_Z m (opp one) = -1 mod m.
Proof. rewrite to_Z_opp, to_Z_1. apply (Z.mod_opp_mod_opp (-1)). Qed.

Lemma unsigned_m1_pos {m : Z} (H : 2 <= m) : @to_Z m (opp one) = m-1.
Proof. rewrite to_Z_opp, Z_mod_nz_opp_full; rewrite mod_to_Z, ?to_Z_1_pos; lia. Qed.
Notation to_Z_m1_pos := unsigned_m1_pos (only parsing).

Lemma unsigned_m1_1 : @to_Z 1 (opp one) = 0. Proof. trivial. Qed.
Notation to_Z_m1_1 := unsigned_m1_1 (only parsing).

Lemma unsigned_m1_m1 : @to_Z (-1) (opp one) = 0. Proof. trivial. Qed.
Notation to_Z_m1_m1 := unsigned_m1_m1 (only parsing).

Lemma unsigned_m1_neg {m : Z} (H : m <= -2) : @to_Z m (opp one) = -1.
Proof. rewrite to_Z_opp, to_Z_1_neg, (Z.mod_diveq (-1)); lia. Qed.
Notation to_Z_m1_neg := unsigned_m1_neg (only parsing).

Lemma unsigned_m1_cases {m} : @to_Z m (opp one) =
  if (m <=? -2) || (m =? 0) then -1
  else if Z.abs m =? 1 then 0
  else m-1.
Proof.
  case (Z.leb_spec m (-2)) as []; auto using to_Z_m1_neg.
  case (Z.eqb_spec m 0) as [->|]; auto using to_Z_of_Z_mod0.
  case (Z.eqb_spec (Z.abs m) 1) as [|].
  { assert (m = 1 \/ m = -1) as [->| ->] by lia; trivial. }
  apply to_Z_m1_pos; lia.
Qed.
Notation to_Z_m1_cases := unsigned_m1_cases (only parsing).

Lemma of_Z_m1 {m} : @of_Z m (-1) = opp one.
Proof.
  rewrite <-of_Z_to_Z.
  apply of_Z_inj_cases; split; intros; subst; trivial; subst m'.
  rewrite to_Z_opp, Z.mod_abs_r_mod.
  cbv [one]; change (-1) with (-(1)).
  rewrite to_Z_of_Z, 2 Z.mod_opp_l_nz; rewrite ?Z.mod_abs_r_mod, ?Z.mod_small; try lia.
Qed.

Lemma signed_m1 {m} (Hm : 2 <= m) : @signed m (opp one) = -1.
Proof.
  destruct (Z.eq_dec m 2) as [->|]; trivial.
  rewrite signed_opp, signed_1, Z.smod_small; Z.to_euclidean_division_equations; lia.
Qed.

Lemma of_Z_opp {m} (x : Z) : of_Z m (Z.opp x) = opp (of_Z m x).
Proof. cbv [opp]. rewrite <-Z.sub_0_l, of_Z_sub, of_Z_0; trivial. Qed.

Lemma opp_zero {m} : @opp m zero = zero.
Proof. apply to_Z_inj. rewrite to_Z_opp, to_Z_0, Zmod_0_l; trivial. Qed.

Lemma opp_overflow {m} (Hm : m mod 2 = 0)
  (x : Zmod m) (Hx : signed x = -m/2) : opp x = x.
Proof.
  apply signed_inj. rewrite signed_opp.
  rewrite (Z.smod_diveq 1); Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_opp_odd {m} (x : Zmod m) (H : m mod 2 = 1) :
  signed (opp x) = Z.opp (signed x).
Proof.
  pose proof signed_range x.
  rewrite signed_opp, (Z.smod_diveq 0); try lia.
  Z.to_euclidean_division_equations; lia.
Qed.

Lemma signed_opp_small {m} (x : Zmod m) (H : signed x = -m/2 -> m mod 2 = 1) :
  signed (- x) = Z.opp (signed x).
Proof.
  rewrite signed_opp.
  case (Z.eq_dec m 0) as [->|]; [apply Z.smod_0_r|].
  apply Z.smod_small_iff; pose proof signed_range x.
  Z.to_euclidean_division_equations; lia.
Qed.

Lemma unsigned_mul {m} (x y : Zmod m) : to_Z (x * y) = (to_Z x * to_Z y) mod m.
Proof. cbv [mul]; rewrite ?to_Z_of_Z; trivial. Qed.
Notation to_Z_mul := unsigned_mul (only parsing).

Lemma signed_mul {m} x y : signed (@mul m x y) = Z.smodulo (signed x*signed y) m.
Proof. rewrite <-!smod_unsigned, to_Z_mul, Z.smod_mod, Z.smod_idemp_mul; trivial. Qed.

Lemma of_Z_mul {m} (x y : Z) : of_Z m (Z.mul x y) = mul (of_Z m x) (of_Z m y).
Proof.
  apply to_Z_inj.
  rewrite to_Z_mul, ?to_Z_of_Z, ?Zmult_mod_idemp_r, ?Zmult_mod_idemp_l; auto.
Qed.

Local Ltac r := try apply to_Z_inj; cbv [one];
  (* Note: rewrite is slow, and autorewrite isn't faster *)
  repeat rewrite ?to_Z_of_Z, ?to_Z_add, ?to_Z_mul, ?to_Z_sub, ?to_Z_opp,
    ?mod_to_Z, ?Zmod_0_l, ?Z.mul_1_l, ?Z.add_0_l, ?Zplus_mod_idemp_l,
    ?Zplus_mod_idemp_r, ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r,
    ?Z.add_opp_diag_r, ?to_Z_0;
  try (f_equal; lia).

Lemma add_0_l {m} a : @add m zero a = a. Proof. r. Qed.
Lemma add_comm {m} a b : @add m a b = add b a. Proof. r. Qed.
Lemma mul_comm {m} a b : @mul m a b = mul b a. Proof. r. Qed.
Lemma add_assoc {m} a b c : @add m a (add b c) = add (add a b) c. Proof. r. Qed.
Lemma mul_assoc {m} a b c : @mul m a (mul b c) = mul (mul a b) c. Proof. r. Qed.
Lemma mul_add_l {m} a b c : @mul m (add a b) c = add (mul a c) (mul b c). Proof. r. Qed.
Lemma mul_1_l {m} a : @mul m one a = a. Proof. r. Qed.
Lemma add_opp_r {m} a b : @add m a (opp b) = sub a b. Proof. r. Qed.
Lemma add_opp_same_r {m} a : @add m a (opp a) = zero. Proof. r. Qed.

Lemma sub_same {m} a : @sub m a a = zero.
Proof. rewrite <-add_opp_r, add_opp_same_r; trivial. Qed.

Lemma ring_theory m : @ring_theory (Zmod m) zero one add mul sub opp eq.
Proof. split; auto using eq_sym, add_0_l, add_comm, mul_comm, add_assoc, mul_assoc, mul_add_l, mul_1_l, add_opp_r, add_opp_same_r. Qed.

Section WithRing.
  Context {m : Z}.
  Add Ring __Private__Zmod_base_ring : (ring_theory m).
  Implicit Types a b c : Zmod m.
  Lemma opp_0 : opp zero = zero :> Zmod m. Proof. ring. Qed.
  Lemma add_0_r a : add a zero = a. Proof. ring. Qed.
  Lemma sub_0_l a : sub zero a = opp a. Proof. ring. Qed.
  Lemma sub_0_r a : sub a zero = a. Proof. ring. Qed.
  Lemma mul_1_r a : mul a one = a. Proof. ring. Qed.
  Lemma mul_m1_l a : mul (opp one) a = opp a. Proof. ring. Qed.
  Lemma mul_m1_r a : mul a (opp one) = opp a. Proof. ring. Qed.
  Lemma mul_0_l a : mul zero a = zero. Proof. ring. Qed.
  Lemma mul_0_r a : mul a zero = zero. Proof. ring. Qed.
  Lemma opp_opp a : opp (opp a) = a. Proof. ring. Qed.
  Lemma opp_inj a b : opp a = opp b -> a = b. Proof. intros H; ring [H]. Qed.
  Lemma opp_inj_iff a b : opp a = opp b <-> a = b. Proof. split. apply opp_inj. congruence. Qed.
  Lemma add_opp_l a b : add (opp a) b = sub b a. Proof. ring. Qed.
  Lemma sub_opp_r a b : sub a (opp b) = add a b. Proof. ring. Qed.
  Lemma sub_opp_l a b : sub (opp a) b = opp (add a b). Proof. ring. Qed.
  Lemma add_sub_r a b c : add a (sub b c) = sub (add a b) c. Proof. ring. Qed.
  Lemma add_sub_l a b c : add (sub a b) c = sub (add a c) b. Proof. ring. Qed.
  Lemma sub_sub_r a b c : sub a (sub b c) = sub (add a c) b. Proof. ring. Qed.
  Lemma sub_sub_l a b c : sub (sub a b) c = sub a (add b c). Proof. ring. Qed.
  Lemma mul_add_r a b c : mul a (add b c) = add (mul a b) (mul a c). Proof. ring. Qed.
  Lemma add_opp_same_l a : @add m (opp a) a = zero. Proof. ring. Qed.
  Lemma mul_sub_l a b c : mul (sub a b) c = sub (mul a c) (mul b c). Proof. ring. Qed.
  Lemma mul_sub_r a b c : mul a (sub b c) = sub (mul a b) (mul a c). Proof. ring. Qed.
  Lemma mul_opp_l a b : mul (opp a) b = opp (mul a b). Proof. ring. Qed.
  Lemma mul_opp_r a b : mul a (opp b) = opp (mul a b). Proof. ring. Qed.
  Lemma mul_opp_opp a b : mul (opp a) (opp b) = mul a b. Proof. ring. Qed.
  Local Lemma square_roots_opp_prime_subproof a b :
    sub (mul a a) (mul b b) = mul (sub a (opp b)) (sub a b). Proof. ring. Qed.
End WithRing.

(** ** Properties of division operators *)

Lemma udiv_0_r {m} x : @udiv m x zero = opp one.
Proof. cbv [udiv]. pose proof to_Z_0 m. case Z.eq_dec as []; congruence. Qed.

Lemma unsigned_udiv {m} (x y : Zmod m) (Hy : y <> 0 :> Z) : to_Z (@udiv m x y) = Z.div x y mod m.
Proof.
  cbv [udiv]; case Z.eq_dec as []; [lia|].
  pose proof unsigned_range x.
  pose proof unsigned_range y.
  rewrite to_Z_of_small_Z; cycle 1; f_equal.
  { apply Z.mod_id_iff; case Z.eqb eqn:?; Z.to_euclidean_division_equations; nia. }
  destruct m as [|m|m]; cbn [Z.sgn Z.opp]; intuition try lia.
  { case Z.eqb; rewrite Zmod_0_r, ?Z.add_0_r; trivial. }
  { case Z.eqb eqn:?; [|rewrite Z.mod_small]; Z.to_euclidean_division_equations; nia. }
  case (Z.eqb_spec (Z.sgn (x/y)) 1) as []; trivial.
  rewrite (Z.mod_diveq (-1)); Z.to_euclidean_division_equations; nia.
  rewrite (Z.mod_diveq 0); Z.to_euclidean_division_equations; nia.
Qed.
Notation to_Z_udiv := unsigned_udiv (only parsing).

Lemma unsigned_udiv_nonneg {m} (x y : Zmod m) (Hm : 0 <= m) (Hy : y <> 0 :> Z) : to_Z (@udiv m x y) = Z.div x y.
Proof.
  rewrite to_Z_udiv by trivial.
  pose proof unsigned_range x.
  pose proof unsigned_range y.
  destruct m as [|m|m]; [apply Zmod_0_r| |lia].
  apply Z.mod_small; Z.to_euclidean_division_equations; nia.
Qed.
Notation to_Z_udiv_nonneg := unsigned_udiv_nonneg (only parsing).

Lemma of_Z_div_small {m} (x y : Z) (Hx : 0 <= x < m) (Hy : 0 < y < m) :
  of_Z m (x / y) = udiv (of_Z _ x) (of_Z _ y).
Proof.
  apply to_Z_inj; rewrite ?to_Z_udiv; rewrite ?to_Z_of_Z, ?Z.mod_small;
    Z.to_euclidean_division_equations; nia.
Qed.

Lemma unsigned_umod {m} x y : to_Z (@umod m x y) = Z.modulo x y.
Proof.
  pose proof unsigned_range x; pose proof unsigned_range y.
  apply to_Z_of_small_Z, Z.mod_id_iff; zify; Z.to_euclidean_division_equations; nia.
Qed.
Notation to_Z_umod := unsigned_umod (only parsing).

Lemma of_Z_umod_small {m} (x y : Z) (Hx : 0 <= x < m) (Hy : 0 <= y < m) :
  of_Z m (x mod y) = umod (of_Z _ x) (of_Z _ y).
Proof.
  apply to_Z_inj; rewrite ?to_Z_umod; rewrite ?to_Z_of_Z, ?(Z.mod_small _ m);
    Z.to_euclidean_division_equations; nia.
Qed.

Lemma umod_0_r {m} x : @umod m x zero = x.
Proof. apply to_Z_inj; rewrite unsigned_umod, unsigned_0, Zmod_0_r; trivial. Qed.

Lemma signed_squot {m} x y : @signed m (squot x y) =
  Z.smodulo (if signed y =? 0 then -1 else signed x ÷ signed y) m.
Proof. apply signed_of_Z. Qed.

Lemma signed_squot_nz {m} x y : signed y <> 0 -> @signed m (squot x y) = Z.smodulo (signed x ÷ signed y) m.
Proof. cbv [squot]. rewrite signed_of_Z. case (signed y); trivial; congruence. Qed.

Lemma signed_srem {m} x y : @signed m (srem x y) = Z.smodulo (Z.rem (signed x) (signed y)) m.
Proof. apply signed_of_Z. Qed.

Lemma squot_0_r {m} x : @squot m x zero = opp one.
Proof. cbv [squot]. rewrite signed_0, of_Z_m1; trivial. Qed.

Lemma smod_0_r {m} x : @srem m x zero = x.
Proof. cbv [srem]. apply signed_inj. rewrite signed_of_Z, signed_0, Z.rem_0_r_ext, smod_signed; trivial. Qed.

Lemma signed_squot_small {m} x y (Hm : 0 <= m) (Hy : signed y <> 0) :
  ~ (signed x = -m/2 /\ signed y = -1 /\ m mod 2 = 0) ->
  @signed m (squot x y) = signed x ÷ signed y.
Proof.
  intros H; rewrite signed_squot_nz by trivial.
  pose proof signed_range x; pose proof signed_range y.
  case (Z.eqb_spec m 0) as [->|]; auto using Z.smod_0_r.
 apply Z.smod_small; Z.to_euclidean_division_equations; nia.
Qed.

Lemma squot_overflow {m} x y
  (Hm : m mod 2 = 0) (Hx : signed x = -m/2) (Hy : signed y = -1) :
  @squot m x y = x.
Proof.
  apply signed_inj; rewrite signed_squot_nz, Hx, Hy by lia.
  rewrite (Z.smod_diveq 1); Z.to_euclidean_division_equations; nia.
Qed.

Lemma squot_m1_r {m} (x : Zmod m) (Hm : 0 < m) : @squot m x (opp one) = opp x.
Proof.
  eapply wlog_eq_Zmod_2_pos; trivial; intro Hm'.
  apply signed_inj.
  rewrite signed_squot_nz; rewrite ?signed_m1; try lia.
  change (-1) with (Z.opp 1); rewrite Z.quot_opp_r, Z.quot_1_r by lia.
  rewrite signed_opp; trivial.
Qed.

Lemma unsigned_inv {m} x : to_Z (@inv m x) = Z.invmod x m.
Proof. apply to_Z_of_small_Z, Z.mod_invmod. Qed.
Notation to_Z_inv := unsigned_inv (only parsing).

Lemma inv_0 {m} : @inv m zero = zero.
Proof. apply to_Z_inj. rewrite to_Z_inv, to_Z_0, Z.invmod_0_l; trivial. Qed.

Lemma unsigned_mdiv {m} x y : to_Z (@mdiv m x y) = x * Z.invmod y m mod m.
Proof. cbv [mdiv]. rewrite to_Z_mul, to_Z_inv; trivial. Qed.
Notation to_Z_mdiv := unsigned_mdiv (only parsing).

Lemma mdiv_0_r {m} x : @mdiv m x zero = zero.
Proof. cbv [mdiv]. rewrite inv_0, mul_0_r; trivial. Qed.

Lemma mul_inv_l {m} x y : mul (@inv m y) x = mdiv x y.
Proof. apply to_Z_inj. cbv [mdiv inv]. rewrite mul_comm; trivial. Qed.

Lemma mul_inv_r {m} x y : mul x (@inv m y) = mdiv x y.
Proof. rewrite mul_comm, mul_inv_l; trivial. Qed.

(** ** Bitwise operations *)
Lemma unsigned_and {m} x y : @to_Z m (and x y) = Z.land x y mod m.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_and := unsigned_and (only parsing).

Lemma unsigned_and_small {m} (Hm : 0 <= m) x y : @to_Z m (and x y) = Z.land x y.
Proof.
  rewrite to_Z_and.
  case (Z.eqb_spec m 0) as [->|]; auto using Zmod_0_r.
  apply Z.mod_small.
  pose proof to_Z_range x; pose proof to_Z_range y.
  pose proof N.land_le_l (Z.to_N x) (Z.to_N y).
  pose proof N2Z.inj_land (Z.to_N x) (Z.to_N y).
  rewrite 2Z2N.id in *; try apply to_Z_range; intuition try lia.
Qed.
Notation to_Z_and_small := unsigned_and_small (only parsing).

Lemma unsigned_ndn {m} x y : @to_Z m (ndn x y) = Z.ldiff x y mod m.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_ndn  := unsigned_ndn (only parsing).

Lemma unsigned_ndn_small {m} x y (Hm : 0 <= m) : @to_Z m (ndn x y) = Z.ldiff x y.
Proof.
  rewrite to_Z_ndn.
  case (Z.eqb_spec m 0) as [->|]; auto using Zmod_0_r.
  apply Z.mod_small.
  pose proof to_Z_range x; pose proof to_Z_range y.
  pose proof N.ldiff_le_l (Z.to_N x) (Z.to_N y).
  pose proof N2Z.inj_ldiff (Z.to_N x) (Z.to_N y).
  rewrite 2Z2N.id in *; try apply to_Z_range; intuition try lia.
Qed.
Notation to_Z_ndn_small := unsigned_ndn_small (only parsing).

(** ** Shifts *)

Lemma unsigned_sru {m} x n : @to_Z m (sru x n) = Z.shiftr x n mod m.
Proof. apply to_Z_of_Z. Qed.
Notation to_Z_sru := unsigned_sru (only parsing).

Lemma unsigned_sru_small {m} x n (Hm : 0 <= m) (Hn : 0 <= n) : @to_Z m (sru x n) = Z.shiftr x n.
Proof.
  rewrite to_Z_sru.
  case (Z.eqb_spec m 0) as [->|]; auto using Zmod_0_r.
  apply Z.mod_small; pose proof (to_Z_range x).
  rewrite Z.shiftr_div_pow2; Z.to_euclidean_division_equations; nia.
Qed.
Notation to_Z_sru_small := unsigned_sru_small (only parsing).

(* TODO
Lemma signed_srs {m} x n : @signed m (srs x n) = Z.shiftr (signed x) n.
Proof.
  cbv [srs]; rewrite signed_of_Z; apply Z.smod_small.
  rewrite Z.shiftr_div_pow2 by lia; pose proof signed_range x.
  Z.to_euclidean_division_equations; nia.
Qed.

Lemma unsigned_srs {m} x n : @to_Z m (srs x n) = Z.shiftr (signed x) n mod m.
Proof. rewrite <-mod_to_Z, <-Z.mod_smod, <-signed_srs, <-signed_of_Z, of_Z_to_Z; trivial. Qed.
Notation to_Z_srs := unsigned_srs (only parsing).
*)

Lemma unsigned_slu {m} x n : @to_Z m (slu x n) = Z.shiftl x n mod m.
Proof. cbv [slu]; rewrite to_Z_of_Z; trivial. Qed.
Notation to_Z_slu := unsigned_slu (only parsing).


(** ** Lemmas for equalities with different moduli *)

Lemma unsigned_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> to_Z a = to_Z b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, to_Z_inj. Qed.
Notation to_Z_inj_dep := unsigned_inj_dep (only parsing).

Lemma unsigned_inj_dep_iff {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n /\ to_Z a = to_Z b <-> existT _ _ a = existT _ _ b.
Proof.
  split. { intros []; auto using to_Z_inj_dep. }
  intros H; inversion_sigma; subst; auto.
Qed.
Notation to_Z_inj_dep_iff := unsigned_inj_dep_iff (only parsing).

Lemma unsigned_eq_rect {m} (a : Zmod m) n p : to_Z (eq_rect _ _ a n p) = to_Z a.
Proof. case p; trivial. Qed.
Notation to_Z_eq_rect := unsigned_eq_rect (only parsing).

Lemma signed_inj_dep {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n -> signed a = signed b -> existT _ _ a = existT _ _ b.
Proof. destruct 1; auto using f_equal, signed_inj. Qed.

Lemma signed_inj_dep_iff {m} (a : Zmod m) {n} (b : Zmod n) :
  m = n /\ signed a = signed b <-> existT _ _ a = existT _ _ b.
Proof.
  split. { intros []; auto using signed_inj_dep. }
  intros H; inversion_sigma; subst; auto.
Qed.

Lemma signed_eq_rect {m} (a : Zmod m) n p : signed (eq_rect _ _ a n p) = signed a.
Proof. case p; trivial. Qed.


(** ** [pow] *)

Lemma pow_0_r {m} x : @pow m x 0 = one.
Proof. trivial. Qed.

Lemma pow_1_r {m} x : @pow m x 1 = x.
Proof. trivial. Qed.

Lemma pow_2_r {m} x : @pow m x 2 = mul x x.
Proof. trivial. Qed.

Local Notation pow_N := ZmodDef.Zmod.Private_pow_N.

Lemma Private_pow_nonneg {m} (x : Zmod m) z (Hz : 0 <= z) : pow x z = pow_N x (Z.to_N z).
Proof. cbv [pow]; case (Z.ltb_spec z 0) as []; trivial; lia. Qed.

Lemma Private_pow_neg {m} (x : Zmod m) z (Hz : z < 0) : pow x z = inv (pow_N x (Z.to_N (-z))).
Proof. cbv [pow]; case (Z.ltb_spec z 0) as []; trivial; lia. Qed.

Lemma pow_neg {m} (x : Zmod m) z (Hz : z < 0) : pow x z = inv (pow x (-z)).
Proof. rewrite Private_pow_neg, Private_pow_nonneg by lia; trivial. Qed.

Lemma Private_pow_N_correct {m} a n : @pow_N m a n = N.iter n (mul a) one.
Proof. apply N.iter_op_correct; auto using mul_1_r, mul_assoc. Qed.

Lemma Private_pow_N_0_r {m} (x : Zmod m) : @pow_N m x 0 = one.
Proof. rewrite Private_pow_N_correct; trivial. Qed.

Lemma Private_pow_N_succ_r {m} (x : Zmod m) n : pow_N x (N.succ n) = mul x (pow_N x n).
Proof. rewrite !Private_pow_N_correct, N.iter_succ; trivial. Qed.

Lemma pow_succ_nonneg_r {m} (x : Zmod m) n (H : 0 <= n) : pow x (Z.succ n) = mul x (pow x n).
Proof.
  cbv [pow].
  case (Z.ltb_spec (Z.succ n) 0), (Z.ltb_spec n 0); try lia.
  rewrite Z2N.inj_succ, Private_pow_N_succ_r; trivial; lia.
Qed.
Notation pow_succ_r_nonneg := pow_succ_nonneg_r.

Lemma pow_add_r_nonneg {m} (x : Zmod m) a b (Ha : 0 <= a) (Hb : 0 <= b) :
  pow x (a+b) = mul (x^a) (x^b).
Proof.
  generalize dependent b; generalize dependent a; refine (natlike_ind _ _ _).
  { intros; rewrite Z.add_0_l, pow_0_r, mul_1_l; trivial. }
  intros a Ha IH b Hb.
  rewrite ?Z.add_succ_l, ?Z.add_pred_l, ?pow_succ_nonneg_r, ?IH, ?mul_assoc by lia; trivial.
Qed.

Lemma pow_mul_l_nonneg {m} (x y : Zmod m) n (Hn : 0 <= n) :
  pow (x * y) n = mul (x ^ n) (y ^ n).
Proof.
  revert y; revert x; generalize dependent n; refine (natlike_ind _ _ _).
  { intros. rewrite ?pow_0_r, ?mul_1_r; trivial. }
  intros a Ha IH b Hb.
  rewrite ?Z.add_succ_l, ?Z.add_pred_l, ?pow_succ_nonneg_r, ?IH by lia; trivial.
  rewrite ?mul_assoc; f_equal; rewrite <-?mul_assoc; f_equal; auto using mul_comm.
Qed.

Local Coercion Z.of_N : N >-> Z.
Lemma Private_to_Z_pow_N {m} x n : @to_Z m (pow_N x n) = to_Z x ^ n mod m.
Proof.
  revert x; induction n using N.peano_ind; intros;
    try apply to_Z_of_small_Z; try apply Zmod_mod.
  rewrite  ?Private_pow_N_succ_r, ?to_Z_mul,
    ?N2Z.inj_succ, ?Z.pow_succ_r, ?IHn, ?Zmult_mod_idemp_r; trivial using N2Z.is_nonneg.
Qed.

Lemma unsigned_pow_nonneg_r {m} x z (Hz : 0 <= z) : @to_Z m (pow x z) = x^z mod m.
Proof. rewrite Private_pow_nonneg, Private_to_Z_pow_N; f_equal; f_equal; lia. Qed.
Notation to_Z_pow_nonneg_r := unsigned_pow_nonneg_r (only parsing).

Lemma unsigned_pow_neg_r {m} x z (Hz : z < 0) : @to_Z m (pow x z) = Z.invmod (to_Z x^(-z)) m.
Proof.
  rewrite pow_neg, to_Z_inv, to_Z_pow_nonneg_r by lia.
  rewrite Z.invmod_mod_l; f_equal; f_equal; lia.
Qed.
Notation to_Z_pow_neg_r := unsigned_pow_neg_r (only parsing).

Lemma signed_pow_nonneg_r {m} x z (Hz : 0 <= z) : @signed m (pow x z) = Z.smodulo (signed x ^ z) m.
Proof.
  rewrite <-!smod_unsigned, to_Z_pow_nonneg_r, Z.smod_mod, Z.smod_pow_l; trivial.
Qed.
Notation signed_pow_nonneg := signed_pow_nonneg_r.

Lemma of_Z_pow {m} x n (H : 0 <= n) : of_Z m (x ^ n) = pow (of_Z m x) n.
Proof.
  apply to_Z_inj. rewrite to_Z_pow_nonneg_r, !to_Z_of_Z, Z.mod_pow_l; trivial.
Qed.

Lemma Private_pow_N_0_l {m} n (Hn : n <> 0%N) : @pow_N m zero n = zero.
Proof. apply to_Z_inj; rewrite Private_to_Z_pow_N, to_Z_0, ?Z.pow_0_l; trivial; lia. Qed.

Lemma pow_0_l {m} n (Hn : n <> 0) : @pow m zero n = zero.
Proof. cbv [pow]; case Z.ltb eqn:?; rewrite Private_pow_N_0_l, ?inv_0 by lia; auto. Qed.


(** ** Misc *)

Lemma sub_eq_0 {m} a b (H : @sub m a b = zero) : a = b.
Proof.
  apply (f_equal to_Z) in H.
  rewrite to_Z_sub, to_Z_0 in H. eapply Z.cong_iff_0 in H.
  rewrite 2 mod_to_Z in *; auto using to_Z_inj.
Qed.

Lemma sub_eq_0_iff {m} a b : @sub m a b = zero <-> a = b.
Proof. split; try apply sub_eq_0. intros; subst; try apply sub_same. Qed.

Lemma add_eq_0 {m} a b (H : @add m a b = zero) : b = opp a.
Proof.
  rewrite <-(opp_opp a), add_opp_l in H.
  apply sub_eq_0 in H; trivial.
Qed.

Lemma add_eq_0_iff {m} a b : @add m a b = zero <-> b = opp a.
Proof. split; try apply add_eq_0. intros ->. rewrite add_opp_r, sub_same; auto. Qed.

Lemma opp_1_neq_1 {m} (Hm : 3 <= Z.abs m) : @opp m one <> one.
Proof.
  intros H%(f_equal to_Z); rewrite to_Z_m1_cases, to_Z_1_cases in H.
  repeat match goal with
         | H : context [ Z.leb ?a ?b ] |- _ => destruct (Z.leb_spec a b) in *
         | H : context [ Z.eqb ?a ?b ] |- _ => destruct (Z.eqb_spec a b) in *
         | _ => progress cbn [andb orb] in *
         end; try lia.
Qed.

Lemma inv_1 {m} : @inv m one = one.
Proof.
  apply to_Z_inj. rewrite to_Z_inv, to_Z_1_cases.
  case Z.leb_spec; try case Z.eqb_spec; intros; trivial.
  { rewrite ?Z.invmod_1_l, ?Z.invmod_0_l, ?Z.mod_small by lia; trivial. }
  pose proof Z.invmod_mod_l 1 m.
  rewrite Z.invmod_1_l, (Z.mod_diveq (-1)) in * by lia.
  assert ((1 - m * -1) = m+1) by lia. congruence.
Qed.

Lemma mdiv_1_r {m} x : @mdiv m x one = x.
Proof. cbv [mdiv]. rewrite inv_1, mul_1_r; trivial. Qed.

(** ** Absolute value *)

Lemma abs_0 m : @abs m zero = zero.
Proof. cbv [abs]. rewrite signed_0; trivial. Qed.

Lemma abs_1 m : @abs m one = one.
Proof.
  cbv [abs signed].
  case (Z.ltb_spec (Z.double _) _); case Z.ltb_spec; trivial; rewrite ?to_Z_1_cases;
    repeat case Z.leb_spec; repeat case Z.eqb_spec; try lia.
  intros; assert (2 = m) as <- by lia; trivial.
Qed.

Lemma abs_nonneg {m} x : 0 <= @signed m x -> abs x = x.
Proof. cbv [abs]. destruct (Z.ltb_spec (signed x) 0); intuition lia. Qed.

Lemma abs_neg {m} x : @signed m x < 0 -> abs x = opp x.
Proof. cbv [abs]. destruct (Z.ltb_spec (signed x) 0); intuition lia. Qed.

Lemma abs_pos {m} x : 0 < @signed m x -> abs x = x.
Proof. cbv [abs]. destruct (Z.ltb_spec (signed x) 0); intuition lia. Qed.

Lemma abs_opp {m} x : @abs m (opp x) = abs x.
Proof.
  eapply signed_inj; case (Z.eqb_spec (signed x) (-m/2)) as []; cycle 1.
  2: case (Z.eqb_spec (m mod 2) 0) as []; cycle 1.
  1,2: cbv [abs]; rewrite ?opp_opp; repeat case Z.ltb_spec; intros; trivial;
    rewrite signed_opp_small in *; Z.to_euclidean_division_equations; lia.
  cbv [abs]; rewrite ?opp_opp; repeat case Z.ltb_spec; trivial;
  rewrite !opp_overflow; trivial; pose proof signed_range x;
  intuition try (Z.to_euclidean_division_equations; nia).
Qed.

Lemma abs_abs {m} (x : Zmod m) : abs (abs x) = abs x.
Proof. unfold abs at 2; case Z.ltb; rewrite ?abs_opp; trivial. Qed.

Lemma signed_abs_small {m} x (H : signed x <> - m / 2) :
  @signed m (abs x) = Z.abs (signed x).
Proof.
  cbv [abs]; destruct (Z.ltb_spec (signed x) 0); [rewrite signed_opp_small|]; lia.
Qed.

Lemma signed_abs_odd {m} (Hm : m mod 2 = 1) x :
  @signed m (abs x) = Z.abs (signed x).
Proof.
  cbv [abs]; destruct (Z.ltb_spec (signed x) 0); [rewrite signed_opp_small|];
    (pose proof signed_range x; Z.div_mod_to_equations; nia).
Qed.

Lemma abs_overflow {m} (Hm : m mod 2 = 0)
  (x : Zmod m) (Hx : signed x = -m/2) : abs x = x.
Proof.
  cbv [abs]. rewrite Hx.
  case (Z.ltb_spec (-m/2) 0) as []; auto using opp_overflow.
Qed.

Lemma signed_abs_nonneg_small {m} (x : Zmod m) (H : signed x <> - m / 2):
  0 <= signed (abs x).
Proof. rewrite signed_abs_small; lia. Qed.

Lemma signed_abs_nonneg_odd {m} (Hm : m mod 2 = 1) (x : Zmod m) :
  0 <= signed (abs x).
Proof. rewrite signed_abs_odd; lia. Qed.

Lemma abs_mul_abs_l {m} (x y : Zmod m) : abs (abs x * y) = abs (x * y).
Proof.
  destruct (Z_lt_le_dec (signed x) 0); rewrite ?(abs_nonneg x), ?(abs_neg x) by lia;
  rewrite ?mul_opp_opp, ?mul_opp_l, ?mul_opp_r, ?abs_opp; trivial.
Qed.

Lemma abs_mul_abs_r {m} (x y : Zmod m) : abs (x * abs y) = abs (x * y).
Proof.
  destruct (Z_lt_le_dec (signed y) 0); rewrite ?(abs_nonneg y), ?(abs_neg y) by lia;
  rewrite ?mul_opp_opp, ?mul_opp_l, ?mul_opp_r, ?abs_opp; trivial.
Qed.

Lemma abs_mul_abs_abs {m} (x y : Zmod m) : abs (abs x * abs y) = abs (x * y).
Proof. rewrite ?abs_mul_abs_l, ?abs_mul_abs_r; trivial. Qed.

Lemma gcd_opp_m {m} x : Z.gcd (@opp m x) m = Z.gcd x m.
Proof. rewrite to_Z_opp, Z.gcd_mod_l, Z.gcd_opp_l; try lia. Qed.

Lemma gcd_abs_m_odd {m} (Hm : m mod 2 = 1) x :
  Z.gcd (@abs m x) m = Z.gcd x m.
Proof. rewrite <-2mod_signed, 2Z.gcd_mod_l, signed_abs_odd, Z.gcd_abs_l; lia. Qed.

Lemma pow_opp_2 {m} (x : Zmod m) : pow (opp x) 2 = pow x 2.
Proof. rewrite !pow_2_r. rewrite ?mul_opp_opp; trivial. Qed.

Lemma pow_abs_2 {m} (x : Zmod m) : pow (abs x) 2 = pow x 2.
Proof. rewrite !pow_2_r. cbv [abs]; case Z.ltb; rewrite ?mul_opp_opp; trivial. Qed.

Lemma eq_abs_iff m (x y : Zmod m) : abs x = abs y <-> (y = x \/ y = opp x).
Proof.
  split.
  { cbv [abs]; do 2 case Z.ltb_spec; intros; subst; auto using opp_inj, opp_opp. }
  { intros [H|H]; apply (f_equal abs) in H; rewrite ?abs_opp in H; congruence. }
Qed.

(** Elements *)

Lemma length_elements m : length (elements m) = Z.abs_nat m.
Proof. cbv [elements]. rewrite List.length_map, List.length_seq; trivial. Qed.

Lemma nth_error_elements {m} n : List.nth_error (elements m) n =
  if (Nat.ltb n (Z.abs_nat m)) then Some (of_Z _ (Z.of_nat n)) else None.
Proof.
  cbv [elements].
  rewrite List.nth_error_map, List.nth_error_seq.
  case Nat.ltb; trivial.
Qed.

Lemma in_elements {m} a (Hm : m <> 0) : List.In a (elements m).
Proof.
  apply List.nth_error_In with (n:=Z.to_nat (a mod Z.abs m)).
  rewrite nth_error_elements. pose proof to_Z_range a.
  case Nat.ltb_spec; [|Z.to_euclidean_division_equations; lia]; intros.
  rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
  rewrite of_Z_mod_abs, of_Z_to_Z; trivial.
Qed.

Lemma NoDup_elements m : List.NoDup (elements m).
Proof.
  cbv [elements].
  eapply List.NoDup_map_inv with (f := fun x : Zmod m => Z.to_nat (x mod (Z.abs m))).
  erewrite List.map_map, List.map_ext_in, List.map_id; trivial using List.seq_NoDup.
  intros a Ha. apply List.in_seq in Ha; cbn [Nat.add] in Ha.
  rewrite to_Z_of_Z, Z.mod_abs_r_mod, Z.mod_small, Nat2Z.id; lia.
Qed.

Example elements_0 : elements 0 = []. Proof. trivial. Qed.

Lemma elements_by_sign m (Hm : m <> 0) :
  elements m = [zero] ++ positives m ++ negatives m.
Proof.
  cbv [elements positives negatives].
  assert ([zero] = map (fun i => of_Z m (Z.of_nat i)) (seq O 1)) as -> by trivial.
  rewrite <-!map_app, <-!seq_app. f_equal; f_equal.
  case Z.ltb_spec; cbn [Z.b2z]; Z.to_euclidean_division_equations; nia.
Qed.

Lemma elements_by_sign' m :
  elements m = List.firstn (Z.abs_nat m) [zero] ++ positives m ++ negatives m.
Proof.
  case (Z.eqb_spec m 0) as [->|]; trivial.
  rewrite elements_by_sign, List.firstn_all2 by (cbn [length]; lia); trivial.
Qed.

Lemma in_positives m x (Hm : m <> 0) : In x (positives m) <-> 0 < signed x.
Proof.
  cbv [positives]. rewrite signed_pos_iff, in_map_iff; setoid_rewrite in_seq.
  split; [intros (i&<-&A)|eexists (Z.to_nat (x mod Z.abs m)); split];
    rewrite ?Z2Nat.id, ?to_Z_of_Z, ?of_Z_mod_abs, ?of_Z_to_Z; trivial;
    try revert A; try case Z.ltb_spec; cbn [Z.b2z]; intros;
    try pose proof unsigned_neg_bound x ltac:(lia);
    rewrite ?Z.mod_small, ?(Z.mod_diveq (-1)) by (Z.to_euclidean_division_equations; lia);
    try (Z.to_euclidean_division_equations; lia).
Qed.

Lemma in_negatives m x (Hm : m <> 0) : In x (negatives m) <-> signed x < 0.
Proof.
  cbv [negatives]. rewrite signed_neg_iff, in_map_iff; setoid_rewrite in_seq.
  split; [intros (i&<-&A)|eexists (Z.to_nat (x mod Z.abs m)); split];
    rewrite ?Z2Nat.id, ?to_Z_of_Z, ?of_Z_mod_abs, ?of_Z_to_Z; trivial;
    try revert A; try case Z.ltb_spec; cbn [Z.b2z]; intros;
    try pose proof unsigned_pos_bound x ltac:(lia);
    rewrite ?Z.mod_small, ?(Z.mod_diveq (-1)) by (Z.to_euclidean_division_equations; lia);
    try (Z.to_euclidean_division_equations; lia).
Qed.


Lemma NoDup_positives m : NoDup (positives m).
Proof.
  pose proof NoDup_elements m as H; rewrite elements_by_sign' in H.
  eauto using NoDup_app_remove_l, NoDup_app_remove_r.
Qed.

Lemma NoDup_negatives m : NoDup (negatives m).
Proof.
  pose proof NoDup_elements m as H; rewrite elements_by_sign' in H.
  eauto using NoDup_app_remove_l, NoDup_app_remove_r.
Qed.

Lemma length_positives' m : length (positives m) = Z.to_nat ((Z.abs m - Z.b2z (0 <? m)) / 2).
Proof. cbv [positives]. rewrite length_map, length_seq; trivial. Qed.

Lemma length_positives m (Hm : 0 < m) : length (positives m) = Z.to_nat ((m-1)/2).
Proof.
  rewrite length_positives'.
  case Z.ltb_spec; cbn [Z.b2z]; try (Z.to_euclidean_division_equations; lia).
Qed.

Lemma length_negatives m (Hm : 0 < m) : length (negatives m) = Z.to_nat (m/2).
Proof.
  cbv [negatives]. rewrite length_map, length_seq.
  case Z.ltb_spec; cbn [Z.b2z]; try (Z.to_euclidean_division_equations; lia).
Qed.

Lemma negatives_as_positives_odd m (Hm : m mod 2 = 1) :
  negatives m = map opp (rev (positives m)).
Proof.
  cbv [positives negatives]; rewrite <-map_rev, map_map.
  apply nth_error_ext; intros i;
    rewrite ?nth_error_map, ?nth_error_rev, ?nth_error_seq, ?length_seq.
  repeat match goal with
  | |- context [Nat.ltb ?a ?b] => case (Nat.ltb_spec a b) as []
  | |- context [Z.ltb ?a ?b] => case (Z.ltb_spec a b) as []; cbn [Z.b2z] in *
  end; trivial; try (Z.to_euclidean_division_equations; lia);
    cbn [option_map]; f_equal; apply to_Z_inj; rewrite ?to_Z_opp, ?to_Z_of_Z;
    assert (Z.of_nat (1 + _) = - (Z.of_nat i - (Z.abs m)/2))
      as -> by (Z.to_euclidean_division_equations; lia);
    repeat rewrite ?Z.mod_opp_mod_opp,
      ?(Z.mod_diveq (-1)), ?(Z.mod_diveq (0)) (* WHY repeat matters?*)
      by (Z.to_euclidean_division_equations; lia);
      (Z.to_euclidean_division_equations; lia).
Qed.

Lemma invertibles_prime p (H : Z.prime p) :
  invertibles p = List.tl (elements p).
Proof.
  cbv [invertibles elements]; pose proof Z.prime_ge_2 p H.
  replace (Z.abs_nat p) with (S (Z.to_nat p-1)) by lia;
    progress cbn [List.seq List.tl List.map List.filter].
  rewrite to_Z_0, Z.gcd_0_l; destruct (Z.eqb_spec (Z.abs p) 1).
  { pose proof Z.prime_ge_2 p H; lia. }
  case Z.eqb_spec; intros; [lia|].
  erewrite filter_map_swap, filter_ext_in, filter_true; trivial; cbv beta.
  intros i ?%List.in_seq; apply Z.eqb_eq.
  rewrite Z.gcd_comm; apply Z.coprime_prime_small; trivial.
  rewrite Zmod.to_Z_of_Z, Z.mod_small; lia.
Qed.

Lemma length_invertibles_prime p (H : Z.prime p) :
  length (invertibles p) = Z.to_nat (p-1).
Proof.
  pose proof Z.prime_ge_2 p H.
  rewrite invertibles_prime, List.length_tl, Zmod.length_elements; trivial; lia.
Qed.

End Zmod.
