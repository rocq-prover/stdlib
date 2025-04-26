From Stdlib Require Import BinInt.
From Stdlib Require Import ZArithRing.
From Stdlib Require Import Zdiv.
From Stdlib Require Import Zdivisibility.
Local Open Scope Z_scope.

Module Z.

(** ** Solving congruences *)

Lemma cong_mul_cancel_r_coprime a b m (Hm : m <> 0) (Hb : Z.coprime b m)
  (H : (a * b) mod m = 0) : a mod m = 0.
Proof.
  apply Z.mod_divide in H; trivial; [].
  rewrite Z.mul_comm in H; apply Z.gauss, Z.mod_divide in H; trivial.
  rewrite Z.gcd_comm; trivial.
Qed.

Definition invmod a m := fst (fst (Z.extgcd (a mod m) m)) mod m.

Lemma invmod_0_l m : invmod 0 m = 0. Proof. reflexivity. Qed.

Lemma invmod_0_r a : invmod a 0 = Z.sgn a.
Proof.
  case (Z.eqb_spec a 0) as [->|nz]; trivial.
  cbv [invmod]; destruct Z.extgcd as [[u v]g] eqn:H.
  eapply Z.extgcd_correct in H; case H as [[]]; subst; cbn [fst snd].
  rewrite ?Zmod_0_r, ?Z.mul_0_r, ?Z.add_0_r in *.
  rewrite Z.gcd_0_r, <-Z.sgn_abs, (Z.mul_comm u) in H.
  eapply Z.mul_cancel_l; eauto.
Qed.

Lemma invmod_ok a m : invmod a m * a mod m = Z.gcd a m mod m.
Proof.
  case (Z.eqb_spec m 0) as [->|nz].
  { rewrite invmod_0_r, ?Zmod_0_r, ?Z.gcd_0_r, <-?Z.sgn_abs; apply Z.mul_comm. }
  cbv [invmod]; destruct Z.extgcd as [[u v]g] eqn:H.
  eapply Z.extgcd_correct in H; case H as [[]]; subst; cbn [fst snd].
  rewrite Z.gcd_mod, Z.gcd_comm in H by trivial; rewrite <-H.
  erewrite Z.mod_add, Z.mul_mod_idemp_l, Z.mul_mod_idemp_r; trivial.
Qed.

Lemma mod_invmod m a : invmod a m mod m = invmod a m. Proof. apply Zmod_mod. Qed.

Lemma invmod_coprime' a m (H : Z.coprime a m) : invmod a m * a mod m = 1 mod m.
Proof. rewrite invmod_ok, H; trivial. Qed.

Lemma invmod_coprime a m (Hm : 2 <= m) (H : Z.coprime a m) : invmod a m * a mod m = 1.
Proof.
  rewrite invmod_coprime', Z.mod_1_l; trivial (*; lia*).
  eapply Z.le_succ_l; trivial.
Qed.

Lemma invmod_prime a m (Hm : Z.prime m) (H : a mod m <> 0) : invmod a m * a mod m = 1.
Proof.
  pose proof Z.prime_ge_2 _ Hm as Hm'.
  rewrite Z.mod_divide in H (* by lia *) by (intro; subst m; auto using Z.not_prime_0).
  apply invmod_coprime; trivial. symmetry. apply Z.coprime_prime_l; trivial.
Qed.

Lemma invmod_1_l m : invmod 1 m = 1 mod m.
Proof.
  pose proof invmod_coprime' 1 m ltac:(apply Z.coprime_1_l).
  rewrite Z.mul_1_r, mod_invmod in *; trivial.
Qed.

Lemma invmod_mod_l a m : invmod (a mod m) m = invmod a m.
Proof.
  case (Z.eq_dec m 0) as [->|]; [rewrite Zmod_0_r; trivial|].
  cbv [invmod]. rewrite Zmod_mod; trivial.
Qed.

Lemma coprime_invmod a m (H : Z.coprime a m) : Z.coprime (invmod a m) m.
Proof.
  destruct (Z.eqb_spec m 0) as [->|].
  { rewrite invmod_0_r. rewrite Z.coprime_0_r_iff in *. case a in *; trivial. }
  cbv [Z.coprime invmod].
  rewrite Z.gcd_mod by trivial.
  destruct Z.extgcd as ([]&?) eqn:HA; apply Z.extgcd_correct in HA; case HA as [Hb Hg']; cbn [fst].
  rewrite Z.gcd_mod, Z.gcd_comm in Hg' by trivial.
  rewrite H in *; subst.
  apply Z.bezout_1_gcd; cbv [Z.Bezout].
  rewrite <-Hg'.
  match goal with z0 : Z, z1 : Z |- _ => exists z0, (z1 mod m); ring end.
Qed.

(** ** Chinese Remainder Theorem *)

Definition combinecong (m1 m2 r1 r2 : Z) :=
  let '(u, v, d) := Z.extgcd m1 m2 in
  if Z.eq_dec (r1 mod d) (r2 mod d) then
    if Z.eq_dec d 0
    then r1
    else (v*m2*r1 + u*m1*r2) / d mod Z.abs (m1*(m2/d))
  else 0.

Lemma mod_combinecong_lcm m1 m2 r1 r2 :
  combinecong m1 m2 r1 r2 mod Z.lcm m1 m2 = combinecong m1 m2 r1 r2.
Proof.
  cbv [combinecong Z.lcm] in *; case (Z.extgcd m1 m2) as [[a b] d] eqn:E.
  eapply Z.extgcd_correct in E; case E as [E D]; rewrite D in *;
  repeat case Z.eq_dec as [];
  rewrite ?e0, ?Zdiv_0_r, ?Z.mul_0_r, ?Zmod_0_r; auto using Zmod_mod.
Qed.

Lemma combinecong_sound m1 m2 r1 r2 (H : r1 mod Z.gcd m1 m2 = r2 mod Z.gcd m1 m2)
  (x := combinecong m1 m2 r1 r2) : x mod m1 = r1 mod m1 /\ x mod m2 = r2 mod m2.
Proof.
  subst x.
  cbv [combinecong] in *; case (Z.extgcd m1 m2) as [[u v] d] eqn:E.
  eapply Z.extgcd_correct in E; case E as [E D]; rewrite D in *;
    change (Z.abs _) with (Z.lcm m1 m2).
  destruct (Z.eq_dec (Z.gcd m1 m2) 0) in *.
  { apply Z.gcd_eq_0 in e; case e as []; subst.
    case Z.eq_dec; rewrite ?Zmod_0_r in *; cbn in *; intuition congruence. }
  case Z.eq_dec as []; try congruence.
  rewrite 2 Z.mod_mod_divide by auto using Z.divide_lcm_l, Z.divide_lcm_r.
  apply Z.cong_iff_0, Z.mod_divide in H; trivial; rewrite <-D in *; clear D.
  rewrite 2Z.cong_iff_0, <-2Z.add_opp_r, <-2Z.div_add by trivial.
  split; rewrite <-E at 1.
  { eassert ((_ + _) = u*m1*-(r1-r2)) as -> by ring.
    rewrite Z.divide_div_mul_exact, Z.mul_comm, Z.mul_assoc, Z_mod_mult; trivial.
    apply Z.divide_opp_r; trivial. }
  { eassert ((_ + _) = v*m2*(r1-r2)) as -> by ring.
    rewrite Z.divide_div_mul_exact, Z.mul_comm, Z.mul_assoc, Z_mod_mult; trivial. }
Qed.

Lemma combinecong_complete' a m1 m2 r1 r2
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) :
  r1 mod Z.gcd m1 m2 = r2 mod Z.gcd m1 m2.
Proof.
  apply (f_equal (fun x => x mod Z.gcd m1 m2)) in H1, H2.
  rewrite !Z.mod_mod_divide in * by auto using Z.gcd_divide_l, Z.gcd_divide_r.
  congruence.
Qed.

Lemma combinecong_complete a m1 m2 r1 r2
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) :
  a mod Z.lcm m1 m2 = combinecong m1 m2 r1 r2.
Proof.
  pose proof combinecong_complete' a m1 m2 r1 r2 H1 H2 as H.
  revert H1 H2; case (combinecong_sound m1 m2 r1 r2 H) as [<- <-]; intros.
  rewrite <-mod_combinecong_lcm. remember (combinecong _ _ _ _) as b.
  case (Z.eq_dec m1 0) as [->|]; case (Z.eq_dec m2 0) as [->|];
    rewrite ?Zmod_0_r in *; try congruence.
  apply Z.cong_iff_ex in H1, H2; case H1 as [s H1]; case H2 as [r H2].
  assert (s*m1/Z.gcd m1 m2 = r*m2/Z.gcd m1 m2) by congruence.
  rewrite !Z.divide_div_mul_exact in * by
    (auto using Z.gcd_divide_l, Z.gcd_divide_r || rewrite Z.gcd_eq_0; intuition congruence).
  case (Z.gauss (m2/Z.gcd m1 m2) (m1/Z.gcd m1 m2) s) as [k ->].
  { eexists; rewrite (Z.mul_comm _ s); eassumption. }
  { rewrite Z.gcd_comm, Z.gcd_div_gcd; trivial; rewrite Z.gcd_eq_0; intuition idtac. }
  apply Z.cong_iff_ex, Z.divide_abs_l; exists k. rewrite H1; ring.
Qed.

Lemma combinecong_contradiction m1 m2 r1 r2  :
  r1 mod Z.gcd m1 m2 <> r2 mod Z.gcd m1 m2 -> combinecong m1 m2 r1 r2 = 0.
Proof.
  cbv [combinecong Z.lcm] in *; case (Z.extgcd m1 m2) as [[a b] d] eqn:E.
  eapply Z.extgcd_correct in E; case E as [E D]; rewrite D in *.
  case Z.eq_dec; congruence.
Qed.

Lemma combinecong_sound_coprime m1 m2 r1 r2 (H : Z.coprime m1 m2)
  (x := combinecong m1 m2 r1 r2) : x mod m1 = r1 mod m1 /\ x mod m2 = r2 mod m2.
Proof. apply combinecong_sound; rewrite H, 2 Z.mod_1_r; trivial. Qed.

Lemma combinecong_complete_coprime_abs a m1 m2 r1 r2 (H : Z.coprime m1 m2)
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) :
  a mod Z.abs (m1 * m2) = combinecong m1 m2 r1 r2.
Proof.
  erewrite <-combinecong_complete; eauto; f_equal.
  case (Z.eq_dec m1 0) as [->|]; case (Z.eq_dec m2 0) as [->|];
      rewrite ?Z.mul_0_r, ?Z.lcm_0_l, ?Z.lcm_0_r; auto; [].
  symmetry; apply Z.gcd_1_lcm_mul; auto.
Qed.

Lemma combinecong_complete_coprime_nonneg a m1 m2 r1 r2 (H : Z.coprime m1 m2)
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) (Hm : 0 <= m1*m2) :
  a mod (m1 * m2) = combinecong m1 m2 r1 r2.
Proof. erewrite <-combinecong_complete_coprime_abs; rewrite ?Z.abs_eq; eauto. Qed.

Lemma combinecong_complete_coprime_nonneg_nonneg a m1 m2 r1 r2 (H : Z.coprime m1 m2)
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) (Hm1 : 0 <= m1) (Hm2 : 0 <= m2) :
  a mod (m1 * m2) = combinecong m1 m2 r1 r2.
Proof. apply combinecong_complete_coprime_nonneg; auto using Z.mul_nonneg_nonneg. Qed.

Lemma combinecong_comm m1 m2 r1 r2 :
  combinecong m1 m2 r1 r2 = combinecong m2 m1 r2 r1.
Proof.
  case (Z.eq_dec (r1 mod Z.gcd m1 m2) (r2 mod Z.gcd m1 m2)) as [].
  { rewrite <-mod_combinecong_lcm, Z.lcm_comm;
    apply combinecong_complete; apply combinecong_sound; trivial. }
  rewrite 2 combinecong_contradiction; rewrite ?(Z.gcd_comm m2); congruence.
Qed.

Lemma combinecong_mod_l m1 m2 r1 r2 :
  combinecong m1 m2 (r1 mod m1) r2 = combinecong m1 m2 r1 r2.
Proof.
  case (Z.eq_dec (r1 mod Z.gcd m1 m2) (r2 mod Z.gcd m1 m2)) as [].
  { symmetry; rewrite <-mod_combinecong_lcm; apply combinecong_complete;
      rewrite ?Zmod_mod; apply combinecong_sound; auto. }
  rewrite 2 combinecong_contradiction;
    rewrite ?Z.mod_mod_divide by apply Z.gcd_divide_l; try congruence.
Qed.

Lemma combinecong_mod_r m1 m2 r1 r2 :
  combinecong m1 m2 r1 (r2 mod m2) = combinecong m1 m2 r1 r2.
Proof. rewrite combinecong_comm, combinecong_mod_l; apply combinecong_comm. Qed.

Lemma combinecong_opp_opp (m1 m2 r1 r2 : Z) :
  combinecong m1 m2 (- r1) (- r2) = - combinecong m1 m2 r1 r2 mod Z.lcm m1 m2.
Proof.
  case (Z.eq_dec (r1 mod Z.gcd m1 m2) (r2 mod Z.gcd m1 m2)) as [?|Y].
  { symmetry; apply combinecong_complete; rewrite <-Z.sub_0_l, <-Zminus_mod_idemp_r;
    case (combinecong_sound m1 m2 r1 r2) as [A B];
    rewrite ?A, ?B, ?Zminus_mod_idemp_r; trivial. }
  { rewrite 2combinecong_contradiction, Zmod_0_l; trivial; intro X; apply Y.
    apply (f_equal (fun z => - z mod Z.gcd m1 m2)) in X.
    rewrite 2Z.mod_opp_mod_opp in X; exact X. }
Qed.
End Z.
