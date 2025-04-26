From Stdlib Require Import BinInt Wf_Z ZArithRing Zdiv Lia.

Module Z.
Local Open Scope Z_scope.

Lemma mod0_divide : forall a b, (b | a) -> a mod b = 0.
Proof. intros a b (c,->); apply Z_mod_mult. Qed.

Lemma absle_divide a b : (a | b) -> b <> 0 -> Z.abs a <= Z.abs b.
Proof.
 intros H Hb.
 rewrite <- Z.divide_abs_l, <- Z.divide_abs_r in H.
 apply Z.abs_pos in Hb.
 now apply Z.divide_pos_le.
Qed.

Lemma BoolSpec_divide_nz a b (H : a <> 0) : BoolSpec (Z.divide a b) (~ Z.divide a b) (b mod a =? 0).
Proof. case Z.eqb_spec; constructor; rewrite <-Z.mod_divide; trivial. Qed.

Lemma BoolSpec_divide a b : BoolSpec (Z.divide a b) (~ Z.divide a b) ((b =? 0) || negb (a =? 0) && (b mod a =? 0))%bool.
Proof.
  case Z.eqb_spec; rewrite ?Bool.orb_true_l, ?Bool.orb_false_l; intros; subst.
  { constructor. apply Z.divide_0_r. }
  case Z.eqb_spec; rewrite ?Bool.orb_true_l, ?Bool.orb_false_l; intros; subst.
  { constructor. intros ?%Z.divide_0_l; contradiction. }
  apply BoolSpec_divide_nz; trivial.
Qed.

Lemma divide_m1_l a : ( -1 | a ).
Proof. apply Z.divide_opp_l, Z.divide_1_l. Qed.

Lemma divide_pow_same_r a n (Hn : 1 <= n) : ( a | a^n ).
Proof.
  rewrite <-(Z.succ_pred n), Z.pow_succ_r by lia.
  apply Z.divide_factor_l.
Qed.

Definition coprime (a b:Z) : Prop := Z.gcd a b = 1.

Lemma BoolSpec_coprime a b : BoolSpec (Z.coprime a b) (~ Z.coprime a b) (Z.gcd a b =? 1).
Proof. case Z.eqb_spec; constructor; assumption. Qed.

Lemma Bezout_coprime_iff a b : Z.coprime a b <-> Z.Bezout a b 1.
Proof. split; try apply Z.gcd_bezout; try apply Z.bezout_1_gcd. Qed.

Definition Bezout_coprime a b := proj1 (Bezout_coprime_iff a b).
Definition coprime_Bezout a b := proj2 (Bezout_coprime_iff a b).

#[global] Instance Symmetric_coprime : RelationClasses.Symmetric coprime.
Proof. cbv [coprime]; intros ? ? ?; rewrite Z.gcd_comm; trivial. Qed.

Lemma coprime_0_l_iff z : coprime 0 z <-> Z.abs z = 1.
Proof. cbv [coprime]. rewrite Z.gcd_0_l. reflexivity. Qed.

Lemma coprime_0_r_iff z : coprime z 0 <-> Z.abs z = 1.
Proof. cbv [coprime]. rewrite Z.gcd_0_r. reflexivity. Qed.

Lemma coprime_1_l z : coprime 1 z. Proof. apply Z.gcd_1_l. Qed.

Lemma coprime_1_r z : coprime z 1. Proof. apply Z.gcd_1_r. Qed.

Lemma coprime_opp_l a b : coprime (- a) b <-> coprime a b.
Proof. cbv [coprime]. rewrite Z.gcd_opp_l. reflexivity. Qed.

Lemma coprime_opp_r a b : coprime a (- b) <-> coprime a b.
Proof. cbv [coprime]. rewrite Z.gcd_opp_r. reflexivity. Qed.

Lemma coprime_mod_l_iff a b : coprime (a mod b) b <-> coprime a b.
Proof. cbv [coprime]. rewrite Z.gcd_mod_l; reflexivity. Qed.

Lemma coprime_mod_r_iff a b : coprime a (b mod a) <-> coprime a b.
Proof. cbv [coprime]. rewrite Z.gcd_mod_r; reflexivity. Qed.

Lemma coprime_mul_r a b c : coprime a b -> coprime a c -> coprime a (b * c).
Proof.
  setoid_rewrite Bezout_coprime_iff.
  intros (u&v&H) (u0&v0&H0); exists (u*u0*a + v0*c*u + u0*v* b), (v*v0).
  rewrite <- H, <-Z.mul_1_r, <- H0; ring.
Qed.

Lemma coprime_mul_l a b c : coprime a c -> coprime b c -> coprime (a * b) c.
Proof. symmetry. apply coprime_mul_r; symmetry; trivial. Qed.

Lemma coprime_pow_r a b n : 0 <= n -> coprime a b -> coprime a (b ^ n).
Proof.
  intros Hn H; pattern n; apply natlike_ind; auto using coprime_1_r; intros.
  rewrite Z.pow_succ_r; auto using coprime_mul_r.
Qed.

Lemma coprime_pow_l a b n : 0 <= n -> coprime a b -> coprime (a ^ n) b.
Proof. symmetry. apply coprime_pow_r; try symmetry; trivial. Qed.


Definition prime p := 1 < p /\ forall n, 1 < n < p -> ~ (n|p).

Lemma not_prime_0 : not (prime 0).
Proof. intros []. lia. Qed.

Lemma not_prime_1 : not (prime 1).
Proof. intros []. lia. Qed.

Lemma prime_2 : prime 2.
Proof. split. lia. intros; intros []; nia. Qed.

Lemma prime_3 : prime 3.
Proof. split. lia. intros; intros []. assert (n = 2); nia. Qed.

Lemma prime_ge_2 p : prime p ->  2 <= p.
Proof. cbv [prime]. lia. Qed.

Lemma divide_prime_r a p (Hp : prime p) (Hd : (a | p)) :
  a = -p \/ a = -1 \/ a = 1 \/ a = p.
Proof.
  pose proof proj1 Hp; pose proof proj2 Hp a; pose proof proj2 Hp (-a).
  pose proof Z.divide_opp_l a p.
  pose proof Z.absle_divide _ _ Hd ltac:(lia).
  case (Z.eqb_spec a 0) as [->|]. { rewrite (Z.divide_0_l p) in * by auto; auto. }
  assert (a = -p \/ 1 < -a < p \/ a = -1 \/ a = 1 \/ 1 < a < p \/ a = p) by lia;
    intuition idtac.
Qed.

Lemma divide_prime_r_iff a p (Hp : prime p) :
  (a | p) <-> a = -p \/ a = -1 \/ a = 1 \/ a = p.
Proof.
  split; auto using divide_prime_r; []; intuition subst; rewrite ?Z.divide_opp_l;
    auto using Z.divide_m1_l, Z.divide_1_l, Z.divide_refl.
Qed.

Lemma not_prime_square a : ~ prime (a * a).
Proof.
  rewrite <-Z.abs_square; intros [? Ha].
  apply (Ha (Z.abs a)); [ nia | trivial using Z.divide_factor_l ].
Qed.

Lemma coprime_prime_l p a (Hp : prime p) (Ha : ~ (p | a)) : coprime p a.
Proof.
  apply Z.gcd_unique; trivial using Z.le_0_1, Z.divide_1_l; [].
  intros d [->|[->|[->| ->] ] ]%divide_prime_r H; rewrite ?Z.divide_opp_l in *;
     intuition trivial using Z.divide_1_l, Z.divide_m1_l.
Qed.

Lemma coprime_prime_l_iff p a (Hp : prime p) : coprime p a <-> ~ (p | a).
Proof.
  split; auto using coprime_prime_l.
  pose proof prime_ge_2 _ Hp.
  intros C; rewrite Z.divide_gcd_iff, C; lia.
Qed.

Lemma coprime_prime_small p a (Hp : prime p) (Ha : 1 <=  a < p) : coprime p a.
Proof. apply Z.coprime_prime_l; trivial. intros ?%Z.divide_pos_le; lia. Qed.

Lemma divide_prime_mul a b p (Hp : prime p) :
  (p | a * b) <-> (p | a) \/ (p | b).
Proof.
  intuition auto using Z.divide_mul_l, Z.divide_mul_r.
  case (BoolSpec_divide p a) as [?|D%coprime_prime_l]; auto.
  eapply Z.gauss in D; eauto.
Qed.

Lemma divide_prime_prime p q (Hp : prime p) (Hq : prime q) :
  ( p | q ) -> p = q.
Proof.
  intros H; pose proof proj1 Hp; pose proof proj1 Hq.
  apply Z.divide_prime_r in H; trivial; lia.
Qed.

Lemma divide_prime_prime_iff p q (Hp : prime p) (Hq : prime q) :
  ( p | q ) <-> p = q.
Proof.
  split; intros; subst; auto using Z.divide_refl, divide_prime_prime.
Qed.

Theorem divide_prime_pp p q n (Hp : prime p) (Hq : prime q) (Hn : 0 <= n) :
  (p | q^n) -> p = q.
Proof.
  pose proof prime_ge_2 _ Hp; pose proof prime_ge_2 _ Hq.
  pattern n; apply natlike_ind; trivial.
  - rewrite Z.pow_0_r; intros [->| ->]%Z.divide_1_r; lia.
  - intros ???.
    rewrite Z.pow_succ_r, Z.divide_prime_mul, divide_prime_prime_iff; intuition idtac.
Qed.

Theorem divide_prime_pp_iff p q n (Hp : prime p) (Hq : prime q) (Hn : 1 <= n) :
  (p | q^n) <-> p = q.
Proof.
  split. { apply divide_prime_pp; trivial; lia. }
  intros ->. apply divide_pow_same_r; trivial.
Qed.

Section extended_euclid_algorithm.
Variables a b : Z.

Local Lemma extgcd_rec_helper r1 r2 q :
  Z.gcd r1 r2 = Z.gcd a b -> Z.gcd (r2 - q * r1) r1 = Z.gcd a b.
Proof.
  intros H; rewrite <-H, Z.gcd_comm.
  rewrite <-(Z.gcd_add_mult_diag_r r1 r2 (-q)). f_equal; ring.
Qed.

Let f := S(S(Z.to_nat(Z.log2_up(Z.log2_up(Z.abs(a*b)))))). (* log2(fuel) *)

Local Definition extgcd_rec : forall r1 u1 v1 r2 u2 v2,
  (True -> 0 <= r1 /\ 0 <= r2 /\ r1 = u1 * a + v1 * b /\ r2 = u2 * a + v2 * b /\
      Z.gcd r1 r2 = Z.gcd a b)
   -> { '(u, v, d) | True -> u * a + v * b = d /\ d = Z.gcd a b}.
Proof.
  refine (Fix (Acc_intro_generator f (Z.lt_wf 0)) _ (fun r1 rec u1 v1  r2 u2 v2 H =>
    if Z.eq_dec r1 0
    then exist (fun '(u, v, d) => _) (u2, v2, r2) (fun _ => _)
    else let q := r2 / r1 in
         rec (r2 - q * r1) _ (u2 - q * u1) (v2 - q * v1) r1 u1 v1 (fun _ => _))).
  all : abstract (intuition (solve
    [ subst; rewrite ?Z.gcd_0_l_nonneg in *; auto using extgcd_rec_helper; ring
    | subst q; rewrite <-Zmod_eq_full by trivial;
      apply Z.mod_pos_bound, Z.le_neq; intuition congruence ])).
Defined.

Definition extgcd : Z*Z*Z.
Proof.
  refine (proj1_sig (extgcd_rec (Z.abs a) (Z.sgn a) 0 (Z.abs b) 0 (Z.sgn b) _)).
  abstract (intuition (trivial using Z.abs_nonneg;
    rewrite ?Z.gcd_abs_r, ?Z.gcd_abs_l, <-?Z.sgn_abs; ring)).
Defined.

Lemma extgcd_correct [u v d] : extgcd = (u, v, d) -> u * a + v * b = d /\ d = Z.gcd a b.
Proof. cbv [extgcd proj1_sig]. case extgcd_rec as (([],?),?). intuition congruence. Qed.
End extended_euclid_algorithm.

End Z.
