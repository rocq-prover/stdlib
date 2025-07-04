(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import BinInt Znat ZArithRing Lia Wf_Z Zcomplements Zdiv Zdivisibility.
From Stdlib Require Export Zpower.
From Stdlib Require Znumtheory.
#[local] Open Scope Z_scope.

(** Properties of the power function over [Z] *)

(** Nota: the usual properties of [Z.pow] are now already provided
    by [BinInt.Z]. Only remain here some compatibility elements,
    as well as more specific results about power and modulo and/or
    primality. *)

Lemma Zpower_pos_1_r x : Z.pow_pos x 1 = x.
Proof (Z.pow_1_r x).

Lemma Zpower_pos_1_l p : Z.pow_pos 1 p = 1.
Proof. now apply (Z.pow_1_l (Zpos p)). Qed.

Lemma Zpower_pos_0_l p : Z.pow_pos 0 p = 0.
Proof. now apply (Z.pow_0_l (Zpos p)). Qed.

Lemma Zpower_pos_pos x p : 0 < x -> 0 < Z.pow_pos x p.
Proof. intros. now apply (Z.pow_pos_nonneg x (Zpos p)). Qed.

Notation Zpower_1_r := Z.pow_1_r (only parsing).
Notation Zpower_1_l := Z.pow_1_l (only parsing).
Notation Zpower_0_l := Z.pow_0_l' (only parsing).
Notation Zpower_0_r := Z.pow_0_r (only parsing).
Notation Zpower_2 := Z.pow_2_r (only parsing).
Notation Zpower_gt_0 := Z.pow_pos_nonneg (only parsing).
Notation Zpower_ge_0 := Z.pow_nonneg (only parsing).
Notation Zpower_Zabs := Z.abs_pow (only parsing).
Notation Zpower_Zsucc := Z.pow_succ_r (only parsing).
Notation Zpower_mult := Z.pow_mul_r (only parsing).
Notation Zpower_le_monotone2 := Z.pow_le_mono_r (only parsing).

Theorem Zpower_le_monotone a b c :
 0 < a -> 0 <= b <= c -> a^b <= a^c.
Proof. intros. now apply Z.pow_le_mono_r. Qed.

Theorem Zpower_lt_monotone a b c :
 1 < a -> 0 <= b < c -> a^b < a^c.
Proof. intros. apply Z.pow_lt_mono_r; lia. Qed.

Theorem Zpower_gt_1 x y : 1 < x -> 0 < y -> 1 < x^y.
Proof. apply Z.pow_gt_1. Qed.

Theorem Zmult_power p q r : 0 <= r -> (p*q)^r = p^r * q^r.
Proof. intros. apply Z.pow_mul_l. Qed.

#[global]
Hint Resolve Z.pow_nonneg Z.pow_pos_nonneg : zarith.

Theorem Zpower_le_monotone3 a b c :
 0 <= c -> 0 <= a <= b -> a^c <= b^c.
Proof. intros. now apply Z.pow_le_mono_l. Qed.

Lemma Zpower_le_monotone_inv a b c :
  1 < a -> 0 < b -> a^b <= a^c -> b <= c.
Proof.
 intros Ha Hb H. apply (Z.pow_le_mono_r_iff a); trivial.
 apply Z.lt_le_incl; apply (Z.pow_gt_1 a); trivial.
 apply Z.lt_le_trans with (a^b); trivial. now apply Z.pow_gt_1.
Qed.

Notation Zpower_nat_Zpower := Zpower_nat_Zpower (only parsing).

Theorem Zpower2_lt_lin n : 0 <= n -> n < 2^n.
Proof. intros. now apply Z.pow_gt_lin_r. Qed.

Theorem Zpower2_le_lin n : 0 <= n -> n <= 2^n.
Proof. intros. apply Z.lt_le_incl. now apply Z.pow_gt_lin_r. Qed.

Lemma Zpower2_Psize n p :
  Zpos p < 2^(Z.of_nat n) <-> (Pos.size_nat p <= n)%nat.
Proof.
  revert p; induction n as [|n IHn].
  - intros p; destruct p; now split.
  - assert (Hn := Nat2Z.is_nonneg n).
    intros p; destruct p as [p|p|]; simpl Pos.size_nat.
    + specialize IHn with p.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia.
    + specialize IHn with p.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia.
    + split.
      * lia.
      * intros _. apply Z.pow_gt_1.
        -- easy.
        -- now rewrite Nat2Z.inj_succ, Z.lt_succ_r.
Qed.

(** * Z.pow and modulo *)

Theorem Zpower_mod p q n :
  0 < n -> (p^q) mod n = ((p mod n)^q) mod n.
Proof.
  intros Hn; destruct (Z.le_gt_cases 0 q) as [H1|H1].
  - pattern q; apply Wf_Z.natlike_ind; trivial.
    clear q H1. intros q Hq Rec. rewrite !Z.pow_succ_r; trivial.
    rewrite Z.mul_mod_idemp_l by lia.
    rewrite Z.mul_mod, Rec, <- Z.mul_mod by lia. reflexivity.
  - rewrite !Z.pow_neg_r; auto with zarith.
Qed.

(** A direct way to compute Z.pow modulo **)

Fixpoint Zpow_mod_pos (a: Z)(m: positive)(n : Z) : Z :=
  match m with
   | xH => a mod n
   | xO m' =>
      let z := Zpow_mod_pos a m' n in
      match z with
       | 0 => 0
       | _ => (z * z) mod n
      end
   | xI m' =>
      let z := Zpow_mod_pos a m' n in
      match z with
       | 0 => 0
       | _ => (z * z * a) mod n
      end
  end.

Definition Zpow_mod a m n :=
  match m with
   | 0 => 1 mod n
   | Zpos p => Zpow_mod_pos a p n
   | Zneg p => 0
  end.

Theorem Zpow_mod_pos_correct a m n :
 n <> 0 -> Zpow_mod_pos a m n = (Z.pow_pos a m) mod n.
Proof.
  intros Hn. induction m as [m IHm|m IHm|].
  - rewrite Pos.xI_succ_xO at 2. rewrite <- Pos.add_1_r, <- Pos.add_diag.
    rewrite 2 Zpower_pos_is_exp, Zpower_pos_1_r.
    rewrite Z.mul_mod, (Z.mul_mod (Z.pow_pos a m)) by trivial.
    rewrite <- IHm, <- Z.mul_mod by trivial.
    simpl. now destruct (Zpow_mod_pos a m n).
  - rewrite <- Pos.add_diag at 2.
    rewrite Zpower_pos_is_exp.
    rewrite Z.mul_mod by trivial.
    rewrite <- IHm.
    simpl. now destruct (Zpow_mod_pos a m n).
  - now rewrite Zpower_pos_1_r.
Qed.

Theorem Zpow_mod_correct a m n :
 n <> 0 -> Zpow_mod a m n = (a ^ m) mod n.
Proof.
  intros Hn. destruct m; simpl; trivial.
  - apply Zpow_mod_pos_correct; auto with zarith.
Qed.

(* Complements about power and number theory. *)

Lemma Zpower_divide p q : 0 < q -> (p | p ^ q).
Proof.
  exists (p^(q - 1)).
  rewrite Z.mul_comm, <- Z.pow_succ_r by lia; f_equal; lia.
Qed.

#[deprecated(use=Z.coprime_pow_r, since="9.1")]
Theorem rel_prime_Zpower_r i p q :
 0 <= i -> Znumtheory.rel_prime p q -> Znumtheory.rel_prime p (q^i).
Proof.
  setoid_rewrite Znumtheory.rel_prime_iff_coprime.
  apply Z.coprime_pow_r.
Qed.

#[deprecated(use=Z.coprime_pow_l, since="9.1")]
Theorem rel_prime_Zpower i j p q :
 0 <= i ->  0 <= j -> Znumtheory.rel_prime p q -> Znumtheory.rel_prime (p^i) (q^j).
Proof.
  setoid_rewrite Znumtheory.rel_prime_iff_coprime.
  intros. apply Z.coprime_pow_l; try apply Z.coprime_pow_r; trivial.
Qed.

Import Znumtheory.

#[deprecated(use=Z.divide_prime_pp, since="9.1")]
Theorem prime_power_prime p q n :
 0 <= n -> prime p -> prime q -> (p | q^n) -> p = q.
Proof. rewrite <-!prime_alt; eauto using Z.divide_prime_pp. Qed.

Theorem Zdivide_power_2 x p n :
 0 <= n -> 0 <= x -> prime p -> (x | p^n) -> exists m, x = p^m.
Proof.
  intros Hn Hx; revert p n Hn. generalize Hx.
  pattern x; apply Z_lt_induction; auto.
  clear x Hx; intros x IH Hx p n Hn Hp H.
  Z.le_elim Hx; subst.
  - apply Z.le_succ_l in Hx; simpl in Hx.
    Z.le_elim Hx; subst.
    + (* x > 1 *)
      case (prime_dec x); intros Hpr.
      * exists 1; rewrite Z.pow_1_r. eapply Z.divide_prime_pp; rewrite ?prime_alt; eauto.
      * case not_prime_divide with (2 := Hpr); auto.
        intros p1 ((Hp1, Hpq1),(q1,->)).
        assert (Hq1 : 0 < q1) by (apply Z.mul_lt_mono_pos_r with p1; lia).
        destruct (IH p1) with p n as (r1,Hr1). 3-4: assumption. 1-2: lia.
        -- transitivity (q1 * p1); trivial. exists q1; auto with zarith.
        -- destruct (IH q1) with p n as (r2,Hr2). 3-4: assumption. 2: lia.
           ++ split.
              ** lia.
              ** rewrite <- (Z.mul_1_r q1) at 1.
                 apply Z.mul_lt_mono_pos_l; auto with zarith.
           ++ transitivity (q1 * p1); trivial. exists p1; auto with zarith.
           ++ exists (r2 + r1); subst.
              symmetry. apply Z.pow_add_r.
              ** generalize Hq1; case r2; now auto with zarith.
              ** generalize Hp1; case r1; now auto with zarith.
    + (* x = 1 *)
      exists 0; rewrite Z.pow_0_r; auto.
  - (* x = 0 *)
    exists n; destruct H as [? H]; rewrite Z.mul_0_r in H; auto.
Qed.

(** * Z.square: a direct definition of [z^2] *)

#[deprecated(use=Pos.square_spec, since="9.1")]
Notation Psquare_correct := Pos.square_spec (only parsing).
#[deprecated(use=Z.square_spec, since="9.1")]
Notation Zsquare_correct := Z.square_spec (only parsing).
