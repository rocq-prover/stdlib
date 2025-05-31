(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** An example of finite type : [Fin.t] *)
#[local] Set Warnings "-stdlib-vector".
Set Implicit Arguments.
From Stdlib Require Import PeanoNat Compare_dec List Finite Fin Permutation.
Export Finite. (* compat 9.0 *)

Lemma Fin_Finite n : Finite (Fin.t n).
Proof.
 induction n as [|n IHn].
 - exists nil.
   red;inversion 1.
 - destruct IHn as (l,Hl).
   exists (Fin.F1 :: map Fin.FS l).
   intros a. revert n a l Hl.
   refine (@Fin.caseS _ _ _); intros.
   + now left.
   + right. now apply in_map.
Qed.

(** Instead of working on a finite subset of nat, another
    solution is to use restricted [nat->nat] functions, and
    to consider them only below a certain bound [n]. *)

Definition bFun n (f:nat->nat) := forall x, x < n -> f x < n.

Definition bInjective n (f:nat->nat) :=
 forall x y, x < n -> y < n -> f x = f y -> x = y.

Definition bSurjective n (f:nat->nat) :=
 forall y, y < n -> exists x, x < n /\ f x = y.

(** We show that this is equivalent to the use of [Fin.t n]. *)

Module Fin2Restrict.

Notation n2f := Fin.of_nat_lt.
Definition f2n {n} (x:Fin.t n) := proj1_sig (Fin.to_nat x).
Definition f2n_ok n (x:Fin.t n) : f2n x < n := proj2_sig (Fin.to_nat x).
Definition n2f_f2n : forall n x, n2f (f2n_ok x) = x := @Fin.of_nat_to_nat_inv.
Definition f2n_n2f x n h : f2n (n2f h) = x := f_equal (@proj1_sig _ _) (@Fin.to_nat_of_nat x n h).
Definition n2f_ext : forall x n h h', n2f h = n2f h' := @Fin.of_nat_ext.
Definition f2n_inj : forall n x y, f2n x = f2n y -> x = y := @Fin.to_nat_inj.

Definition extend n (f:Fin.t n -> Fin.t n) : (nat->nat) :=
 fun x =>
   match le_lt_dec n x with
     | left _ => 0
     | right h => f2n (f (n2f h))
   end.

Definition restrict n (f:nat->nat)(hf : bFun n f) : (Fin.t n -> Fin.t n) :=
 fun x => let (x',h) := Fin.to_nat x in n2f (hf _ h).

Ltac break_dec H :=
 let H' := fresh "H" in
 destruct le_lt_dec as [H'|H'];
  [elim (proj1 (Nat.le_ngt _ _) H' H)
  |try rewrite (n2f_ext H' H) in *; try clear H'].

Lemma extend_ok n f : bFun n (@extend n f).
Proof.
 intros x h. unfold extend. break_dec h. apply f2n_ok.
Qed.

Lemma extend_f2n n f (x:Fin.t n) : extend f (f2n x) = f2n (f x).
Proof.
 generalize (n2f_f2n x). unfold extend, f2n, f2n_ok.
 destruct (Fin.to_nat x) as (x',h); simpl.
 break_dec h.
 now intros ->.
Qed.

Lemma extend_n2f n f x (h:x<n) : n2f (extend_ok f h) = f (n2f h).
Proof.
 generalize (extend_ok f h). unfold extend in *. break_dec h. intros h'.
 rewrite <- n2f_f2n. now apply n2f_ext.
Qed.

Lemma restrict_f2n n f hf (x:Fin.t n) :
 f2n (@restrict n f hf x) = f (f2n x).
Proof.
 unfold restrict, f2n. destruct (Fin.to_nat x) as (x',h); simpl.
 apply f2n_n2f.
Qed.

Lemma restrict_n2f n f hf x (h:x<n) :
 @restrict n f hf (n2f h) = n2f (hf _ h).
Proof.
 unfold restrict. generalize (f2n_n2f h). unfold f2n.
 destruct (Fin.to_nat (n2f h)) as (x',h'); simpl. intros ->.
 now apply n2f_ext.
Qed.

Lemma extend_surjective n f :
  bSurjective n (@extend n f) <-> Surjective f.
Proof.
 split.
 - intros hf y.
   destruct (hf _ (f2n_ok y)) as (x & h & Eq).
   exists (n2f h).
   apply f2n_inj. now rewrite <- Eq, <- extend_f2n, f2n_n2f.
 - intros hf y hy.
   destruct (hf (n2f hy)) as (x,Eq).
   exists (f2n x).
   split.
   + apply f2n_ok.
   + rewrite extend_f2n, Eq. apply f2n_n2f.
Qed.

Lemma extend_injective n f :
  bInjective n (@extend n f) <-> Injective f.
Proof.
 split.
 - intros hf x y Eq.
   apply f2n_inj. apply hf; try apply f2n_ok.
   now rewrite 2 extend_f2n, Eq.
 - intros hf x y hx hy Eq.
   rewrite <- (f2n_n2f hx), <- (f2n_n2f hy). f_equal.
   apply hf.
   rewrite <- 2 extend_n2f.
   generalize (extend_ok f hx) (extend_ok f hy).
   rewrite Eq. apply n2f_ext.
Qed.

Lemma restrict_surjective n f h :
  Surjective (@restrict n f h) <-> bSurjective n f.
Proof.
 split.
 - intros hf y hy.
   destruct (hf (n2f hy)) as (x,Eq).
   exists (f2n x).
   split.
   + apply f2n_ok.
   + rewrite <- (restrict_f2n h), Eq. apply f2n_n2f.
 - intros hf y.
   destruct (hf _ (f2n_ok y)) as (x & hx & Eq).
   exists (n2f hx).
   apply f2n_inj. now rewrite restrict_f2n, f2n_n2f.
Qed.

Lemma restrict_injective n f h :
  Injective (@restrict n f h) <-> bInjective n f.
Proof.
 split.
 - intros hf x y hx hy Eq.
   rewrite <- (f2n_n2f hx), <- (f2n_n2f hy). f_equal.
   apply hf.
   rewrite 2 restrict_n2f.
   generalize (h x hx) (h y hy).
   rewrite Eq. apply n2f_ext.
 - intros hf x y Eq.
   apply f2n_inj. apply hf; try apply f2n_ok.
   now rewrite <- 2 (restrict_f2n h), Eq.
Qed.

End Fin2Restrict.
Import Fin2Restrict.

(** We can now use Proof via the equivalence ... *)

Lemma bInjective_bSurjective n (f:nat->nat) :
 bFun n f -> (bInjective n f <-> bSurjective n f).
Proof.
 intros h.
 rewrite <- (restrict_injective h), <- (restrict_surjective h).
 apply Endo_Injective_Surjective.
 - apply Fin_Finite.
 - intros x y. destruct (Fin.eq_dec x y); [left|right]; trivial.
Qed.

Lemma bSurjective_bBijective n (f:nat->nat) :
 bFun n f -> bSurjective n f ->
 exists g, bFun n g /\ forall x, x < n -> g (f x) = x /\ f (g x) = x.
Proof.
 intro hf.
 rewrite <- (restrict_surjective hf). intros Su.
 assert (Ij : Injective (restrict hf)).
 { apply Endo_Injective_Surjective; trivial.
   - apply Fin_Finite.
   - intros x y. destruct (Fin.eq_dec x y); [left|right]; trivial. }
 assert (Bi : Bijective (restrict hf)).
 { apply Injective_Surjective_Bijective; trivial.
   - apply Fin_Finite.
   - exact Fin.eq_dec. }
 destruct Bi as (g & Hg & Hg').
 exists (extend g).
 split.
 - apply extend_ok.
 - intros x Hx. split.
   + now rewrite <- (f2n_n2f Hx), <- (restrict_f2n hf), extend_f2n, Hg.
   + now rewrite <- (f2n_n2f Hx), extend_f2n, <- (restrict_f2n hf), Hg'.
Qed.

Section Permutation_alt.
Variable A:Type.
Implicit Type a : A.
Implicit Type l : list A.

Lemma Permutation_nth_error_bis l l' :
 Permutation l l' <->
  exists f:nat->nat,
    Injective f /\
    bFun (length l) f /\
    (forall n, nth_error l' n = nth_error l (f n)).
Proof.
 rewrite Permutation_nth_error; split.
 - intros (E & f & Hf & Hf').
   exists f. do 2 (split; trivial).
   intros n Hn.
   destruct (Nat.le_gt_cases (length l) (f n)) as [LE|LT]; trivial.
   rewrite <- nth_error_None, <- Hf', nth_error_None, <- E in LE.
   elim (proj1 (Nat.lt_nge _ _) Hn LE).
 - intros (f & Hf & Hf2 & Hf3); split; [|exists f; auto].
   assert (H : length l' <= length l') by auto.
   rewrite <- nth_error_None, Hf3, nth_error_None in H.
   destruct (Nat.le_gt_cases (length l) (length l')) as [LE|LT];
    [|apply Hf2 in LT; elim (proj1 (Nat.lt_nge _ _) LT H)].
   apply Nat.lt_eq_cases in LE. destruct LE as [LT|EQ]; trivial.
   rewrite <- nth_error_Some, Hf3, nth_error_Some in LT.
   assert (Hf' : bInjective (length l) f).
   { intros x y _ _ E. now apply Hf. }
   rewrite (bInjective_bSurjective Hf2) in Hf'.
   destruct (Hf' _ LT) as (y & Hy & Hy').
   apply Hf in Hy'. subst y. elim (Nat.lt_irrefl _ Hy).
Qed.

Lemma Permutation_nth l l' d :
 Permutation l l' <->
  (let n := length l in
   length l' = n /\
   exists f:nat->nat,
    bFun n f /\
    bInjective n f /\
    (forall x, x < n -> nth x l' d = nth (f x) l d)).
Proof.
 split.
 - intros H.
   assert (E := Permutation_length H).
   split; auto.
   apply Permutation_nth_error_bis in H.
   destruct H as (f & Hf & Hf2 & Hf3).
   exists f. split; [|split]; auto.
   + intros x y _ _ Hxy. now apply Hf.
   + intros n Hn. rewrite <- 2 nth_default_eq. unfold nth_default.
     now rewrite Hf3.
 - intros (E & f & Hf1 & Hf2 & Hf3).
   rewrite Permutation_nth_error.
   split; auto.
   exists (fun n => if le_lt_dec (length l) n then n else f n).
   split.
   * intros x y.
     destruct le_lt_dec as [LE|LT];
      destruct le_lt_dec as [LE'|LT']; auto.
     + apply Hf1 in LT'. intros ->.
       elim (Nat.lt_irrefl (f y)). eapply Nat.lt_le_trans; eauto.
     + apply Hf1 in LT. intros <-.
       elim (Nat.lt_irrefl (f x)). eapply Nat.lt_le_trans; eauto.
   * intros n.
     destruct le_lt_dec as [LE|LT].
     + assert (LE' : length l' <= n) by (now rewrite E).
       rewrite <- nth_error_None in LE, LE'. congruence.
     + assert (LT' : n < length l') by (now rewrite E).
       specialize (Hf3 n LT). rewrite <- 2 nth_default_eq in Hf3.
       unfold nth_default in Hf3.
       apply Hf1 in LT.
       rewrite <- nth_error_Some in LT, LT'.
       do 2 destruct nth_error; congruence.
Qed.

End Permutation_alt.
