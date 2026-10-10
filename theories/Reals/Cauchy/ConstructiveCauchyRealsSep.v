(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(************************************************************************)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import QArith.Qabs.
From Stdlib Require Import Qpower.
From Stdlib Require Import Setoid.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import QExtra.
From Stdlib Require Import ConstructiveCauchyReals.

(** * Escape-window separation engine for the constructive Cauchy reals

    This file provides an abstract irrationality criterion for the
    constructive Cauchy reals of [ConstructiveCauchyReals].  Let [x] be a
    constructive Cauchy real and [e : nat -> Q] a family of positive
    "escape window" widths that decay slower than the resolution
    [2 * 2^(-n)] of Cauchy reals.  Suppose that every rational [q]
    eventually escapes the window around the resolution-tail value
    [seq x (- Z.of_nat n)]: for some [n], [e n < |q - seq x (- Z.of_nat n)|].
    Then [x] is apart, in the sense of [CReal_appart] (a sum of
    strict-order witnesses, in [Set]), from the embedded rational
    [inject_Q q], i.e. [x] carries a strictly positive rational distance
    from every rational constant.

    The main statement is [creal_escape_window_apart].  The stdlib
    [CRealLt x y] is itself the positive-distance witness form
    [{n : Z | 2 * 2^n < seq y n - seq x n}], and the Cauchy modulus of [x]
    controls its negative tail: values at any index [m <= k] agree with
    [seq x k] within [2^k].  At an escape index [n0] the window width
    [E = e n0] dominates the resolution [2 * 2^(- Z.of_nat n0)] by the
    coupling conjunct; pushing further down the negative tail to an index
    [m] chosen by the Q-archimedean lower bound [QarchimedeanLowExp2_Z]
    makes the witness threshold [2 * 2^m] drop below the margin
    [E - 2^(- Z.of_nat n0)], and the sign of [q - seq x (- Z.of_nat n0)],
    decidable in Q, selects which side of [CReal_appart] is produced.

    Statements are [Set]-valued throughout (sigma witnesses and the sum
    type [CReal_appart]); the only [Prop] occurrences are [Qlt]
    predicates inside the sigma type, mirroring the [CRealLt] definition
    itself.  No axiom and no classical logic is used; the main proof is a
    fully explicit chain of rational-order lemmas (no tactic closes the
    main statement), decidability of Q being used only to branch on the
    sign.

    WARNING: this file is experimental and likely to change in future
    releases. *)

(* Positivity and monotonicity of the powers of two. *)

Lemma creal_two_pos : (0 < 2)%Q.
Proof. unfold Qlt, Qnum, Qden. lia. Qed.

Lemma creal_two_ge1 : (1 <= 2)%Q.
Proof. unfold Qle, Qnum, Qden. lia. Qed.

Lemma creal_two_lt3 : (2 < 3)%Q.
Proof. unfold Qlt, Qnum, Qden. lia. Qed.

Lemma creal_three_pos : (0 < 3)%Q.
Proof. unfold Qlt, Qnum, Qden. lia. Qed.

Lemma creal_three_ge0 : (0 <= 3)%Q.
Proof. unfold Qle, Qnum, Qden. lia. Qed.

Lemma creal_third_pos : (0 < 1 # 3)%Q.
Proof. unfold Qlt, Qnum, Qden. lia. Qed.

Lemma creal_pow2_pos : forall z : Z, (0 < 2 ^ z)%Q.
Proof. intros z. apply Qpower_0_lt. exact creal_two_pos. Qed.

Lemma creal_pow2_le_mono : forall z z' : Z,
  (z <= z')%Z -> (2 ^ z <= 2 ^ z')%Q.
Proof.
  intros z z' H. apply Qpower_le_compat_l.
  - exact H.
  - exact creal_two_ge1.
Qed.

(* Escape-window structure and the separation engine.

   The escape family [e] must decay slower than the CReal resolution
   [2 * 2^(-n)] (first conjunct of each witness), and every rational [q]
   must escape the window centered at the resolution-tail value
   [seq x (- Z.of_nat n)] for some [n] (second conjunct).  The conclusion
   is the stdlib apartness [CReal_appart x (inject_Q q)]: a sum-type
   positive-distance certificate, carried by an explicit index with
   [2 * 2^m] strictly below the distance of the embedded constant. *)

Definition creal_escape_window (x : CReal) (e : nat -> Q) : Set :=
  forall q : Q,
    { n : nat |
      (Qlt (2 * 2 ^ Z.opp (Z.of_nat n)) (e n)
       /\ Qlt (e n) (Qabs (q - seq x (Z.opp (Z.of_nat n)))))%Q }.

Lemma seq_inject_Q : forall (q : Q) (n : Z), seq (inject_Q q) n = q.
Proof. reflexivity. Qed.

Theorem creal_escape_window_apart :
  forall (x : CReal) (e : nat -> Q),
    creal_escape_window x e ->
    forall q : Q, CReal_appart x (inject_Q q).
Proof.
  intros x e Hw q.
  destruct (Hw q) as [n0 [Hres Hesc]].
  set (n0z := Z.opp (Z.of_nat n0)) in *.
  set (E := e n0) in *.
  (* The coupling conjunct says E > 2 * 2^n0z, hence the margin       *)
  (* M := E - 2^n0z is positive and even above 2^n0z.                 *)
  assert (Hres' : (2 ^ n0z + 2 ^ n0z < E)%Q).
  { assert (HeqR : (2 * 2 ^ n0z == 2 ^ n0z + 2 ^ n0z)%Q) by ring.
    rewrite HeqR in Hres. exact Hres. }
  assert (Hmarg : (2 ^ n0z < E + - 2 ^ n0z)%Q).
  { pose proof (Qplus_lt_le_compat (2 ^ n0z + 2 ^ n0z) E (- 2 ^ n0z)
                  (- 2 ^ n0z) Hres' (Qle_refl _)) as HH.
    assert (HeqM : ((2 ^ n0z + 2 ^ n0z) + - 2 ^ n0z == 2 ^ n0z)%Q) by ring.
    rewrite HeqM in HH. exact HH. }
  assert (HmarginPos : (0 < E + - 2 ^ n0z)%Q)
    by exact (Qlt_trans _ _ _ (creal_pow2_pos n0z) Hmarg).
  (* Archimedean push: an index j with 2^j below one third of M.      *)
  assert (HTpos : (0 < (E + - 2 ^ n0z) * (1 # 3))%Q).
  { pose proof (Qmult_lt_compat_r 0 (E + - 2 ^ n0z) (1 # 3)
                  creal_third_pos HmarginPos) as HH.
    rewrite Qmult_0_l in HH. exact HH. }
  destruct (QarchimedeanLowExp2_Z ((E + - 2 ^ n0z) * (1 # 3)) HTpos)
    as [j Hj].
  assert (Hm1 : (Z.min n0z j <= n0z)%Z) by apply Z.le_min_l.
  assert (Hm2 : (Z.min n0z j <= j)%Z) by apply Z.le_min_r.
  (* Tail control on the negative tail, from the Cauchy modulus of x. *)
  pose proof (cauchy x n0z (Z.min n0z j) n0z Hm1 (Z.le_refl n0z)) as Hc.
  apply Qabs_diff_Qlt_condition in Hc. destruct Hc as [Hlow Hhigh].
  (* Hkey : 3 * 2^m < M, where m := Z.min n0z j.                      *)
  assert (Hkey : (3 * 2 ^ Z.min n0z j < E + - 2 ^ n0z)%Q).
  { pose proof (creal_pow2_le_mono (Z.min n0z j) j Hm2) as Hpowj.
    pose proof (Qmult_le_compat_r (2 ^ Z.min n0z j) (2 ^ j) 3 Hpowj
                  creal_three_ge0) as Hs1.
    pose proof (Qmult_lt_compat_r (2 ^ j) ((E + - 2 ^ n0z) * (1 # 3)) 3
                  creal_three_pos Hj) as Hs2.
    assert (Hs3 : (((E + - 2 ^ n0z) * (1 # 3)) * 3 == (E + - 2 ^ n0z))%Q)
      by ring.
    rewrite Hs3 in Hs2.
    rewrite (Qmult_comm (2 ^ Z.min n0z j) 3) in Hs1.
    rewrite (Qmult_comm (2 ^ j) 3) in Hs1.
    rewrite (Qmult_comm (2 ^ j) 3) in Hs2.
    exact (Qle_lt_trans _ _ _ Hs1 Hs2). }
  assert (H23 : (2 * 2 ^ Z.min n0z j < 3 * 2 ^ Z.min n0z j)%Q)
    by exact (Qmult_lt_compat_r 2 3 (2 ^ Z.min n0z j)
                (creal_pow2_pos (Z.min n0z j)) creal_two_lt3).
  destruct (Qlt_le_dec 0 (q - seq x n0z)) as [Hs | Hs].
  - (* q - seq x n0z > 0: x lies strictly below q. *)
    unfold CReal_appart. left.
    assert (HabsS : Qabs (q - seq x n0z) == q - seq x n0z).
    { apply Qabs_pos. apply Qlt_le_weak. exact Hs. }
    rewrite HabsS in Hesc.
    exists (Z.min n0z j).
    (* From Hlow: seq x m < seq x n0z + 2^n0z. *)
    assert (Hupper : (seq x (Z.min n0z j) < seq x n0z + 2 ^ n0z)%Q).
    { pose proof (Qplus_lt_le_compat
                    (seq x (Z.min n0z j) + - 2 ^ n0z) (seq x n0z)
                    (2 ^ n0z) (2 ^ n0z) Hlow (Qle_refl _)) as HH.
      assert (HeqU : ((seq x (Z.min n0z j) + - 2 ^ n0z) + 2 ^ n0z
                      == seq x (Z.min n0z j))%Q) by ring.
      rewrite HeqU in HH. exact HH. }
    (* Chain: E - 2^n0z < q - seq x m. *)
    assert (Hchain : (E + - 2 ^ n0z < q - seq x (Z.min n0z j))%Q).
    { pose proof (Qplus_lt_le_compat E (q - seq x n0z) (- 2 ^ n0z)
                    (- 2 ^ n0z) Hesc (Qle_refl _)) as Hs4.
      pose proof (Qopp_lt_compat (seq x (Z.min n0z j))
                    (seq x n0z + 2 ^ n0z) Hupper) as HnegU.
      pose proof (proj2 (Qplus_le_l (- (seq x n0z + 2 ^ n0z))
                          (- seq x (Z.min n0z j)) q)
                    (Qlt_le_weak _ _ HnegU)) as Hadd.
      assert (Heq2 : ( - (seq x n0z + 2 ^ n0z) + q
                      == (q - seq x n0z) + - 2 ^ n0z)%Q) by ring.
      assert (Heq3 : ( - seq x (Z.min n0z j) + q
                      == q - seq x (Z.min n0z j))%Q) by ring.
      rewrite Heq2, Heq3 in Hadd.
      exact (Qlt_le_trans _ _ _ Hs4 Hadd). }
    rewrite seq_inject_Q.
    exact (Qlt_trans _ (E + - 2 ^ n0z) _
            (Qlt_trans _ (3 * 2 ^ Z.min n0z j) _ H23 Hkey) Hchain).
  - (* q - seq x n0z <= 0: the escape margin forces q < x. *)
    unfold CReal_appart. right.
    assert (HabsS : Qabs (q - seq x n0z) == - (q - seq x n0z)).
    { apply Qabs_neg. exact Hs. }
    rewrite HabsS in Hesc.
    exists (Z.min n0z j).
    (* From Hhigh: -2^n0z < seq x m - seq x n0z. *)
    assert (Hcomp2 : (- 2 ^ n0z
                      < seq x (Z.min n0z j) + - seq x n0z)%Q).
    { assert (HeqC1 : (- 2 ^ n0z
                       == - (seq x (Z.min n0z j) + 2 ^ n0z)
                       + seq x (Z.min n0z j))%Q) by ring.
      assert (HeqC2 : (seq x (Z.min n0z j) + - seq x n0z
                       == - seq x n0z + seq x (Z.min n0z j))%Q) by ring.
      rewrite HeqC1, HeqC2.
      apply (Qplus_lt_le_compat
               (- (seq x (Z.min n0z j) + 2 ^ n0z)) (- seq x n0z)
               (seq x (Z.min n0z j)) (seq x (Z.min n0z j))).
      - exact (Qopp_lt_compat _ _ Hhigh).
      - apply Qle_refl. }
    pose proof (Qplus_lt_compat E (- (q - seq x n0z)) (- 2 ^ n0z)
                  (seq x (Z.min n0z j) + - seq x n0z) Hesc Hcomp2) as Hsum.
    assert (Hfin : (E + - 2 ^ n0z < seq x (Z.min n0z j) - q)%Q).
    { assert (HeqF : (- (q - seq x n0z)
                      + (seq x (Z.min n0z j) + - seq x n0z)
                      == seq x (Z.min n0z j) - q)%Q) by ring.
      rewrite HeqF in Hsum. exact Hsum. }
    rewrite seq_inject_Q.
    exact (Qlt_trans _ (E + - 2 ^ n0z) _
            (Qlt_trans _ (3 * 2 ^ Z.min n0z j) _ H23 Hkey) Hfin).
Qed.
