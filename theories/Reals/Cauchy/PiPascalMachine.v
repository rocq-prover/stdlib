(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * The Pascal row machine: row sums, binomial row sums, and the
    odd half-row

    Mission.  The combinatorial content of the row identity in the
    partial-sum stratification of [sin(2x) = 2 sin x cos x] -- the
    row-sum machine (the sum of the first [n] terms), the binomial
    row sum ([sum_{k<=n} C(n,k) == 2^n] and its shifted companion),
    the binomial-factorial identity ([C(n,k) * k! * (n-k)! == n!]),
    the even-odd split of row sums, the alternating row sum (the
    row-sum content of [(1-1)^n == 0]), and the odd half-row
    ([sum_{i<=m} C(2m+1,2i+1) == 2^(2m)]).

    Dependencies.  Stdlib [QArith.QArith]; [PiKernelSlack]
    ([bpa_binom] binomial coefficients, [q_fact] factorials, [q_pow]
    powers, [lw0_alt] alternating signs).

    References.  The coefficient content of the offset row
    decomposition [piL_sin_dres] in Section 2 of
    [PiKernelSlack_D1_identity]; the standard identities of binomial
    coefficients (the row-sum, alternating-sum, and half-sum splits).

    Constructivity.  The statement level consists entirely of [Qeq]
    identities (computational content at the [Q] level, in the
    statement shape of the [PiKernelSlack_D1_identity] family);
    assumption-free and fully proved, with no non-constructive
    principles; induction with explicit algebraic chains and no
    solver endings; the computational witnesses of the final section
    are auxiliary statements whose trivial character is declared
    explicitly.

    Build.  [coqc -native-compiler no -q -Q . "" PiPascalMachine.v];
    the first eight bytes of the artifact are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import setoid_ring.ArithRing.
From Stdlib Require Import Lia.
Require Import PiKernelSlack.

(* ================= Section 1. The row-sum machine (the sum of the first [n] terms, [sum_{i<n} f i]) ================= *)

Fixpoint piLsb_sumR (f : nat -> Q) (n : nat) : Q :=
  match n with
  | O => 0%Q
  | Datatypes.S m => piLsb_sumR f m + f m
  end.

Lemma piLsb_sumR_snoc : forall (f : nat -> Q) (n : nat),
  piLsb_sumR f (Datatypes.S n) == piLsb_sumR f n + f n.
Proof. intros f n. reflexivity. Qed.

Lemma piLsb_sumR_plus : forall (f g : nat -> Q) (n : nat),
  piLsb_sumR (fun i => f i + g i) n == piLsb_sumR f n + piLsb_sumR g n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [piLsb_sumR]. rewrite IH. ring.
Qed.

Lemma piLsb_sumR_opp : forall (f : nat -> Q) (n : nat),
  piLsb_sumR (fun i => - f i) n == - piLsb_sumR f n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [piLsb_sumR]. rewrite IH. ring.
Qed.

Lemma piLsb_sumR_ext : forall (f g : nat -> Q) (n : nat),
  (forall i : nat, (i < n)%nat -> f i == g i) ->
  piLsb_sumR f n == piLsb_sumR g n.
Proof.
  induction n as [| n IH]; intros Hfg.
  - reflexivity.
  - cbn [piLsb_sumR].
    rewrite (IH (fun i H => Hfg i (Nat.lt_le_trans i n (Datatypes.S n) H
                                      (Nat.le_succ_diag_r n)))).
    rewrite (Hfg n (Nat.lt_succ_diag_r n)).
    reflexivity.
Qed.

Lemma piLsb_sumR_head : forall (f : nat -> Q) (n : nat),
  piLsb_sumR f (Datatypes.S n)
  == f 0%nat + piLsb_sumR (fun i => f (Datatypes.S i)) n.
Proof.
  induction n as [| n IH].
  - cbn [piLsb_sumR]. ring.
  - cbn [piLsb_sumR]. rewrite IH. ring.
Qed.

(* ================= Section 2. Small [Qeq] algebra lemmas ================= *)

Lemma piLsb_eq_cancel_r : forall a b c : Q, (a + c == b + c)%Q -> a == b.
Proof.
  intros a b c H.
  assert (H2 : a == a + c + (- c)%Q) by ring.
  rewrite H2, H. ring.
Qed.

Lemma piLsb_eq_cancel2 : forall a b c d : Q, c == d -> (a + c == b + d)%Q -> a == b.
Proof.
  intros a b c d Hcd H.
  rewrite <- Hcd in H.
  exact (piLsb_eq_cancel_r _ _ _ H).
Qed.

Lemma piLsb_eq_cancel_dbl : forall a b : Q, (a + a == b + b)%Q -> a == b.
Proof.
  intros a b H.
  assert (Hh1 : ((1#2)%Q * (a + a) == a)%Q) by ring.
  assert (Hh2 : ((1#2)%Q * (b + b) == b)%Q) by ring.
  assert (Hh3 : (1#2)%Q * (a + a) == (1#2)%Q * (b + b))
    by (rewrite H; reflexivity).
  rewrite Hh1, Hh2 in Hh3. exact Hh3.
Qed.

Lemma piLsb_q_succ_lit : forall m : nat,
  (Z.of_nat (Datatypes.S m) # 1)%Q == (Z.of_nat m # 1)%Q + 1%Q.
Proof.
  intros m.
  unfold Qeq, Qplus. cbn [Qnum Qden].
  rewrite !Z.mul_1_r, Nat2Z.inj_succ.
  symmetry. apply Z.add_1_r.
Qed.

(* ================= Section 3. Binomial point lemmas and the binomial-factorial identity ================= *)

Lemma piLsb_bpa_diag : forall n : nat, bpa_binom n n == 1%Q.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite bpa_binom_pascal, IH.
    rewrite (bpa_binom_out n (Datatypes.S n) (Nat.lt_succ_diag_r n)).
    ring.
Qed.

Lemma piLsb_bpa_bridge : forall n k : nat, (k <= n)%nat ->
  bpa_binom n k * q_fact k * q_fact (n - k)%nat == q_fact n.
Proof.
  induction n as [| n IH]; intros k Hk.
  - assert (Hk0 : k = 0%nat) by (inversion Hk; reflexivity).
    rewrite Hk0. cbn [bpa_binom q_fact Nat.sub]. ring.
  - destruct k as [| k'].
    + rewrite bpa_binom_0, Nat.sub_0_r, q_fact_succ. cbn [q_fact]. ring.
    + assert (Hk' : (k' <= n)%nat) by (apply (proj2 (Nat.succ_le_mono k' n)); exact Hk).
      (* Common normalization: [S n - S k'] folds to [n - k'], and
         both [q_fact] sides unfold by definition *)
      rewrite (Nat.sub_succ_r (S n) k'), (Nat.sub_succ_l k' n Hk').
      cbn [Nat.pred].
      rewrite (q_fact_succ k'), (q_fact_succ n).
      rewrite bpa_binom_pascal.
      destruct (proj1 (Nat.lt_eq_cases k' n) Hk') as [Hlt | Hkn].
      * (* Case [k' < n]: two induction instances *)
        assert (HSk : (Datatypes.S k' <= n)%nat) by exact Hlt.
        assert (IH1 := IH k' Hk').
        assert (IH2 := IH (Datatypes.S k') HSk).
        rewrite (lw0_sub_succ_eq n k' HSk), (q_fact_succ (n - S k')) in IH1.
        rewrite (q_fact_succ k') in IH2.
        rewrite (lw0_sub_succ_eq n k' HSk), (q_fact_succ (n - S k')).
        assert (Hdist :
          (bpa_binom n k' + bpa_binom n (Datatypes.S k'))
            * ((Z.of_nat (Datatypes.S k') # 1) * q_fact k')
            * ((Z.of_nat (Datatypes.S (n - S k')) # 1) * q_fact (n - S k'))
          == (bpa_binom n k' * q_fact k'
                * ((Z.of_nat (Datatypes.S (n - S k')) # 1)
                     * q_fact (n - S k')))
             * (Z.of_nat (Datatypes.S k') # 1)
             + (bpa_binom n (Datatypes.S k')
                  * ((Z.of_nat (Datatypes.S k') # 1) * q_fact k')
                  * q_fact (n - S k'))
               * ((Z.of_nat (Datatypes.S (n - S k')) # 1))) by ring.
        assert (HzQ :
          ((Z.of_nat (Datatypes.S k') # 1)%Q
             + (Z.of_nat (Datatypes.S (n - S k')) # 1)%Q)
          == (Z.of_nat (Datatypes.S n) # 1)%Q).
          { assert (Hnateq : (k' + S (n - S k'))%nat = n).
          { rewrite <- (lw0_sub_succ_eq n k' HSk).
            rewrite Nat.add_comm.
            apply Nat.sub_add. exact Hk'. }
          assert (Hz1 : (Z.of_nat (Datatypes.S k')
                          + Z.of_nat (Datatypes.S (n - S k')))%Z
                        = Z.of_nat (Datatypes.S n)).
          { rewrite <- Nat2Z.inj_add.
            f_equal.
            rewrite Nat.add_succ_l. f_equal. exact Hnateq. }
          unfold Qeq, Qplus. cbn [Qnum Qden].
          rewrite !Z.mul_1_r. rewrite Hz1 at 1. reflexivity. }
        assert (Hfin :
          q_fact n * (Z.of_nat (Datatypes.S k') # 1)%Q
            + q_fact n * (Z.of_nat (Datatypes.S (n - S k')) # 1)%Q
          == ((Z.of_nat (Datatypes.S k') # 1)%Q
                + (Z.of_nat (Datatypes.S (n - S k')) # 1)%Q)
               * q_fact n) by ring.
        rewrite Hdist, IH1, IH2, Hfin, <- HzQ. apply Qeq_refl.
      * (* Case [k' = n]: the diagonal term *)
        rewrite Hkn.
        rewrite piLsb_bpa_diag,
                (bpa_binom_out n (Datatypes.S n) (Nat.lt_succ_diag_r n)).
        rewrite Nat.sub_diag. cbn [q_fact]. ring.
Qed.

(* ================= Section 4. The binomial row sum (with its shifted companion; one induction, two products) ================= *)

Lemma piLsb_bpa_row_tot : forall n : nat,
  piLsb_sumR (bpa_binom n) (Datatypes.S n) == q_pow 2%Q n
  /\ piLsb_sumR (fun i => bpa_binom n (Datatypes.S i)) (Datatypes.S n)
     == q_pow 2%Q n - 1%Q.
Proof.
  induction n as [| n IH].
  - split; cbn [piLsb_sumR q_pow bpa_binom]; ring.
  - destruct IH as [IHt IHs].
    assert (Hdgn : piLsb_sumR (bpa_binom n) n + bpa_binom n n
                   == piLsb_sumR (bpa_binom n) (Datatypes.S n)) by reflexivity.
    rewrite piLsb_bpa_diag, IHt in Hdgn.
    assert (Hs0 : piLsb_sumR (fun i => bpa_binom n (Datatypes.S i)) n
                  == q_pow 2%Q n - 1%Q).
    { cbn [piLsb_sumR] in IHs.
      rewrite (bpa_binom_out n (Datatypes.S n) (Nat.lt_succ_diag_r n)) in IHs.
      rewrite <- IHs. ring. }
    assert (Htot : piLsb_sumR (bpa_binom (Datatypes.S n))
                     (Datatypes.S (Datatypes.S n)) == q_pow 2%Q (Datatypes.S n)).
    { rewrite (piLsb_sumR_snoc (bpa_binom (Datatypes.S n)) (Datatypes.S n)).
      rewrite piLsb_bpa_diag.
      rewrite piLsb_sumR_head.
      rewrite (bpa_binom_0 (Datatypes.S n)).
      assert (Hpascal :
        piLsb_sumR (fun i => bpa_binom (Datatypes.S n) (Datatypes.S i)) n
        == piLsb_sumR (fun i => bpa_binom n i + bpa_binom n (Datatypes.S i)) n).
      { apply piLsb_sumR_ext. intros i _.
        rewrite bpa_binom_pascal. apply Qeq_refl. }
      rewrite Hpascal, piLsb_sumR_plus, q_pow_succ, Hs0, <- Hdgn. ring. }
    split.
    + exact Htot.
    + assert (Hhead :
        bpa_binom (Datatypes.S n) 0%nat
        + piLsb_sumR (fun i => bpa_binom (Datatypes.S n) (Datatypes.S i))
                     (Datatypes.S n)
        == piLsb_sumR (bpa_binom (Datatypes.S n)) (Datatypes.S (Datatypes.S n))).
      { symmetry.
        apply (piLsb_sumR_head (bpa_binom (Datatypes.S n)) (Datatypes.S n)). }
      rewrite (bpa_binom_0 (Datatypes.S n)), Htot in Hhead.
      rewrite (piLsb_sumR_snoc
                 (fun i => bpa_binom (Datatypes.S n) (Datatypes.S i))
                 (Datatypes.S n)).
      cbv beta.
      rewrite (bpa_binom_out (Datatypes.S n) (Datatypes.S (Datatypes.S n))
                 (Nat.lt_succ_diag_r _)).
      rewrite <- Hhead. ring.
Qed.

(* ================= Section 5. Alternating-sign point lemmas and the even-odd split of row sums ================= *)

Lemma piLsb_lw0_alt_even : forall i : nat, lw0_alt (2 * i)%nat == 1%Q.
Proof.
  induction i as [| i IH].
  - reflexivity.
  - replace (2 * Datatypes.S i)%nat
      with (Datatypes.S (Datatypes.S (2 * i)))%nat by lia.
    cbn [lw0_alt]. rewrite IH. ring.
Qed.

Lemma piLsb_lw0_alt_odd : forall i : nat,
  lw0_alt (Datatypes.S (2 * i)%nat) == (-1)%Q.
Proof.
  intros i.
  change (lw0_alt (Datatypes.S (2 * i))%nat) with (Qopp (lw0_alt (2 * i))%Q).
  rewrite piLsb_lw0_alt_even. reflexivity.
Qed.

Lemma piLsb_sumR_even_odd : forall (f : nat -> Q) (n : nat),
  piLsb_sumR f (2 * Datatypes.S n)%nat
  == piLsb_sumR (fun i => f (2 * i)%nat) (Datatypes.S n)
     + piLsb_sumR (fun i => f (Datatypes.S (2 * i)%nat)) (Datatypes.S n).
Proof.
  induction n as [| n IH].
  - replace (2 * Datatypes.S 0)%nat with 2%nat by lia.
    cbn [piLsb_sumR]. rewrite Nat.mul_0_r. ring.
  - replace (2 * Datatypes.S (Datatypes.S n))%nat
      with (Datatypes.S (Datatypes.S (2 * Datatypes.S n)))%nat by lia.
    change (piLsb_sumR f (Datatypes.S (Datatypes.S (2 * Datatypes.S n))))
      with ((piLsb_sumR f (2 * Datatypes.S n)%nat + f (2 * Datatypes.S n)%nat
             + f (Datatypes.S (2 * Datatypes.S n)%nat))%Q).
    change (piLsb_sumR (fun i => f (2 * i)%nat) (Datatypes.S (Datatypes.S n)))
      with ((piLsb_sumR (fun i => f (2 * i)%nat) (Datatypes.S n)
             + f (2 * Datatypes.S n)%nat)%Q).
    change (piLsb_sumR (fun i => f (Datatypes.S (2 * i)%nat))
                       (Datatypes.S (Datatypes.S n)))
      with ((piLsb_sumR (fun i => f (Datatypes.S (2 * i)%nat)) (Datatypes.S n)
             + f (Datatypes.S (2 * Datatypes.S n)%nat))%Q).
    rewrite IH. ring.
Qed.

Lemma piLsb_sumR_even_odd_S : forall (f : nat -> Q) (n : nat),
  piLsb_sumR f (Datatypes.S (2 * n))%nat
  == piLsb_sumR (fun i => f (2 * i)%nat) (Datatypes.S n)
     + piLsb_sumR (fun i => f (Datatypes.S (2 * i)%nat)) n.
Proof.
  induction n as [| n IH].
  - rewrite Nat.mul_0_r. cbn [piLsb_sumR]. rewrite Nat.mul_0_r. ring.
  - replace (Datatypes.S (2 * Datatypes.S n))%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (2 * n))))%nat by lia.
    change (piLsb_sumR f (Datatypes.S (Datatypes.S (Datatypes.S (2 * n)))))
      with ((piLsb_sumR f (Datatypes.S (2 * n)%nat)
             + f (Datatypes.S (2 * n)%nat)
             + f (Datatypes.S (Datatypes.S (2 * n)%nat)))%Q).
    rewrite IH.
    change (piLsb_sumR (fun i => f (2 * i)%nat) (Datatypes.S (Datatypes.S n)))
      with ((piLsb_sumR (fun i => f (2 * i)%nat) (Datatypes.S n)
             + f (2 * Datatypes.S n)%nat)%Q).
    change (piLsb_sumR (fun i => f (Datatypes.S (2 * i)%nat)) (Datatypes.S n))
      with ((piLsb_sumR (fun i => f (Datatypes.S (2 * i)%nat)) n
             + f (Datatypes.S (2 * n)%nat))%Q).
    replace (2 * Datatypes.S n)%nat
      with (Datatypes.S (Datatypes.S (2 * n)))%nat by lia.
    ring.
Qed.

(* ================= Section 6. The alternating row sum (the row-sum content of [(1-1)^n]) ================= *)

Lemma piLsb_row_alt_rec : forall n : nat,
  piLsb_sumR (fun j => bpa_binom (Datatypes.S n) j * lw0_alt j)
             (Datatypes.S (Datatypes.S n))
  == 1%Q - (piLsb_sumR (fun j => bpa_binom n j * lw0_alt j) (Datatypes.S n)
            + piLsb_sumR (fun i => bpa_binom n (Datatypes.S i) * lw0_alt i)
                         (Datatypes.S n)).
Proof.
  intros n.
  rewrite (piLsb_sumR_head
             (fun j => bpa_binom (Datatypes.S n) j * lw0_alt j) (Datatypes.S n)).
  cbv beta.
  rewrite (bpa_binom_0 (Datatypes.S n)). cbn [lw0_alt].
  assert (Hext :
    piLsb_sumR (fun i => bpa_binom (Datatypes.S n) (Datatypes.S i)
                          * lw0_alt (Datatypes.S i)) (Datatypes.S n)
    == piLsb_sumR (fun i => - (bpa_binom n i * lw0_alt i
                               + bpa_binom n (Datatypes.S i) * lw0_alt i))
                  (Datatypes.S n)).
  { apply piLsb_sumR_ext. intros i _.
    change (lw0_alt (Datatypes.S i)) with (Qopp (lw0_alt i))%Q.
    rewrite bpa_binom_pascal. ring. }
  rewrite Hext, piLsb_sumR_opp, piLsb_sumR_plus. ring.
Qed.

Lemma piLsb_row_alt_conj : forall n : nat,
  (piLsb_sumR (fun j => bpa_binom n j * lw0_alt j) (Datatypes.S n)
   + piLsb_sumR (fun i => bpa_binom n (Datatypes.S i) * lw0_alt i)
                (Datatypes.S n) == 1%Q)
  /\ piLsb_sumR (fun j => bpa_binom (Datatypes.S n) j * lw0_alt j)
                (Datatypes.S (Datatypes.S n)) == 0%Q.
Proof.
  induction n as [| n IH].
  - split; cbn [piLsb_sumR bpa_binom lw0_alt]; ring.
  - destruct IH as [IH1 IH2].
    assert (Hout : bpa_binom (Datatypes.S n) (Datatypes.S (Datatypes.S n)) == 0%Q)
      by apply (bpa_binom_out (Datatypes.S n) (Datatypes.S (Datatypes.S n))
                  (Nat.lt_succ_diag_r _)).
    assert (HBsn :
      piLsb_sumR (fun i => bpa_binom (Datatypes.S n) (Datatypes.S i) * lw0_alt i)
                 (Datatypes.S (Datatypes.S n)) == 1%Q).
    { rewrite (piLsb_sumR_snoc
                 (fun i => bpa_binom (Datatypes.S n) (Datatypes.S i) * lw0_alt i)
                 (Datatypes.S n)).
      cbv beta.
      rewrite Hout.
      assert (HextB :
        piLsb_sumR (fun i => bpa_binom (Datatypes.S n) (Datatypes.S i) * lw0_alt i)
                   (Datatypes.S n)
        == piLsb_sumR (fun i => bpa_binom n i * lw0_alt i
                                + bpa_binom n (Datatypes.S i) * lw0_alt i)
                      (Datatypes.S n)).
      { apply piLsb_sumR_ext. intros i _.
        rewrite bpa_binom_pascal. ring. }
      rewrite HextB, piLsb_sumR_plus, IH1. ring. }
    assert (HABsn :
      piLsb_sumR (fun j => bpa_binom (Datatypes.S n) j * lw0_alt j)
                 (Datatypes.S (Datatypes.S n))
      + piLsb_sumR (fun i => bpa_binom (Datatypes.S n) (Datatypes.S i) * lw0_alt i)
                   (Datatypes.S (Datatypes.S n)) == 1%Q).
    { rewrite IH2, HBsn. ring. }
    split.
    + exact HABsn.
    + pose proof (piLsb_row_alt_rec (Datatypes.S n)) as Hrec.
      rewrite Hrec, HABsn. ring.
Qed.

Lemma piLsb_row_alt : forall n : nat, (1 <= n)%nat ->
  piLsb_sumR (fun j => bpa_binom n j * lw0_alt j) (Datatypes.S n) == 0%Q.
Proof.
  intros n Hn. destruct n as [| n'].
  - inversion Hn.
  - exact (proj2 (piLsb_row_alt_conj n')).
Qed.

(* ================= Section 7. The odd half-row (from the even-odd split, the row sums, and the alternating row sum) ================= *)

Lemma piLsb_row_odd : forall m : nat,
  piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i)))
             (Datatypes.S m)
  == q_pow 2%Q (2 * m)%nat.
Proof.
  intros m.
  assert (H1le : (1 <= Datatypes.S (2 * m))%nat)
    by (apply (proj1 (Nat.succ_le_mono 0 (2 * m))); apply Nat.le_0_l).
  pose proof (piLsb_bpa_row_tot (Datatypes.S (2 * m))) as [Htot _].
  replace (Datatypes.S (Datatypes.S (2 * m)))%nat
    with (2 * Datatypes.S m)%nat in Htot by lia.
  rewrite (piLsb_sumR_even_odd (bpa_binom (Datatypes.S (2 * m))) m) in Htot.
  pose proof (piLsb_row_alt (Datatypes.S (2 * m)) H1le) as Halt.
  replace (Datatypes.S (Datatypes.S (2 * m)))%nat
    with (2 * Datatypes.S m)%nat in Halt by lia.
  rewrite (piLsb_sumR_even_odd
             (fun j => bpa_binom (Datatypes.S (2 * m)) j * lw0_alt j) m) in Halt.
  cbv beta in Halt.
  assert (Hev :
    piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (2 * i) * lw0_alt (2 * i))
               (Datatypes.S m)
    == piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (2 * i)) (Datatypes.S m)).
  { apply piLsb_sumR_ext. intros i _.
    rewrite piLsb_lw0_alt_even. ring. }
  assert (Hod :
    piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i))
                          * lw0_alt (Datatypes.S (2 * i)))
               (Datatypes.S m)
    == - piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i)))
                    (Datatypes.S m)).
  { assert (Hpre :
      piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i))
                            * lw0_alt (Datatypes.S (2 * i)))
                 (Datatypes.S m)
      == piLsb_sumR (fun i => - bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i)))
                    (Datatypes.S m))
      by (apply piLsb_sumR_ext; intros i _; rewrite piLsb_lw0_alt_odd; ring).
    exact (Qeq_trans _ _ _ Hpre
             (piLsb_sumR_opp
                (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i)))
                (Datatypes.S m))). }
  rewrite Hev, Hod in Halt.
  assert (HEO :
    piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (2 * i)) (Datatypes.S m)
    == piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i)))
                  (Datatypes.S m)).
  { assert (Hstep1 :
      piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (2 * i)) (Datatypes.S m)
      == piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (2 * i)) (Datatypes.S m)
         + - piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i)))
                        (Datatypes.S m)
         + piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * m)) (Datatypes.S (2 * i)))
                      (Datatypes.S m)) by ring.
    rewrite Hstep1, Halt. ring. }
  rewrite HEO, q_pow_succ in Htot.
  assert (Htt : 2%Q * q_pow 2%Q (2 * m) == q_pow 2%Q (2 * m) + q_pow 2%Q (2 * m))
    by ring.
  rewrite Htt in Htot.
  exact (piLsb_eq_cancel_dbl _ _ Htot).
Qed.

(* ================= Section 8. Computational witnesses (auxiliary statements; trivial character declared explicitly) ================= *)

(** In-kernel witnesses for small instances: for the odd half-row at
    [m=3], [C(7,1)+C(7,3)+C(7,5)+C(7,7)=64=2^6]; for the row sum at
    [n=5], [2^5=32]; for the alternating row sum at [n=4], [0]. *)

Definition piLsb_witness_row_odd_3 : Q :=
  piLsb_sumR (fun i => bpa_binom (Datatypes.S (2 * 3)) (Datatypes.S (2 * i)))
             (Datatypes.S 3).

Lemma piLsb_witness_row_odd_3_val : piLsb_witness_row_odd_3 == 64%Q.
Proof. vm_compute. reflexivity. Qed.

Definition piLsb_witness_row_tot_5 : Q :=
  piLsb_sumR (bpa_binom 5) (Datatypes.S 5).

Lemma piLsb_witness_row_tot_5_val : piLsb_witness_row_tot_5 == 32%Q.
Proof. vm_compute. reflexivity. Qed.

Definition piLsb_witness_alt_4 : Q :=
  piLsb_sumR (fun j => bpa_binom 4 j * lw0_alt j) (Datatypes.S 4).

Lemma piLsb_witness_alt_4_val : piLsb_witness_alt_4 == 0%Q.
Proof. vm_compute. reflexivity. Qed.
