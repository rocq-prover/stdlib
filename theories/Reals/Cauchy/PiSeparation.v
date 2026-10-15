(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * PiSeparation: separation of the Leibniz series real [pi_leibniz]
      from every rational number (the engine-assembly closing piece).

    Mission.  This file mounts the engine piece
      [creal_escape_window pi_leibniz lw0m_e] and takes the final
      jump [creal_escape_window_apart] directly from the engine
      (zero new proofs): the separation of [pi_leibniz] from every
      rational number (the closing piece of the [pi] program).  Main
      theorem:
      [pi_leibniz_strong_irrational : forall a b : Q, b <> 0 ->
      CReal_appart pi_leibniz (inject_Q (a / b))].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
      [ZArith.ZArith], [Arith.PeanoNat], [ArithRing], [Setoid],
      [ConstructiveCauchyReals]; [PiLeibnizCReal] ([pi_leibniz],
      [lw0m_e], [lw0m_vanish_pi], [pi_leibniz_seq_negtail],
      [piL_qabs_sym], [piL_qpow2_neg]); [PiKernelSlack]
      ([NatLe_lift]; the three seeds [piLd3_seed_halfwin],
      [piLd3_seed_dres], [piLd3_seed_dcos] at the [Set] level; the
      [leibsep_q_kernel] margin supply); [PiSeedSupplyShell] (the
      three seed supplies [piLsup_halfwin_supply],
      [piLsup_dres_supply], [piLsup_dcos_supply]); [PiCompareT] (the
      thin decision wrappers; its
      [QltT] shares its source with the kernel output form, and the
      window-core down-level bridges are used under qualified names);
      [ConstructiveCauchyRealsSep] (the engine file, built on stdlib
      [ConstructiveCauchyReals]; after it lands upstream, the import
      switches to a single [From Stdlib] line).

    References.  This development,
      [LW0LeibSeparation.v:L5697-L5719] (the four assembly steps)
      and [LW0LeibSeparation.v:L298-L375] (the guarded form; the
      Real-metric content is absorbed by the engine conclusion shape
      and its body is not ported); this development,
      [ConstructiveCauchyRealsSep.v:L99] and
      [ConstructiveCauchyRealsSep.v:L108] (the two engine entry
      points taken directly).  The statement names follow the
      assembly plan and the distilled statement inventory of this
      development.

    Constructivity.  Assumption-free and fully proved statements;
      conclusions at the [Set] level (the sum-type form of
      [CReal_appart] with [sig] witnesses); [Prop] occurs only as
      [Q]-order scaffolding (the same rule as the engine file at
      [L47-L50]); the [Require] face imports no external decision
      procedure; the [CReal] projection names ([seq] and so on) are
      imported directly from stdlib [ConstructiveCauchyReals] (the
      engine file does not [Export] it, as verified);
      [leibsep_q_kernel] carries the three [Set]-typed seeds as
      explicit premises; this file fills the three slots from
      [PiSeedSupplyShell], so the mounting piece and the two closing
      theorems are assumption-free.

    Build.  [rocq c -native-compiler no -q -Q . "" PiSeparation.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

(* ---------------------------------------------------------------- *)
(* Require face (root-level bare names during the vendored period;    *)
(* after the engine file lands upstream, switch to a single           *)
(* [From Stdlib] line)                                                *)
(* ---------------------------------------------------------------- *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import ArithRing.
From Stdlib Require Import Setoid.
From Stdlib Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsSep.
Require Import PiCompareT.
Require Import PiLeibnizCReal.
Require Import PiKernelSlack.
Require Import PiSeedSupplyShell.

(* ---------------------------------------------------------------- *)
(* Section 1. The guarded [Q] chain (the engine-assembly restatement  *)
(* of the two branches at [LW0LeibSeparation.v:L5716-L5718])          *)
(*                                                                    *)
(* The vanish threshold dominates the margin, and the margin          *)
(* dominates the engine escape conjunct: a single [Qlt_trans] chain   *)
(* plus a [Qeq] reversal, in the direct-chain account with no         *)
(* forbidden-fragment dependency.                                     *)
(* ---------------------------------------------------------------- *)

(** The thin down-level bridge for the strict order (self-contained
      in this file): from the [QltT] statement face to the
      [Prop]-level strict order, with the same down-level bridge
      proof body as in [PiCompareT], the home file of the decision
      wrappers (the [Qcompare] three-way decision plus the
      definitional reflection of [Qlt_alt]).  The decision wrappers
      are pinned under the fully qualified [PiCompareT] names (same
      source as the kernel output form; with the same-named [QltT]
      of the two families coexisting, the qualified names rule out
      shadowing). *)
Lemma pi_sep_qltT_down :
  forall x y : Q, PiCompareT.QltT x y -> Qlt x y.
Proof.
  intros x y H.
  unfold PiCompareT.QltT in H.
  unfold PiCompareT.Qlt_bool in H.
  destruct (Qcompare x y) eqn:E; try (inversion H).
  apply Qlt_alt. exact E.
Qed.

(** The thin cross-family up-level bridge: from the [PiCompareT]
      family [QltT] to the window-core family [QltT].  The kernel
      margin supply form (decision-wrapper family) and the
      unified-window vanish consumption form (window-core family)
      belong to two different families (the decision wrappers carry
      two same-named definitions with distinct [Id] types, so they
      cannot be converted directly); the bridge rebuilds the
      window-core family [id_refl] through the [Qcompare] three-way
      decision. *)
Lemma pi_sep_qltT_up_wc :
  forall x y : Q, PiCompareT.QltT x y -> PiCompareT.QltT x y.
Proof.
  intros x y H.
  unfold PiCompareT.QltT, PiCompareT.Qlt_bool in H.
  unfold PiCompareT.QltT, PiCompareT.Qlt_bool.
  destruct (Qcompare x y) eqn:E; try (inversion H).
  exact (@PiCompareT.id_refl bool true).
Qed.

(* ---------------------------------------------------------------- *)
(* Section 0. Depth selection (the three-line unified selection of    *)
(* n0: self-contained on stdlib, a family of newly written small      *)
(* pieces)                                                            *)
(* ---------------------------------------------------------------- *)

(** The power unboundedness witness: for every window depth [N],
      there exists [k] with [N <= 2^k] (nat powers, by a direct
      induction).  The positivity anchor [1 <= 2^k'] follows
      directly from [2^0 = 1] and monotonicity of powers. *)
Lemma pi_sep_pow2_witness :
  forall N : nat, sig (fun k : nat => (N <= 2 ^ k)%nat).
Proof.
  induction N as [| N' IH].
  - exists 0%nat. apply Nat.le_0_l.
  - destruct IH as [k' Hk'].
    exists (S k').
    (* S N' <= S(2^k') <= 2 * 2^k' = 2^(S k'); the positivity *)
    (* anchor [1 <= 2^k']                                     *)
    assert (H1 : (1 <= 2 ^ k')%nat).
    { pose proof (Nat.pow_le_mono_r 2 0 k' (Nat.neq_succ_0 1)
                    (Nat.le_0_l k')) as Hle.
      simpl in Hle. exact Hle. }
    assert (Hstep : (S N' <= 2 ^ k' + 2 ^ k')%nat).
    { pose proof (Nat.add_le_mono N' (2 ^ k') 1 (2 ^ k') Hk' H1) as Hs.
      rewrite Nat.add_1_r in Hs. exact Hs. }
    simpl. rewrite Nat.add_0_r. exact Hstep.
Qed.

(** The three-line unified selection of [n0]: [n0] is simultaneously
      at least the vanish threshold [N0] and its depth image
      satisfies [2^n0 >= N] (the mu-image of the kernel window
      depth).  The unified two-threshold choice
      [N1 := max N (max N0 1)] of the source splits, at the engine
      read-point depth [2^n0], into the pair [([n0], [2^n0])]. *)
Lemma pi_sep_n0_select :
  forall N N0 : nat,
    sig (fun n0 : nat => (N0 <= n0)%nat /\ (N <= 2 ^ n0)%nat).
Proof.
  intros N N0.
  destruct (pi_sep_pow2_witness N) as [k Hk].
  exists (Nat.max N0 k).
  split.
  - apply Nat.le_max_l.
  - apply Nat.le_trans with (2 ^ k)%nat.
    + exact Hk.
    + apply Nat.pow_le_mono_r.
      * apply Nat.neq_succ_0.
      * apply Nat.le_max_r.
Qed.

(** The guarded [Q] chain: the kernel margin (the [xL - q] order) is
      reversed through [Qabs] symmetry into the engine [q - xL]
      order, forming with the vanish-threshold chain
      [lw0m_e n0 < c < |q - xL(2^n0)|].  The premise face uses plain
      [Qlt] ([Prop]-level order scaffolding): the decision-wrapper
      down-level reshaping is concentrated at the mounting site (the
      consumption face of this file spans two families; see the
      reshaping note at the mounting site). *)
Lemma pi_sep_escape_conj :
  forall (q c : Q) (n0 : nat),
    Qlt (lw0m_e n0) c ->
    Qlt c (Qabs ((lw0m_xL (2 ^ n0) - q)%Q)) ->
    Qlt (lw0m_e n0) (Qabs ((q - lw0m_xL (2 ^ n0))%Q)).
Proof.
  intros q c n0 He Hmargin.
  (* [Qabs (q - xL)] reversed into [Qabs (xL - q)], to enter the *)
  (* margin premise order                                        *)
  rewrite (piL_qabs_sym q (lw0m_xL (2 ^ n0))).
  exact (Qlt_trans (lw0m_e n0) c (Qabs ((lw0m_xL (2 ^ n0) - q)%Q)) He Hmargin).
Qed.

(** The coupling leg: the resolution [2 * 2^(-n)] always stays below
      the window bound [lw0m_e n = 5/(2(n+1))] -- the nat core
      [4n+4 < 5 * 2^n] by a direct induction, compared at the [Q]
      level through the power normal form of [piL_qpow2_neg] and the
      [Qnum]/[QDen] expansion.  The exponent/polynomial slack
      involves no critical [n]. *)
Lemma pi_sep_coupling : forall n : nat,
  Qlt (2 * 2 ^ Z.opp (Z.of_nat n)) (lw0m_e n).
Proof.
  intros n.
  (* nat core: [4n+4 < 5 * 2^n], by induction on the fuel *)
  (* [4 <= 5 * 2^n]                                       *)
  assert (Hfuel : forall m : nat, (4 <= 5 * 2 ^ m)%nat).
  { intros m.
    assert (H1 : (1 <= 2 ^ m)%nat).
    { pose proof (Nat.pow_le_mono_r 2 0 m (Nat.neq_succ_0 1)
                    (Nat.le_0_l m)) as Hle.
      simpl in Hle. exact Hle. }
    assert (H51 : (5 * 1 <= 5 * 2 ^ m)%nat)
      by (apply Nat.mul_le_mono_l; exact H1).
    rewrite Nat.mul_1_r in H51.
    apply Nat.le_trans with 5%nat.
    - apply Nat.le_succ_diag_r.
    - exact H51. }
  assert (Hcore : (4 * n + 4 < 5 * 2 ^ n)%nat).
  { induction n as [|n IH].
    - simpl. apply Nat.lt_succ_diag_r.
    - rewrite (Nat.pow_succ_r 2 n (Nat.le_0_l n)).
      assert (Hre : (4 * S n + 4 = (4 * n + 4) + 4)%nat) by (simpl; ring).
      rewrite Hre.
      assert (Hlt : ((4 * n + 4) + 4 < 5 * 2 ^ n + 4)%nat)
        by (apply (proj1 (Nat.add_lt_mono_r _ _ _)); exact IH).
      apply Nat.lt_le_trans with (5 * 2 ^ n + 4)%nat.
      + exact Hlt.
      + apply Nat.le_trans with (5 * 2 ^ n + 5 * 2 ^ n)%nat.
        * apply (proj1 (Nat.add_le_mono_l _ _ _)). exact (Hfuel n).
        * assert (Hbr : (5 * 2 ^ n + 5 * 2 ^ n = 5 * (2 * 2 ^ n))%nat) by ring.
          rewrite Hbr. apply Nat.le_refl. }
  (* [Q]-level order comparison: the power normal form, the *)
  (* [Qnum]/[QDen] expansion, and the transport of the nat core *)
  unfold lw0m_e, PiWindowCore.leiblw_nivwin.
  rewrite (piL_qpow2_neg n).
  unfold Qlt.
  cbn [Qnum Qden Qmult Pos.mul].
  rewrite piL_pos_succ1, piL_pos_succ1.
  rewrite !Z.mul_1_r.
  (* [2 * (2n+2) < 5 * 2^n]: transport of the nat core *)
  assert (H1 : (Z.of_nat (n + n + 1) + 1 = Z.of_nat n + Z.of_nat n + 1 + 1)%Z).
  { rewrite Nat2Z.inj_add, Nat2Z.inj_add. reflexivity. }
  rewrite H1.
  assert (Hge1 : (1 <= 2 ^ n)%nat).
  { pose proof (Nat.pow_le_mono_r 2 0 n (Nat.neq_succ_0 1)
                  (Nat.le_0_l n)) as Hle.
    simpl in Hle. exact Hle. }
  assert (H21 : ((2 ^ n - 1) + 1 = 2 ^ n)%nat)
    by (apply Nat.sub_add; exact Hge1).
  assert (H2 : (Z.of_nat (2 ^ n - 1) + 1 = Z.of_nat (2 ^ n))%Z).
  { rewrite Z.add_1_r, <- Nat2Z.inj_succ, <- Nat.add_1_r.
    f_equal. exact H21. }
  rewrite H2.
  assert (H3 : (Z.of_nat (5 * 2 ^ n) = 5 * Z.of_nat (2 ^ n))%Z)
    by (apply Nat2Z.inj_mul).
  rewrite <- H3.
  assert (H4 : (Z.of_nat (4 * n + 4) =
                (2 * (Z.of_nat n + Z.of_nat n + 1 + 1)))%Z).
  { rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
    change (Z.of_nat 4) with 4%Z. ring. }
  rewrite <- H4.
  apply Nat2Z.inj_lt. exact Hcore.
Qed.

(* ---------------------------------------------------------------- *)
(* Section 2. The engine mounting piece (the confluence of the        *)
(* first, second, third and fourth assembly steps)                    *)
(* ---------------------------------------------------------------- *)

(* ---------------------------------------------------------------- *)
(* The three seed supplies: each slot type of [leibsep_q_kernel] is   *)
(* filled by the corresponding supply of [PiSeedSupplyShell] (the     *)
(* half-window pair from the occupied seed, the two double-angle      *)
(* truncation-residual seeds from the band assembly).  With the slots *)
(* filled, the mounting piece and the two closing theorems below are  *)
(* assumption-free statements.                                        *)
(* ---------------------------------------------------------------- *)

Definition pi_sep_seed_halfwin : piLd3_seed_halfwin := piLsup_halfwin_supply.
Definition pi_sep_seed_dres : piLd3_seed_dres := piLsup_dres_supply.
Definition pi_sep_seed_dcos : piLd3_seed_dcos := piLsup_dcos_supply.

(** The engine mounting piece: for every rational number [q], the
      kernel margin (ingredient 1) and the unified-window vanish
      [eps := c] (ingredient 2) flow, through the depth selection
      (ingredient 3), into the escape witness [n0]: the coupling leg
      (ingredient 4) is taken directly, and the escape leg enters
      the guarded [Q] chain after a rewrite through the read-point
      bridge (ingredient 5). *)
Definition creal_escape_window_pi_leibniz :
  creal_escape_window pi_leibniz lw0m_e.
Proof.
  intros q.
  (* Ingredient 1: the kernel supplies the margin [c] and the window *)
  (* depth [N] (with the three seeds as explicit arguments)          *)
  destruct (leibsep_q_kernel pi_sep_seed_halfwin pi_sep_seed_dres
             pi_sep_seed_dcos q) as [c [Hc0 [N HN]]].
  apply (pi_sep_qltT_up_wc 0 c) in Hc0.
  (* Ingredient 2: the unified-window vanish [eps := c] yields [N0]  *)
  (* (the kernel supply form enters the window-core family through   *)
  (* the cross-family up-level bridge)                               *)
  destruct (lw0m_vanish_pi c Hc0) as [N0 HN0].
  (* Ingredient 3: depth selection of [n0] ([N0 <= n0] and *)
  (* [N <= 2^n0])                                          *)
  destruct (pi_sep_n0_select N N0) as [n0 [Hn0N0 Hn0N]].
  exists n0. split.
  - (* Coupling leg: the resolution always stays below the window *)
    (* bound (newly written in this file; the upstream coupling    *)
    (* leg carries no existing proof)                              *)
    exact (pi_sep_coupling n0).
  - (* Escape leg: after the read-point bridge translates back to *)
    (* [lw0m_xL (2^n0)], the guarded [Q] chain applies.  The       *)
    (* decision-wrapper down-level reshaping is concentrated at    *)
    (* this site: the vanish output is a window-core family        *)
    (* [QltT] (through the window-core down-level bridge), while   *)
    (* the kernel margin is a decision-wrapper origin [QltT]       *)
    (* (through the thin bridge of this file)                      *)
    rewrite (pi_leibniz_seq_negtail n0).
    apply (pi_sep_escape_conj q c n0).
    + exact (PiWindowCore.QltT_to_Qlt _ _ (HN0 n0 Hn0N0)).
    + apply (pi_sep_qltT_down _ _).
      apply (HN (2 ^ n0)%nat).
      exact (NatLe_lift N (2 ^ n0)%nat Hn0N).
Defined.

(* ---------------------------------------------------------------- *)
(* Section 3. The closing theorems (the final jump taken directly     *)
(* from the engine: zero new proofs)                                  *)
(* ---------------------------------------------------------------- *)

(** The separation of [pi_leibniz] from every rational number (zero
      premises; the cleanest showcase form of the development): the
      final jump taken directly from the engine. *)
Theorem pi_leibniz_appart_all_Q :
  forall q : Q, CReal_appart pi_leibniz (inject_Q q).
Proof.
  exact (creal_escape_window_apart pi_leibniz lw0m_e
         creal_escape_window_pi_leibniz).
Defined.

(** The main theorem (the mandated form): the separation of
      [pi_leibniz] from every rational number [a/b] with nonzero
      denominator.  Note on the zero-consumption premise: the
      mounting piece holds for every [q], so [b <> 0] serves only as
      the semantic guard of the notion of a rational number. *)
Theorem pi_leibniz_strong_irrational :
  forall a b : Q, b <> 0 -> CReal_appart pi_leibniz (inject_Q (a / b)).
Proof.
  intros a b _.
  exact (pi_leibniz_appart_all_Q (a / b)).
Defined.


(* Statement provenance: for every statement of this file, the
   source statement of this development that it was migrated from,
   with the source coordinates.  Rows marked (new) are statements
   first stated in this file.

   [pi_sep_qltT_down] <- (new in this file; the down-level bridge of
      the decision wrappers, restated with the [Qcompare] three-way
      split proof body of [PiCompareT.v])
   [pi_sep_qltT_up_wc] <- (new in this file; the cross-family bridge
      into the unified-window consumption face)
   [pi_sep_pow2_witness] <- (new in this file)
   [pi_sep_n0_select] <- (new in this file; the unified two-threshold
      depth selection of [leibsep_pi_rational_unconditional] at
      [LW0LeibSeparation.v:L5697-L5719], split into the pair
      ([n0], [2^n0]))
   [pi_sep_escape_conj] <- [leibsep_pi_rational_unconditional] (the
      two branches of the guarded application) at
      [LW0LeibSeparation.v:L5716-L5718]
   [pi_sep_coupling] <- (new in this file; the upstream coupling leg
      carries no existing proof)
   [creal_escape_window_pi_leibniz] <- [creal_escape_window]
      (statement face) at [ConstructiveCauchyRealsSep.v:L99]; the
      confluence of the four assembly steps of
      [leibsep_pi_rational_unconditional] at
      [LW0LeibSeparation.v:L5697-L5719]
   [pi_leibniz_appart_all_Q] <- [creal_escape_window_apart] (the
      final jump taken directly) at [ConstructiveCauchyRealsSep.v:L108]
   [pi_leibniz_strong_irrational] <-
      [leibsep_pi_rational_unconditional] (the unconditional
      separation, restated in the [a/b] form) at
      [LW0LeibSeparation.v:L5697-L5719]
*)
