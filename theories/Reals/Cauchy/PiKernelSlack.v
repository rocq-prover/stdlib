(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Kernel-slack restatements of the Leibniz [pi] bounds at the [Q] level

    Mission.  This file is the kernel-slack piece of the Leibniz [pi]
    program: a [Q]-level restatement of the three [pi] bounds of the
    kernel chain and of the endpoint-gap slot on the geometric side
    (first segment: the three [sigT] witness triples, the pointwise
    restatement of the endpoint-gap slot, and the two pointwise
    bounds), together with the thirteen [Q]-level definitions of
    [LW0PiIrrational] (second segment: the differential-algebra base
    of [qpoly] and the [Q]-level construction of the [Wb]/[sin]/[F]
    and Niven polynomials, with no [Real] type entering any
    conclusion).  The [lp_*]/[lw0m_xL]/[QltT]/[NatLe]/[qpoly]
    families keep their source names; the [piL_*] family is new at
    the [Q] level.  Two companion pieces close the file: the bridge
    [qleT'_plus_compat] (a thin right-monotone addition bridge for
    [QleT'], same-named and same-shaped as its source) and the
    companion base of thin bridges for the rational image and for
    reciprocal comparison (the carrier closure of the window-budget
    assembly family).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [QArith.Qround], [ZArith.ZArith], [Arith.PeanoNat], [Setoid],
    [Morphisms], [setoid_ring.ArithRing]; [PiCompareT] (the thin [Q]
    decision wrappers: [Id]/[QltT]/[QleT']); [PiLeibnizCReal] (the
    [Q]-level [lp]/[lw0m] family).  The [Require] face imports no
    forbidden fragment: no external decision procedure.

    References.  This development: [S01_BaseRing.v:L46-L100],
    [S02_CauchyComplete.v:L50-L607], [S03_QExp.v:L36-L923],
    [S10_KVQuantTrig.v:L1209-L9372], [LW0PiIrrational.v:L48-L9679],
    [LW0LeibSeparation.v:L67-L5623], [PiEnvelope.v:L921] (source
    coordinates of the migrated statements; the decision wrappers
    themselves live in [PiCompareT], and the five Leibniz vertex
    definitions in Section 1 of [PiLeibnizCReal]).

    Constructivity.  Statements at the [Set] level ([QltT] as the
    reflected form of [Id], [NatLe] as the reflected form of
    [Nat.leb], [sigT] witnesses, the Set-level product connective
    [And]); assumption-free and fully proved, with no
    non-constructive principles; within proofs, [Qlt]/[Qle] facts
    serve as scaffolding, and concrete constant comparisons close
    through [Qeq]/[Z.lt] conversion chains.

    Build.  [rocq c -native-compiler no -q -Q . "" PiKernelSlack.v]
    compiles cleanly (exit 0); the first eight bytes of the artifact
    are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

(* Merged-segment note.  Six segments are mounted after the base body at
   their separator lines: the double-angle identity bundle, the remainder
   bundle, the absolute-value reduction piece, the prerequisite bundle, the
   double-index synthesis bundle, and the Leibniz separation core (source
   file names and digests are recorded in the separator lines themselves).
   The [Require] face below additionally imports [QArith.Qminmax], so the
   dependency list above extends by [QArith.Qminmax].  The mission account
   of the six mounted segments is kept in the block
   that follows. *)

(*
   Merged-segment mission ledger (the source file name and digest of each
   segment are recorded in the separator note line at the head of that
   segment):
   Segment 1, the identity bundle -- the stratification of the partial
   sums of the sin/cos double-angle identities and the Pythagorean
   identity (with explicit truncation residual terms), the quadruple-angle
   composite stratification, the substitution interface at the pi_L window
   points, and the residual factor control bounds.
   Segment 2, the remainder bundle -- factor control bounds for the
   residuals of the sin/cos Taylor partial sums: term-level and
   partial-sum-level absolute value bounds, an explicit per-term majorant
   recursion for the residuals, and three master bounds.
   Segment 3, the reduction piece -- the reduction bound for the vanishing
   vertex factor: |C-S| <= |C^2-S^2| (under the premise 1 <= C+S), with a
   minimal companion interface for consuming the vertex zero anchor.
   Segment 4, the synthesis premise bundle -- an explicit pure-Q chain
   dominating power tails by factorial tails, the geometric decay of the
   Taylor terms, tail sums dominated by the first omitted term, the
   half-power witness, the uniform Cauchy face of the partial sums, and
   the Cauchy face of the double-angle residual majorant series.
   Segment 5, the two-index synthesis bundle -- the two-index vanishing
   synthesis of the sin/cos partial sums at the window points (three
   explicit seed slots carried at the Set level, plus the identity
   gathering and order bookkeeping auxiliaries).
   Segment 6, the separation kernel -- the Leibniz series separation
   kernel [leibsep_q_kernel]: for every rational q it provides a positive
   distance witness c and a threshold N such that every sample point
   [lw0m_xL m] beyond N stays at distance more than c from q; the proof
   chain runs: the two triangular-window vanishing pieces (carried by the
   three seed premises) -> the tail rescaling [caps_scaled] -> the margin
   assembly. *)
From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround.
From Stdlib Require Import QArith.Qminmax.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import setoid_ring.ArithRing.
Require Import PiCompareT.
Require Import PiLeibnizCReal.

(* ============================================================ *)
(* Section 0. The [Set]-level base ([Id]/[QltT]/[QleT'] carried by the *)
(* same-named, same-shaped copies in [PiCompareT])  *)
(* ============================================================ *)

(* The Set-level product connective (the stdlib [And] lives in [Prop]; *)
(* the product form [A*B] used here is isomorphic to the kernel *)
(* statement face) *)
Definition And (A B : Set) : Set := A * B.
(* The [nat] order reflected at the [Set] level: the [leb] decision in *)
(* identity form *)
Definition NatLe (n m : nat) : Set := Id (Nat.leb n m) true.
(* ---- Fully constructive argument bridge: [NatLe] <-> [(<=)%nat] ---- *)
Lemma NatLe_drop : forall n m : nat, NatLe n m -> (n <= m)%nat.
Proof.
  intros n m H.
  unfold NatLe in H.
  destruct (Nat.leb n m) eqn:E.
  - apply (proj1 (Nat.leb_le n m)). exact E.
  - inversion H.
Qed.

Lemma NatLe_lift : forall n m : nat, (n <= m)%nat -> NatLe n m.
Proof.
  intros n m H.
  unfold NatLe.
  destruct (Nat.leb n m) eqn:E.
  - reflexivity.
  - exfalso.
    apply (proj1 (Nat.leb_gt n m)) in E.
    exact (proj2 (Nat.nle_gt n m) E H).
Qed.
(* ============================================================ *)
(* Section 1. Thin [Q] decision wrappers (the three definitions       *)
(* [Qlt_bool]/[QltT]/[QleT'] are carried by the same-named, same-     *)
(* shaped copies in [PiCompareT]; this file provides only the bridge  *)
(* family)                                                            *)
(* ============================================================ *)

(* This file does not carry its own definition bodies for
   [Id]/[Qlt_bool]/[QltT]: they are carried by the same-named,
   same-shaped copies under [Require Import PiCompareT] (the three
   local-segment definitions were merged into [PiCompareT] with zero
   change to the statement face). *)

Lemma QltT_to_Qlt : forall x y : Q, QltT x y -> Qlt x y.
Proof.
  intros x y H.
  unfold QltT in H.
  unfold Qlt_bool in H.
  destruct (Qcompare x y) eqn:E; try (inversion H).
  apply Qlt_alt. exact E.
Qed.

Lemma Qlt_to_QltT : forall x y : Q, Qlt x y -> QltT x y.
Proof.
  intros x y H.
  unfold QltT, Qlt_bool.
  destruct (Qcompare x y) eqn:E.
  - (* Eq branch: [x == y] contradicts the strict order *)
    exfalso.
    apply (Qlt_irrefl y).
    assert (Heq : x == y) by (apply Qeq_alt; exact E).
    rewrite Heq in H.
    exact H.
  - (* Lt branch: the decision reflects directly *)
    reflexivity.
  - (* Gt branch: [y < x] contradicts [x < y] *)
    exfalso.
    apply (Qlt_irrefl x).
    assert (Hyx : y < x) by (apply Qgt_alt; exact E).
    eapply Qlt_trans.
    exact H.
    exact Hyx.
Qed.
(* ---- Non-strict order bridge family: [QleT'] <-> [Qle] ([QleT'] is *)
(* the same-named piece of [PiCompareT]; [Qle_bool] is the stdlib *)
(* native form) ---- *)
Lemma QleT'_to_Qle : forall x y : Q, QleT' x y -> Qle x y.
Proof.
  intros x y H.
  unfold QleT' in H.
  destruct (Qle_bool x y) eqn:E.
  - apply (proj1 (Qle_bool_iff x y)). exact E.
  - inversion H.
Qed.

Lemma Qle_to_QleT' : forall x y : Q, Qle x y -> QleT' x y.
Proof.
  intros x y H.
  assert (E : Qle_bool x y = true) by (apply (proj2 (Qle_bool_iff x y)); exact H).
  unfold QleT'. rewrite E. apply id_refl.
Qed.

Lemma qleT'_refl : forall x : Q, QleT' x x.
Proof.
  intro x. apply Qle_to_QleT'. apply Qle_refl.
Qed.

Lemma qleT'_trans : forall x y z : Q, QleT' x y -> QleT' y z -> QleT' x z.
Proof.
  intros x y z H1 H2. apply Qle_to_QleT'.
  apply (Qle_trans x y z).
  - apply QleT'_to_Qle. exact H1.
  - apply QleT'_to_Qle. exact H2.
Qed.

Lemma qeq_le : forall x y : Q, x == y -> Qle x y.
Proof.
  intros x y H.
  unfold Qle, Qeq in *.
  rewrite H.
  apply Z.le_refl.
Qed.
(* Auxiliary lemma: if [0 <= y], then [x <= x + y] *)
Lemma Qle_plus_nonneg_r : forall x y, 0 <= y -> x <= x + y.
Proof.
  intros x y Hy.
  exact (Qle_trans x (x + 0) (x + y)
    (qeq_le x (x + 0) (Qeq_sym (x + 0) x (Qplus_0_r x)))
    (Qplus_le_compat x x 0 y (Qle_refl x) Hy)).
Qed.

Lemma qleT'_plus_nonneg_rT : forall x y : Q, QleT' 0 y -> QleT' x (x + y).
Proof.
  intros x y H. apply Qle_to_QleT'.
  apply Qle_plus_nonneg_r. apply QleT'_to_Qle. exact H.
Qed.

Lemma qeq_leT' : forall a b : Q, a == b -> QleT' a b.
Proof.
  intros a b H. apply Qle_to_QleT'. exact (qeq_le a b H).
Qed.
(* Addition is monotone (a thin monotone-addition bridge on the *)
(* two-premise direct chain of [QleT']) *)
Lemma qleT'_plus_compat : forall a b c d : Q,
  QleT' a b -> QleT' c d -> QleT' (a + c) (b + d).
Proof.
  intros a b c d Hab Hcd.
  exact (Qle_to_QleT' _ _
           (Qplus_le_compat a b c d (QleT'_to_Qle _ _ Hab)
              (QleT'_to_Qle _ _ Hcd))).
Qed.
(* The thin monotone-addition bridge; the proof bodies of the
   shore-side chains below use it directly. *)

(* ============================================================ *)
(* Section 2. The Leibniz vertices (the five definitions              *)
(* [lp_a]/[lp_pair]/[lp_odd]/[lp_four]/[lw0m_xL] are imported from    *)
(* Section 1 of [PiLeibnizCReal] via [Require] -- same names, same    *)
(* shapes, zero change to the statement face; this file sets up no    *)
(* local copies and takes [PiLeibnizCReal] as the unique source)      *)
(* ============================================================ *)

(* ============================================================ *)
(* Section 3. Order inequalities on the partial sums (proof faces     *)
(* are direct [QArith] lemma chains throughout)                       *)
(* ============================================================ *)

(* [Q] tool lemmas (the reciprocal-comparison lemma [q_le_div_le]
   and its dependencies) *)
Lemma q_neq_of_lt : forall x : Q, Qlt 0 x -> ~ (x == 0).
Proof.
  intros x Hx H. exact (Qlt_not_eq 0 x Hx (Qeq_sym x 0 H)).
Qed.

Lemma Qle_div_same_denom : forall a b e : Q,
  Qlt 0 e -> Qle a b -> Qle (a / e) (b / e).
Proof.
  intros a b e He Hab.
  unfold Qdiv.
  exact (Qmult_le_compat_r a b (/ e) Hab
    (Qinv_le_0_compat e (Qlt_le_weak 0 e He))).
Qed.

Lemma q_le_div_le : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qle (a * d) (c * b) -> Qle (a / b) (c / d).
Proof.
  intros a b c d Hb Hd Hle.
  apply (Qle_trans _ ((a * d) / (b * d)) _).
  - apply qeq_le.
    field; split; try (apply q_neq_of_lt; assumption).
  - apply (Qle_trans _ ((c * b) / (b * d)) _).
    + apply (Qle_div_same_denom (a * d) (c * b) (b * d)).
      * apply Qmult_lt_0_compat. exact Hb. exact Hd.
      * exact Hle.
    + apply qeq_le.
      field; split; try (apply q_neq_of_lt; assumption).
Qed.
(* Concrete positive-denominator form: [0 < (2n+1)#1] (direct [Nat2Z] *)
(* chain) *)
Lemma q_lt_0_odd_den : forall n : nat, Qlt 0 ((Z.of_nat (2 * n + 1)) # 1)%Q.
Proof.
  intro n.
  unfold Qlt. cbn. rewrite !Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_lt 0 (2 * n + 1))).
  rewrite Nat.add_1_r.
  exact (Nat.lt_0_succ (2 * n)).
Qed.
(* [a] is antitone (the [<=] form): [k <= j] implies
   [1/(2j+1) <= 1/(2k+1)] *)
Lemma sc_lpa_decr_le : forall k j : nat, (k <= j)%nat -> Qle (lp_a j) (lp_a k).
Proof.
  intros k j Hkj.
  unfold lp_a.
  apply (q_le_div_le 1 ((Z.of_nat (2 * j + 1)) # 1)%Q
                       1 ((Z.of_nat (2 * k + 1)) # 1)%Q).
  - exact (q_lt_0_odd_den j).
  - exact (q_lt_0_odd_den k).
  - (* Cross-multiplication: [1*d_k <= 1*d_j] *)
    setoid_replace (1 * ((Z.of_nat (2 * k + 1)) # 1)%Q)
      with (((Z.of_nat (2 * k + 1)) # 1)%Q * 1) by (apply Qmult_comm).
    setoid_replace (1 * ((Z.of_nat (2 * j + 1)) # 1)%Q)
      with (((Z.of_nat (2 * j + 1)) # 1)%Q * 1) by (apply Qmult_comm).
    apply (Qmult_le_compat_r ((Z.of_nat (2 * k + 1)) # 1)%Q
                             ((Z.of_nat (2 * j + 1)) # 1)%Q 1).
    + unfold Qle. cbn. rewrite !Z.mul_1_r.
      apply (proj1 (Nat2Z.inj_le (2 * k + 1) (2 * j + 1))).
      rewrite !Nat.add_1_r.
      exact (proj1 (Nat.succ_le_mono (2 * k) (2 * j))
               (Nat.mul_le_mono_l k j 2 Hkj)).
    + apply Qlt_le_weak. unfold Qlt. reflexivity.
Qed.

Lemma sc_lpa_nonneg : forall k : nat, Qle 0 (lp_a k).
Proof.
  intro k.
  unfold lp_a.
  apply Qlt_le_weak.
  apply (Qmult_lt_0_compat 1 (Qinv ((Z.of_nat (2 * k + 1)) # 1)%Q)).
  - unfold Qlt. reflexivity.
  - apply Qinv_lt_0_compat.
    exact (q_lt_0_odd_den k).
Qed.

Lemma sc_lp_pair_nonneg : forall j : nat, Qle 0 (lp_pair j).
Proof.
  intro j.
  unfold lp_pair.
  apply (proj1 (Qle_minus_iff (lp_a (2 * j + 1)) (lp_a (2 * j)))).
  apply sc_lpa_decr_le.
  rewrite Nat.add_1_r.
  exact (Nat.le_succ_diag_r (2 * j)).
Qed.

Lemma sc_lp_odd_mono : forall m : nat, Qle (lp_odd m) (lp_odd (Datatypes.S m)).
Proof.
  intro m.
  change (Qle (lp_odd m) (lp_odd m + lp_pair (Datatypes.S m))).
  exact (Qle_plus_nonneg_r (lp_odd m) (lp_pair (Datatypes.S m))
           (sc_lp_pair_nonneg (Datatypes.S m))).
Qed.

Lemma sc_lp_odd_chain : forall m n : nat, (m <= n)%nat ->
  Qle (lp_odd m) (lp_odd n).
Proof.
  intros m n Hmn.
  induction Hmn as [| n' Hmn' IH].
  - apply Qle_refl.
  - apply (Qle_trans _ (lp_odd n') _).
    + exact IH.
    + apply sc_lp_odd_mono.
Qed.
(* Auxiliary: [S n <= n] is impossible (direct [Nat.nle_gt] chain) *)
Lemma nat_le_Sn_n_absurd : forall n : nat, ~ (S n <= n)%nat.
Proof.
  intro n.
  intro H.
  exact (proj2 (Nat.nle_gt (S n) n) (Nat.lt_succ_diag_r n) H).
Qed.
(* The even-sum decreases: [E_m := lp_odd m + a_{2m+2}] with
   [E_{S m} <= E_m] *)
Lemma sc_lp_ev_decr : forall m : nat,
  Qle (lp_odd (Datatypes.S m) + lp_a (2 * Datatypes.S m + 2))
      (lp_odd m + lp_a (2 * m + 2)).
Proof.
  intro m.
  change (Qle (lp_odd m + lp_pair (Datatypes.S m) + lp_a (2 * Datatypes.S m + 2))
              (lp_odd m + lp_a (2 * m + 2))).
  replace (2 * Datatypes.S m + 2)%nat with (2 * m + 4)%nat
    by (rewrite Nat.mul_succ_r; rewrite <- Nat.add_assoc; reflexivity).
  replace (2 * Datatypes.S m)%nat with (2 * m + 2)%nat
    by (symmetry; apply Nat.mul_succ_r).
  apply (Qle_trans _ (lp_odd m + lp_a (2 * m + 2) + (lp_a (2 * m + 4) - lp_a (2 * m + 3))) _).
  - apply qeq_le.
    unfold lp_pair.
    replace (2 * Datatypes.S m)%nat with (2 * m + 2)%nat
      by (symmetry; apply Nat.mul_succ_r).
    replace (2 * m + 2 + 1)%nat with (2 * m + 3)%nat
      by (rewrite !Nat.add_succ_r; rewrite !Nat.add_0_r; reflexivity).
    ring.
  - apply (Qle_trans _ (lp_odd m + lp_a (2 * m + 2) + 0) _).
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * (* [a_{2m+4} - a_{2m+3} <= 0] *)
        apply (Qle_trans _ (- (lp_a (2 * m + 3) - lp_a (2 * m + 4))) _).
        -- apply qeq_le. ring.
        -- apply (Qopp_le_compat 0 (lp_a (2 * m + 3) - lp_a (2 * m + 4))).
           apply (proj1 (Qle_minus_iff (lp_a (2 * m + 4)) (lp_a (2 * m + 3)))).
           apply sc_lpa_decr_le.
           apply Nat.add_le_mono;
             [apply Nat.le_refl | apply Nat.le_le_succ_r; apply Nat.le_refl].
    + apply qeq_le. ring.
Qed.
(* The [S6] upper bound of [E_n] ([n >= 2]): [E_n <= E_2] *)
Lemma sc_lp_ev_le_s6 : forall n : nat, (2 <= n)%nat ->
  Qle (lp_odd n + lp_a (2 * n + 2)) (lp_odd 2 + lp_a 6).
Proof.
  induction n as [| n IH]; intros Hn.
  - exfalso. exact (Nat.nle_succ_0 1 Hn).
  - destruct n as [| n'].
    + exfalso. exact (nat_le_Sn_n_absurd 1 Hn).
    + destruct n' as [| n''].
      * (* [n = 2]: [E_2 <= E_2] *)
        apply Qle_refl.
      * (* [n >= 3]: [E_n <= E_{n-1} <= E_2] *)
        apply (Qle_trans _ (lp_odd (Datatypes.S (Datatypes.S n''))
                            + lp_a (2 * Datatypes.S (Datatypes.S n'') + 2)) _).
        -- apply (sc_lp_ev_decr (Datatypes.S (Datatypes.S n''))).
        -- apply IH.
           apply (proj1 (Nat.succ_le_mono 1 (S n''))).
           apply (proj1 (Nat.succ_le_mono 0 n'')).
           apply Nat.le_0_l.
Qed.
(* Upper bound for every [n]: [lp_odd n <= S6] with
   [S6 := lp_odd 2 + lp_a 6] *)
Lemma sc_lp_odd_le_s6 : forall n : nat, Qle (lp_odd n) (lp_odd 2 + lp_a 6).
Proof.
  intro n.
  destruct (Nat.leb 2 n) eqn:E2n.
  - apply Nat.leb_le in E2n.
    apply (Qle_trans _ (lp_odd n + lp_a (2 * n + 2)) _).
    + apply (Qle_plus_nonneg_r (lp_odd n) (lp_a (2 * n + 2))).
      apply sc_lpa_nonneg.
    + apply sc_lp_ev_le_s6. exact E2n.
  - apply Nat.leb_gt in E2n.
    assert (Hn2 : (n <= 2)%nat) by (exact (Nat.lt_le_incl n 2 E2n)).
    apply (Qle_trans _ (lp_odd 2) _).
    + apply sc_lp_odd_chain. exact Hn2.
    + apply (Qle_plus_nonneg_r (lp_odd 2) (lp_a 6)).
      apply sc_lpa_nonneg.
Qed.

Lemma sc_lp_four_nonneg : Qle 0 lp_four.
Proof.
  apply Qlt_le_weak. unfold Qlt, lp_four. reflexivity.
Qed.
(* Concrete value 1: [4*lp_odd 3 == 8/3 + 8/35 + 8/99 + 8/195]
   (closed by the [Qeq] conversion) *)
Lemma sc_lp_three_value : lp_four * lp_odd 3 == 8 / 3 + 8 / 35 + 8 / 99 + 8 / 195.
Proof.
  unfold lp_four, lp_odd, lp_pair, lp_a.
  unfold Qeq. reflexivity.
Qed.
(* Concrete comparison: [3 + 1/100 < 4*lp_odd 3] *)
Lemma sc_lp_three_margin : Qlt (3 + 1 / 100) (lp_four * lp_odd 3).
Proof.
  rewrite sc_lp_three_value.
  unfold Qlt. reflexivity.
Qed.
(* Concrete value 2: [4*S6 == 147916/45045]
   (with [S6 := lp_odd 2 + lp_a 6]) *)
Lemma sc_lp_six_value : lp_four * (lp_odd 2 + lp_a 6) == 147916 / 45045.
Proof.
  unfold lp_four, lp_odd, lp_pair, lp_a.
  unfold Qeq. reflexivity.
Qed.
(* The margin: [1/60 < 10/3 - 4*S6] ([2234/45045 > 1/60]) *)
Lemma sc_lp_six_margin : Qlt (1 / 60) ((10 / 3) - lp_four * (lp_odd 2 + lp_a 6)).
Proof.
  rewrite sc_lp_six_value.
  unfold Qlt. reflexivity.
Qed.
(* ============================================================ *)
(* Section 4. [Q]-level witnesses and pointwise restatements of the   *)
(* three [pi] bounds                                                  *)
(* ============================================================ *)

(* Pointwise upper bound: [n >= 2] implies
   [1/60 < 10/3 - 4*lp_odd n] (the [Q]-level form isomorphic to the
   lower-bound lemma) *)
Lemma piL_xL_under_ten_thirds : forall n : nat, (2 <= n)%nat ->
  QltT (1 / 60)%Q ((10 / 3)%Q - lw0m_xL n)%Q.
Proof.
  intro n.
  intro Hn.
  unfold lw0m_xL.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ ((10 / 3)%Q - lp_four * (lp_odd 2 + lp_a 6)) _).
  - exact sc_lp_six_margin.
  - apply Qplus_le_compat.
    + apply Qle_refl.
    + apply Qopp_le_compat.
      * setoid_replace (lp_four * lp_odd n) with (lp_odd n * lp_four)
          by (apply Qmult_comm).
        setoid_replace (lp_four * (lp_odd 2 + lp_a 6)) with ((lp_odd 2 + lp_a 6) * lp_four)
          by (apply Qmult_comm).
        apply (Qmult_le_compat_r (lp_odd n) (lp_odd 2 + lp_a 6) lp_four).
        -- exact (sc_lp_odd_le_s6 n).
        -- exact sc_lp_four_nonneg.
Qed.
(* Pointwise lower bound: [n >= 3] implies [1/100 < 4*lp_odd n - 3] *)
(* (the [pi_L]-side counterpart is [PiEnvelope.v:L921]) *)
Lemma piL_xL_over_three : forall n : nat, (3 <= n)%nat ->
  QltT (1 / 100)%Q ((lw0m_xL n - 3)%Q).
Proof.
  intro n.
  intro Hn.
  unfold lw0m_xL.
  apply Qlt_to_QltT.
  apply (Qlt_le_trans _ (lp_four * lp_odd 3 - 3) _).
  - apply (proj2 (Qlt_minus_iff (1 / 100)%Q (lp_four * lp_odd 3 - 3))).
    setoid_replace ((lp_four * lp_odd 3 - 3) - (1 / 100)%Q)
      with (lp_four * lp_odd 3 - (3 + (1 / 100)%Q)) by ring.
    apply (proj1 (Qlt_minus_iff (3 + (1 / 100)%Q) (lp_four * lp_odd 3))).
    exact sc_lp_three_margin.
  - apply Qplus_le_compat.
    + setoid_replace (lp_four * lp_odd 3) with (lp_odd 3 * lp_four)
        by (apply Qmult_comm).
      setoid_replace (lp_four * lp_odd n) with (lp_odd n * lp_four)
        by (apply Qmult_comm).
      apply (Qmult_le_compat_r (lp_odd 3) (lp_odd n) lp_four).
      * exact (sc_lp_odd_chain 3 n Hn).
      * exact sc_lp_four_nonneg.
    + apply Qle_refl.
Qed.
(* Witness triple one: the explicit witness of the upper bound by
   [10/3] on the [pi_L] side ([eg] is a positive [Q] constant plus
   the pointwise bound; this sits at the witness position of the
   geometric side of the source) *)
Definition piL_ten_thirds_supply :
  sigT (fun eg : Q => And (QltT 0 eg)
    (sigT (fun N0 : nat => forall n : nat, NatLe N0 n ->
      QltT eg ((10 / 3)%Q - lw0m_xL n)%Q))).
Proof.
  exists (1 / 60)%Q.
  split.
  - apply Qlt_to_QltT. unfold Qlt. reflexivity.
  - exists 2%nat.
    intros n Hn.
    apply piL_xL_under_ten_thirds.
    exact (NatLe_drop 2 n Hn).
Defined.
(* Witness triple two: the [el] slot, an alias of the same value (the
   witness is verbatim same-shaped as triple one).  The witness-triple
   shape matches [S02_CauchyComplete.v:L468] ([real_lt]); the
   conclusion face carries no [Real] type. *)
Definition piL_leibniz_ten_thirds_supply
  : sigT (fun el : Q => And (QltT 0 el)
      (sigT (fun N0 : nat => forall n : nat, NatLe N0 n ->
        QltT el ((10 / 3)%Q - lw0m_xL n)%Q)))
  := piL_ten_thirds_supply.
(* Witness triple three: the explicit witness of the lower bound [3]
   on the [pi_L] side *)
Definition piL_three_supply :
  sigT (fun e3 : Q => And (QltT 0 e3)
    (sigT (fun N3 : nat => forall n : nat, NatLe N3 n ->
      QltT e3 ((lw0m_xL n - 3)%Q)))).
Proof.
  exists (1 / 100)%Q.
  split.
  - apply Qlt_to_QltT. unfold Qlt. reflexivity.
  - exists 3%nat.
    intros n Hn.
    apply piL_xL_over_three.
    exact (NatLe_drop 3 n Hn).
Defined.
(* Pointwise restatement of the endpoint-gap slot: when
   [eps2 <= eg], the pointwise gap bound transports directly (the
   construction corresponds line by line to the source at
   [L5619-L5623]: [Qle_lt_trans eps2 eg] plus [QltT_to_Qlt]) *)
Lemma piL_hn0g2_under_ten_thirds :
  forall (eg eps2 : Q) (N0g : nat),
    (forall n : nat, NatLe N0g n -> QltT eg ((10 / 3)%Q - lw0m_xL n)%Q) ->
    Qle eps2 eg ->
    forall n : nat, NatLe N0g n -> QltT eps2 ((10 / 3)%Q - lw0m_xL n)%Q.
Proof.
  intros eg eps2 N0g HN0g Hep n Hn.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans eps2 eg _).
  - exact Hep.
  - apply QltT_to_Qlt.
    exact (HN0g n Hn).
Qed.
(* ============================================================ *)
(* Section 5. The thirteen [Q]-level definitions of [LW0PiIrrational] *)
(* -- the differential-algebra base and the [Q] tool lemmas           *)
(* ============================================================ *)

(* ---- The [Q]-polynomial base (coefficient lists, lowest degree
   first; the minimal carrier closure of the thirteen definitions) ---- *)
Definition QPoly := list Q.

Fixpoint qpoly_add (p q : QPoly) : QPoly :=
  match p with
  | nil => q
  | cons a p' =>
      match q with
      | nil => p
      | cons b q' => cons (a + b) (qpoly_add p' q')
      end
  end.

Fixpoint qpoly_scalar (a : Q) (p : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons b p' => cons (a * b) (qpoly_scalar a p')
  end.

Fixpoint qpoly_mul (p q : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons a p' =>
      qpoly_add (qpoly_scalar a q) (cons 0 (qpoly_mul p' q))
  end.
(* Evaluation: the Horner recursion (this file carries only the
   definition body; the evaluation-identity family is outside the
   thirteen-definition closure) *)
Fixpoint qpoly_eval (p : QPoly) (x : Q) : Q :=
  match p with
  | nil => 0
  | cons a p' => a + x * qpoly_eval p' x
  end.

Fixpoint qpoly_deriv (p : QPoly) : QPoly :=
  match p with
  | nil => nil
  | cons a p' => qpoly_add p' (cons 0 (qpoly_deriv p'))
  end.

Fixpoint qpoly_deriv_iter (n : nat) (p : QPoly) : QPoly :=
  match n with
  | 0 % nat => p
  | S m => qpoly_deriv (qpoly_deriv_iter m p)
  end.
(* Source notation alias: [qpoly] is notation for [QPoly] (the
   statement face keeps the source word form) *)
Abbreviation qpoly := QPoly.
(* ---- [Q] powers and factorial tools (the carrier closure of the
   [lw0_Wb]/[sin]/Niven families) ---- *)
Fixpoint q_pow (x : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => x * q_pow x m
  end.

Fixpoint q_fact (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => (Z.of_nat (Datatypes.S m) # 1) * q_fact m
  end.
(* The [Q] constant of a positive integer ([Z.of_nat (S m) # 1]) is
   always positive (a direct [QArith] chain: the [Nat2Z.inj_lt] bridge) *)
Lemma q_lt_0_succ_den : forall m : nat, Qlt 0 ((Z.of_nat (Datatypes.S m)) # 1)%Q.
Proof.
  intro m.
  unfold Qlt. cbn [Qnum Qden]. rewrite !Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S m))).
  exact (Nat.lt_0_succ m).
Qed.

Lemma q_fact_pos : forall n : nat, Qlt 0 (q_fact n).
Proof.
  induction n as [| m IH].
  - reflexivity.
  - apply Qmult_lt_0_compat.
    + apply q_lt_0_succ_den.
    + exact IH.
Qed.
(* ---- Alternating sign and positivity of powers (the carrier
   closure of the [Wb] family) ---- *)
(* The [Q]-level carrier of the alternating sign [(-1)^j]. *)
Fixpoint lw0_alt (j : nat) : Q :=
  match j with
  | Datatypes.O => 1%Q
  | Datatypes.S j' => Qopp (lw0_alt j')
  end.

Lemma lw0_q_pow_pos : forall (x : Q) (k : nat), QltT 0 x -> QltT 0 (q_pow x k).
Proof.
  intros x k Hx. induction k as [| k IH].
  - reflexivity.
  - apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    + apply QltT_to_Qlt. exact Hx.
    + apply QltT_to_Qlt. exact IH.
Qed.
(* [QltT 0 x] implies [QleT' 0 x] (a thin bridge from the strict
   order up to the non-strict order) *)
Lemma lw0_QltT_le : forall x : Q, QltT 0 x -> QleT' 0 x.
Proof. intros x H. apply Qle_to_QleT'. apply (Qlt_le_weak 0). apply QltT_to_Qlt. exact H. Qed.
(* ---- The closed Beta form of the [W] series, and positivity ---- *)
Definition lw0_Wb (b q : Q) (n j : nat) : Q :=
  q_pow b n * q_pow q (2*n + 2*j + 2) * q_fact (n + 2*j + 1) /
  (q_fact n * q_fact (2*j + 1) * q_fact (2*n + 2*j + 2)).

Lemma lw0_Wb_pos : forall (b q : Q) (n j : nat),
  QltT 0 b -> QltT 0 q -> QltT 0 (lw0_Wb b q n j).
Proof.
  intros b q n j Hb Hq.
  assert (Hnum : Qlt 0 (q_pow b n * q_pow q (2*n + 2*j + 2) * q_fact (n + 2*j + 1))).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat; apply QltT_to_Qlt;
        [ apply lw0_q_pow_pos; exact Hb | apply lw0_q_pow_pos; exact Hq ].
    - apply q_fact_pos. }
  assert (Hden : Qlt 0 (q_fact n * q_fact (2*j + 1) * q_fact (2*n + 2*j + 2))).
  { apply Qmult_lt_0_compat; [ apply Qmult_lt_0_compat; apply q_fact_pos | apply q_fact_pos ]. }
  unfold lw0_Wb, Qdiv. apply Qlt_to_QltT. apply Qmult_lt_0_compat.
  - exact Hnum.
  - apply Qinv_lt_0_compat. exact Hden.
Qed.
(* ---- Polynomial coefficient lists of the partial sums (carried by
   the sigma tables) ---- *)
Fixpoint lw0_sin_aux (j : nat) (acc : qpoly) : qpoly :=
  match j with
  | Datatypes.O => cons 0 (cons (q_pow (-1) 0 / q_fact 1)%Q acc)
  | Datatypes.S M =>
      lw0_sin_aux M
        (cons 0
           (cons (q_pow (-1) (Datatypes.S M)
                   / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q
              acc))
  end.

Definition lw0_sin_qp (N : nat) : qpoly := lw0_sin_aux N nil.
(* ---- The alternating-sum operator ([lw0_F f J = sum over j <= J of
   (-1)^j * f^(2j)], lowest degree first) ---- *)
Fixpoint lw0_F_aux (f : qpoly) (c : Q) (J : nat) : qpoly :=
  match J with
  | Datatypes.O => qpoly_scalar c f
  | Datatypes.S J' =>
      qpoly_add (lw0_F_aux f c J')
        (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
           (qpoly_deriv_iter (2 * Datatypes.S J') f))
  end.

Definition lw0_F (f : qpoly) (J : nat) : qpoly := lw0_F_aux f 1%Q J.
(* ---- The Niven polynomial family and its explicit indices ---- *)
(* The lowest-degree-first coefficient list of the monomial [t^m]:
   [t^0] is the constant-one list, and [t^(m+1)] is the [t^m] list
   multiplied by the linear list. *)
Fixpoint lw0_pi_mono (m : nat) : qpoly :=
  match m with
  | 0%nat => cons 1%Q nil
  | Datatypes.S m' => qpoly_mul (lw0_pi_mono m') (cons 0%Q (cons 1%Q nil))
  end.
(* The lowest-degree-first coefficient list of the binomial
   [(q - t)^n]: the list [(q; -1)] is multiplied in step by step. *)
Fixpoint lw0_pi_qminus_pow (q : Q) (n : nat) : qpoly :=
  match n with
  | 0%nat => cons 1%Q nil
  | Datatypes.S m =>
      qpoly_mul (lw0_pi_qminus_pow q m) (cons q (cons (-1)%Q nil))
  end.
(* The Niven scaling: the polynomial carrier of
   [f_n = (b^n / n!) * t^n * (q - t)^n]. *)
Definition lw0_niven_f (q b : Q) (n : nat) : qpoly :=
  qpoly_scalar (q_pow b n / q_fact n)
    (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)).
(* The explicit choice of [n]: [lw0_n_select b k = 22 + 2 * max k b]
   (always even, so [n >= 22] enters the factorial-dominance range) *)
Definition lw0_n_select (b k : nat) : nat := (22 + 2 * Nat.max k b)%nat.
(* The explicit index of the denominator datum [b]:
   [d0(b) = Z.to_nat (Z.succ (Qceiling (Qabs b)))] *)
Definition lw0_pi_d0_of (b : Q) : nat := Z.to_nat (Z.succ (Qceiling (Qabs b))).
(* ---- Slack-constant notations (the rational constants used on the
         statement face; only the notation bodies are kept here,
         with no dependency on any external decision procedure) ---- *)
Abbreviation S973 := (1 + (121 # 18) + (73205 # 5364))%Q.
(* ============================================================ *)
(* Section 6. Early-region [Q] micro-pieces and the shore-side order  *)
(* budget family (statements and proof bodies carried verbatim; the   *)
(* whole metric-side transport trampoline branch, the gap re-handoff  *)
(* pieces, the projection folding steps, and the real-equation        *)
(* unpacking layer stay outside this file's closure)                  *)
(* ============================================================ *)

(* ---- [Q] linear-order transport bridges (for two-way rewriting
   with [wd2]) ---- *)

Lemma leibsep_qlt_wd2 : forall a b c e : Q,
  a == c -> b == e -> Qlt a b -> Qlt c e.
Proof.
  intros a b c e Hac Hbe H.
  rewrite <- Hac. rewrite <- Hbe. exact H.
Qed.

Lemma leibsep_qle_wd2 : forall a b c e : Q,
  a == c -> b == e -> Qle a b -> Qle c e.
Proof.
  intros a b c e Hac Hbe H.
  rewrite <- Hac. rewrite <- Hbe. exact H.
Qed.

Lemma leibsep_qlt_minus : forall x y : Q, Qlt x y -> Qlt 0 (y - x).
Proof. intros x y H. exact (proj1 (Qlt_minus_iff x y) H). Qed.

Lemma leibsep_qlt_of_minus : forall x y : Q, Qlt 0 (y - x) -> Qlt x y.
Proof. intros x y H. exact (proj2 (Qlt_minus_iff x y) H). Qed.

Lemma leibsep_qle_minus : forall x y : Q, Qle x y -> Qle 0 (y - x).
Proof. intros x y H. exact (proj1 (Qle_minus_iff x y) H). Qed.

Lemma leibsep_qle_of_minus : forall x y : Q, Qle 0 (y - x) -> Qle x y.
Proof. intros x y H. exact (proj2 (Qle_minus_iff x y) H). Qed.

Lemma leibsep_qlt_1 : Qlt 0 1.
Proof. unfold Qlt. simpl. reflexivity. Qed.

Lemma leibsep_qlt_half : Qlt 0 (1 # 2).
Proof. unfold Qlt. simpl. reflexivity. Qed.

Lemma leibsep_qlt_half_1 : Qlt (1 # 2) 1.
Proof. unfold Qlt. simpl. reflexivity. Qed.
(* ---- Both-sides extraction of [Qabs] upper bounds (the dual piece
   of the [<=] form) ---- *)
Lemma leibsep_qabs_le_two : forall d t : Q,
  Qle (Qabs d) t -> And (QleT' d t) (QleT' (- t) d).
Proof.
  intros d t H.
  destruct (Qlt_le_dec d 0) as [Hd | Hd].
  - assert (Habs : Qabs d == (- d)%Q)
      by (apply Qabs_neg; apply Qlt_le_weak; exact Hd).
    rewrite Habs in H. split.
    + exact (Qle_to_QleT' _ _ (Qle_trans d (- d)%Q t
               (Qle_trans d 0 (- d)%Q (Qlt_le_weak d 0 Hd)
                  (Qopp_le_compat d 0 (Qlt_le_weak d 0 Hd))) H)).
    + exact (Qle_to_QleT' _ _ (leibsep_qle_wd2 (Qopp t) (Qopp (Qopp d)) (Qopp t) d
               (Qeq_refl (Qopp t)) (Qopp_involutive d)
               (Qopp_le_compat (- d)%Q t H))).
  - assert (Habs : Qabs d == d) by (apply Qabs_pos; exact Hd).
    rewrite Habs in H. split.
    + exact (Qle_to_QleT' _ _ H).
    + exact (Qle_to_QleT' _ _ (Qle_trans (- t)%Q 0 d
               (Qopp_le_compat 0 t (Qle_trans 0 d t Hd H)) Hd)).
Qed.
(* ---- Order reversal under negation for [Q] (the direct
   [Qopp_le_compat] chain) ---- *)
Lemma lw0_opp_le_swap : forall x y : Q, QleT' x y -> QleT' (Qopp y) (Qopp x).
Proof.
  intros x y H. apply Qle_to_QleT'.
  apply Qopp_le_compat. apply QleT'_to_Qle. exact H.
Qed.
(* ---- The two self-dominance pieces for [Abs] (the two-direction
   extraction cores) ---- *)
Lemma leibsep_abs_ge_self : forall x : Q, QleT' x (Qabs x).
Proof.
  intros x. apply (Qabs_case x (fun y => QleT' x y)).
  - intros _. apply qleT'_refl.
  - intros Hx0. apply (qleT'_trans x 0%Q (Qopp x)).
    + apply Qle_to_QleT'. exact Hx0.
    + apply (qleT'_trans (Qopp 0)%Q (Qopp x) (Qopp x)).
      * apply lw0_opp_le_swap. apply Qle_to_QleT'. exact Hx0.
      * apply qeq_leT'. ring.
Qed.

Lemma leibsep_abs_ge_opp : forall x : Q, QleT' (Qopp (Qabs x)) x.
Proof.
  intros x. apply (Qabs_case x (fun y => QleT' (Qopp y) x)).
  - intros Hx0. apply (qleT'_trans (Qopp x) (Qopp 0)%Q x).
    + apply lw0_opp_le_swap. apply Qle_to_QleT'. exact Hx0.
    + apply (qleT'_trans (Qopp 0)%Q 0%Q x).
      * apply qeq_leT'. ring.
      * apply Qle_to_QleT'. exact Hx0.
  - intros Hx0. apply qeq_leT'. ring.
Qed.
(* ---- Basic bridge micro-pieces: from [Qeq] to [Qle] ---- *)
Lemma leibsep_qeq_le : forall x y : Q, x == y -> x <= y.
Proof.
  intros x y H. rewrite H. apply Qle_refl.
Qed.
(* ---- The two Lipschitz summators (explicitly computable
   [Fixpoint]s) ---- *)
Fixpoint leibsep_abssum (B : Q) (n : nat) : Q :=
  match n with
  | 0%nat => q_pow B (2 * 0)%nat / q_fact (2 * 0)%nat
  | Datatypes.S m => leibsep_abssum B m
                     + (q_pow B (2 * Datatypes.S m)%nat / q_fact (2 * Datatypes.S m)%nat)
  end.

Fixpoint leibsep_abssum_cos (B : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 0
  | Datatypes.S m => leibsep_abssum_cos B m
                     + (q_pow B (Datatypes.S (2 * m))%nat / q_fact (Datatypes.S (2 * m))%nat)
  end.
(* ---- The shore clean-piece family (statement faces and proof
   bodies carried verbatim) ---- *)

(* The restatement piece of the C brick (renaming the atoms is the
   whole proof: the source proof face performs no unfold and no
   projection evaluation; all twelve occurrences of the source
   projection pointwise term are replaced by [lw0m_xL m0]; the proof
   body stays verbatim) *)
Lemma leibsep_shore_upper :
  forall (q W eps0 : Q) (m0 : nat),
    QleT' (Qabs ((lw0m_xL m0 - q)%Q)) W ->
    Qle (lw0m_xL m0) ((10 / 3)%Q - eps0)%Q ->
    QleT' W eps0 ->
    QleT' q (10 / 3)%Q.
Proof.
  intros q W eps0 m0 Hband Hpi HW.
  pose proof (QleT'_to_Qle _ _ Hband) as Hband'.
  pose proof (QleT'_to_Qle _ _ HW) as HW'.
  assert (Hneg : (q - lw0m_xL m0)%Q
                 == (-(lw0m_xL m0 - q))%Q) by ring.
  assert (Habsopp : Qabs ((q - lw0m_xL m0)%Q)
                    == Qabs ((lw0m_xL m0 - q)%Q)).
  { rewrite Hneg. apply Qabs_opp. }
  assert (Hz : ((10 / 3)%Q - eps0 + eps0)%Q == (10 / 3)%Q) by ring.
  assert (Hsplit : q == (lw0m_xL m0
                         + (q - lw0m_xL m0))%Q) by ring.
  assert (Hst1 : (lw0m_xL m0 + (q - lw0m_xL m0))%Q
                 <= (lw0m_xL m0
                     + Qabs ((lw0m_xL m0 - q)%Q))%Q).
  { apply (Qplus_le_compat (lw0m_xL m0) (lw0m_xL m0)
             (q - lw0m_xL m0)%Q
             (Qabs ((lw0m_xL m0 - q)%Q))).
    - apply Qle_refl.
    - apply (Qle_trans (q - lw0m_xL m0)%Q
               (Qabs ((q - lw0m_xL m0)%Q))
               (Qabs ((lw0m_xL m0 - q)%Q))).
      + exact (QleT'_to_Qle _ _ (leibsep_abs_ge_self
                                  (q - lw0m_xL m0)%Q)).
      + rewrite Habsopp. apply Qle_refl. }
  assert (Hst2 : (lw0m_xL m0
                  + Qabs ((lw0m_xL m0 - q)%Q))%Q
                 <= (lw0m_xL m0 + W)%Q).
  { apply (Qplus_le_compat (lw0m_xL m0) (lw0m_xL m0)
             (Qabs ((lw0m_xL m0 - q)%Q)) W).
    - apply Qle_refl.
    - exact Hband'. }
  assert (Hfin : (lw0m_xL m0 + W)%Q <= (10 / 3)%Q).
  { apply (Qle_trans _ ((10 / 3)%Q - eps0 + eps0)%Q).
    - apply (Qplus_le_compat (lw0m_xL m0)
               ((10 / 3)%Q - eps0)%Q W eps0).
      + exact Hpi.
      + exact HW'.
    - rewrite Hz. apply Qle_refl. }
  apply Qle_to_QleT'.
  rewrite Hsplit.
  apply (Qle_trans _
          (lw0m_xL m0
           + Qabs ((lw0m_xL m0 - q)%Q))%Q).
  - exact Hst1.
  - apply (Qle_trans _ (lw0m_xL m0 + W)%Q).
    + exact Hst2.
    + exact Hfin.
Qed.
(* The E brick: the window budget (the budget account of the
   vanishing branch, purely at the [Q] level; statement and proof
   body carried verbatim) *)
Lemma leibsep_shore_W_le : forall eN eps0 : Q,
  QltT eN (eps0 * (1 # 4))%Q ->
  QleT' (eN + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8)) + eN + (eps0 * (1 # 8)))%Q eps0.
Proof.
  intros eN eps0 H4.
  pose proof (QltT_to_Qlt eN (eps0 * (1 # 4))%Q H4) as H4'.
  assert (H2e : Qlt (eN + eN)%Q (eps0 * (1 # 4) + eps0 * (1 # 4))%Q)
    by exact (Qplus_lt_compat eN (eps0 * (1 # 4))%Q eN (eps0 * (1 # 4))%Q H4' H4').
  assert (H2lt : Qlt (2 * eN)%Q (eps0 * (1 # 2))%Q).
  { apply (leibsep_qlt_wd2 (eN + eN)%Q (eps0 * (1 # 4) + eps0 * (1 # 4))%Q
             (2 * eN)%Q (eps0 * (1 # 2))%Q).
    - ring.
    - ring.
    - exact H2e. }
  assert (Hstep : Qlt (2 * eN + eps0 * (1 # 2))%Q (eps0 * (1 # 2) + eps0 * (1 # 2))%Q).
  { apply (Qplus_lt_le_compat (2 * eN)%Q (eps0 * (1 # 2))%Q
             (eps0 * (1 # 2))%Q (eps0 * (1 # 2))%Q H2lt).
    apply Qle_refl. }
  apply Qle_to_QleT'.
  apply (Qle_trans _ (2 * eN + eps0 * (1 # 2))%Q).
  - apply leibsep_qeq_le. ring.
  - apply (Qle_trans _ (eps0 * (1 # 2) + eps0 * (1 # 2))%Q).
    + apply Qlt_le_weak. exact Hstep.
    + apply leibsep_qeq_le. ring.
Qed.
(* The F brick: from a strict-gap witness to a [Q] upper bound at
   the sequence points (pure [Q] abstraction; statement and proof
   body carried verbatim) *)
Lemma leibsep_shore_gap_upper : forall eps0 x y : Q,
  QltT eps0 (x - y)%Q -> Qle y (x - eps0)%Q.
Proof.
  intros eps0 x y H.
  pose proof (QltT_to_Qlt eps0 (x - y)%Q H) as Hq.
  assert (H1 : Qlt (eps0 + y)%Q ((x - y) + y)%Q)
    by exact (proj2 (Qplus_lt_l eps0 (x - y)%Q y) Hq).
  assert (H2 : Qlt (y + eps0)%Q x%Q).
  { apply (leibsep_qlt_wd2 (eps0 + y)%Q ((x - y) + y)%Q (y + eps0)%Q x%Q).
    - ring.
    - ring.
    - exact H1. }
  assert (H3 : Qlt (y + eps0)%Q ((x - eps0) + eps0)%Q).
  { apply (leibsep_qlt_wd2 (y + eps0)%Q x%Q (y + eps0)%Q ((x - eps0) + eps0)%Q).
    - apply Qeq_refl.
    - ring.
    - exact H2. }
  apply Qlt_le_weak.
  exact (proj1 (Qplus_lt_l y (x - eps0)%Q eps0) H3).
Qed.
(* ============================================================ *)
(* Section 7. Power/factorial difference closure and the sin/cos      *)
(* partial-sum face (power and factorial difference tools plus the    *)
(* two Lipschitz pieces; proof faces are direct [QArith] chains       *)
(* throughout)                                                        *)
(* ============================================================ *)

Lemma q_pow_succ : forall x n, q_pow x (Datatypes.S n) == x * q_pow x n.
Proof. intros. reflexivity. Qed.

Lemma q_fact_succ : forall k : nat, q_fact (Datatypes.S k) == (Z.of_nat (Datatypes.S k) # 1) * q_fact k.
Proof. intro k. reflexivity. Qed.

Lemma q_pow_abs : forall (x : Q) (n : nat), Qabs (q_pow x n) == q_pow (Qabs x) n.
Proof.
  intros x n. induction n as [| m IH]; simpl.
  - assert (H1 : Qabs (1%Q) == 1%Q) by (unfold Qabs; simpl; reflexivity).
    exact H1.
  - change (Qabs (x * q_pow x m) == Qabs x * q_pow (Qabs x) m).
    rewrite Qabs_Qmult.
    rewrite IH. reflexivity.
Qed.

Lemma q_pow_nonneg : forall (x : Q) (n : nat), Qle 0 x -> Qle 0 (q_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH]; simpl.
  - apply Qlt_le_weak. unfold Qlt. reflexivity.
  - apply Qmult_le_0_compat; [exact Hx | exact IH].
Qed.

Lemma q_pow_mono : forall (A B : Q) (n : nat),
  Qle 0 A -> Qle A B -> Qle (q_pow A n) (q_pow B n).
Proof.
  intros A B n HA HAB. induction n as [| m IH]; simpl.
  - exact (Qle_refl 1).
  - exact (Qmult_le_compat_nonneg A B (q_pow A m) (q_pow B m)
             (conj HA HAB) (conj (q_pow_nonneg A m HA) IH)).
Qed.

Lemma q_pow_wd : forall x y n, x == y -> q_pow x n == q_pow y n.
Proof.
  intros x y n Hxy. induction n as [| n IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite Hxy. reflexivity.
Qed.
(* The [nat]-successor literal identity: [(S k)#1 + 1 == (S(S k))#1] *)
Lemma q_succ_add : forall (k : nat),
  Qplus (Z.of_nat (Datatypes.S k) # 1) 1 == Z.of_nat (Datatypes.S (Datatypes.S k)) # 1.
Proof.
  intros k.
  unfold Qeq, Qplus, Qred. simpl.
  rewrite (Pos.mul_1_r (Pos.of_succ_nat k)).
  rewrite (Pos.mul_1_r (Pos.add (Pos.of_succ_nat k) 1)).
  rewrite (Pos.mul_1_r (Pos.succ (Pos.of_succ_nat k))).
  apply f_equal. apply Pos.add_1_r.
Qed.
(* The power-difference bound (in the [S n] form, no underflow) *)
Lemma q_pow_diff_bound : forall (x y B : Q) (n : nat),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (q_pow x (Datatypes.S n) - q_pow y (Datatypes.S n)))
      (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S n) # 1) (q_pow B n))).
Proof.
  intros x y B n HB Hx Hy.
  induction n as [| m IH].
  - (* [n = 0]: [|x^1 - y^1| = |x-y| <= |x-y| * (1#1 * B^0)] *)
    rewrite (q_pow_succ x 0), (q_pow_succ y 0).
    setoid_replace (q_pow x 0) with 1 by reflexivity.
    assert (Hxy : Qmult x 1 - Qmult y 1 == x - y) by ring.
    apply (Qle_trans _ (Qabs (x - y)) _).
    { apply qeq_le. apply (Qabs_wd (Qmult x 1 - Qmult y 1) (x - y)). exact Hxy. }
    { apply qeq_le. apply Qeq_sym. apply Qmult_1_r. }
  - (* [n = S m]: split [x*x^{Sm} - y*y^{Sm}], triangle plus the IH *)
    assert (Halg : q_pow x (Datatypes.S (Datatypes.S m)) - q_pow y (Datatypes.S (Datatypes.S m)) ==
                   x * (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)) + (x - y) * q_pow y (Datatypes.S m)).
    { simpl. ring. }
    setoid_rewrite Halg.
    apply (Qle_trans _ (Qabs (Qmult x (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m))) +
                        Qabs (Qmult (x - y) (q_pow y (Datatypes.S m)))) _).
    + apply Qabs_triangle.
    + apply (Qle_trans _ (Qplus (Qmult (Qabs x) (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m))))
                                (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m)))) _).
      * apply Qplus_le_compat.
        -- apply qeq_le. apply Qabs_Qmult.
        -- apply (Qle_trans _ (Qmult (Qabs (x - y)) (Qabs (q_pow y (Datatypes.S m)))) _).
           ++ apply qeq_le. apply Qabs_Qmult.
           ++ apply (Qmult_le_compat_nonneg (Qabs (x - y)) (Qabs (x - y))
                                            (Qabs (q_pow y (Datatypes.S m))) (q_pow B (Datatypes.S m))).
              ** split; [apply Qabs_nonneg | apply Qle_refl].
              ** split; [apply Qabs_nonneg | (rewrite q_pow_abs; apply q_pow_mono; [apply Qabs_nonneg | exact Hy])].
      * apply (Qle_trans _ (Qplus (Qmult B (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B m))))
                                  (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m)))) _).
        -- apply Qplus_le_compat.
           ++ apply (Qle_trans _ (Qmult B (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)))) _).
              ** apply (Qmult_le_compat_r (Qabs x) B (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)))).
                 --- exact Hx.
                 --- apply Qabs_nonneg.
              ** apply (Qmult_le_compat_nonneg B B
                                            (Qabs (q_pow x (Datatypes.S m) - q_pow y (Datatypes.S m)))
                                            (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B m)))).
                 --- split; [exact HB | apply Qle_refl].
                 --- split; [apply Qabs_nonneg | exact IH].
           ++ (* Second term: [|x-y|*B^{Sm} <= |x-y|*B^{Sm}] by [refl] *)
              apply Qle_refl.
        -- (* Algebra: [B*(|x-y|*(Sm#1*B^m)) + |x-y|*B^{Sm} == |x-y|*((S(S m))#1*B^{S m})] *)
           setoid_replace (Qmult B (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B m))))
             with (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B (Datatypes.S m)))).
           2: { assert (Hbs : q_pow B (Datatypes.S m) == B * q_pow B m) by apply q_pow_succ.
                setoid_rewrite Hbs. ring. }
           setoid_replace (Qplus (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S m) # 1) (q_pow B (Datatypes.S m))))
                                 (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S m))))
             with (Qmult (Qabs (x - y)) (Qmult (Qplus (Z.of_nat (Datatypes.S m) # 1) 1) (q_pow B (Datatypes.S m)))).
           2: ring.
           setoid_replace (Qmult (Qabs (x - y)) (Qmult (Qplus (Z.of_nat (Datatypes.S m) # 1) 1) (q_pow B (Datatypes.S m))))
             with (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1) (q_pow B (Datatypes.S m)))).
           2: { setoid_rewrite (q_succ_add m). reflexivity. }
           apply Qle_refl.
Qed.
(* Ratio cancellation: [((S k)#1*B^k) / ((S k)!) == B^k / (k!)] (the
   [Qmult_inv_r] positivity chain) *)
Lemma q_ratio_cancel_succ : forall (B : Q) (k : nat),
  Qmult (Qmult (Z.of_nat (Datatypes.S k) # 1) (q_pow B k))
        (Qinv (q_fact (Datatypes.S k)))
  == q_pow B k * Qinv (q_fact k).
Proof.
  intros B k.
  setoid_rewrite (q_fact_succ k).
  setoid_rewrite (Qinv_mult_distr (Z.of_nat (Datatypes.S k) # 1) (q_fact k)).
  setoid_replace (Qmult (Qmult (Z.of_nat (Datatypes.S k) # 1) (q_pow B k))
                        (Qmult (Qinv (Z.of_nat (Datatypes.S k) # 1)) (Qinv (q_fact k))))
    with (Qmult (Qmult (Qmult (Z.of_nat (Datatypes.S k) # 1) (Qinv (Z.of_nat (Datatypes.S k) # 1))) (q_pow B k)) (Qinv (q_fact k))).
  2: ring.
  rewrite (Qmult_inv_r (Z.of_nat (Datatypes.S k) # 1)).
  - ring.
  - apply q_neq_of_lt. apply q_lt_0_succ_den.
Qed.
(* ---- The sin/cos terms and partial sums (pure data face as [Q]
   [Fixpoint]s) ---- *)
Definition sin_term (j : nat) (x : Q) : Q :=
  q_pow (-1) j * (q_pow x (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))).
(* [cos_term j x := (-1)^j * x^{2j} / (2j)!] *)
Definition cos_term (j : nat) (x : Q) : Q :=
  q_pow (-1) j * (q_pow x (2 * j) / q_fact (2 * j)).

Fixpoint sin_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => sin_term 0%nat x
  | Datatypes.S m => sin_partial m x + sin_term (Datatypes.S m) x
  end.

Fixpoint cos_partial (n : nat) (x : Q) : Q :=
  match n with
  | 0%nat => cos_term 0%nat x
  | Datatypes.S m => cos_partial m x + cos_term (Datatypes.S m) x
  end.

Lemma sc_q_pow_one : forall j : nat, q_pow 1 j == 1.
Proof.
  induction j as [| j IH]; simpl.
  - reflexivity.
  - rewrite IH. ring.
Qed.

Lemma sc_abs_sign : forall j : nat, Qabs (q_pow (-1) j) == 1.
Proof.
  intro j.
  rewrite q_pow_abs.
  rewrite (q_pow_wd (Qabs (-1)) 1 j).
  - apply sc_q_pow_one.
  - unfold Qabs. simpl. reflexivity.
Qed.
(* The sin-term difference:
   [|sin_term j x - sin_term j y| <= |x-y| * B^{2j} / (2j)!] *)
Lemma sc_sin_term_diff : forall (x y B : Q) (j : nat),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (sin_term j x - sin_term j y))
      (Qmult (Qabs (x - y)) (q_pow B (2 * j) / q_fact (2 * j))).
Proof.
  intros x y B j HB Hx Hy.
  unfold sin_term.
  (* [sign*(x^{S(2j)}*inv f) - sign*(y^{S(2j)}*inv f) ==
     sign*((x^{S(2j)}-y^{S(2j)})*inv f)] *)
  assert (Halg : q_pow (-1) j * (q_pow x (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))) -
                  q_pow (-1) j * (q_pow y (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))) ==
                  q_pow (-1) j * ((q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))) *
                    Qinv (q_fact (Datatypes.S (2 * j))))).
  { unfold Qdiv. ring. }
  setoid_rewrite Halg.
  apply (Qle_trans _ (Qabs ((q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))) *
                            Qinv (q_fact (Datatypes.S (2 * j))))) _).
  - (* [|sign*t| <= |t|] (with [|sign| == 1]: the equation first, then [<=]) *)
    apply qeq_le.
    rewrite Qabs_Qmult.
    rewrite (sc_abs_sign j).
    ring.
  - apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                              (Qabs (Qinv (q_fact (Datatypes.S (2 * j)))))) _).
    + apply qeq_le. apply Qabs_Qmult.
    + apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                                (Qinv (q_fact (Datatypes.S (2 * j))))) _).
      * apply (Qmult_le_compat_nonneg
                 (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                 (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                 (Qabs (Qinv (q_fact (Datatypes.S (2 * j)))))
                 (Qinv (q_fact (Datatypes.S (2 * j))))).
        -- split; [apply Qabs_nonneg | apply Qle_refl].
        -- split.
           ++ apply Qabs_nonneg.
           ++ assert (Hinvpos : Qlt 0 (Qinv (q_fact (Datatypes.S (2 * j))))).
              { apply Qinv_lt_0_compat. apply q_fact_pos. }
              apply qeq_le.
              apply (Qabs_pos (Qinv (q_fact (Datatypes.S (2 * j))))
                              (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (2 * j)))) Hinvpos)).
      * apply (Qle_trans _ (Qmult (Qmult (Qabs (x - y))
                                         (Qmult (Z.of_nat (Datatypes.S (2 * j)) # 1) (q_pow B (2 * j))))
                                  (Qinv (q_fact (Datatypes.S (2 * j))))) _).
        -- apply (Qmult_le_compat_r
                   (Qabs (q_pow x (Datatypes.S (2 * j)) - q_pow y (Datatypes.S (2 * j))))
                   (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (2 * j)) # 1) (q_pow B (2 * j))))
                   (Qinv (q_fact (Datatypes.S (2 * j))))).
           ++ apply (q_pow_diff_bound x y B (2 * j)); assumption.
           ++ apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (2 * j))))).
              apply Qinv_lt_0_compat. apply q_fact_pos.
        -- (* [(|x-y|*((S(2j))#1*B^{2j})) / ((S(2j))!) == |x-y|*B^{2j} / ((2j)!)] *)
           setoid_replace (Qmult (Qmult (Qabs (x - y))
                                        (Qmult (Z.of_nat (Datatypes.S (2 * j)) # 1) (q_pow B (2 * j))))
                                 (Qinv (q_fact (Datatypes.S (2 * j)))))
             with (Qmult (Qabs (x - y))
                         (Qmult (Qmult (Z.of_nat (Datatypes.S (2 * j)) # 1) (q_pow B (2 * j)))
                                (Qinv (q_fact (Datatypes.S (2 * j)))))) by ring.
           rewrite (q_ratio_cancel_succ B (2 * j)).
           apply Qle_refl.
Qed.
(* The cos-term difference ([j = S m >= 1]):
   [|cos_term (S m) x - cos_term (S m) y| <=
   |x-y| * B^{S(2m)} / (S(2m))!] *)
Lemma sc_cos_term_diff : forall (x y B : Q) (m : nat),
  Qle 0 B -> Qle (Qabs x) B -> Qle (Qabs y) B ->
  Qle (Qabs (cos_term (Datatypes.S m) x - cos_term (Datatypes.S m) y))
      (Qmult (Qabs (x - y)) (q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)))).
Proof.
  intros x y B m HB Hx Hy.
  unfold cos_term.
  (* Reindexing the power: [2*(S m)] becomes [S(2m+1)] *)
  replace (2 * Datatypes.S m)%nat with (Datatypes.S (2 * m + 1))%nat
    by (rewrite Nat.mul_succ_r; rewrite <- Nat.add_1_r; rewrite <- Nat.add_assoc; reflexivity).
  assert (Halg : q_pow (-1) (Datatypes.S m) * (q_pow x (Datatypes.S (2 * m + 1)) / q_fact (Datatypes.S (2 * m + 1))) -
                  q_pow (-1) (Datatypes.S m) * (q_pow y (Datatypes.S (2 * m + 1)) / q_fact (Datatypes.S (2 * m + 1))) ==
                  q_pow (-1) (Datatypes.S m) * ((q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))) *
                    Qinv (q_fact (Datatypes.S (2 * m + 1))))).
  { unfold Qdiv. ring. }
  setoid_rewrite Halg.
  apply (Qle_trans _ (Qabs ((q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))) *
                            Qinv (q_fact (Datatypes.S (2 * m + 1))))) _).
  - apply qeq_le.
    rewrite Qabs_Qmult.
    rewrite (sc_abs_sign (Datatypes.S m)).
    ring.
  - apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                              (Qabs (Qinv (q_fact (Datatypes.S (2 * m + 1)))))) _).
    + apply qeq_le. apply Qabs_Qmult.
    + apply (Qle_trans _ (Qmult (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                                (Qinv (q_fact (Datatypes.S (2 * m + 1))))) _).
      * apply (Qmult_le_compat_nonneg
                 (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                 (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                 (Qabs (Qinv (q_fact (Datatypes.S (2 * m + 1)))))
                 (Qinv (q_fact (Datatypes.S (2 * m + 1))))).
        -- split; [apply Qabs_nonneg | apply Qle_refl].
        -- split.
           ++ apply Qabs_nonneg.
           ++ assert (Hinvpos : Qlt 0 (Qinv (q_fact (Datatypes.S (2 * m + 1))))).
              { apply Qinv_lt_0_compat. apply q_fact_pos. }
              apply qeq_le.
              apply (Qabs_pos (Qinv (q_fact (Datatypes.S (2 * m + 1))))
                              (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (2 * m + 1)))) Hinvpos)).
      * apply (Qle_trans _ (Qmult (Qmult (Qabs (x - y))
                                         (Qmult (Z.of_nat (Datatypes.S (2 * m + 1)) # 1) (q_pow B (2 * m + 1))))
                                  (Qinv (q_fact (Datatypes.S (2 * m + 1))))) _).
        -- apply (Qmult_le_compat_r
                   (Qabs (q_pow x (Datatypes.S (2 * m + 1)) - q_pow y (Datatypes.S (2 * m + 1))))
                   (Qmult (Qabs (x - y)) (Qmult (Z.of_nat (Datatypes.S (2 * m + 1)) # 1) (q_pow B (2 * m + 1))))
                   (Qinv (q_fact (Datatypes.S (2 * m + 1))))).
           ++ apply (q_pow_diff_bound x y B (2 * m + 1)); assumption.
           ++ apply (Qlt_le_weak 0 (Qinv (q_fact (Datatypes.S (2 * m + 1))))).
              apply Qinv_lt_0_compat. apply q_fact_pos.
        -- (* Regroup so that the ratio-cancel pattern becomes a direct subterm, then reindex *)
           setoid_replace (Qmult (Qmult (Qabs (x - y))
                                (Qmult (Z.of_nat (Datatypes.S (2 * m + 1)) # 1) (q_pow B (2 * m + 1))))
                         (Qinv (q_fact (Datatypes.S (2 * m + 1)))))
             with (Qmult (Qabs (x - y))
                         (Qmult (Qmult (Z.of_nat (Datatypes.S (2 * m + 1)) # 1) (q_pow B (2 * m + 1)))
                                (Qinv (q_fact (Datatypes.S (2 * m + 1)))))) by ring.
           rewrite (q_ratio_cancel_succ B (2 * m + 1)).
           replace (2 * m + 1)%nat with (Datatypes.S (2 * m))%nat
             by (rewrite Nat.add_1_r; reflexivity).
           apply Qle_refl.
Qed.
(* ---- The two pointwise-Lipschitz-on-partial-sums pieces (the
   slack cores) ---- *)
Lemma leibsep_sin_partial_lipschitz : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (sin_partial n x - sin_partial n y))
        (Qabs (x - y) * leibsep_abssum B n)%Q.
Proof.
  intros x y B n HB Hx Hy.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ HB) as HB'.
  pose proof (QleT'_to_Qle _ _ Hx) as Hx'.
  pose proof (QleT'_to_Qle _ _ Hy) as Hy'.
  induction n as [| n IH].
  - simpl. apply (sc_sin_term_diff x y B 0); assumption.
  - simpl sin_partial. simpl leibsep_abssum.
    apply (Qle_trans _ (Qabs (sin_partial n x - sin_partial n y)
                        + Qabs (sin_term (Datatypes.S n) x
                                - sin_term (Datatypes.S n) y))).
    + assert (Halg : (Qabs ((sin_partial n x + sin_term (Datatypes.S n) x)
                            - (sin_partial n y + sin_term (Datatypes.S n) y)))%Q ==
                     (Qabs ((sin_partial n x - sin_partial n y)
                            + (sin_term (Datatypes.S n) x
                               - sin_term (Datatypes.S n) y)))%Q)
        by (apply Qabs_wd; ring).
      rewrite Halg. apply Qabs_triangle.
    + assert (Heq : (Qabs (x - y) * leibsep_abssum B (Datatypes.S n))%Q ==
                    (Qabs (x - y) * leibsep_abssum B n
                     + Qabs (x - y)
                       * (q_pow B (2 * Datatypes.S n) / q_fact (2 * Datatypes.S n)))%Q)
        by (simpl; ring).
      rewrite Heq. apply Qplus_le_compat.
      * exact IH.
      * apply (sc_sin_term_diff x y B (Datatypes.S n)); assumption.
Qed.

Lemma leibsep_cos_partial_lipschitz : forall (x y B : Q) (n : nat),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (cos_partial n x - cos_partial n y))
        (Qabs (x - y) * leibsep_abssum_cos B n)%Q.
Proof.
  intros x y B n HB Hx Hy.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ HB) as HB'.
  pose proof (QleT'_to_Qle _ _ Hx) as Hx'.
  pose proof (QleT'_to_Qle _ _ Hy) as Hy'.
  induction n as [| n IH].
  - simpl leibsep_abssum_cos.
    assert (Hz : cos_term 0 x - cos_term 0 y == 0)
      by (unfold cos_term; simpl; ring).
    rewrite Hz. rewrite Qmult_0_r. apply Qle_refl.
  - simpl cos_partial. simpl leibsep_abssum_cos.
    apply (Qle_trans _ (Qabs (cos_partial n x - cos_partial n y)
                        + Qabs (cos_term (Datatypes.S n) x
                                - cos_term (Datatypes.S n) y))).
    + assert (Halg : (Qabs ((cos_partial n x + cos_term (Datatypes.S n) x)
                            - (cos_partial n y + cos_term (Datatypes.S n) y)))%Q ==
                     (Qabs ((cos_partial n x - cos_partial n y)
                            + (cos_term (Datatypes.S n) x
                               - cos_term (Datatypes.S n) y)))%Q)
        by (apply Qabs_wd; ring).
      rewrite Halg. apply Qabs_triangle.
    + assert (Heq : (Qabs (x - y) * leibsep_abssum_cos B (Datatypes.S n))%Q ==
                    (Qabs (x - y) * leibsep_abssum_cos B n
                     + Qabs (x - y)
                       * (q_pow B (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n))))%Q)
        by (simpl; ring).
      rewrite Heq. apply Qplus_le_compat.
      * exact IH.
      * apply (sc_cos_term_diff x y B n); assumption.
Qed.
(* ---- The rational-image thin-bridge family (the rational image of
   [nat] and the lifted order/addition/multiplication) ---- *)

Lemma qeq_imp_qle : forall a b : Q, a == b -> Qle a b.
Proof.
  intros a b Hab. unfold Qle, Qeq in *. destruct a, b. simpl in *. rewrite Hab. apply Z.le_refl.
Qed.

Lemma qeq_ltT : forall a b : Q, a == b -> QltT 0 a -> QltT 0 b.
Proof.
  intros a b Hab Ha. exact (Qlt_to_QltT _ _ (Qlt_le_trans 0 a b (QltT_to_Qlt _ _ Ha) (qeq_imp_qle _ _ Hab))).
Qed.

Lemma lw0_q_eq_le : forall x y : Q, x == y -> x <= y.
Proof.
  intros x y Hxy.
  unfold Qeq in Hxy. unfold Qle.
  rewrite Hxy. apply Z.le_refl.
Qed.

Definition lw0_q_of_nat (n : nat) : Q := (Z.of_nat n # 1)%Q.

Lemma lw0_q_of_nat_nonneg : forall n : nat, QleT' 0 (lw0_q_of_nat n).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden].
  rewrite !Z.mul_1_r. apply Zle_0_nat.
Qed.

Lemma lw0_q_of_nat_ge_one : forall n : nat, QleT' 1 (lw0_q_of_nat (Datatypes.S n)).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_le 1 (Datatypes.S n))).
  apply (proj1 (Nat.succ_le_mono 0 n)). apply Nat.le_0_l.
Qed.

Lemma lw0_q_of_nat_le_succ : forall n : nat,
  QleT' (lw0_q_of_nat n) (lw0_q_of_nat (Datatypes.S n)).
Proof.
  intro n. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden].
  rewrite !Z.mul_1_r. rewrite Nat2Z.inj_succ.
  apply Z.le_succ_diag_r.
Qed.

Lemma lw0_q_of_nat_le_add : forall a b : nat,
  QleT' (lw0_q_of_nat a) (lw0_q_of_nat (a + b)%nat).
Proof.
  intros a b. apply Qle_to_QleT'.
  unfold Qle, lw0_q_of_nat. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  apply (proj1 (Nat2Z.inj_le a (a + b)%nat)). apply Nat.le_add_r.
Qed.

Lemma lw0_q_of_nat_le_mono : forall a b : nat, (a <= b)%nat -> QleT' (lw0_q_of_nat a) (lw0_q_of_nat b).
Proof. intros a b H. apply Qle_to_QleT'. unfold lw0_q_of_nat, Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_r. exact (proj1 (Nat2Z.inj_le a b) H). Qed.

Lemma lw0_q_of_nat_succ : forall k : nat, lw0_q_of_nat (Datatypes.S k) == lw0_q_of_nat k + 1.
Proof.
  intro k. unfold lw0_q_of_nat, Qeq, Qplus. cbn [Qnum Qden Pos.mul].
  rewrite Nat2Z.inj_succ. rewrite !Z.mul_1_r. rewrite Z.add_1_r. reflexivity.
Qed.

Lemma lw0_q_of_nat_add : forall a b : nat,
  lw0_q_of_nat (a + b)%nat == lw0_q_of_nat a + lw0_q_of_nat b.
Proof.
  intros a b. unfold lw0_q_of_nat, Qeq, Qplus. cbn [Qnum Qden Pos.mul].
  rewrite Nat2Z.inj_add. rewrite !Z.mul_1_r. reflexivity.
Qed.

Lemma lw0_q_mult_le_l : forall c x y : Q, (0 <= c)%Q -> x <= y -> c * x <= c * y.
Proof.
  intros c x y Hc Hxy.
  apply (Qle_trans (c * x) (x * c)).
  - apply lw0_q_eq_le. apply Qmult_comm.
  - apply (Qle_trans (x * c) (y * c)).
    + apply Qmult_le_compat_r; [exact Hxy | exact Hc].
    + apply (Qle_trans (y * c) (c * y)).
      * apply lw0_q_eq_le. apply Qmult_comm.
      * apply Qle_refl.
Qed.
(* ---- The reciprocal-comparison bridge pieces (the nonzero carrier
   of denominator positivity and right cancellation of
   multiplication) ---- *)

Lemma lw0_pitS_qne0_of_pos : forall x : Q, QltT 0 x -> ~ (x == 0).
Proof.
  intros x H Hz. exact (Qlt_not_eq 0 x (QltT_to_Qlt 0 x H) (Qeq_sym x 0 Hz)).
Qed.

Lemma lw0_pitS_qof_add : forall a b : nat,
  lw0_q_of_nat (a + b)%nat == lw0_q_of_nat a + lw0_q_of_nat b.
Proof.
  intros a b. unfold lw0_q_of_nat, Qeq, Qplus. cbn [Qnum Qden Pos.mul].
  rewrite Nat2Z.inj_add. rewrite !Z.mul_1_r. reflexivity.
Qed.

Lemma lw0_pitS_qof_mul : forall a b : nat,
  lw0_q_of_nat (a * b)%nat == lw0_q_of_nat a * lw0_q_of_nat b.
Proof.
  intros a b. unfold lw0_q_of_nat, Qeq, Qmult. cbn [Qnum Qden Pos.mul].
  rewrite Nat2Z.inj_mul. rewrite !Z.mul_1_r. reflexivity.
Qed.

Lemma lw0_pitS_qmult_reg_r : forall x y z : Q,
  QltT 0 z -> QleT' (x * z) (y * z) -> QleT' x y.
Proof.
  intros x y z Hz0 H.
  assert (Hne : ~ (z == 0)) by (exact (lw0_pitS_qne0_of_pos z Hz0)).
  assert (E : ((y * z) * / z)%Q == y).
  { rewrite <- (Qmult_assoc y z (/ z)), (Qmult_inv_r z Hne), Qmult_1_r.
    reflexivity. }
  apply (qleT'_trans _ ((y * z) * / z)%Q).
  - apply (qleT'_trans _ ((x * z) * / z)%Q).
    + apply qeq_leT'.
      rewrite <- (Qmult_assoc x z (/ z)), (Qmult_inv_r z Hne), Qmult_1_r.
      reflexivity.
    + apply Qle_to_QleT'. apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ H).
      * apply (Qlt_le_weak 0). apply Qinv_lt_0_compat.
        apply QltT_to_Qlt. exact Hz0.
  - apply qeq_leT'. exact E.
Qed.
(* ---- The rounding carrier pieces of the pinned-bound denominator
   (absorption and positivity of the [d0] notation) ---- *)

Lemma lw0_pi_d0_absorb : forall b : Q,
  QltT 0 (Qabs b) -> QleT' (Qabs b) (lw0_q_of_nat (lw0_pi_d0_of b)).
Proof.
  intros b Hab.
  assert (Hbpos : Qlt 0 (Qabs b)) by (apply QltT_to_Qlt; exact Hab).
  assert (Hcq : Qle 0 (Qceiling (Qabs b) # 1)).
  { apply (Qle_trans 0 (Qabs b) (Qceiling (Qabs b) # 1)).
    - apply (Qlt_le_weak 0). exact Hbpos.
    - apply Qle_ceiling. }
  assert (Hcpos : (0 <= Qceiling (Qabs b))%Z).
  { unfold Qle in Hcq. cbn [Qnum Qden] in Hcq.
    rewrite !Z.mul_1_r in Hcq. exact Hcq. }
  apply Qle_to_QleT'.
  unfold lw0_pi_d0_of, lw0_q_of_nat.
  rewrite Z2Nat.id by (exact (Z.le_le_succ_r 0 (Qceiling (Qabs b)) Hcpos)).
  apply (Qle_trans (Qabs b) (Qceiling (Qabs b) # 1)
                   ((Z.succ (Qceiling (Qabs b))) # 1)).
  - apply Qle_ceiling.
  - unfold Qle. cbn [Qnum Qden]. rewrite !Z.mul_1_r. apply Z.le_succ_diag_r.
Qed.

Lemma lw0_pi_b_den_pos : forall q : Q, QltT 0 ((Zpos (Qden q) # 1)%Q).
Proof.
  intros q. destruct (Qden q); reflexivity.
Qed.
(* ============================================================ *)
(* Section. The termwise antiderivative core and the integration-by-  *)
(* parts family (a [qp] algebra extension: the pointwise-evaluation   *)
(* layer of the paired product)                                       *)
(* ============================================================ *)

(* Pointwise evaluation distributes over addition (list induction). *)
Lemma qpoly_eval_add : forall p q x,
  qpoly_eval (qpoly_add p q) x == qpoly_eval p x + qpoly_eval q x.
Proof.
  induction p as [|a p IH]; intros q x; simpl.
  - ring.
  - destruct q as [|b q]; simpl.
    + ring.
    + rewrite (IH q x); ring.
Qed.
(* Pointwise evaluation distributes over scalar multiplication. *)
Lemma qpoly_eval_scalar : forall a p x,
  qpoly_eval (qpoly_scalar a p) x == a * qpoly_eval p x.
Proof.
  intros a p x; induction p as [|b p IH]; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

(* The derivative of a nonempty list, evaluated pointwise: this is the    *)
(* Pointwise-evaluation form of the derivative at the cons layer:
   [P' = P + t*P'] (a list-representation identity). *)
Lemma qpoly_eval_deriv_cons : forall a p x,
  qpoly_eval (qpoly_deriv (cons a p)) x ==
  qpoly_eval p x + x * qpoly_eval (qpoly_deriv p) x.
Proof.
  intros a p x.
  change (qpoly_deriv (cons a p))
    with (qpoly_add p (cons 0 (qpoly_deriv p))).
  rewrite (qpoly_eval_add p (cons 0 (qpoly_deriv p)) x).
  change (qpoly_eval (cons 0 (qpoly_deriv p)) x)
    with (0 + x * qpoly_eval (qpoly_deriv p) x).
  ring.
Qed.
(* Reciprocal product of positive integers: [(z#1) / (z#1) == 1] (the
   [Qeq]-level equation of [Qmult_inv_r] is carried by a linear [Z]-
   level chain). *)
Lemma lw0_q_int_inv : forall z : Z, (0 < z)%Z -> (z # 1) * (/ (z # 1)) == 1.
Proof.
  intros z Hz.
  apply Qmult_inv_r.
  unfold Qeq, Qmult. cbn [Qnum Qden].
  rewrite Z.mul_1_r, ?Z.mul_1_l.
  intro Hzz.
  rewrite Hzz in Hz.
  simpl in Hz. discriminate Hz.
Qed.
(* Multiply back after division by positive integers:
   [(z#1) * (a / (z#1)) == a] (the reciprocal product plus [Qmult]
   associativity/commutativity). *)
Lemma lw0_q_div_int_mul : forall (z : Z) (a : Q),
  (0 < z)%Z -> (z # 1) * (a / (z # 1)) == a.
Proof.
  intros z a Hz.
  change (a / (z # 1)) with (a * / (z # 1)).
  rewrite (Qmult_assoc (z # 1) a (/ (z # 1))).
  rewrite (Qmult_comm (z # 1) a).
  rewrite <- (Qmult_assoc a (z # 1) (/ (z # 1))).
  rewrite (lw0_q_int_inv z Hz).
  ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Termwise antiderivative: the recursion carries the degree index k
   (the coefficient at layer j is divided by j+k+1).                   *)
(* Mathematical shape: [lw0_qp_ai p k = sum_j p_j t^j/(j+k+1)];
   [lw0_qp_antideriv p = cons 0 (lw0_qp_ai p 0) =
   sum_j p_j t^{j+1}/(j+1)].                                           *)
(* ------------------------------------------------------------------ *)
(* The termwise antiderivative core: the recursion carries the degree
   index [k] (the coefficient at layer [j] is divided by [j+k+1]). *)
Fixpoint lw0_qp_ai (p : qpoly) (k : nat) : qpoly :=
  match p with
  | nil => nil
  | cons a p' => cons (a / (Z.of_nat (S k) # 1)) (lw0_qp_ai p' (S k))
  end.
(* The antiderivative list: [cons 0 (ai p 0) =
   sum_j p_j t^{j+1}/(j+1)]. *)
Definition lw0_qp_antideriv (p : qpoly) : qpoly := cons 0 (lw0_qp_ai p 0).
(* Unfolding of the pointwise evaluation of an antiderivative slice
   at the cons layer. *)
Lemma lw0_qp_ai_cons_eval : forall a p k x,
  qpoly_eval (lw0_qp_ai (cons a p) k) x ==
  a / (Z.of_nat (S k) # 1) + x * qpoly_eval (lw0_qp_ai p (S k)) x.
Proof.
  intros a p k x.
  change (lw0_qp_ai (cons a p) k)
    with (cons (a / (Z.of_nat (S k) # 1)) (lw0_qp_ai p (S k))).
  change (qpoly_eval (cons (a / (Z.of_nat (S k) # 1)) (lw0_qp_ai p (S k))) x)
    with (a / (Z.of_nat (S k) # 1)
            + x * qpoly_eval (lw0_qp_ai p (S k)) x).
  reflexivity.
Qed.
(* Evaluation of the antiderivative slice with a zero head term: the
   zero head coefficient cancels. *)
Lemma lw0_qp_ai_zero_head_eval : forall p k x,
  qpoly_eval (lw0_qp_ai (cons 0 p) k) x == x * qpoly_eval (lw0_qp_ai p (S k)) x.
Proof.
  intros p k x.
  rewrite (lw0_qp_ai_cons_eval 0 p k x).
  assert (Hz : 0 / (Z.of_nat (S k) # 1) == 0) by (unfold Qdiv; ring).
  rewrite Hz.
  ring.
Qed.
(* The antiderivative distributes over addition (pointwise-evaluation
   level). *)
Lemma lw0_qp_ai_add : forall p q k x,
  qpoly_eval (lw0_qp_ai (qpoly_add p q) k) x ==
  qpoly_eval (lw0_qp_ai p k) x + qpoly_eval (lw0_qp_ai q k) x.
Proof.
  induction p as [|a p IH]; intros q k x.
  - simpl. ring.
  - destruct q as [|b q].
    + change (qpoly_add (cons a p) nil) with (cons a p).
      change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
      ring.
    + change (qpoly_add (cons a p) (cons b q))
        with (cons (a + b) (qpoly_add p q)).
      rewrite (lw0_qp_ai_cons_eval (a + b) (qpoly_add p q) k x).
      rewrite (lw0_qp_ai_cons_eval a p k x).
      rewrite (lw0_qp_ai_cons_eval b q k x).
      rewrite (IH q (S k) x).
      change ((a + b) / (Z.of_nat (S k) # 1))
        with ((a + b) * / (Z.of_nat (S k) # 1)).
      change (a / (Z.of_nat (S k) # 1))
        with (a * / (Z.of_nat (S k) # 1)).
      change (b / (Z.of_nat (S k) # 1))
        with (b * / (Z.of_nat (S k) # 1)).
      ring.
Qed.
(* The antiderivative distributes over scalar multiplication
   (pointwise-evaluation level). *)
Lemma lw0_qp_ai_scalar : forall c p k x,
  qpoly_eval (lw0_qp_ai (qpoly_scalar c p) k) x ==
  c * qpoly_eval (lw0_qp_ai p k) x.
Proof.
  intros c p.
  induction p as [|a p IH]; intros k x.
  - simpl. ring.
  - change (qpoly_scalar c (cons a p)) with (cons (c * a) (qpoly_scalar c p)).
    rewrite (lw0_qp_ai_cons_eval (c * a) (qpoly_scalar c p) k x).
    rewrite (lw0_qp_ai_cons_eval a p k x).
    rewrite IH.
    change ((c * a) / (Z.of_nat (S k) # 1))
      with ((c * a) * / (Z.of_nat (S k) # 1)).
    change (a / (Z.of_nat (S k) # 1))
      with (a * / (Z.of_nat (S k) # 1)).
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Induction core of the right-inverse law: the weighted identity of
   an antiderivative slice and its derivative (the family of degree
   indices).                                                           *)
(* Mathematical content: [(k+1)*t^k*A_k(t) + t^{k+1}*A_k'(t) =
   t^k*p(t)], with [A_k := lw0_qp_ai p k].  The induction assumptions
   at the cons layer and at the index [k+1] meet exactly.              *)
(* ------------------------------------------------------------------ *)
(* Induction core of the right-inverse law: [(k+1)*t^k*A_k(t) +
   t^{k+1}*A_k'(t) = t^k*p(t)]. *)
Lemma lw0_qp_ai_deriv_pair : forall p k x,
  (Z.of_nat (S k) # 1) * q_pow x k * qpoly_eval (lw0_qp_ai p k) x
  + q_pow x (S k) * qpoly_eval (qpoly_deriv (lw0_qp_ai p k)) x
  == q_pow x k * qpoly_eval p x.
Proof.
  induction p as [|a p IH]; intros k x.
  - simpl. ring.
  - assert (Hpos : (0 < Z.of_nat (S k))%Z)
      by (change 0%Z with (Z.of_nat 0);
            apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S k))); apply Nat.lt_0_succ).
    assert (Hz : (Z.of_nat (S k) # 1) * (a / (Z.of_nat (S k) # 1)) == a)
      by exact (lw0_q_div_int_mul (Z.of_nat (S k)) a Hpos).
    assert (Hn : Z.of_nat (S (S k)) = (Z.of_nat (S k) + 1)%Z)
      by (rewrite Nat2Z.inj_succ; symmetry; apply Z.add_1_r).
    assert (Hz2 : ((Z.of_nat (S k) # 1)%Q + 1)%Q
                  == (Z.of_nat (S (S k)) # 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult];
      rewrite Hn, !Z.mul_1_r, ?Z.mul_1_l; reflexivity).
    assert (Hf := IH (S k) x).
    rewrite <- Hz2 in Hf.
    rewrite (q_pow_succ x (S k)) in Hf.
    rewrite (q_pow_succ x k) in Hf.
    rewrite (lw0_qp_ai_cons_eval a p k x).
    change (qpoly_deriv (cons (a / (Z.of_nat (S k) # 1)) (lw0_qp_ai p (S k))))
      with (qpoly_add (lw0_qp_ai p (S k))
              (cons 0 (qpoly_deriv (lw0_qp_ai p (S k))))).
    rewrite (qpoly_eval_add (lw0_qp_ai p (S k))
               (cons 0 (qpoly_deriv (lw0_qp_ai p (S k)))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (lw0_qp_ai p (S k)))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p (S k))) x).
    change (q_pow x (S k)) with (x * q_pow x k).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    assert (Hd : (Z.of_nat (S k) # 1) * q_pow x k
                   * (a / (Z.of_nat (S k) # 1)
                      + x * qpoly_eval (lw0_qp_ai p (S k)) x)
                 == q_pow x k * a
                    + (Z.of_nat (S k) # 1) * q_pow x k * x
                      * qpoly_eval (lw0_qp_ai p (S k)) x).
    { transitivity ((Z.of_nat (S k) # 1) * q_pow x k
                      * (a / (Z.of_nat (S k) # 1))
                    + (Z.of_nat (S k) # 1) * q_pow x k * x
                      * qpoly_eval (lw0_qp_ai p (S k)) x)%Q.
      - ring.
      - rewrite <- (Qmult_assoc (Z.of_nat (S k) # 1) (q_pow x k)
                      (a / (Z.of_nat (S k) # 1))).
        rewrite (Qmult_comm (q_pow x k) (a / (Z.of_nat (S k) # 1))).
        rewrite (Qmult_assoc (Z.of_nat (S k) # 1) (a / (Z.of_nat (S k) # 1))
                   (q_pow x k)).
        rewrite Hz.
        ring. }
    rewrite Hd.
    assert (Hg : q_pow x k * a
                 + x * q_pow x k * (((Z.of_nat (S k) # 1)%Q + 1)
                                      * qpoly_eval (lw0_qp_ai p (S k)) x
                                      + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p (S k))) x)
                 == q_pow x k * a + x * q_pow x k * qpoly_eval p x).
    { rewrite <- Hf. ring. }
    transitivity (q_pow x k * a
                    + x * q_pow x k * (((Z.of_nat (S k) # 1)%Q + 1)
                                         * qpoly_eval (lw0_qp_ai p (S k)) x
                                         + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p (S k))) x))%Q.
    { ring. }
    { rewrite Hg. ring. }
Qed.
(* The [k = 0] case of the right-inverse law: the derivative of the
   antiderivative list restores [p] pointwise. *)
Lemma lw0_qp_antideriv_deriv : forall p x,
  qpoly_eval (qpoly_deriv (lw0_qp_antideriv p)) x == qpoly_eval p x.
Proof.
  intros p x.
  unfold lw0_qp_antideriv.
  change (qpoly_deriv (cons 0 (lw0_qp_ai p 0)))
    with (qpoly_add (lw0_qp_ai p 0) (cons 0 (qpoly_deriv (lw0_qp_ai p 0)))).
  rewrite (qpoly_eval_add (lw0_qp_ai p 0)
             (cons 0 (qpoly_deriv (lw0_qp_ai p 0))) x).
  change (qpoly_eval (cons 0 (qpoly_deriv (lw0_qp_ai p 0))) x)
    with (0 + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p 0)) x).
  assert (Hk := lw0_qp_ai_deriv_pair p 0 x).
  assert (Hz1 : (Z.of_nat (S 0) # 1)%Q == 1) by reflexivity.
  assert (H1 : q_pow x 0 == 1) by reflexivity.
  assert (Hs : q_pow x (S 0) == x).
  { change (q_pow x (S 0)) with (x * q_pow x 0).
    change (q_pow x 0) with 1.
    ring. }
  rewrite Hz1 in Hk.
  rewrite H1 in Hk.
  rewrite Hs in Hk.
  transitivity (1 * 1 * qpoly_eval (lw0_qp_ai p 0) x
                + x * qpoly_eval (qpoly_deriv (lw0_qp_ai p 0)) x)%Q.
  { ring. }
  { rewrite Hk. ring. }
Qed.

(* ------------------------------------------------------------------ *)
(* Induction core of the Newton-Leibniz law: the antiderivative
   identity of the derivative slice (the family of degree indices).    *)
(* Mathematical content: [t^{k+2}*B_{k+1}(t) + (k+1)*t^{k+1}*A_k(t) =
   t^{k+1}*p(t)], with [A_k := ai p k] and
   [B_{k+1} := ai (deriv p) (S k)].                                     *)
(* ------------------------------------------------------------------ *)
(* Induction core of Newton-Leibniz: [t^{k+2}*B_{k+1} +
   (k+1)*t^{k+1}*A_k = t^{k+1}*p]. *)
Lemma lw0_qp_ai_deriv_ft : forall p k x,
  q_pow x (S (S k)) * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S k)) x
  + (Z.of_nat (S k) # 1) * q_pow x (S k) * qpoly_eval (lw0_qp_ai p k) x
  == q_pow x (S k) * qpoly_eval p x.
Proof.
  induction p as [|a p IH]; intros k x.
  - simpl. ring.
  - assert (Hpos : (0 < Z.of_nat (S k))%Z)
      by (change 0%Z with (Z.of_nat 0);
            apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S k))); apply Nat.lt_0_succ).
    assert (Hz : (Z.of_nat (S k) # 1) * (a / (Z.of_nat (S k) # 1)) == a)
      by exact (lw0_q_div_int_mul (Z.of_nat (S k)) a Hpos).
    assert (Hn : Z.of_nat (S (S k)) = (Z.of_nat (S k) + 1)%Z)
      by (rewrite Nat2Z.inj_succ; symmetry; apply Z.add_1_r).
    assert (Hz2 : ((Z.of_nat (S k) # 1)%Q + 1)%Q
                  == (Z.of_nat (S (S k)) # 1)%Q)
      by (unfold Qeq; cbn [Qnum Qden Qplus Qmult];
      rewrite Hn, !Z.mul_1_r, ?Z.mul_1_l; reflexivity).
    assert (Hf := IH (S k) x).
    rewrite <- Hz2 in Hf.
    rewrite (q_pow_succ x (S (S k))) in Hf.
    rewrite (q_pow_succ x (S k)) in Hf.
    rewrite (q_pow_succ x k) in Hf.
    change (qpoly_deriv (cons a p))
      with (qpoly_add p (cons 0 (qpoly_deriv p))).
    rewrite (lw0_qp_ai_add p (cons 0 (qpoly_deriv p)) (S k) x).
    change (lw0_qp_ai (cons 0 (qpoly_deriv p)) (S k))
      with (cons (0 / (Z.of_nat (S (S k)) # 1))
              (lw0_qp_ai (qpoly_deriv p) (S (S k)))).
    change (qpoly_eval
              (cons (0 / (Z.of_nat (S (S k)) # 1))
                 (lw0_qp_ai (qpoly_deriv p) (S (S k)))) x)
      with (0 / (Z.of_nat (S (S k)) # 1)
              + x * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S (S k))) x).
    rewrite (lw0_qp_ai_cons_eval a p k x).
    change (q_pow x (S (S k))) with (x * q_pow x (S k)).
    change (q_pow x (S k)) with (x * q_pow x k).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    assert (Hz0 : 0 / (Z.of_nat (S (S k)) # 1) == 0)
      by (unfold Qdiv; ring).
    rewrite Hz0.
    assert (Hd : (Z.of_nat (S k) # 1) * (x * q_pow x k)
                   * (a / (Z.of_nat (S k) # 1)
                      + x * qpoly_eval (lw0_qp_ai p (S k)) x)
                 == (x * q_pow x k) * a
                    + (Z.of_nat (S k) # 1) * (x * q_pow x k) * x
                      * qpoly_eval (lw0_qp_ai p (S k)) x).
    { transitivity ((Z.of_nat (S k) # 1) * (x * q_pow x k)
                      * (a / (Z.of_nat (S k) # 1))
                    + (Z.of_nat (S k) # 1) * (x * q_pow x k) * x
                      * qpoly_eval (lw0_qp_ai p (S k)) x)%Q.
      - ring.
      - rewrite <- (Qmult_assoc (Z.of_nat (S k) # 1) (x * q_pow x k)
                      (a / (Z.of_nat (S k) # 1))).
        rewrite (Qmult_comm (x * q_pow x k) (a / (Z.of_nat (S k) # 1))).
        rewrite (Qmult_assoc (Z.of_nat (S k) # 1) (a / (Z.of_nat (S k) # 1))
                   (x * q_pow x k)).
        rewrite Hz.
        ring. }
    rewrite Hd.
    assert (Hg : q_pow x k * x * x
                   * (((Z.of_nat (S k) # 1)%Q + 1) * qpoly_eval (lw0_qp_ai p (S k)) x
                      + x * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S (S k))) x)
                 == x * (x * q_pow x k) * qpoly_eval p x).
    { rewrite <- Hf. ring. }
    transitivity ((x * q_pow x k) * a
                    + q_pow x k * x * x
                        * (((Z.of_nat (S k) # 1)%Q + 1) * qpoly_eval (lw0_qp_ai p (S k)) x
                           + x * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S (S k))) x))%Q.
    { ring. }
    { rewrite Hg. ring. }
Qed.
(* Newton-Leibniz at [k = 0]: the integral of [p'] equals
   [p(x) - p(0)]. *)
Lemma lw0_qp_antideriv_deriv_at : forall p x,
  qpoly_eval (lw0_qp_antideriv (qpoly_deriv p)) x
  == qpoly_eval p x - qpoly_eval p 0.
Proof.
  induction p as [|a p IH]; intros x.
  - simpl. ring.
  - assert (Hf := lw0_qp_ai_deriv_ft p 0 x).
    rewrite (q_pow_succ x (S 0)) in Hf.
    rewrite (q_pow_succ x 0) in Hf.
    change (q_pow x 0) with 1 in Hf.
    assert (Hz1 : (Z.of_nat (S 0) # 1)%Q == 1) by reflexivity.
    rewrite Hz1 in Hf.
    rewrite (Qmult_1_r x) in Hf.
    change (qpoly_deriv (cons a p))
      with (qpoly_add p (cons 0 (qpoly_deriv p))).
    unfold lw0_qp_antideriv.
    change (qpoly_eval
              (cons 0
                 (lw0_qp_ai (qpoly_add p (cons 0 (qpoly_deriv p))) 0)) x)
      with (0 + x * qpoly_eval
              (lw0_qp_ai (qpoly_add p (cons 0 (qpoly_deriv p))) 0) x).
    rewrite (lw0_qp_ai_add p (cons 0 (qpoly_deriv p)) 0 x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_deriv p) 0 x).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    change (qpoly_eval (cons a p) 0%Q) with (a + 0 * qpoly_eval p 0%Q).
    assert (Hg : x * (qpoly_eval (lw0_qp_ai p 0) x
                        + x * qpoly_eval (lw0_qp_ai (qpoly_deriv p) (S 0)) x)
                 == x * qpoly_eval p x).
    { rewrite <- Hf. ring. }
    rewrite Hg.
    ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Vanishing beyond the degree: once the differentiation count
   reaches the list length the evaluation is pointwise zero (list
   length >= polynomial degree + 1).                                   *)
(* The criterion is taken as [(length p <= n)%nat]: the [nat]/[Z]
   order premise keeps the shape of the source statement.              *)
(* ------------------------------------------------------------------ *)
(* Iterated differentiation adds the counts: [deriv_iter (n+m)] is
   [deriv_iter n] composed with [deriv_iter m] (at the list level). *)
Lemma lw0_qp_deriv_iter_plus : forall n m p,
  qpoly_deriv_iter (n + m) p = qpoly_deriv_iter n (qpoly_deriv_iter m p).
Proof.
  induction n as [|n IH]; intros m p.
  - reflexivity.
  - change (qpoly_deriv_iter (S n + m) p)
      with (qpoly_deriv (qpoly_deriv_iter (n + m) p)).
    rewrite (IH m p).
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Monomials and the paired product. *)
(* ------------------------------------------------------------------ *)
(* The paired product: [pair(f,g)(q)] is the evaluation at [q] of the
   integral of [f*g]. *)
Definition lw0_qp_pair (f g : qpoly) (q : Q) : Q :=
  qpoly_eval (lw0_qp_antideriv (qpoly_mul f g)) q.
(* The integral distributes over addition in the left argument
   (induction on the unfolded product list). *)
Lemma lw0_qp_ai_mul_add_l : forall f1 f2 g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_add f1 f2) g) k) x ==
  qpoly_eval (lw0_qp_ai (qpoly_mul f1 g) k) x
  + qpoly_eval (lw0_qp_ai (qpoly_mul f2 g) k) x.
Proof.
  induction f1 as [|a f1 IH]; intros f2 g k x.
  - change (qpoly_add nil f2) with f2.
    change (qpoly_mul nil g) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
    ring.
  - destruct f2 as [|b f2].
    + change (qpoly_add (cons a f1) nil) with (cons a f1).
      change (qpoly_mul nil g) with (@nil Q).
      change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
      ring.
    + change (qpoly_add (cons a f1) (cons b f2))
        with (cons (a + b) (qpoly_add f1 f2)).
      change (qpoly_mul (cons (a + b) (qpoly_add f1 f2)) g)
        with (qpoly_add (qpoly_scalar (a + b) g)
                (cons 0 (qpoly_mul (qpoly_add f1 f2) g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar (a + b) g)
                 (cons 0 (qpoly_mul (qpoly_add f1 f2) g)) k x).
      rewrite (lw0_qp_ai_scalar (a + b) g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_add f1 f2) g) k x).
      rewrite (IH f2 g (S k) x).
      change (qpoly_mul (cons a f1) g)
        with (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f1 g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g) (cons 0 (qpoly_mul f1 g)) k x).
      rewrite (lw0_qp_ai_scalar a g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f1 g) k x).
      change (qpoly_mul (cons b f2) g)
        with (qpoly_add (qpoly_scalar b g) (cons 0 (qpoly_mul f2 g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar b g) (cons 0 (qpoly_mul f2 g)) k x).
      rewrite (lw0_qp_ai_scalar b g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f2 g) k x).
      ring.
Qed.
(* The paired product distributes over addition in the left
   argument. *)
Lemma lw0_qp_pair_add_l : forall f1 f2 g q,
  lw0_qp_pair (qpoly_add f1 f2) g q
  == lw0_qp_pair f1 g q + lw0_qp_pair f2 g q.
Proof.
  intros f1 f2 g q.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul (qpoly_add f1 f2) g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_add f1 f2) g) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f1 g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f1 g) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f2 g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f2 g) 0) q).
  rewrite (lw0_qp_ai_mul_add_l f1 f2 g 0 q).
  ring.
Qed.
(* Zero raised to a positive power is zero. *)
Lemma lw0_q_pow_zero_succ : forall n : nat, q_pow 0 (Datatypes.S n) == 0.
Proof.
  intros n.
  change (q_pow 0 (Datatypes.S n)) with (0 * q_pow 0 n)%Q.
  ring.
Qed.

(* The weighted fundamental-theorem family: the pointwise
   Newton-Leibniz law under the [t^k] weight (the [k = 0] case is the
   expanded form of the existing lemma [lw0_qp_antideriv_deriv_at]).
   Induction along the coefficient list; at the cons layer the
   [k = 0] case and                                                     *)

(* The weighted fundamental-theorem family: the pointwise
   Newton-Leibniz law under the [t^k] weight (at [k = 0] this reduces
   to [lw0_qp_antideriv_deriv_at]). *)
Lemma lw0_qp_ai_deriv_ft_pow : forall p k x,
  q_pow x (Datatypes.S k) * qpoly_eval (lw0_qp_ai (qpoly_deriv p) k) x
  + (Z.of_nat k # 1) * q_pow x k * qpoly_eval (lw0_qp_ai p (Nat.sub k 1)) x
  == q_pow x k * qpoly_eval p x - q_pow 0 k * qpoly_eval p 0.
Proof.
  induction p as [|a p IH]; intros k x.
  - change (qpoly_deriv (@nil Q)) with (@nil Q).
    change (lw0_qp_ai (@nil Q) k) with (@nil Q).
    change (lw0_qp_ai (@nil Q) (Nat.sub k 1)) with (@nil Q).
    change (qpoly_eval (@nil Q) x) with 0%Q.
    change (qpoly_eval (@nil Q) 0%Q) with 0%Q.
    ring.
  - destruct k as [|j].
    + assert (Hf := lw0_qp_antideriv_deriv_at (cons a p) x).
      unfold lw0_qp_antideriv in Hf.
      change (qpoly_eval
                (cons 0 (lw0_qp_ai (qpoly_deriv (cons a p)) 0)) x)
        with (0 + x * qpoly_eval (lw0_qp_ai (qpoly_deriv (cons a p)) 0) x)
        in Hf.
      assert (H1 : (Z.of_nat 0 # 1)%Q == 0) by reflexivity.
      rewrite H1.
      assert (H2 : q_pow x (Datatypes.S 0) == x).
      { change (q_pow x (Datatypes.S 0)) with (x * q_pow x 0).
        change (q_pow x 0) with 1.
        ring. }
      rewrite H2.
      change (q_pow x 0) with 1.
      change (q_pow 0 0) with 1.
      rewrite (Qmult_1_l (qpoly_eval (cons a p) x)).
      rewrite (Qmult_1_l (qpoly_eval (cons a p) 0%Q)).
      transitivity (x * qpoly_eval (lw0_qp_ai (qpoly_deriv (cons a p)) 0) x
                    + 0 * qpoly_eval (lw0_qp_ai (cons a p) (Nat.sub 0 1)) x)%Q.
      { ring. }
      { rewrite <- Hf. ring. }
    + assert (Hpos : (0 < Z.of_nat (Datatypes.S j))%Z)
      by (change 0%Z with (Z.of_nat 0);
            apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S j))); apply Nat.lt_0_succ).
      assert (Hc : (Z.of_nat (Datatypes.S j) # 1)
                     * (a / (Z.of_nat (Datatypes.S j) # 1)) == a)
        by exact (lw0_q_div_int_mul (Z.of_nat (Datatypes.S j)) a Hpos).
      rewrite (q_pow_succ x (Datatypes.S j)).
      assert (Hsub : Nat.sub (Datatypes.S j) 1 = j)
      by (rewrite Nat.sub_succ, Nat.sub_0_r; reflexivity).
      rewrite Hsub.
      change (qpoly_deriv (cons a p))
        with (qpoly_add p (cons 0 (qpoly_deriv p))).
      rewrite (lw0_qp_ai_add p (cons 0 (qpoly_deriv p)) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_deriv p) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_cons_eval a p j x).
      change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
      change (qpoly_eval (cons a p) 0%Q)
        with (a + 0 * qpoly_eval p 0%Q).
      rewrite (lw0_q_pow_zero_succ j).
      assert (Hih := IH (Datatypes.S (Datatypes.S j)) x).
      rewrite (q_pow_succ x (Datatypes.S (Datatypes.S j))) in Hih.
      rewrite (q_pow_succ x (Datatypes.S j)) in Hih.
      assert (Hn2 : Z.of_nat (Datatypes.S (Datatypes.S j))
                    = (Z.of_nat (Datatypes.S j) + 1)%Z)
      by (rewrite Nat2Z.inj_succ; symmetry; apply Z.add_1_r).
      assert (Hz3 : (Z.of_nat (Datatypes.S (Datatypes.S j)) # 1)%Q
                    == ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)%Q)
        by (unfold Qeq; cbn [Qnum Qden Qplus Qmult];
      rewrite Hn2, !Z.mul_1_r, ?Z.mul_1_l; reflexivity).
      rewrite Hz3 in Hih.
      change (Nat.sub (Datatypes.S (Datatypes.S j)) 1)
        with (Datatypes.S j) in Hih.
      rewrite (lw0_q_pow_zero_succ (Datatypes.S j)) in Hih.
      assert (Hd : (Z.of_nat (Datatypes.S j) # 1) * q_pow x (Datatypes.S j)
                     * (a / (Z.of_nat (Datatypes.S j) # 1)
                        + x * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x)
                   == q_pow x (Datatypes.S j) * a
                      + (Z.of_nat (Datatypes.S j) # 1)
                          * q_pow x (Datatypes.S j) * x
                          * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x).
      { transitivity ((Z.of_nat (Datatypes.S j) # 1)
                        * q_pow x (Datatypes.S j)
                        * (a / (Z.of_nat (Datatypes.S j) # 1))
                      + (Z.of_nat (Datatypes.S j) # 1)
                          * q_pow x (Datatypes.S j) * x
                          * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x)%Q.
        - ring.
        - rewrite <- (Qmult_assoc (Z.of_nat (Datatypes.S j) # 1)
                        (q_pow x (Datatypes.S j))
                        (a / (Z.of_nat (Datatypes.S j) # 1))).
          rewrite (Qmult_comm (q_pow x (Datatypes.S j))
                     (a / (Z.of_nat (Datatypes.S j) # 1))).
          rewrite (Qmult_assoc (Z.of_nat (Datatypes.S j) # 1)
                     (a / (Z.of_nat (Datatypes.S j) # 1))
                     (q_pow x (Datatypes.S j))).
          rewrite Hc.
          ring. }
      rewrite Hd.
      assert (Hg : q_pow x (Datatypes.S j) * a
                   + (x * (x * q_pow x (Datatypes.S j))
                        * qpoly_eval (lw0_qp_ai (qpoly_deriv p)
                                             (Datatypes.S (Datatypes.S j))) x
                      + ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)
                          * (x * q_pow x (Datatypes.S j))
                          * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x)
                   == q_pow x (Datatypes.S j) * a
                      + x * q_pow x (Datatypes.S j) * qpoly_eval p x
                      - 0 * qpoly_eval p 0%Q).
      { rewrite Hih. ring. }
      transitivity (q_pow x (Datatypes.S j) * a
                    + (x * (x * q_pow x (Datatypes.S j))
                         * qpoly_eval (lw0_qp_ai (qpoly_deriv p)
                                              (Datatypes.S (Datatypes.S j))) x
                       + ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)
                           * (x * q_pow x (Datatypes.S j))
                           * qpoly_eval (lw0_qp_ai p (Datatypes.S j)) x))%Q.
      { ring. }
      { rewrite Hg. ring. }
Qed.

(* The main integration-by-parts identity (weighted family): induction
   on the first argument; the head constant term of the cons layer (an
   instance of the [t^k]-weighted fundamental-theorem family) is paid
   off layer by layer along the induction, and the tail contribution is
   exactly the induction assumption of the layer above                *)

(* The main integration-by-parts identity (weighted family): induction
   on the first argument; the head constant contribution of the cons
   layer is paid off layer by layer. *)
Lemma lw0_qp_pair_ibp_family : forall R S k x,
  q_pow x (Datatypes.S k)
    * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S) k) x
  + q_pow x (Datatypes.S k)
    * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S)) k) x
  + (Z.of_nat k # 1) * q_pow x k
    * qpoly_eval (lw0_qp_ai (qpoly_mul R S) (Nat.sub k 1)) x
  == q_pow x k * qpoly_eval (qpoly_mul R S) x
     - q_pow 0 k * qpoly_eval (qpoly_mul R S) 0.
Proof.
  induction R as [|a R IH]; intros S k x.
  - change (qpoly_deriv (@nil Q)) with (@nil Q).
    change (qpoly_mul (@nil Q) S) with (@nil Q).
    change (qpoly_mul (@nil Q) (qpoly_deriv S)) with (@nil Q).
    change (lw0_qp_ai (@nil Q) k) with (@nil Q).
    change (lw0_qp_ai (@nil Q) (Nat.sub k 1)) with (@nil Q).
    change (qpoly_eval (@nil Q) x) with 0%Q.
    change (qpoly_eval (@nil Q) 0%Q) with 0%Q.
    ring.
  - destruct k as [|j].
    + assert (H1 : (Z.of_nat 0 # 1)%Q == 0) by reflexivity.
      rewrite H1.
      assert (H2 : q_pow x (Datatypes.S 0) == x).
      { change (q_pow x (Datatypes.S 0)) with (x * q_pow x 0).
        change (q_pow x 0) with 1.
        ring. }
      rewrite H2.
      change (q_pow x 0) with 1.
      change (q_pow 0 0) with 1.
      change (qpoly_deriv (cons a R))
        with (qpoly_add R (cons 0 (qpoly_deriv R))).
      rewrite (lw0_qp_ai_mul_add_l R (cons 0 (qpoly_deriv R)) S 0 x).
      change (qpoly_mul (cons 0 (qpoly_deriv R)) S)
        with (qpoly_add (qpoly_scalar 0 S)
               (cons 0 (qpoly_mul (qpoly_deriv R) S))).
      rewrite (lw0_qp_ai_add (qpoly_scalar 0 S)
                 (cons 0 (qpoly_mul (qpoly_deriv R) S)) 0 x).
      rewrite (lw0_qp_ai_scalar 0 S 0 x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_deriv R) S) 0 x).
      change (qpoly_mul (cons a R) (qpoly_deriv S))
        with (qpoly_add (qpoly_scalar a (qpoly_deriv S))
               (cons 0 (qpoly_mul R (qpoly_deriv S)))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_deriv S))
                 (cons 0 (qpoly_mul R (qpoly_deriv S))) 0 x).
      rewrite (lw0_qp_ai_scalar a (qpoly_deriv S) 0 x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul R (qpoly_deriv S)) 0 x).
      change (qpoly_mul (cons a R) S)
        with (qpoly_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S))
                 (Nat.sub 0 1) x).
      rewrite (lw0_qp_ai_scalar a S (Nat.sub 0 1) x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul R S) (Nat.sub 0 1) x).
      rewrite (qpoly_eval_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) x).
      rewrite (qpoly_eval_scalar a S x).
      assert (Hc0 : qpoly_eval (cons 0 (qpoly_mul R S)) x
                    == 0 + x * qpoly_eval (qpoly_mul R S) x)
        by reflexivity.
      rewrite ?Hc0.
      rewrite (qpoly_eval_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) 0%Q).
      rewrite (qpoly_eval_scalar a S 0%Q).
      change (qpoly_eval (cons 0 (qpoly_mul R S)) 0%Q)
        with (0 + 0 * qpoly_eval (qpoly_mul R S) 0%Q).
      assert (Hih := IH S (Datatypes.S 0) x).
      rewrite (q_pow_succ x (Datatypes.S 0)) in Hih.
      rewrite H2 in Hih.
      assert (Hz1 : (Z.of_nat (Datatypes.S 0) # 1)%Q == 1) by reflexivity.
      rewrite Hz1 in Hih.
      assert (Hs01 : Nat.sub (Datatypes.S 0) 1 = 0%nat) by reflexivity.
      rewrite Hs01 in Hih.
      rewrite (lw0_q_pow_zero_succ 0) in Hih.
      assert (Hn0 := lw0_qp_ai_deriv_ft_pow S 0 x).
      rewrite H1 in Hn0.
      rewrite H2 in Hn0.
      change (q_pow x 0) with 1 in Hn0.
      change (q_pow 0 0) with 1 in Hn0.
      assert (Hg : x * x
                     * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S)
                                        (Datatypes.S 0)) x
                   + x * x
                     * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S))
                                        (Datatypes.S 0)) x
                   + 1 * x * qpoly_eval (lw0_qp_ai (qpoly_mul R S) 0) x
                   + a * (x * qpoly_eval (lw0_qp_ai (qpoly_deriv S) 0) x
                            + 0 * 1
                                * qpoly_eval (lw0_qp_ai S (Nat.sub 0 1)) x)
                   == a * qpoly_eval S x
                      + (x * qpoly_eval (qpoly_mul R S) x
                         - 0 * qpoly_eval (qpoly_mul R S) 0%Q)
                      - a * qpoly_eval S 0%Q).
      { rewrite Hih. rewrite Hn0. ring. }
      transitivity (x * x
                      * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S)
                                           (Datatypes.S 0)) x
                    + x * x
                      * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S))
                                           (Datatypes.S 0)) x
                    + 1 * x * qpoly_eval (lw0_qp_ai (qpoly_mul R S) 0) x
                    + a * (x * qpoly_eval (lw0_qp_ai (qpoly_deriv S) 0) x
                             + 0 * 1
                                 * qpoly_eval (lw0_qp_ai S (Nat.sub 0 1)) x))%Q.
      { ring. }
      { rewrite Hg. ring. }
    + rewrite (q_pow_succ x (Datatypes.S j)).
      assert (Hsub : Nat.sub (Datatypes.S j) 1 = j)
      by (rewrite Nat.sub_succ, Nat.sub_0_r; reflexivity).
      rewrite Hsub.
      change (qpoly_deriv (cons a R))
        with (qpoly_add R (cons 0 (qpoly_deriv R))).
      rewrite (lw0_qp_ai_mul_add_l R (cons 0 (qpoly_deriv R)) S
                 (Datatypes.S j) x).
      change (qpoly_mul (cons 0 (qpoly_deriv R)) S)
        with (qpoly_add (qpoly_scalar 0 S)
               (cons 0 (qpoly_mul (qpoly_deriv R) S))).
      rewrite (lw0_qp_ai_add (qpoly_scalar 0 S)
                 (cons 0 (qpoly_mul (qpoly_deriv R) S)) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_scalar 0 S (Datatypes.S j) x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_deriv R) S)
                 (Datatypes.S j) x).
      change (qpoly_mul (cons a R) (qpoly_deriv S))
        with (qpoly_add (qpoly_scalar a (qpoly_deriv S))
               (cons 0 (qpoly_mul R (qpoly_deriv S)))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_deriv S))
                 (cons 0 (qpoly_mul R (qpoly_deriv S))) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_scalar a (qpoly_deriv S) (Datatypes.S j) x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul R (qpoly_deriv S))
                 (Datatypes.S j) x).
      change (qpoly_mul (cons a R) S)
        with (qpoly_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) j x).
      rewrite (lw0_qp_ai_scalar a S j x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul R S) j x).
      rewrite (lw0_q_pow_zero_succ j).
      rewrite (qpoly_eval_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) x).
      rewrite (qpoly_eval_scalar a S x).
      assert (Hc0j : qpoly_eval (cons 0 (qpoly_mul R S)) x
                     == 0 + x * qpoly_eval (qpoly_mul R S) x)
        by reflexivity.
      rewrite ?Hc0j.
      rewrite (qpoly_eval_add (qpoly_scalar a S) (cons 0 (qpoly_mul R S)) 0%Q).
      rewrite (qpoly_eval_scalar a S 0%Q).
      change (qpoly_eval (cons 0 (qpoly_mul R S)) 0%Q)
        with (0 + 0 * qpoly_eval (qpoly_mul R S) 0%Q).
      assert (Hih := IH S (Datatypes.S (Datatypes.S j)) x).
      rewrite (q_pow_succ x (Datatypes.S (Datatypes.S j))) in Hih.
      rewrite (q_pow_succ x (Datatypes.S j)) in Hih.
      assert (Hn2 : Z.of_nat (Datatypes.S (Datatypes.S j))
                    = (Z.of_nat (Datatypes.S j) + 1)%Z)
      by (rewrite Nat2Z.inj_succ; symmetry; apply Z.add_1_r).
      assert (Hz3 : (Z.of_nat (Datatypes.S (Datatypes.S j)) # 1)%Q
                    == ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)%Q)
        by (unfold Qeq; cbn [Qnum Qden Qplus Qmult];
      rewrite Hn2, !Z.mul_1_r, ?Z.mul_1_l; reflexivity).
      rewrite Hz3 in Hih.
      change (Nat.sub (Datatypes.S (Datatypes.S j)) 1)
        with (Datatypes.S j) in Hih.
      rewrite (lw0_q_pow_zero_succ (Datatypes.S j)) in Hih.
      assert (Hn := lw0_qp_ai_deriv_ft_pow S (Datatypes.S j) x).
      rewrite (q_pow_succ x (Datatypes.S j)) in Hn.
      assert (Hsubn : Nat.sub (Datatypes.S j) 1 = j)
      by (rewrite Nat.sub_succ, Nat.sub_0_r; reflexivity).
      rewrite Hsubn in Hn.
      rewrite (lw0_q_pow_zero_succ j) in Hn.
      assert (Hg : a * (x * q_pow x (Datatypes.S j)
                          * qpoly_eval (lw0_qp_ai (qpoly_deriv S)
                                             (Datatypes.S j)) x
                        + (Z.of_nat (Datatypes.S j) # 1)
                            * q_pow x (Datatypes.S j)
                            * qpoly_eval (lw0_qp_ai S j) x)
                   + (x * (x * q_pow x (Datatypes.S j))
                        * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S)
                                             (Datatypes.S (Datatypes.S j))) x
                      + x * (x * q_pow x (Datatypes.S j))
                          * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S))
                                                   (Datatypes.S (Datatypes.S j))) x
                      + ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)
                          * (x * q_pow x (Datatypes.S j))
                          * qpoly_eval (lw0_qp_ai (qpoly_mul R S)
                                                   (Datatypes.S j)) x)
                   == q_pow x (Datatypes.S j) * a * qpoly_eval S x
                      + (x * q_pow x (Datatypes.S j)
                           * qpoly_eval (qpoly_mul R S) x
                         - 0 * qpoly_eval (qpoly_mul R S) 0%Q)).
      { rewrite Hn. rewrite <- Hih. ring. }
      transitivity (a * (x * q_pow x (Datatypes.S j)
                           * qpoly_eval (lw0_qp_ai (qpoly_deriv S)
                                                (Datatypes.S j)) x
                         + (Z.of_nat (Datatypes.S j) # 1)
                             * q_pow x (Datatypes.S j)
                             * qpoly_eval (lw0_qp_ai S j) x)
                    + (x * (x * q_pow x (Datatypes.S j))
                         * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S)
                                              (Datatypes.S (Datatypes.S j))) x
                       + x * (x * q_pow x (Datatypes.S j))
                           * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S))
                                                (Datatypes.S (Datatypes.S j))) x
                       + ((Z.of_nat (Datatypes.S j) # 1)%Q + 1)
                           * (x * q_pow x (Datatypes.S j))
                           * qpoly_eval (lw0_qp_ai (qpoly_mul R S)
                                                (Datatypes.S j)) x))%Q.
      { ring. }
      { rewrite Hg. ring. }
Qed.
(* The integration-by-parts identity (the [k = 0] instance): the
   integral of [R'S] plus the integral of [RS'] equals [RS(q) - RS(0)]. *)
Lemma lw0_qp_pair_ibp : forall R S q,
  lw0_qp_pair (qpoly_deriv R) S q + lw0_qp_pair R (qpoly_deriv S) q
  == qpoly_eval (qpoly_mul R S) q - qpoly_eval (qpoly_mul R S) 0.
Proof.
  intros R S q.
  unfold lw0_qp_pair.
  unfold lw0_qp_antideriv.
  change (qpoly_eval
            (cons 0 (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S) 0) q).
  change (qpoly_eval
            (cons 0 (lw0_qp_ai (qpoly_mul R (qpoly_deriv S)) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S)) 0) q).
  assert (Hf := lw0_qp_pair_ibp_family R S 0 q).
  assert (H1 : (Z.of_nat 0 # 1)%Q == 0) by reflexivity.
  rewrite H1 in Hf.
  assert (H2 : q_pow q (Datatypes.S 0) == q).
  { change (q_pow q (Datatypes.S 0)) with (q * q_pow q 0).
    change (q_pow q 0) with 1.
    ring. }
  rewrite H2 in Hf.
  change (q_pow q 0) with 1 in Hf.
  change (q_pow 0 0) with 1 in Hf.
  transitivity (q * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_deriv R) S) 0) q
                + q * qpoly_eval (lw0_qp_ai (qpoly_mul R (qpoly_deriv S)) 0) q
                + 0 * 1
                    * qpoly_eval (lw0_qp_ai (qpoly_mul R S)
                                     (Nat.sub 0 1)) q)%Q.
  { ring. }
  { rewrite Hf. ring. }
Qed.


(* ------------------------------------------------------------------ *)
(* The polynomial surrogate layer of the partial sums (sigma / gamma).
   Mathematical content: [sin_partial N] and [cos_partial N] are
   polynomials in [t] (truncated Taylor lists); their coefficient
   lists (lowest degree first) are given by an accumulator recursion
   that wraps segments from the high-degree end toward the low-degree
   end.  Four generalized engines give the exact conversions of the
   evaluation and of the pointwise derivative; everything is stated
   along the pointwise-equality convention at the eval layer.          *)
(* ------------------------------------------------------------------ *)
(* ============================================================ *)
(* Section. The generalized engine family for the evaluation and the  *)
(* derivative evaluation of the sin/cos partial sums (Horner-layer    *)
(* identities)                                                        *)
(* ============================================================ *)

(* The cos-side accumulator recursion (the [gamma_j] list wraps toward
   the low degrees; even index [(-1)^M / (2M+2)!]). *)
Fixpoint lw0_cos_aux (j : nat) (acc : qpoly) : qpoly :=
  match j with
  | Datatypes.O => cons (q_pow (-1) 0 / q_fact 0)%Q acc
  | Datatypes.S M =>
      lw0_cos_aux M
        (cons 0
           (cons (q_pow (-1) (Datatypes.S M)
                   / q_fact (Datatypes.S (Datatypes.S (2 * M))))%Q
              acc))
  end.
(* The cos polynomial surrogate: [cos_qp N = cos_aux N nil]. *)
Definition lw0_cos_qp (N : nat) : qpoly := lw0_cos_aux N nil.

(* Engine one (the generalized sin-side evaluation): the list is the
   [sigma_j] list ++ acc; after the Horner expansion                    *)

(* Engine one (generalized sin evaluation): the Horner evaluation of
   the [sigma_j] list ++ acc equals the partial sum plus the tail
   power times acc. *)
Lemma lw0_sin_aux_eval : forall j acc x,
  qpoly_eval (lw0_sin_aux j acc) x
  == sin_partial j x
     + q_pow x (Datatypes.S (Datatypes.S (2 * j))) * qpoly_eval acc x.
Proof.
  induction j as [|M IH]; intros acc x.
  - unfold sin_partial.
    change (lw0_sin_aux 0 acc)
      with (cons 0 (cons (q_pow (-1) 0 / q_fact 1) acc)).
    change (qpoly_eval (cons 0 (cons (q_pow (-1) 0 / q_fact 1) acc)) x)
      with (0 + x * (q_pow (-1) 0 / q_fact 1 + x * qpoly_eval acc x)).
    change (sin_term 0 x)
      with (q_pow (-1) 0
              * (q_pow x (Datatypes.S (2 * 0))
                 / q_fact (Datatypes.S (2 * 0)))).
    change (q_pow (-1) 0) with 1%Q.
    change (q_pow x (Datatypes.S (2 * 0))) with (x * q_pow x 0)%Q.
    change (q_pow x 0) with 1%Q.
    change (q_fact 1) with ((Z.of_nat 1 # 1) * q_fact 0)%Q.
    change (q_fact (Datatypes.S (2 * 0)))
      with ((Z.of_nat 1 # 1) * q_fact 0)%Q.
    change (q_fact 0) with 1%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (2 * 0))))
      with (x * (x * q_pow x 0))%Q.
    change (q_pow x 0) with 1%Q.
    unfold Qdiv. ring.
  - change (sin_partial (Datatypes.S M) x)
      with (sin_partial M x + sin_term (Datatypes.S M) x).
    set (c := (q_pow (-1) (Datatypes.S M)
               / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q).
    change (lw0_sin_aux (Datatypes.S M) acc)
      with (lw0_sin_aux M (cons 0 (cons c acc))).
    rewrite (IH (cons 0 (cons c acc)) x).
    change (qpoly_eval (cons 0 (cons c acc)) x)
      with (0 + x * (c + x * qpoly_eval acc x)).
    change (sin_term (Datatypes.S M) x)
      with (q_pow (-1) (Datatypes.S M)
              * (q_pow x (Datatypes.S (2 * Datatypes.S M))
                 / q_fact (Datatypes.S (2 * Datatypes.S M)))).
    assert (H2 : Datatypes.S (2 * Datatypes.S M)
                 = Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) by (rewrite Nat.mul_succ_r, !Nat.add_succ_r, Nat.add_0_r; reflexivity).
    rewrite H2.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))).
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (2 * M)))).
    unfold c. unfold Qdiv. ring.
Qed.
(* The sin partial sum vanishes at zero. *)
Lemma lw0_sin_partial_zero : forall N, sin_partial N 0 == 0.
Proof.
  induction N as [|M IH].
  - unfold sin_partial. unfold sin_term.
    change (q_pow (-1) 0) with 1%Q.
    rewrite (lw0_q_pow_zero_succ (2 * 0)).
    unfold Qdiv. ring.
  - unfold sin_partial. rewrite IH. unfold sin_term.
    rewrite (lw0_q_pow_zero_succ (Datatypes.S (2 * Datatypes.S M))).
    unfold Qdiv. ring.
Qed.
(* The evaluation of the sin polynomial surrogate equals the sin
   partial sum (the zero-acc tail term cancels). *)
Lemma lw0_sin_qp_eval : forall N x,
  qpoly_eval (lw0_sin_qp N) x == sin_partial N x.
Proof.
  intros N x. unfold lw0_sin_qp.
  rewrite (lw0_sin_aux_eval N nil x).
  change (qpoly_eval nil x) with 0%Q.
  assert (H0 : q_pow x (Datatypes.S (Datatypes.S (2 * N))) * 0 == 0) by ring.
  rewrite H0. ring.
Qed.
(* The sin polynomial surrogate vanishes at zero. *)
Lemma lw0_sin_qp_zero_eval : forall N, qpoly_eval (lw0_sin_qp N) 0 == 0.
Proof. intros N. rewrite (lw0_sin_qp_eval N 0). exact (lw0_sin_partial_zero N). Qed.

(* Engine two (the generalized cos-side evaluation): the list is the
   [gamma_j] list ++ acc; after the Horner expansion the tail segment
   is multiplied in with the power [t^(2j+1)].  The proof is the
   verbatim template of the established sin-side shape plus an index map:
   [cos_term] uses its own [2j] index (distinct from the sin [2j+1]),
   and the index-conversion equations carry %nat annotations.          *)

(* Engine two (generalized cos evaluation): the Horner evaluation of
   the [gamma_j] list ++ acc equals the cos partial sum plus the tail
   power times acc. *)
Lemma lw0_cos_aux_eval : forall j acc x,
  qpoly_eval (lw0_cos_aux j acc) x
  == cos_partial j x
     + q_pow x (Datatypes.S (2 * j)) * qpoly_eval acc x.
Proof.
  induction j as [|M IH]; intros acc x.
  - unfold cos_partial.
    change (lw0_cos_aux 0 acc) with (cons (q_pow (-1) 0 / q_fact 0) acc).
    change (qpoly_eval (cons (q_pow (-1) 0 / q_fact 0) acc) x)
      with (q_pow (-1) 0 / q_fact 0 + x * qpoly_eval acc x).
    change (cos_term 0 x)
      with (q_pow (-1) 0 * (q_pow x (2 * 0) / q_fact (2 * 0))).
    change (q_pow (-1) 0) with 1%Q.
    change (q_pow x (2 * 0)) with 1%Q.
    change (q_fact (2 * 0)) with 1%Q.
    change (q_fact 0) with 1%Q.
    change (q_pow x (Datatypes.S (2 * 0))) with (x * q_pow x 0)%Q.
    change (q_pow x 0) with 1%Q.
    unfold Qdiv. ring.
  - change (cos_partial (Datatypes.S M) x)
      with (cos_partial M x + cos_term (Datatypes.S M) x).
    set (c := (q_pow (-1) (Datatypes.S M)
               / q_fact (Datatypes.S (Datatypes.S (2 * M))))%Q).
    change (lw0_cos_aux (Datatypes.S M) acc)
      with (lw0_cos_aux M (cons 0 (cons c acc))).
    rewrite (IH (cons 0 (cons c acc)) x).
    change (qpoly_eval (cons 0 (cons c acc)) x)
      with (0 + x * (c + x * qpoly_eval acc x)).
    change (cos_term (Datatypes.S M) x)
      with (q_pow (-1) (Datatypes.S M)
              * (q_pow x (2 * Datatypes.S M)
                 / q_fact (2 * Datatypes.S M))).
    assert (H2 : (2 * Datatypes.S M)%nat
                 = Datatypes.S (Datatypes.S (2 * M))) by (rewrite Nat.mul_succ_r, !Nat.add_succ_r, Nat.add_0_r; reflexivity).
    rewrite H2.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (2 * M)))).
    change (q_pow x (Datatypes.S (Datatypes.S (2 * M))))
      with (x * q_pow x (Datatypes.S (2 * M))).
    unfold c. unfold Qdiv. ring.
Qed.
(* The cos partial sum is [1] at zero. *)
Lemma lw0_cos_partial_zero : forall N, cos_partial N 0 == 1.
Proof.
  induction N as [|M IH].
  - unfold cos_partial. unfold cos_term.
    change (q_pow (-1) 0) with 1%Q.
    change (q_pow 0 (2 * 0) / q_fact (2 * 0)) with 1%Q.
    unfold Qdiv. ring.
  - unfold cos_partial. rewrite IH. unfold cos_term.
    assert (H2 : (2 * Datatypes.S M)%nat
                 = Datatypes.S (Datatypes.S (2 * M))) by (rewrite Nat.mul_succ_r, !Nat.add_succ_r, Nat.add_0_r; reflexivity).
    rewrite H2.
    rewrite (lw0_q_pow_zero_succ (Datatypes.S (2 * M))).
    unfold Qdiv. ring.
Qed.
(* The evaluation of the cos polynomial surrogate equals the cos
   partial sum. *)
Lemma lw0_cos_qp_eval : forall N x,
  qpoly_eval (lw0_cos_qp N) x == cos_partial N x.
Proof.
  intros N x. unfold lw0_cos_qp.
  rewrite (lw0_cos_aux_eval N nil x).
  change (qpoly_eval nil x) with 0%Q.
  assert (H0 : q_pow x (Datatypes.S (2 * N)) * 0 == 0) by ring.
  rewrite H0. ring.
Qed.
(* The cos polynomial surrogate is [1] at zero. *)
Lemma lw0_cos_qp_zero_eval : forall N, qpoly_eval (lw0_cos_qp N) 0 == 1.
Proof. intros N. rewrite (lw0_cos_qp_eval N 0). exact (lw0_cos_partial_zero N). Qed.

(* ------------------------------------------------------------------ *)
(* The two deriv pieces: a three-term generalized engine at the eval
   layer.  Mathematical content: the list-deriv evaluation of
   [sin_aux j acc] equals [gamma_j + (2j+2)*t^{2j+1}*acc +
   t^{2j+2}*acc']; the list-deriv evaluation of [cos_aux (S i) acc]
   equals [-sigma_i + (2i+3)*t^{2i+2}*acc + t^{2i+3}*acc'] (the shift
   of [gamma_{S i}' = -sigma_i] by one position).  At the induction
   step, the cancellation of the segment-head coefficient goes through
   the manual chain [q_fact_succ] + [Qinv_mult_distr] +
   [lw0_q_int_inv] (of the [lw0_q_div_int_mul] kind); the segment-head
   quotient is normalized in one piece by change at the base case
   (splitting one-sided [Qinv] atoms is off limits); nat index
   equations are always annotated in %nat.                             *)
(* ------------------------------------------------------------------ *)

(* Generalized cancellation helper: for positive [z],
   [(z#1) * (a / ((z#1) * b)) = a / b].  The proof is the pure
   syntactic re-association chain of [Qmult_assoc]/[Qmult_comm] in the
   [lw0_q_div_int_mul] style (ring cannot                                *)

(* Generalized cancellation helper: for positive [z],
   [(z#1) * (a / ((z#1) * b)) = a / b] (a pure syntactic [Qmult]
   re-association chain). *)
Lemma lw0_q_div_int_mul_gen : forall (z : Z) (a b : Q),
  (0 < z)%Z -> (z # 1) * (a / ((z # 1) * b)) == a / b.
Proof.
  intros z a b Hz.
  change (a / ((z # 1) * b)) with (a * / ((z # 1) * b)).
  change (a / b) with (a * / b).
  rewrite Qinv_mult_distr.
  rewrite (Qmult_assoc (z # 1) a (/ (z # 1) * / b)).
  rewrite (Qmult_comm (z # 1) a).
  rewrite <- (Qmult_assoc a (z # 1) (/ (z # 1) * / b)).
  rewrite (Qmult_assoc (z # 1) (/ (z # 1)) (/ b)).
  rewrite (lw0_q_int_inv z Hz).
  ring.
Qed.
(* Generalized deriv evaluation (sin side): [gamma_j +
   (2j+2)*t^{2j+1}*acc + t^{2j+2}*acc']. *)
Lemma lw0_sin_aux_deriv_eval : forall j acc x,
  qpoly_eval (qpoly_deriv (lw0_sin_aux j acc)) x
  == cos_partial j x
     + q_pow x (Datatypes.S (2 * j))
         * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)
              * qpoly_eval acc x)
     + q_pow x (Datatypes.S (Datatypes.S (2 * j)))
         * qpoly_eval (qpoly_deriv acc) x.
Proof.
  induction j as [|M IH]; intros acc x.
  - unfold cos_partial.
    change (lw0_sin_aux 0 acc)
      with (cons 0 (cons (q_pow (-1) 0 / q_fact 1) acc)).
    change (qpoly_deriv (cons 0 (cons (q_pow (-1) 0 / q_fact 1) acc)))
      with (qpoly_add (cons (q_pow (-1) 0 / q_fact 1) acc)
              (cons 0 (qpoly_deriv (cons (q_pow (-1) 0 / q_fact 1) acc)))).
    rewrite (qpoly_eval_add (cons (q_pow (-1) 0 / q_fact 1) acc)
               (cons 0 (qpoly_deriv (cons (q_pow (-1) 0 / q_fact 1) acc))) x).
    change (qpoly_eval
              (cons 0 (qpoly_deriv (cons (q_pow (-1) 0 / q_fact 1) acc))) x)
      with (0 + x * qpoly_eval
              (qpoly_deriv (cons (q_pow (-1) 0 / q_fact 1) acc)) x).
    rewrite (qpoly_eval_deriv_cons (q_pow (-1) 0 / q_fact 1) acc x).
    change (qpoly_eval (cons (q_pow (-1) 0 / q_fact 1) acc) x)
      with (q_pow (-1) 0 / q_fact 1 + x * qpoly_eval acc x).
    change (cos_term 0 x) with 1%Q.
    change (q_pow (-1) 0 / q_fact 1) with 1%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (2 * 0))))
      with (x * (x * q_pow x 0))%Q.
    change (q_pow x (Datatypes.S (2 * 0))) with (x * q_pow x 0)%Q.
    change (q_pow x 0) with 1%Q.
    change (Z.of_nat (Datatypes.S (Datatypes.S (2 * 0))) # 1)
      with (1 + 1)%Q.
    unfold Qdiv. ring.
  - change (cos_partial (Datatypes.S M) x)
      with (cos_partial M x + cos_term (Datatypes.S M) x).
    set (c := (q_pow (-1) (Datatypes.S M)
               / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q).
    change (lw0_sin_aux (Datatypes.S M) acc)
      with (lw0_sin_aux M (cons 0 (cons c acc))).
    rewrite (IH (cons 0 (cons c acc)) x).
    change (qpoly_eval (cons 0 (cons c acc)) x)
      with (0 + x * (c + x * qpoly_eval acc x)).
    change (qpoly_deriv (cons 0 (cons c acc)))
      with (qpoly_add (cons c acc) (cons 0 (qpoly_deriv (cons c acc)))).
    rewrite (qpoly_eval_add (cons c acc)
               (cons 0 (qpoly_deriv (cons c acc))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (cons c acc))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (cons c acc)) x).
    rewrite (qpoly_eval_deriv_cons c acc x).
    change (qpoly_eval (cons c acc) x)
      with (c + x * qpoly_eval acc x).
    change (cos_term (Datatypes.S M) x)
      with (q_pow (-1) (Datatypes.S M)
              * (q_pow x (2 * Datatypes.S M)
                 / q_fact (2 * Datatypes.S M))).
    assert (H2 : Datatypes.S (2 * Datatypes.S M)
                 = Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) by (rewrite Nat.mul_succ_r, !Nat.add_succ_r, Nat.add_0_r; reflexivity).
    rewrite H2.
    assert (H2b : (2 * Datatypes.S M)%nat
                  = Datatypes.S (Datatypes.S (2 * M))) by (rewrite Nat.mul_succ_r, !Nat.add_succ_r, Nat.add_0_r; reflexivity).
    rewrite H2b.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (2 * M))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (2 * M))))
      with (x * q_pow x (Datatypes.S (2 * M)))%Q.
    change (q_pow x (Datatypes.S (2 * M)))
      with (x * q_pow x (2 * M))%Q.
    assert (Hpos : (0 < Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Z) by (change 0%Z with (Z.of_nat 0);
            apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))); apply Nat.lt_0_succ).
    assert (Hn3 : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))
                  = (Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) + 1)%Z) by (rewrite Nat2Z.inj_succ; symmetry; apply Z.add_1_r).
    assert (Hz3 : ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)%Q + 1)%Q
                  == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q) by (unfold Qeq; cbn [Qnum Qden Qplus Qmult];
      rewrite Hn3, !Z.mul_1_r, ?Z.mul_1_l; reflexivity).
    assert (Hn4 : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                  = (Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) + 2)%Z) by (rewrite !Nat2Z.inj_succ, <- !Z.add_1_r, <- Z.add_assoc; reflexivity).
    assert (Hz4 : ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)%Q + 1 + 1)%Q
                  == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) # 1)%Q) by (unfold Qeq; cbn [Qnum Qden Qplus Qmult];
      rewrite Hn4, !Z.mul_1_r, ?Z.mul_1_l, <- Z.add_assoc; reflexivity).
    assert (Hkey : (Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)
                     * (q_pow (-1) (Datatypes.S M)
                        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                     + (q_pow (-1) (Datatypes.S M)
                        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                   == q_pow (-1) (Datatypes.S M)
                      / q_fact (Datatypes.S (Datatypes.S (2 * M)))).
    { unfold c.
      transitivity (((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)%Q + 1)
                      * (q_pow (-1) (Datatypes.S M)
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
      { ring. }
      rewrite Hz3.
      rewrite (q_fact_succ (Datatypes.S (Datatypes.S (2 * M)))).
      rewrite (lw0_q_div_int_mul_gen
                 (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                 (q_pow (-1) (Datatypes.S M))
                 (q_fact (Datatypes.S (Datatypes.S (2 * M)))) Hpos).
      reflexivity. }
    assert (Hza : ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)
                     * qpoly_eval acc x
                     + qpoly_eval acc x + qpoly_eval acc x)%Q
                  == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) # 1)
                       * qpoly_eval acc x).
    { transitivity (((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)%Q + 1 + 1)
                      * qpoly_eval acc x).
      { ring. }
      rewrite Hz4. ring. }
    transitivity (cos_partial M x
                  + (x * (x * q_pow x (2 * M)))
                      * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1) * c + c)
                  + (x * (x * (x * q_pow x (2 * M))))
                      * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * M))) # 1)
                           * qpoly_eval acc x
                         + qpoly_eval acc x + qpoly_eval acc x)
                  + (x * (x * (x * (x * q_pow x (2 * M)))))
                      * qpoly_eval (qpoly_deriv acc) x)%Q.
    { ring. }
    unfold c.
    rewrite Hkey. rewrite Hza.
    unfold Qdiv. ring.
Qed.
(* Generalized deriv evaluation (cos side): [-sigma_i +
   (2i+3)*t^{2i+2}*acc + t^{2i+3}*acc']. *)
Lemma lw0_cos_aux_deriv_eval_S : forall i acc x,
  qpoly_eval (qpoly_deriv (lw0_cos_aux (Datatypes.S i) acc)) x
  == - sin_partial i x
     + q_pow x (2 * Datatypes.S i)
         * ((Z.of_nat (Datatypes.S (2 * Datatypes.S i)) # 1)
              * qpoly_eval acc x)
     + q_pow x (Datatypes.S (2 * Datatypes.S i))
         * qpoly_eval (qpoly_deriv acc) x.
Proof.
  induction i as [|M IH]; intros acc x.
  - unfold sin_partial.
    set (c0 := (q_pow (-1) (Datatypes.S 0)
                / q_fact (Datatypes.S (Datatypes.S (2 * 0))))%Q).
    change (lw0_cos_aux (Datatypes.S 0) acc)
      with (lw0_cos_aux 0 (cons 0 (cons c0 acc))).
    change (lw0_cos_aux 0 (cons 0 (cons c0 acc)))
      with (cons (q_pow (-1) 0 / q_fact 0) (cons 0 (cons c0 acc))).
    change (qpoly_deriv
              (cons (q_pow (-1) 0 / q_fact 0) (cons 0 (cons c0 acc))))
      with (qpoly_add (cons 0 (cons c0 acc))
              (cons 0 (qpoly_deriv (cons 0 (cons c0 acc))))).
    rewrite (qpoly_eval_add (cons 0 (cons c0 acc))
               (cons 0 (qpoly_deriv (cons 0 (cons c0 acc)))) x).
    change (qpoly_eval
              (cons 0 (qpoly_deriv (cons 0 (cons c0 acc)))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (cons 0 (cons c0 acc))) x).
    rewrite (qpoly_eval_deriv_cons 0 (cons c0 acc) x).
    change (qpoly_eval (cons 0 (cons c0 acc)) x)
      with (0 + x * (c0 + x * qpoly_eval acc x)).
    rewrite (qpoly_eval_deriv_cons c0 acc x).
    change (qpoly_eval (cons c0 acc) x)
      with (c0 + x * qpoly_eval acc x).
    change (sin_term 0 x)
      with (q_pow (-1) 0
              * (q_pow x (Datatypes.S (2 * 0))
                 / q_fact (Datatypes.S (2 * 0)))).
    change (q_pow (-1) 0) with 1%Q.
    change (q_pow x (Datatypes.S (2 * Datatypes.S 0)))
      with (x * q_pow x (2 * Datatypes.S 0))%Q.
    change (q_pow x (2 * Datatypes.S 0)) with (x * (x * q_pow x 0))%Q.
    change (q_pow x (Datatypes.S (2 * 0))) with (x * q_pow x 0)%Q.
    change (q_pow x 0) with 1%Q.
    change (Z.of_nat (Datatypes.S (2 * Datatypes.S 0)) # 1)
      with (1 + 1 + 1)%Q.
    assert (Hkey0 : (2 * x) * (q_pow (-1) (Datatypes.S 0)
                               / q_fact (Datatypes.S (Datatypes.S (2 * 0))))
                    == - (1 * ((x * 1)
                               / q_fact (Datatypes.S (2 * 0))))).
    { change (q_fact (Datatypes.S (Datatypes.S (2 * 0))))
        with (((2 # 1) * q_fact (Datatypes.S (2 * 0)))%Q).
      change (q_pow (-1) (Datatypes.S 0)) with (-1)%Q.
      assert (Hpos2 : (0 < 2)%Z) by reflexivity.
      rewrite <- (Qmult_assoc (2 # 1) x
                    ((-1) / ((2 # 1) * q_fact (Datatypes.S (2 * 0))))).
      rewrite (Qmult_comm x
                 ((-1) / ((2 # 1) * q_fact (Datatypes.S (2 * 0))))).
      rewrite (Qmult_assoc (2 # 1)
                 ((-1) / ((2 # 1) * q_fact (Datatypes.S (2 * 0)))) x).
      rewrite (lw0_q_div_int_mul_gen 2 (-1)
                 (q_fact (Datatypes.S (2 * 0))) Hpos2).
      unfold Qdiv. ring. }
    transitivity ((2 * x) * c0
                  + (x * (x * 1)) * ((1 + 1 + 1) * qpoly_eval acc x)
                  + (x * (x * (x * 1)))
                      * qpoly_eval (qpoly_deriv acc) x)%Q.
    { ring. }
    unfold c0.
    rewrite Hkey0.
    unfold Qdiv. ring.
  - change (- sin_partial (Datatypes.S M) x)
      with (- (sin_partial M x + sin_term (Datatypes.S M) x))%Q.
    set (c := (q_pow (-1) (Datatypes.S (Datatypes.S M))
               / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S M))))%Q).
    change (lw0_cos_aux (Datatypes.S (Datatypes.S M)) acc)
      with (lw0_cos_aux (Datatypes.S M) (cons 0 (cons c acc))).
    rewrite (IH (cons 0 (cons c acc)) x).
    change (qpoly_eval (cons 0 (cons c acc)) x)
      with (0 + x * (c + x * qpoly_eval acc x)).
    change (qpoly_deriv (cons 0 (cons c acc)))
      with (qpoly_add (cons c acc) (cons 0 (qpoly_deriv (cons c acc)))).
    rewrite (qpoly_eval_add (cons c acc)
               (cons 0 (qpoly_deriv (cons c acc))) x).
    change (qpoly_eval (cons 0 (qpoly_deriv (cons c acc))) x)
      with (0 + x * qpoly_eval (qpoly_deriv (cons c acc)) x).
    rewrite (qpoly_eval_deriv_cons c acc x).
    change (qpoly_eval (cons c acc) x)
      with (c + x * qpoly_eval acc x).
    change (sin_term (Datatypes.S M) x)
      with (q_pow (-1) (Datatypes.S M)
              * (q_pow x (Datatypes.S (2 * Datatypes.S M))
                 / q_fact (Datatypes.S (2 * Datatypes.S M)))).
    assert (H2 : Datatypes.S (2 * Datatypes.S M)
                 = Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) by (rewrite Nat.mul_succ_r, !Nat.add_succ_r, Nat.add_0_r; reflexivity).
    rewrite H2.
    assert (H2b : (2 * Datatypes.S M)%nat
                  = Datatypes.S (Datatypes.S (2 * M))) by (rewrite Nat.mul_succ_r, !Nat.add_succ_r, Nat.add_0_r; reflexivity).
    rewrite H2b.
    assert (H4 : Datatypes.S (2 * Datatypes.S (Datatypes.S M))
                 = Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))) by (rewrite !Nat.mul_succ_r, !Nat.add_succ_r, !Nat.add_0_r; reflexivity).
    rewrite H4.
    assert (H3 : (2 * Datatypes.S (Datatypes.S M))%nat
                 = Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) by (rewrite !Nat.mul_succ_r, !Nat.add_succ_r, !Nat.add_0_r; reflexivity).
    rewrite H3.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
      with (x * q_pow x (Datatypes.S (Datatypes.S (2 * M))))%Q.
    change (q_pow x (Datatypes.S (Datatypes.S (2 * M))))
      with (x * q_pow x (Datatypes.S (2 * M)))%Q.
    change (q_pow x (Datatypes.S (2 * M)))
      with (x * q_pow x (2 * M))%Q.
    assert (Hpos4 : (0 < Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))%Z) by (change 0%Z with (Z.of_nat 0);
            apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))); apply Nat.lt_0_succ).
    assert (Hn4c : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))
                   = (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) + 1)%Z) by (rewrite Nat2Z.inj_succ; symmetry; apply Z.add_1_r).
    assert (Hz3c : ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q + 1)%Q
                   == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) # 1)%Q) by (unfold Qeq; cbn [Qnum Qden Qplus Qmult];
      rewrite Hn4c, !Z.mul_1_r, ?Z.mul_1_l; reflexivity).
    assert (Hn5c : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
                   = (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) + 2)%Z) by (rewrite !Nat2Z.inj_succ, <- !Z.add_1_r, <- Z.add_assoc; reflexivity).
    assert (Hz5c : ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q + 1 + 1)%Q
                   == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))) # 1)%Q) by (unfold Qeq; cbn [Qnum Qden Qplus Qmult];
      rewrite Hn5c, !Z.mul_1_r, ?Z.mul_1_l, <- Z.add_assoc; reflexivity).
    assert (HkeyM : (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)
                      * (q_pow (-1) (Datatypes.S (Datatypes.S M))
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
                      + (q_pow (-1) (Datatypes.S (Datatypes.S M))
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
                    == - (q_pow (-1) (Datatypes.S M)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
    { unfold c.
      transitivity (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q + 1)
                      * (q_pow (-1) (Datatypes.S (Datatypes.S M))
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))).
      { ring. }
      rewrite Hz3c.
      rewrite (q_fact_succ (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))).
      rewrite (lw0_q_div_int_mul_gen
                 (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
                 (q_pow (-1) (Datatypes.S (Datatypes.S M)))
                 (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) Hpos4).
      change (q_pow (-1) (Datatypes.S (Datatypes.S M)))
        with ((-1) * q_pow (-1) (Datatypes.S M))%Q.
      unfold Qdiv. ring. }
    assert (HzaC : ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)
                      * qpoly_eval acc x
                      + qpoly_eval acc x + qpoly_eval acc x)%Q
                   == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))) # 1)
                        * qpoly_eval acc x).
    { transitivity (((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)%Q + 1 + 1)
                      * qpoly_eval acc x).
      { ring. }
      rewrite Hz5c. ring. }
    transitivity (- sin_partial M x
                  + (x * (x * (x * q_pow x (2 * M))))
                      * ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1) * c + c)
                  + (x * (x * (x * (x * q_pow x (2 * M)))))
                      * ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))) # 1)
                           * qpoly_eval acc x
                         + qpoly_eval acc x + qpoly_eval acc x)
                  + (x * (x * (x * (x * (x * q_pow x (2 * M))))))
                      * qpoly_eval (qpoly_deriv acc) x)%Q.
    { ring. }
    unfold c.
    rewrite H2.
    rewrite HkeyM. rewrite HzaC.
    unfold Qdiv. ring.
Qed.
(* The derivative evaluation of the sin surrogate equals the cos
   partial sum. *)
Lemma lw0_sin_qp_deriv_eval : forall N x,
  qpoly_eval (qpoly_deriv (lw0_sin_qp N)) x == cos_partial N x.
Proof.
  intros N x. unfold lw0_sin_qp.
  rewrite (lw0_sin_aux_deriv_eval N nil x).
  change (qpoly_eval (qpoly_deriv nil) x) with 0%Q.
  change (qpoly_eval nil x) with 0%Q.
  assert (H0 : q_pow x (Datatypes.S (2 * N))
                 * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * N))) # 1) * 0) == 0) by ring.
  assert (H1 : q_pow x (Datatypes.S (Datatypes.S (2 * N))) * 0 == 0) by ring.
  rewrite H0. rewrite H1. ring.
Qed.
(* The derivative evaluation of the cos surrogate at the [S N] layer
   equals the negated sin partial sum. *)
Lemma lw0_cos_qp_deriv_eval : forall N x,
  qpoly_eval (qpoly_deriv (lw0_cos_qp (Datatypes.S N))) x == - sin_partial N x.
Proof.
  intros N x. unfold lw0_cos_qp.
  rewrite (lw0_cos_aux_deriv_eval_S N nil x).
  change (qpoly_eval (qpoly_deriv nil) x) with 0%Q.
  change (qpoly_eval nil x) with 0%Q.
  assert (H0 : q_pow x (2 * Datatypes.S N)
                 * ((Z.of_nat (Datatypes.S (2 * Datatypes.S N)) # 1) * 0) == 0) by ring.
  assert (H1 : q_pow x (Datatypes.S (2 * Datatypes.S N)) * 0 == 0) by ring.
  rewrite H0. rewrite H1. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* The absolute-value envelope of the paired product (the proof face
   is a term-by-term [Qabs_triangle] suppression).                      *)
(* Mathematical content: [|<f,g>_q| = |q * sum_j c_j q^j/(j+1)| <=
   |q| * sum_j |c_j| * |q|^j / (j+1)] (the [c_j] are the coefficients
   of [mul f g]; the right-hand side is exactly the value at [|q|] of
   the antiderivative slice of (abs mapped over [mul f g])).           *)
(* The engine statement takes the same [ai] form on both sides:
   [|A_k(p)(x)| <= A_k(map Qabs p)(|x|)] -- at the induction step the
   segment head [|a/(z#1)|] is suppressed by the pure equation chain
   [Qabs_Qmult] + [Qabs_Qinv] + [Qabs_pos] (for positive [z],
   [|z#1| == z#1]); the whole piece has no division-order stretching
   ([Qmult_le_compat_r] exists only in the right-multiplication form,
   and no library piece stretches on the left, so this shape avoids
   the issue).  The upgraded shape ([mul (map abs f) (map abs g)]) is
   still two pieces short -- coefficient-dominance suppression and the
   removal of the [1/(j+1)] factor -- and remains unattempted (the
   upgrade is not required).                                           *)
(* ------------------------------------------------------------------ *)
(* Pointwise coefficient map (the carrier operator of the abs
   envelope). *)
Fixpoint qpoly_map (h : Q -> Q) (p : qpoly) : qpoly :=
  match p with
  | nil => nil
  | cons a p' => cons (h a) (qpoly_map h p')
  end.
(* Absolute-value splitting for division by a positive denominator:
   [|a/(z#1)| = |a|/(z#1)]. *)
Lemma lw0_q_abs_div : forall (z : Z) (a : Q),
  (0 < z)%Z -> Qabs (a / (z # 1)) == Qabs a / (z # 1).
Proof.
  intros z a Hz.
  assert (H0 : (0 <= (z # 1))%Q) by (unfold Qle; cbn [Qnum Qden]; rewrite !Z.mul_1_r;
            exact (Z.lt_le_incl 0 z Hz)).
  change (a / (z # 1)) with (a * / (z # 1)).
  change (Qabs a / (z # 1)) with (Qabs a * / (z # 1)).
  rewrite Qabs_Qmult.
  rewrite Qabs_Qinv.
  rewrite (Qabs_pos (z # 1) H0).
  reflexivity.
Qed.
(* The antiderivative-slice absolute-value envelope:
   [|A_k(p)(x)| <= A_k(map abs p)(|x|)] ([Qabs_triangle] suppression). *)
Lemma lw0_qp_ai_abs_bound : forall p k x,
  Qabs (qpoly_eval (lw0_qp_ai p k) x)
  <= qpoly_eval (lw0_qp_ai (qpoly_map Qabs p) k) (Qabs x).
Proof.
  induction p as [|a p IH]; intros k x.
  - change (qpoly_eval (lw0_qp_ai nil k) x) with 0%Q.
    change (lw0_qp_ai (qpoly_map Qabs nil) k) with (@nil Q).
    change (qpoly_eval (@nil Q) (Qabs x)) with 0%Q.
    change (Qabs 0) with 0%Q.
    apply Qle_refl.
  - assert (Hpos : (0 < Z.of_nat (S k))%Z) by (change 0%Z with (Z.of_nat 0);
            apply (proj1 (Nat2Z.inj_lt 0 (S k))); apply Nat.lt_0_succ).
    change (qpoly_map Qabs (cons a p)) with (cons (Qabs a) (qpoly_map Qabs p)).
    change (lw0_qp_ai (cons (Qabs a) (qpoly_map Qabs p)) k)
      with (cons (Qabs a / (Z.of_nat (S k) # 1))
                    (lw0_qp_ai (qpoly_map Qabs p) (S k))).
    change (qpoly_eval
              (cons (Qabs a / (Z.of_nat (S k) # 1))
                    (lw0_qp_ai (qpoly_map Qabs p) (S k))) (Qabs x))
      with (Qabs a / (Z.of_nat (S k) # 1)
              + Qabs x * qpoly_eval (lw0_qp_ai (qpoly_map Qabs p) (S k)) (Qabs x)).
    rewrite (lw0_qp_ai_cons_eval a p k x).
    apply (Qle_trans
            (Qabs (a / (Z.of_nat (S k) # 1)
                    + x * qpoly_eval (lw0_qp_ai p (S k)) x))
            (Qabs (a / (Z.of_nat (S k) # 1))
              + Qabs (x * qpoly_eval (lw0_qp_ai p (S k)) x))).
    + apply Qabs_triangle.
    + rewrite (lw0_q_abs_div (Z.of_nat (S k)) a Hpos).
      rewrite (Qabs_Qmult x (qpoly_eval (lw0_qp_ai p (S k)) x)).
      apply Qplus_le_compat.
      * apply Qle_refl.
      * apply (lw0_q_mult_le_l (Qabs x)).
        -- apply Qabs_nonneg.
        -- apply IH.
Qed.
(* ============================================================ *)
(* Section. The coefficient functionals and the die budget decision   *)
(* family (factorial-weight identities at the coef level)             *)
(* ============================================================ *)

(* The die budget decision: whether [p] is fully differentiable
   within [n] steps (the two-expenditure form). *)
Fixpoint lw0_die (p : qpoly) (n : nat) : bool :=
  match p with
  | nil => true
  | cons _ p' =>
      match n with
      | Datatypes.O => false
      | Datatypes.S n' => lw0_die p' (Datatypes.S n') && lw0_die p' n'
      end
  end.
(* The successor of the alternating factor is its negation
   (definitional). *)
Lemma lw0_alt_opp : forall j : nat, lw0_alt (Datatypes.S j) == Qopp (lw0_alt j).
Proof. intros j. reflexivity. Qed.
(* The [Qmake] add-one bridge: [(1+z)#1 = 1 + (z#1)] (a unit of
   multiplication chain at the [Z] numerator level). *)
Lemma lw0_Qmake_succ_eq : forall z : Z,
  ((1 + z) # 1)%Q = (1 + (z # 1)%Q)%Q.
Proof.
  intros z.
  replace (1 + (z # 1)%Q)%Q with (Qmake (1 * 1 + z * 1) (1 * 1))
    by reflexivity.
  apply f_equal2.
  - rewrite !Z.mul_1_r, ?Z.mul_1_l. reflexivity.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The coefficient functional: j-th coefficient of a coefficient list. *)
(* ------------------------------------------------------------------ *)
(* The coefficient functional: take the [j]-th coefficient (zero once
   [j] exceeds the list length). *)
Fixpoint lw0_coef (j : nat) (p : QPoly) {struct p} : Q :=
  match p with
  | nil => 0%Q
  | cons a p' =>
      match j with
      | 0%nat => a
      | Datatypes.S j' => lw0_coef j' p'
      end
  end.
(* Addition distributes over the coefficients pointwise. *)
Lemma lw0_coef_add : forall (j : nat) (p q : QPoly),
  lw0_coef j (qpoly_add p q) == lw0_coef j p + lw0_coef j q.
Proof.
  intros j p; revert j; induction p as [|a p IH]; intros j q.
  - destruct q as [|b q]; simpl; ring.
  - destruct q as [|b q].
    + simpl. ring.
    + destruct j as [|j'].
      * simpl. reflexivity.
      * change (qpoly_add (cons a%Q p) (cons b%Q q))
          with (cons (a + b)%Q (qpoly_add p q)).
        change (lw0_coef (Datatypes.S j') (cons (a + b)%Q (qpoly_add p q)))
          with (lw0_coef j' (qpoly_add p q)).
        change (lw0_coef (Datatypes.S j') (cons a%Q p)) with (lw0_coef j' p).
        change (lw0_coef (Datatypes.S j') (cons b%Q q)) with (lw0_coef j' q).
        apply (IH j' q).
Qed.
(* Scalar multiplication distributes over the coefficients
   pointwise. *)
Lemma lw0_coef_scalar : forall j a p,
  lw0_coef j (qpoly_scalar a p) == a * lw0_coef j p.
Proof.
  intros j a p; revert j; induction p as [|b p IH]; intros j.
  - simpl. ring.
  - destruct j as [|j'].
    + simpl. ring.
    + change (qpoly_scalar a (cons b%Q p))
        with (cons (a * b)%Q (qpoly_scalar a p)).
      change (lw0_coef (Datatypes.S j') (cons (a * b)%Q (qpoly_scalar a p)))
        with (lw0_coef j' (qpoly_scalar a p)).
      change (lw0_coef (Datatypes.S j') (cons b%Q p)) with (lw0_coef j' p).
      apply (IH j').
Qed.
(* The coefficient shift law of the derivative:
   [coef j (deriv p) = (j+1) * coef (j+1) p]. *)
Lemma lw0_coef_deriv : forall j p,
  lw0_coef j (qpoly_deriv p)
  == (Z.of_nat (Datatypes.S j) # 1)%Q * lw0_coef (Datatypes.S j) p.
Proof.
  intros j p; revert j; induction p as [|a p IH]; intro j; simpl.
  - ring.
  - rewrite lw0_coef_add.
    destruct j as [|j'].
    + simpl. ring.
    + simpl (lw0_coef (Datatypes.S j') (cons 0%Q (qpoly_deriv p))).
      rewrite (IH j').
      replace (Z.pos (PosDef.Pos.of_succ_nat (Datatypes.S j')))
        with (Z.of_nat (Datatypes.S (Datatypes.S j')))%Z by reflexivity.
      replace (Z.of_nat (Datatypes.S (Datatypes.S j')))
        with (1 + Z.of_nat (Datatypes.S j'))%Z
        by (rewrite (Nat2Z.inj_succ j'), !Nat2Z.inj_succ, Z.add_1_l; reflexivity).
      replace ((1 + Z.of_nat (Datatypes.S j')) # 1)%Q
        with (1 + (Z.of_nat (Datatypes.S j') # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      ring.
Qed.

(* Coefficients of iterated derivatives, in multiplied form (no         *)
(* division): coefficient j of the k-th derivative carries the          *)
(* The factorial-weight identity of iterated-derivative coefficients:
   [coef j (iter k p) * j! = (j+k)! * coef (j+k) p]. *)
Lemma lw0_coef_iter_mul : forall k j p,
  lw0_coef j (qpoly_deriv_iter k p) * q_fact j
  == q_fact (j + k) * lw0_coef (j + k) p.
Proof.
  induction k as [|k IH]; intros j p.
  - rewrite Nat.add_0_r. rewrite Qmult_comm. reflexivity.
  - assert (IHj := IH (Datatypes.S j) p).
    replace (Datatypes.S j + k)%nat with (Datatypes.S (j + k))%nat in IHj
      by (rewrite Nat.add_succ_l; reflexivity).
    replace (j + Datatypes.S k)%nat with (Datatypes.S (j + k))%nat
      by (rewrite Nat.add_succ_r; reflexivity).
    simpl (qpoly_deriv_iter (Datatypes.S k) p).
    rewrite lw0_coef_deriv.
    rewrite q_fact_succ in IHj. rewrite q_fact_succ in IHj.
    rewrite (q_fact_succ (j + k)).
    rewrite (Qmult_comm (Z.of_nat (Datatypes.S j) # 1)%Q
               (lw0_coef (Datatypes.S j) (qpoly_deriv_iter k p))).
    rewrite <- (Qmult_assoc (lw0_coef (Datatypes.S j) (qpoly_deriv_iter k p))
               (Z.of_nat (Datatypes.S j) # 1)%Q (q_fact j)).
    exact IHj.
Qed.
(* Iterated differentiation commutes with addition (at the
   coefficient level). *)
Lemma lw0_coef_iter_add : forall k j u v,
  lw0_coef j (qpoly_deriv_iter k (qpoly_add u v))
  == lw0_coef j (qpoly_deriv_iter k u) + lw0_coef j (qpoly_deriv_iter k v).
Proof.
  induction k as [|k IH]; intros j u v; simpl.
  - apply lw0_coef_add.
  - rewrite !lw0_coef_deriv, (IH (Datatypes.S j) u v). ring.
Qed.
(* Iterated differentiation commutes with scalar multiplication (at
   the coefficient level). *)
Lemma lw0_coef_iter_scalar : forall k j a p,
  lw0_coef j (qpoly_deriv_iter k (qpoly_scalar a p))
  == a * lw0_coef j (qpoly_deriv_iter k p).
Proof.
  induction k as [|k IH]; intros j a p; simpl.
  - apply lw0_coef_scalar.
  - rewrite lw0_coef_deriv, lw0_coef_deriv, (IH (Datatypes.S j) a p). ring.
Qed.
(* The die budget is monotone: a wider budget inherits the
   decision. *)
Lemma lw0_die_budget_mono : forall (p : QPoly) (m k : nat),
  lw0_die p m = true -> (m <= k)%nat -> lw0_die p k = true.
Proof.
  induction p as [|a p IH]; intros m k Hm Hk.
  - reflexivity.
  - destruct m as [|m'].
    + cbn [lw0_die] in Hm. discriminate Hm.
    + cbn [lw0_die] in Hm. apply andb_true_iff in Hm.
      destruct Hm as [H1 H2].
      destruct k as [|k'].
      * exfalso. exact (Nat.nle_succ_0 m' Hk).
      * cbn [lw0_die]. apply andb_true_iff. split.
        -- apply (IH (Datatypes.S m') (Datatypes.S k')); [ exact H1 | exact Hk ].
        -- apply (IH m' k'); [ exact H2 | exact (proj2 (Nat.succ_le_mono m' k') Hk) ].
Qed.
(* [die] is invariant under scalar multiplication. *)
Lemma lw0_die_scalar : forall (c : Q) (p : qpoly) (M : nat),
  lw0_die (qpoly_scalar c p) M = lw0_die p M.
Proof.
  intros c p. induction p as [|b p IH]; intros M.
  - reflexivity.
  - destruct M as [|M'].
    + reflexivity.
    + cbn [lw0_die qpoly_scalar].
      rewrite (IH (Datatypes.S M')). rewrite (IH M'). reflexivity.
Qed.
(* The die budget adds over addition: if both lists carry an [M]
   budget, so does their sum. *)
Lemma lw0_die_add : forall (M : nat) (p q : qpoly),
  lw0_die p M = true -> lw0_die q M = true ->
  lw0_die (qpoly_add p q) M = true.
Proof.
  intros M p. revert M. induction p as [|a p' IH]; intros M q Hp Hq.
  - exact Hq.
  - destruct q as [|b q'].
    + exact Hp.
    + destruct M as [|M'].
      * cbn [lw0_die] in Hp. discriminate Hp.
      * cbn [lw0_die] in Hp. cbn [lw0_die] in Hq.
        apply andb_true_iff in Hp. destruct Hp as [Hp1 Hp2].
        apply andb_true_iff in Hq. destruct Hq as [Hq1 Hq2].
        cbn [lw0_die qpoly_add]. apply andb_true_iff. split.
        -- exact (IH (Datatypes.S M') q' Hp1 Hq1).
        -- exact (IH M' q' Hp2 Hq2).
Qed.
(* The sharp multiplication budget of [die]: the expenditure of
   [S a * S b] is exactly [S (a+b)]. *)
Lemma lw0_die_mul_sharp : forall (f g : qpoly) (a b : nat),
  lw0_die f (Datatypes.S a) = true -> lw0_die g (Datatypes.S b) = true ->
  lw0_die (qpoly_mul f g) (Datatypes.S (a + b)) = true.
Proof.
  intros f g. induction f as [|f0 f IH]; intros a b Hf Hg.
  - reflexivity.
  - destruct a as [|a'].
    + destruct f as [|x f'].
      * replace (Datatypes.S (Datatypes.O + b))%nat
          with (Datatypes.S b)%nat by (rewrite Nat.add_0_l; reflexivity).
        apply (lw0_die_add (Datatypes.S b) (qpoly_scalar f0 g) (cons 0%Q nil)).
        -- rewrite lw0_die_scalar. exact Hg.
        -- reflexivity.
      * cbn [lw0_die] in Hf. apply andb_true_iff in Hf.
        destruct Hf as [Hf1 Hf2]. discriminate Hf2.
    + cbn [lw0_die] in Hf. apply andb_true_iff in Hf.
      destruct Hf as [Hf1 Hf2].
      replace (Datatypes.S (Datatypes.S a' + b))%nat
        with (Datatypes.S (Datatypes.S (a' + b)))%nat
        by (rewrite Nat.add_succ_l; reflexivity).
      apply (lw0_die_add (Datatypes.S (Datatypes.S (a' + b)))
               (qpoly_scalar f0 g)
               (cons 0%Q (qpoly_mul f g))).
      * rewrite lw0_die_scalar.
        apply (lw0_die_budget_mono _ (Datatypes.S b)
                 (Datatypes.S (Datatypes.S (a' + b))) Hg).
         apply (proj1 (Nat.succ_le_mono b (S (a' + b)))).
         apply Nat.le_le_succ_r.
         rewrite Nat.add_comm.
         apply Nat.le_add_r.
      * cbn [lw0_die]. apply andb_true_iff. split.
        -- apply (lw0_die_budget_mono _ (Datatypes.S (a' + b))
                    (Datatypes.S (Datatypes.S (a' + b)))
                    (IH a' b Hf2 Hg)).
         exact (proj1 (Nat.succ_le_mono (a' + b) (S (a' + b)))
                 (Nat.le_succ_diag_r (a' + b))).
        -- exact (IH a' b Hf2 Hg).
Qed.
(* The die budget of the [pi_mono] list (exactly [S m]). *)
Lemma lw0_pi_mono_die : forall m : nat,
  lw0_die (lw0_pi_mono m) (Datatypes.S m) = true.
Proof.
  induction m as [|m IH].
  - reflexivity.
  - cbn [lw0_pi_mono].
    replace (Datatypes.S (Datatypes.S m))%nat
      with (Datatypes.S (m + 1))%nat by (rewrite Nat.add_1_r; reflexivity).
    apply (lw0_die_mul_sharp (lw0_pi_mono m) (cons 0%Q (cons 1%Q nil)) m 1).
    + exact IH.
    + reflexivity.
Qed.
(* The die budget of the [pi_qminus_pow] list (exactly [S n]). *)
Lemma lw0_pi_qminus_pow_die : forall (q : Q) (n : nat),
  lw0_die (lw0_pi_qminus_pow q n) (Datatypes.S n) = true.
Proof.
  intros q n. induction n as [|n IH].
  - reflexivity.
  - cbn [lw0_pi_qminus_pow].
    replace (Datatypes.S (Datatypes.S n))%nat
      with (Datatypes.S (n + 1))%nat by (rewrite Nat.add_1_r; reflexivity).
    apply (lw0_die_mul_sharp (lw0_pi_qminus_pow q n)
             (cons q (cons (-1)%Q nil)) n 1).
    + exact IH.
    + reflexivity.
Qed.
(* The die budget of the [niven_f] list (within [2 * S n]). *)
Lemma lw0_niven_f_die : forall (q b : Q) (n : nat),
  lw0_die (lw0_niven_f q b n) (2 * Datatypes.S n) = true.
Proof.
  intros q b n. unfold lw0_niven_f.
  rewrite lw0_die_scalar.
  apply (lw0_die_budget_mono _ (Datatypes.S (n + n)) (2 * Datatypes.S n)).
  - apply (lw0_die_mul_sharp (lw0_pi_mono n) (lw0_pi_qminus_pow q n) n n).
    + exact (lw0_pi_mono_die n).
    + exact (lw0_pi_qminus_pow_die q n).
  - rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_1_r.
    assert (H2 : (2 * n)%nat = (n + n)%nat)
      by (rewrite Nat.mul_succ_l, Nat.mul_1_l; reflexivity).
    rewrite H2.
    exact (proj1 (Nat.succ_le_mono (n + n) (S (n + n)))
            (Nat.le_succ_diag_r (n + n))).
Qed.
(* ============================================================ *)
(* Section. Poly-level coefficient equalities and shift algebra (the  *)
(* congruence-combinator family)                                      *)
(* ============================================================ *)

(* The poly-level coefficient equality: pointwise equality (a sound
   invariant under lowest-degree-first lists with trailing zeros). *)
Definition lw0_qpoly_eq (p q : qpoly) : Prop :=
  forall j : nat, lw0_coef j p == lw0_coef j q.
(* Trailing-zero shift: the coefficient list of [t^m * p] (lowest
   degree first). *)
Fixpoint qpoly_shift (n : nat) (p : qpoly) : qpoly :=
  match n with
  | Datatypes.O => p
  | Datatypes.S m => cons 0%Q (qpoly_shift m p)
  end.
(* The [Qmake] successor bridge: [(S n)#1 = (n#1) + 1] (a successor
   chain at the [Z] level). *)
Lemma lw0_qmake_Z_succ : forall n : nat,
  (Z.of_nat (Datatypes.S n) # 1)%Q == ((Z.of_nat n # 1) + 1)%Q.
Proof.
  intro n.
  assert (Hn : Z.of_nat (Datatypes.S n) = (Z.of_nat n + 1)%Z) by (rewrite Nat2Z.inj_succ; symmetry; apply Z.add_1_r).
  unfold Qeq; cbn [Qnum Qden Qplus Qmult];
    rewrite Hn, !Z.mul_1_r, ?Z.mul_1_l; reflexivity.
Qed.
(* The [Qmake] addition bridge: [(n+m)#1 = (n#1) + (m#1)] (the
   distributivity of [Nat2Z] over addition). *)
Lemma lw0_qmake_add : forall n m : nat,
  (Z.of_nat (n + m) # 1)%Q == ((Z.of_nat n # 1) + (Z.of_nat m # 1))%Q.
Proof.
  intros n m.
  assert (Hn : Z.of_nat (n + m) = (Z.of_nat n + Z.of_nat m)%Z)
    by apply Nat2Z.inj_add.
  unfold Qeq; cbn [Qnum Qden Qplus Qmult];
    rewrite Hn, !Z.mul_1_r, ?Z.mul_1_l; reflexivity.
Qed.
(* The [Qmake] normal form of the literal [2]. *)
Lemma lw0_qmake_2 : (Z.of_nat (Datatypes.S (Datatypes.S Datatypes.O)) # 1)%Q
                    == (1 + 1)%Q.
Proof. unfold Qeq; cbn [Qnum Qden Qplus Qmult]; reflexivity. Qed.
(* The [Qmake] normal form of the literal [1]. *)
Lemma lw0_qmake_1 : (Z.of_nat (Datatypes.S Datatypes.O) # 1)%Q == 1%Q.
Proof. unfold Qeq; cbn [Qnum Qden]; reflexivity. Qed.
(* The poly-level equality is reflexive. *)
Lemma lw0_qpoly_eq_refl : forall p : qpoly, lw0_qpoly_eq p p.
Proof. intros p j. apply Qeq_refl. Qed.
(* The poly-level equality is symmetric. *)
Lemma lw0_qpoly_eq_sym : forall p q : qpoly,
  lw0_qpoly_eq p q -> lw0_qpoly_eq q p.
Proof. intros p q H j. apply Qeq_sym. apply H. Qed.
(* The poly-level equality is transitive. *)
Lemma lw0_qpoly_eq_trans : forall p q r : qpoly,
  lw0_qpoly_eq p q -> lw0_qpoly_eq q r -> lw0_qpoly_eq p r.
Proof. intros p q r H1 H2 j. apply Qeq_trans with (lw0_coef j q).
  apply H1. apply H2. Qed.
(* Cons-layer inheritance of pointwise equality. *)
Lemma lw0_cons_congr : forall (a b : Q) (p q : qpoly),
  a == b -> lw0_qpoly_eq p q -> lw0_qpoly_eq (cons a p) (cons b q).
Proof.
  intros a b p q Hab Hp j. destruct j as [|j'].
  - simpl. exact Hab.
  - simpl. exact (Hp j').
Qed.
(* Addition respects the poly-level equality. *)
Lemma lw0_qpoly_eq_add : forall p1 q1 p2 q2 : qpoly,
  lw0_qpoly_eq p1 q1 -> lw0_qpoly_eq p2 q2 ->
  lw0_qpoly_eq (qpoly_add p1 p2) (qpoly_add q1 q2).
Proof.
  intros p1 q1 p2 q2 H1 H2 j.
  rewrite lw0_coef_add, lw0_coef_add.
  apply Qeq_trans with (lw0_coef j q1 + lw0_coef j p2)%Q.
  - rewrite (H1 j). ring.
  - rewrite (H2 j). ring.
Qed.
(* Associativity of addition (identity at the coefficient level). *)
Lemma lw0_qpoly_add_assoc : forall p q r : qpoly,
  lw0_qpoly_eq (qpoly_add (qpoly_add p q) r) (qpoly_add p (qpoly_add q r)).
Proof.
  intros p q r k. repeat rewrite lw0_coef_add. ring.
Qed.
(* The derivative respects the poly-level equality. *)
Lemma lw0_qpoly_eq_deriv : forall p q : qpoly,
  lw0_qpoly_eq p q -> lw0_qpoly_eq (qpoly_deriv p) (qpoly_deriv q).
Proof.
  intros p q H j.
  rewrite lw0_coef_deriv, (H (Datatypes.S j)), lw0_coef_deriv. reflexivity.
Qed.
(* Coefficient recovery after shifting: [coef (n+r) (shift n p) =
   coef r p]. *)
Lemma lw0_coef_shift : forall (n r : nat) (p : qpoly),
  lw0_coef (n + r)%nat (qpoly_shift n p) == lw0_coef r p.
Proof.
  induction n as [|n IH]; intros r p.
  - simpl. reflexivity.
  - replace (Datatypes.S n + r)%nat with (Datatypes.S (n + r))%nat
    by (rewrite Nat.add_succ_l; reflexivity).
    simpl. exact (IH r p).
Qed.
(* The one-position shift instance. *)
Lemma lw0_coef_shift_1 : forall (r : nat) (p : qpoly),
  lw0_coef (Datatypes.S r) (qpoly_shift 1 p) == lw0_coef r p.
Proof. intros r p. exact (lw0_coef_shift 1 r p). Qed.
(* The two-position shift instance. *)
Lemma lw0_coef_shift_2 : forall (r : nat) (p : qpoly),
  lw0_coef (Datatypes.S (Datatypes.S r)) (qpoly_shift 2 p) == lw0_coef r p.
Proof. intros r p. exact (lw0_coef_shift 2 r p). Qed.
(* Coefficients beyond the shift range vanish. *)
Lemma lw0_coef_shift_lt : forall (m k : nat) (p : qpoly),
  (k < m)%nat -> lw0_coef k (qpoly_shift m p) == 0%Q.
Proof.
  induction m as [|m IH]; intros k p Hk.
  - exfalso. exact (Nat.nle_succ_0 k Hk).
  - destruct k as [|k'].
    + reflexivity.
    + simpl. apply IH. exact (proj2 (Nat.succ_lt_mono k' m) Hk).
Qed.
(* The shift-by-derivative coefficient bridge:
   [coef k (shift 1 (deriv w)) = k * coef k w]. *)
Lemma lw0_shift1_deriv_coef : forall (k : nat) (w : qpoly),
  lw0_coef k (qpoly_shift 1 (qpoly_deriv w)) == (Z.of_nat k # 1)%Q * lw0_coef k w.
Proof.
  intros k w. destruct k as [|k'].
  - rewrite (lw0_coef_shift_lt 1 0 (qpoly_deriv w)) by (apply (Nat.lt_0_succ 0)).
    change (Z.of_nat Datatypes.O # 1)%Q with 0%Q.
    symmetry. apply Qmult_0_l.
  - rewrite lw0_coef_shift_1, lw0_coef_deriv. reflexivity.
Qed.
(* Shift distributes over addition (at the coefficient level). *)
Lemma lw0_shift_add : forall (m : nat) (p q : qpoly),
  lw0_qpoly_eq (qpoly_shift m (qpoly_add p q))
               (qpoly_add (qpoly_shift m p) (qpoly_shift m q)).
Proof.
  induction m as [|m IH]; intros p q k.
  - reflexivity.
  - destruct k as [|k'].
    + cbn [lw0_coef qpoly_shift qpoly_add]. ring.
    + cbn [lw0_coef qpoly_shift qpoly_add]. exact (IH p q k').
Qed.
(* Shift composition: [shift (m+n)] is [shift m] composed with
   [shift n]. *)
Lemma lw0_shift_shift : forall (m n : nat) (p : qpoly),
  lw0_qpoly_eq (qpoly_shift (m + n) p) (qpoly_shift m (qpoly_shift n p)).
Proof.
  induction m as [|m IH]; intros n p k.
  - reflexivity.
  - replace (Datatypes.S m + n)%nat with (Datatypes.S (m + n))%nat
    by (rewrite Nat.add_succ_l; reflexivity).
    destruct k as [|k'].
    + reflexivity.
    + cbn [lw0_coef qpoly_shift]. exact (IH n p k').
Qed.
(* Shift respects the poly-level equality (the two-way split of
   in-range recovery and out-of-range vanishing). *)
Lemma lw0_shift_congr : forall (m : nat) (p q : qpoly),
  lw0_qpoly_eq p q -> lw0_qpoly_eq (qpoly_shift m p) (qpoly_shift m q).
Proof.
  intros m p q H k.
  destruct (Nat.le_gt_cases m k) as [Hle | Hgt].
  - assert (Hr : k = (m + (k - m))%nat)
      by (rewrite Nat.add_comm; symmetry; apply Nat.sub_add; exact Hle).
    rewrite Hr.
    rewrite (lw0_coef_shift m (k - m) p).
    rewrite (lw0_coef_shift m (k - m) q).
    apply H.
  - rewrite (lw0_coef_shift_lt m k p Hgt).
    rewrite (lw0_coef_shift_lt m k q Hgt). ring.
Qed.
(* A double cons list equals a double constant list plus a
   two-shifted tail (at the coefficient level). *)
Lemma lw0_cons2_shift2 : forall (a b : Q) (w : qpoly),
  lw0_qpoly_eq (cons a (cons b w))
               (qpoly_add (cons a (cons b nil)) (qpoly_shift 2 w)).
Proof.
  intros a b w k. rewrite lw0_coef_add. destruct k as [|k'].
  - cbn [lw0_coef]. rewrite (lw0_coef_shift_lt 2 0 w) by (apply (Nat.lt_0_succ 1)). ring.
  - destruct k' as [|k''].
    + cbn [lw0_coef]. rewrite (lw0_coef_shift_lt 2 1 w) by (apply (proj1 (Nat.succ_lt_mono 0 1)); apply (Nat.lt_0_succ 0)). ring.
    + rewrite lw0_coef_shift_2.
      cbn [lw0_coef].
      ring.
Qed.
(* The scalarized double cons list equals a scalar double constant
   list plus a two-shifted scalar tail. *)
Lemma lw0_scal_pair_shift : forall (c x y : Q) (w : qpoly),
  lw0_qpoly_eq (qpoly_scalar c (cons x (cons y w)))
               (qpoly_add (qpoly_scalar c (cons x (cons y nil)))
                          (qpoly_shift 2 (qpoly_scalar c w))).
Proof.
  intros c x y w k. cbn [qpoly_scalar].
  rewrite lw0_coef_add. destruct k as [|k'].
  - rewrite (lw0_coef_shift_lt 2 0 (qpoly_scalar c w)) by (apply (Nat.lt_0_succ 1)).
    cbn [lw0_coef].
    ring.
  - destruct k' as [|k''].
    + rewrite (lw0_coef_shift_lt 2 1 (qpoly_scalar c w)) by (apply (proj1 (Nat.succ_lt_mono 0 1)); apply (Nat.lt_0_succ 0)).
      cbn [lw0_coef].
      ring.
    + rewrite lw0_coef_shift_2.
      cbn [lw0_coef].
      ring.
Qed.
(* The scalarized sin list equals a fully scalarized list plus the
   tail shifted by [(2j+2)] -- a coefficient-level decomposition built
   term by term with the congruence combinators, with zero forall-form
   rewriting: under [lw0_coef]/[qpoly_shift] there is no morphism
   instance, and a forall-form lemma matches only at the root of the
   term. *)
Lemma lw0_sin_aux_scal_append : forall (j : nat) (c : Q) (w : qpoly),
  lw0_qpoly_eq (qpoly_scalar c (lw0_sin_aux j w))
               (qpoly_add (qpoly_scalar c (lw0_sin_aux j nil))
                          (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                       (qpoly_scalar c w))).
Proof.
  induction j as [|j IH]; intros c w k.
  - cbn [lw0_sin_aux qpoly_scalar].
    rewrite lw0_coef_add. destruct k as [|k'].
    + rewrite (lw0_coef_shift_lt (Datatypes.S (Datatypes.S (0 + 0))) Datatypes.O (qpoly_scalar c w)) by (apply (Nat.lt_0_succ 1)).
      cbn [lw0_coef].
      ring.
    + destruct k' as [|k''].
      * rewrite (lw0_coef_shift_lt (Datatypes.S (Datatypes.S (0 + 0))) (Datatypes.S Datatypes.O) (qpoly_scalar c w)) by (apply (proj1 (Nat.succ_lt_mono 0 1)); apply (Nat.lt_0_succ 0)).
        cbn [lw0_coef].
        ring.
      * rewrite lw0_coef_shift_2.
        cbn [lw0_coef].
        ring.
  - cbn [lw0_sin_aux].
    set (cig := (q_pow (-1) (Datatypes.S j)
                 / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q).
    rewrite (IH c (cons 0%Q (cons cig w)) k).
    rewrite (lw0_coef_add k (qpoly_scalar c (lw0_sin_aux j nil))
               (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                            (qpoly_scalar c (cons 0%Q (cons cig w))))).
    rewrite (lw0_coef_add k (qpoly_scalar c (lw0_sin_aux j (cons 0%Q (cons cig nil))))
               (qpoly_shift (Datatypes.S (Datatypes.S (Datatypes.S j + Datatypes.S j)))
                            (qpoly_scalar c w))).
    rewrite (IH c (cons 0%Q (cons cig nil)) k).
    rewrite (lw0_coef_add k (qpoly_scalar c (lw0_sin_aux j nil))
               (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                            (qpoly_scalar c (cons 0%Q (cons cig nil))))).
    
    pose proof (lw0_shift_congr (Datatypes.S (Datatypes.S (j + j)))
                  (qpoly_scalar c (cons 0%Q (cons cig w)))
                  (qpoly_add (qpoly_scalar c (cons 0%Q (cons cig nil)))
                             (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                                          (qpoly_scalar c w)))
                  (lw0_scal_pair_shift c 0%Q cig w)) as Hid1.
    pose proof (lw0_shift_add (Datatypes.S (Datatypes.S (j + j)))
                  (qpoly_scalar c (cons 0%Q (cons cig nil)))
                  (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                               (qpoly_scalar c w))) as Hid2.
    pose proof (lw0_shift_shift (Datatypes.S (Datatypes.S (j + j)))
                  (Datatypes.S (Datatypes.S Datatypes.O)) (qpoly_scalar c w)) as Hid3.
    pose proof (lw0_qpoly_eq_sym _ _ Hid3) as Hid3s.
    pose proof (lw0_qpoly_eq_trans _ _ _ Hid1 Hid2) as Hid12.
    pose proof (lw0_qpoly_eq_add _ _ _ _
                  (lw0_qpoly_eq_refl (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                      (qpoly_scalar c (cons 0%Q (cons cig nil)))))
                  Hid3s) as HidF.
    pose proof (lw0_qpoly_eq_trans _ _ _ Hid12 HidF) as Hid.
    specialize (Hid k).
    rewrite Hid.
    rewrite (lw0_coef_add k (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                            (qpoly_scalar c (cons 0%Q (cons cig nil))))
               (qpoly_shift (Datatypes.S (Datatypes.S (j + j)) + Datatypes.S (Datatypes.S Datatypes.O))
                            (qpoly_scalar c w))).
    replace (Datatypes.S (Datatypes.S (j + j)) + 2)%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S j + Datatypes.S j)))%nat
      by (replace (Datatypes.S j + Datatypes.S j)%nat
            with (Datatypes.S (Datatypes.S (j + j)))%nat
            by (rewrite Nat.add_succ_l, Nat.add_succ_r; reflexivity);
          rewrite Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r;
          reflexivity).
    ring.
Qed.
(* The cos accumulator respects the poly-level equality. *)
Lemma lw0_cos_aux_congr : forall (j : nat) (w1 w2 : qpoly),
  lw0_qpoly_eq w1 w2 -> lw0_qpoly_eq (lw0_cos_aux j w1) (lw0_cos_aux j w2).
Proof.
  induction j as [|j IH]; intros w1 w2 H k.
  - destruct k as [|k'].
    + reflexivity.
    + simpl. exact (H k').
  - cbn [lw0_cos_aux].
    apply IH. intro k0. destruct k0 as [|k0].
    + reflexivity.
    + destruct k0 as [|k0'].
      * reflexivity.
      * simpl. exact (H k0').
Qed.
(* The sin accumulator respects the poly-level equality. *)
Lemma lw0_sin_aux_congr : forall (j : nat) (w1 w2 : qpoly),
  lw0_qpoly_eq w1 w2 -> lw0_qpoly_eq (lw0_sin_aux j w1) (lw0_sin_aux j w2).
Proof.
  induction j as [|j IH]; intros w1 w2 H k.
  - destruct k as [|k'].
    + reflexivity.
    + destruct k' as [|k''].
      * reflexivity.
      * simpl. exact (H k'').
  - cbn [lw0_sin_aux].
    apply IH. intro k0. destruct k0 as [|k0].
    + reflexivity.
    + destruct k0 as [|k0'].
      * reflexivity.
      * simpl. exact (H k0').
Qed.
(* ============================================================ *)
(* Section. The [W]/[X] transforms and the poly-level derivative main *)
(* lemma (the no-evaluation-lift route)                                *)
(* ============================================================ *)

(* The [W] transform: the shifted composition of [(2j+2)*acc + acc']
   (carried as the recursive prefix of the [sigma] list on the pair
   [(0, sigma_j)]). *)
Definition lw0_Wp (j : nat) (acc : qpoly) : qpoly :=
  qpoly_add (qpoly_scalar (Z.of_nat (Datatypes.S (Datatypes.S (j + j))) # 1)%Q acc)
            (qpoly_shift 1 (qpoly_deriv acc)).
(* The [X] transform: the shifted composition of [(2j+3)*acc + acc']
   (the gamma-side counterpart). *)
Definition lw0_Xc (j : nat) (acc : qpoly) : qpoly :=
  qpoly_add (qpoly_scalar
               (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))) # 1)%Q
               acc)
            (qpoly_shift 1 (qpoly_deriv acc)).
(* The [W] transform of the empty list is the empty list. *)
Lemma lw0_Wp_nil : forall j : nat, lw0_qpoly_eq (lw0_Wp j nil) nil.
Proof.
  intros j k. unfold lw0_Wp.
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct k; simpl; ring.
Qed.
(* The [X] transform of the empty list is the empty list. *)
Lemma lw0_Xc_nil : forall j : nat, lw0_qpoly_eq (lw0_Xc j nil) nil.
Proof.
  intros j k. unfold lw0_Xc.
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct k; simpl; ring.
Qed.
(* The cons-layer step of the [W] transform: [(0, c::acc)] maps to
   [(0, (2j+3)c :: W_{S j} acc)]. *)
Lemma lw0_Wp_push : forall (j : nat) (c : Q) (acc : qpoly),
  lw0_qpoly_eq (lw0_Wp j (cons 0%Q (cons c acc)))
               (cons 0%Q
                  (cons ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))) # 1)%Q * c)%Q
                        (lw0_Wp (Datatypes.S j) acc))).
Proof.
  intros j c acc k.
  unfold lw0_Wp.
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct k as [|k'].
  - rewrite (lw0_coef_shift_lt 1 0 (qpoly_deriv (cons 0%Q (cons c acc)))) by (apply (Nat.lt_0_succ 0)).
    cbn [lw0_coef].
    ring.
  - destruct k' as [|k''].
    + rewrite lw0_coef_shift_1, lw0_coef_deriv.
      cbn [lw0_coef].
      rewrite (lw0_qmake_Z_succ (Datatypes.S (Datatypes.S (j + j)))), lw0_qmake_1. ring.
    + rewrite lw0_coef_shift_1, lw0_coef_deriv.
      cbn [lw0_coef].
      unfold lw0_Wp.
      rewrite lw0_coef_add, lw0_coef_scalar, lw0_shift1_deriv_coef.
      cbn [lw0_coef].
      replace (Datatypes.S (Datatypes.S k''))%nat with (k'' + 2)%nat
        by (rewrite Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r; reflexivity).
      replace (Datatypes.S j + Datatypes.S j)%nat
        with (Datatypes.S (Datatypes.S (j + j)))%nat
        by (rewrite Nat.add_succ_l, Nat.add_succ_r; reflexivity).
      replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))))%nat
        with ((Datatypes.S (Datatypes.S (j + j))) + 2)%nat
        by (rewrite Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r; reflexivity).
      rewrite (lw0_qmake_add k'' (Datatypes.S (Datatypes.S Datatypes.O))).
      rewrite (lw0_qmake_add (Datatypes.S (Datatypes.S (j + j)))
                (Datatypes.S (Datatypes.S Datatypes.O))).
      rewrite lw0_qmake_2.
      ring.
Qed.
(* The cons-layer step of the [X] transform: [(0, c::acc)] maps to
   [(0, (2j+4)c :: X_{S j} acc)]. *)
Lemma lw0_Xc_push : forall (j : nat) (c : Q) (acc : qpoly),
  lw0_qpoly_eq (lw0_Xc j (cons 0%Q (cons c acc)))
               (cons 0%Q
                  (cons ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))) # 1)%Q * c)%Q
                        (lw0_Xc (Datatypes.S j) acc))).
Proof.
  intros j c acc k.
  unfold lw0_Xc.
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct k as [|k'].
  - rewrite (lw0_coef_shift_lt 1 0 (qpoly_deriv (cons 0%Q (cons c acc)))) by (apply (Nat.lt_0_succ 0)).
    cbn [lw0_coef].
    ring.
  - destruct k' as [|k''].
    + rewrite lw0_coef_shift_1, lw0_coef_deriv.
      cbn [lw0_coef].
      replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))))%nat
        with ((Datatypes.S (Datatypes.S (Datatypes.S (j + j))))
                + Datatypes.S Datatypes.O)%nat
        by (rewrite Nat.add_1_r; reflexivity).
      rewrite lw0_qmake_add, lw0_qmake_1. ring.
    + rewrite lw0_coef_shift_1, lw0_coef_deriv.
      cbn [lw0_coef].
      unfold lw0_Xc.
      rewrite lw0_coef_add, lw0_coef_scalar, lw0_shift1_deriv_coef.
      cbn [lw0_coef].
      replace (Datatypes.S (Datatypes.S k''))%nat with (k'' + 2)%nat
        by (rewrite Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r; reflexivity).
      replace (Datatypes.S j + Datatypes.S j)%nat
        with (Datatypes.S (Datatypes.S (j + j)))%nat
        by (rewrite Nat.add_succ_l, Nat.add_succ_r; reflexivity).
      replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))))%nat
        with ((Datatypes.S (Datatypes.S (Datatypes.S (j + j)))) + 2)%nat
        by (rewrite Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r; reflexivity).
      rewrite (lw0_qmake_add k'' (Datatypes.S (Datatypes.S Datatypes.O))).
      rewrite (lw0_qmake_add (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))
                (Datatypes.S (Datatypes.S Datatypes.O))).
      rewrite lw0_qmake_2.
      ring.
Qed.
(* The sin segment-head coefficient conversion key:
   [(2j+3) * eps_j = eps'_j] (the [q_fact_succ] chain plus the
   cancellation helper). *)
Lemma lw0_sin_qmake_key : forall j : nat,
  ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))) # 1)%Q
    * ((q_pow (-1) (Datatypes.S j)
        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)
  == ((q_pow (-1) (Datatypes.S j)
       / q_fact (Datatypes.S (Datatypes.S (2 * j)))))%Q.
Proof.
  intros j.
  transitivity ((((Z.of_nat (Datatypes.S (Datatypes.S (j + j)))) # 1)%Q + 1)
    * ((q_pow (-1) (Datatypes.S j)
        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)).
  - rewrite (lw0_qmake_Z_succ (Datatypes.S (Datatypes.S (j + j)))). ring.
  - replace (Datatypes.S (Datatypes.S (j + j)))%nat
      with (Datatypes.S (Datatypes.S (2 * j)))%nat
      by (assert (H2 : (2 * j)%nat = (j + j)%nat)
            by (rewrite Nat.mul_succ_l, Nat.mul_1_l; reflexivity);
          rewrite H2; reflexivity).
    assert (Hpos : (0 < Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Z) by (change 0%Z with (Z.of_nat 0);
            apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))); apply Nat.lt_0_succ).
    assert (Hn3 : Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                = (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) + 1)%Z) by (rewrite Nat2Z.inj_succ; symmetry; apply Z.add_1_r).
    assert (Hz3 : ((Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)%Q + 1)
                == (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))) # 1)) by (unfold Qeq; cbn [Qnum Qden Qplus Qmult];
      rewrite Hn3, !Z.mul_1_r, ?Z.mul_1_l; reflexivity).
    rewrite Hz3.
    rewrite (q_fact_succ (Datatypes.S (Datatypes.S (2 * j)))).
    rewrite (lw0_q_div_int_mul_gen
               (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
               (q_pow (-1) (Datatypes.S j))
               (q_fact (Datatypes.S (Datatypes.S (2 * j)))) Hpos).
    reflexivity.
Qed.
(* The cos segment-head coefficient conversion key:
   [(2j+4) * gamma_{S j} = -eps_{S j}]. *)
Lemma lw0_cos_qmake_key : forall j : nat,
  ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))))) # 1)%Q
    * ((q_pow (-1) (Datatypes.S (Datatypes.S j))
        / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q)
  == (-1)%Q * ((q_pow (-1) (Datatypes.S j)
                / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q).
Proof.
  intros j.
  assert (Hpos : (0 < Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))%Z) by (change 0%Z with (Z.of_nat 0);
            apply (proj1 (Nat2Z.inj_lt 0 (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))); apply Nat.lt_0_succ).
  replace (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))))%nat
    with (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%nat
    by (assert (H2 : (2 * j)%nat = (j + j)%nat)
          by (rewrite Nat.mul_succ_l, Nat.mul_1_l; reflexivity);
        rewrite H2; reflexivity).
  replace (Datatypes.S (Datatypes.S (2 * Datatypes.S j)))%nat
    with (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%nat
    by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r;
        reflexivity).
  change (q_pow (-1) (Datatypes.S (Datatypes.S j)))
    with ((-1)%Q * q_pow (-1) (Datatypes.S j))%Q.
  rewrite (q_fact_succ (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))).
  rewrite (lw0_q_div_int_mul_gen
             (Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
             ((-1)%Q * q_pow (-1) (Datatypes.S j))%Q
             (q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))) Hpos).
  unfold Qdiv. ring.
Qed.
(* The derivative of the sigma list equals [cos_aux (W j acc)] (the
   poly-level main lemma, no-evaluation-lift route). *)
Lemma lw0_sin_aux_deriv_poly_gen : forall (j : nat) (acc : qpoly),
  lw0_qpoly_eq (qpoly_deriv (lw0_sin_aux j acc)) (lw0_cos_aux j (lw0_Wp j acc)).
Proof.
  induction j as [|j IH]; intros acc.
  - intro k.
    change (lw0_sin_aux Datatypes.O acc)
      with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q acc)).
    change (lw0_cos_aux Datatypes.O (lw0_Wp Datatypes.O acc))
      with (cons (q_pow (-1) 0 / q_fact 0)%Q (lw0_Wp Datatypes.O acc)).
    rewrite lw0_coef_deriv.
    destruct k as [|k'].
    + change (Z.of_nat (Datatypes.S Datatypes.O)) with 1%Z.
      cbn [lw0_coef].
      change (q_pow (-1) 0 / q_fact 1) with 1%Q.
      change (q_pow (-1) 0 / q_fact 0) with 1%Q.
      ring.
    + cbn [lw0_coef].
      unfold lw0_Wp.
      rewrite lw0_coef_add, lw0_coef_scalar, lw0_shift1_deriv_coef.
      replace (Datatypes.S (Datatypes.S k'))%nat
        with (Datatypes.S (Datatypes.S (0 + 0)) + k')%nat
        by (rewrite !Nat.add_succ_l; simpl; reflexivity).
      rewrite lw0_qmake_add.
      ring.
  - change (lw0_sin_aux (Datatypes.S j) acc)
      with (lw0_sin_aux j (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                 acc))).
    change (lw0_cos_aux (Datatypes.S j) (lw0_Wp (Datatypes.S j) acc))
      with (lw0_cos_aux j (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (2 * j))))%Q
                 (lw0_Wp (Datatypes.S j) acc)))).
    apply (lw0_qpoly_eq_trans _ (lw0_cos_aux j (lw0_Wp j (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                 acc))))).
    + exact (IH (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                 acc))).
    + apply lw0_cos_aux_congr.
      apply (lw0_qpoly_eq_trans _ (cons 0%Q
              (cons ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (j + j)))) # 1)%Q
                      * (q_pow (-1) (Datatypes.S j)
                         / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                 (lw0_Wp (Datatypes.S j) acc)))).
      * exact (lw0_Wp_push j (q_pow (-1) (Datatypes.S j)
                           / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q acc).
      * apply lw0_cons_congr.
        -- ring.
        -- apply lw0_cons_congr.
           ++ exact (lw0_sin_qmake_key j).
           ++ apply lw0_qpoly_eq_refl.
Qed.
(* The derivative of the gamma list at the [S] layer equals
   [-sigma_j nil + shift (X j acc)] (the poly-level main lemma). *)
Lemma lw0_cos_aux_deriv_S_poly_gen : forall (j : nat) (acc : qpoly),
  lw0_qpoly_eq (qpoly_deriv (lw0_cos_aux (Datatypes.S j) acc))
               (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil))
                          (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                       (lw0_Xc j acc))).
Proof.
  induction j as [|j IH]; intros acc.
  - intro k.
    change (lw0_cos_aux (Datatypes.S Datatypes.O) acc)
      with (cons (q_pow (-1) 0 / q_fact 0)%Q
              (cons 0%Q
                 (cons (q_pow (-1) (Datatypes.S Datatypes.O)
                         / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.O))))%Q
                    acc))).
    change (lw0_sin_aux Datatypes.O nil)
      with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q nil)).
    rewrite lw0_coef_deriv.
    rewrite lw0_coef_add.
    destruct k as [|k'].
    + rewrite (lw0_coef_shift_lt (Datatypes.S (Datatypes.S (Datatypes.O + Datatypes.O))) Datatypes.O (lw0_Xc Datatypes.O acc)) by (apply (Nat.lt_0_succ 1)).
      rewrite lw0_coef_scalar.
      cbn [lw0_coef].
      change (Z.of_nat (Datatypes.S Datatypes.O)) with 1%Z.
      ring.
    + destruct k' as [|k''].
      * rewrite (lw0_coef_shift_lt (Datatypes.S (Datatypes.S (Datatypes.O + Datatypes.O))) (Datatypes.S Datatypes.O) (lw0_Xc Datatypes.O acc)) by (apply (proj1 (Nat.succ_lt_mono 0 1)); apply (Nat.lt_0_succ 0)).
        rewrite lw0_coef_scalar.
        cbn [lw0_coef].
        change (q_pow (-1) 0 / q_fact 1) with 1%Q.
        change (q_pow (-1) (Datatypes.S Datatypes.O)
                  / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.O))))
          with ((-1) # 2)%Q.
        change (Z.of_nat (Datatypes.S (Datatypes.S Datatypes.O)) # 1) with (1 + 1)%Q.
        ring.
      * rewrite lw0_coef_shift_2.
        unfold lw0_Xc.
        rewrite lw0_coef_add, !lw0_coef_scalar, lw0_shift1_deriv_coef.
        cbn [lw0_coef].
        replace (Datatypes.S (Datatypes.S (Datatypes.S k'')))%nat
          with (Datatypes.S (Datatypes.S (Datatypes.S (0 + 0))) + k'')%nat
          by (rewrite !Nat.add_succ_l; simpl; reflexivity).
        rewrite lw0_qmake_add.
        ring.
  - change (lw0_cos_aux (Datatypes.S (Datatypes.S j)) acc)
      with (lw0_cos_aux (Datatypes.S j) (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S (Datatypes.S j))
                      / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q
                 acc))).
    change (lw0_sin_aux (Datatypes.S j) nil)
      with (lw0_sin_aux j (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S j)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                 nil))).
    replace (Datatypes.S (Datatypes.S (Datatypes.S j + Datatypes.S j)))%nat
      with (Datatypes.S (Datatypes.S (j + j)) + 2)%nat
      by (symmetry;
          replace (Datatypes.S j + Datatypes.S j)%nat
            with (Datatypes.S (Datatypes.S (j + j)))%nat
            by (rewrite Nat.add_succ_l, Nat.add_succ_r; reflexivity);
          rewrite Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r;
          reflexivity).
    apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil)) (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (lw0_Xc j (cons 0%Q (cons (q_pow (-1) (Datatypes.S (Datatypes.S j)) / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q acc)))))).
    + exact (IH (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S (Datatypes.S j))
                      / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q
                 acc))).
    + apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil)) (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (cons 0%Q (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q (lw0_Xc (Datatypes.S j) acc)))))).
      * apply lw0_qpoly_eq_add.
        -- apply lw0_qpoly_eq_refl.
        -- apply lw0_shift_congr.
           apply (lw0_qpoly_eq_trans _ (cons 0%Q
                    (cons ((Z.of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (j + j))))) # 1)%Q
                            * (q_pow (-1) (Datatypes.S (Datatypes.S j))
                               / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q)%Q
                       (lw0_Xc (Datatypes.S j) acc)))).
           ++ exact (lw0_Xc_push j (q_pow (-1) (Datatypes.S (Datatypes.S j))
                                / q_fact (Datatypes.S (Datatypes.S (2 * Datatypes.S j))))%Q acc).
           ++ apply lw0_cons_congr.
              ** ring.
              ** apply lw0_cons_congr.
                 --- exact (lw0_cos_qmake_key j).
                 --- apply lw0_qpoly_eq_refl.
      * apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil)) (qpoly_add (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (cons 0%Q (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q nil))) (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O)) (lw0_Xc (Datatypes.S j) acc)))))).
        -- apply lw0_qpoly_eq_add.
           ++ apply lw0_qpoly_eq_refl.
           ++ apply (lw0_qpoly_eq_trans _ (qpoly_shift (Datatypes.S (Datatypes.S (j + j))) (qpoly_add (cons 0%Q (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q nil)) (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O)) (lw0_Xc (Datatypes.S j) acc))))).
           --- apply lw0_shift_congr.
               exact (lw0_cons2_shift2 0%Q
                        ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                        (lw0_Xc (Datatypes.S j) acc)).
           --- exact (lw0_shift_add (Datatypes.S (Datatypes.S (j + j)))
                       (cons 0%Q
                          (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j) / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                             nil))
                       (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                                    (lw0_Xc (Datatypes.S j) acc))).
        -- apply (lw0_qpoly_eq_trans _
                    (qpoly_add (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil))
                               (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                            (cons ((-1)%Q * 0%Q)%Q
                                               (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j)
                                                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                                                  nil))))
                              (qpoly_shift (Datatypes.S (Datatypes.S (j + j)) + 2)
                                           (lw0_Xc (Datatypes.S j) acc)))).
           ++ apply (lw0_qpoly_eq_trans _
                       (qpoly_add (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux j nil))
                                  (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                               (cons 0%Q
                                                  (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j)
                                                             / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                                                     nil))))
                                 (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                              (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                                                           (lw0_Xc (Datatypes.S j) acc))))).
              ** exact (lw0_qpoly_eq_sym _ _
                          (lw0_qpoly_add_assoc (qpoly_scalar (-1)%Q (lw0_sin_aux j nil))
                             (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                          (cons 0%Q
                                             (cons ((-1)%Q * (q_pow (-1) (Datatypes.S j)
                                                        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q)%Q
                                               nil)))
                             (qpoly_shift (Datatypes.S (Datatypes.S (j + j)))
                                          (qpoly_shift (Datatypes.S (Datatypes.S Datatypes.O))
                                                       (lw0_Xc (Datatypes.S j) acc))))).
              ** apply lw0_qpoly_eq_add.
                 --- apply lw0_qpoly_eq_add.
                     +++ apply lw0_qpoly_eq_refl.
                     +++ apply lw0_shift_congr. apply lw0_cons_congr.
                         ---- ring.
                         ---- apply lw0_qpoly_eq_refl.
                 --- exact (lw0_qpoly_eq_sym _ _
                              (lw0_shift_shift (Datatypes.S (Datatypes.S (j + j)))
                                 (Datatypes.S (Datatypes.S Datatypes.O))
                                 (lw0_Xc (Datatypes.S j) acc))).
           ++ apply lw0_qpoly_eq_add.
              ** exact (lw0_qpoly_eq_sym _ _
                          (lw0_sin_aux_scal_append j (-1)%Q
                             (cons 0%Q
                                (cons (q_pow (-1) (Datatypes.S j)
                                        / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                                   nil)))).
              ** apply lw0_qpoly_eq_refl.
Qed.
(* The derivative of the sin surrogate equals the cos surrogate (a
   poly-level identity). *)
Lemma lw0_sin_qp_deriv_poly : forall N : nat,
  lw0_qpoly_eq (qpoly_deriv (lw0_sin_qp N)) (lw0_cos_qp N).
Proof.
  intro N. unfold lw0_sin_qp, lw0_cos_qp.
  apply (lw0_qpoly_eq_trans _ (lw0_cos_aux N (lw0_Wp N nil))).
  - apply lw0_sin_aux_deriv_poly_gen.
  - apply (lw0_qpoly_eq_trans _ (lw0_cos_aux N nil)).
    + apply lw0_cos_aux_congr. apply lw0_Wp_nil.
    + apply lw0_qpoly_eq_refl.
Qed.
(* The derivative of the cos surrogate at the [S] layer equals the
   negated sin surrogate (a poly-level identity). *)
Lemma lw0_cos_qp_deriv_poly : forall N : nat,
  lw0_qpoly_eq (qpoly_deriv (lw0_cos_qp (Datatypes.S N)))
               (qpoly_scalar (-1)%Q (lw0_sin_qp N)).
Proof.
  intro N. unfold lw0_cos_qp, lw0_sin_qp.
  apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux N nil))
            (qpoly_shift (Datatypes.S (Datatypes.S (N + N))) (lw0_Xc N nil)))).
  - apply lw0_cos_aux_deriv_S_poly_gen.
  - apply (lw0_qpoly_eq_trans _ (qpoly_add (qpoly_scalar (-1)%Q (lw0_sin_aux N nil)) (qpoly_shift (Datatypes.S (Datatypes.S (N + N))) (qpoly_scalar (-1)%Q nil)))).
    + apply lw0_qpoly_eq_add.
      * apply lw0_qpoly_eq_refl.
      * apply lw0_shift_congr. exact (lw0_Xc_nil N).
    + exact (lw0_qpoly_eq_sym _ _ (lw0_sin_aux_scal_append N (-1)%Q nil)).
Qed.
(* The second derivative of the sin surrogate equals the negated sin
   surrogate (one of the three sigma-'' identity pieces). *)
Lemma lw0_sin_qp_deriv2 : forall m : nat,
  lw0_qpoly_eq (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S m)))
               (qpoly_scalar (-1)%Q (lw0_sin_qp m)).
Proof.
  intro m.
  change (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S m)))
    with (qpoly_deriv (qpoly_deriv (lw0_sin_qp (Datatypes.S m)))).
  apply (lw0_qpoly_eq_trans _ (qpoly_deriv (lw0_cos_qp (Datatypes.S m)))).
  - apply lw0_qpoly_eq_deriv. apply lw0_sin_qp_deriv_poly.
  - apply lw0_cos_qp_deriv_poly.
Qed.
(* The zero-shift list construction of the pitB conv block (the
   structural base of the [lw385] [ai_zero_shift]/[delta_odd] family). *)
Fixpoint lw0_pitB_conv_zero_shift (m : nat) (p : QPoly) : QPoly :=
  match m with
  | Datatypes.O => p
  | Datatypes.S m' => cons 0%Q (lw0_pitB_conv_zero_shift m' p)
  end.
(* ---- The Set-level [Q] equality decision (the three pieces
   migrated directly from [S02]) ---- *)

(* Set-level [Q] equality: the [Qcompare] three-way singleton decision
   leaf (an extraction-friendly form) *)
Definition QeqT (a b : Q) : Set :=
  Id (match Qcompare a b with
      | Eq => true
      | _ => false
      end) true.

Lemma qeq_imp_qeqT : forall a b : Q, a == b -> QeqT a b.
Proof.
  intros a b Hab.
  unfold QeqT.
  destruct (Qcompare a b) eqn:E.
  - reflexivity.
  - exfalso.
    assert (Hc : Qcompare a b = Eq).
    { apply (proj1 (Qeq_alt a b)). exact Hab. }
    rewrite E in Hc. discriminate.
  - exfalso.
    assert (Hc : Qcompare a b = Eq).
    { apply (proj1 (Qeq_alt a b)). exact Hab. }
    rewrite E in Hc. discriminate.
Qed.

Lemma qeqT_imp_qeq : forall a b : Q, QeqT a b -> a == b.
Proof.
  intros a b H. unfold QeqT in H. destruct (Qcompare a b) eqn:E.
  - exact (proj2 (Qeq_alt a b) E).
  - inversion H.
  - inversion H.
Qed.
(* The Set-level poly equality: a coefficient-level pointwise [Id]
   decision. *)
Definition lw0_qpoly_eqT (p q : qpoly) : Type :=
  forall j : nat, QeqT (lw0_coef j p) (lw0_coef j q).
(* ============================================================ *)
(* Section. The coefficient-level realization of the die budget, the  *)
(* F telescope, and the shore-flip family (the poly-level load-bearing *)
(* face of the pair slot)                                             *)
(* ============================================================ *)

(* The factorial is nonzero (positivity transport). *)
Lemma lw385_q_fact_neq : forall j : nat, ~ q_fact j == 0%Q.
Proof.
  intro j. intro Hq.
  apply (Qlt_not_eq 0%Q (q_fact j) (q_fact_pos j)).
  apply Qeq_sym. exact Hq.
Qed.
(* Right-addition congruence for [Qeq] (a rewrite at the atom level,
   so that composite-sum rewriting does not run into the [Z] expansion
   shape). *)
Lemma lw385_Qplus_eq_compat_r : forall x y z : Q, x == y -> x + z == y + z.
Proof. intros x y z H. rewrite H. reflexivity. Qed.
(* Two-sided addition congruence for [Qeq]. *)
Lemma lw385_Qplus_eq_compat2 : forall a b c d : Q,
  a == b -> a + c + d == b + c + d.
Proof. intros a b c d H. rewrite H. reflexivity. Qed.
(* The [Id] bridge for [bool] equality (the [Prop] equation at the die
   slot enters the [Set] level). *)
Lemma lw385_eq_Id : forall b : bool, b = true -> Id b true.
Proof. intros b H. destruct H. apply id_refl. Qed.
(* The conjunction decision enters the Set-level product. *)
Lemma lw385_andb_Id : forall b1 b2 : bool,
  Id (andb b1 b2) true -> And (Id b1 true) (Id b2 true).
Proof.
  intros b1 b2 H. destruct b1; destruct b2.
  - exact (id_refl, id_refl).
  - inversion H.
  - inversion H.
  - inversion H.
Qed.
(* The list-length realization of the die budget:
   [die p n = true] implies [length p <= n]. *)
Lemma lw385_die_length : forall (p : qpoly) (n : nat),
  Id (lw0_die p n) true -> (length p <= n)%nat.
Proof.
  induction p as [|a p IH]; intros n Hd.
  - simpl. apply Nat.le_0_l.
  - destruct n as [|n'].
    + inversion Hd.
    + assert (Hs := lw385_andb_Id _ _ Hd).
      destruct Hs as [H1 H2].
      assert (Hl1 := IH (Datatypes.S n') H1).
      assert (Hl2 := IH n' H2).
      simpl. exact (proj1 (Nat.succ_le_mono (length p) n') Hl2).
Qed.
(* Coefficients beyond the list length are zero. *)
Lemma lw385_coef_len_zero : forall (p : qpoly) (k : nat),
  (length p <= k)%nat -> lw0_coef k p == 0%Q.
Proof.
  induction p as [|a p IH]; intros k Hk.
  - reflexivity.
  - destruct k as [|k'].
    + simpl in Hk. exfalso. exact (Nat.nle_succ_0 _ Hk).
    + simpl in Hk. simpl. apply (IH k').
      exact (proj2 (Nat.succ_le_mono (length p) k') Hk).
Qed.
(* The coefficient-level realization of the die budget: after [n]
   iterated differentiations the coefficients vanish pointwise. *)
Lemma lw385_die_coef_zero : forall (p : qpoly) (n j : nat),
  Id (lw0_die p n) true -> lw0_coef j (qpoly_deriv_iter n p) == 0%Q.
Proof.
  intros p n j Hd.
  assert (Hlen := lw385_die_length p n Hd).
  assert (Hc0 : lw0_coef (j + n) p == 0%Q)
    by (apply lw385_coef_len_zero;
        apply (Nat.le_trans (length p) n (j + n));
        [ exact Hlen | rewrite Nat.add_comm; apply Nat.le_add_r ]).
  pose proof (lw0_coef_iter_mul n j p) as H1.
  rewrite Hc0 in H1. rewrite Qmult_0_r in H1.
  rewrite (Qmult_comm (lw0_coef j (qpoly_deriv_iter n p)) (q_fact j)) in H1.
  apply (Qmult_integral_l _ _ (lw385_q_fact_neq j) H1).
Qed.
(* The second-derivative telescope of [F_aux] (coefficient level,
   pointwise): [D^2(F_aux J) + F_aux J =
   c*f + c*(-1)^J * D^{2(S J)}f]. *)
Lemma lw385_F_aux_plus_deriv2_coef : forall (J : nat) (f : qpoly) (c : Q),
  lw0_qpoly_eqT
    (qpoly_add (qpoly_deriv_iter 2 (lw0_F_aux f c J)) (lw0_F_aux f c J))
    (qpoly_add (qpoly_scalar c f)
       (qpoly_scalar (c * lw0_alt J)%Q
          (qpoly_deriv_iter (2 * Datatypes.S J) f))).
Proof.
  induction J as [|J' IH]; intros f c j; apply qeq_imp_qeqT.
  - change (lw0_F_aux f c 0%nat) with (qpoly_scalar c f).
    change (2 * Datatypes.S 0)%nat with 2%nat.
    change (lw0_alt 0%nat) with 1%Q.
    rewrite !lw0_coef_add.
    rewrite (lw0_coef_iter_scalar 2 j c f).
    rewrite !lw0_coef_scalar.
    ring.
  - change (lw0_F_aux f c (Datatypes.S J'))
      with (qpoly_add (lw0_F_aux f c J')
              (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                 (qpoly_deriv_iter (2 * Datatypes.S J') f))).
    rewrite !lw0_coef_add.
    rewrite (lw0_coef_iter_add 2 j (lw0_F_aux f c J')
               (qpoly_scalar (c * lw0_alt (Datatypes.S J'))%Q
                  (qpoly_deriv_iter (2 * Datatypes.S J') f))).
    rewrite !lw0_coef_scalar.
    rewrite (lw0_coef_iter_scalar 2 j (c * lw0_alt (Datatypes.S J'))%Q
               (qpoly_deriv_iter (2 * Datatypes.S J') f)).
    rewrite <- (lw0_qp_deriv_iter_plus 2 (2 * Datatypes.S J') f).
    replace (2 + 2 * Datatypes.S J')%nat
      with (2 * Datatypes.S (Datatypes.S J'))%nat
      by (rewrite !Nat.mul_succ_r, Nat.add_comm; reflexivity).
    assert (IHj := qeqT_imp_qeq _ _ (IH f c j)).
    transitivity (lw0_coef j (qpoly_deriv_iter 2 (lw0_F_aux f c J'))
                  + lw0_coef j (lw0_F_aux f c J')
                  + (c * lw0_alt (Datatypes.S J'))%Q
                    * lw0_coef j (qpoly_deriv_iter (2 * Datatypes.S J') f)
                  + (c * lw0_alt (Datatypes.S J'))%Q
                    * lw0_coef j (qpoly_deriv_iter
                         (2 * Datatypes.S (Datatypes.S J')) f)).
    + rewrite (lw0_alt_opp J'). ring.
    + transitivity (c * lw0_coef j f
                    + (c * lw0_alt J')%Q
                      * lw0_coef j (qpoly_deriv_iter (2 * Datatypes.S J') f)
                    + (c * lw0_alt (Datatypes.S J'))%Q
                      * lw0_coef j (qpoly_deriv_iter (2 * Datatypes.S J') f)
                    + (c * lw0_alt (Datatypes.S J'))%Q
                      * lw0_coef j (qpoly_deriv_iter
                           (2 * Datatypes.S (Datatypes.S J')) f)).
      * rewrite !lw0_coef_add in IHj. rewrite !lw0_coef_scalar in IHj.
        apply (lw385_Qplus_eq_compat2 _ _ _ _ IHj).
      * rewrite (lw0_alt_opp J'). ring.
Qed.
(* The main piece of the first slot: [F + F'' = f] (poly level; the
   die premise is carried as a Set-level [Id]). *)
Lemma lw385_F_plus_deriv2_coef : forall (f : qpoly) (J : nat),
  Id (lw0_die f (2 * Datatypes.S J)) true ->
  lw0_qpoly_eqT (qpoly_add (qpoly_deriv_iter 2 (lw0_F f J)) (lw0_F f J)) f.
Proof.
  intros f J Hd j. apply qeq_imp_qeqT.
  unfold lw0_F.
  assert (Haux := qeqT_imp_qeq _ _
    (lw385_F_aux_plus_deriv2_coef J f 1%Q j)).
  rewrite !lw0_coef_add in Haux.
  rewrite (lw0_coef_scalar j 1%Q f) in Haux.
  rewrite (lw0_coef_scalar j (1 * lw0_alt J)%Q
             (qpoly_deriv_iter (2 * Datatypes.S J) f)) in Haux.
  rewrite !lw0_coef_add.
  rewrite Haux.
  assert (Hz := lw385_die_coef_zero f (2 * Datatypes.S J) j Hd).
  rewrite Hz. ring.
Qed.
(* The [niven_f] instance: [F + F'' = niven_f] (the direct
   substitution form at [J := n]). *)
Lemma lw385_F_plus_deriv2_coef_niven : forall (q b : Q) (n : nat),
  lw0_qpoly_eqT
    (qpoly_add (qpoly_deriv_iter 2 (lw0_F (lw0_niven_f q b n) n))
               (lw0_F (lw0_niven_f q b n) n))
    (lw0_niven_f q b n).
Proof.
  intros q b n. apply lw385_F_plus_deriv2_coef.
  apply lw385_eq_Id. apply lw0_niven_f_die.
Qed.
(* Integral cancellation of the zero head term of [mul]. *)
Lemma lw385_ai_mul_zero : forall (g p : qpoly),
  (forall j : nat, lw0_coef j p == 0%Q) ->
  forall (k : nat) (x : Q),
    qpoly_eval (lw0_qp_ai (qpoly_mul p g) k) x == 0%Q.
Proof.
  intros g p. induction p as [|a p IH]; intros Hz k x.
  - reflexivity.
  - assert (Ha : a == 0%Q) by (apply (Hz 0%nat)).
    change (qpoly_mul (cons a p) g)
      with (qpoly_add (qpoly_scalar a g) (cons 0%Q (qpoly_mul p g))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g)
               (cons 0%Q (qpoly_mul p g)) k x).
    rewrite (lw0_qp_ai_scalar a g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul p g) k x).
    rewrite Ha.
    rewrite (IH (fun j => Hz (Datatypes.S j)) (Datatypes.S k) x).
    ring.
Qed.
(* Inheritance of the poly-level equality of [mul] lists under the ai
   evaluation. *)
Lemma lw385_ai_mul_congr_eval : forall (g p f : qpoly),
  lw0_qpoly_eqT p f ->
  forall (k : nat) (x : Q),
    qpoly_eval (lw0_qp_ai (qpoly_mul p g) k) x
    == qpoly_eval (lw0_qp_ai (qpoly_mul f g) k) x.
Proof.
  intros g p. induction p as [|a p IH]; intros f Hp k x.
  - destruct f as [|b f].
    + apply Qeq_refl.
    + assert (Hz : forall j : nat, lw0_coef j (cons b f) == 0%Q)
        by (intro j; apply Qeq_sym; apply qeqT_imp_qeq; apply Hp).
      transitivity 0%Q.
      * reflexivity.
      * symmetry. exact (lw385_ai_mul_zero g (cons b f) Hz k x).
  - destruct f as [|b f].
    + assert (Hz : forall j : nat, lw0_coef j (cons a p) == 0%Q)
        by (intro j; apply qeqT_imp_qeq; apply Hp).
      transitivity 0%Q.
      * exact (lw385_ai_mul_zero g (cons a p) Hz k x).
      * reflexivity.
    + assert (Hab : a == b%Q) by (apply qeqT_imp_qeq; apply (Hp 0%nat)).
      assert (Htail : lw0_qpoly_eqT p f)
        by (intro j; exact (Hp (Datatypes.S j))).
      change (qpoly_mul (cons a p) g)
        with (qpoly_add (qpoly_scalar a g) (cons 0%Q (qpoly_mul p g))).
      change (qpoly_mul (cons b f) g)
        with (qpoly_add (qpoly_scalar b g) (cons 0%Q (qpoly_mul f g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g)
                 (cons 0%Q (qpoly_mul p g)) k x).
      rewrite (lw0_qp_ai_add (qpoly_scalar b g)
                 (cons 0%Q (qpoly_mul f g)) k x).
      rewrite (lw0_qp_ai_scalar a g k x).
      rewrite (lw0_qp_ai_scalar b g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul p g) k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g) k x).
      rewrite Hab.
      rewrite (IH f Htail (Datatypes.S k) x).
      reflexivity.
Qed.
(* The paired product respects the poly-level equality in its left
   argument. *)
Lemma lw385_pair_congr_l : forall (p f g : qpoly) (x : Q),
  lw0_qpoly_eqT p f -> QeqT (lw0_qp_pair p g x) (lw0_qp_pair f g x).
Proof.
  intros p f g x Hp. apply qeq_imp_qeqT.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0%Q (lw0_qp_ai (qpoly_mul p g) 0)) x)
    with (0 + x * qpoly_eval (lw0_qp_ai (qpoly_mul p g) 0) x)%Q.
  change (qpoly_eval (cons 0%Q (lw0_qp_ai (qpoly_mul f g) 0)) x)
    with (0 + x * qpoly_eval (lw0_qp_ai (qpoly_mul f g) 0) x)%Q.
  rewrite (lw385_ai_mul_congr_eval g p f Hp 0%nat x).
  reflexivity.
Qed.
(* The [F + F''] identity for [pair(F, .)] (for the IBP assembly). *)
Lemma lw385_pair_F_plus_deriv2 : forall (f g : qpoly) (J : nat) (x : Q),
  Id (lw0_die f (2 * Datatypes.S J)) true ->
  QeqT (lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F f J)) g x
        + lw0_qp_pair (lw0_F f J) g x)
       (lw0_qp_pair f g x).
Proof.
  intros f g J x Hd. apply qeq_imp_qeqT.
  transitivity (lw0_qp_pair (qpoly_add (qpoly_deriv_iter 2 (lw0_F f J))
                              (lw0_F f J)) g x).
  - exact (Qeq_sym _ _ (lw0_qp_pair_add_l (qpoly_deriv_iter 2 (lw0_F f J))
               (lw0_F f J) g x)).
  - exact (qeqT_imp_qeq _ _
             (lw385_pair_congr_l (qpoly_add (qpoly_deriv_iter 2 (lw0_F f J))
                                  (lw0_F f J)) f g x
                (lw385_F_plus_deriv2_coef f J Hd))).
Qed.
(* The Niven instance of the [F + F''] identity for [pair(F, .)]. *)
Lemma lw385_pair_F_plus_deriv2_niven :
  forall (q b : Q) (n m : nat) (x : Q),
  QeqT (lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F (lw0_niven_f q b n) n))
                    (lw0_sin_qp m) x
        + lw0_qp_pair (lw0_F (lw0_niven_f q b n) n) (lw0_sin_qp m) x)
       (lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) x).
Proof.
  intros q b n m x. apply (lw385_pair_F_plus_deriv2).
  apply lw385_eq_Id. apply lw0_niven_f_die.
Qed.
(* The shore-flip transform: bool-alternating pointwise negation (the
   alternating signs of the odd/even coefficients cancel [s^2]). *)
Fixpoint lw385_flip_aux (b : bool) (p : qpoly) : qpoly :=
  match p with
  | nil => nil
  | cons a p' =>
      match b with
      | true => cons a (lw385_flip_aux false p')
      | false => cons (- a)%Q (lw385_flip_aux true p')
      end
  end.
(* An even power of a negative base equals the same power of the
   positive base. *)
Lemma lw385_q_pow_neg_even : forall (n : nat) (x : Q),
  q_pow (- x)%Q (2 * n) == q_pow x (2 * n).
Proof.
  induction n as [|n IH]; intros x.
  - reflexivity.
  - replace (2 * Datatypes.S n)%nat
      with (Datatypes.S (Datatypes.S (2 * n)))%nat
      by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r;
          reflexivity).
    rewrite (q_pow_succ (- x)%Q (Datatypes.S (2 * n))).
    rewrite (q_pow_succ (- x)%Q (2 * n)).
    rewrite IH.
    rewrite (q_pow_succ x (Datatypes.S (2 * n))).
    rewrite (q_pow_succ x (2 * n)).
    ring.
Qed.
(* An odd power of a negative base equals the negated same power of
   the positive base. *)
Lemma lw385_q_pow_neg_odd : forall (n : nat) (x : Q),
  q_pow (- x)%Q (Datatypes.S (2 * n)) == (- q_pow x (Datatypes.S (2 * n)))%Q.
Proof.
  intros n x.
  rewrite (q_pow_succ (- x)%Q (2 * n)).
  rewrite (lw385_q_pow_neg_even n x).
  rewrite (q_pow_succ x (2 * n)).
  ring.
Qed.
(* The integral conversion of the zero-shift list: the degree index
   moves by [n]. *)
Lemma lw385_ai_zero_shift : forall (n : nat) (p : qpoly) (k : nat) (x : Q),
  qpoly_eval (lw0_qp_ai (lw0_pitB_conv_zero_shift n p) k) x
  == q_pow x n * qpoly_eval (lw0_qp_ai p (k + n)%nat) x.
Proof.
  induction n as [|n IH]; intros p k x.
  - change (lw0_pitB_conv_zero_shift 0 p) with p.
    change (q_pow x 0) with 1%Q.
    rewrite Nat.add_0_r. rewrite Qmult_1_l. reflexivity.
  - change (lw0_pitB_conv_zero_shift (Datatypes.S n) p)
      with (cons 0%Q (lw0_pitB_conv_zero_shift n p)).
    rewrite (lw0_qp_ai_zero_head_eval (lw0_pitB_conv_zero_shift n p) k x).
    rewrite (IH p (Datatypes.S k) x).
    replace (Datatypes.S k + n)%nat with (k + Datatypes.S n)%nat
      by (rewrite Nat.add_succ_l, Nat.add_succ_r; reflexivity).
    rewrite (q_pow_succ x n).
    ring.
Qed.
(* The symmetry of the odd-index difference at [-x] (carried by odd
   powers of a negative base). *)
Lemma lw385_ai_delta_odd : forall (j : nat) (c : Q) (k : nat) (x : Q),
  qpoly_eval (lw0_qp_ai (qpoly_scalar c
    (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))) k)
    (- x)%Q
  == (- qpoly_eval (lw0_qp_ai (qpoly_scalar c
        (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))) k)
        x)%Q.
Proof.
  intros j c k x.
  rewrite (lw0_qp_ai_scalar c
             (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))
             k (- x)%Q).
  rewrite (lw0_qp_ai_scalar c
             (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))
             k x).
  rewrite (lw385_ai_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil) k (- x)%Q).
  rewrite (lw385_ai_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil) k x).
  rewrite (lw385_q_pow_neg_odd j x).
  rewrite (lw0_qp_ai_cons_eval 1%Q nil
             (k + Datatypes.S (2 * j))%nat (- x)%Q).
  rewrite (lw0_qp_ai_cons_eval 1%Q nil
             (k + Datatypes.S (2 * j))%nat x).
  cbn [lw0_qp_ai qpoly_eval].
  ring.
Qed.
(* The [mul]/[ai] shore-flip invariant (bool-alternating cancellation
   of [s^2]; the generalized induction core). *)
Lemma lw385_ai_mul_flip_aux : forall (p : qpoly) (b : bool) (g : qpoly)
                                     (k : nat) (x : Q),
  (forall (j : nat) (y : Q),
     QeqT (qpoly_eval (lw0_qp_ai g j) (- y)%Q)
          (- qpoly_eval (lw0_qp_ai g j) y)%Q) ->
  qpoly_eval (lw0_qp_ai (qpoly_mul p g) k) (- x)%Q
  == (if b then 1 else (-1))%Q
     * qpoly_eval (lw0_qp_ai
          (qpoly_mul (lw385_flip_aux (negb b) p) g) k) x.
Proof.
  induction p as [|a p IH]; intros b g k x Hodd.
  - cbn [qpoly_mul lw385_flip_aux lw0_qp_ai qpoly_eval]. ring.
  - destruct b.
    + change (qpoly_mul (cons a p) g)
        with (qpoly_add (qpoly_scalar a g) (cons 0%Q (qpoly_mul p g))).
      change (lw385_flip_aux (negb true) (cons a p))
        with (cons (- a)%Q (lw385_flip_aux true p)).
      change (qpoly_mul (cons (- a)%Q (lw385_flip_aux true p)) g)
        with (qpoly_add (qpoly_scalar (- a)%Q g)
               (cons 0%Q (qpoly_mul (lw385_flip_aux true p) g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g)
                 (cons 0%Q (qpoly_mul p g)) k (- x)%Q).
      rewrite (lw0_qp_ai_add (qpoly_scalar (- a)%Q g)
                 (cons 0%Q (qpoly_mul (lw385_flip_aux true p) g)) k x).
      rewrite (lw0_qp_ai_scalar a g k (- x)%Q).
      rewrite (lw0_qp_ai_scalar (- a)%Q g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul p g) k (- x)%Q).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (lw385_flip_aux true p) g)
                 k x).
      rewrite (qeqT_imp_qeq _ _ (Hodd k x)).
      rewrite (IH false g (Datatypes.S k) x Hodd).
      change (negb false) with true.
      change (if false then 1 else (-1))%Q with (-1)%Q.
      change (if true then 1 else (-1))%Q with 1%Q.
      ring.
    + change (qpoly_mul (cons a p) g)
        with (qpoly_add (qpoly_scalar a g) (cons 0%Q (qpoly_mul p g))).
      change (lw385_flip_aux (negb false) (cons a p))
        with (cons a (lw385_flip_aux false p)).
      change (qpoly_mul (cons a (lw385_flip_aux false p)) g)
        with (qpoly_add (qpoly_scalar a g)
               (cons 0%Q (qpoly_mul (lw385_flip_aux false p) g))).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g)
                 (cons 0%Q (qpoly_mul p g)) k (- x)%Q).
      rewrite (lw0_qp_ai_add (qpoly_scalar a g)
                 (cons 0%Q (qpoly_mul (lw385_flip_aux false p) g)) k x).
      rewrite (lw0_qp_ai_scalar a g k (- x)%Q).
      rewrite (lw0_qp_ai_scalar a g k x).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul p g) k (- x)%Q).
      rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (lw385_flip_aux false p) g)
                 k x).
      rewrite (qeqT_imp_qeq _ _ (Hodd k x)).
      rewrite (IH true g (Datatypes.S k) x Hodd).
      change (negb true) with false.
      change (if true then 1 else (-1))%Q with 1%Q.
      change (if false then 1 else (-1))%Q with (-1)%Q.
      ring.
Qed.
(* The [mul]/[ai] shore-flip invariant (the [b := true] instance). *)
Lemma lw385_ai_mul_flip : forall (p g : qpoly) (k : nat) (x : Q),
  (forall (j : nat) (y : Q),
     QeqT (qpoly_eval (lw0_qp_ai g j) (- y)%Q)
          (- qpoly_eval (lw0_qp_ai g j) y)%Q) ->
  qpoly_eval (lw0_qp_ai (qpoly_mul p g) k) (- x)%Q
  == qpoly_eval (lw0_qp_ai (qpoly_mul (lw385_flip_aux false p) g) k) x.
Proof.
  intros p g k x Hodd.
  apply Qeq_trans with
    (1%Q * qpoly_eval (lw0_qp_ai (qpoly_mul (lw385_flip_aux (negb true) p) g) k) x)%Q.
  - exact (lw385_ai_mul_flip_aux p true g k x Hodd).
  - apply Qmult_1_l.
Qed.
(* Inheritance of the evaluation under the [q]-to-equality switch. *)
Lemma lw385_qp_eval_q_wd : forall (E : qpoly) (q q' : Q),
  q == q' -> qpoly_eval E q == qpoly_eval E q'.
Proof.
  induction E as [|a E IH]; intros q q' Hq.
  - reflexivity.
  - change (qpoly_eval (cons a E) q) with (a + q * qpoly_eval E q)%Q.
    change (qpoly_eval (cons a E) q') with (a + q' * qpoly_eval E q')%Q.
    rewrite (IH q q' Hq). rewrite Hq. reflexivity.
Qed.
(* Inheritance of the [q]-to-equality switch for the paired product. *)
Lemma lw385_pair_q_wd : forall (p g : qpoly) (q q' : Q),
  q == q' -> QeqT (lw0_qp_pair p g q) (lw0_qp_pair p g q').
Proof.
  intros p g q q' Hq. apply qeq_imp_qeqT.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  exact (lw385_qp_eval_q_wd _ _ _ Hq).
Qed.
(* The absolute-value shore of the paired product (the suppression
   form of [|pair|]). *)
Lemma lw385_pair_abs_shore : forall (p g : qpoly) (x : Q),
  QleT' 0 x -> QeqT (lw0_qp_pair p g x) (lw0_qp_pair p g (Qabs x)).
Proof.
  intros p g x Hx.
  apply (lw385_pair_q_wd p g x (Qabs x)).
  apply Qeq_sym. apply Qabs_pos. apply QleT'_to_Qle. exact Hx.
Qed.
(* The absolute-value shore of the paired product after the shore
   flip. *)
Lemma lw385_pair_flip_shore : forall (p g : qpoly) (x : Q),
  (forall (j : nat) (y : Q),
     QeqT (qpoly_eval (lw0_qp_ai g j) (- y)%Q)
          (- qpoly_eval (lw0_qp_ai g j) y)%Q) ->
  QeqT (lw0_qp_pair p g (- x)%Q)
       (- lw0_qp_pair (lw385_flip_aux false p) g x)%Q.
Proof.
  intros p g x Hodd. apply qeq_imp_qeqT.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0%Q (lw0_qp_ai (qpoly_mul p g) 0)) (- x)%Q)
    with (0 + (- x)%Q * qpoly_eval (lw0_qp_ai (qpoly_mul p g) 0) (- x)%Q)%Q.
  change (qpoly_eval
            (cons 0%Q (lw0_qp_ai (qpoly_mul (lw385_flip_aux false p) g) 0)) x)
    with (0 + x * qpoly_eval
            (lw0_qp_ai (qpoly_mul (lw385_flip_aux false p) g) 0) x)%Q.
  rewrite (lw385_ai_mul_flip p g 0%nat x Hodd).
  ring.
Qed.
(* The scalar-monotone suppression form of the shore-flipped paired
   product. *)
Lemma lw385_pair_flip_shore_mono : forall (j : nat) (c : Q) (p : qpoly) (x : Q),
  QeqT (lw0_qp_pair p (qpoly_scalar c
          (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil)))
          (- x)%Q)
       (- lw0_qp_pair (lw385_flip_aux false p) (qpoly_scalar c
          (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil))) x)%Q.
Proof.
  intros j c p x. apply lw385_pair_flip_shore.
  intros j0 y. apply qeq_imp_qeqT. apply lw385_ai_delta_odd.
Qed.
(* ---- The ratio chain of the [Wb] series: order bridges and thin
   monotonicity lemmas ---- *)

Lemma lw0_ltT_leT_trans : forall x y z : Q,
  QltT x y -> QleT' y z -> QltT x z.
Proof.
  intros x y z H1 H2. apply Qlt_to_QltT.
  apply QltT_to_Qlt in H1. apply QleT'_to_Qle in H2.
  exact (Qlt_le_trans x y z H1 H2).
Qed. 
Lemma lw0_leT'_ltT_trans : forall x y z : Q,
  QleT' x y -> QltT y z -> QltT x z.
Proof.
  intros x y z H1 H2. apply Qlt_to_QltT.
  apply QleT'_to_Qle in H1. apply QltT_to_Qlt in H2.
  exact (Qle_lt_trans x y z H1 H2).
Qed. 
Lemma lw0_Qlt_le : forall x : Q, Qlt 0 x -> QleT' 0 x.
Proof. intros x H. apply Qle_to_QleT'. apply (Qlt_le_weak 0). exact H. Qed. 
Lemma lw0_qmul_le0T : forall a b : Q, QleT' 0 a -> QleT' 0 b -> QleT' 0 (a * b).
Proof. intros a b Ha Hb. apply Qle_to_QleT'.
  apply Qmult_le_0_compat; apply QleT'_to_Qle; assumption. Qed. 
Lemma lw0_qcompat4 : forall w x y z : Q,
  QleT' 0 w -> QleT' w x -> QleT' 0 y -> QleT' y z -> QleT' (w * y) (x * z).
Proof. intros w x y z H1 H2 H3 H4. apply Qle_to_QleT'.
  apply Qmult_le_compat_nonneg; split; apply QleT'_to_Qle; assumption. Qed. 
Lemma lw0_qcompat_r : forall x y z : Q,
  QleT' x y -> QleT' 0 z -> QleT' (x * z) (y * z).
Proof. intros x y z H1 H2. apply Qle_to_QleT'.
  apply Qmult_le_compat_r; apply QleT'_to_Qle; assumption. Qed. 
Lemma lw0_qcompat_l : forall x y z : Q,
  QleT' x y -> QleT' 0 z -> QleT' 0 x -> QleT' (z * x) (z * y).
Proof. intros x y z H1 H2 H3. apply Qle_to_QleT'.
  apply (Qmult_le_compat_nonneg z z x y).
  - split; apply QleT'_to_Qle; [ exact H2 | apply qleT'_refl ].
  - split; apply QleT'_to_Qle; [ exact H3 | exact H1 ].
Qed. 
Lemma qltT_not_eq_zero : forall x : Q, QltT 0 x -> x == 0 -> False.
Proof.
  intros x Hx Hz. exact (Qlt_not_eq 0 x (QltT_to_Qlt 0 x Hx) (Qeq_sym x 0 Hz)).
Qed. 
Lemma qmult_ltT_0_compat : forall a b : Q, QltT 0 a -> QltT 0 b -> QltT 0 (a * b).
Proof.
  intros a b Ha Hb. exact (Qlt_to_QltT _ _ (Qmult_lt_0_compat a b (QltT_to_Qlt _ _ Ha) (QltT_to_Qlt _ _ Hb))).
Qed. 
Lemma lw0_q_pow_nonnegT : forall (x : Q) (k : nat), QleT' 0 x -> QleT' 0 (q_pow x k).
Proof.
  intros x k Hx. induction k as [| k IH].
  - apply Qle_to_QleT'. cbn [q_pow]. unfold Qle. cbn [Qnum Qden]. red. intros Hc. discriminate Hc.
  - apply lw0_qmul_le0T.
    + exact Hx.
    + exact IH.
Qed. 
Lemma lw0_q_of_nat_lt0T_S : forall m : nat, QltT 0 (lw0_q_of_nat (Datatypes.S m)).
Proof.
  intro m. apply (lw0_ltT_leT_trans 0 1 (lw0_q_of_nat (Datatypes.S m))).
  - exact (@id_refl bool true).
  - apply lw0_q_of_nat_ge_one.
Qed. 
Lemma lw0_q_of_nat_lt0T : forall m : nat, (1 <= m)%nat -> QltT 0 (lw0_q_of_nat m).
Proof.
  intros m Hm. destruct m as [| m']; [ exfalso; inversion Hm
  | apply lw0_q_of_nat_lt0T_S ].
Qed. 
Lemma lw0_mul_lt_one : forall z x : Q, Qlt 0 z -> Qlt x 1 -> Qlt (z * x) z.
Proof.
  intros z x Hz Hx1.
  pose proof (Qmult_lt_compat_r x 1 z Hz Hx1) as Hraw.
  rewrite (Qmult_comm x z) in Hraw. rewrite (Qmult_1_l z) in Hraw.
  exact Hraw.
Qed. 
Lemma lw0_div_lt : forall x y z : Q,
  QltT 0 z -> QltT x (y * z) -> QltT (x / z) y.
Proof.
  intros x y z Hz Hlt.
  assert (Hz0 : z == 0 -> False) by (apply qltT_not_eq_zero; exact Hz).
  assert (Hpos : Qlt 0 (/ z)) by (apply Qinv_lt_0_compat; apply QltT_to_Qlt; exact Hz).
  apply Qlt_to_QltT. apply QltT_to_Qlt in Hlt.
  unfold Qdiv.
  pose proof (Qmult_lt_compat_r x (y * z) (/ z) Hpos Hlt) as Hfin.
  rewrite <- (Qmult_assoc y z (/ z)), (Qmult_inv_r z Hz0), Qmult_1_r in Hfin.
  exact Hfin.
Qed. 
Lemma lw0_inv_le : forall x y : Q,
  QltT 0 x -> QltT 0 y -> QleT' x y -> QleT' (/ y) (/ x).
Proof.
  intros x y Hx Hy Hle.
  assert (Hx0 : x == 0 -> False) by (apply qltT_not_eq_zero; exact Hx).
  assert (Hy0 : y == 0 -> False) by (apply qltT_not_eq_zero; exact Hy).
  assert (Hpos : QleT' 0 ((/ x) * (/ y))).
  { apply lw0_qmul_le0T; apply lw0_Qlt_le; apply Qinv_lt_0_compat, QltT_to_Qlt;
      [ exact Hx | exact Hy ]. }
  apply (qleT'_trans (/ y) (x * ((/ x) * (/ y))) (/ x)).
  - apply qeq_leT'.
    rewrite (Qmult_assoc x (/ x) (/ y)), (Qmult_inv_r x Hx0). ring.
  - apply (qleT'_trans (x * ((/ x) * (/ y))) (y * ((/ x) * (/ y))) (/ x)).
    + apply (lw0_qcompat_r x y ((/ x) * (/ y)) Hle Hpos).
    + apply qeq_leT'.
      rewrite (Qmult_comm y ((/ x) * (/ y))), <- (Qmult_assoc (/ x) (/ y) y).
      rewrite (Qmult_comm (/ y) y), (Qmult_inv_r y Hy0). ring.
Qed. (* ---- The factor-list decomposition of the factorial and the closed form of the Wb ratio ---- *)

Lemma lw0_q_pow_mono_base : forall (x y : Q) (n : nat),
  QleT' 0 x -> QleT' x y -> QleT' (q_pow x n) (q_pow y n).
Proof.
  intros x y n H0 Hxy. apply Qle_to_QleT'.
  induction n as [| n IH].
  - apply Qle_refl.
  - cbn [q_pow].
    apply (Qle_trans _ (x * q_pow y n)%Q).
    + rewrite (Qmult_comm x (q_pow x n)), (Qmult_comm x (q_pow y n)).
      apply Qmult_le_compat_r.
      * exact IH.
      * exact (QleT'_to_Qle _ _ H0).
    + apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ Hxy).
      * apply q_pow_nonneg. exact (QleT'_to_Qle _ _ (qleT'_trans 0 x y H0 Hxy)).
Qed. 
Lemma lw0_q_fact_step : forall k : nat,
  q_fact (Datatypes.S k) == lw0_q_of_nat (Datatypes.S k) * q_fact k.
Proof. intro k. reflexivity. Qed. 
Fixpoint lw0_fact_range (a k : nat) : Q :=
  match k with
  | 0%nat => 1%Q
  | Datatypes.S j => lw0_q_of_nat (a + Datatypes.S j) * lw0_fact_range a j
  end. 
Lemma lw0_q_fact_split : forall a k : nat,
  q_fact (a + k)%nat == q_fact a * lw0_fact_range a k.
Proof.
  intros a k. induction k as [| k IH].
  - rewrite Nat.add_0_r, Qmult_1_r. reflexivity.
  - cbn [lw0_fact_range].
    replace (a + Datatypes.S k)%nat with (Datatypes.S (a + k))%nat by ring.
    rewrite lw0_q_fact_step, IH. ring.
Qed. 
Lemma lw0_fact_range_ge_pow : forall a k : nat,
  QleT' (q_pow (lw0_q_of_nat (Datatypes.S a)) k) (lw0_fact_range a k).
Proof.
  intros a k. induction k as [| k IH].
  - apply qleT'_refl.
  - apply Qle_to_QleT'.
    cbn [lw0_fact_range q_pow].
    apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S a) * lw0_fact_range a k)%Q).
    + rewrite (Qmult_comm (lw0_q_of_nat (Datatypes.S a))
                          (q_pow (lw0_q_of_nat (Datatypes.S a)) k)),
              (Qmult_comm (lw0_q_of_nat (Datatypes.S a)) (lw0_fact_range a k)).
      apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ IH).
      * apply QleT'_to_Qle. apply lw0_q_of_nat_nonneg.
    + apply Qmult_le_compat_r.
      * apply QleT'_to_Qle. apply lw0_q_of_nat_le_mono.
        replace (a + Datatypes.S k)%nat with (Datatypes.S (a + k))%nat
          by (rewrite Nat.add_succ_r; reflexivity).
        apply le_n_S. apply Nat.le_add_r.
      * apply (Qle_trans 0%Q (q_pow (lw0_q_of_nat (Datatypes.S a)) k)
                           (lw0_fact_range a k)).
        -- apply q_pow_nonneg. apply QleT'_to_Qle. apply lw0_q_of_nat_nonneg.
        -- exact (QleT'_to_Qle _ _ IH).
Qed. 
Lemma lw0_q_pow_S : forall (x : Q) (k : nat),
  q_pow x (Datatypes.S k) == x * q_pow x k.
Proof. intros x k. reflexivity. Qed. 
Lemma lw0_q_fact_ne0 : forall k : nat, ~ (q_fact k == 0).
Proof.
  intro k. intro Hne. apply (qltT_not_eq_zero (q_fact k)).
  - apply Qlt_to_QltT. apply q_fact_pos.
  - exact Hne.
Qed. 
Lemma lw0_Wb_nonneg : forall (b q : Q) (n j : nat),
  QleT' 0 b -> QleT' 0 q -> QleT' 0 (lw0_Wb b q n j).
Proof.
  intros b q n j Hb Hq. unfold lw0_Wb, Qdiv.
  apply lw0_qmul_le0T.
  - apply lw0_qmul_le0T.
    + apply lw0_qmul_le0T.
      * exact (lw0_q_pow_nonnegT b n Hb).
      * exact (lw0_q_pow_nonnegT q (2*n + 2*j + 2)%nat Hq).
    + exact (lw0_Qlt_le (q_fact (n + 2*j + 1)) (q_fact_pos (n + 2*j + 1))).
  - apply lw0_Qlt_le. apply Qinv_lt_0_compat.
    apply Qmult_lt_0_compat;
      [ apply Qmult_lt_0_compat; apply q_fact_pos | apply q_fact_pos ].
Qed. 
Lemma lw0_Wb_ratio_eq : forall (b q : Q) (n j : nat),
  lw0_Wb b q n (Datatypes.S j) ==
  lw0_Wb b q n j *
  (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
   (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
    lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
Proof.
  intros b q n j.
  assert (E1 : q_fact (n + 2 * Datatypes.S j + 1)%nat ==
               lw0_q_of_nat (n + 2*j + 3) * lw0_q_of_nat (n + 2*j + 2) * q_fact (n + 2*j + 1)).
  { replace (n + 2 * Datatypes.S j + 1)%nat with (Datatypes.S (n + 2*j + 2))%nat by ring.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (n + 2*j + 2))%nat with (n + 2*j + 3)%nat by ring.
    replace (n + 2 * j + 2)%nat with (Datatypes.S (n + 2*j + 1))%nat by ring.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (Datatypes.S (n + 2*j + 1)))%nat with (n + 2*j + 3)%nat by ring.
    replace (Datatypes.S (n + 2*j + 1))%nat with (n + 2*j + 2)%nat by ring.
    ring. }
  assert (E2 : q_fact (2 * Datatypes.S j + 1)%nat ==
               lw0_q_of_nat (2*j + 3) * lw0_q_of_nat (2*j + 2) * q_fact (2*j + 1)).
  { replace (2 * Datatypes.S j + 1)%nat with (Datatypes.S (2 * j + 2))%nat by ring.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (2 * j + 2))%nat with (2 * j + 3)%nat by ring.
    replace (2 * j + 2)%nat with (Datatypes.S (2 * j + 1))%nat by ring.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (Datatypes.S (2 * j + 1)))%nat with (2 * j + 3)%nat by ring.
    replace (Datatypes.S (2 * j + 1))%nat with (2 * j + 2)%nat by ring.
    ring. }
  assert (E3 : q_fact (2 * n + 2 * Datatypes.S j + 2)%nat ==
               lw0_q_of_nat (2*n + 2*j + 4) * lw0_q_of_nat (2*n + 2*j + 3) * q_fact (2*n + 2*j + 2)).
  { replace (2 * n + 2 * Datatypes.S j + 2)%nat with (Datatypes.S (2 * n + 2*j + 3))%nat by ring.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (2 * n + 2*j + 3))%nat with (2 * n + 2*j + 4)%nat by ring.
    replace (2 * n + 2*j + 3)%nat with (Datatypes.S (2 * n + 2*j + 2))%nat by ring.
    rewrite lw0_q_fact_step.
    replace (Datatypes.S (Datatypes.S (2 * n + 2*j + 2)))%nat with (2 * n + 2*j + 4)%nat by ring.
    replace (Datatypes.S (2 * n + 2*j + 2))%nat with (2 * n + 2*j + 3)%nat by ring.
    ring. }
  assert (E4 : q_pow q (2 * n + 2 * Datatypes.S j + 2)%nat ==
               q * q * q_pow q (2*n + 2*j + 2)%nat).
  { replace (2 * n + 2 * Datatypes.S j + 2)%nat
      with (Datatypes.S (Datatypes.S (2 * n + 2 * j + 2)))%nat by ring.
    rewrite !lw0_q_pow_S. ring. }
  unfold lw0_Wb, Qdiv.
  rewrite E4, E1, E2, E3.
  assert (HD : (q_fact n * (lw0_q_of_nat (2*j + 3) * lw0_q_of_nat (2*j + 2) * q_fact (2*j + 1)) *
                (lw0_q_of_nat (2*n + 2*j + 4) * lw0_q_of_nat (2*n + 2*j + 3) * q_fact (2*n + 2*j + 2)))%Q ==
               ((q_fact n * q_fact (2*j + 1) * q_fact (2*n + 2*j + 2)) *
                (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                 lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))%Q) by ring.
  rewrite HD.
  rewrite (Qinv_mult_distr (q_fact n * q_fact (2*j + 1) * q_fact (2*n + 2*j + 2))
             (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
              lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
  ring.
Qed. 
Lemma lw0_frac_le : forall X Y P D : Q,
  QltT 0 Y -> QltT 0 D -> QleT' (X * D) (Y * P) -> QleT' (X / Y) (P / D).
Proof.
  intros X Y P D HY HD Hkey.
  assert (HY0 : Y == 0 -> False) by (apply qltT_not_eq_zero; exact HY).
  assert (HD0 : D == 0 -> False) by (apply qltT_not_eq_zero; exact HD).
  assert (Hpos : QleT' 0 ((/ Y) * (/ D))).
  { apply lw0_qmul_le0T; apply lw0_Qlt_le; apply Qinv_lt_0_compat, QltT_to_Qlt;
      [ exact HY | exact HD ]. }
  apply (qleT'_trans (X / Y) ((X * D) * ((/ Y) * (/ D))) (P / D)).
  - apply qeq_leT'. unfold Qdiv.
    rewrite <- (Qmult_assoc X D ((/ Y) * (/ D))), (Qmult_comm D ((/ Y) * (/ D))).
    rewrite <- (Qmult_assoc (/ Y) (/ D) D), (Qmult_comm (/ D) D), (Qmult_inv_r D HD0).
    ring.
  - apply (qleT'_trans ((X * D) * ((/ Y) * (/ D))) ((Y * P) * ((/ Y) * (/ D))) (P / D)).
    + apply (lw0_qcompat_r (X * D) (Y * P) ((/ Y) * (/ D)) Hkey Hpos).
    + apply qeq_leT'.
      unfold Qdiv. rewrite (Qmult_comm Y P).
      rewrite <- (Qmult_assoc P Y ((/ Y) * (/ D))), (Qmult_assoc Y (/ Y) (/ D)).
      rewrite (Qmult_inv_r Y HY0). ring.
Qed. 
Lemma lw0_lin_beat2 : forall (n j : nat),
  QleT' ((2#1) * lw0_q_of_nat (n + 2*j + 2)) (lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2)).
Proof.
  intros n j.
  assert (HA : lw0_q_of_nat (n + 2*j + 2) == lw0_q_of_nat (n + 2) + lw0_q_of_nat (2*j)) by
    (replace (n + 2*j + 2)%nat with ((n + 2) + (2*j))%nat by ring;
     apply lw0_q_of_nat_add).
  assert (HC : lw0_q_of_nat (2*j + 2) == lw0_q_of_nat 2 + lw0_q_of_nat (2*j)) by
    (replace (2*j + 2)%nat with (2 + (2*j))%nat by ring; apply lw0_q_of_nat_add).
  assert (H2 : lw0_q_of_nat 2 == (2#1)) by reflexivity.
  apply (qleT'_trans ((2#1) * lw0_q_of_nat (n + 2*j + 2))
                     ((2#1) * lw0_q_of_nat (n + 2) + (2#1) * lw0_q_of_nat (2*j))
                     (lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2))).
  - apply (qeq_leT' ((2#1) * lw0_q_of_nat (n + 2*j + 2))
                    ((2#1) * lw0_q_of_nat (n + 2) + (2#1) * lw0_q_of_nat (2*j))).
    rewrite HA. ring.
  - apply (qleT'_trans
           ((2#1) * lw0_q_of_nat (n + 2) + (2#1) * lw0_q_of_nat (2*j))
           (lw0_q_of_nat (n + 2) * (2#1) + lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j))
           (lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2))).
    + apply qleT'_plus_compat.
      * apply (qeq_leT' ((2#1) * lw0_q_of_nat (n + 2))
                        (lw0_q_of_nat (n + 2) * (2#1))).
        ring.
      * apply lw0_qcompat_r.
        -- replace (2#1)%Q with (lw0_q_of_nat 2) by reflexivity.
           apply lw0_q_of_nat_le_mono. exact (Nat.le_add_l 2 n).
        -- apply lw0_q_of_nat_nonneg.
    + apply (qeq_leT' (lw0_q_of_nat (n + 2) * (2#1) + lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j))
                      (lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2))).
      rewrite HC. rewrite H2. ring.
Qed. 
Lemma lw0_lin_beat3 : forall (n j : nat),
  QleT' ((3#1) * lw0_q_of_nat (n + 2*j + 3)) (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3)).
Proof.
  intros n j.
  assert (HA : lw0_q_of_nat (n + 2*j + 3) == lw0_q_of_nat (n + 3) + lw0_q_of_nat (2*j)) by
    (replace (n + 2*j + 3)%nat with ((n + 3) + (2*j))%nat by ring;
     apply lw0_q_of_nat_add).
  assert (HC : lw0_q_of_nat (2*j + 3) == lw0_q_of_nat 3 + lw0_q_of_nat (2*j)) by
    (replace (2*j + 3)%nat with (3 + (2*j))%nat by ring; apply lw0_q_of_nat_add).
  assert (H3 : lw0_q_of_nat 3 == (3#1)) by reflexivity.
  apply (qleT'_trans ((3#1) * lw0_q_of_nat (n + 2*j + 3))
                     ((3#1) * lw0_q_of_nat (n + 3) + (3#1) * lw0_q_of_nat (2*j))
                     (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))).
  - apply (qeq_leT' ((3#1) * lw0_q_of_nat (n + 2*j + 3))
                    ((3#1) * lw0_q_of_nat (n + 3) + (3#1) * lw0_q_of_nat (2*j))).
    rewrite HA. ring.
  - apply (qleT'_trans
           ((3#1) * lw0_q_of_nat (n + 3) + (3#1) * lw0_q_of_nat (2*j))
           (lw0_q_of_nat (n + 3) * (3#1) + lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j))
           (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))).
    + apply qleT'_plus_compat.
      * apply (qeq_leT' ((3#1) * lw0_q_of_nat (n + 3))
                        (lw0_q_of_nat (n + 3) * (3#1))).
        ring.
      * apply lw0_qcompat_r.
        -- replace (3#1)%Q with (lw0_q_of_nat 3) by reflexivity.
           apply lw0_q_of_nat_le_mono. exact (Nat.le_add_l 3 n).
        -- apply lw0_q_of_nat_nonneg.
    + apply (qeq_leT' (lw0_q_of_nat (n + 3) * (3#1) + lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j))
                      (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))).
      rewrite HC. rewrite H3. ring.
Qed. 
Lemma lw0_twelve_AB_le : forall (n j : nat), (2 <= n)%nat ->
  QleT' ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3))
        (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)).
Proof.
  intros n j Hn.
  assert (S1 := lw0_lin_beat2 n j).
  assert (S2 := lw0_lin_beat3 n j).
  assert (S3 : QleT' (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4))
                     (lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
  { apply lw0_qcompat4.
    - apply lw0_q_of_nat_nonneg.
    - apply lw0_q_of_nat_le_mono.
      exact (Nat.add_le_mono (2 * n) (2 * n + 2 * j) 3 3
               (Nat.le_add_r (2 * n) (2 * j)) (Nat.le_refl 3)).
    - apply lw0_q_of_nat_nonneg.
    - apply lw0_q_of_nat_le_mono.
      exact (Nat.add_le_mono (2 * n) (2 * n + 2 * j) 4 4
               (Nat.le_add_r (2 * n) (2 * j)) (Nat.le_refl 4)). }
  assert (S4 : QleT' ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3))
                     (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4))).
  { assert (HD : lw0_q_of_nat (2*n + 4) == (2#1) * lw0_q_of_nat (n + 2)).
    { replace (2 * n + 4)%nat with ((n + 2) + (n + 2))%nat by ring.
      rewrite lw0_q_of_nat_add. ring. }
    apply (qleT'_trans ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3))
                       (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2 * n + 4))
                       (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4))).
    - apply (qeq_leT' ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3))
                      (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2 * n + 4))).
      rewrite HD. ring.
    - apply lw0_qcompat_r.
      + apply lw0_q_of_nat_le_mono.
        replace (2 * n + 3)%nat with (n + (n + 3))%nat by ring.
        exact (Nat.le_add_l (n + 3) n).
      + apply lw0_q_of_nat_nonneg. }
  apply (qleT'_trans
      ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3))
      (((lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2)) *
        (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))) * (2#1))
      (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
       lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
  - apply (qleT'_trans
        ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3))
        (((2#1) * lw0_q_of_nat (n + 2*j + 2)) * ((3#1) * lw0_q_of_nat (n + 2*j + 3)) * (2#1))
        (((lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2)) *
          (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))) * (2#1))).
    + apply qeq_leT'. ring.
    + apply lw0_qcompat_r.
      * apply lw0_qcompat4.
        -- apply lw0_qmul_le0T;
             [ exact (@id_refl bool true)
             | apply lw0_q_of_nat_nonneg ].
        -- exact S1.
        -- apply lw0_qmul_le0T;
             [ exact (@id_refl bool true)
             | apply lw0_q_of_nat_nonneg ].
        -- exact S2.
      * exact (@id_refl bool true).
  - apply (qleT'_trans
        (((lw0_q_of_nat (n + 2) * lw0_q_of_nat (2*j + 2)) *
          (lw0_q_of_nat (n + 3) * lw0_q_of_nat (2*j + 3))) * (2#1))
        ((lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)) *
         ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3)))
        (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
    + apply qeq_leT'. ring.
    + apply (qleT'_trans
          ((lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)) *
           ((2#1) * lw0_q_of_nat (n + 2) * lw0_q_of_nat (n + 3)))
          ((lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)) *
           (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4)))
          (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
           lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
      * apply lw0_qcompat4.
        -- apply lw0_qmul_le0T; apply lw0_q_of_nat_nonneg.
        -- apply qleT'_refl.
        -- apply lw0_qmul_le0T;
             [ apply lw0_qmul_le0T;
                 [ exact (@id_refl bool true) | apply lw0_q_of_nat_nonneg ]
             | apply lw0_q_of_nat_nonneg ].
        -- exact S4.
      * apply (qleT'_trans
              ((lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)) *
               (lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4)))
              ((lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4)) *
               (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)))
              (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
               lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
        -- apply qeq_leT'. ring.
        -- apply (qleT'_trans
                ((lw0_q_of_nat (2*n + 3) * lw0_q_of_nat (2*n + 4)) *
                 (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)))
                ((lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)) *
                 (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3)))
                (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                 lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
           ++ apply lw0_qcompat_r.
              ** exact S3.
              ** apply lw0_qmul_le0T; apply lw0_q_of_nat_nonneg.
           ++ apply qeq_leT'. ring.
Qed. 
Lemma lw0_Wb_ratio_bound : forall (b q : Q) (n j : nat),
  QleT' 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  QleT' (lw0_Wb b q n (Datatypes.S j)) (lw0_Wb b q n j * (25#27)).
Proof.
  intros b q n j Hb0 Hq Hq103 Hn.
  assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
  assert (Hden : QltT 0 (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply QltT_to_Qlt. apply qmult_ltT_0_compat.
      + apply qmult_ltT_0_compat; apply lw0_q_of_nat_lt0T.
        * apply (Nat.le_trans 1 2 (2*j+2)).
          -- apply le_n_S. apply Nat.le_0_l.
          -- apply Nat.le_add_l.
        * apply (Nat.le_trans 1 3 (2*j+3)).
          -- apply le_n_S. apply Nat.le_0_l.
          -- apply Nat.le_add_l.
      + apply lw0_q_of_nat_lt0T.
        apply (Nat.le_trans 1 3 (2*n+2*j+3)).
        * apply le_n_S. apply Nat.le_0_l.
        * apply Nat.le_add_l.
    - apply QltT_to_Qlt. apply lw0_q_of_nat_lt0T.
      apply (Nat.le_trans 1 4 (2*n+2*j+4)).
      * apply le_n_S. apply Nat.le_0_l.
      * apply Nat.le_add_l. }
  assert (Hqq : QleT' (q * q) ((100#9))).
  { apply (qleT'_trans (q * q) ((10#3) * (10#3)) ((100#9))).
    - apply lw0_qcompat4; assumption.
    - apply qeq_leT'. reflexivity. }
  assert (Hratio : QleT' (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                          (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                           lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))
                         ((25#1) / (27#1))).
  { apply lw0_frac_le.
    + exact Hden.
    + exact (@id_refl bool true).
    + apply (qleT'_trans
          ((q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)) * (27#1))
          (((100#9) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)) * (27#1))
          (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
           lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4) * (25#1))).
      * apply lw0_qcompat_r.
        -- apply lw0_qcompat_r.
           ++ apply lw0_qcompat_r.
              ** exact Hqq.
              ** apply lw0_q_of_nat_nonneg.
           ++ apply lw0_q_of_nat_nonneg.
        -- exact (@id_refl bool true).
      * apply (qleT'_trans
            (((100#9) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)) * (27#1))
            ((25#1) * ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)))
            (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
             lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4) * (25#1))).
        -- apply qeq_leT'. ring.
        -- apply (qleT'_trans
              ((25#1) * ((12#1) * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3)))
              ((25#1) * (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))
              (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
               lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4) * (25#1))).
           ++ apply lw0_qcompat_l.
              ** exact (lw0_twelve_AB_le n j Hn).
              ** exact (@id_refl bool true).
              ** apply lw0_qmul_le0T.
                 --- apply lw0_qmul_le0T;
                       [ exact (@id_refl bool true)
                       | apply lw0_q_of_nat_nonneg ].
                 --- apply lw0_q_of_nat_nonneg.
           ++ apply qeq_leT'. ring. }
  assert (Hratio0 : QleT' 0 (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                           (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                            lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4)))).
  { unfold Qdiv. apply lw0_qmul_le0T.
    - apply lw0_QltT_le. apply qmult_ltT_0_compat.
      + apply qmult_ltT_0_compat.
        * exact (qmult_ltT_0_compat q q Hq Hq).
        * apply lw0_q_of_nat_lt0T.
          apply (Nat.le_trans 1 2 (n+2*j+2));
            [ apply le_n_S; apply Nat.le_0_l
            | apply Nat.le_add_l ].
      + apply lw0_q_of_nat_lt0T.
        apply (Nat.le_trans 1 3 (n+2*j+3)).
        * apply le_n_S. apply Nat.le_0_l.
        * apply Nat.le_add_l.
    - apply lw0_Qlt_le. apply Qinv_lt_0_compat. apply QltT_to_Qlt. exact Hden. }
  apply (qleT'_trans (lw0_Wb b q n (Datatypes.S j))
                     (lw0_Wb b q n j * (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                       (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                        lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))))
                     (lw0_Wb b q n j * (25#27))).
  - apply (qeq_leT' (lw0_Wb b q n (Datatypes.S j))
                    (lw0_Wb b q n j * (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                     (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                      lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))))).
    exact (lw0_Wb_ratio_eq b q n j).
  - apply (qleT'_trans (lw0_Wb b q n j * (q * q * lw0_q_of_nat (n + 2*j + 2) * lw0_q_of_nat (n + 2*j + 3) /
                        (lw0_q_of_nat (2*j + 2) * lw0_q_of_nat (2*j + 3) *
                         lw0_q_of_nat (2*n + 2*j + 3) * lw0_q_of_nat (2*n + 2*j + 4))))
                       (lw0_Wb b q n j * ((25#1) / (27#1)))
                       (lw0_Wb b q n j * (25#27))).
    + apply lw0_qcompat_l.
      * exact Hratio.
      * exact (lw0_Wb_nonneg b q n j Hb0 Hq0).
      * exact Hratio0.
    + apply qeq_leT'. reflexivity.
Qed. 
Lemma lw0_Wb_seq_nonneg : forall (b q : Q) (n j : nat),
  QleT' 0 b -> QltT 0 q -> QleT' 0 (lw0_Wb b q n j).
Proof.
  intros b q n j Hb Hq.
  apply lw0_Wb_nonneg.
  - exact Hb.
  - apply lw0_QltT_le. exact Hq.
Qed. 
Lemma lw0_Wb_seq_decr : forall (b q : Q) (n j : nat),
  QleT' 0 b -> QltT 0 q -> QleT' q (10/3) -> (2 <= n)%nat ->
  QleT' (lw0_Wb b q n (Datatypes.S j)) (lw0_Wb b q n j).
Proof.
  intros b q n j Hb Hq Hq103 Hn.
  apply (qleT'_trans (lw0_Wb b q n (Datatypes.S j))
                     (lw0_Wb b q n j * (25#27)) (lw0_Wb b q n j)).
  - apply lw0_Wb_ratio_bound; assumption.
  - apply (qleT'_trans (lw0_Wb b q n j * (25#27))
                       (lw0_Wb b q n j * 1) (lw0_Wb b q n j)).
    + apply (lw0_qcompat_l (25#27) 1 (lw0_Wb b q n j)).
      * exact (@id_refl bool true).
      * apply lw0_Wb_seq_nonneg; [ exact Hb | exact Hq ].
      * exact (@id_refl bool true).
    + apply qeq_leT'. ring.
Qed. (* ---- The sign-absorption lemma family of the alternating-sum accumulator ---- *)

Lemma altsum_qleT'_neg_le0 : forall a : Q, QleT' 0 a -> QleT' (Qopp a) 0.
Proof.
  intros a H.
  apply Qle_to_QleT'.
  apply (Qle_trans (Qopp a) (Qopp 0) 0).
  - apply Qopp_le_compat. apply QleT'_to_Qle. exact H.
  - apply qeq_imp_qle. ring.
Qed. 
Lemma altsum_qleT'_ge_sub : forall a b : Q, QleT' a b -> QleT' 0 (b + Qopp a).
Proof.
  intros a b H.
  apply Qle_to_QleT'.
  apply (Qle_trans 0 (a + Qopp a) (b + Qopp a)).
  - apply qeq_imp_qle. apply Qeq_sym. apply Qplus_opp_r.
  - apply (Qplus_le_compat a b (Qopp a) (Qopp a)).
    + apply QleT'_to_Qle. exact H.
    + apply Qle_refl.
Qed. 
Fixpoint altsum_acc (sg : bool) (f : nat -> Q) (k n : nat) : Q :=
  match n with
  | 0%nat => 0%Q
  | Datatypes.S m => (if sg then f k else Qopp (f k))
                     + altsum_acc (negb sg) f (Datatypes.S k) m
  end. 
Definition altsum (f : nat -> Q) (n : nat) : Q := altsum_acc true f 0%nat n. 
Definition altsum_sgp (k : nat) : bool := if Nat.even k then true else false. 
Lemma altsum_acc_T : forall (f : nat -> Q) (k m : nat),
  altsum_acc true f k (Datatypes.S m) == f k + altsum_acc false f (Datatypes.S k) m.
Proof. intros f k m. simpl. ring. Qed. 
Lemma altsum_acc_F : forall (f : nat -> Q) (k m : nat),
  altsum_acc false f k (Datatypes.S m) == Qopp (f k) + altsum_acc true f (Datatypes.S k) m.
Proof. intros f k m. simpl. ring. Qed. 
Lemma altsum_acc_0_eq : forall (sg : bool) (f : nat -> Q) (k : nat),
  altsum_acc sg f k 0%nat == 0.
Proof. intros sg f k. exact (Qeq_refl 0). Qed. 
Lemma lw0_acc_add_gen : forall (a : nat) (sg : bool) (W : nat -> Q) (k b : nat),
  altsum_acc sg W k (a + b)%nat ==
  altsum_acc sg W k a +
  altsum_acc (if Nat.even a then sg else negb sg) W (k + a) b.
Proof.
  intros a. induction a as [| a IH]; intros sg W k b.
  - replace (0 + b)%nat with b%nat by ring.
    rewrite (altsum_acc_0_eq sg W k).
    replace (k + 0)%nat with k%nat by ring.
    replace (if Nat.even 0 then sg else negb sg) with sg by reflexivity.
    ring.
  - destruct sg.
    + replace (Datatypes.S a + b)%nat with (Datatypes.S (a + b))%nat by ring.
      rewrite altsum_acc_T.
      rewrite (IH false W (Datatypes.S k) b).
      rewrite (altsum_acc_T W k a).
      replace (k + Datatypes.S a)%nat with (Datatypes.S k + a)%nat by ring.
      rewrite Nat.even_succ, <- Nat.negb_even.
      destruct (Nat.even a); cbn; ring.
    + replace (Datatypes.S a + b)%nat with (Datatypes.S (a + b))%nat by ring.
      rewrite altsum_acc_F.
      rewrite (IH true W (Datatypes.S k) b).
      rewrite (altsum_acc_F W k a).
      replace (k + Datatypes.S a)%nat with (Datatypes.S k + a)%nat by ring.
      rewrite Nat.even_succ, <- Nat.negb_even.
      destruct (Nat.even a); cbn; ring.
Qed. 
Lemma lw0_altsum_add : forall (W : nat -> Q) (a b : nat),
  altsum W (a + b)%nat == altsum W a + altsum_acc (altsum_sgp a) W a b.
Proof.
  intros W a b. unfold altsum, altsum_sgp.
  pose proof (lw0_acc_add_gen a true W 0 b) as H.
  rewrite H.
  destruct (Nat.even a); cbn; ring.
Qed. 
Lemma lw0_acc_quad : forall (W : nat -> Q),
  (forall k, QleT' 0 (W k)) -> (forall k, QleT' (W (Datatypes.S k)) (W k)) ->
  forall m k : nat,
  And (QleT' 0 (altsum_acc true W k m))
  (And (QleT' (altsum_acc true W k m) (W k))
  (And (QleT' (altsum_acc false W k m) 0)
       (QleT' (Qopp (W k)) (altsum_acc false W k m)))).
Proof.
  intros W H0 Hd m. induction m as [| m IH].
  - intro k. split; [ apply qleT'_refl | split; [ apply H0
      | split; [ apply qleT'_refl | apply altsum_qleT'_neg_le0; apply H0 ] ] ].
  - intro k.
    destruct (IH k) as [I1 [I2 [I3 I4]]].
    destruct (IH (Datatypes.S k)) as [J1 [J2 [J3 J4]]].
      assert (EA : altsum_acc true W k (Datatypes.S m)
                   == W k + altsum_acc false W (Datatypes.S k) m) by apply altsum_acc_T.
      assert (EB : altsum_acc false W k (Datatypes.S m)
                   == Qopp (W k) + altsum_acc true W (Datatypes.S k) m) by apply altsum_acc_F.
      split.
      * apply (qleT'_trans 0 (W k + Qopp (W (Datatypes.S k)))
                           (altsum_acc true W k (Datatypes.S m))).
        -- apply altsum_qleT'_ge_sub. apply Hd.
        -- apply (qleT'_trans (W k + Qopp (W (Datatypes.S k)))
                              (W k + altsum_acc false W (Datatypes.S k) m)
                              (altsum_acc true W k (Datatypes.S m))).
           ++ apply qleT'_plus_compat; [ apply qleT'_refl | exact J4 ].
           ++ apply qeq_leT'. rewrite EA. reflexivity.
      * split.
        -- apply (qleT'_trans (altsum_acc true W k (Datatypes.S m)) (W k + 0) (W k)).
           ++ apply (qleT'_trans (altsum_acc true W k (Datatypes.S m))
                                 (W k + altsum_acc false W (Datatypes.S k) m)
                                 (W k + 0)).
              ** apply qeq_leT'. rewrite EA. reflexivity.
              ** apply qleT'_plus_compat; [ apply qleT'_refl | exact J3 ].
           ++ apply qeq_leT'. ring.
        -- split.
              ** apply (qleT'_trans (altsum_acc false W k (Datatypes.S m))
                                    (Qopp (W k) + altsum_acc true W (Datatypes.S k) m) 0).
                 --- apply qeq_leT'. rewrite EB. reflexivity.
                 --- apply (qleT'_trans (Qopp (W k) + altsum_acc true W (Datatypes.S k) m)
                                        (Qopp (W k) + W k) 0).
                     +++ apply qleT'_plus_compat;
                         [ apply qleT'_refl
                         | apply (qleT'_trans (altsum_acc true W (Datatypes.S k) m)
                                              (W (Datatypes.S k)) (W k));
                           [ exact J2 | apply Hd ] ].
                     +++ apply qeq_leT'. ring.
              ** apply (qleT'_trans (Qopp (W k)) (Qopp (W k) + 0)
                                       (altsum_acc false W k (Datatypes.S m))).
                 --- apply qeq_leT'. ring.
                 --- apply (qleT'_trans (Qopp (W k) + 0)
                           (Qopp (W k) + altsum_acc true W (Datatypes.S k) m)
                           (altsum_acc false W k (Datatypes.S m))).
                     +++ apply qleT'_plus_compat; [ apply qleT'_refl | exact J1 ].
                     +++ apply qeq_leT'. rewrite EB. reflexivity.
Qed. (* ---- Numerator-side factor control and the w0n core estimate ---- *)

Lemma lw0_pitS_q_pow_mul : forall (x y : Q) (t : nat),
  q_pow x t * q_pow y t == q_pow (x * y) t.
Proof.
  intros x y t. induction t as [|t IH].
  - reflexivity.
  - rewrite (q_pow_succ x t), (q_pow_succ y t), (q_pow_succ (x * y) t).
    rewrite <- IH. ring.
Qed. 
Lemma lw0_pitS_qmul_div_cancel : forall c a d : Q,
  ~ (c == 0) -> ~ (d == 0) -> c * (a * / (c * d)) == a * / d.
Proof.
  intros c a d Hc0 Hd0.
  assert (Hcd : ~ (c * d == 0)).
  { intro Hz. destruct (Qmult_integral c d Hz) as [Hx | Hx];
      [ exact (Hc0 Hx) | exact (Hd0 Hx) ]. }
  assert (EL : (c * a * / (c * d)) * (c * d) == c * a).
  { rewrite <- (Qmult_assoc (c * a) (/ (c * d)) (c * d)),
      (Qmult_comm (/ (c * d)) (c * d)), (Qmult_inv_r (c * d) Hcd),
      Qmult_1_r. reflexivity. }
  assert (ER : (a * / d) * (c * d) == c * a).
  { rewrite <- (Qmult_assoc a (/ d) (c * d)), (Qmult_comm (/ d) (c * d)),
      <- (Qmult_assoc c d (/ d)), (Qmult_inv_r d Hd0).
    rewrite Qmult_1_r, (Qmult_comm a c). reflexivity. }
  assert (XL : (c * a * / (c * d) * (c * d)) * / (c * d)
               == c * a * / (c * d)).
  { rewrite <- Qmult_assoc, (Qmult_inv_r (c * d) Hcd), Qmult_1_r. reflexivity. }
  assert (XR : (a * / d * (c * d)) * / (c * d) == a * / d).
  { rewrite <- Qmult_assoc, (Qmult_inv_r (c * d) Hcd), Qmult_1_r. reflexivity. }
  assert (EY : (c * a * / (c * d) * (c * d)) * / (c * d)
               == (a * / d * (c * d)) * / (c * d)).
  { rewrite EL, ER. reflexivity. }
  apply (Qeq_trans _ (c * a * / (c * d))).
  - rewrite Qmult_assoc. reflexivity.
  - apply (Qeq_trans _ ((a * / d * (c * d)) * / (c * d))).
    + rewrite <- EY, EL. reflexivity.
    + exact XR.
Qed. 
Lemma lw0_pitS_div_lt_one : forall x y : Q, QltT 0 y -> QltT x y -> QltT (x / y) 1.
Proof.
  intros x y Hy0 Hxy.
  assert (Hy : ~ (y == 0)) by (exact (lw0_pitS_qne0_of_pos y Hy0)).
  apply Qlt_to_QltT. rewrite <- (Qmult_inv_r y Hy).
  apply Qmult_lt_compat_r.
  - apply Qinv_lt_0_compat. apply QltT_to_Qlt. exact Hy0.
  - apply QltT_to_Qlt. exact Hxy.
Qed. 
Lemma lw0_pitS_pow_dec_helper : forall (x : Q) (t : nat),
  QleT' 0 x -> QleT' x 1 -> QleT' (q_pow x (Datatypes.S t)) (q_pow x t).
Proof.
  intros x t H0 H1.
  apply (qleT'_trans _ (x * q_pow x t)%Q).
  - apply qeq_leT'. apply q_pow_succ.
  - apply (qleT'_trans _ (1 * q_pow x t)%Q).
    + apply Qle_to_QleT'. apply Qmult_le_compat_r.
      * exact (QleT'_to_Qle _ _ H1).
      * apply q_pow_nonneg. exact (QleT'_to_Qle _ _ H0).
    + apply qeq_leT'. rewrite Qmult_1_l. reflexivity.
Qed. 
Lemma lw0_pitS_pow_le_base : forall (x : Q) (n : nat),
  QleT' 0 x -> QleT' x 1 -> (1 <= n)%nat -> QleT' (q_pow x n) x.
Proof.
  intros x n H0 H1 Hn.
  assert (Haux : forall t : nat, QleT' (q_pow x (Datatypes.S t)) x).
  { intro t. induction t as [|t IH].
    - cbn [q_pow]. apply Qle_to_QleT'.
      rewrite Qmult_1_r. apply Qle_refl.
    - apply (qleT'_trans _ (q_pow x (Datatypes.S t))).
      + apply lw0_pitS_pow_dec_helper; assumption.
      + exact IH. }
  destruct n as [|n']; [ exfalso; exact (Nat.nle_succ_0 0 Hn) | apply Haux ].
Qed. 
Lemma lw0_pitS_Wbn0_scale_eq : forall (b q : Q) (n : nat),
  q_fact n * lw0_Wb b q n 0 ==
  q_pow b n * q_pow q (2 * n + 2) * q_fact (n + 1) / q_fact (2 * n + 2).
Proof.
  intros b q n. unfold lw0_Wb, Qdiv.
  replace (n + 2 * 0 + 1)%nat with (Datatypes.S n) by ring.
  replace (2 * n + 2 * 0 + 2)%nat with (Datatypes.S (Datatypes.S (2 * n))) by ring.
  replace (2 * 0 + 1)%nat with 1%nat by ring.
  replace (2 * n + 2)%nat with (Datatypes.S (Datatypes.S (2 * n))) by ring.
  replace (n + 1)%nat with (Datatypes.S n) by ring.
  assert (E1 : q_fact 1%nat == 1%Q) by reflexivity.
  rewrite E1, Qmult_1_r.
  apply (lw0_pitS_qmul_div_cancel (q_fact n)).
  - exact (lw0_q_fact_ne0 n).
  - apply lw0_pitS_qne0_of_pos. apply Qlt_to_QltT. apply q_fact_pos.
Qed. 
Lemma lw0_q_pow_add : forall (x : Q) (m n : nat),
  q_pow x (m + n)%nat == q_pow x m * q_pow x n.
Proof.
  intros x m n. induction n as [| n IH].
  - rewrite Nat.add_0_r, Qmult_1_r. reflexivity.
  - replace (m + Datatypes.S n)%nat with (Datatypes.S (m + n))%nat by ring.
    rewrite !q_pow_succ, IH. ring.
Qed. 
Lemma lw0_pitS_w0n_core : forall (b q : Q) (d n : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3) -> QleT' b (lw0_q_of_nat d) ->
  (22 + 2 * (10 * d) <= n)%nat ->
  QltT (q_fact n * lw0_Wb b q n 0) 1.
Proof.
  intros b q d n Hb Hq0 Hq103 Hbd Hn.
  assert (Hd1 : (1 <= d)%nat).
  { destruct d as [|d'].
    - exfalso.
      assert (Hz : QltT 0 (lw0_q_of_nat 0))
        by (apply (lw0_ltT_leT_trans 0 b (lw0_q_of_nat 0) Hb Hbd)).
      cbn [lw0_q_of_nat] in Hz. unfold QltT, Qlt_bool in Hz.
      cbn in Hz. inversion Hz.
    - apply le_n_S. apply Nat.le_0_l. }
  assert (Hdp : QltT 0 (lw0_q_of_nat d)).
  { destruct d as [|d']; [ exfalso; exact (Nat.nle_succ_0 0 Hd1) | ].
    apply (lw0_ltT_leT_trans 0 1 (lw0_q_of_nat (Datatypes.S d'))).
    - apply Qlt_to_QltT. unfold Qlt. reflexivity.
    - apply lw0_q_of_nat_ge_one. }
  assert (Hp2 : QltT 0 (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                              (Datatypes.S n))).
  { apply lw0_q_pow_pos.
    apply (lw0_ltT_leT_trans 0 1 (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
    - apply Qlt_to_QltT. unfold Qlt. reflexivity.
    - apply lw0_q_of_nat_ge_one. }
  assert (HRpos : QltT 0 (lw0_fact_range (Datatypes.S n) (Datatypes.S n))).
  { apply (lw0_ltT_leT_trans 0
             (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                    (Datatypes.S n)) _ Hp2
             (lw0_fact_range_ge_pow (Datatypes.S n) (Datatypes.S n))). }
  assert (Hlin : QleT' (lw0_q_of_nat d * (100 # 9))
                       ((5 # 9) * lw0_q_of_nat (n + 2))).
  { assert (E100 : ((100 # 9) * 9)%Q == 100%Q) by reflexivity.
    assert (E5x9 : ((5 # 9) * lw0_q_of_nat (n + 2) * 9)%Q
                   == (5 * lw0_q_of_nat (n + 2))%Q) by ring.
    apply (lw0_pitS_qmult_reg_r _ _ 9).
    - apply Qlt_to_QltT. unfold Qlt. reflexivity.
    - apply Qle_to_QleT'.
      apply (Qle_trans _ (lw0_q_of_nat d * 100)%Q).
      + apply QleT'_to_Qle. apply qeq_leT'. ring.
      + apply (Qle_trans _ (lw0_q_of_nat (5 * (n + 2)))).
        * apply QleT'_to_Qle.
          apply (qleT'_trans _ (lw0_q_of_nat (100 * d))).
          -- apply qeq_leT'.
             assert (Eq1 : (lw0_q_of_nat d * 100)%Q
                           == lw0_q_of_nat (100 * d)%nat).
             { rewrite (lw0_pitS_qof_mul 100 d).
               replace (lw0_q_of_nat 100)%Q with 100%Q by reflexivity.
               apply Qmult_comm. }
             exact Eq1.
          -- apply lw0_q_of_nat_le_mono.
             assert (H20 : (20 * d <= n)%nat).
             { replace (20 * d)%nat with (2 * (10 * d))%nat by ring.
               exact (Nat.le_trans (2 * (10 * d)) (22 + 2 * (10 * d)) n
                       (Nat.le_add_l (2 * (10 * d)) 22) Hn). }
             replace (100 * d)%nat with (5 * (20 * d))%nat by ring.
             exact (Nat.mul_le_mono (5) (5) (20 * d) (n + 2)
                     (Nat.le_refl 5)
                     (Nat.le_trans (20 * d) n (n + 2) H20
                       (Nat.le_add_r n 2))).
        * apply QleT'_to_Qle. apply qeq_leT'.
          assert (Eq2 : (5 * lw0_q_of_nat (n + 2))%Q
                        == lw0_q_of_nat (5 * (n + 2))%nat).
          { rewrite (lw0_pitS_qof_mul 5 (n + 2)).
            replace (lw0_q_of_nat 5)%Q with 5%Q by reflexivity.
            reflexivity. }
          symmetry in Eq2.
          assert (Eall : (lw0_q_of_nat (5 * (n + 2))
                          == (5 # 9) * lw0_q_of_nat (n + 2) * 9)%Q).
          { apply (Qeq_trans _ (5 * lw0_q_of_nat (n + 2))%Q).
            - exact Eq2.
            - symmetry. exact E5x9. }
          exact Eall. }
  replace (n + 2)%nat with (Datatypes.S (Datatypes.S n))%nat in Hlin by ring.
  assert (H509 : QleT' 0 (5 # 9))
    by exact (@id_refl bool true).
  assert (H511 : QleT' (5 # 9) 1)
    by exact (@id_refl bool true).
  assert (Hp : QleT' 0 (lw0_q_of_nat d * (100 # 9))%Q).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ (0 * (100 # 9))%Q).
    - rewrite Qmult_0_l. apply Qle_refl.
    - apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg d)).
      + apply QleT'_to_Qle. exact (@id_refl bool true). }
  assert (Hmono : QleT' (q_pow (lw0_q_of_nat d * (100 # 9)) n)
                        (q_pow ((5 # 9) * lw0_q_of_nat
                                  (Datatypes.S (Datatypes.S n))) n))
    by (apply lw0_q_pow_mono_base; [ exact Hp | exact Hlin ]).
  assert (Pform : (q_pow (10 / 3) (Datatypes.S n + Datatypes.S n)
                   == (100 # 9) * q_pow (100 # 9) n)%Q).
  { rewrite (lw0_q_pow_add (10 / 3) (Datatypes.S n) (Datatypes.S n)),
      (lw0_pitS_q_pow_mul (10 / 3) (10 / 3) (Datatypes.S n)).
    replace ((10 / 3) * (10 / 3))%Q with (100 # 9)%Q by reflexivity.
    apply q_pow_succ. }
  assert (HMsucc : (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
                    * lw0_q_of_nat (Datatypes.S (Datatypes.S n))
                    == q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                             (Datatypes.S n))%Q).
  { rewrite (Qmult_comm (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
              (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
    rewrite <- (q_pow_succ (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n).
    reflexivity. }
  assert (Hqt : forall u v w : Q, u == v -> QltT w u -> QltT w v).
  { intros u v w Huv Hwu. apply Qlt_to_QltT. rewrite <- Huv.
    apply QltT_to_Qlt. exact Hwu. }
  assert (H500 : QltT (500 # 81)
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
  { apply (lw0_ltT_leT_trans (500 # 81) (lw0_q_of_nat 24) _).
    - apply Qlt_to_QltT. vm_compute. reflexivity.
    - apply lw0_q_of_nat_le_mono.
      apply (Nat.le_trans 24 ((22 + 2 * (10 * d)) + 2)
               (Datatypes.S (Datatypes.S n))).
      + apply (Nat.le_trans 24 (24 + 2 * (10 * d)) ((22 + 2 * (10 * d)) + 2)).
        * apply Nat.le_add_r.
        * replace (24 + 2 * (10 * d))%nat with ((22 + 2 * (10 * d)) + 2)%nat by ring.
          apply Nat.le_refl.
      + replace (Datatypes.S (Datatypes.S n))%nat with (n + 2)%nat by ring.
        exact (proj1 (Nat.add_le_mono_r (22 + 2 * (10 * d)) n 2) Hn). }
  assert (Hstr : QltT (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
                       * (500 # 81))%Q
                      (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                             (Datatypes.S n))).
  { apply (Hqt _ _ _ HMsucc).
    apply Qlt_to_QltT.
    rewrite (Qmult_comm (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
              (500 # 81)),
            (Qmult_comm (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n)
              (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
    apply Qmult_lt_compat_r.
    - apply QltT_to_Qlt. apply lw0_q_pow_pos.
      apply (lw0_ltT_leT_trans 0 1
               (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))).
      + apply Qlt_to_QltT. unfold Qlt. reflexivity.
      + apply lw0_q_of_nat_ge_one.
    - apply QltT_to_Qlt. exact H500. }
  assert (Hbig : QleT' (q_pow (lw0_q_of_nat d) n
                        * ((100 # 9) * q_pow (100 # 9) n))%Q
                       (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
                        * (500 # 81))%Q).
  { apply (qleT'_trans _
      (q_pow (lw0_q_of_nat d * (100 # 9)) n * (100 # 9))%Q).
    - apply qeq_leT'.
      rewrite <- (lw0_pitS_q_pow_mul (lw0_q_of_nat d) (100 # 9) n). ring.
    - apply (qleT'_trans _
        (q_pow ((5 # 9) * lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
         * (100 # 9))%Q).
      + apply Qle_to_QleT'. apply Qmult_le_compat_r.
        * exact (QleT'_to_Qle _ _ Hmono).
        * apply QleT'_to_Qle. exact (@id_refl bool true).
      + apply (qleT'_trans _
          (q_pow (5 # 9) n
           * q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
           * (100 # 9))%Q).
        * apply qeq_leT'.
          rewrite (lw0_pitS_q_pow_mul (5 # 9)
                    (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n).
          reflexivity.
        * apply (qleT'_trans _
            (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
             * (q_pow (5 # 9) n * (100 # 9)))%Q).
          -- apply qeq_leT'. ring.
          -- apply (qleT'_trans _
              (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
               * ((5 # 9) * (100 # 9)))%Q).
            ++ apply Qle_to_QleT'.
               rewrite (Qmult_comm (q_pow (lw0_q_of_nat
                                            (Datatypes.S (Datatypes.S n))) n)
                         (q_pow (5 # 9) n * (100 # 9))),
                       (Qmult_comm (q_pow (lw0_q_of_nat
                                            (Datatypes.S (Datatypes.S n))) n)
                         ((5 # 9) * (100 # 9))).
               apply Qmult_le_compat_r.
               ** apply Qmult_le_compat_r.
                  assert (Hn1 : (1 <= n)%nat).
                  { replace (22 + 2 * (10 * d))%nat
                      with (1 + (21 + 2 * (10 * d)))%nat by ring.
                    exact (Nat.le_trans 1 (1 + (21 + 2 * (10 * d))) n
                            (Nat.le_add_r 1 (21 + 2 * (10 * d))) Hn). }
                  --- exact (QleT'_to_Qle _ _
                        (lw0_pitS_pow_le_base (5 # 9) n H509 H511 Hn1)).
                  --- apply QleT'_to_Qle. exact (@id_refl bool true).
               ** exact (QleT'_to_Qle _ _
                          (lw0_q_pow_nonnegT (lw0_q_of_nat
                            (Datatypes.S (Datatypes.S n))) n
                            (lw0_q_of_nat_nonneg
                              (Datatypes.S (Datatypes.S n))))).
            ++ apply qeq_leT'. reflexivity. }
  assert (Hb0 : QleT' 0 b)
    by (apply Qle_to_QleT'; apply (Qlt_le_weak 0); apply QltT_to_Qlt; exact Hb).
  assert (Hbpow : QleT' (q_pow b n) (q_pow (lw0_q_of_nat d) n))
    by (apply lw0_q_pow_mono_base; [ exact Hb0 | exact Hbd ]).
  assert (Hqp : QleT' (q_pow q (Datatypes.S n + Datatypes.S n))
                      (q_pow (10 / 3) (Datatypes.S n + Datatypes.S n)))
    by (apply lw0_q_pow_mono_base; [ exact Hq0 | exact Hq103 ]).
  assert (Hprod : QleT' (q_pow b n * q_pow q (Datatypes.S n + Datatypes.S n))%Q
                        (q_pow (lw0_q_of_nat d) n
                         * q_pow (10 / 3) (Datatypes.S n + Datatypes.S n))%Q).
  { apply (qleT'_trans _ (q_pow (lw0_q_of_nat d) n
                          * q_pow q (Datatypes.S n + Datatypes.S n))%Q).
    - apply Qle_to_QleT'. apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ Hbpow).
      + apply q_pow_nonneg. exact (QleT'_to_Qle _ _ Hq0).
    - apply Qle_to_QleT'.
      rewrite (Qmult_comm (q_pow (lw0_q_of_nat d) n)
                (q_pow q (Datatypes.S n + Datatypes.S n))),
              (Qmult_comm (q_pow (lw0_q_of_nat d) n)
                (q_pow (10 / 3) (Datatypes.S n + Datatypes.S n))).
      apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ Hqp).
      + apply q_pow_nonneg.
        exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg d)). }
  apply Qlt_to_QltT. rewrite lw0_pitS_Wbn0_scale_eq.
  replace (2 * n + 2)%nat with (Datatypes.S n + Datatypes.S n)%nat by ring.
  replace (n + 1)%nat with (Datatypes.S n)%nat by ring.
  rewrite lw0_q_fact_split.
  apply QltT_to_Qlt.
  apply (lw0_leT'_ltT_trans _
    (q_pow (lw0_q_of_nat d) n * q_pow (10 / 3) (Datatypes.S n + Datatypes.S n)
     / q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
             (Datatypes.S n))%Q).
  - apply Qle_to_QleT'. unfold Qdiv.
    replace (10 * / 3)%Q with (10 / 3)%Q by reflexivity.
    rewrite <- (Qmult_assoc (q_pow b n * q_pow q (Datatypes.S n + Datatypes.S n))
              (q_fact (Datatypes.S n))
              (/ (q_fact (Datatypes.S n)
                  * lw0_fact_range (Datatypes.S n) (Datatypes.S n)))).
    rewrite (Qinv_mult_distr (q_fact (Datatypes.S n))
              (lw0_fact_range (Datatypes.S n) (Datatypes.S n))).
    rewrite (Qmult_assoc (q_fact (Datatypes.S n)) (/ (q_fact (Datatypes.S n)))
              (/ (lw0_fact_range (Datatypes.S n) (Datatypes.S n)))).
    rewrite (Qmult_inv_r (q_fact (Datatypes.S n))
              (lw0_q_fact_ne0 (Datatypes.S n))).
    rewrite Qmult_1_l.
    apply Qmult_le_compat_nonneg.
    + split.
      * exact (QleT'_to_Qle _ _
                (lw0_qmul_le0T (q_pow b n)
                  (q_pow q (Datatypes.S n + Datatypes.S n))
                  (lw0_q_pow_nonnegT b n Hb0)
                  (lw0_q_pow_nonnegT q (Datatypes.S n + Datatypes.S n) Hq0))).
      * exact (QleT'_to_Qle _ _ Hprod).
    + split.
      * apply (Qlt_le_weak 0). apply Qinv_lt_0_compat.
        apply QltT_to_Qlt. exact HRpos.
      * apply QleT'_to_Qle.
        exact (lw0_inv_le (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n)))
                            (Datatypes.S n))
                (lw0_fact_range (Datatypes.S n) (Datatypes.S n))
                Hp2 HRpos
                (lw0_fact_range_ge_pow (Datatypes.S n) (Datatypes.S n))).
  - apply lw0_pitS_div_lt_one.
    + exact Hp2.
    + apply (lw0_leT'_ltT_trans _
        (q_pow (lw0_q_of_nat d) n
         * ((100 # 9) * q_pow (100 # 9) n))%Q).
      * apply qeq_leT'. rewrite Pform. reflexivity.
      * apply (lw0_leT'_ltT_trans _
          (q_pow (lw0_q_of_nat (Datatypes.S (Datatypes.S n))) n
           * (500 # 81))%Q).
        -- exact Hbig.
        -- exact Hstr.
Qed. 
Lemma lw0_pi_w0n_lt1 : forall (b q : Q) (d k : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3) -> QleT' b (lw0_q_of_nat d) ->
  QltT (q_fact (lw0_n_select (10 * d) k)
        * lw0_Wb b q (lw0_n_select (10 * d) k) 0) 1.
Proof.
  intros b q d k H1 H2 H3 H4.
  apply (lw0_pitS_w0n_core b q d (lw0_n_select (10 * d) k) H1 H2 H3 H4).
  unfold lw0_n_select. pose proof (Nat.le_max_r k (10 * d)).
  apply Nat.add_le_mono; [ apply Nat.le_refl | ].
  replace (2 * 10 * d)%nat with (2 * (10 * d))%nat by ring.
  apply Nat.mul_le_mono; [ apply Nat.le_refl | exact H ].
Qed. (* ---- Terminal lemmas of the w0n chain (the Leibniz separation side) ---- *)

Lemma leibsep_altsum_two_shore : forall W : nat -> Q,
  (forall k : nat, QleT' 0 (W k)) ->
  (forall k : nat, QleT' (W (Datatypes.S k)) (W k)) ->
  forall m : nat,
    And (QleT' (W 0%nat - W 1%nat)%Q (altsum W (Datatypes.S m)))
        (QleT' (altsum W (Datatypes.S m)) (W 0%nat)).
Proof.
  intros W H0 Hd m.
  pose proof (lw0_altsum_add W 1%nat m) as Hadd.
  assert (Eidx : (1 + m)%nat = Datatypes.S m) by reflexivity.
  rewrite Eidx in Hadd.
  assert (E01 : altsum W 1%nat == W 0%nat)
    by (cbn [altsum altsum_acc altsum_sgp]; now rewrite Qplus_0_r).
  assert (Esgp : altsum_sgp 1%nat = false) by reflexivity.
  rewrite Esgp in Hadd.
  destruct (lw0_acc_quad W H0 Hd m 1%nat) as [Q1 [Q2 [Q3 Q4]]].
  split.
  - apply (qleT'_trans (W 0%nat - W 1%nat)%Q
                       (W 0%nat + Qopp (W 1%nat))%Q
                       (altsum W (Datatypes.S m))).
    + apply qeq_leT'. ring.
    + apply (qleT'_trans (W 0%nat + Qopp (W 1%nat))%Q
                         (W 0%nat + altsum_acc false W 1%nat m)%Q
                         (altsum W (Datatypes.S m))).
      * apply qleT'_plus_compat; [apply qleT'_refl | exact Q4].
      * apply qeq_leT'. rewrite Hadd, E01. ring.
  - apply (qleT'_trans (altsum W (Datatypes.S m))
                       (W 0%nat + altsum_acc false W 1%nat m)%Q
                       (W 0%nat)).
    + apply qeq_leT'. rewrite Hadd, E01. reflexivity.
    + apply (qleT'_trans (W 0%nat + altsum_acc false W 1%nat m)%Q
                         (W 0%nat + 0)%Q (W 0%nat)).
      * apply qleT'_plus_compat; [apply qleT'_refl | exact Q3].
      * apply qeq_leT'. ring.
Qed. 
Lemma leibsep_w0n_xfer : forall A B C D : Q,
  Qlt 0 C -> Qlt 0 D ->
  QleT' (A * D) (B * C) ->
  QleT' (A * / C) (B * / D).
Proof.
  intros A B C D HC HD H.
  assert (Hpos : QltT 0 (C * D)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - exact HC.
    - exact HD. }
  assert (Hbr1 : ((A * / C) * (C * D))%Q == A * D).
  { transitivity ((A * (C * / C)) * D)%Q.
    - ring.
    - rewrite (Qmult_inv_r C (lw0_pitS_qne0_of_pos C (Qlt_to_QltT 0 C HC))). ring. }
  assert (Hbr3 : ((B * / D) * (C * D))%Q == B * C).
  { transitivity ((B * (D * / D)) * C)%Q.
    - ring.
    - rewrite (Qmult_inv_r D (lw0_pitS_qne0_of_pos D (Qlt_to_QltT 0 D HD))). ring. }
  apply (lw0_pitS_qmult_reg_r (A * / C) (B * / D) (C * D) Hpos).
  apply Qle_to_QleT'.
  apply (Qle_trans ((A * / C) * (C * D))%Q (A * D)%Q ((B * / D) * (C * D))%Q).
  - apply leibsep_qeq_le. exact Hbr1.
  - apply (Qle_trans (A * D)%Q (B * C)%Q ((B * / D) * (C * D))%Q).
    + exact (QleT'_to_Qle _ _ H).
    + apply leibsep_qeq_le. exact (Qeq_sym _ _ Hbr3).
Qed. 
Lemma leibsep_w0n_step : forall (b q : Q) (d n : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3)%Q -> QleT' b (lw0_q_of_nat d) ->
  (20 * d <= n)%nat ->
  QleT' (q_fact (Datatypes.S n) * lw0_Wb b q (Datatypes.S n) 0)%Q
        ((1 # 5) * (q_fact n * lw0_Wb b q n 0))%Q.
Proof.
  intros b q d n Hb Hq0 Hq103 Hbd Hn.
  unfold lw0_Wb.
  replace (2 * Datatypes.S n + 2 * 0 + 2)%nat
    with (Datatypes.S (Datatypes.S (2 * n + 2)))%nat by ring.
  replace (Datatypes.S n + 2 * 0 + 1)%nat
    with (Datatypes.S (Datatypes.S n))%nat by ring.
  replace (2 * n + 2 * 0 + 2)%nat with (2 * n + 2)%nat by ring.
  replace (n + 2 * 0 + 1)%nat with (Datatypes.S n)%nat by ring.
  replace (2 * 0 + 1)%nat with 1%nat by ring.
  assert (E1009 : ((10 / 3) * (10 / 3))%Q == (100 # 9)%Q) by reflexivity.
  assert (En2 : (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                == lw0_q_of_nat (Datatypes.S (Datatypes.S n))) by reflexivity.
  assert (Ed : (Z.of_nat d # 1) == lw0_q_of_nat d) by reflexivity.
  assert (En4 : (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                == lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * n + 2)))) by reflexivity.
  assert (En3 : (Z.of_nat (Datatypes.S (2 * n + 2)) # 1)
                == lw0_q_of_nat (Datatypes.S (2 * n + 2))) by reflexivity.
  assert (Enat : (9 * Datatypes.S (Datatypes.S (2 * n + 2)) * Datatypes.S (2 * n + 2)
                   = 18 * (2 * n + 3) * Datatypes.S (Datatypes.S n))%nat) by ring.
  assert (Hqp2 : QleT' (q * q) (100 # 9)).
  { apply (qleT'_trans (q * q) (q_pow q 2) (100 # 9)).
    - apply (qeq_leT' (q * q) (q_pow q 2)).
      rewrite (q_pow_succ q 1), (q_pow_succ q 0). cbn [q_pow]. ring.
    - apply (qleT'_trans (q_pow q 2) (q_pow (10 / 3) 2) (100 # 9)).
      + apply Qle_to_QleT'. apply q_pow_mono.
        * exact (QleT'_to_Qle _ _ Hq0).
        * exact (QleT'_to_Qle _ _ Hq103).
      + apply (qeq_leT' (q_pow (10 / 3) 2) (100 # 9)).
        rewrite (q_pow_succ (10 / 3) 1), (q_pow_succ (10 / 3) 0). cbn [q_pow].
        transitivity ((10 / 3) * (10 / 3))%Q.
        * ring.
        * exact E1009. }
  assert (HXY : QleT' (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))
                      ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9))).
  { apply (qleT'_trans
            (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))
            ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (q * q))
            ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9))).
    - apply qeq_leT'. ring.
    - apply Qle_to_QleT'.
      apply (lw0_q_mult_le_l (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)).
      + apply (Qlt_le_weak 0). apply QltT_to_Qlt.
        exact (lw0_q_of_nat_lt0T_S (Datatypes.S n)).
      + exact (QleT'_to_Qle _ _ Hqp2). }
  assert (Hl1 : QleT' (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
                      ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))).
  { apply (qleT'_trans
            (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
            (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * b)
            ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))).
    - apply qeq_leT'. ring.
    - apply (qleT'_trans
              (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * b)
              (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (Z.of_nat d # 1))
              ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))).
      + apply Qle_to_QleT'.
        apply (lw0_q_mult_le_l (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))).
        * apply Qmult_le_0_compat.
          -- apply Qmult_le_0_compat.
             ++ exact (QleT'_to_Qle _ _ Hq0).
             ++ exact (QleT'_to_Qle _ _ Hq0).
          -- apply (Qlt_le_weak 0). apply QltT_to_Qlt.
             exact (lw0_q_of_nat_lt0T_S (Datatypes.S n)).
        * exact (QleT'_to_Qle _ _ Hbd).
      + apply qeq_leT'. ring. }
  assert (Hl2 : QleT' ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
                      ((Z.of_nat d # 1)
                       * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)))).
  { apply Qle_to_QleT'.
    apply (lw0_q_mult_le_l (Z.of_nat d # 1)).
    - exact (QleT'_to_Qle _ _ (lw0_q_of_nat_nonneg d)).
    - exact (QleT'_to_Qle _ _ HXY). }
  assert (E500 : 500%Q == lw0_q_of_nat 500) by reflexivity.
  assert (Hbr500 : ((Z.of_nat d # 1)
                    * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)) * 45)%Q
                   == lw0_q_of_nat (500 * d * Datatypes.S (Datatypes.S n))).
  { rewrite En2, Ed.
    transitivity ((500%Q * lw0_q_of_nat d)
                  * lw0_q_of_nat (Datatypes.S (Datatypes.S n)))%Q.
    - ring.
    - rewrite E500.
      rewrite <- (lw0_pitS_qof_mul 500 d).
      rewrite <- (lw0_pitS_qof_mul (500 * d) (Datatypes.S (Datatypes.S n))).
      reflexivity. }
  assert (E9 : 9%Q == lw0_q_of_nat 9) by reflexivity.
  assert (Hbr45 : (((1 # 5) * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                              * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))) * 45)%Q
                  == lw0_q_of_nat (9 * Datatypes.S (Datatypes.S (2 * n + 2))
                                   * Datatypes.S (2 * n + 2)))).
  { rewrite En4, En3.
    transitivity (9%Q * (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * n + 2)))
                         * lw0_q_of_nat (Datatypes.S (2 * n + 2))))%Q.
    - ring.
    - rewrite E9.
      rewrite <- (lw0_pitS_qof_mul (Datatypes.S (Datatypes.S (2 * n + 2)))
                   (Datatypes.S (2 * n + 2))).
      rewrite <- (lw0_pitS_qof_mul 9
                   (Datatypes.S (Datatypes.S (2 * n + 2)) * Datatypes.S (2 * n + 2))).
      replace (9 * (Datatypes.S (Datatypes.S (2 * n + 2)) * Datatypes.S (2 * n + 2)))%nat
        with (9 * Datatypes.S (Datatypes.S (2 * n + 2)) * Datatypes.S (2 * n + 2))%nat
        by ring.
      reflexivity. }
  assert (Hl3 : QleT' ((Z.of_nat d # 1)
                       * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)))
                      ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                                   * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))).
  { apply (lw0_pitS_qmult_reg_r
             ((Z.of_nat d # 1)
              * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)))
             ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                         * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))) 45%Q).
    - apply Qlt_to_QltT. unfold Qlt. reflexivity.
    - apply Qle_to_QleT'.
      apply (Qle_trans
              (((Z.of_nat d # 1)
                * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9))) * 45)%Q
              (lw0_q_of_nat (500 * d * Datatypes.S (Datatypes.S n)))
              (((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                             * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))) * 45)%Q).
      + apply leibsep_qeq_le. exact Hbr500.
      + apply (Qle_trans
                (lw0_q_of_nat (500 * d * Datatypes.S (Datatypes.S n)))
                (lw0_q_of_nat (9 * Datatypes.S (Datatypes.S (2 * n + 2))
                               * Datatypes.S (2 * n + 2)))
                (((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                             * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))) * 45)%Q).
        * assert (Hmono : QleT' (lw0_q_of_nat (500 * d * Datatypes.S (Datatypes.S n)))
                                (lw0_q_of_nat (9 * Datatypes.S (Datatypes.S (2 * n + 2))
                                               * Datatypes.S (2 * n + 2)))).
          { apply lw0_q_of_nat_le_mono.
            rewrite Enat.
            apply (Nat.le_trans _ (25 * n * Datatypes.S (Datatypes.S n)) _).
            -- apply Nat.mul_le_mono.
               ++ replace (500 * d)%nat with (25 * (20 * d))%nat by ring.
                  apply Nat.mul_le_mono; [ apply Nat.le_refl | exact Hn ].
               ++ apply Nat.le_refl.
            -- apply Nat.mul_le_mono.
               ++ replace (18 * (2 * n + 3))%nat with (25 * n + (11 * n + 54))%nat by ring.
                  exact (Nat.le_add_r (25 * n) (11 * n + 54)).
               ++ apply Nat.le_refl. }
          exact (QleT'_to_Qle _ _ Hmono).
        * apply leibsep_qeq_le. exact (Qeq_sym _ _ Hbr45). }
  assert (Hheart : QleT' (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
                         ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                                     * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))).
  { apply (qleT'_trans
            (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
            ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
            ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                        * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))).
    - exact Hl1.
    - apply (qleT'_trans
              ((Z.of_nat d # 1) * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))
              ((Z.of_nat d # 1)
               * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * (100 # 9)))
              ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                          * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))).
      + exact Hl2.
      + exact Hl3. }
  assert (HheartS : QleT'
    (q_fact (Datatypes.S n)
     * (q_fact (Datatypes.S n) * (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)))))
    (q_fact (Datatypes.S n)
     * (q_fact (Datatypes.S n)
         * ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                       * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1)))))).
  { apply Qle_to_QleT'.
    apply (lw0_q_mult_le_l (q_fact (Datatypes.S n))).
    - apply Qlt_le_weak. apply q_fact_pos.
    - apply (lw0_q_mult_le_l (q_fact (Datatypes.S n))).
      + apply Qlt_le_weak. apply q_fact_pos.
      + exact (QleT'_to_Qle _ _ Hheart). }
  assert (Hcommon : Qle 0
    (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2)))))).
  { apply Qmult_le_0_compat.
    - apply q_pow_nonneg. apply (Qlt_le_weak 0). apply QltT_to_Qlt. exact Hb.
    - apply Qmult_le_0_compat.
      + apply q_pow_nonneg. exact (QleT'_to_Qle _ _ Hq0).
      + apply Qmult_le_0_compat.
        * apply Qlt_le_weak. apply q_fact_pos.
        * apply Qmult_le_0_compat.
          -- apply Qlt_le_weak. apply q_fact_pos.
          -- apply Qlt_le_weak. apply q_fact_pos. }
  assert (HheartC : QleT'
    (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
     * (q_fact (Datatypes.S n)
         * (q_fact (Datatypes.S n)
             * (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))))))
    (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
     * (q_fact (Datatypes.S n)
         * (q_fact (Datatypes.S n)
             * ((1 # 5) * (Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                           * ((Z.of_nat (Datatypes.S (2 * n + 2)) # 1))))))).
  { apply Qle_to_QleT'.
    apply (lw0_q_mult_le_l
            (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2)))))).
    - exact Hcommon.
    - exact (QleT'_to_Qle _ _ HheartS). }
  assert (Hprem : QleT'
    ((q_fact (Datatypes.S n)
      * ((b * q_pow b n)
         * (q * (q * q_pow q (2 * n + 2))
             * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n)))))
     * (q_fact n * q_fact 1 * q_fact (2 * n + 2)))
    ((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n))))
     * (q_fact (Datatypes.S n) * q_fact 1
               * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))).
  { apply (qleT'_trans
            ((q_fact (Datatypes.S n)
              * ((b * q_pow b n)
                 * (q * (q * q_pow q (2 * n + 2))
                     * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                        * q_fact (Datatypes.S n)))))
             * (q_fact n * q_fact 1 * q_fact (2 * n + 2)))
            (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
             * (q_fact (Datatypes.S n)
                 * (q_fact (Datatypes.S n)
                     * (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))))))
            ((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n))))
             * (q_fact (Datatypes.S n) * q_fact 1
                       * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))).
    - apply qeq_leT'. ring.
    - apply (qleT'_trans
              (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
               * (q_fact (Datatypes.S n)
                   * (q_fact (Datatypes.S n)
                       * (b * (q * q * (Z.of_nat (Datatypes.S (Datatypes.S n)) # 1))))))
              (q_pow b n * (q_pow q (2 * n + 2) * (q_fact n * (q_fact 1 * q_fact (2 * n + 2))))
               * (q_fact (Datatypes.S n)
                   * (q_fact (Datatypes.S n)
                       * ((1 # 5) * ((Z.of_nat (Datatypes.S (Datatypes.S (2 * n + 2))) # 1)
                                     * (Z.of_nat (Datatypes.S (2 * n + 2)) # 1))))))
              ((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n))))
               * (q_fact (Datatypes.S n) * q_fact 1
                         * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))).
      + exact HheartC.
      + apply qeq_leT'.
        rewrite (q_fact_succ (Datatypes.S (2 * n + 2))), (q_fact_succ (2 * n + 2)).
        ring. }
  assert (Hdso : Qlt 0 (q_fact (Datatypes.S n) * q_fact 1
                         * q_fact (Datatypes.S (Datatypes.S (2 * n + 2))))).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat.
      + apply q_fact_pos.
      + apply q_fact_pos.
    - apply q_fact_pos. }
  assert (Hdno : Qlt 0 (q_fact n * q_fact 1 * q_fact (2 * n + 2))).
  { apply Qmult_lt_0_compat.
    - apply Qmult_lt_0_compat.
      + apply q_fact_pos.
      + apply q_fact_pos.
    - apply q_fact_pos. }
  apply (qleT'_trans
          (q_fact (Datatypes.S n)
           * (q_pow b (Datatypes.S n)
              * q_pow q (Datatypes.S (Datatypes.S (2 * n + 2)))
              * q_fact (Datatypes.S (Datatypes.S n))
              / (q_fact (Datatypes.S n) * q_fact 1
                 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2))))))
          ((q_fact (Datatypes.S n)
            * ((b * q_pow b n)
               * (q * (q * q_pow q (2 * n + 2))
                   * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1)
                      * q_fact (Datatypes.S n)))))
           / (q_fact (Datatypes.S n) * q_fact 1
              * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))
          ((1 # 5) * (q_fact n
                      * (q_pow b n * q_pow q (2 * n + 2) * q_fact (Datatypes.S n)
                         / (q_fact n * q_fact 1 * q_fact (2 * n + 2)))))).
  - apply qeq_leT'.
    unfold Qdiv.
    rewrite (q_pow_succ b n), (q_pow_succ q (Datatypes.S (2 * n + 2))),
            (q_pow_succ q (2 * n + 2)), (q_fact_succ (Datatypes.S n)).
    ring.
  - apply (qleT'_trans
            ((q_fact (Datatypes.S n) * ((b * q_pow b n) * (q * (q * q_pow q (2 * n + 2)) * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n))))) / (q_fact (Datatypes.S n) * q_fact 1 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))
            ((q_fact (Datatypes.S n) * ((b * q_pow b n) * (q * (q * q_pow q (2 * n + 2)) * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n))))) * / (q_fact (Datatypes.S n) * q_fact 1 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))
            ((1 # 5) * (q_fact n * (q_pow b n * q_pow q (2 * n + 2) * q_fact (Datatypes.S n) / (q_fact n * q_fact 1 * q_fact (2 * n + 2)))))).
    + apply qeq_leT'.
      unfold Qdiv.
      ring.
    + apply (qleT'_trans
              ((q_fact (Datatypes.S n) * ((b * q_pow b n) * (q * (q * q_pow q (2 * n + 2)) * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n))))) * / (q_fact (Datatypes.S n) * q_fact 1 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2)))))
              (((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n))))) * / (q_fact n * q_fact 1 * q_fact (2 * n + 2)))
              ((1 # 5) * (q_fact n * (q_pow b n * q_pow q (2 * n + 2) * q_fact (Datatypes.S n) / (q_fact n * q_fact 1 * q_fact (2 * n + 2)))))).
      * exact (leibsep_w0n_xfer
                 (q_fact (Datatypes.S n) * ((b * q_pow b n) * (q * (q * q_pow q (2 * n + 2)) * ((Z.of_nat (Datatypes.S (Datatypes.S n)) # 1) * q_fact (Datatypes.S n)))))
                 ((1 # 5) * (q_fact n * (q_pow b n * (q_pow q (2 * n + 2) * q_fact (Datatypes.S n)))))
                 (q_fact (Datatypes.S n) * q_fact 1 * q_fact (Datatypes.S (Datatypes.S (2 * n + 2))))
                 (q_fact n * q_fact 1 * q_fact (2 * n + 2))
                 Hdso Hdno Hprem).
      * apply qeq_leT'. unfold Qdiv. ring.
Qed. 
Lemma leibsep_w0n_pow : forall (b q : Q) (d n j : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3)%Q -> QleT' b (lw0_q_of_nat d) ->
  (20 * d <= n)%nat ->
  QleT' (q_fact (n + j) * lw0_Wb b q (n + j) 0)%Q
        (q_pow (1 # 5) j * (q_fact n * lw0_Wb b q n 0))%Q.
Proof.
  intros b q d n j Hb Hq0 Hq103 Hbd Hn.
  induction j as [| j IH].
  - replace (n + 0)%nat with n%nat by ring.
    apply (qeq_leT' (q_fact n * lw0_Wb b q n 0)
                    (q_pow (1 # 5) 0 * (q_fact n * lw0_Wb b q n 0))).
    cbn [q_pow]. ring.
  - replace (n + Datatypes.S j)%nat with (Datatypes.S (n + j))%nat by ring.
    apply (qleT'_trans
            (q_fact (Datatypes.S (n + j)) * lw0_Wb b q (Datatypes.S (n + j)) 0)
            ((1 # 5) * (q_fact (n + j) * lw0_Wb b q (n + j) 0))
            (q_pow (1 # 5) (Datatypes.S j) * (q_fact n * lw0_Wb b q n 0))).
    + apply (leibsep_w0n_step b q d (n + j) Hb Hq0 Hq103 Hbd
               (Nat.le_trans (20 * d) n (n + j) Hn (Nat.le_add_r n j))).
    + apply (qleT'_trans
              ((1 # 5) * (q_fact (n + j) * lw0_Wb b q (n + j) 0))
              ((1 # 5) * (q_pow (1 # 5) j * (q_fact n * lw0_Wb b q n 0)))
              (q_pow (1 # 5) (Datatypes.S j) * (q_fact n * lw0_Wb b q n 0))).
      * apply Qle_to_QleT'.
        apply (lw0_q_mult_le_l (1 # 5)%Q).
        -- unfold Qle. cbn [Qnum Qden]. red. intros Hc. discriminate Hc.
        -- exact (QleT'_to_Qle _ _ IH).
      * apply qeq_leT'.
        rewrite (q_pow_succ (1 # 5) j). ring.
Qed. 
Lemma leibsep_w0n_half : forall (b q : Q) (d k j : nat),
  QltT 0 b -> QleT' 0 q -> QleT' q (10 / 3)%Q -> QleT' b (lw0_q_of_nat d) ->
  (1 <= j)%nat ->
  QltT (q_fact (lw0_n_select (10 * d) k + j)
        * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)%Q (1 # 2)%Q.
Proof.
  intros b q d k j Hb Hq0 Hq103 Hbd Hj.
  assert (Hn0 : (20 * d <= lw0_n_select (10 * d) k)%nat).
  { unfold lw0_n_select. pose proof (Nat.le_max_r k (10 * d)) as Hmx.
    replace (20 * d)%nat with (2 * (10 * d))%nat by ring.
    apply (Nat.le_trans (2 * (10 * d)) (2 * Nat.max k (10 * d))
            (22 + 2 * Nat.max k (10 * d))).
    - apply Nat.mul_le_mono; [ apply Nat.le_refl | exact Hmx ].
    - apply Nat.le_add_l. }
  assert (Hlt1 : QltT (q_fact (lw0_n_select (10 * d) k)
                       * lw0_Wb b q (lw0_n_select (10 * d) k) 0) 1).
  { exact (lw0_pi_w0n_lt1 b q d k Hb Hq0 Hq103 Hbd). }
  assert (Hle1 : QleT' (q_fact (lw0_n_select (10 * d) k)
                        * lw0_Wb b q (lw0_n_select (10 * d) k) 0) 1).
  { apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hlt1. }
  assert (Hpow : QleT' (q_fact (lw0_n_select (10 * d) k + j)
                        * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)
                       (q_pow (1 # 5) j
                        * (q_fact (lw0_n_select (10 * d) k)
                           * lw0_Wb b q (lw0_n_select (10 * d) k) 0))).
  { exact (leibsep_w0n_pow b q d (lw0_n_select (10 * d) k) j Hb Hq0 Hq103 Hbd Hn0). }
  assert (Hscal : QleT' (q_pow (1 # 5) j
                         * (q_fact (lw0_n_select (10 * d) k)
                            * lw0_Wb b q (lw0_n_select (10 * d) k) 0))
                        (q_pow (1 # 5) j * 1%Q)).
  { apply Qle_to_QleT'.
    apply (lw0_q_mult_le_l (q_pow (1 # 5) j)).
    - apply q_pow_nonneg. unfold Qle. cbn [Qnum Qden]. red. intros Hc. discriminate Hc.
    - exact (QleT'_to_Qle _ _ Hle1). }
  assert (Htail : QleT' (q_pow (1 # 5) j) (1 # 5)).
  { destruct j as [| m].
    - exfalso. exact (Nat.nle_succ_0 0 Hj).
    - apply (qleT'_trans (q_pow (1 # 5) (Datatypes.S m))
                         ((1 # 5) * q_pow (1 # 5) m)
                         (1 # 5)%Q).
      + apply (qeq_leT' (q_pow (1 # 5) (Datatypes.S m))
                        ((1 # 5) * q_pow (1 # 5) m)).
        rewrite (q_pow_succ (1 # 5) m). reflexivity.
      + apply (qleT'_trans ((1 # 5) * q_pow (1 # 5) m) ((1 # 5) * 1%Q) (1 # 5)%Q).
        * apply Qle_to_QleT'.
          apply (lw0_q_mult_le_l (1 # 5)%Q).
          -- unfold Qle. cbn [Qnum Qden]. red. intros Hc. discriminate Hc.
          -- apply (Qle_trans (q_pow (1 # 5) m) (q_pow 1 m) 1).
             ++ apply (q_pow_mono (1 # 5) 1 m).
                ** unfold Qle. cbn [Qnum Qden]. red. intros Hc. discriminate Hc.
                ** unfold Qle. cbn [Qnum Qden]. red. intros Hc. discriminate Hc.
             ++ rewrite (sc_q_pow_one m). apply Qle_refl.
        * apply qeq_leT'. ring. }
  apply (lw0_leT'_ltT_trans
          (q_fact (lw0_n_select (10 * d) k + j)
           * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)
          (q_pow (1 # 5) j) (1 # 2)).
  - apply (qleT'_trans
            (q_fact (lw0_n_select (10 * d) k + j)
             * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)
            (q_pow (1 # 5) j * 1%Q)
            (q_pow (1 # 5) j)).
    + apply (qleT'_trans
              (q_fact (lw0_n_select (10 * d) k + j)
               * lw0_Wb b q (lw0_n_select (10 * d) k + j) 0)
              (q_pow (1 # 5) j
               * (q_fact (lw0_n_select (10 * d) k)
                  * lw0_Wb b q (lw0_n_select (10 * d) k) 0))
              (q_pow (1 # 5) j * 1%Q)).
      * exact Hpow.
      * exact Hscal.
    + apply qeq_leT'. ring.
  - apply (lw0_leT'_ltT_trans (q_pow (1 # 5) j) (1 # 5) (1 # 2) Htail).
    apply Qlt_to_QltT. unfold Qlt. reflexivity.
Qed. (* ============ pitB bridge and the conv convergence mountain (the polynomial-layer pointwise identity family) ============ *)

Lemma qpoly_eval_mul : forall p q x,
  qpoly_eval (qpoly_mul p q) x == qpoly_eval p x * qpoly_eval q x.
Proof.
  induction p as [|a p IH]; intros q x.
  - simpl; ring.
  - replace (qpoly_mul (cons a p) q)
      with (qpoly_add (qpoly_scalar a q) (cons 0 (qpoly_mul p q)))
        by reflexivity.
    rewrite (qpoly_eval_add (qpoly_scalar a q) (cons 0 (qpoly_mul p q)) x).
    rewrite (qpoly_eval_scalar a q x).
    change (qpoly_eval (cons 0 (qpoly_mul p q)) x)
      with (0 + x * qpoly_eval (qpoly_mul p q) x).
    rewrite (IH q x).
    change (qpoly_eval (cons a p) x) with (a + x * qpoly_eval p x).
    ring.
Qed.

Lemma qpoly_deriv_iter_commute : forall n p,
  qpoly_deriv_iter (S n) p = qpoly_deriv_iter n (qpoly_deriv p).
Proof.
  induction n as [|n IH]; intros p.
  - reflexivity.
  - change (qpoly_deriv_iter (S (S n)) p)
      with (qpoly_deriv (qpoly_deriv_iter (S n) p)).
    rewrite (IH p).
    reflexivity.
Qed.

Lemma lw0_q_fact_ge_one : forall k : nat, QleT' 1 (q_fact k).
Proof.
  intro k. apply Qle_to_QleT'.
  induction k as [| k IH].
  - apply Qle_refl.
  - rewrite lw0_q_fact_step.
    apply Qmult_le_1_compat.
    + exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one k)).
    + exact IH.
Qed.

Lemma lw0_q_fact_step2 : forall k : nat,
  q_fact (Datatypes.S (Datatypes.S k)) ==
  lw0_q_of_nat (Datatypes.S (Datatypes.S k)) * lw0_q_of_nat (Datatypes.S k) * q_fact k.
Proof.
  intro k.
  transitivity (lw0_q_of_nat (Datatypes.S (Datatypes.S k)) *
                (lw0_q_of_nat (Datatypes.S k) * q_fact k))%Q.
  - reflexivity.
  - ring.
Qed.

Lemma lw0_q_pow_mult : forall (x y : Q) (k : nat),
  q_pow x k * q_pow y k == q_pow (x * y) k.
Proof.
  intros x y k. induction k as [| k IH].
  - reflexivity.
  - rewrite !lw0_q_pow_S.
    transitivity ((x * y) * (q_pow x k * q_pow y k))%Q.
    + ring.
    + rewrite IH. ring.
Qed.

Lemma lw0_Qabs_pos_eq : forall x : Q, QleT' 0 x -> Qabs x == x.
Proof. intros x H. apply Qabs_pos. apply QleT'_to_Qle. exact H. Qed.

Lemma lw0_q_pow_one : forall j : nat, q_pow 1%Q j == 1%Q.
Proof.
  intro j. induction j as [| j IH].
  - reflexivity.
  - rewrite lw0_q_pow_S, IH. reflexivity.
Qed.

Fixpoint qpoly_opp (p : qpoly) : qpoly :=
  match p with
  | nil => nil
  | cons a p' => cons (- a)%Q (qpoly_opp p')
  end.

Fixpoint lw0_mono (m : nat) : qpoly :=
  match m with
  | 0%nat => cons 1 nil
  | Datatypes.S m' => cons 0 (lw0_mono m')
  end.

Lemma lw0_qp_ai_mul_scalar_l : forall c f g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_scalar c f) g) k) x ==
  c * qpoly_eval (lw0_qp_ai (qpoly_mul f g) k) x.
Proof.
  intros c f.
  induction f as [|a f IH]; intros g k x.
  - change (qpoly_scalar c nil) with (@nil Q).
    change (qpoly_mul nil g) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
    ring.
  - change (qpoly_scalar c (cons a f)) with (cons (c * a) (qpoly_scalar c f)).
    change (qpoly_mul (cons (c * a) (qpoly_scalar c f)) g)
      with (qpoly_add (qpoly_scalar (c * a) g)
              (cons 0 (qpoly_mul (qpoly_scalar c f) g))).
    rewrite (lw0_qp_ai_add (qpoly_scalar (c * a) g)
               (cons 0 (qpoly_mul (qpoly_scalar c f) g)) k x).
    rewrite (lw0_qp_ai_scalar (c * a) g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_scalar c f) g) k x).
    rewrite IH.
    change (qpoly_mul (cons a f) g)
      with (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g)) k x).
    rewrite (lw0_qp_ai_scalar a g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g) k x).
    ring.
Qed.

Lemma lw0_qp_ai_mul_add_r : forall f g1 g2 k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul f (qpoly_add g1 g2)) k) x ==
  qpoly_eval (lw0_qp_ai (qpoly_mul f g1) k) x
  + qpoly_eval (lw0_qp_ai (qpoly_mul f g2) k) x.
Proof.
  induction f as [|a f IH]; intros g1 g2 k x.
  - change (qpoly_mul nil (qpoly_add g1 g2)) with (@nil Q).
    change (qpoly_mul nil g1) with (@nil Q).
    change (qpoly_mul nil g2) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
    ring.
  - change (qpoly_mul (cons a f) (qpoly_add g1 g2))
      with (qpoly_add (qpoly_scalar a (qpoly_add g1 g2))
              (cons 0 (qpoly_mul f (qpoly_add g1 g2)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_add g1 g2))
               (cons 0 (qpoly_mul f (qpoly_add g1 g2))) k x).
    rewrite (lw0_qp_ai_scalar a (qpoly_add g1 g2) k x).
    rewrite (lw0_qp_ai_add g1 g2 k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f (qpoly_add g1 g2)) k x).
    rewrite (IH g1 g2 (S k) x).
    change (qpoly_mul (cons a f) g1)
      with (qpoly_add (qpoly_scalar a g1) (cons 0 (qpoly_mul f g1))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g1) (cons 0 (qpoly_mul f g1)) k x).
    rewrite (lw0_qp_ai_scalar a g1 k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g1) k x).
    change (qpoly_mul (cons a f) g2)
      with (qpoly_add (qpoly_scalar a g2) (cons 0 (qpoly_mul f g2))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g2) (cons 0 (qpoly_mul f g2)) k x).
    rewrite (lw0_qp_ai_scalar a g2 k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g2) k x).
    ring.
Qed.

Lemma lw0_qp_ai_mul_scalar_r : forall c f g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul f (qpoly_scalar c g)) k) x ==
  c * qpoly_eval (lw0_qp_ai (qpoly_mul f g) k) x.
Proof.
  intros c f.
  induction f as [|a f IH]; intros g k x.
  - change (qpoly_mul nil (qpoly_scalar c g)) with (@nil Q).
    change (qpoly_mul nil g) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai nil k) x) with (0%Q).
    ring.
  - change (qpoly_mul (cons a f) (qpoly_scalar c g))
      with (qpoly_add (qpoly_scalar a (qpoly_scalar c g))
              (cons 0 (qpoly_mul f (qpoly_scalar c g)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_scalar c g))
               (cons 0 (qpoly_mul f (qpoly_scalar c g))) k x).
    rewrite (lw0_qp_ai_scalar a (qpoly_scalar c g) k x).
    rewrite (lw0_qp_ai_scalar c g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f (qpoly_scalar c g)) k x).
    rewrite IH.
    change (qpoly_mul (cons a f) g)
      with (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g)) k x).
    rewrite (lw0_qp_ai_scalar a g k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul f g) k x).
    ring.
Qed.

Lemma lw0_qp_pair_add_r : forall f g1 g2 q,
  lw0_qp_pair f (qpoly_add g1 g2) q
  == lw0_qp_pair f g1 q + lw0_qp_pair f g2 q.
Proof.
  intros f g1 g2 q.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f (qpoly_add g1 g2)) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f (qpoly_add g1 g2)) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f g1) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f g1) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f g2) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f g2) 0) q).
  rewrite (lw0_qp_ai_mul_add_r f g1 g2 0 q).
  ring.
Qed.

Lemma lw0_qp_pair_scalar_l : forall c f g q,
  lw0_qp_pair (qpoly_scalar c f) g q == c * lw0_qp_pair f g q.
Proof.
  intros c f g q.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul (qpoly_scalar c f) g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_scalar c f) g) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f g) 0) q).
  rewrite (lw0_qp_ai_mul_scalar_l c f g 0 q).
  ring.
Qed.

Lemma lw0_qp_pair_scalar_r : forall c f g q,
  lw0_qp_pair f (qpoly_scalar c g) q == c * lw0_qp_pair f g q.
Proof.
  intros c f g q.
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f (qpoly_scalar c g)) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f (qpoly_scalar c g)) 0) q).
  change (qpoly_eval (cons 0 (lw0_qp_ai (qpoly_mul f g) 0)) q)
    with (0 + q * qpoly_eval (lw0_qp_ai (qpoly_mul f g) 0) q).
  rewrite (lw0_qp_ai_mul_scalar_r c f g 0 q).
  ring.
Qed.

Lemma lw0_eval_opp : forall p x,
  qpoly_eval (qpoly_opp p) x == - (qpoly_eval p x).
Proof.
  intro p; induction p as [|a p IH]; intro x; simpl.
  - ring.
  - rewrite IH; ring.
Qed.

Lemma lw0_Qmake_plus : forall x y : Z,
  (x # 1)%Q + (y # 1)%Q == ((x + y) # 1)%Q.
Proof.
  intros x y. unfold Qeq, Qeq_bool. simpl.
  repeat rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma lw0_Qmake_succ : forall z : Z, ((1 + z) # 1)%Q == 1 + (z # 1)%Q.
Proof.
  intros z. unfold Qeq, Qeq_bool. simpl.
  repeat rewrite Z.mul_1_r. reflexivity.
Qed.

Lemma lw0_coef_opp : forall j p,
  lw0_coef j (qpoly_opp p) == - (lw0_coef j p).
Proof.
  intros j p; revert j; induction p as [|a p IH]; intros j.
  - simpl. ring.
  - destruct j as [|j'].
    + simpl. ring.
    + change (qpoly_opp (cons a%Q p)) with (cons (- a)%Q (qpoly_opp p)).
      change (lw0_coef (Datatypes.S j') (cons (- a)%Q (qpoly_opp p)))
        with (lw0_coef j' (qpoly_opp p)).
      change (lw0_coef (Datatypes.S j') (cons a%Q p)) with (lw0_coef j' p).
      apply (IH j').
Qed.

Lemma lw0_coef_iter_opp : forall k j p,
  lw0_coef j (qpoly_deriv_iter k (qpoly_opp p))
  == - lw0_coef j (qpoly_deriv_iter k p).
Proof.
  induction k as [|k IH]; intros j p; simpl.
  - apply lw0_coef_opp.
  - rewrite lw0_coef_deriv, lw0_coef_deriv, (IH (Datatypes.S j) p). ring.
Qed.

Lemma lw0_eval_at_zero : forall p : QPoly, qpoly_eval p 0 == lw0_coef 0 p.
Proof.
  destruct p as [|a p]; simpl; ring.
Qed.

Lemma lw0_eval_deriv_coef0 : forall k p,
  qpoly_eval (qpoly_deriv_iter k p) 0 == q_fact k * lw0_coef k p.
Proof.
  induction k as [|k IH]; intro p.
  - rewrite lw0_eval_at_zero. simpl. ring.
  - simpl (qpoly_deriv_iter (Datatypes.S k) p).
    rewrite lw0_eval_at_zero.
    rewrite lw0_coef_deriv.
    replace (Z.of_nat (Datatypes.S 0)) with 1%Z by reflexivity.
    assert (Hq1 : q_fact (Datatypes.S 0) == 1%Q) by (simpl; ring).
    pose proof (lw0_coef_iter_mul k (Datatypes.S 0) p) as Hm.
    rewrite Hq1 in Hm.
    replace (Datatypes.S 0 + k)%nat with (Datatypes.S k) in Hm by ring.
    rewrite Qmult_1_r in Hm.
    rewrite Hm. ring.
Qed.

Lemma lw0_eval_zero_coef : forall p x,
  (forall j, lw0_coef j p == 0) -> qpoly_eval p x == 0.
Proof.
  induction p as [|a p IH]; intros x H; simpl in *.
  - ring.
  - assert (Ha : a == 0) by (apply (H 0%nat)).
    assert (Hp : forall j, lw0_coef j p == 0)
      by (intro j; apply (H (Datatypes.S j))).
    rewrite Ha, (IH x Hp). ring.
Qed.

Lemma lw0_eval_len_indep : forall p q x,
  (forall j, lw0_coef j p == lw0_coef j q) -> qpoly_eval p x == qpoly_eval q x.
Proof.
  induction p as [|a p IH]; intros q x H.
  - destruct q as [|b q].
    + simpl. ring.
    + symmetry. apply lw0_eval_zero_coef. intro j. destruct j as [|j'].
      * assert (H0 := H 0%nat). simpl in H0. symmetry. exact H0.
      * assert (Hs := H (Datatypes.S j')). simpl in Hs. symmetry. exact Hs.
  - destruct q as [|b q].
    + apply lw0_eval_zero_coef. intro j. destruct j as [|j'].
      * assert (H0 := H 0%nat). simpl in H0. exact H0.
      * assert (Hs := H (Datatypes.S j')). simpl in Hs. exact Hs.
    + assert (Hab : a == b) by (apply (H 0%nat)).
      assert (Hpq : forall j, lw0_coef j p == lw0_coef j q).
      { intro j.
        assert (Hs := H (Datatypes.S j)). simpl in Hs. exact Hs. }
      simpl. rewrite Hab, (IH q x Hpq). ring.
Qed.

Lemma lw0_coef_iter_congr : forall k u v,
  (forall j, lw0_coef j u == lw0_coef j v) ->
  forall j, lw0_coef j (qpoly_deriv_iter k u)
            == lw0_coef j (qpoly_deriv_iter k v).
Proof.
  induction k as [|k IH]; intros u v H j.
  - apply H.
  - simpl. rewrite lw0_coef_deriv, (IH u v H), lw0_coef_deriv. reflexivity.
Qed.

Lemma lw0_eval_iter_congr : forall k u v x,
  (forall j, lw0_coef j u == lw0_coef j v) ->
  qpoly_eval (qpoly_deriv_iter k u) x
  == qpoly_eval (qpoly_deriv_iter k v) x.
Proof.
  intros k u v x H. apply lw0_eval_len_indep. apply (lw0_coef_iter_congr k u v H).
Qed.

Lemma lw0_eval_deriv_iter_add : forall k u v x,
  qpoly_eval (qpoly_deriv_iter k (qpoly_add u v)) x
  == qpoly_eval (qpoly_deriv_iter k u) x + qpoly_eval (qpoly_deriv_iter k v) x.
Proof.
  intros k u v x.
  transitivity (qpoly_eval
                  (qpoly_add (qpoly_deriv_iter k u) (qpoly_deriv_iter k v)) x).
  - apply lw0_eval_len_indep. intro j.
    rewrite lw0_coef_iter_add, lw0_coef_add. reflexivity.
  - rewrite qpoly_eval_add. reflexivity.
Qed.

Lemma lw0_eval_deriv_iter_scalar : forall k a p x,
  qpoly_eval (qpoly_deriv_iter k (qpoly_scalar a p)) x
  == a * qpoly_eval (qpoly_deriv_iter k p) x.
Proof.
  intros k a p x.
  transitivity (qpoly_eval (qpoly_scalar a (qpoly_deriv_iter k p)) x).
  - apply lw0_eval_len_indep. intro j.
    rewrite lw0_coef_iter_scalar, lw0_coef_scalar. reflexivity.
  - rewrite qpoly_eval_scalar. reflexivity.
Qed.

Lemma lw0_eval_iter_opp : forall k p x,
  qpoly_eval (qpoly_deriv_iter k (qpoly_opp p)) x
  == - qpoly_eval (qpoly_deriv_iter k p) x.
Proof.
  intros k p x.
  transitivity (qpoly_eval (qpoly_opp (qpoly_deriv_iter k p)) x).
  - apply lw0_eval_len_indep. intro j.
    rewrite lw0_coef_iter_opp, lw0_coef_opp. reflexivity.
  - rewrite lw0_eval_opp. reflexivity.
Qed.

Definition lw0_pred_iter (k : nat) (w : QPoly) : QPoly :=
  match k with
  | 0%nat => w
  | Datatypes.S k' => qpoly_deriv_iter k' w
  end.

Lemma lw0_shift_deriv : forall k w x,
  qpoly_eval (qpoly_deriv_iter k (cons 0 w)) x
  == x * qpoly_eval (qpoly_deriv_iter k w) x
  + (Z.of_nat k # 1)%Q * qpoly_eval (lw0_pred_iter k w) x.
Proof.
  induction k as [|k IH]; intros w x.
  - simpl. ring.
  - rewrite qpoly_deriv_iter_commute.
    change (qpoly_deriv (cons 0 w))
      with (qpoly_add w (cons 0 (qpoly_deriv w))).
    rewrite lw0_eval_deriv_iter_add.
    rewrite (IH (qpoly_deriv w) x).
    rewrite <- (qpoly_deriv_iter_commute k w).
    destruct k as [|k'].
    + change (lw0_pred_iter 0%nat (qpoly_deriv w)) with (qpoly_deriv w).
      change (qpoly_deriv_iter (Datatypes.S 0) w) with (qpoly_deriv w).
      change (lw0_pred_iter (Datatypes.S 0) w) with (qpoly_deriv_iter 0%nat w).
      change (qpoly_deriv_iter 0%nat w) with w.
      replace (Z.of_nat 0) with 0%Z by reflexivity.
      replace (Z.of_nat (Datatypes.S 0)) with 1%Z by reflexivity.
      ring.
    + change (lw0_pred_iter (Datatypes.S k') (qpoly_deriv w))
        with (qpoly_deriv_iter k' (qpoly_deriv w)).
      rewrite <- (qpoly_deriv_iter_commute k' w).
      change (lw0_pred_iter (Datatypes.S (Datatypes.S k')) w)
        with (qpoly_deriv_iter (Datatypes.S k') w).
      replace (Z.of_nat (Datatypes.S (Datatypes.S k')))
        with (1 + Z.of_nat (Datatypes.S k'))%Z
        by (rewrite (Nat2Z.inj_succ (Datatypes.S k')),
            (Nat2Z.inj_succ k'),
            (Z.add_comm 1 (Z.succ (Z.of_nat k'))); reflexivity).
      replace (Z.of_nat (Datatypes.S k')) with (1 + Z.of_nat k')%Z by (rewrite (Nat2Z.inj_succ k'), (Z.add_comm 1 (Z.of_nat k')); reflexivity).
      replace ((1 + (1 + Z.of_nat k')) # 1)%Q
        with (1 + ((1 + Z.of_nat k') # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      replace ((1 + Z.of_nat k') # 1)%Q
        with (1 + (Z.of_nat k' # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      ring.
Qed.

Definition lw0_qtail (q : Q) (P : QPoly) : QPoly :=
  qpoly_add (qpoly_scalar q P) (cons 0 (qpoly_opp P)).

Lemma lw0_qtail_deriv_congr : forall q P j,
  lw0_coef j (qpoly_deriv (lw0_qtail q P))
  == lw0_coef j (qpoly_add (lw0_qtail q (qpoly_deriv P)) (qpoly_opp P)).
Proof.
  intros q P j. unfold lw0_qtail.
  rewrite lw0_coef_deriv.
  rewrite lw0_coef_add. rewrite lw0_coef_add. rewrite lw0_coef_add.
  rewrite lw0_coef_scalar. rewrite lw0_coef_scalar.
  destruct j as [|j'].
  - simpl. rewrite lw0_coef_opp.
    rewrite (lw0_coef_deriv 0%nat P).
    replace (Z.of_nat (Datatypes.S 0)) with 1%Z by reflexivity.
    ring.
  - simpl (lw0_coef (Datatypes.S (Datatypes.S j')) (cons 0%Q (qpoly_opp P))).
    simpl (lw0_coef (Datatypes.S j') (cons 0%Q (qpoly_opp (qpoly_deriv P)))).
    rewrite lw0_coef_opp. rewrite lw0_coef_opp.
    rewrite lw0_coef_deriv. rewrite lw0_coef_deriv.
    replace (Z.of_nat (Datatypes.S (Datatypes.S j')))
      with (1 + Z.of_nat (Datatypes.S j'))%Z by (rewrite (Nat2Z.inj_succ (Datatypes.S j')),
            (Nat2Z.inj_succ j'),
            (Z.add_comm 1 (Z.succ (Z.of_nat j'))); reflexivity).
    replace ((1 + Z.of_nat (Datatypes.S j')) # 1)%Q
      with (1 + (Z.of_nat (Datatypes.S j') # 1))%Q
      by (symmetry; apply lw0_Qmake_succ_eq).
    ring.
Qed.

Lemma lw0_qtail_step : forall q P k,
  qpoly_eval (qpoly_deriv_iter k (lw0_qtail q P)) q
  == - ((Z.of_nat k # 1)%Q * qpoly_eval (lw0_pred_iter k P) q).
Proof.
  intros q P k. revert P. induction k as [|k IH]; intros P.
  - unfold lw0_qtail. simpl.
    rewrite (qpoly_eval_add (qpoly_scalar q P) (cons 0%Q (qpoly_opp P)) q).
    rewrite (qpoly_eval_scalar q P q). simpl.
    rewrite (lw0_eval_opp P q). ring.
  - rewrite qpoly_deriv_iter_commute.
    rewrite (lw0_eval_iter_congr k (qpoly_deriv (lw0_qtail q P))
               (qpoly_add (lw0_qtail q (qpoly_deriv P)) (qpoly_opp P)) q
               (fun j => lw0_qtail_deriv_congr q P j)).
    rewrite (lw0_eval_deriv_iter_add k (lw0_qtail q (qpoly_deriv P))
               (qpoly_opp P) q).
    rewrite (IH (qpoly_deriv P)).
    rewrite (lw0_eval_iter_opp k P q).
    change (lw0_pred_iter (Datatypes.S k) P) with (qpoly_deriv_iter k P).
    destruct k as [|k'].
    + replace (Z.of_nat 0) with 0%Z by reflexivity.
      replace (Z.of_nat (Datatypes.S 0)) with 1%Z by reflexivity.
      change (lw0_pred_iter 0%nat (qpoly_deriv P)) with (qpoly_deriv P).
      change (qpoly_deriv_iter 0%nat P) with P.
      ring.
    + change (lw0_pred_iter (Datatypes.S k') (qpoly_deriv P))
        with (qpoly_deriv_iter k' (qpoly_deriv P)).
      rewrite <- (qpoly_deriv_iter_commute k' P).
      replace (Z.of_nat (Datatypes.S (Datatypes.S k')))
        with (1 + Z.of_nat (Datatypes.S k'))%Z
        by (rewrite (Nat2Z.inj_succ (Datatypes.S k')),
            (Nat2Z.inj_succ k'),
            (Z.add_comm 1 (Z.succ (Z.of_nat k'))); reflexivity).
      replace (Z.of_nat (Datatypes.S k')) with (1 + Z.of_nat k')%Z by (rewrite (Nat2Z.inj_succ k'), (Z.add_comm 1 (Z.of_nat k')); reflexivity).
      replace ((1 + (1 + Z.of_nat k')) # 1)%Q
        with (1 + ((1 + Z.of_nat k') # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      replace ((1 + Z.of_nat k') # 1)%Q
        with (1 + (Z.of_nat k' # 1))%Q
        by (symmetry; apply lw0_Qmake_succ_eq).
      ring.
Qed.

Lemma lw0_coef_mul_mono_lt : forall n k (W : QPoly), (k < n)%nat ->
  lw0_coef k (qpoly_mul (lw0_mono n) W) == 0.
Proof.
  induction n as [|m IH]; intros k W Hk.
  - inversion Hk.
  - destruct k as [|k'].
    + change (lw0_mono (Datatypes.S m)) with (cons 0 (lw0_mono m)).
      change (qpoly_mul (cons 0 (lw0_mono m)) W)
        with (qpoly_add (qpoly_scalar 0%Q W)
                        (cons 0 (qpoly_mul (lw0_mono m) W))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      simpl (lw0_coef 0%nat (cons 0%Q (qpoly_mul (lw0_mono m) W))).
      ring.
    + change (lw0_mono (Datatypes.S m)) with (cons 0 (lw0_mono m)).
      change (qpoly_mul (cons 0 (lw0_mono m)) W)
        with (qpoly_add (qpoly_scalar 0%Q W)
                        (cons 0 (qpoly_mul (lw0_mono m) W))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      simpl (lw0_coef (Datatypes.S k') (cons 0%Q (qpoly_mul (lw0_mono m) W))).
      assert (IH0 : lw0_coef k' (qpoly_mul (lw0_mono m) W) == 0%Q)
        by (apply (IH k' W (proj2 (Nat.succ_lt_mono k' m) Hk))).
      rewrite IH0.
      ring.
Qed.

Lemma lw0_coef_mul_mono_ge : forall n k (W : QPoly), (n <= k)%nat ->
  lw0_coef k (qpoly_mul (lw0_mono n) W) == lw0_coef (k - n) W.
Proof.
  induction n as [|m IH]; intros k W Hk.
  - replace (k - 0)%nat with k by (rewrite Nat.sub_0_r; reflexivity).
    change (qpoly_mul (lw0_mono 0) W)
      with (qpoly_add (qpoly_scalar 1%Q W) (cons 0%Q (@nil Q))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct k as [|k''].
    + simpl. ring.
    + simpl (lw0_coef (Datatypes.S k'') (cons 0%Q (@nil Q))). ring.
  - destruct k as [|k']; [ inversion Hk | ].
    change (lw0_mono (Datatypes.S m)) with (cons 0 (lw0_mono m)).
    change (qpoly_mul (cons 0 (lw0_mono m)) W)
      with (qpoly_add (qpoly_scalar 0%Q W)
                      (cons 0 (qpoly_mul (lw0_mono m) W))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    simpl (lw0_coef (Datatypes.S k') (cons 0%Q (qpoly_mul (lw0_mono m) W))).
    rewrite (IH k' W (proj2 (Nat.succ_le_mono m k') Hk)).
    replace (Datatypes.S k' - Datatypes.S m)%nat with (k' - m)%nat by (rewrite Nat.sub_succ; reflexivity).
    ring.
Qed.

Fixpoint lw0_qminus_pow (q : Q) (n : nat) : QPoly :=
  match n with
  | 0%nat => cons 1 nil
  | Datatypes.S m =>
      qpoly_mul (lw0_qminus_pow q m) (cons q (cons (-1)%Q nil))
  end.

Definition lw0_niven_f_z (q : Q) (b : Z) (n : nat) : QPoly :=
  qpoly_scalar ((Zpower_nat b n) # (Pos.of_nat (fact n)))%Q
    (qpoly_mul (lw0_mono n) (lw0_qminus_pow q n)).

Lemma lw0_niven_deriv_zero_0 : forall q b n k, (k < n)%nat ->
  qpoly_eval (qpoly_deriv_iter k (lw0_niven_f_z q b n)) 0 == 0.
Proof.
  intros q b n k Hk. unfold lw0_niven_f_z.
  rewrite lw0_eval_deriv_iter_scalar, lw0_eval_deriv_coef0.
  assert (H0 : lw0_coef k
                 (qpoly_mul (lw0_mono n) (lw0_qminus_pow q n)) == 0%Q)
    by (apply (lw0_coef_mul_mono_lt n k (lw0_qminus_pow q n) Hk)).
  rewrite H0.
  ring.
Qed.

Lemma lw0_coef_mul_h0 : forall (A : QPoly) q,
  lw0_coef 0%nat (qpoly_mul A (cons q (cons (-1)%Q nil)))
  == q * lw0_coef 0%nat A.
Proof.
  induction A as [|a A IH]; intro q.
  - simpl. ring.
  - change (qpoly_mul (cons a A) (cons q (cons (-1)%Q nil)))
      with (qpoly_add (qpoly_scalar a (cons q (cons (-1)%Q nil)))
                      (cons 0 (qpoly_mul A (cons q (cons (-1)%Q nil))))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    simpl (lw0_coef 0%nat (cons q (cons (-1)%Q nil))).
    simpl (lw0_coef 0%nat (cons 0%Q (qpoly_mul A (cons q (cons (-1)%Q nil))))).
    simpl (lw0_coef 0%nat (cons a%Q A)).
    ring.
Qed.

Lemma lw0_coef_mul_hS : forall (A : QPoly) q j,
  lw0_coef (Datatypes.S j) (qpoly_mul A (cons q (cons (-1)%Q nil)))
  == q * lw0_coef (Datatypes.S j) A - lw0_coef j A.
Proof.
  induction A as [|a A IH]; intros q j.
  - simpl. ring.
  - change (qpoly_mul (cons a A) (cons q (cons (-1)%Q nil)))
      with (qpoly_add (qpoly_scalar a (cons q (cons (-1)%Q nil)))
                      (cons 0 (qpoly_mul A (cons q (cons (-1)%Q nil))))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + simpl (lw0_coef (Datatypes.S 0) (cons q (cons (-1)%Q nil))).
      simpl (lw0_coef (Datatypes.S 0)
               (cons 0%Q (qpoly_mul A (cons q (cons (-1)%Q nil))))).
      simpl (lw0_coef (Datatypes.S 0) (cons a A)).
      simpl (lw0_coef 0%nat (cons a A)).
      rewrite (lw0_coef_mul_h0 A q). ring.
    + simpl (lw0_coef (Datatypes.S (Datatypes.S j'))
               (cons q (cons (-1)%Q nil))).
      simpl (lw0_coef (Datatypes.S (Datatypes.S j'))
               (cons 0%Q (qpoly_mul A (cons q (cons (-1)%Q nil))))).
      rewrite (IH q j').
      destruct j' as [|j''].
      * simpl. ring.
      * simpl (lw0_coef (Datatypes.S (Datatypes.S (Datatypes.S j'')))
                  (cons q (cons (-1)%Q nil))).
        simpl (lw0_coef (Datatypes.S (Datatypes.S (Datatypes.S j'')))
                  (cons a%Q A)).
        simpl (lw0_coef (Datatypes.S (Datatypes.S j'')) (cons a%Q A)).
        ring.
Qed.
(* ---- The binomial-coefficient prelude (the recursive coefficient
   [bpa_binom], its Pascal identity, its value at [k = 0], and its
   vanishing outside the coefficient range) ---- *)

Fixpoint bpa_binom (n k : nat) {struct n} : Q :=
  match n with
  | 0%nat =>
      match k with
      | 0%nat => 1%Q
      | Datatypes.S _ => 0%Q
      end
  | Datatypes.S n' =>
      match k with
      | 0%nat => 1%Q
      | Datatypes.S k' => (bpa_binom n' k' + bpa_binom n' (Datatypes.S k'))%Q
      end
  end.

Lemma bpa_binom_pascal : forall n k : nat,
  bpa_binom (Datatypes.S n) (Datatypes.S k)
    = (bpa_binom n k + bpa_binom n (Datatypes.S k))%Q.
Proof. intros n k. reflexivity. Qed.

Lemma bpa_binom_0 : forall n : nat, bpa_binom n 0%nat = 1%Q.
Proof. intros n. destruct n as [| n']; reflexivity. Qed.

Lemma bpa_binom_out : forall n k : nat, (n < k)%nat -> bpa_binom n k == 0%Q.
Proof.
  intros n. induction n as [| n' IH]; intros k Hk.
  - destruct k as [| k']; [ inversion Hk | ].
    apply Qeq_refl.
  - destruct k as [| k']; [ inversion Hk | ].
    change (bpa_binom (Datatypes.S n') (Datatypes.S k'))
      with (bpa_binom n' k' + bpa_binom n' (Datatypes.S k'))%Q.
    setoid_rewrite (IH k' (proj2 (Nat.succ_lt_mono n' k') Hk)).
    setoid_rewrite (IH (Datatypes.S k') (Nat.lt_lt_succ_r n' k' (proj2 (Nat.succ_lt_mono n' k') Hk))).
    apply Qplus_0_l.
Qed.

Lemma lw0_sub_succ_eq : forall m j' : nat, (Datatypes.S j' <= m)%nat ->
  (m - j')%nat = Datatypes.S (m - Datatypes.S j')%nat.
Proof.
  intros m j' Hb.
  destruct (Nat.le_exists_sub (Datatypes.S j') m Hb) as [d [Hd _]].
  rewrite Hd, (Nat.add_succ_r d j').
  rewrite (Nat.sub_succ (d + j') j'), Nat.add_sub.
  replace (S (d + j') - j')%nat with (S d)%nat
    by (rewrite (Nat.sub_succ_l j' (d + j'));
        [ f_equal; symmetry; exact (Nat.add_sub d j')
        | rewrite Nat.add_comm; apply Nat.le_add_r ]).
  reflexivity.
Qed.
(* Companion algebraic-identity helper (the explicit chain of the
   linear-arithmetic slot corresponding to the source region
   [LW0PiIrrational.v:L7466]) *)

Lemma lw0_coef_qminus_pow : forall n q j,
  lw0_coef j (lw0_qminus_pow q n)
  == bpa_binom n j * q_pow (-1)%Q j * q_pow q (n - j)%nat.
Proof.
  induction n as [|m IH]; intros q j.
  - destruct j as [|j'].
    + simpl. ring.
    + simpl (lw0_coef (Datatypes.S j') (lw0_qminus_pow q 0)).
      simpl (bpa_binom 0 (Datatypes.S j')).
      simpl (q_pow (-1)%Q (Datatypes.S j')).
      simpl (q_pow q (0 - Datatypes.S j')).
      ring.
  - change (lw0_qminus_pow q (Datatypes.S m))
      with (qpoly_mul (lw0_qminus_pow q m) (cons q (cons (-1)%Q nil))).
    destruct j as [|j'].
    + rewrite (lw0_coef_mul_h0 (lw0_qminus_pow q m) q), (IH q 0%nat).
      rewrite (bpa_binom_0 (Datatypes.S m)), (bpa_binom_0 m).
      simpl (q_pow (-1)%Q 0).
      replace (Datatypes.S m - 0)%nat with (Datatypes.S m) by (rewrite Nat.sub_0_r; reflexivity).
      replace (m - 0)%nat with m by (rewrite Nat.sub_0_r; reflexivity).
      rewrite q_pow_succ. ring.
    + rewrite (lw0_coef_mul_hS (lw0_qminus_pow q m) q j').
      rewrite (IH q (Datatypes.S j')), (IH q j').
      rewrite (bpa_binom_pascal m j').
      replace (Datatypes.S m - Datatypes.S j')%nat with (m - j')%nat by (rewrite Nat.sub_succ; reflexivity).
      simpl (q_pow (-1)%Q (Datatypes.S j')).
      destruct (Nat.leb (Datatypes.S j') m) eqn:Hb.
      * apply Nat.leb_le in Hb.
        assert (HM : q_pow q (m - Datatypes.S j')%nat * q == q_pow q (m - j')%nat).
        { replace (m - j')%nat with (Datatypes.S (m - Datatypes.S j'))%nat by (symmetry; apply lw0_sub_succ_eq; exact Hb).
          rewrite q_pow_succ. ring. }
        rewrite <- HM. ring.
      * apply Nat.leb_gt in Hb.
        assert (Ho1 : bpa_binom m (Datatypes.S j') == 0%Q)
          by (apply (bpa_binom_out m (Datatypes.S j') Hb)).
        rewrite Ho1.
        ring.
Qed.

Fixpoint lw0_ratio (n k : nat) : nat :=
  match k with
  | 0%nat => 1%nat
  | Datatypes.S k' =>
      if Nat.leb n k' then (Datatypes.S k' * lw0_ratio n k')%nat else 1%nat
  end.

Lemma lw0_fact_ratio : forall k n, (n <= k)%nat ->
  fact k = (fact n * lw0_ratio n k)%nat.
Proof.
  induction k as [|k' IH]; intros n Hk.
  - replace n with 0%nat by (symmetry; apply Nat.le_0_r; exact Hk). reflexivity.
  - destruct (Nat.leb n k') eqn:Hb.
    + assert (Hle : (n <= k')%nat) by (apply Nat.leb_le; exact Hb).
      assert (Hf : fact (Datatypes.S k') = (Datatypes.S k' * fact k')%nat)
        by reflexivity.
      simpl (lw0_ratio n (Datatypes.S k')). rewrite Hb.
      rewrite Hf, (IH n Hle).
      rewrite Nat.mul_assoc, (Nat.mul_comm (Datatypes.S k') (fact n)).
      rewrite <- Nat.mul_assoc. reflexivity.
    + change (lw0_ratio n (Datatypes.S k'))
        with (if Nat.leb n k' then (Datatypes.S k' * lw0_ratio n k')%nat
              else 1%nat).
      rewrite Hb.
      replace (if false then (Datatypes.S k' * lw0_ratio n k')%nat else 1%nat)
        with 1%nat by reflexivity.
      apply Nat.leb_gt in Hb.
      replace n with (Datatypes.S k')
        by (apply (Nat.le_antisymm (Datatypes.S k') n);
            [ exact (proj2 (Nat.le_succ_l k' n) Hb) | exact Hk ]).
      rewrite Nat.mul_1_r. reflexivity.
Qed.

Lemma lw0_Qmake_mul : forall x y : Z, (x # 1)%Q * (y # 1)%Q == ((x * y) # 1)%Q.
Proof. intros x y. reflexivity. Qed.

Lemma lw0_qfact_Z : forall n, q_fact n == ((Z.of_nat (fact n)) # 1)%Q.
Proof.
  induction n as [|m IH].
  - reflexivity.
  - rewrite q_fact_succ, IH.
    assert (Hf : fact (Datatypes.S m) = (Datatypes.S m * fact m)%nat)
      by reflexivity.
    rewrite Hf.
    assert (Hm : ((Z.of_nat (Datatypes.S m) # 1)%Q
                  * ((Z.of_nat (fact m)) # 1)%Q)%Q
                 == ((Z.of_nat (Datatypes.S m) * Z.of_nat (fact m)) # 1)%Q)
      by (apply (lw0_Qmake_mul (Z.of_nat (Datatypes.S m))
                  (Z.of_nat (fact m)))).
    rewrite Hm, <- Nat2Z.inj_mul. reflexivity.
Qed.

Fixpoint lw0_binom (n k : nat) {struct n} : nat :=
  match n with
  | 0%nat =>
      match k with
      | 0%nat => 1%nat
      | Datatypes.S _ => 0%nat
      end
  | Datatypes.S n' =>
      match k with
      | 0%nat => 1%nat
      | Datatypes.S k' => (lw0_binom n' k' + lw0_binom n' (Datatypes.S k'))%nat
      end
  end.

Lemma lw0_binom_out : forall n k : nat, (n < k)%nat -> lw0_binom n k = 0%nat.
Proof.
  intros n. induction n as [|n' IH]; intros k Hk.
  - destruct k as [|k']; [ inversion Hk | reflexivity ].
  - destruct k as [|k']; [ inversion Hk | ].
    change (lw0_binom (Datatypes.S n') (Datatypes.S k'))
      with (lw0_binom n' k' + lw0_binom n' (Datatypes.S k'))%nat.
    rewrite (IH k' (proj2 (Nat.succ_lt_mono n' k') Hk)),
(IH (Datatypes.S k') (Nat.lt_lt_succ_r n' k' (proj2 (Nat.succ_lt_mono n' k') Hk))).
    reflexivity.
Qed.

Fixpoint lw0_zsign (m : nat) : Z :=
  match m with
  | 0%nat => 1%Z
  | Datatypes.S m' => (- lw0_zsign m')%Z
  end.

Lemma lw0_zsign_step : forall m : nat,
  lw0_zsign (Datatypes.S m) = (- lw0_zsign m)%Z.
Proof. intros m. reflexivity. Qed.

Definition lw0_z_lo (a b : Z) (n k : nat) : Q :=
  ((lw0_zsign (k - n) * Z.of_nat (lw0_binom n (k - n))
     * Zpower_nat a ((2 * n) - k) * Zpower_nat b (k - n)) # 1)%Q
  * ((Z.of_nat (lw0_ratio n k)) # 1)%Q.

Definition lw0_z_hi (a b : Z) (n k : nat) : Q :=
  ((lw0_zsign (n - k) * Z.of_nat (lw0_binom n (n - k))
     * Zpower_nat a k * Zpower_nat b (n - k)) # 1)%Q
  * ((Z.of_nat (lw0_ratio n (2 * n - k))) # 1)%Q.

Fixpoint lw0_qsum (g : nat -> Q) (m : nat) : Q :=
  match m with
  | 0%nat => g 0%nat
  | Datatypes.S m' => lw0_qsum g m' + g (Datatypes.S m')
  end.

Definition lw0_K_leg (a b : Z) (n j : nat) : Q :=
  (lw0_zsign j # 1)%Q *
  (if Nat.leb n (2 * j)
   then lw0_z_lo a b n (2 * j) + lw0_z_hi a b n (2 * (n - j))
   else (0 # 1)%Q).

Definition lw0_K (a b : Z) (n : nat) : Q :=
  lw0_qsum (lw0_K_leg a b n) n.

Lemma lw0_pi_mono_eval : forall (m : nat) (t : Q),
  qpoly_eval (lw0_pi_mono m) t == q_pow t m.
Proof.
  intros m t. induction m as [| m IH].
  - cbn [lw0_pi_mono qpoly_eval q_pow]. ring.
  - cbn [lw0_pi_mono]. rewrite qpoly_eval_mul, IH.
    cbn [qpoly_eval q_pow]. ring.
Qed.

Lemma lw0_pi_qminus_pow_eval : forall (q t : Q) (n : nat),
  qpoly_eval (lw0_pi_qminus_pow q n) t == q_pow (q - t) n.
Proof.
  intros q t n. induction n as [| n IH].
  - cbn [lw0_pi_qminus_pow qpoly_eval q_pow]. ring.
  - cbn [lw0_pi_qminus_pow]. rewrite qpoly_eval_mul, IH.
    cbn [qpoly_eval q_pow]. ring.
Qed.

Fixpoint Powpos (p : positive) (m : nat) : positive :=
  match m with
  | 0%nat => 1%positive
  | Datatypes.S m' => p * Powpos p m'
  end.

Lemma lw0_posnat_zeq : forall m : nat, (1 <= m)%nat ->
  Zpos (Pos.of_nat m) = Z.of_nat m.
Proof.
  intros m Hm. destruct m as [|m']; [ exfalso; inversion Hm | ].
  change (Z.of_nat (Datatypes.S m')) with (Z.pos (Pos.of_succ_nat m')).
  rewrite <- Pos.of_nat_succ.
  reflexivity.
Qed.

Lemma lw0_zpower_nat_add : forall (z : Z) (m n : nat),
  Zpower_nat z (m + n) = (Zpower_nat z m * Zpower_nat z n)%Z.
Proof.
  intros z m n. induction n as [|n IH].
  - rewrite Nat.add_0_r, Z.mul_1_r. reflexivity.
  - replace (m + Datatypes.S n)%nat with (Datatypes.S (m + n))%nat by ring.
    rewrite Zpower_nat_succ_r, IH, Zpower_nat_succ_r. ring.
Qed.

Lemma lw0_zpos_pospow : forall (p : positive) (m : nat),
  Zpos (Powpos p m) = Zpower_nat (Zpos p) m.
Proof.
  intros p m. induction m as [|m IH].
  - reflexivity.
  - change (Powpos p (Datatypes.S m)) with (p * Powpos p m)%positive.
    rewrite Pos2Z.inj_mul, IH, Zpower_nat_succ_r. reflexivity.
Qed.

Lemma lw0_q_pow_qmake : forall (x : Z) (p : positive) (m : nat),
  q_pow ((x # p)%Q) m == ((Zpower_nat x m) # (Powpos p m))%Q.
Proof.
  intros x p m. induction m as [|m IH].
  - reflexivity.
  - change (q_pow (x # p)%Q (Datatypes.S m)) with ((x # p)%Q * q_pow (x # p)%Q m).
    change (Zpower_nat x (Datatypes.S m)) with (x * Zpower_nat x m)%Z.
    change (Powpos p (Datatypes.S m)) with (p * Powpos p m)%positive.
    rewrite IH. reflexivity.
Qed.

Lemma lw0_q_pow_m1 : forall m : nat, q_pow (-1)%Q m == ((lw0_zsign m) # 1)%Q.
Proof.
  intros m. induction m as [|m IH].
  - reflexivity.
  - change (q_pow (-1)%Q (Datatypes.S m)) with ((-1)%Q * q_pow (-1)%Q m).
    change (lw0_zsign (Datatypes.S m)) with (- lw0_zsign m)%Z.
    rewrite IH.
    replace ((-1)%Q * ((lw0_zsign m) # 1)%Q)
      with (((-1 * lw0_zsign m)%Z # 1)%Q) by reflexivity.
    replace (-1 * lw0_zsign m)%Z with (- lw0_zsign m)%Z by ring.
    reflexivity.
Qed.

Lemma lw0_bpa_binom_eq : forall n k : nat,
  bpa_binom n k == (Z.of_nat (lw0_binom n k) # 1)%Q.
Proof.
  intros n. induction n as [|n IH]; intros k.
  - destruct k as [|k].
    + reflexivity.
    + reflexivity.
  - destruct k as [|k].
    + reflexivity.
    + change (bpa_binom (Datatypes.S n) (Datatypes.S k))
        with (bpa_binom n k + bpa_binom n (Datatypes.S k))%Q.
      change (lw0_binom (Datatypes.S n) (Datatypes.S k))
        with (lw0_binom n k + lw0_binom n (Datatypes.S k))%nat.
      rewrite (IH k), (IH (Datatypes.S k)).
      rewrite Nat2Z.inj_add.
      apply lw0_Qmake_plus.
Qed.

Lemma lw0_sub_sub_shift : forall n k : nat, (n <= k)%nat ->
  (n - (k - n))%nat = (2 * n - k)%nat.
Proof.
  intros n k Hk.
  destruct (Nat.le_exists_sub n k Hk) as [d [Hd _]].
  rewrite Hd. clear Hk k Hd.
  induction d as [|d' IHd].
  - replace (2 * n)%nat with (n + n)%nat by ring.
    rewrite Nat.add_0_l, Nat.add_sub, Nat.sub_diag, Nat.sub_0_r. reflexivity.
  - rewrite Nat.add_succ_l, (Nat.sub_succ_l n (d' + n)).
    + rewrite Nat.sub_succ_r, Nat.sub_succ_r, <- IHd, Nat.add_sub. reflexivity.
    + rewrite Nat.add_comm. apply Nat.le_add_r.
Qed.
(* Companion algebraic-identity helper: [n-(k-n) = 2n-k] (the
   induction chain of the linear-arithmetic slot corresponding to the
   source region [LW0PiIrrational.v:L7232]) *)

Lemma lw0_conn_lo : forall (a : Z) (b : positive) (n k : nat), (n <= k)%nat ->
  qpoly_eval (qpoly_deriv_iter k (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0
  == lw0_z_lo a (Zpos b) n k.
Proof.
  intros a b n k Hk.
  assert (Hfn : (1 <= fact n)%nat) by (destruct (fact n) as [|k0] eqn:Ek; [ exfalso; apply (fact_neq_0 n); exact Ek | apply le_n_S; apply Nat.le_0_l ]).
  unfold lw0_niven_f_z.
  rewrite lw0_eval_deriv_iter_scalar.
  rewrite lw0_eval_deriv_coef0.
  rewrite (lw0_coef_mul_mono_ge n k (lw0_qminus_pow (a # b)%Q n) Hk).
  rewrite (lw0_coef_qminus_pow n (a # b)%Q (k - n)).
  replace (n - (k - n))%nat with (2 * n - k)%nat by (symmetry; apply lw0_sub_sub_shift; exact Hk).
  rewrite (lw0_bpa_binom_eq n (k - n)).
  rewrite lw0_qfact_Z.
  rewrite (lw0_q_pow_m1 (k - n)).
  rewrite (lw0_q_pow_qmake a b (2 * n - k)).
  unfold lw0_z_lo.
  destruct (Nat.leb (k - n) n) eqn:Hb2.
  - apply Nat.leb_le in Hb2.
    assert (Hf : Z.of_nat (fact k) = (Z.of_nat (fact n) * Z.of_nat (lw0_ratio n k))%Z).
    { rewrite <- Nat2Z.inj_mul. f_equal. exact (lw0_fact_ratio k n Hk). }
    assert (Hpow : (Zpower_nat (Zpos b) (k - n) * Zpower_nat (Zpos b) (2 * n - k))%Z
                   = Zpower_nat (Zpos b) n).
    { rewrite <- lw0_zpower_nat_add. f_equal.
      rewrite <- (lw0_sub_sub_shift n k Hk).
      rewrite Nat.add_comm. exact (Nat.sub_add (k - n) n Hb2). }
    replace (Zpower_nat (Zpos b) n)
      with (Zpower_nat (Zpos b) (k - n) * Zpower_nat (Zpos b) (2 * n - k))%Z by exact Hpow.
    unfold Qeq, Qeq_bool. simpl.
    rewrite Pos2Z.inj_mul, (lw0_posnat_zeq (fact n) Hfn),
            lw0_zpos_pospow, Hf.
    ring.
  - apply Nat.leb_gt in Hb2.
    assert (H0 : lw0_binom n (k - n) = 0%nat) by (apply lw0_binom_out; exact Hb2).
    rewrite H0. unfold Qeq, Qeq_bool. simpl.
    first [ reflexivity | ring ].
Qed.

Lemma lw0_conn_hi : forall (a : Z) (b : positive) (n j : nat),
  (n <= 2 * j)%nat -> (j <= n)%nat ->
  qpoly_eval (qpoly_deriv_iter (2 * j) (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0
  == lw0_z_hi a (Zpos b) n (2 * (n - j)).
Proof.
  intros a b n j H1 H2.
  rewrite (lw0_conn_lo a b n (2 * j) H1).
  unfold lw0_z_lo, lw0_z_hi.
  replace (2 * j - n)%nat with (n - (2 * (n - j)))%nat
    by (destruct (Nat.le_exists_sub n (2 * j) H1) as [d [Hd _]];
        destruct (Nat.le_exists_sub j n H2) as [e [He _]];
        rewrite He in Hd;
        assert (Hjed : (j = d + e)%nat)
          by (replace (2 * j)%nat with (j + j)%nat in Hd by ring;
              rewrite Nat.add_assoc in Hd;
              exact (proj1 (Nat.add_cancel_r j (d + e) j) Hd));
        rewrite He, Hd;
        rewrite Nat.add_sub;
        rewrite Nat.add_sub;
        rewrite Hjed;
        replace (e + (d + e))%nat with (d + 2 * e)%nat by ring;
        rewrite Nat.add_sub;
        reflexivity).
  replace (2 * n - 2 * j)%nat with (2 * (n - j))%nat
    by (apply Nat.mul_sub_distr_l).
  replace (2 * j)%nat with (2 * n - (2 * (n - j)))%nat
    by (rewrite (Nat.mul_sub_distr_l n j 2);
        apply Nat.add_sub_eq_l;
        rewrite Nat.sub_add by (apply Nat.mul_le_mono_l; exact H2);
        reflexivity).
  reflexivity.
Qed.

Lemma lw0_alt_zsign : forall j : nat, lw0_alt j == (lw0_zsign j # 1)%Q.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - rewrite lw0_alt_opp. rewrite IH. rewrite lw0_zsign_step. reflexivity.
Qed.

Lemma lw0_pitB_ibp_dbl : forall (f g : qpoly) (q : Q),
  lw0_qp_pair f (qpoly_deriv_iter 2 g) q ==
  lw0_qp_pair (qpoly_deriv_iter 2 f) g q
  + (qpoly_eval (qpoly_mul f (qpoly_deriv g)) q
       - qpoly_eval (qpoly_mul f (qpoly_deriv g)) 0)
  - (qpoly_eval (qpoly_mul (qpoly_deriv f) g) q
       - qpoly_eval (qpoly_mul (qpoly_deriv f) g) 0).
Proof.
  intros f g q.
  change (qpoly_deriv_iter 2 f) with (qpoly_deriv (qpoly_deriv f)).
  change (qpoly_deriv_iter 2 g) with (qpoly_deriv (qpoly_deriv g)).
  assert (HA := lw0_qp_pair_ibp (qpoly_deriv f) g q).
  assert (HB := lw0_qp_pair_ibp f (qpoly_deriv g) q).
  rewrite <- HA. rewrite <- HB.
  ring.
Qed.

Lemma lw0_pitB_ai_mul01 : forall g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (cons 0%Q (cons 1%Q nil)) g) k) x
  == x * qpoly_eval (lw0_qp_ai g (Datatypes.S k)) x.
Proof.
  intros g k x.
  change (qpoly_mul (cons 0%Q (cons 1%Q nil)) g)
    with (qpoly_add (qpoly_scalar 0%Q g) (cons 0%Q (qpoly_mul (cons 1%Q nil) g))).
  rewrite (lw0_qp_ai_add (qpoly_scalar 0%Q g) (cons 0%Q (qpoly_mul (cons 1%Q nil) g)) k x).
  rewrite (lw0_qp_ai_scalar 0%Q g k x).
  rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (cons 1%Q nil) g) k x).
  change (qpoly_mul (cons 1%Q nil) g)
    with (qpoly_add (qpoly_scalar 1%Q g) (cons 0%Q (qpoly_mul (@nil Q) g))).
  change (qpoly_mul (@nil Q) g) with (@nil Q).
  rewrite (lw0_qp_ai_add (qpoly_scalar 1%Q g) (cons 0%Q (@nil Q)) (Datatypes.S k) x).
  rewrite (lw0_qp_ai_scalar 1%Q g (Datatypes.S k) x).
  rewrite (lw0_qp_ai_zero_head_eval (@nil Q) (Datatypes.S k) x).
  change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S (Datatypes.S k))) x) with 0%Q.
  ring.
Qed.

Lemma lw0_pitB_ai_mulA : forall A B C k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (qpoly_mul A B) C) k) x
  == qpoly_eval (lw0_qp_ai (qpoly_mul A (qpoly_mul B C)) k) x.
Proof.
  induction A as [|a A IH]; intros B C k x.
  - change (qpoly_mul (@nil Q) B) with (@nil Q).
    change (qpoly_mul (@nil Q) (qpoly_mul B C)) with (@nil Q).
    reflexivity.
  - change (qpoly_mul (cons a A) B)
      with (qpoly_add (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B))).
    rewrite (lw0_qp_ai_mul_add_l (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B)) C k x).
    rewrite (lw0_qp_ai_mul_scalar_l a B C k x).
    change (qpoly_mul (cons 0%Q (qpoly_mul A B)) C)
      with (qpoly_add (qpoly_scalar 0%Q C) (cons 0%Q (qpoly_mul (qpoly_mul A B) C))).
    rewrite (lw0_qp_ai_add (qpoly_scalar 0%Q C) (cons 0%Q (qpoly_mul (qpoly_mul A B) C)) k x).
    rewrite (lw0_qp_ai_scalar 0%Q C k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul (qpoly_mul A B) C) k x).
    change (qpoly_mul (cons a A) (qpoly_mul B C))
      with (qpoly_add (qpoly_scalar a (qpoly_mul B C))
              (cons 0%Q (qpoly_mul A (qpoly_mul B C)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (qpoly_mul B C))
               (cons 0%Q (qpoly_mul A (qpoly_mul B C))) k x).
    rewrite (lw0_qp_ai_scalar a (qpoly_mul B C) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul A (qpoly_mul B C)) k x).
    rewrite (IH B C (Datatypes.S k) x).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

Lemma lw0_pitB_ai_monoL : forall p g k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_mono p) g) k) x
  == q_pow x p * qpoly_eval (lw0_qp_ai g (k + p)) x.
Proof.
  induction p as [|p IH]; intros g k x.
  - change (lw0_pi_mono 0) with (cons 1%Q nil).
    change (qpoly_mul (cons 1%Q nil) g)
      with (qpoly_add (qpoly_scalar 1%Q g) (cons 0%Q (qpoly_mul (@nil Q) g))).
    change (qpoly_mul (@nil Q) g) with (@nil Q).
    rewrite (lw0_qp_ai_add (qpoly_scalar 1%Q g) (cons 0%Q (@nil Q)) k x).
    rewrite (lw0_qp_ai_scalar 1%Q g k x).
    rewrite (lw0_qp_ai_zero_head_eval (@nil Q) k x).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) x) with 0%Q.
    change (q_pow x 0) with 1%Q.
    replace (k + 0)%nat with k by ring.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (lw0_pi_mono (Datatypes.S p))
      with (qpoly_mul (lw0_pi_mono p) (cons 0%Q (cons 1%Q nil))).
    rewrite (lw0_pitB_ai_mulA (lw0_pi_mono p) (cons 0%Q (cons 1%Q nil)) g k x).
    rewrite (IH (qpoly_mul (cons 0%Q (cons 1%Q nil)) g) k x).
    rewrite (lw0_pitB_ai_mul01 g (k + p)%nat x).
    rewrite (q_pow_succ x p).
    replace (k + Datatypes.S p)%nat with (Datatypes.S (k + p)) by ring.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

Lemma lw0_pitB_ai_pair2 : forall g a b k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul g (cons a (cons b nil))) k) x
  == a * qpoly_eval (lw0_qp_ai g k) x
     + b * (x * qpoly_eval (lw0_qp_ai g (Datatypes.S k)) x).
Proof.
  induction g as [|c g IH]; intros a b k x.
  - change (qpoly_mul (@nil Q) (cons a (cons b nil))) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) x) with 0%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (qpoly_mul (cons c g) (cons a (cons b nil)))
      with (qpoly_add (qpoly_scalar c (cons a (cons b nil)))
              (cons 0%Q (qpoly_mul g (cons a (cons b nil))))).
    rewrite (lw0_qp_ai_add (qpoly_scalar c (cons a (cons b nil)))
               (cons 0%Q (qpoly_mul g (cons a (cons b nil)))) k x).
    rewrite (lw0_qp_ai_scalar c (cons a (cons b nil)) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul g (cons a (cons b nil))) k x).
    rewrite (IH a b (Datatypes.S k) x).
    rewrite (lw0_qp_ai_cons_eval a (cons b nil) k x).
    rewrite (lw0_qp_ai_cons_eval b (@nil Q) (Datatypes.S k) x).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S (Datatypes.S k))) x) with 0%Q.
    rewrite (lw0_qp_ai_cons_eval c g k x).
    rewrite (lw0_qp_ai_cons_eval c g (Datatypes.S k) x).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

Lemma lw0_pitB_div_scale : forall a d E : Q, ~ E == 0 -> a / d == a * E / (E * d).
Proof.
  intros a d E HE.
  unfold Qdiv.
  rewrite Qinv_mult_distr.
  assert (Hm : (a * E * (Qinv E * Qinv d))%Q == ((a * (E * Qinv E)) * Qinv d)%Q) by ring.
  rewrite Hm.
  rewrite (Qmult_inv_r E HE).
  ring.
Qed.

Lemma lw0_pitB_E : forall n q k,
  qpoly_eval (lw0_qp_ai (lw0_pi_qminus_pow q n) k) q
  == q_pow q n * q_fact n * q_fact k / q_fact (n + k + 1).
Proof.
  intros n q. induction n as [|n IH]; intros k.
  - change (lw0_pi_qminus_pow q 0) with (cons 1%Q nil).
    rewrite (lw0_qp_ai_cons_eval 1%Q (@nil Q) k q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) q) with 0%Q.
    change (q_pow q 0) with 1%Q.
    change (q_fact 0) with 1%Q.
    replace (0 + k + 1)%nat with (Datatypes.S k)
      by (rewrite Nat.add_0_l, Nat.add_1_r; reflexivity).
    rewrite (q_fact_succ k).
    assert (Hk0 : ~ q_fact k == 0%Q).
    { intro Hc. apply (Qlt_not_eq 0 (q_fact k) (q_fact_pos k)).
      symmetry. exact Hc. }
    assert (Hm2 : (1 * 1 * q_fact k * (Qinv (Z.of_nat (Datatypes.S k) # 1) * Qinv (q_fact k)))%Q
                  == ((1 * 1 * (q_fact k * Qinv (q_fact k))) * Qinv (Z.of_nat (Datatypes.S k) # 1))%Q) by ring.
    assert (Hbase : (1 * 1 * q_fact k / ((Z.of_nat (Datatypes.S k) # 1) * q_fact k)
                     == 1 / (Z.of_nat (Datatypes.S k) # 1))%Q).
    { unfold Qdiv. rewrite Qinv_mult_distr. rewrite Hm2.
      rewrite (Qmult_inv_r (q_fact k) Hk0). ring. }
    rewrite Hbase. unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (lw0_pi_qminus_pow q (Datatypes.S n))
      with (qpoly_mul (lw0_pi_qminus_pow q n) (cons q (cons (-1)%Q nil))).
    rewrite (lw0_pitB_ai_pair2 (lw0_pi_qminus_pow q n) q (-1)%Q k q).
    rewrite (IH k). rewrite (IH (Datatypes.S k)).
    change (q_pow q (Datatypes.S n)) with (q * q_pow q n)%Q.
    rewrite (q_fact_succ n). rewrite (q_fact_succ k).
    replace (n + Datatypes.S k + 1)%nat with (Datatypes.S (n + k + 1)) by ring.
    replace (Datatypes.S n + k + 1)%nat with (Datatypes.S (n + k + 1)) by ring.
    rewrite (q_fact_succ (n + k + 1)).
    assert (Hz : (Z.of_nat (Datatypes.S (n + k + 1))
                  = (Z.of_nat (Datatypes.S n) + Z.of_nat (Datatypes.S k)))%Z).
    { rewrite <- (Nat2Z.inj_add (Datatypes.S n) (Datatypes.S k)). f_equal. ring. }
    assert (Hzq : (Z.of_nat (Datatypes.S (n + k + 1)) # 1)%Q
                  == ((Z.of_nat (Datatypes.S n) # 1) + (Z.of_nat (Datatypes.S k) # 1))%Q).
    { rewrite Hz. symmetry. apply lw0_Qmake_plus. }
    rewrite Hzq.
    assert (HE : ~ ((Z.of_nat (Datatypes.S n) # 1) + (Z.of_nat (Datatypes.S k) # 1))%Q == 0%Q).
    { intros Hc.
      assert (H1 : Qlt 0 (Z.of_nat (Datatypes.S n) # 1))
        by (apply QltT_to_Qlt; apply lw0_q_of_nat_lt0T_S).
      assert (H2 : Qlt 0 (Z.of_nat (Datatypes.S k) # 1))
        by (apply QltT_to_Qlt; apply lw0_q_of_nat_lt0T_S).
      assert (Hs : Qlt (0 + 0)%Q ((Z.of_nat (Datatypes.S n) # 1)
                                   + (Z.of_nat (Datatypes.S k) # 1))%Q)
        by (apply Qplus_lt_compat; [exact H1 | exact H2]).
      rewrite Qplus_0_l in Hs.
      apply (Qlt_not_eq 0 ((Z.of_nat (Datatypes.S n) # 1)
                           + (Z.of_nat (Datatypes.S k) # 1))%Q Hs).
      symmetry. exact Hc. }
    rewrite (lw0_pitB_div_scale (q_pow q n * q_fact n * q_fact k)
                  (q_fact (n + k + 1))
                  ((Z.of_nat (Datatypes.S n) # 1) + (Z.of_nat (Datatypes.S k) # 1))%Q
                  HE).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

Lemma lw0_pitB_ai_sin_aux : forall j acc k x,
  qpoly_eval (lw0_qp_ai (lw0_sin_aux j acc) k) x
  == qpoly_eval (lw0_qp_ai (lw0_sin_qp j) k) x
     + q_pow x (Datatypes.S (Datatypes.S (2 * j)))
       * qpoly_eval (lw0_qp_ai acc (k + Datatypes.S (Datatypes.S (2 * j)))) x.
Proof.
  induction j as [|M IH]; intros acc k x.
  - change (lw0_sin_aux 0 acc)
      with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q acc)).
    rewrite (lw0_qp_ai_zero_head_eval (cons (q_pow (-1) 0 / q_fact 1)%Q acc) k x).
    rewrite (lw0_qp_ai_cons_eval (q_pow (-1) 0 / q_fact 1)%Q acc (Datatypes.S k) x).
    change (lw0_sin_qp 0) with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q (@nil Q))).
    rewrite (lw0_qp_ai_zero_head_eval (cons (q_pow (-1) 0 / q_fact 1)%Q (@nil Q)) k x).
    rewrite (lw0_qp_ai_cons_eval (q_pow (-1) 0 / q_fact 1)%Q (@nil Q) (Datatypes.S k) x).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S (Datatypes.S k))) x) with 0%Q.
    change (Datatypes.S (Datatypes.S (2 * 0))) with 2%nat.
    replace (k + 2)%nat with (Datatypes.S (Datatypes.S k)) by ring.
    cbn [q_pow].
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - set (c := (q_pow (-1) (Datatypes.S M)
               / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%Q).
    change (lw0_sin_aux (Datatypes.S M) acc) with (lw0_sin_aux M (cons 0%Q (cons c acc))).
    change (lw0_sin_qp (Datatypes.S M)) with (lw0_sin_aux M (cons 0%Q (cons c (@nil Q)))).
    rewrite (IH (cons 0%Q (cons c acc)) k x).
    rewrite (IH (cons 0%Q (cons c (@nil Q))) k x).
    rewrite (lw0_qp_ai_zero_head_eval (cons c acc)
               (k + Datatypes.S (Datatypes.S (2 * M))) x).
    rewrite (lw0_qp_ai_zero_head_eval (cons c (@nil Q))
               (k + Datatypes.S (Datatypes.S (2 * M))) x).
    rewrite (lw0_qp_ai_cons_eval c acc
               (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * M)))) x).
    rewrite (lw0_qp_ai_cons_eval c (@nil Q)
               (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * M)))) x).
    change (qpoly_eval (lw0_qp_ai (@nil Q)
              (Datatypes.S (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * M)))))) x)
      with 0%Q.
    replace (Datatypes.S (Datatypes.S (2 * Datatypes.S M)))
      with (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))) by ring.
    replace (k + Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))%nat
      with (Datatypes.S (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * M))))) by ring.
    change (q_pow x (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * M))))))
      with (x * (x * q_pow x (Datatypes.S (Datatypes.S (2 * M))))%Q)%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

Lemma lw0_pitB_ai_mul_sin_aux : forall F j acc k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul F (lw0_sin_aux j acc)) k) x
  == qpoly_eval (lw0_qp_ai (qpoly_mul F (lw0_sin_qp j)) k) x
     + q_pow x (Datatypes.S (Datatypes.S (2 * j)))
       * qpoly_eval (lw0_qp_ai (qpoly_mul F acc)
                              (k + Datatypes.S (Datatypes.S (2 * j)))) x.
Proof.
  induction F as [|a F IH]; intros j acc k x.
  - change (qpoly_mul (@nil Q) (lw0_sin_aux j acc)) with (@nil Q).
    change (qpoly_mul (@nil Q) (lw0_sin_qp j)) with (@nil Q).
    change (qpoly_mul (@nil Q) acc) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    change (qpoly_eval (lw0_qp_ai (@nil Q) (k + Datatypes.S (Datatypes.S (2 * j)))) x)
      with 0%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (qpoly_mul (cons a F) (lw0_sin_aux j acc))
      with (qpoly_add (qpoly_scalar a (lw0_sin_aux j acc))
              (cons 0%Q (qpoly_mul F (lw0_sin_aux j acc)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (lw0_sin_aux j acc))
               (cons 0%Q (qpoly_mul F (lw0_sin_aux j acc))) k x).
    rewrite (lw0_qp_ai_scalar a (lw0_sin_aux j acc) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F (lw0_sin_aux j acc)) k x).
    rewrite (lw0_pitB_ai_sin_aux j acc k x).
    rewrite (IH j acc (Datatypes.S k) x).
    change (qpoly_mul (cons a F) (lw0_sin_qp j))
      with (qpoly_add (qpoly_scalar a (lw0_sin_qp j))
              (cons 0%Q (qpoly_mul F (lw0_sin_qp j)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (lw0_sin_qp j))
               (cons 0%Q (qpoly_mul F (lw0_sin_qp j))) k x).
    rewrite (lw0_qp_ai_scalar a (lw0_sin_qp j) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F (lw0_sin_qp j)) k x).
    change (qpoly_mul (cons a F) acc)
      with (qpoly_add (qpoly_scalar a acc) (cons 0%Q (qpoly_mul F acc))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a acc) (cons 0%Q (qpoly_mul F acc))
               (k + Datatypes.S (Datatypes.S (2 * j))) x).
    rewrite (lw0_qp_ai_scalar a acc (k + Datatypes.S (Datatypes.S (2 * j))) x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F acc)
               (k + Datatypes.S (Datatypes.S (2 * j))) x).
    replace (Datatypes.S (k + Datatypes.S (Datatypes.S (2 * j))))%nat
      with (Datatypes.S k + Datatypes.S (Datatypes.S (2 * j)))%nat by ring.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

Lemma lw0_pitB_ai_mul_cons0 : forall F w k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul F (cons 0%Q w)) k) x
  == x * qpoly_eval (lw0_qp_ai (qpoly_mul F w) (Datatypes.S k)) x.
Proof.
  induction F as [|a F IH]; intros w k x.
  - change (qpoly_mul (@nil Q) (cons 0%Q w)) with (@nil Q).
    change (qpoly_mul (@nil Q) w) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) x) with 0%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (qpoly_mul (cons a F) (cons 0%Q w))
      with (qpoly_add (qpoly_scalar a (cons 0%Q w))
              (cons 0%Q (qpoly_mul F (cons 0%Q w)))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (cons 0%Q w))
               (cons 0%Q (qpoly_mul F (cons 0%Q w))) k x).
    rewrite (lw0_qp_ai_scalar a (cons 0%Q w) k x).
    rewrite (lw0_qp_ai_zero_head_eval w k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F (cons 0%Q w)) k x).
    rewrite (IH w (Datatypes.S k) x).
    change (qpoly_mul (cons a F) w)
      with (qpoly_add (qpoly_scalar a w) (cons 0%Q (qpoly_mul F w))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a w) (cons 0%Q (qpoly_mul F w))
               (Datatypes.S k) x).
    rewrite (lw0_qp_ai_scalar a w (Datatypes.S k) x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F w) (Datatypes.S k) x).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

Lemma lw0_pitB_ai_mul_cons1 : forall F c k x,
  qpoly_eval (lw0_qp_ai (qpoly_mul F (cons c%Q (@nil Q))) k) x
  == c * qpoly_eval (lw0_qp_ai F k) x.
Proof.
  induction F as [|a F IH]; intros c k x.
  - change (qpoly_mul (@nil Q) (cons c%Q (@nil Q))) with (@nil Q).
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    change (qpoly_eval (lw0_qp_ai (@nil Q) k) x) with 0%Q.
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
  - change (qpoly_mul (cons a F) (cons c%Q (@nil Q)))
      with (qpoly_add (qpoly_scalar a (cons c%Q (@nil Q)))
              (cons 0%Q (qpoly_mul F (cons c%Q (@nil Q))))).
    rewrite (lw0_qp_ai_add (qpoly_scalar a (cons c%Q (@nil Q)))
               (cons 0%Q (qpoly_mul F (cons c%Q (@nil Q)))) k x).
    rewrite (lw0_qp_ai_scalar a (cons c%Q (@nil Q)) k x).
    rewrite (lw0_qp_ai_zero_head_eval (qpoly_mul F (cons c%Q (@nil Q))) k x).
    rewrite (IH c (Datatypes.S k) x).
    rewrite (lw0_qp_ai_cons_eval c (@nil Q) k x).
    change (qpoly_eval (lw0_qp_ai (@nil Q) (Datatypes.S k)) x) with 0%Q.
    rewrite (lw0_qp_ai_cons_eval a F k x).
    unfold Qdiv. rewrite ?Qinv_mult_distr. ring.
Qed.

Lemma lw0_pitB_acc_S : forall sg f k m,
  altsum_acc sg f k (Datatypes.S m)
  == altsum_acc sg f k m
     + (if sg then q_pow (-1) m else Qopp (q_pow (-1) m)) * f (k + m)%nat.
Proof.
  intros sg f k m. revert sg k.
  induction m as [|m IH]; intros sg k.
  - cbn [altsum_acc].
    replace (k + 0)%nat with k by ring.
    destruct sg; cbn [q_pow]; ring.
  - assert (Hstep : forall (sg0 : bool) (j n : nat),
        altsum_acc sg0 f j (Datatypes.S n)
        == (if sg0 then f j else Qopp (f j))
           + altsum_acc (negb sg0) f (Datatypes.S j) n)
      by (intros sg0 j n; destruct sg0; reflexivity).
    rewrite (Hstep sg k (Datatypes.S m)).
    rewrite (Hstep sg k m).
    rewrite (IH (negb sg) (Datatypes.S k)).
    replace (Datatypes.S k + m)%nat with (k + Datatypes.S m)%nat by ring.
    change (q_pow (-1) (Datatypes.S m)) with ((-1) * q_pow (-1) m)%Q.
    destruct sg; cbn [negb]; ring.
Qed.

Lemma lw0_pitB_altsum_S : forall W m,
  altsum W (Datatypes.S m) == altsum W m + q_pow (-1) m * W m.
Proof.
  intros W m. unfold altsum.
  rewrite (lw0_pitB_acc_S true W 0 m).
  replace (0 + m)%nat with m by reflexivity.
  reflexivity.
Qed.

Lemma lw0_pitB_q_pow_add : forall (x : Q) (a b : nat),
  q_pow x (a + b)%nat == q_pow x a * q_pow x b.
Proof.
  intros x a b. induction a as [|a IH].
  - replace (0 + b)%nat with b by reflexivity.
    cbn [q_pow]. ring.
  - replace (Datatypes.S a + b)%nat with (Datatypes.S (a + b)) by ring.
    cbn [q_pow]. rewrite IH. ring.
Qed.

Lemma lw0_pitB_Qeq_cancel_l : forall (z X Y : Q),
  ~ z == 0 -> z * X == z * Y -> X == Y.
Proof.
  intros z X Y Hz H.
  assert (Hs : (Qinv z * (z * X))%Q == (Qinv z * (z * Y))%Q)
    by (rewrite H; reflexivity).
  assert (Hm : (Qinv z * (z * X))%Q == ((z * Qinv z) * X)%Q) by ring.
  assert (Hm2 : (Qinv z * (z * Y))%Q == ((z * Qinv z) * Y)%Q) by ring.
  rewrite Hm in Hs. rewrite Hm2 in Hs.
  rewrite (Qmult_inv_r z Hz) in Hs.
  rewrite (Qmult_1_l X) in Hs. rewrite (Qmult_1_l Y) in Hs.
  exact Hs.
Qed.

Lemma lw0_pitB_bridge_aux : forall (n : nat) (b q : Q) (m : nat),
  q_fact n * (q_fact n * altsum (lw0_Wb b q n) (Datatypes.S m))
  == q_pow b n * (q * (q_pow q n
       * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n) (lw0_sin_qp m)) n) q)).
Proof.
  intros n b q. induction m as [|m IH].
  - unfold altsum. cbn [altsum_acc].
    change (lw0_sin_qp 0) with (cons 0%Q (cons (q_pow (-1) 0 / q_fact 1)%Q (@nil Q))).
    rewrite (lw0_pitB_ai_mul_cons0 (lw0_pi_qminus_pow q n)
               (cons (q_pow (-1) 0 / q_fact 1)%Q (@nil Q)) n q).
    rewrite (lw0_pitB_ai_mul_cons1 (lw0_pi_qminus_pow q n)
               (q_pow (-1) 0 / q_fact 1)%Q (Datatypes.S n) q).
    rewrite (lw0_pitB_E n q (Datatypes.S n)).
    unfold lw0_Wb.
    replace (n + 2 * 0 + 1)%nat with (Datatypes.S n) by ring.
    replace (n + Datatypes.S n + 1)%nat with (2 * n + 2 * 0 + 2)%nat by ring.
    rewrite (q_fact_succ n).
    replace (2 * 0 + 1)%nat with 1%nat by ring.
    change (q_fact 1) with ((Z.of_nat 1 # 1) * q_fact 0)%Q.
    change (q_fact 0) with 1%Q.
    change (q_pow (-1) 0) with 1%Q.
    replace (2 * n + 2 * 0 + 2)%nat with (Datatypes.S n + Datatypes.S n)%nat by ring.
    rewrite (lw0_pitB_q_pow_add q (Datatypes.S n) (Datatypes.S n)).
    rewrite (lw0_q_pow_S q n).
    unfold Qdiv. rewrite ?Qinv_mult_distr.
    assert (Hn0 : ~ q_fact n == 0%Q).
    { intro Hc. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)).
      symmetry. exact Hc. }
    assert (Hc1 : (q_pow b n * (q * q_pow q n * (q * q_pow q n)) *
                    ((Z.of_nat (S n) # 1) * q_fact n) *
                    (/ q_fact n * (/ (Z.of_nat 1 # 1) * / 1)
                       * / q_fact (S n + S n)))%Q
                  == (q_pow b n * (q * q_pow q n * (q * q_pow q n)) *
                      (Z.of_nat (S n) # 1) * (q_fact n * / q_fact n)
                      * (/ (Z.of_nat 1 # 1) * / 1) * / q_fact (S n + S n))%Q)
      by ring.
    rewrite Hc1. rewrite (Qmult_inv_r (q_fact n) Hn0).
    ring.
  - rewrite (lw0_pitB_altsum_S (lw0_Wb b q n) (Datatypes.S m)).
    assert (Hsp : (q_fact n * (q_fact n
                    * (altsum (lw0_Wb b q n) (Datatypes.S m)
                       + q_pow (-1) (Datatypes.S m) * lw0_Wb b q n (Datatypes.S m))))%Q
                  == (q_fact n * (q_fact n * altsum (lw0_Wb b q n) (Datatypes.S m))
                      + q_fact n * (q_fact n * (q_pow (-1) (Datatypes.S m) * lw0_Wb b q n (Datatypes.S m))))%Q)
      by ring.
    rewrite Hsp. rewrite IH.
    change (lw0_sin_qp (Datatypes.S m))
      with (lw0_sin_aux m (cons 0%Q
              (cons (q_pow (-1) (Datatypes.S m)
                      / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%Q
                 (@nil Q)))).
    rewrite (lw0_pitB_ai_mul_sin_aux (lw0_pi_qminus_pow q n) m
               (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S m)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%Q
                     (@nil Q))) n q).
    replace (n + Datatypes.S (Datatypes.S (2 * m)))%nat with (n + 2 * m + 2)%nat by ring.
    rewrite (lw0_pitB_ai_mul_cons0 (lw0_pi_qminus_pow q n)
               (cons (q_pow (-1) (Datatypes.S m)
                       / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%Q
                  (@nil Q)) (n + 2 * m + 2)%nat q).
    rewrite (lw0_pitB_ai_mul_cons1 (lw0_pi_qminus_pow q n)
               (q_pow (-1) (Datatypes.S m)
                / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%Q
               (Datatypes.S (n + 2 * m + 2)) q).
    rewrite (lw0_pitB_E n q (Datatypes.S (n + 2 * m + 2))).
    replace (n + Datatypes.S (n + 2 * m + 2) + 1)%nat
      with (2 * n + 2 * Datatypes.S m + 2)%nat by ring.
    unfold lw0_Wb.
    replace (2 * Datatypes.S m + 1)%nat
      with (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))%nat by ring.
    replace (n + 2 * Datatypes.S m + 1)%nat
      with (Datatypes.S (n + 2 * m + 2))%nat by ring.
    rewrite (q_fact_succ (n + 2 * m + 2)).
    replace (2 * n + 2 * Datatypes.S m + 2)%nat
      with (Datatypes.S n + (n + Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))%nat by ring.
    rewrite (lw0_pitB_q_pow_add q (Datatypes.S n)
               (n + Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))).
    rewrite (lw0_pitB_q_pow_add q n
               (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))).
    change (q_pow q (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))
      with (q * q_pow q (Datatypes.S (Datatypes.S (2 * m))))%Q.
    rewrite (lw0_q_pow_S q n).
    unfold Qdiv. rewrite ?Qinv_mult_distr.
    assert (Hn0 : ~ q_fact n == 0%Q).
    { intro Hc. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)).
      symmetry. exact Hc. }
    assert (Hc1 : (q_fact n *
                    (q_fact n *
                     (q_pow (-1) (S m) *
                      (q_pow b n * (q * q_pow q n * (q_pow q n * (q * q_pow q (S (S (2 * m)))))) *
                       ((Z.of_nat (S (n + 2 * m + 2)) # 1) * q_fact (n + 2 * m + 2)) *
                       (/ q_fact n * / q_fact (S (S (S (2 * m)))) *
                        / q_fact (S n + (n + S (S (S (2 * m))))))))))%Q
                  == (q_fact n *
                      (q_pow (-1) (S m) *
                       (q_pow b n * (q * q_pow q n * (q_pow q n * (q * q_pow q (S (S (2 * m)))))) *
                        (Z.of_nat (S (n + 2 * m + 2)) # 1) * q_fact (n + 2 * m + 2) *
                        (q_fact n * / q_fact n) * / q_fact (S (S (S (2 * m)))) *
                        / q_fact (S n + (n + S (S (S (2 * m))))))))%Q)
      by ring.
    rewrite Hc1. rewrite (Qmult_inv_r (q_fact n) Hn0).
    ring.
Qed.

Lemma lw0_pitB_bridge : forall (m : nat) (b q : Q) (n : nat),
  altsum (lw0_Wb b q n) (Datatypes.S m)
  == 1 / q_fact n * lw0_qp_pair (lw0_niven_f q b n) (lw0_sin_qp m) q.
Proof.
  intros m b q n.
  assert (Hn0 : ~ q_fact n == 0%Q).
  { intro Hc. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)).
    symmetry. exact Hc. }
  unfold lw0_niven_f.
  rewrite (lw0_qp_pair_scalar_l (q_pow b n / q_fact n)
             (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)) (lw0_sin_qp m) q).
  unfold lw0_qp_pair, lw0_qp_antideriv.
  change (qpoly_eval
            (cons 0
               (lw0_qp_ai
                  (qpoly_mul
                     (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)) (lw0_sin_qp m)) 0)) q)
    with (0 + q * qpoly_eval
            (lw0_qp_ai
               (qpoly_mul
                  (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)) (lw0_sin_qp m)) 0) q).
  rewrite (lw0_pitB_ai_mulA (lw0_pi_mono n) (lw0_pi_qminus_pow q n) (lw0_sin_qp m) 0 q).
  rewrite (lw0_pitB_ai_monoL n (qpoly_mul (lw0_pi_qminus_pow q n) (lw0_sin_qp m)) 0 q).
  replace (0 + n)%nat with n by reflexivity.
  assert (Haux := lw0_pitB_bridge_aux n b q m).
  assert (Hpack : (q_fact n * (q_fact n
                   * (1 / q_fact n
                      * (q_pow b n / q_fact n
                         * (0 + q * (q_pow q n
                              * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n)
                                             (lw0_sin_qp m)) n) q))))))%Q
                  == (q_pow b n * (q * (q_pow q n
                       * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n)
                                      (lw0_sin_qp m)) n) q)))%Q).
  { unfold Qdiv.
    assert (Hm : (q_fact n * (q_fact n
                  * (1 * Qinv (q_fact n)
                     * (q_pow b n * Qinv (q_fact n)
                        * (0 + q * (q_pow q n
                             * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n)
                                            (lw0_sin_qp m)) n) q))))))%Q
                 == (q_fact n * Qinv (q_fact n)
                     * (q_fact n * Qinv (q_fact n)
                        * (q_pow b n * (q * (q_pow q n
                             * qpoly_eval (lw0_qp_ai (qpoly_mul (lw0_pi_qminus_pow q n)
                                            (lw0_sin_qp m)) n) q)))))%Q) by ring.
    rewrite Hm.
    assert (Hz1 : (q_fact n * / q_fact n)%Q == 1%Q)
      by exact (Qmult_inv_r (q_fact n) Hn0).
    rewrite Hz1. rewrite ?Qmult_1_l. reflexivity. }
  rewrite <- Hpack in Haux.
  apply (lw0_pitB_Qeq_cancel_l (q_fact n) _ _ Hn0).
  apply (lw0_pitB_Qeq_cancel_l (q_fact n) _ _ Hn0).
  exact Haux.
Qed.

Lemma lw0_pitB_conv_lw0_succ : forall n : nat,
  QeqT (lw0_q_of_nat (Datatypes.S n)) (1 + lw0_q_of_nat n)%Q.
Proof.
  intro n. apply qeq_imp_qeqT. unfold lw0_q_of_nat.
  assert (Ez : Z.of_nat (Datatypes.S n) = (1 + Z.of_nat n)%Z).
  { change (Datatypes.S n) with (1 + n)%nat. rewrite Nat2Z.inj_add. reflexivity. }
  rewrite Ez. apply lw0_Qmake_succ.
Qed.

Lemma lw0_pitB_conv_mult_le_l : forall (p n m : Q),
  QleT' n m -> QleT' 0 p -> QleT' (p * n) (p * m).
Proof.
  intros p n m Hn H0. apply Qle_to_QleT'.
  assert (E : (p * n)%Q == (n * p)%Q) by ring.
  assert (E2 : (p * m)%Q == (m * p)%Q) by ring.
  rewrite E, E2. apply Qmult_le_compat_r;
    [ exact (QleT'_to_Qle _ _ Hn) | exact (QleT'_to_Qle _ _ H0) ].
Qed.

Lemma lw0_pitB_conv_pow2_ge : forall L : nat,
  QleT' (lw0_q_of_nat (Datatypes.S L)) (q_pow (2#1) L).
Proof.
  intro L. induction L as [| L IH].
  - change (q_pow (2#1) 0) with 1%Q.
    change (lw0_q_of_nat 1) with (1#1)%Q.
    apply qleT'_refl.
  - apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S L)))
                       (1 + lw0_q_of_nat (Datatypes.S L))%Q
                       (q_pow (2#1) (Datatypes.S L))).
    + apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (Datatypes.S L)))
                      (1 + lw0_q_of_nat (Datatypes.S L))%Q
                      (qeqT_imp_qeq _ _ (lw0_pitB_conv_lw0_succ (Datatypes.S L)))).
    + apply Qle_to_QleT'.
      apply (Qle_trans (1 + lw0_q_of_nat (Datatypes.S L))%Q
                       (q_pow (2#1) L + q_pow (2#1) L)%Q
                       (q_pow (2#1) (Datatypes.S L))).
      * apply (Qle_trans (1 + lw0_q_of_nat (Datatypes.S L))%Q
                         (lw0_q_of_nat (Datatypes.S L) + q_pow (2#1) L)%Q _).
        -- apply Qplus_le_compat.
           ** exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one L)).
           ** exact (QleT'_to_Qle _ _ IH).
        -- apply Qplus_le_compat.
           ** exact (QleT'_to_Qle _ _ IH).
           ** apply Qle_refl.
      * change (q_pow (2#1) (Datatypes.S L)) with ((2#1) * q_pow (2#1) L)%Q.
        apply qeq_le. ring.
Qed.

Lemma lw0_pitB_conv_half_le1 : forall L : nat, QleT' (q_pow (1#2) L) 1%Q.
Proof.
  intro L. induction L as [| L IH].
  - change (q_pow (1#2) 0) with 1%Q. apply qleT'_refl.
  - apply (qleT'_trans (q_pow (1#2) (Datatypes.S L)) ((1#2) * 1%Q) 1%Q).
    + change (q_pow (1#2) (Datatypes.S L)) with ((1#2) * q_pow (1#2) L)%Q.
      apply (lw0_pitB_conv_mult_le_l (1#2) (q_pow (1#2) L) 1%Q).
      * exact IH.
      * unfold QleT'. reflexivity.
    + unfold QleT'. reflexivity.
Qed.

Lemma lw0_pitB_conv_half_mono : forall a b : nat, (b <= a)%nat ->
  QleT' (q_pow (1#2) a) (q_pow (1#2) b).
Proof.
  intros a b Hba.
  assert (E1 : a%nat = (b + (a - b))%nat).
  { rewrite Nat.add_comm. symmetry. apply Nat.sub_add. exact Hba. }
  assert (Eadd : q_pow (1#2) (b + (a - b))%nat
                 == q_pow (1#2) b * q_pow (1#2) (a - b)) by apply lw0_q_pow_add.
  apply (eq_rect (b + (a - b))%nat (fun n0 : nat => QleT' (q_pow (1#2) n0) (q_pow (1#2) b))).
  - apply (qleT'_trans (q_pow (1#2) (b + (a - b))%nat)
                       (q_pow (1#2) (a - b) * q_pow (1#2) b)
                       (q_pow (1#2) b)).
    + apply qeq_leT'. rewrite Eadd. ring.
    + apply Qle_to_QleT'.
      apply (Qle_trans (q_pow (1#2) (a - b) * q_pow (1#2) b)
                       (1%Q * q_pow (1#2) b) (q_pow (1#2) b)).
      * assert (H02T : QleT' 0 (1#2)%Q) by (unfold QleT'; reflexivity).
        apply (Qmult_le_compat_r (q_pow (1#2) (a - b)) 1%Q (q_pow (1#2) b));
          [ exact (QleT'_to_Qle _ _ (lw0_pitB_conv_half_le1 (a - b)))
          | apply q_pow_nonneg; exact (QleT'_to_Qle _ _ H02T) ].
      * assert (E1l : (1%Q * q_pow (1#2) b)%Q == (q_pow (1#2) b)%Q) by ring.
        rewrite E1l. apply Qle_refl.
  - exact (eq_sym E1).
Qed.

Lemma lw0_pitB_conv_div_mul_cancel : forall (a eps : Q),
  QltT 0 eps -> QeqT (a / eps * eps) a.
Proof.
  intros a eps Heps. apply qeq_imp_qeqT.
  assert (Hne : eps == 0%Q -> False) by (apply qltT_not_eq_zero; exact Heps).
  unfold Qdiv.
  transitivity (a * (eps * / eps))%Q.
  - rewrite <- (Qmult_assoc a%Q (/ eps)%Q eps%Q).
    apply (Qmult_comp a%Q a%Q (Qeq_refl a%Q)).
    apply Qmult_comm.
  - rewrite (Qmult_inv_r eps Hne). apply (Qmult_1_r a%Q).
Qed.

Lemma lw0_pitB_conv_geomscale : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun L : nat => QleT' B (q_pow (2#1) L * eps)).
Proof.
  intros B eps HB Heps.
  assert (HBe : Qle 0 (B / eps)).
  { apply Qmult_le_0_compat;
      [ exact (QleT'_to_Qle _ _ HB)
      | apply Qinv_le_0_compat; apply Qlt_le_weak; apply QltT_to_Qlt; exact Heps ]. }
  assert (Hznat : (0 <= Z.succ (Qceiling (B / eps)))%Z).
  { assert (Hz0 : Qceiling 0%Q = 0%Z) by reflexivity.
    pose proof (Qceiling_resp_le 0%Q (B / eps) HBe) as Hm.
    rewrite Hz0 in Hm. apply Z.le_le_succ_r. exact Hm. }
  assert (HL2 : QleT' ((Qceiling (B / eps) + 1)#1)
                      (lw0_q_of_nat (Z.to_nat (Z.succ (Qceiling (B / eps)))))).
  { unfold lw0_q_of_nat.
    assert (EZ : Z.of_nat (Z.to_nat (Z.succ (Qceiling (B / eps))))
                 = (Qceiling (B / eps) + 1)%Z).
    { rewrite Z2Nat.id by exact Hznat. symmetry. apply Z.add_1_r. }
    apply (qeq_leT' ((Qceiling (B / eps) + 1)#1)
                    ((Z.of_nat (Z.to_nat (Z.succ (Qceiling (B / eps)))))#1)).
    rewrite EZ. apply Qeq_refl. }
  exists (Z.to_nat (Z.succ (Qceiling (B / eps)))).
  assert (Hceil : Qle (B / eps) ((Qceiling (B / eps))#1)) by apply Qle_ceiling.
  apply (qleT'_trans B (B / eps * eps)
                     (q_pow (2#1) (Z.to_nat (Z.succ (Qceiling (B / eps)))) * eps)).
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_div_mul_cancel B eps Heps)).
    apply Qle_refl.
  - apply (qleT'_trans (B / eps * eps) (((Qceiling (B / eps))#1) * eps)
                       (q_pow (2#1) (Z.to_nat (Z.succ (Qceiling (B / eps)))) * eps)).
    + apply Qle_to_QleT'. apply Qmult_le_compat_r;
        [ exact Hceil | apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Heps) ].
    + apply (qleT'_trans (((Qceiling (B / eps))#1) * eps)
                         (((Qceiling (B / eps) + 1)#1) * eps)
                         (q_pow (2#1) (Z.to_nat (Z.succ (Qceiling (B / eps)))) * eps)).
      * apply Qle_to_QleT'. apply Qmult_le_compat_r.
        -- unfold Qle. cbn [Qnum Qden]. rewrite ?Z.mul_1_r.
           apply Z.le_succ_diag_r.
        -- apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Heps).
      * apply (qleT'_trans (((Qceiling (B / eps) + 1)#1) * eps)
                           (lw0_q_of_nat (Z.to_nat (Z.succ (Qceiling (B / eps)))) * eps) _).
        -- apply Qle_to_QleT'. apply Qmult_le_compat_r;
             [ exact (QleT'_to_Qle _ _ HL2)
             | apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Heps) ].
        -- apply Qle_to_QleT'. apply Qmult_le_compat_r.
           ++ apply (Qle_trans
                        (lw0_q_of_nat (Z.to_nat (Z.succ (Qceiling (B / eps)))))
                        (lw0_q_of_nat (S (Z.to_nat (Z.succ (Qceiling (B / eps))))))
                        (q_pow (2#1) (Z.to_nat (Z.succ (Qceiling (B / eps)))))).
            ** exact (QleT'_to_Qle _ _ (lw0_q_of_nat_le_succ (Z.to_nat (Z.succ (Qceiling (B / eps)))))).
            ** exact (QleT'_to_Qle _ _ (lw0_pitB_conv_pow2_ge (Z.to_nat (Z.succ (Qceiling (B / eps)))))).
           ++ apply Qlt_le_weak; exact (QltT_to_Qlt _ _ Heps).
Qed.

Lemma lw0_pitB_conv_qabs_pow : forall (x : Q) (k : nat),
  QeqT (Qabs (q_pow x k)) (q_pow (Qabs x) k).
Proof.
  intros x k. apply qeq_imp_qeqT. induction k as [| k IH].
  - change (q_pow x 0) with 1%Q. change (q_pow (Qabs x) 0) with 1%Q.
    simpl. reflexivity.
  - rewrite (q_pow_succ x k), (q_pow_succ (Qabs x) k), Qabs_Qmult, IH. reflexivity.
Qed.

Lemma lw0_pitB_conv_t_nonneg : forall (c : Q) (k : nat),
  QleT' 0 c -> QleT' 0 (q_pow c k / q_fact k).
Proof.
  intros c k Hc. apply Qle_to_QleT'.
  apply Qmult_le_0_compat.
  - apply q_pow_nonneg. exact (QleT'_to_Qle _ _ Hc).
  - apply Qinv_le_0_compat. apply (Qlt_le_weak 0). apply q_fact_pos.
Qed.

Lemma lw0_pitB_conv_tstep : forall (c : Q) (N : nat),
  QleT' 0 c ->
  QleT' (2 * q_pow c 2)
        (lw0_q_of_nat (Datatypes.S N)
         * lw0_q_of_nat (Datatypes.S (Datatypes.S N))) ->
  QleT' (q_pow c (Datatypes.S (Datatypes.S N)) / q_fact (Datatypes.S (Datatypes.S N)))
        ((1#2) * (q_pow c N / q_fact N)).
Proof.
  intros c N Hc0 H.
  set (D := lw0_q_of_nat (Datatypes.S N)
             * lw0_q_of_nat (Datatypes.S (Datatypes.S N))) in *.
  assert (Hstep : q_fact (Datatypes.S (Datatypes.S N)) == D * q_fact N).
  { unfold D. rewrite (lw0_q_fact_step2 N). ring. }
  assert (Hpos : QltT 0 D).
  { unfold D. apply Qlt_to_QltT. apply Qmult_lt_0_compat;
      [ apply QltT_to_Qlt; apply lw0_q_of_nat_lt0T_S
      | apply QltT_to_Qlt; apply (lw0_q_of_nat_lt0T_S (Datatypes.S N)) ]. }
  assert (HDne : D == 0%Q -> False) by (apply qltT_not_eq_zero; exact Hpos).
  assert (HDinv : D * / D == 1%Q) by (apply Qmult_inv_r; exact HDne).
  assert (Hinvpos : QleT' 0 (/ D)).
  { apply Qle_to_QleT'. apply Qinv_le_0_compat.
    apply (Qlt_le_weak 0). exact (QltT_to_Qlt _ _ Hpos). }
  assert (Hfactor : (q_pow c (Datatypes.S (Datatypes.S N)) / q_fact (Datatypes.S (Datatypes.S N)))%Q
                    == (c * c * / D) * (q_pow c N / q_fact N)).
  { rewrite Hstep.
    rewrite (q_pow_succ c (Datatypes.S N)), (q_pow_succ c N).
    unfold Qdiv.
    rewrite (Qinv_mult_distr D (q_fact N)).
    ring. }
  assert (H2ltT : QltT 0 (2#1)%Q) by (unfold QltT, Qlt_bool; reflexivity).
  assert (Hkey : QleT' (c * c * / D) (1#2)).
  { apply Qle_to_QleT'.
    apply (proj1 (Qmult_le_r (c * c * / D) (1#2) (2#1) (QltT_to_Qlt _ _ H2ltT))).
    assert (Er : (c * c * / D * 2%Q)%Q == (2 * c * c * / D)%Q) by ring.
    assert (E2 : q_pow c 2 == c * c)
      by (rewrite (q_pow_succ c 1), (q_pow_succ c 0);
          change (q_pow c 0) with 1%Q; ring).
    assert (H2c2 : Qle (2 * c * c) D).
    { pose proof (QleT'_to_Qle _ _ H) as Hq.
      rewrite E2 in Hq.
      assert (E23 : (2 * (c * c))%Q == (2 * c * c)%Q) by ring.
      rewrite E23 in Hq. exact Hq. }
    apply (Qle_trans (c * c * / D * 2%Q) (2 * c * c * / D) ((1#2) * 2%Q)).
    - rewrite Er. apply Qle_refl.
    - apply (Qle_trans (2 * c * c * / D) (D * / D) ((1#2) * 2%Q)).
      + apply Qmult_le_compat_r.
        * exact H2c2.
        * exact (QleT'_to_Qle _ _ Hinvpos).
      + assert (Eone : (D * / D)%Q == ((1#2) * 2%Q)%Q).
        { rewrite HDinv. reflexivity. }
        rewrite Eone. apply Qle_refl. }
  apply (qleT'_trans (q_pow c (Datatypes.S (Datatypes.S N)) / q_fact (Datatypes.S (Datatypes.S N)))
                     ((c * c * / D) * (q_pow c N / q_fact N))
                     ((1#2) * (q_pow c N / q_fact N))).
  - apply qeq_leT'. exact Hfactor.
  - apply Qle_to_QleT'. apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Hkey).
    + exact (QleT'_to_Qle _ _ (lw0_pitB_conv_t_nonneg c N Hc0)).
Qed.

Lemma lw0_pitB_conv_half_iter : forall (t : nat -> Q) (L M : nat),
  (forall j : nat, (M <= j)%nat -> QleT' (t (Datatypes.S j)) ((1#2) * t j)) ->
  QleT' (t (M + L)%nat) (t M * q_pow (1#2) L).
Proof.
  intros t L. induction L as [| L IH]; intros M Hhalf.
  - assert (E0 : (M + 0)%nat = M) by apply Nat.add_0_r.
    assert (Hbase : QleT' (t M) (t M * q_pow (1#2) 0)).
    { change (q_pow (1#2) 0) with 1%Q.
      apply (qeq_leT' (t M) (t M * 1%Q)).
      exact (Qeq_sym _ _ (Qmult_1_r (t M))). }
    exact (eq_rect_r (fun n0 : nat => QleT' (t n0) (t M * q_pow (1#2) 0)) Hbase E0).
  - assert (E1 : (M + Datatypes.S L)%nat = (Datatypes.S (M + L))%nat)
      by (rewrite Nat.add_succ_r; reflexivity).
    assert (Hmain : QleT' (t (Datatypes.S ((M + L)%nat))) (t M * q_pow (1#2) (Datatypes.S L))).
    { apply (qleT'_trans (t (Datatypes.S ((M + L)%nat)))
                         ((1#2) * (t M * q_pow (1#2) L))
                         (t M * q_pow (1#2) (Datatypes.S L))).
      - apply (qleT'_trans (t (Datatypes.S ((M + L)%nat)))
                           ((1#2) * t ((M + L)%nat))
                           ((1#2) * (t M * q_pow (1#2) L))).
        + apply Hhalf.
          exact (Nat.le_add_r M L).
        + apply (lw0_pitB_conv_mult_le_l (1#2) (t ((M + L)%nat))
                   (t M * q_pow (1#2) L) (IH M Hhalf)).
          unfold QleT'. reflexivity.
      - apply (qeq_leT' ((1#2) * (t M * q_pow (1#2) L))
                        (t M * q_pow (1#2) (Datatypes.S L))).
        change (q_pow (1#2) (Datatypes.S L))
          with ((1#2) * q_pow (1#2) L)%Q.
        rewrite (Qmult_assoc (t M) (1#2) (q_pow (1#2) L)).
        rewrite <- (Qmult_comm (1#2) (t M)).
        rewrite <- (Qmult_assoc (1#2) (t M) (q_pow (1#2) L)).
        apply Qeq_refl. }
    exact (eq_rect_r (fun n0 : nat => QleT' (t n0) (t M * q_pow (1#2) (Datatypes.S L))) Hmain E1).
Qed.

Lemma lw0_pitB_conv_qthr : forall (c : Q) (K j : nat),
  QleT' c (lw0_q_of_nat (Datatypes.S K)) -> QleT' 0 c -> (K <= j)%nat ->
  QleT' (2 * q_pow c 2)
        (lw0_q_of_nat (Datatypes.S (2 * j))
         * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))).
Proof.
  intros c K j HcK Hc0 Hj.
  assert (Hcj : QleT' c (lw0_q_of_nat (Datatypes.S j))).
  { apply (qleT'_trans c (lw0_q_of_nat (Datatypes.S K)) (lw0_q_of_nat (Datatypes.S j))).
    - exact HcK.
    - assert (Ej : Datatypes.S j%nat = (Datatypes.S K + (j - K))%nat).
      { rewrite Nat.add_succ_l. apply f_equal.
        rewrite Nat.add_comm. symmetry. apply Nat.sub_add. exact Hj. }
      apply (eq_rect (Datatypes.S K + (j - K))%nat
                    (fun n0 : nat => QleT' (lw0_q_of_nat (Datatypes.S K)) (lw0_q_of_nat n0))).
      + apply lw0_q_of_nat_le_add.
      + exact (eq_sym Ej). }
  assert (H2pos : QltT 0 (2#1)%Q) by (unfold QltT, Qlt_bool; reflexivity).
  assert (H2lw : QeqT (2%Q * lw0_q_of_nat (Datatypes.S j))
                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  { assert (E2j : (2 * Datatypes.S j)%nat = Datatypes.S (Datatypes.S (2 * j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * j) 1).
      rewrite (Nat.add_succ_r (2 * j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    apply (eq_rect (2 * Datatypes.S j)%nat
                   (fun n0 : nat => QeqT (2%Q * lw0_q_of_nat (Datatypes.S j))
                                         (lw0_q_of_nat n0))).
    - apply qeq_imp_qeqT. unfold lw0_q_of_nat, Qeq, Qmult. cbn [Qnum Qden].
      rewrite Nat2Z.inj_mul. reflexivity.
    - exact E2j. }
  assert (H2c : QleT' (2 * c) (2 * lw0_q_of_nat (Datatypes.S j))).
  { apply (lw0_pitB_conv_mult_le_l 2%Q c (lw0_q_of_nat (Datatypes.S j)) Hcj).
    unfold QleT'. reflexivity. }
  assert (H2c2 : Qle (2 * c)
                     (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  { apply QleT'_to_Qle.
    apply (qleT'_trans (2 * c) (2 * lw0_q_of_nat (Datatypes.S j))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
    - exact H2c.
    - apply (qeq_leT' (2 * lw0_q_of_nat (Datatypes.S j))
                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
      exact (qeqT_imp_qeq _ _ H2lw). }
  assert (Emul2 : forall k : nat, (2 * k)%nat = (k + k)%nat).
  { intro k. rewrite (Nat.mul_comm 2 k). rewrite (Nat.mul_succ_r k 1).
    rewrite Nat.mul_1_r. reflexivity. }
  assert (Hj2 : (j <= 2 * j)%nat).
  { rewrite (Emul2 j). apply Nat.le_add_r. }
  assert (Ejj : (Datatypes.S j + j)%nat = Datatypes.S (2 * j)%nat).
  { rewrite Nat.add_succ_l. rewrite (Emul2 j). reflexivity. }
  assert (Hmid : QleT' (lw0_q_of_nat (Datatypes.S j))
                       (lw0_q_of_nat (Datatypes.S (2 * j)))).
  { apply (eq_rect (Datatypes.S j + j)%nat
                   (fun n0 : nat => QleT' (lw0_q_of_nat (Datatypes.S j))
                                          (lw0_q_of_nat n0))
                   (lw0_q_of_nat_le_add (Datatypes.S j) j)
                   (Datatypes.S (2 * j))%nat Ejj). }
  apply (qleT'_trans (2 * q_pow c 2) (c * (2 * c))
                     (lw0_q_of_nat (Datatypes.S (2 * j))
                      * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  - apply (qeq_leT' (2 * q_pow c 2) (c * (2 * c))).
    assert (E2 : q_pow c 2 == c * c)
      by (rewrite (q_pow_succ c 1), (q_pow_succ c 0);
          change (q_pow c 0) with 1%Q; ring).
    rewrite E2. rewrite (Qmult_comm c (2%Q * c)).
    rewrite <- (Qmult_assoc 2%Q c c).
    apply Qeq_refl.
  - apply Qle_to_QleT'.
    apply (Qle_trans (c * (2 * c))
                     (lw0_q_of_nat (Datatypes.S j) * (2 * c))
                     (lw0_q_of_nat (Datatypes.S (2 * j))
                      * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
    + apply Qmult_le_compat_r;
        [ exact (QleT'_to_Qle _ _ Hcj)
        | apply Qmult_le_0_compat;
            [ apply (Qlt_le_weak 0%Q (2#1)%Q); exact (QltT_to_Qlt 0%Q (2#1)%Q H2pos)
            | exact (QleT'_to_Qle _ _ Hc0) ] ].
    + apply (Qle_trans (lw0_q_of_nat (Datatypes.S j) * (2 * c))
                       (lw0_q_of_nat (Datatypes.S (2 * j)) * (2 * c)) _).
      * apply Qmult_le_compat_r;
          [ exact (QleT'_to_Qle _ _ Hmid)
          | apply Qmult_le_0_compat;
              [ apply (Qlt_le_weak 0%Q (2#1)%Q); exact (QltT_to_Qlt 0%Q (2#1)%Q H2pos)
              | exact (QleT'_to_Qle _ _ Hc0) ] ].
      * exact (QleT'_to_Qle _ _
                 (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (2 * j)))
                    (2 * c)
                    (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                    (Qle_to_QleT' _ _ H2c2) (lw0_q_of_nat_nonneg (Datatypes.S (2 * j))))).
Qed.

Lemma lw0_pitB_conv_qeqL_ltT : forall (a b c : Q),
  QeqT a b -> QltT b c -> QltT a c.
Proof.
  intros a b c Hab Hbc. apply Qlt_to_QltT.
  apply (Qle_lt_trans a b c).
  - apply (qeq_imp_qle a b). exact (qeqT_imp_qeq _ _ Hab).
  - exact (QltT_to_Qlt b c Hbc).
Qed.

Lemma lw0_pitB_conv_qeqR_ltT : forall (a b c : Q),
  QltT a b -> QeqT b c -> QltT a c.
Proof.
  intros a b c Hab Hbc. apply Qlt_to_QltT.
  apply (Qlt_le_trans a b c).
  - exact (QltT_to_Qlt a b Hab).
  - apply (qeq_imp_qle b c). exact (qeqT_imp_qeq _ _ Hbc).
Qed.

Lemma lw0_pitB_conv_t_vanish : forall (c : Q) (eps : Q),
  QleT' 0 c -> QltT 0 eps ->
  sigT (fun M0 : nat => sigT (fun _ : QleT' c (lw0_q_of_nat (Datatypes.S M0)) =>
    forall M : nat, (M0 <= M)%nat ->
    QltT (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))) eps)).
Proof.
  intros c eps Hc0 Heps.
  assert (Hnum0 : (0 <= Qnum c)%Z).
  { assert (Hq : Qle 0 c) by exact (QleT'_to_Qle _ _ Hc0).
    unfold Qle in Hq. cbn [Qnum Qden] in Hq. rewrite Z.mul_1_r in Hq. exact Hq. }
  set (t := fun j : nat => q_pow c (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))).
  set (M1 := Z.to_nat (Qnum c)).
  assert (Hc1a : Qle c ((Qnum c)#1)).
  { unfold Qle. cbn [Qnum Qden]. rewrite Z.mul_1_r.
    destruct (Z_lt_le_dec 0 (Qnum c)) as [Hpos | Hnonpos].
    - apply (proj1 (Z.le_mul_diag_r (Qnum c) (Z.pos (Qden c)) Hpos)).
      pose proof (Zgt_pos_0 (Qden c)) as Hdp.
      apply (Zlt_le_succ 0). exact (proj1 (Z.gt_lt_iff _ _) Hdp).
    - assert (Hz : Qnum c = 0%Z)
        by (apply Z.le_antisymm; [ exact Hnonpos | exact Hnum0 ]).
      rewrite Hz. apply Z.le_refl. }
  assert (Hc1 : QleT' c (lw0_q_of_nat (Datatypes.S M1))).
  { apply (qleT'_trans c ((Qnum c)#1) (lw0_q_of_nat (Datatypes.S M1))).
    - exact (Qle_to_QleT' _ _ Hc1a).
    - apply (qleT'_trans ((Qnum c)#1) (lw0_q_of_nat M1)
                         (lw0_q_of_nat (Datatypes.S M1))).
      + apply (qeq_leT' ((Qnum c)#1) (lw0_q_of_nat M1)).
        assert (EZ : Z.of_nat (Z.to_nat (Qnum c)) = Qnum c)
          by (apply Z2Nat.id; exact Hnum0).
        unfold lw0_q_of_nat, M1. rewrite EZ. apply Qeq_refl.
      + apply lw0_q_of_nat_le_succ. }
  assert (Hr : forall j : nat, (M1 <= j)%nat ->
           QleT' (2 * q_pow c 2)
                 (lw0_q_of_nat (Datatypes.S (2 * j))
                  * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))).
  { intros j Hj. exact (lw0_pitB_conv_qthr c M1 j Hc1 Hc0 Hj). }
  assert (HhalfM : forall j : nat, (M1 <= j)%nat -> QleT' (t (Datatypes.S j)) ((1#2) * t j)).
  { intros j Hj. unfold t.
    apply (eq_rect (Datatypes.S (Datatypes.S (2 * j))%nat)
                   (fun n0 : nat => QleT' (q_pow c (Datatypes.S n0) / q_fact (Datatypes.S n0))
                                          ((1#2) * (q_pow c (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))))).
    - apply (lw0_pitB_conv_tstep c (Datatypes.S (2 * j)) Hc0).
      apply (qleT'_trans (2 * q_pow c 2)
                         (lw0_q_of_nat (Datatypes.S (2 * j))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
      + exact (Hr j Hj).
      + apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (2 * j)))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
        * apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (2 * j))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (2 * j)))
                           (Qmult_comm (lw0_q_of_nat (Datatypes.S (2 * j)))
                                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))))).
        * apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (2 * j)))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
          -- apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j)))
                                (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
             ++ apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_le_succ.
          -- apply lw0_q_of_nat_nonneg.
    - rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * j) 1).
      rewrite (Nat.add_succ_r (2 * j) 0).
      rewrite Nat.add_0_r. reflexivity. }
  assert (Heps2 : QltT 0 ((1#2) * eps)).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - apply (QltT_to_Qlt 0%Q (1#2)%Q). unfold QltT. reflexivity.
    - exact (QltT_to_Qlt _ _ Heps). }
  destruct (lw0_pitB_conv_geomscale (t M1) ((1#2) * eps)
             (lw0_pitB_conv_t_nonneg c (Datatypes.S (2 * M1)) Hc0) Heps2) as [L HL].
  exists (M1 + L)%nat.
  assert (Hmono2 : QleT' (lw0_q_of_nat (Datatypes.S M1))
                         (lw0_q_of_nat (Datatypes.S (M1 + L)))).
  { apply (eq_rect (Datatypes.S M1 + L)%nat
                   (fun n0 : nat => QleT' (lw0_q_of_nat (Datatypes.S M1))
                                          (lw0_q_of_nat n0))).
    - apply lw0_q_of_nat_le_add.
    - apply Nat.add_succ_l. }
  exists (qleT'_trans c (lw0_q_of_nat (Datatypes.S M1))
                        (lw0_q_of_nat (Datatypes.S (M1 + L))) Hc1 Hmono2).
  intros M HM.
  assert (HMe : (M1 <= M)%nat).
  { apply (Nat.le_trans M1 (M1 + L) M).
    - apply Nat.le_add_r.
    - exact HM. }
  assert (HMm : (L <= M - M1)%nat).
  { rewrite Nat.add_comm in HM. exact (Nat.le_add_le_sub_r L M M1 HM). }
  assert (Hdec : QleT' (t M) (q_pow (1#2) L * t M1)).
  { assert (E1 : (M1 + (M - M1))%nat = M)
      by (rewrite Nat.add_comm; apply Nat.sub_add; exact HMe).
    apply (eq_rect (M1 + (M - M1))%nat
                  (fun n0 : nat => QleT' (t n0) (q_pow (1#2) L * t M1))).
    - apply (qleT'_trans (t ((M1 + (M - M1))%nat))
                         (t M1 * q_pow (1#2) ((M - M1)%nat))
                         (q_pow (1#2) L * t M1)).
      + exact (lw0_pitB_conv_half_iter t (M - M1) M1 HhalfM).
      + apply (qleT'_trans (t M1 * q_pow (1#2) ((M - M1)%nat))
                           (q_pow (1#2) ((M - M1)%nat) * t M1)
                           (q_pow (1#2) L * t M1)).
        * apply (qeq_leT' (t M1 * q_pow (1#2) ((M - M1)%nat))
                          (q_pow (1#2) ((M - M1)%nat) * t M1)).
          exact (Qmult_comm (t M1) (q_pow (1#2) ((M - M1)%nat))).
        * apply Qle_to_QleT'. apply Qmult_le_compat_r.
          -- exact (QleT'_to_Qle _ _
                      (lw0_pitB_conv_half_mono (M - M1) L HMm)).
          -- exact (QleT'_to_Qle _ _
                      (lw0_pitB_conv_t_nonneg c (Datatypes.S (2 * M1)) Hc0)).
    - exact E1. }
  assert (Hchain : QleT' (t M) ((1#2) * eps)).
  { apply (qleT'_trans (t M)
                       (q_pow (1#2) L * t M1)
                       ((1#2) * eps)).
    - exact Hdec.
    - apply (qleT'_trans (q_pow (1#2) L * t M1)
                         (q_pow (1#2) L * (q_pow (2#1) L * ((1#2) * eps)))
                         ((1#2) * eps)).
      + apply (lw0_pitB_conv_mult_le_l (q_pow (1#2) L) (t M1)
                 (q_pow (2#1) L * ((1#2) * eps)) HL).
        apply Qle_to_QleT'. apply q_pow_nonneg.
        apply (Qlt_le_weak 0%Q (1#2)%Q).
        apply (QltT_to_Qlt 0%Q (1#2)%Q).
        unfold QltT. reflexivity.
      + apply (qeq_leT' (q_pow (1#2) L * (q_pow (2#1) L * ((1#2) * eps)))
                        ((1#2) * eps)).
        assert (Ec12 : QeqT ((1#2) * (2#1))%Q 1%Q)
          by (unfold QeqT; cbn; reflexivity).
        rewrite (Qmult_assoc (q_pow (1#2) L) (q_pow (2#1) L) ((1#2) * eps)).
        rewrite (lw0_q_pow_mult (1#2) (2#1) L).
        rewrite (q_pow_wd ((1#2) * (2#1))%Q 1%Q L (qeqT_imp_qeq _ _ Ec12)).
        rewrite (lw0_q_pow_one L).
        apply Qmult_1_l. }
  apply (lw0_leT'_ltT_trans (t M) ((1#2) * eps) eps).
  + exact Hchain.
  + apply Qlt_to_QltT.
    apply (Qlt_le_trans ((1#2) * eps) (1%Q * eps) eps).
    * apply (Qmult_lt_compat_r (1#2)%Q 1%Q eps).
      -- exact (QltT_to_Qlt _ _ Heps).
      -- apply (QltT_to_Qlt 0%Q 1%Q). unfold QltT. reflexivity.
    * apply QleT'_to_Qle. apply (qeq_leT' (1%Q * eps) eps (Qmult_1_l eps)).
Qed.

Fixpoint lw0_pitB_conv_pwi (p : QPoly) (k : nat) (c : Q) : Q :=
  match p with
  | nil => 0%Q
  | cons a p' => Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                 + Qabs c * lw0_pitB_conv_pwi p' (Datatypes.S k) c
  end.

Lemma lw0_pitB_conv_pwi_scalar : forall (a : Q) (p : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (qpoly_scalar a p) k c)
       (Qabs a * lw0_pitB_conv_pwi p k c).
Proof.
  intros a p. induction p as [| b p IH]; intros k c.
  - change (lw0_pitB_conv_pwi (qpoly_scalar a nil) k c) with 0%Q.
    change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply qeq_imp_qeqT. ring.
  - change (lw0_pitB_conv_pwi (qpoly_scalar a (cons b p)) k c)
      with (Qabs (a * b) * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi (qpoly_scalar a p) (Datatypes.S k) c).
    change (Qabs a * lw0_pitB_conv_pwi (cons b p) k c)
      with (Qabs a * (Qabs b * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                       + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)).
    apply qeq_imp_qeqT.
    rewrite Qabs_Qmult.
    rewrite (qeqT_imp_qeq _ _ (IH (Datatypes.S k) c)).
    ring.
Qed.

Lemma lw0_pitB_conv_pwi_add_le : forall (p q : QPoly) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi (qpoly_add p q) k c)
        (lw0_pitB_conv_pwi p k c + lw0_pitB_conv_pwi q k c).
Proof.
  intro p. induction p as [| a p IH]; intros q k c.
  - change (lw0_pitB_conv_pwi (qpoly_add nil q) k c)
      with (lw0_pitB_conv_pwi q k c).
    change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply (qeq_leT' (lw0_pitB_conv_pwi q k c) (0%Q + lw0_pitB_conv_pwi q k c)).
    rewrite Qplus_0_l. apply Qeq_refl.
  - destruct q as [| b q'].
    + change (lw0_pitB_conv_pwi (qpoly_add (cons a p) nil) k c)
        with (lw0_pitB_conv_pwi (cons a p) k c).
      change (lw0_pitB_conv_pwi nil k c) with 0%Q.
      apply (qeq_leT' (lw0_pitB_conv_pwi (cons a p) k c)
                      (lw0_pitB_conv_pwi (cons a p) k c + 0%Q)).
      rewrite Qplus_0_r. apply Qeq_refl.
    + assert (HH0 : QleT' 0 (Qabs c / lw0_q_of_nat (Datatypes.S k))).
      { apply Qle_to_QleT'. apply Qmult_le_0_compat.
        - apply Qabs_nonneg.
        - apply Qinv_le_0_compat. apply Qlt_le_weak.
          apply (Qlt_le_trans 0%Q 1%Q (lw0_q_of_nat (Datatypes.S k))).
          + apply QltT_to_Qlt. unfold QltT. reflexivity.
          + apply QleT'_to_Qle. apply lw0_q_of_nat_ge_one. }
      change (lw0_pitB_conv_pwi (qpoly_add (cons a p) (cons b q')) k c)
        with (Qabs (a + b) * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi (qpoly_add p q') (Datatypes.S k) c).
      change (lw0_pitB_conv_pwi (cons a p) k c)
        with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
      change (lw0_pitB_conv_pwi (cons b q') k c)
        with (Qabs b * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi q' (Datatypes.S k) c).
      apply (qleT'_trans
               (Qabs (a + b) * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                + Qabs c * lw0_pitB_conv_pwi (qpoly_add p q') (Datatypes.S k) c)
               ((Qabs a + Qabs b) * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                + (Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c
                   + Qabs c * lw0_pitB_conv_pwi q' (Datatypes.S k) c))
               (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c
                + (Qabs b * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                   + Qabs c * lw0_pitB_conv_pwi q' (Datatypes.S k) c))).
      * apply Qle_to_QleT'. apply Qplus_le_compat.
        -- apply Qmult_le_compat_r.
           ++ exact (Qabs_triangle a b).
           ++ exact (QleT'_to_Qle _ _ HH0).
        -- apply QleT'_to_Qle.
           apply (qleT'_trans
             (Qabs c * lw0_pitB_conv_pwi (qpoly_add p q') (Datatypes.S k) c)
             (Qabs c * (lw0_pitB_conv_pwi p (Datatypes.S k) c
                       + lw0_pitB_conv_pwi q' (Datatypes.S k) c))
             (Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c
             + Qabs c * lw0_pitB_conv_pwi q' (Datatypes.S k) c)).
           ++ apply (lw0_pitB_conv_mult_le_l (Qabs c)
                    (lw0_pitB_conv_pwi (qpoly_add p q') (Datatypes.S k) c)
                    (lw0_pitB_conv_pwi p (Datatypes.S k) c
                     + lw0_pitB_conv_pwi q' (Datatypes.S k) c)
                    (IH q' (Datatypes.S k) c)).
              apply Qle_to_QleT'. apply Qabs_nonneg.
           ++ apply qeq_leT'. ring.
      * apply qeq_leT'. ring.
Qed.

Lemma lw0_pitB_conv_pwi_mul_le : forall (a : Q) (f g : QPoly) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi (qpoly_mul (cons a f) g) k c)
        (Qabs a * lw0_pitB_conv_pwi g k c
         + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c).
Proof.
  intros a f g k c.
  change (qpoly_mul (cons a f) g)
    with (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g))).
  apply (qleT'_trans
           (lw0_pitB_conv_pwi
              (qpoly_add (qpoly_scalar a g) (cons 0 (qpoly_mul f g))) k c)
           (lw0_pitB_conv_pwi (qpoly_scalar a g) k c
            + lw0_pitB_conv_pwi (cons 0 (qpoly_mul f g)) k c)
           (Qabs a * lw0_pitB_conv_pwi g k c
            + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c)).
  - exact (lw0_pitB_conv_pwi_add_le (qpoly_scalar a g)
             (cons 0 (qpoly_mul f g)) k c).
  - change (lw0_pitB_conv_pwi (cons 0 (qpoly_mul f g)) k c)
      with (Qabs 0 * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c).
    apply (qeq_leT'
             (lw0_pitB_conv_pwi (qpoly_scalar a g) k c
              + (Qabs 0 * (Qabs c / lw0_q_of_nat (Datatypes.S k))
                 + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c))
             (Qabs a * lw0_pitB_conv_pwi g k c
              + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f g) (Datatypes.S k) c)).
    + rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_pwi_scalar a g k c)).
      assert (Ec0 : QeqT (Qabs 0%Q) 0%Q) by (unfold QeqT; cbn; reflexivity).
      rewrite (qeqT_imp_qeq _ _ Ec0).
      ring.
Qed.

Lemma lw0_pitB_conv_pwi_ai_le : forall (p : QPoly) (k : nat) (c : Q),
  QleT' (Qabs (c * qpoly_eval (lw0_qp_ai p k) c))
        (lw0_pitB_conv_pwi p k c).
Proof.
  intro p. induction p as [| a p IH]; intros k c.
  - change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply (qeq_leT' (Qabs (c * qpoly_eval (lw0_qp_ai nil k) c)) 0%Q).
    change (qpoly_eval (lw0_qp_ai nil k) c) with 0%Q.
    rewrite (Qmult_0_r c). apply Qeq_refl.
  - assert (Hltpos : Qlt 0 ((Z.of_nat (Datatypes.S k) # 1)%Q)).
    { apply (Qlt_le_trans 0%Q 1%Q ((Z.of_nat (Datatypes.S k) # 1)%Q)).
      - apply QltT_to_Qlt. unfold QltT. reflexivity.
      - exact (QleT'_to_Qle _ _ (lw0_q_of_nat_ge_one k)). }
    change (lw0_pitB_conv_pwi (cons a p) k c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
    apply (qleT'_trans
             (Qabs (c * qpoly_eval (lw0_qp_ai (cons a p) k) c))
             (Qabs (c * (a / (Z.of_nat (Datatypes.S k) # 1)%Q))
              + Qabs (c * (c * qpoly_eval (lw0_qp_ai p (Datatypes.S k)) c)))
             (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)).
    + apply Qle_to_QleT'.
      rewrite (lw0_qp_ai_cons_eval a p k c).
      assert (Esplit : c * (a / (Z.of_nat (Datatypes.S k) # 1)%Q
                            + c * qpoly_eval (lw0_qp_ai p (Datatypes.S k)) c)
                     == c * (a / (Z.of_nat (Datatypes.S k) # 1)%Q)
                      + c * (c * qpoly_eval (lw0_qp_ai p (Datatypes.S k)) c)) by ring.
      rewrite (Qabs_wd _ _ Esplit).
      apply Qabs_triangle.
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * assert (Ehead : Qabs (c * (a * / (Z.of_nat (Datatypes.S k) # 1)%Q))
                        == Qabs a * (Qabs c * / (Z.of_nat (Datatypes.S k) # 1)%Q)).
        { rewrite Qabs_Qmult, Qabs_Qmult.
          rewrite (lw0_Qabs_pos_eq (Qinv ((Z.of_nat (Datatypes.S k) # 1)%Q)))
            by (apply Qle_to_QleT'; apply Qinv_le_0_compat;
                apply Qlt_le_weak; exact Hltpos).
          ring. }
        unfold Qdiv, lw0_q_of_nat.
        rewrite Ehead. apply Qle_refl.
      * rewrite Qabs_Qmult.
        apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs c)
                 (Qabs (c * qpoly_eval (lw0_qp_ai p (Datatypes.S k)) c))
                 (lw0_pitB_conv_pwi p (Datatypes.S k) c)
                 (IH (Datatypes.S k) c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
Qed.

Lemma lw0_pitB_conv_pair_vanish : forall (tau : nat -> QPoly) (Wg c eps : Q),
  QleT' 0 c -> QltT 0 eps -> QltT 0 Wg ->
  (forall M : nat,
     QleT' (lw0_pitB_conv_pwi (tau M) 0 c)
           (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))) ->
  sigT (fun M0 : nat => forall M : nat, (M0 <= M)%nat ->
    QltT (Qabs (c * qpoly_eval (lw0_qp_ai (tau M) 0) c)) eps).
Proof.
  intros tau Wg c eps Hc0 Heps HWg Hob.
  assert (Hne : Wg == 0%Q -> False) by (intros Hw0; exact (qltT_not_eq_zero Wg HWg Hw0)).
  assert (HepsW : QltT 0 (eps * / Wg)%Q).
  { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
    - exact (QltT_to_Qlt _ _ Heps).
    - apply Qinv_lt_0_compat. exact (QltT_to_Qlt _ _ HWg). }
  destruct (lw0_pitB_conv_t_vanish c (eps * / Wg)%Q Hc0 HepsW)
    as [M0 [_ HM0]].
  exists M0. intros M HM.
  specialize (HM0 M HM).
  apply (lw0_leT'_ltT_trans
           (Qabs (c * qpoly_eval (lw0_qp_ai (tau M) 0) c))
           (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
           eps).
  - apply (qleT'_trans
             (Qabs (c * qpoly_eval (lw0_qp_ai (tau M) 0) c))
             (lw0_pitB_conv_pwi (tau M) 0 c)
             (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))).
    + exact (lw0_pitB_conv_pwi_ai_le (tau M) 0 c).
    + exact (Hob M).
  - apply (lw0_pitB_conv_qeqR_ltT
             (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
             (eps * / Wg * Wg)%Q eps).
    + apply (lw0_pitB_conv_qeqL_ltT
               (Wg * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
               (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)) * Wg)
               (eps * / Wg * Wg)%Q).
      * apply qeq_imp_qeqT. apply Qmult_comm.
      * apply Qlt_to_QltT.
        apply (Qmult_lt_compat_r
                 (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                 (eps * / Wg)%Q Wg).
        -- exact (QltT_to_Qlt _ _ HWg).
        -- exact (QltT_to_Qlt _ _ HM0).
    + apply qeq_imp_qeqT.
      rewrite <- Qmult_assoc, (Qmult_comm (/ Wg)%Q Wg), (Qmult_inv_r Wg Hne).
      apply (Qmult_1_r eps).
Qed.

Lemma lw0_pi_qeq_ltT_r : forall x y e : Q, x == y -> QltT y e -> QltT x e.
Proof.
  intros x y e Hxy Hy.
  unfold QltT, Qlt_bool in Hy.
  assert (Hcmp : (x ?= e)%Q = (y ?= e)%Q)
    by exact (Qcompare_comp x y Hxy e e (Qeq_refl e)).
  unfold QltT, Qlt_bool. rewrite Hcmp. exact Hy.
Qed.

Definition lw0_pitB_pair_rtail (q : Q) (n m : nat) : Q :=
  lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp m) q
  - lw0_K (Qnum q) (Zpos (Qden q)) n
  + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
      * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
  - qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
      * qpoly_eval (lw0_sin_qp m) q.

Lemma lw0_pitB_pair_rtail_vanish_gap : forall (q : Q) (n : nat),
  lw0_K (Qnum q) (Zpos (Qden q)) n
  == qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
     + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q ->
  (forall eps : Q, QltT 0 eps ->
     sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
       QltT (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp m) q
                   - qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
                   - qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                       * qpoly_eval (lw0_sin_qp m) q
                   + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                       * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q)) eps)) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
    QltT (Qabs (lw0_pitB_pair_rtail q n m)) eps).
Proof.
  intros q n HK Hpair eps Heps.
  destruct (Hpair eps Heps) as [Mt HMt].
  exists Mt.
  intros m Hm.
  specialize (HMt m Hm).
  apply (lw0_pi_qeq_ltT_r
           (Qabs (lw0_pitB_pair_rtail q n m))
           (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                              (lw0_sin_qp m) q
                  - qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
                  - qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                      * qpoly_eval (lw0_sin_qp m) q
                  + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                      * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q)) eps).
  - apply Qabs_wd.
    unfold lw0_pitB_pair_rtail.
    rewrite HK.
    ring.
  - exact HMt.
Qed.

Lemma lw0_add_nil_r : forall p : QPoly, qpoly_add p nil = p.
Proof.
  intro p. destruct p as [|a p].
  - reflexivity.
  - reflexivity.
Qed.

Lemma lw0_mul_nil_r_coef : forall (p : QPoly) (j : nat),
  lw0_coef j (qpoly_mul p nil) == 0.
Proof.
  induction p as [|a p IH]; intro j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons a%Q p) nil)
      with (qpoly_add (qpoly_scalar a nil) (cons 0%Q (qpoly_mul p nil))).
    cbn [qpoly_scalar qpoly_add].
    destruct j as [|j']; cbn [lw0_coef].
    + ring.
    + rewrite (IH j'). ring.
Qed.

Lemma lw0_mul_scalar_left : forall (a : Q) (B C : QPoly) (j : nat),
  lw0_coef j (qpoly_mul (qpoly_scalar a B) C)
  == a * lw0_coef j (qpoly_mul B C).
Proof.
  intros a B. induction B as [|b B IH]; intros C j.
  - cbn [qpoly_scalar qpoly_mul lw0_coef]. ring.
  - cbn [qpoly_scalar].
    change (qpoly_mul (cons (a * b)%Q (qpoly_scalar a B)) C)
      with (qpoly_add (qpoly_scalar (a * b)%Q C)
                      (cons 0%Q (qpoly_mul (qpoly_scalar a B) C))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    change (qpoly_mul (cons b%Q B) C)
      with (qpoly_add (qpoly_scalar b C) (cons 0%Q (qpoly_mul B C))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef]. rewrite (IH C j'). ring.
Qed.

Lemma lw0_mul_add_left : forall (U V C : QPoly) (j : nat),
  lw0_coef j (qpoly_mul (qpoly_add U V) C)
  == lw0_coef j (qpoly_mul U C) + lw0_coef j (qpoly_mul V C).
Proof.
  induction U as [|a U IH]; intros V C j.
  - cbn [qpoly_add qpoly_mul lw0_coef]. ring.
  - destruct V as [|c V].
    + rewrite lw0_add_nil_r.
      change (qpoly_mul (cons a%Q U) C)
        with (qpoly_add (qpoly_scalar a C) (cons 0%Q (qpoly_mul U C))).
      rewrite !lw0_coef_add, !lw0_coef_scalar.
      destruct j as [|j']; cbn [lw0_coef qpoly_mul lw0_coef]; ring.
    + cbn [qpoly_add].
      change (qpoly_mul (cons (a + c)%Q (qpoly_add U V)) C)
        with (qpoly_add (qpoly_scalar (a + c)%Q C)
                        (cons 0%Q (qpoly_mul (qpoly_add U V) C))).
      change (qpoly_mul (cons a%Q U) C)
        with (qpoly_add (qpoly_scalar a C) (cons 0%Q (qpoly_mul U C))).
      change (qpoly_mul (cons c%Q V) C)
        with (qpoly_add (qpoly_scalar c C) (cons 0%Q (qpoly_mul V C))).
      rewrite !lw0_coef_add, !lw0_coef_scalar.
      destruct j as [|j'].
      * cbn [lw0_coef]. ring.
      * cbn [lw0_coef]. rewrite (IH V C j'). ring.
Qed.

Lemma lw0_mul_cons0_left : forall (X C : QPoly) (j : nat),
  lw0_coef j (qpoly_mul (cons 0%Q X) C)
  == lw0_coef j (cons 0%Q (qpoly_mul X C)).
Proof.
  intros X C j.
  change (qpoly_mul (cons 0%Q X) C)
    with (qpoly_add (qpoly_scalar 0%Q C) (cons 0%Q (qpoly_mul X C))).
  rewrite lw0_coef_add, lw0_coef_scalar.
  destruct j as [|j']; cbn [lw0_coef]; ring.
Qed.

Lemma lw0_mul_assoc : forall (A B C : QPoly) (j : nat),
  lw0_coef j (qpoly_mul A (qpoly_mul B C))
  == lw0_coef j (qpoly_mul (qpoly_mul A B) C).
Proof.
  induction A as [|a A IH]; intros B C j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons a%Q A) (qpoly_mul B C))
      with (qpoly_add (qpoly_scalar a (qpoly_mul B C))
                      (cons 0%Q (qpoly_mul A (qpoly_mul B C)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    change (qpoly_mul (cons a%Q A) B)
      with (qpoly_add (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B))).
    rewrite lw0_mul_add_left.
    rewrite lw0_mul_scalar_left.
    rewrite lw0_mul_cons0_left.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef]. rewrite (IH B C j'). ring.
Qed.

Lemma lw0_mul_unit_right : forall (X : QPoly) (j : nat),
  lw0_coef j (qpoly_mul X (cons 1%Q nil)) == lw0_coef j X.
Proof.
  induction X as [|a X IH]; intros j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons a%Q X) (cons 1%Q nil))
      with (qpoly_add (qpoly_scalar a (cons 1%Q nil))
                      (cons 0%Q (qpoly_mul X (cons 1%Q nil)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef]. rewrite (IH j'). ring.
Qed.

Lemma lw0_mul_cons0_right : forall (A B : QPoly) (j : nat),
  lw0_coef j (qpoly_mul A (cons 0%Q B))
  == lw0_coef j (cons 0%Q (qpoly_mul A B)).
Proof.
  induction A as [|a A IH]; intros B j.
  - cbn [qpoly_mul lw0_coef]. destruct j as [|j']; ring.
  - change (qpoly_mul (cons a%Q A) (cons 0%Q B))
      with (qpoly_add (qpoly_scalar a (cons 0%Q B))
                      (cons 0%Q (qpoly_mul A (cons 0%Q B)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef]. rewrite (IH B j').
      change (qpoly_mul (cons a%Q A) B)
        with (qpoly_add (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      ring.
Qed.

Lemma lw0_mul_comm : forall (A B : QPoly) (j : nat),
  lw0_coef j (qpoly_mul A B) == lw0_coef j (qpoly_mul B A).
Proof.
  induction A as [|a A IHA]; intros B; induction B as [|b B IHB]; intros j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - rewrite lw0_mul_nil_r_coef. cbn [qpoly_mul lw0_coef]. ring.
  - rewrite lw0_mul_nil_r_coef. cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons a%Q A) (cons b%Q B))
      with (qpoly_add (qpoly_scalar a (cons b%Q B))
                      (cons 0%Q (qpoly_mul A (cons b%Q B)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    change (qpoly_mul (cons b%Q B) (cons a%Q A))
      with (qpoly_add (qpoly_scalar b (cons a%Q A))
                      (cons 0%Q (qpoly_mul B (cons a%Q A)))).
    rewrite lw0_coef_add, lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. ring.
    + cbn [lw0_coef].
      rewrite (IHA (cons b%Q B) j').
      change (qpoly_mul (cons b%Q B) A)
        with (qpoly_add (qpoly_scalar b A) (cons 0%Q (qpoly_mul B A))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      rewrite <- (IHB j').
      change (qpoly_mul (cons a%Q A) B)
        with (qpoly_add (qpoly_scalar a B) (cons 0%Q (qpoly_mul A B))).
      rewrite lw0_coef_add, lw0_coef_scalar.
      destruct j' as [|j''].
      * cbn [lw0_coef]. ring.
      * cbn [lw0_coef]. rewrite (IHA B j''). ring.
Qed.

Lemma lw0_lintail_qtail : forall (q : Q) (P : QPoly) (j : nat),
  lw0_coef j (qpoly_mul P (cons q (cons (-1)%Q nil)))
  == lw0_coef j (lw0_qtail q P).
Proof.
  intros q P j. unfold lw0_qtail.
  destruct j as [|j'].
  - rewrite lw0_coef_mul_h0.
    rewrite lw0_coef_add, lw0_coef_scalar.
    cbn [lw0_coef]. ring.
  - rewrite lw0_coef_mul_hS.
    rewrite lw0_coef_add, lw0_coef_scalar.
    cbn [lw0_coef]. rewrite lw0_coef_opp. ring.
Qed.

Lemma lw0_cons0_congr : forall (A B : QPoly) (j : nat),
  (forall i, lw0_coef i A == lw0_coef i B) ->
  lw0_coef j (cons 0%Q A) == lw0_coef j (cons 0%Q B).
Proof.
  intros A B j H. destruct j as [|j'].
  - cbn [lw0_coef]. reflexivity.
  - cbn [lw0_coef]. apply H.
Qed.

Lemma lw0_pi_mono_cons0 : forall (i j : nat),
  lw0_coef j (lw0_pi_mono (Datatypes.S i))
  == lw0_coef j (cons 0%Q (lw0_pi_mono i)).
Proof.
  intros i j. cbn [lw0_pi_mono].
  rewrite lw0_mul_cons0_right.
  destruct j as [|j'].
  - cbn [lw0_coef]. reflexivity.
  - cbn [lw0_coef]. apply lw0_mul_unit_right.
Qed.

Lemma lw0_pi_qminus_qtail : forall (q : Q) (i j : nat),
  lw0_coef j (lw0_pi_qminus_pow q (Datatypes.S i))
  == lw0_coef j (lw0_qtail q (lw0_pi_qminus_pow q i)).
Proof.
  intros q i j. cbn [lw0_pi_qminus_pow]. apply lw0_lintail_qtail.
Qed.

Lemma lw0_mul_tshift : forall (X : QPoly) (j : nat),
  lw0_coef j (qpoly_mul X (cons 0%Q (cons 1%Q nil)))
  == lw0_coef j (cons 0%Q X).
Proof.
  intros X j. rewrite lw0_mul_cons0_right.
  destruct j as [|j'].
  - cbn [lw0_coef]. reflexivity.
  - cbn [lw0_coef]. apply lw0_mul_unit_right.
Qed.

Lemma lw0_qtail_eval_0 : forall (q : Q) (P : QPoly) (m : nat),
  qpoly_eval (qpoly_deriv_iter (Datatypes.S m) (lw0_qtail q P)) 0
  == q * qpoly_eval (qpoly_deriv_iter (Datatypes.S m) P) 0
     - (Z.of_nat (Datatypes.S m) # 1)%Q * qpoly_eval (qpoly_deriv_iter m P) 0.
Proof.
  intros q P m. unfold lw0_qtail.
  rewrite lw0_eval_deriv_iter_add.
  rewrite lw0_eval_deriv_iter_scalar.
  rewrite lw0_shift_deriv.
  change (lw0_pred_iter (Datatypes.S m) (qpoly_opp P))
    with (qpoly_deriv_iter m (qpoly_opp P)).
  rewrite (lw0_eval_iter_opp m P 0).
  ring.
Qed.

Lemma lw0_deriv_iter_one : forall (m : nat) (x : Q),
  qpoly_eval (qpoly_deriv_iter (Datatypes.S m) (cons 1%Q nil)) x == 0.
Proof.
  intros m x.
  assert (Hd : qpoly_deriv_iter (Datatypes.S m) (cons 1%Q nil) = cons 0%Q nil).
  { induction m as [|m IH].
    - reflexivity.
    - change (qpoly_deriv_iter (Datatypes.S (Datatypes.S m)) (cons 1%Q nil))
        with (qpoly_deriv (qpoly_deriv_iter (Datatypes.S m) (cons 1%Q nil))).
      rewrite IH. reflexivity. }
  rewrite Hd. cbn [qpoly_eval]. ring.
Qed.

Lemma lw0_alt_double : forall j : nat, lw0_alt (j + j)%nat == 1%Q.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - replace (Datatypes.S j + Datatypes.S j)%nat with (Datatypes.S (j + Datatypes.S j)) by ring.
    rewrite lw0_alt_opp.
    replace (j + Datatypes.S j)%nat with (Datatypes.S (j + j)) by ring.
    rewrite lw0_alt_opp, IH. ring.
Qed.

Lemma lw0_q_pow_m0 : forall (x : Q) (n : nat), q_pow (x - 0)%Q n == q_pow x n.
Proof.
  intros x n. induction n as [|n IH].
  - reflexivity.
  - change (q_pow (x - 0)%Q (Datatypes.S n)) with ((x - 0)%Q * q_pow (x - 0)%Q n).
    change (q_pow x (Datatypes.S n)) with (x * q_pow x n).
    rewrite IH.
    assert (Hx0 : (x - 0)%Q == x) by ring.
    rewrite Hx0.
    reflexivity.
Qed.

Lemma lw0_pi_mirror_bnd : forall (q : Q) (i m : nat),
  qpoly_eval (qpoly_deriv_iter m (lw0_pi_mono i)) q
  == lw0_alt m *
     qpoly_eval (qpoly_deriv_iter m (lw0_pi_qminus_pow q i)) 0.
Proof.
  intros q i. induction i as [|i IH]; intros m.
  - destruct m as [|m].
    + cbn [qpoly_deriv_iter lw0_pi_mono lw0_pi_qminus_pow qpoly_eval lw0_alt].
      ring.
    + cbn [lw0_pi_mono lw0_pi_qminus_pow].
      rewrite lw0_deriv_iter_one, lw0_deriv_iter_one.
      ring.
  - destruct m as [|m].
    + cbn [qpoly_deriv_iter lw0_alt].
      rewrite lw0_pi_mono_eval, lw0_pi_qminus_pow_eval.
      rewrite lw0_q_pow_m0.
      ring.
    +                                             
      change (lw0_pi_mono (Datatypes.S i))
        with (qpoly_mul (lw0_pi_mono i) (cons 0%Q (cons 1%Q nil))).
      rewrite (lw0_eval_iter_congr (Datatypes.S m) _
                 (cons 0%Q (lw0_pi_mono i)) q
                 (fun j => lw0_pi_mono_cons0 i j)).
      rewrite lw0_shift_deriv.
      change (lw0_pred_iter (Datatypes.S m) (lw0_pi_mono i))
        with (qpoly_deriv_iter m (lw0_pi_mono i)).
                                                   
      change (lw0_pi_qminus_pow q (Datatypes.S i))
        with (qpoly_mul (lw0_pi_qminus_pow q i) (cons q (cons (-1)%Q nil))).
      rewrite (lw0_eval_iter_congr (Datatypes.S m) _
                 (lw0_qtail q (lw0_pi_qminus_pow q i)) 0
                 (fun j => lw0_pi_qminus_qtail q i j)).
      rewrite lw0_qtail_eval_0.
      rewrite (IH (Datatypes.S m)), (IH m).
      rewrite lw0_alt_opp.
      ring.
Qed.

Lemma lw0_niven_mirror : forall (q : Q) (i j k : nat),
  qpoly_eval (qpoly_deriv_iter k (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j))) q
  == lw0_alt k *
     qpoly_eval (qpoly_deriv_iter k (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j))) 0.
Proof.
  intros q i j k. revert i j.
  induction k as [|k IH]; intros i j.
  - cbn [qpoly_deriv_iter].
    rewrite qpoly_eval_mul, qpoly_eval_mul.
    rewrite lw0_pi_mono_eval, lw0_pi_qminus_pow_eval,
            lw0_pi_qminus_pow_eval, lw0_pi_mono_eval.
    destruct j as [|j'].
    + cbn [q_pow lw0_alt].
      rewrite lw0_q_pow_m0. ring.
    + cbn [q_pow lw0_alt].
      ring.
  - destruct j as [|j'].
    +                          
      cbn [lw0_pi_qminus_pow lw0_pi_mono].
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (lw0_pi_mono i) (cons 1%Q nil))
                 (lw0_pi_mono i) q
                 (fun j0 => lw0_mul_unit_right (lw0_pi_mono i) j0)).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (lw0_pi_qminus_pow q i) (cons 1%Q nil))
                 (lw0_pi_qminus_pow q i) 0
                 (fun j0 => lw0_mul_unit_right (lw0_pi_qminus_pow q i) j0)).
      apply (lw0_pi_mirror_bnd q i (Datatypes.S k)).
    +                                   
      change (lw0_pi_qminus_pow q (Datatypes.S j'))
        with (qpoly_mul (lw0_pi_qminus_pow q j') (cons q (cons (-1)%Q nil))).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (lw0_pi_mono i)
                    (qpoly_mul (lw0_pi_qminus_pow q j') (cons q (cons (-1)%Q nil))))
                 (qpoly_mul (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j'))
                    (cons q (cons (-1)%Q nil))) q
                 (fun j0 => lw0_mul_assoc (lw0_pi_mono i) (lw0_pi_qminus_pow q j')
                              (cons q (cons (-1)%Q nil)) j0)).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j'))
                    (cons q (cons (-1)%Q nil)))
                 (lw0_qtail q (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j'))) q
                 (fun j0 => lw0_lintail_qtail q _ j0)).
      rewrite lw0_qtail_step.
      change (lw0_pred_iter (Datatypes.S k) (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j')))
        with (qpoly_deriv_iter k (qpoly_mul (lw0_pi_mono i) (lw0_pi_qminus_pow q j'))).
      rewrite (IH i j').
      change (lw0_pi_mono (Datatypes.S j'))
        with (qpoly_mul (lw0_pi_mono j') (cons 0%Q (cons 1%Q nil))).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (lw0_pi_qminus_pow q i)
                    (qpoly_mul (lw0_pi_mono j') (cons 0%Q (cons 1%Q nil))))
                 (qpoly_mul (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j'))
                    (cons 0%Q (cons 1%Q nil))) 0
                 (fun j0 => lw0_mul_assoc (lw0_pi_qminus_pow q i) (lw0_pi_mono j')
                              (cons 0%Q (cons 1%Q nil)) j0)).
      rewrite (lw0_eval_iter_congr (Datatypes.S k)
                 (qpoly_mul (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j'))
                    (cons 0%Q (cons 1%Q nil)))
                 (cons 0%Q (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j'))) 0
                 (fun j0 => lw0_mul_tshift _ j0)).
      rewrite lw0_shift_deriv.
      change (lw0_pred_iter (Datatypes.S k) (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j')))
        with (qpoly_deriv_iter k (qpoly_mul (lw0_pi_qminus_pow q i) (lw0_pi_mono j'))).
      rewrite lw0_alt_opp.
      ring.
Qed.

Lemma lw0_niven_deriv_mirror_even : forall (q b : Q) (n j : nat),
  qpoly_eval (qpoly_deriv_iter (2 * j)%nat (lw0_niven_f q b n)) q
  == qpoly_eval (qpoly_deriv_iter (2 * j)%nat (lw0_niven_f q b n)) 0.
Proof.
  intros q b n j. unfold lw0_niven_f.
  rewrite (lw0_eval_deriv_iter_scalar (2 * j)%nat _ _ q).
  rewrite (lw0_eval_deriv_iter_scalar (2 * j)%nat _ _ 0).
  rewrite (lw0_niven_mirror q n n (2 * j)%nat).
  rewrite (lw0_eval_iter_congr (2 * j)%nat
             (qpoly_mul (lw0_pi_qminus_pow q n) (lw0_pi_mono n))
             (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow q n)) 0
             (fun i => lw0_mul_comm (lw0_pi_qminus_pow q n) (lw0_pi_mono n) i)).
  replace (2 * j)%nat with (j + j)%nat by ring.
  rewrite lw0_alt_double.
  ring.
Qed.

Lemma lw0_coef_mul_congr : forall (A U V : QPoly),
  (forall i : nat, lw0_coef i U == lw0_coef i V) ->
  forall j : nat, lw0_coef j (qpoly_mul A U) == lw0_coef j (qpoly_mul A V).
Proof.
  intros A. induction A as [|c A IH]; intros U V H j.
  - cbn [qpoly_mul lw0_coef]. ring.
  - change (qpoly_mul (cons c%Q A) U)
      with (qpoly_add (qpoly_scalar c U) (cons 0%Q (qpoly_mul A U))).
    change (qpoly_mul (cons c%Q A) V)
      with (qpoly_add (qpoly_scalar c V) (cons 0%Q (qpoly_mul A V))).
    rewrite !lw0_coef_add, !lw0_coef_scalar.
    destruct j as [|j'].
    + cbn [lw0_coef]. rewrite (H 0%nat). apply Qeq_refl.
    + cbn [lw0_coef]. rewrite (H (Datatypes.S j')). rewrite (IH U V H j').
      apply Qeq_refl.
Qed.

Lemma lw0_pi_qminus_z_bridge : forall (q : Q) (i j : nat),
  lw0_coef j (lw0_pi_qminus_pow q i) == lw0_coef j (lw0_qminus_pow q i).
Proof.
  intros q i. induction i as [|i IH]; intro j.
  - reflexivity.
  - cbn [lw0_pi_qminus_pow lw0_qminus_pow].
    rewrite (lw0_mul_comm (lw0_pi_qminus_pow q i) (cons q (cons (-1)%Q nil)) j).
    rewrite (lw0_mul_comm (lw0_qminus_pow q i) (cons q (cons (-1)%Q nil)) j).
    apply lw0_coef_mul_congr. exact IH.
Qed.

Lemma lw0_pi_mono_z_bridge : forall (i j : nat),
  lw0_coef j (lw0_pi_mono i) == lw0_coef j (lw0_mono i).
Proof.
  intros i. induction i as [|i IH]; intro j.
  - reflexivity.
  - rewrite lw0_pi_mono_cons0.
    change (lw0_mono (Datatypes.S i)) with (cons 0%Q (lw0_mono i)).
    exact (lw0_cons0_congr (lw0_pi_mono i) (lw0_mono i) j IH).
Qed.

Lemma lw0_q_pow_one_base : forall (x : Z) (n : nat),
  q_pow (x # 1)%Q n == (Zpower_nat x n # 1)%Q.
Proof.
  intros x. induction n as [|n IH].
  - reflexivity.
  - change (q_pow (x # 1)%Q (Datatypes.S n))
      with ((x # 1)%Q * q_pow (x # 1)%Q n).
    rewrite IH.
    change (Zpower_nat x (Datatypes.S n)) with (x * Zpower_nat x n)%Z.
    apply lw0_Qmake_mul.
Qed.

Lemma lw0_niven_scalar_bridge : forall (x : Z) (n : nat),
  q_pow (x # 1)%Q n / q_fact n == (Zpower_nat x n # Pos.of_nat (fact n))%Q.
Proof.
  intros x n.
  assert (Hfn : (1 <= fact n)%nat) by (destruct (fact n) as [|k0] eqn:Ek; [ exfalso; apply (fact_neq_0 n); exact Ek | apply le_n_S; apply Nat.le_0_l ]).
  assert (Hz : (0 < Z.of_nat (fact n))%Z).
  { destruct (fact n) as [|k] eqn:Ek;
      [ exfalso; apply (fact_neq_0 n); exact Ek
      | rewrite Nat2Z.inj_succ;
        apply (proj2 (Z.lt_succ_r 0 (Z.of_nat k))); apply Nat2Z.is_nonneg ]. }
  assert (Hmul : q_pow (x # 1)%Q n
                 == (Zpower_nat x n # Pos.of_nat (fact n))%Q * (Z.of_nat (fact n) # 1)%Q).
  { rewrite lw0_q_pow_one_base. unfold Qeq, Qmult. cbn [Qnum Qden].
    rewrite Pos.mul_1_r, (lw0_posnat_zeq (fact n) Hfn). ring. }
  rewrite lw0_qfact_Z, Hmul.
  change ((Zpower_nat x n # Pos.of_nat (fact n))%Q * (Z.of_nat (fact n) # 1)%Q /
          (Z.of_nat (fact n) # 1)%Q)
    with ((Zpower_nat x n # Pos.of_nat (fact n))%Q * (Z.of_nat (fact n) # 1)%Q *
          / (Z.of_nat (fact n) # 1)%Q).
  assert (Hre : (Zpower_nat x n # Pos.of_nat (fact n))%Q * (Z.of_nat (fact n) # 1)%Q *
                / (Z.of_nat (fact n) # 1)%Q
                == (Zpower_nat x n # Pos.of_nat (fact n))%Q
                   * ((Z.of_nat (fact n) # 1)%Q * / (Z.of_nat (fact n) # 1)%Q)).
  { apply Qeq_sym. apply Qmult_assoc. }
  rewrite Hre.
  rewrite (lw0_q_int_inv (Z.of_nat (fact n)) Hz).
  ring.
Qed.

Lemma lw0_niven_pi_z_bridge : forall (a : Z) (b : positive) (n j : nat),
  lw0_coef j (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)
  == lw0_coef j (lw0_niven_f_z (a # b)%Q (Zpos b) n).
Proof.
  intros a b n j. unfold lw0_niven_f, lw0_niven_f_z.
  rewrite !lw0_coef_scalar.
  rewrite (lw0_niven_scalar_bridge (Zpos b) n).
  assert (Hm : lw0_coef j (qpoly_mul (lw0_pi_mono n) (lw0_pi_qminus_pow (a # b)%Q n))
               == lw0_coef j (qpoly_mul (lw0_mono n) (lw0_qminus_pow (a # b)%Q n))).
  { transitivity (lw0_coef j (qpoly_mul (lw0_pi_mono n) (lw0_qminus_pow (a # b)%Q n))).
    - apply lw0_coef_mul_congr. intro i. apply lw0_pi_qminus_z_bridge.
    - transitivity (lw0_coef j (qpoly_mul (lw0_qminus_pow (a # b)%Q n) (lw0_pi_mono n))).
      + apply lw0_mul_comm.
      + transitivity (lw0_coef j (qpoly_mul (lw0_qminus_pow (a # b)%Q n) (lw0_mono n))).
        * apply lw0_coef_mul_congr. intro i. apply lw0_pi_mono_z_bridge.
        * apply lw0_mul_comm. }
  rewrite Hm. apply Qeq_refl.
Qed.

Lemma lw0_niven_deriv_zero_0_ab : forall (a : Z) (b : positive) (n k : nat),
  (k < n)%nat ->
  qpoly_eval (qpoly_deriv_iter k (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) 0 == 0.
Proof.
  intros a b n k Hk.
  transitivity (qpoly_eval (qpoly_deriv_iter k (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0).
  - apply (lw0_eval_iter_congr k _ _ 0 (fun j => lw0_niven_pi_z_bridge a b n j)).
  - apply lw0_niven_deriv_zero_0. exact Hk.
Qed.

Lemma lw0_niven_deriv_conn_lo_ab : forall (a : Z) (b : positive) (n k : nat),
  (n <= k)%nat ->
  qpoly_eval (qpoly_deriv_iter k (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) 0
  == lw0_z_lo a (Zpos b) n k.
Proof.
  intros a b n k Hk.
  transitivity (qpoly_eval (qpoly_deriv_iter k (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0).
  - apply (lw0_eval_iter_congr k _ _ 0 (fun j => lw0_niven_pi_z_bridge a b n j)).
  - apply lw0_conn_lo. exact Hk.
Qed.

Lemma lw0_niven_deriv_conn_hi_ab : forall (a : Z) (b : positive) (n j : nat),
  (n <= 2 * j)%nat -> (j <= n)%nat ->
  qpoly_eval (qpoly_deriv_iter (2 * j)%nat (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n)) 0
  == lw0_z_hi a (Zpos b) n (2 * (n - j))%nat.
Proof.
  intros a b n j H1 H2.
  transitivity (qpoly_eval (qpoly_deriv_iter (2 * j)%nat (lw0_niven_f_z (a # b)%Q (Zpos b) n)) 0).
  - apply (lw0_eval_iter_congr (2 * j)%nat _ _ 0 (fun i => lw0_niven_pi_z_bridge a b n i)).
  - apply lw0_conn_hi; assumption.
Qed.

Lemma lw0_F_eval_qsum : forall (f : qpoly) (J : nat) (x : Q),
  qpoly_eval (lw0_F f J) x
  == lw0_qsum (fun j : nat => lw0_alt j * qpoly_eval (qpoly_deriv_iter (2 * j)%nat f) x) J.
Proof.
  intros f J x. induction J as [|J' IH].
  - unfold lw0_F, lw0_F_aux. cbn [lw0_qsum].
    change (qpoly_deriv_iter (2 * 0)%nat f) with f.
    change (lw0_alt 0%nat) with 1%Q.
    rewrite qpoly_eval_scalar. ring.
  - unfold lw0_F. cbn [lw0_F_aux].
    change (lw0_F_aux f 1%Q J') with (lw0_F f J').
    rewrite qpoly_eval_add, qpoly_eval_scalar.
    rewrite IH. cbn [lw0_qsum]. ring.
Qed.

Lemma lw0_qsum_ext2 : forall (g h1 h2 : nat -> Q) (m : nat),
  (forall j : nat, (j <= m)%nat -> g j == h1 j + h2 j) ->
  lw0_qsum g m == lw0_qsum h1 m + lw0_qsum h2 m.
Proof.
  intros g h1 h2 m. induction m as [|m IH]; intro H.
  - cbn [lw0_qsum]. apply (H 0%nat (Nat.le_0_l 0%nat)).
  - cbn [lw0_qsum].
    rewrite (IH (fun j Hj => H j (Nat.le_le_succ_r _ _ Hj))).
    rewrite (H (Datatypes.S m) (Nat.le_refl (Datatypes.S m))).
    ring.
Qed.

Lemma lw0_K_closure_F0Fq : forall (q : Q) (n : nat),
  lw0_K (Qnum q) (Zpos (Qden q)) n
  == qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
     + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q.
Proof.
  intros q n. destruct q as [a b]. cbn [Qnum Qden].
  rewrite (lw0_F_eval_qsum (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n 0).
  rewrite (lw0_F_eval_qsum (lw0_niven_f (a # b)%Q (Zpos b # 1)%Q n) n ((a # b)%Q)).
  apply (lw0_qsum_ext2 (lw0_K_leg a (Zpos b) n)).
  intros j Hj. cbn beta. unfold lw0_K_leg.
  destruct (Nat.leb n (2 * j)) eqn:Hle.
  - apply Nat.leb_le in Hle.
    change (if true
            then lw0_z_lo a (Zpos b) n (2 * j) + lw0_z_hi a (Zpos b) n (2 * (n - j))
            else (0 # 1)%Q)
      with (lw0_z_lo a (Zpos b) n (2 * j) + lw0_z_hi a (Zpos b) n (2 * (n - j)))%Q.
    rewrite (lw0_alt_zsign j).
    rewrite (lw0_niven_deriv_conn_lo_ab a b n (2 * j)%nat Hle).
    rewrite (lw0_niven_deriv_mirror_even (a # b)%Q (Zpos b # 1)%Q n j).
    rewrite (lw0_niven_deriv_conn_hi_ab a b n j Hle Hj).
    ring.
  - apply Nat.leb_gt in Hle.
    change (if false
            then lw0_z_lo a (Zpos b) n (2 * j) + lw0_z_hi a (Zpos b) n (2 * (n - j))
            else (0 # 1)%Q)
      with (0 # 1)%Q.
    rewrite (lw0_niven_deriv_mirror_even (a # b)%Q (Zpos b # 1)%Q n j).
    rewrite (lw0_niven_deriv_zero_0_ab a b n (2 * j)%nat Hle).
    ring.
Qed.

Lemma lw0_pitB_pair_rtail_vanish_hpair : forall (q : Q) (n : nat),
  (forall eps : Q, QltT 0 eps ->
     sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
       QltT (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp m) q
                   - qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) 0
                   - qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                       * qpoly_eval (lw0_sin_qp m) q
                   + qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                       * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q)) eps)) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
    QltT (Qabs (lw0_pitB_pair_rtail q n m)) eps).
Proof.
  intros q n Hpair eps Heps.
  exact (lw0_pitB_pair_rtail_vanish_gap q n (lw0_K_closure_F0Fq q n) Hpair eps Heps).
Qed.

Definition lw0_pitB_pair_conv_f (q : Q) (n : nat) : qpoly :=
  lw0_niven_f q (Zpos (Qden q) # 1)%Q n.

Definition lw0_pitB_pair_conv_delta (j : nat) : qpoly :=
  qpoly_scalar (1 / q_fact (Datatypes.S (2 * j)))%Q
    (lw0_pitB_conv_zero_shift (Datatypes.S (2 * j)) (cons 1%Q nil)).

Definition lw0_pitB_pair_conv_delta' (j : nat) : qpoly :=
  qpoly_scalar (1 / q_fact (Datatypes.S (2 * j)))%Q
    (qpoly_shift (Datatypes.S (2 * j)) (cons 1%Q nil)).

Lemma lw0_qpoly_eqT_of_prop : forall p q : qpoly,
  lw0_qpoly_eq p q -> lw0_qpoly_eqT p q.
Proof.
  intros p q H j. apply qeq_imp_qeqT. exact (H j).
Qed.

Lemma lw0_qpoly_eq_prop_of_eqT : forall p q : qpoly,
  lw0_qpoly_eqT p q -> lw0_qpoly_eq p q.
Proof.
  intros p q H j. apply qeqT_imp_qeq. apply H.
Qed.

Lemma lw0_qpoly_eqT_refl : forall p : qpoly, lw0_qpoly_eqT p p.
Proof.
  intro p. apply lw0_qpoly_eqT_of_prop. apply lw0_qpoly_eq_refl.
Qed.

Lemma lw0_qpoly_eqT_sym : forall p q : qpoly,
  lw0_qpoly_eqT p q -> lw0_qpoly_eqT q p.
Proof.
  intros p q H. apply lw0_qpoly_eqT_of_prop.
  apply lw0_qpoly_eq_sym. apply lw0_qpoly_eq_prop_of_eqT. exact H.
Qed.

Lemma lw0_qpoly_eqT_trans : forall p q r : qpoly,
  lw0_qpoly_eqT p q -> lw0_qpoly_eqT q r -> lw0_qpoly_eqT p r.
Proof.
  intros p q r H1 H2. apply lw0_qpoly_eqT_of_prop.
  apply (lw0_qpoly_eq_trans p q r).
  - apply lw0_qpoly_eq_prop_of_eqT. exact H1.
  - apply lw0_qpoly_eq_prop_of_eqT. exact H2.
Qed.

Lemma lw0_qpoly_eqT_add : forall p1 q1 p2 q2 : qpoly,
  lw0_qpoly_eqT p1 q1 -> lw0_qpoly_eqT p2 q2 ->
  lw0_qpoly_eqT (qpoly_add p1 p2) (qpoly_add q1 q2).
Proof.
  intros p1 q1 p2 q2 H1 H2. apply lw0_qpoly_eqT_of_prop.
  apply lw0_qpoly_eq_add.
  - apply lw0_qpoly_eq_prop_of_eqT. exact H1.
  - apply lw0_qpoly_eq_prop_of_eqT. exact H2.
Qed.

Lemma lw0_qpoly_eqT_cons_congr : forall (a b : Q) (p q : qpoly),
  a == b -> lw0_qpoly_eqT p q -> lw0_qpoly_eqT (cons a p) (cons b q).
Proof.
  intros a b p q Hab H. apply lw0_qpoly_eqT_of_prop.
  apply lw0_cons_congr.
  - exact Hab.
  - apply lw0_qpoly_eq_prop_of_eqT. exact H.
Qed.

Lemma lw0_pitB_pair_conv_scalar_congr : forall (c : Q) (p q : qpoly),
  lw0_qpoly_eqT p q -> lw0_qpoly_eqT (qpoly_scalar c p) (qpoly_scalar c q).
Proof.
  intros c p q H j. apply qeq_imp_qeqT.
  rewrite lw0_coef_scalar, lw0_coef_scalar.
  rewrite (qeqT_imp_qeq _ _ (H j)). reflexivity.
Qed.

Lemma lw0_pitB_pair_conv_mul_r : forall (f g1 g2 : qpoly),
  lw0_qpoly_eqT g1 g2 -> lw0_qpoly_eqT (qpoly_mul f g1) (qpoly_mul f g2).
Proof.
  intros f. induction f as [|a f IH]; intros g1 g2 H.
  - cbn [qpoly_mul]. apply lw0_qpoly_eqT_refl.
  - cbn [qpoly_mul]. apply lw0_qpoly_eqT_add.
    + apply lw0_pitB_pair_conv_scalar_congr. exact H.
    + apply lw0_qpoly_eqT_cons_congr.
      * reflexivity.
      * apply IH. exact H.
Qed.

Lemma lw0_pitB_pair_conv_coef_ai : forall (p : qpoly) (k j : nat),
  lw0_coef j (lw0_qp_ai p k)
  == lw0_coef j p / (Z.of_nat (Datatypes.S (j + k)) # 1)%Q.
Proof.
  induction p as [|a p IH]; intros k j.
  - cbn [lw0_qp_ai]. destruct j as [|j']; reflexivity.
  - destruct j as [|j'].
    + reflexivity.
    + cbn [lw0_qp_ai lw0_coef].
      replace (Datatypes.S (Datatypes.S j' + k))%nat
        with (Datatypes.S (j' + Datatypes.S k))%nat by ring.
      rewrite <- (IH (Datatypes.S k) j').
      reflexivity.
Qed.

Lemma lw0_pitB_pair_conv_ai_congr : forall (p q : qpoly) (k : nat),
  lw0_qpoly_eqT p q -> lw0_qpoly_eqT (lw0_qp_ai p k) (lw0_qp_ai q k).
Proof.
  intros p q k H j. apply qeq_imp_qeqT.
  rewrite lw0_pitB_pair_conv_coef_ai, lw0_pitB_pair_conv_coef_ai.
  rewrite (qeqT_imp_qeq _ _ (H j)). reflexivity.
Qed.

Lemma lw0_pitB_pair_conv_pair_congr_r : forall (f g1 g2 : qpoly) (x : Q),
  lw0_qpoly_eqT g1 g2 -> QeqT (lw0_qp_pair f g1 x) (lw0_qp_pair f g2 x).
Proof.
  intros f g1 g2 x H. apply qeq_imp_qeqT. apply lw0_eval_len_indep.
  intro j. unfold lw0_qp_pair, lw0_qp_antideriv.
  destruct j as [|j'].
  - reflexivity.
  - apply lw0_cons_congr.
    + reflexivity.
    + apply lw0_qpoly_eq_prop_of_eqT.
      apply lw0_pitB_pair_conv_ai_congr. apply lw0_pitB_pair_conv_mul_r. exact H.
Qed.

Lemma lw0_pitB_pair_conv_zshift_bridge : forall (n : nat) (p : qpoly),
  lw0_qpoly_eqT (lw0_pitB_conv_zero_shift n p) (qpoly_shift n p).
Proof.
  induction n as [|n IH]; intros p.
  - cbn [lw0_pitB_conv_zero_shift qpoly_shift]. apply lw0_qpoly_eqT_refl.
  - cbn [lw0_pitB_conv_zero_shift qpoly_shift].
    apply lw0_qpoly_eqT_cons_congr.
    + reflexivity.
    + apply IH.
Qed.

Lemma lw0_pitB_pair_conv_delta_br : forall j : nat,
  lw0_qpoly_eqT (lw0_pitB_pair_conv_delta j) (lw0_pitB_pair_conv_delta' j).
Proof.
  intro j. apply lw0_pitB_pair_conv_scalar_congr.
  apply lw0_pitB_pair_conv_zshift_bridge.
Qed.

Lemma lw0_pitB_pair_conv_sin_aux_hi : forall (j : nat) (acc : qpoly) (r : nat),
  lw0_coef ((2 * j + 2 + r)%nat) (lw0_sin_aux j acc)
  == lw0_coef ((2 * j + 2 + r)%nat) (lw0_sin_aux j nil) + lw0_coef r acc.
Proof.
  induction j as [|j IH]; intros acc r.
  - replace (2 * 0 + 2 + r)%nat with (Datatypes.S (Datatypes.S r))%nat by ring.
    cbn [lw0_sin_aux lw0_coef]. ring.
  - cbn [lw0_sin_aux].
    replace (2 * Datatypes.S j + 2 + r)%nat
      with (2 * j + 2 + (r + 2))%nat by ring.
    rewrite (IH (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     acc)) (r + 2)%nat).
    rewrite (IH (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     nil)) (r + 2)%nat).
    replace (r + 2)%nat with (Datatypes.S (Datatypes.S r))%nat by ring.
    cbn [lw0_coef]. ring.
Qed.

Lemma lw0_pitB_pair_conv_sin_aux_lo : forall (j : nat) (acc : qpoly) (k : nat),
  (k < Datatypes.S (Datatypes.S (2 * j)))%nat ->
  lw0_coef k (lw0_sin_aux j acc) == lw0_coef k (lw0_sin_aux j nil).
Proof.
  induction j as [|j IH]; intros acc k Hk.
  - destruct k as [|k'].
    + reflexivity.
    + destruct k' as [|k''].
      * reflexivity.
      * exfalso.
        exact (Nat.nle_succ_0 k''
                 (proj2 (Nat.succ_le_mono (Datatypes.S k'') 0)
                    (proj2 (Nat.succ_le_mono (Datatypes.S (Datatypes.S k'')) 1)
                       Hk))).
  - cbn [lw0_sin_aux].
    destruct (le_lt_dec (Datatypes.S (Datatypes.S (2 * j)))%nat k) as [Hge | Hlt].
    + assert (Hge2 : (2 * j + 2 <= k)%nat).
      { replace (2 * j + 2)%nat with (Datatypes.S (Datatypes.S (2 * j))) by ring.
        exact Hge. }
      replace k with ((2 * j + 2 + (k - (2 * j + 2)))%nat)
        by (rewrite Nat.add_comm; apply Nat.sub_add; exact Hge2).
      rewrite (lw0_pitB_pair_conv_sin_aux_hi j (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     acc)) (k - (2 * j + 2))%nat).
      rewrite (lw0_pitB_pair_conv_sin_aux_hi j (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     nil)) (k - (2 * j + 2))%nat).
      destruct (k - (2 * j + 2))%nat as [|b] eqn:HD.
      * cbn [lw0_coef]. ring.
      * destruct b as [|b'] eqn:HD2.
        -- cbn [lw0_coef]. ring.
        -- exfalso.
           assert (Hkeq : k = (2 * j + 2 + Datatypes.S (Datatypes.S b'))%nat)
             by (rewrite <- HD; rewrite Nat.add_comm; symmetry;
                 apply Nat.sub_add; exact Hge2).
           rewrite Hkeq in Hk.
           replace (2 * Datatypes.S j)%nat with (2 * j + 2)%nat in Hk by ring.
           rewrite Nat.add_succ_r, Nat.add_succ_r in Hk.
           exact (Nat.lt_irrefl (2 * j + 2)%nat
                    (Nat.le_lt_trans _ _ _ (Nat.le_add_r (2 * j + 2)%nat b')
                       (proj2 (Nat.succ_lt_mono (2 * j + 2 + b')%nat
                                 (2 * j + 2)%nat)
                          (proj2 (Nat.succ_lt_mono
                                    (Datatypes.S (2 * j + 2 + b'))%nat
                                    (Datatypes.S (2 * j + 2))%nat)
                             Hk)))).
    + assert (Hk' := Hlt).
      assert (H1 := IH (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     acc)) k Hk').
      assert (H2 := IH (cons 0%Q
                  (cons (q_pow (-1) (Datatypes.S j)
                          / q_fact (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))%Q
                     nil)) k Hk').
      rewrite H1, H2. reflexivity.
Qed.

Lemma lw0_pitB_pair_conv_qdiv_mult_inv : forall a d : Q, a / d == a * (1 / d)%Q.
Proof.
  intros a d. unfold Qdiv. ring.
Qed.

Lemma lw0_pitB_pair_conv_sin_inc : forall j : nat,
  lw0_qpoly_eqT (qpoly_add (lw0_sin_qp (Datatypes.S j))
                            (qpoly_scalar (-1)%Q (lw0_sin_qp j)))
                (qpoly_scalar (q_pow (-1) (Datatypes.S j))%Q
                              (lw0_pitB_pair_conv_delta' (Datatypes.S j))).
Proof.
  intro j. unfold lw0_sin_qp, lw0_pitB_pair_conv_delta'.
  cbn [lw0_sin_aux]. intro k.
  apply qeq_imp_qeqT.
  rewrite lw0_coef_add, lw0_coef_scalar, lw0_coef_scalar.
  destruct (le_lt_dec (Datatypes.S (Datatypes.S (2 * j)))%nat k) as [Hge | Hlt].
  - replace k with ((Datatypes.S (Datatypes.S (2 * j)) + (k - Datatypes.S (Datatypes.S (2 * j))))%nat)
      by (rewrite Nat.add_comm; apply Nat.sub_add; exact Hge).
    replace (Datatypes.S (Datatypes.S (2 * j)))%nat
      with (2 * j + 2)%nat by ring.
    rewrite lw0_pitB_pair_conv_sin_aux_hi.
    rewrite lw0_pitB_pair_conv_sin_aux_hi.
    rewrite lw0_coef_scalar.
    destruct (k - (2 * j + 2))%nat as [|b] eqn:HD.
    + rewrite (lw0_coef_shift_lt (S (2 * Datatypes.S j)) (2 * j + 2 + 0)%nat
                 (cons 1%Q nil))
        by (replace (2 * j + 2 + 0)%nat with (2 * j + 2)%nat by ring;
            replace (2 * Datatypes.S j)%nat with (2 * j + 2)%nat by ring;
            apply Nat.lt_succ_diag_r).
      cbn [lw0_coef]. ring.
    + replace (2 * j + 2 + Datatypes.S b)%nat
        with (Datatypes.S (2 * Datatypes.S j) + b)%nat by ring.
      rewrite lw0_coef_shift.
      destruct b as [|b'] eqn:HD2.
      * cbn [lw0_coef].
        replace (Datatypes.S (2 * j + 2))%nat
          with (Datatypes.S (2 * Datatypes.S j))%nat by ring.
        rewrite Qmult_1_r.
        rewrite <- (lw0_pitB_pair_conv_qdiv_mult_inv
                      (q_pow (-1) (Datatypes.S j))%Q
                      (q_fact (Datatypes.S (2 * Datatypes.S j)))).
        assert (Hcancel : forall A : Q,
                   (A + 0%Q + (q_pow (-1) (Datatypes.S j)
                                / q_fact (Datatypes.S (2 * Datatypes.S j)))%Q)
                   + (-1)%Q * (A + 0%Q)
                   == (q_pow (-1) (Datatypes.S j)
                       / q_fact (Datatypes.S (2 * Datatypes.S j)))%Q)
          by (intro A; ring).
        apply Hcancel.
      * cbn [lw0_coef]. ring.
  - rewrite lw0_pitB_pair_conv_sin_aux_lo by exact Hlt.
    rewrite lw0_coef_scalar.
    replace (Datatypes.S (Datatypes.S (2 * j)))%nat
      with (2 * j + 2)%nat by ring.
    rewrite (lw0_coef_shift_lt (S (2 * Datatypes.S j)) k (cons 1%Q nil))
      by (apply (proj2 (Nat.lt_succ_r k (2 * Datatypes.S j)));
          replace (2 * Datatypes.S j)%nat
            with (Datatypes.S (Datatypes.S (2 * j)))%nat by ring;
          exact (Nat.lt_le_incl _ _ Hlt)).
    ring.
Qed.

Lemma lw0_pitB_pair_conv_qabs_sign1 : forall j : nat,
  Qabs (q_pow (-1) (Datatypes.S j)) == 1%Q.
Proof.
  intro j.
  rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_qabs_pow (-1)%Q (Datatypes.S j))).
  change (Qabs (-1)%Q) with 1%Q. apply lw0_q_pow_one.
Qed.

Lemma lw0_pitB_pair_conv_sig2 : forall (q : Q) (n j : nat) (x : Q),
  QeqT (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) x
        + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp j) x)
       0%Q.
Proof.
  intros q n j x. apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _
            (lw0_pitB_pair_conv_pair_congr_r
               (lw0_F (lw0_pitB_pair_conv_f q n) n)
               (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j)))
               (qpoly_scalar (-1)%Q (lw0_sin_qp j)) x
               (lw0_qpoly_eqT_of_prop _ _ (lw0_sin_qp_deriv2 j)))).
  rewrite (lw0_qp_pair_scalar_r (-1)%Q
             (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp j) x).
  ring.
Qed.

Lemma lw0_pitB_pair_conv_sinc : forall (q : Q) (n j : nat) (x : Q),
  QeqT (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
          (lw0_sin_qp (Datatypes.S j)) x
        - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp j) x)
       ((q_pow (-1) (Datatypes.S j))%Q
        * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
            (lw0_pitB_pair_conv_delta (Datatypes.S j)) x).
Proof.
  intros q n j x. apply qeq_imp_qeqT.
  rewrite <- (lw0_qp_pair_scalar_r (q_pow (-1) (Datatypes.S j))%Q
                (lw0_F (lw0_pitB_pair_conv_f q n) n)
                (lw0_pitB_pair_conv_delta (Datatypes.S j)) x).
  rewrite (qeqT_imp_qeq _ _
            (lw0_pitB_pair_conv_pair_congr_r
               (lw0_F (lw0_pitB_pair_conv_f q n) n)
               (qpoly_scalar (q_pow (-1) (Datatypes.S j))%Q
                  (lw0_pitB_pair_conv_delta (Datatypes.S j)))
               (qpoly_add (lw0_sin_qp (Datatypes.S j))
                          (qpoly_scalar (-1)%Q (lw0_sin_qp j))) x
               (lw0_qpoly_eqT_trans _ _ _
                  (lw0_pitB_pair_conv_scalar_congr (q_pow (-1) (Datatypes.S j))%Q
                     (lw0_pitB_pair_conv_delta (Datatypes.S j))
                     (lw0_pitB_pair_conv_delta' (Datatypes.S j))
                     (lw0_pitB_pair_conv_delta_br (Datatypes.S j)))
                  (lw0_qpoly_eqT_sym _ _ (lw0_pitB_pair_conv_sin_inc j))))).
  rewrite (lw0_qp_pair_add_r (lw0_F (lw0_pitB_pair_conv_f q n) n)
             (lw0_sin_qp (Datatypes.S j))
             (qpoly_scalar (-1)%Q (lw0_sin_qp j)) x).
  rewrite (lw0_qp_pair_scalar_r (-1)%Q
             (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp j) x).
  ring.
Qed.

Lemma lw0_pitB_pair_conv_core : forall (q : Q) (n m : nat),
  (forall x : Q,
     QeqT (lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F (lw0_pitB_pair_conv_f q n) n)) (lw0_sin_qp m) x
          + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) x)
          (lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp m) x)) ->
  lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp m) q
  - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
  - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
    * qpoly_eval (lw0_sin_qp m) q
  + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
    * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q
  == lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) q
     + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
         (qpoly_deriv_iter 2 (lw0_sin_qp m)) q.
Proof.
  intros q n m HF2.
  assert (Hz0 : qpoly_eval (lw0_sin_qp m) 0 == 0)
    by (apply lw0_sin_qp_zero_eval).
  assert (Ho1 : qpoly_eval (qpoly_deriv (lw0_sin_qp m)) 0 == 1%Q)
    by (rewrite (lw0_sin_qp_deriv_eval m 0); apply lw0_cos_partial_zero).
  assert (HA := lw0_pitB_ibp_dbl (lw0_F (lw0_pitB_pair_conv_f q n) n)
                                 (lw0_sin_qp m) q).
  assert (HB := qeqT_imp_qeq _ _ (HF2 q)).
  assert (HAm : lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F (lw0_pitB_pair_conv_f q n) n)) (lw0_sin_qp m) q
                == lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp m) q
                 - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) q).
  { transitivity (lw0_qp_pair (qpoly_deriv_iter 2 (lw0_F (lw0_pitB_pair_conv_f q n) n)) (lw0_sin_qp m) q
                  + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) q
                  - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n) (lw0_sin_qp m) q).
    - ring.
    - rewrite HB. ring. }
  rewrite HAm in HA.
  rewrite (qpoly_eval_mul (lw0_F (lw0_pitB_pair_conv_f q n) n)
             (qpoly_deriv (lw0_sin_qp m)) q) in HA.
  rewrite (qpoly_eval_mul (lw0_F (lw0_pitB_pair_conv_f q n) n)
             (qpoly_deriv (lw0_sin_qp m)) 0) in HA.
  rewrite (qpoly_eval_mul (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n))
             (lw0_sin_qp m) q) in HA.
  rewrite (qpoly_eval_mul (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n))
             (lw0_sin_qp m) 0) in HA.
  rewrite Ho1 in HA. rewrite Hz0 in HA.
  rewrite HA. ring.
Qed.

Lemma lw0_pitB_pair_conv_qabs_canon : forall x : Q,
  Qabs x == (if Qle_bool 0 x then x else (- x)%Q).
Proof.
  intro x.
  apply (Qabs_case x (fun z => z == (if Qle_bool 0 x then x else (- x)%Q))).
  - intros Hx. rewrite (proj2 (Qle_bool_iff 0 x) Hx). reflexivity.
  - intros Hx0. destruct (Qle_bool 0 x) eqn:E.
    + assert (Hz : x == 0%Q).
      { apply (Qle_antisym x 0).
        - exact Hx0.
        - exact (Qle_bool_imp_le 0 x E). }
      rewrite Hz. reflexivity.
    + reflexivity.
Qed.

Lemma lw0_pitB_pair_conv_qabs_wd : forall (x y : Q), x == y -> Qabs x == Qabs y.
Proof.
  intros x y Hxy.
  rewrite (lw0_pitB_pair_conv_qabs_canon x).
  rewrite (lw0_pitB_pair_conv_qabs_canon y).
  destruct (Qle_bool 0 x) eqn:Ex; destruct (Qle_bool 0 y) eqn:Ey.
  - exact Hxy.
  - exfalso.
    assert (Hx0 : 0 <= x) by (apply (Qle_bool_imp_le 0 x Ex)).
    assert (Hby : Qle_bool 0 y = Qle_bool 0 x) by (rewrite Hxy; reflexivity).
    rewrite Hby in Ey. rewrite (proj2 (Qle_bool_iff 0 x) Hx0) in Ey. discriminate Ey.
  - exfalso.
    assert (Hy0 : 0 <= y) by (apply (Qle_bool_imp_le 0 y Ey)).
    assert (Hbx : Qle_bool 0 x = Qle_bool 0 y) by (rewrite Hxy; reflexivity).
    rewrite Hbx in Ex. rewrite (proj2 (Qle_bool_iff 0 y) Hy0) in Ex. discriminate Ex.
  - rewrite Hxy. reflexivity.
Qed.

Lemma lw0_pitB_conv_pwi_shift1_eq : forall (p : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (cons 0%Q p) k c)
       (Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
Proof.
  intros p k c. apply qeq_imp_qeqT.
  change (lw0_pitB_conv_pwi (cons 0%Q p) k c)
    with (Qabs 0%Q * (Qabs c / lw0_q_of_nat (Datatypes.S k))
          + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
  assert (E0 : QeqT (Qabs 0%Q) 0%Q) by (unfold QeqT; cbn; reflexivity).
  rewrite (qeqT_imp_qeq _ _ E0).
  ring.
Qed.

Lemma lw0_pitB_conv_pwi_zero_shift_eq : forall (m : nat) (p : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m p) k c)
       (q_pow (Qabs c) m * lw0_pitB_conv_pwi p (k + m)%nat c).
Proof.
  intro m. induction m as [| m IH]; intros p k c.
  - change (lw0_pitB_conv_zero_shift 0 p) with p.
    change (q_pow (Qabs c) 0) with 1%Q.
    rewrite Nat.add_0_r.
    apply qeq_imp_qeqT. ring.
  - change (lw0_pitB_conv_zero_shift (Datatypes.S m) p)
      with (cons 0%Q (lw0_pitB_conv_zero_shift m p)).
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _
              (lw0_pitB_conv_pwi_shift1_eq (lw0_pitB_conv_zero_shift m p) k c)).
    rewrite (qeqT_imp_qeq _ _ (IH p (Datatypes.S k) c)).
    assert (E1 : (Datatypes.S k + m)%nat = Datatypes.S (k + m)%nat) by ring.
    rewrite E1.
    rewrite (Nat.add_succ_r k m).
    rewrite (q_pow_succ (Qabs c) m).
    ring.
Qed.

Lemma lw0_pitB_conv_div_den_mono : forall (x d1 d2 : Q),
  QleT' 0 x -> QleT' 1 d1 -> QleT' d1 d2 ->
  QleT' (x / d2) (x / d1).
Proof.
  intros x d1 d2 Hx0 Hd1 Hd12.
  apply Qle_to_QleT'.
  assert (H01 : Qlt 0 1%Q) by (apply QltT_to_Qlt; unfold QltT; reflexivity).
  assert (Hlt1 : Qlt 0 d1).
  { apply (Qlt_le_trans 0%Q 1%Q d1).
    - exact H01.
    - exact (QleT'_to_Qle _ _ Hd1). }
  assert (Hlt2 : Qlt 0 d2).
  { apply (Qlt_le_trans 0%Q 1%Q d2).
    - exact H01.
    - apply QleT'_to_Qle. exact (qleT'_trans 1%Q d1 d2 Hd1 Hd12). }
  assert (Hne1 : d1 == 0%Q -> False).
  { intros H. apply (qltT_not_eq_zero d1). apply Qlt_to_QltT. exact Hlt1. exact H. }
  assert (Hne2 : d2 == 0%Q -> False).
  { intros H. apply (qltT_not_eq_zero d2). apply Qlt_to_QltT. exact Hlt2. exact H. }
  assert (HstepA : QleT' (d1 * / d2) 1%Q).
  { apply (qleT'_trans (d1 * / d2)%Q (/ d2 * d2)%Q 1%Q).
    - apply (qleT'_trans (d1 * / d2)%Q (/ d2 * d1)%Q (/ d2 * d2)%Q).
      + apply qeq_leT'. ring.
      + apply (lw0_pitB_conv_mult_le_l (/ d2) d1 d2 Hd12).
        apply Qle_to_QleT'. apply Qinv_le_0_compat.
        apply (Qlt_le_weak 0). exact Hlt2.
    - apply qeq_leT'. rewrite (Qmult_comm (/ d2) d2).
      apply Qmult_inv_r. exact Hne2. }
  assert (HstepB : QleT' (/ d2) (/ d1)).
  { apply (qleT'_trans (/ d2)%Q (/ d1 * (d1 * / d2))%Q (/ d1)%Q).
    - apply qeq_leT'.
      rewrite (Qmult_assoc (/ d1) d1 (/ d2)).
      rewrite (Qmult_comm (/ d1) d1).
      rewrite (Qmult_inv_r d1 Hne1).
      ring.
    - apply (qleT'_trans (/ d1 * (d1 * / d2))%Q (/ d1 * 1)%Q (/ d1)%Q).
      + apply (lw0_pitB_conv_mult_le_l (/ d1) (d1 * / d2)%Q 1%Q HstepA).
        apply Qle_to_QleT'. apply Qinv_le_0_compat.
        apply (Qlt_le_weak 0). exact Hlt1.
      + apply qeq_leT'. ring. }
  apply QleT'_to_Qle.
  apply (lw0_pitB_conv_mult_le_l x (/ d2) (/ d1) HstepB Hx0).
Qed.

Lemma lw0_pitB_conv_pwi_k_mono : forall (p : QPoly) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi p (Datatypes.S k) c) (lw0_pitB_conv_pwi p k c).
Proof.
  intro p. induction p as [| a p IH]; intros k c.
  - change (lw0_pitB_conv_pwi nil (Datatypes.S k) c) with 0%Q.
    change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply (qeq_leT' 0%Q 0%Q). apply Qeq_refl.
  - change (lw0_pitB_conv_pwi (cons a p) (Datatypes.S k) c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S (Datatypes.S k)))
            + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S (Datatypes.S k)) c).
    change (lw0_pitB_conv_pwi (cons a p) k c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
    apply (qleT'_trans
             (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S (Datatypes.S k)))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S (Datatypes.S k)) c)
             (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S (Datatypes.S k)))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)
             (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
              + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)).
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs c)
                 (lw0_pitB_conv_pwi p (Datatypes.S (Datatypes.S k)) c)
                 (lw0_pitB_conv_pwi p (Datatypes.S k) c)
                 (IH (Datatypes.S k) c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs a)
                 (Qabs c / lw0_q_of_nat (Datatypes.S (Datatypes.S k)))
                 (Qabs c / lw0_q_of_nat (Datatypes.S k))).
        -- apply (lw0_pitB_conv_div_den_mono (Qabs c)
                    (lw0_q_of_nat (Datatypes.S k))
                    (lw0_q_of_nat (Datatypes.S (Datatypes.S k)))).
           ++ apply Qle_to_QleT'. apply Qabs_nonneg.
           ++ exact (lw0_q_of_nat_ge_one k).
           ++ exact (lw0_q_of_nat_le_succ (Datatypes.S k)).
        -- apply Qle_to_QleT'. apply Qabs_nonneg.
      * apply Qle_refl.
Qed.

Lemma lw0_pitB_conv_pwi_add_k_mono : forall (p : QPoly) (k j : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi p (k + j)%nat c) (lw0_pitB_conv_pwi p k c).
Proof.
  intros p k j. induction j as [| j IH]; intro c.
  - rewrite Nat.add_0_r. apply Qle_to_QleT'. apply Qle_refl.
  - assert (E : (k + Datatypes.S j)%nat = Datatypes.S (k + j)%nat) by ring.
    rewrite E.
    apply (qleT'_trans (lw0_pitB_conv_pwi p (Datatypes.S (k + j)) c)
                       (lw0_pitB_conv_pwi p (k + j) c)
                       (lw0_pitB_conv_pwi p k c)).
    + exact (lw0_pitB_conv_pwi_k_mono p (k + j) c).
    + exact (IH c).
Qed.

Lemma lw0_pitB_conv_pwi_nonneg : forall (p : QPoly) (k : nat) (c : Q),
  QleT' 0 (lw0_pitB_conv_pwi p k c).
Proof.
  intro p. induction p as [| a p IH]; intros k c.
  - change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply (qeq_leT' 0%Q 0%Q). apply Qeq_refl.
  - change (lw0_pitB_conv_pwi (cons a p) k c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c).
    assert (Hd : Qle 0 (Qabs c / lw0_q_of_nat (Datatypes.S k))).
    { apply Qmult_le_0_compat.
      - apply Qabs_nonneg.
      - apply Qinv_le_0_compat.
        apply Qlt_le_weak.
        apply (Qlt_le_trans 0%Q 1%Q (lw0_q_of_nat (Datatypes.S k))).
        + apply QltT_to_Qlt. unfold QltT. reflexivity.
        + apply QleT'_to_Qle. apply lw0_q_of_nat_ge_one. }
    assert (Hsum : Qle (0 + 0)%Q
              (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
               + Qabs c * lw0_pitB_conv_pwi p (Datatypes.S k) c)%Q).
    { apply Qplus_le_compat.
      - apply Qmult_le_0_compat.
        + apply Qabs_nonneg.
        + exact Hd.
      - apply Qmult_le_0_compat.
        + apply Qabs_nonneg.
        + exact (QleT'_to_Qle _ _ (IH (Datatypes.S k) c)). }
    apply Qle_to_QleT'. rewrite Qplus_0_l in Hsum. exact Hsum.
Qed.

Lemma lw0_pitB_conv_pwi_one_eq : forall (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi (cons 1%Q nil) k c)
       (Qabs c / lw0_q_of_nat (Datatypes.S k)).
Proof.
  intros k c. apply qeq_imp_qeqT.
  change (lw0_pitB_conv_pwi (cons 1%Q nil) k c)
    with (Qabs 1%Q * (Qabs c / lw0_q_of_nat (Datatypes.S k))
          + Qabs c * lw0_pitB_conv_pwi nil (Datatypes.S k) c).
  change (lw0_pitB_conv_pwi nil (Datatypes.S k) c) with 0%Q.
  assert (E1 : QeqT (Qabs 1%Q) 1%Q) by (unfold QeqT; cbn; reflexivity).
  rewrite (qeqT_imp_qeq _ _ E1).
  ring.
Qed.

Fixpoint lw0_pitB_conv_pwi_muliter (f g : QPoly) (k : nat) (c : Q) : Q :=
  match f with
  | nil => 0%Q
  | cons a f' => Qabs a * lw0_pitB_conv_pwi g k c
                 + Qabs c * lw0_pitB_conv_pwi_muliter f' g (Datatypes.S k) c
  end.

Lemma lw0_pitB_conv_pwi_mul_le_iter : forall (f g : QPoly) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi (qpoly_mul f g) k c)
        (lw0_pitB_conv_pwi_muliter f g k c).
Proof.
  intro f. induction f as [| a f' IH]; intros g k c.
  - change (lw0_pitB_conv_pwi (qpoly_mul nil g) k c) with 0%Q.
    change (lw0_pitB_conv_pwi_muliter nil g k c) with 0%Q.
    apply (qeq_leT' 0%Q 0%Q). apply Qeq_refl.
  - apply (qleT'_trans
             (lw0_pitB_conv_pwi (qpoly_mul (cons a f') g) k c)
             (Qabs a * lw0_pitB_conv_pwi g k c
              + Qabs c * lw0_pitB_conv_pwi (qpoly_mul f' g) (Datatypes.S k) c)
             (Qabs a * lw0_pitB_conv_pwi g k c
              + Qabs c * lw0_pitB_conv_pwi_muliter f' g (Datatypes.S k) c)).
    + exact (lw0_pitB_conv_pwi_mul_le a f' g k c).
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * apply Qle_refl.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs c)
                 (lw0_pitB_conv_pwi (qpoly_mul f' g) (Datatypes.S k) c)
                 (lw0_pitB_conv_pwi_muliter f' g (Datatypes.S k) c)).
        -- exact (IH g (Datatypes.S k) c).
        -- apply Qle_to_QleT'. apply Qabs_nonneg.
Qed.

Lemma lw0_pitB_conv_pwi_shift_one_domin : forall (m j : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) j c)
        (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) j c).
Proof.
  intros m j c.
  apply (qleT'_trans
          (lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) j c)
          (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) (j + m)%nat c)
          (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) j c)).
  - apply qeq_leT'. apply qeqT_imp_qeq.
    exact (lw0_pitB_conv_pwi_zero_shift_eq m (cons 1%Q nil) j c).
  - apply (lw0_pitB_conv_mult_le_l (q_pow (Qabs c) m)
             (lw0_pitB_conv_pwi (cons 1%Q nil) (j + m)%nat c)
             (lw0_pitB_conv_pwi (cons 1%Q nil) j c)
             (lw0_pitB_conv_pwi_add_k_mono (cons 1%Q nil) j m c)).
    apply Qle_to_QleT'. apply q_pow_nonneg. apply Qabs_nonneg.
Qed.

Lemma lw0_pitB_conv_pwi_muliter_scalar : forall (f : QPoly) (s : Q) (m : nat) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi_muliter f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
       (Qabs s * lw0_pitB_conv_pwi_muliter f (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c).
Proof.
  intro f. induction f as [| a f' IH]; intros s m k c.
  - change (lw0_pitB_conv_pwi_muliter nil (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
      with 0%Q.
    change (lw0_pitB_conv_pwi_muliter nil (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
      with 0%Q.
    apply qeq_imp_qeqT. rewrite Qmult_0_r. apply Qeq_refl.
  - change (lw0_pitB_conv_pwi_muliter (cons a f')
              (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
      with (Qabs a * lw0_pitB_conv_pwi (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c
            + Qabs c * lw0_pitB_conv_pwi_muliter f'
                (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) (Datatypes.S k) c).
    change (Qabs s * lw0_pitB_conv_pwi_muliter (cons a f')
              (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
      with (Qabs s * (Qabs a * lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c
                      + Qabs c * lw0_pitB_conv_pwi_muliter f'
                          (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) (Datatypes.S k) c)).
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _
              (lw0_pitB_conv_pwi_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)).
    rewrite (qeqT_imp_qeq _ _ (IH s m (Datatypes.S k) c)).
    ring.
Qed.

Lemma lw0_pitB_conv_pwi_muliter_shift : forall (f : QPoly) (m : nat) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi_muliter f (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
        (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c).
Proof.
  intro f. induction f as [| a f' IH]; intros m k c.
  - change (lw0_pitB_conv_pwi_muliter nil (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
      with 0%Q.
    change (lw0_pitB_conv_pwi_muliter nil (cons 1%Q nil) k c) with 0%Q.
    apply (qeq_leT' 0%Q (q_pow (Qabs c) m * 0%Q)).
    rewrite Qmult_0_r. apply Qeq_refl.
  - change (lw0_pitB_conv_pwi_muliter (cons a f')
              (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
      with (Qabs a * lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c
            + Qabs c * lw0_pitB_conv_pwi_muliter f'
                (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) (Datatypes.S k) c).
    apply (qleT'_trans
            (Qabs a * lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c
             + Qabs c * lw0_pitB_conv_pwi_muliter f'
                 (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) (Datatypes.S k) c)
            (Qabs a * (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) k c)
             + Qabs c * (q_pow (Qabs c) m
                         * lw0_pitB_conv_pwi_muliter f' (cons 1%Q nil) (Datatypes.S k) c))
            (q_pow (Qabs c) m
             * (Qabs a * lw0_pitB_conv_pwi (cons 1%Q nil) k c
                + Qabs c * lw0_pitB_conv_pwi_muliter f' (cons 1%Q nil) (Datatypes.S k) c))).
    + apply Qle_to_QleT'. apply Qplus_le_compat.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs a)
                   (lw0_pitB_conv_pwi (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
                   (q_pow (Qabs c) m * lw0_pitB_conv_pwi (cons 1%Q nil) k c)
                   (lw0_pitB_conv_pwi_shift_one_domin m k c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
      * apply QleT'_to_Qle.
        apply (lw0_pitB_conv_mult_le_l (Qabs c)
                   (lw0_pitB_conv_pwi_muliter f'
                     (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) (Datatypes.S k) c)
                   (q_pow (Qabs c) m
                    * lw0_pitB_conv_pwi_muliter f' (cons 1%Q nil) (Datatypes.S k) c)
                   (IH m (Datatypes.S k) c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
    + apply qeq_leT'. ring.
Qed.

Lemma lw0_pitB_conv_pwi_muliter_eq : forall (f : QPoly) (k : nat) (c : Q),
  QeqT (lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c)
       (lw0_pitB_conv_pwi f k c).
Proof.
  intro f. induction f as [| a f' IH]; intros k c.
  - change (lw0_pitB_conv_pwi_muliter nil (cons 1%Q nil) k c) with 0%Q.
    change (lw0_pitB_conv_pwi nil k c) with 0%Q.
    apply qeq_imp_qeqT. apply Qeq_refl.
  - change (lw0_pitB_conv_pwi_muliter (cons a f') (cons 1%Q nil) k c)
      with (Qabs a * lw0_pitB_conv_pwi (cons 1%Q nil) k c
            + Qabs c * lw0_pitB_conv_pwi_muliter f' (cons 1%Q nil) (Datatypes.S k) c).
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_pwi_one_eq k c)).
    rewrite (qeqT_imp_qeq _ _ (IH (Datatypes.S k) c)).
    change (lw0_pitB_conv_pwi (cons a f') k c)
      with (Qabs a * (Qabs c / lw0_q_of_nat (Datatypes.S k))
            + Qabs c * lw0_pitB_conv_pwi f' (Datatypes.S k) c).
    ring.
Qed.

Lemma lw0_pitB_conv_pwi_mul_shift_domin : forall (f : QPoly) (s : Q) (m : nat) (k : nat) (c : Q),
  QleT' (lw0_pitB_conv_pwi
          (qpoly_mul f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil)))) k c)
        (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi f k c)).
Proof.
  intros f s m k c.
  apply (qleT'_trans
          (lw0_pitB_conv_pwi
            (qpoly_mul f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil)))) k c)
          (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c))
          (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi f k c))).
  - apply (qleT'_trans
            (lw0_pitB_conv_pwi
              (qpoly_mul f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil)))) k c)
            (lw0_pitB_conv_pwi_muliter f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
            (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c))).
    + exact (lw0_pitB_conv_pwi_mul_le_iter f
               (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c).
    + apply (qleT'_trans
              (lw0_pitB_conv_pwi_muliter f (qpoly_scalar s (lw0_pitB_conv_zero_shift m (cons 1%Q nil))) k c)
              (Qabs s * lw0_pitB_conv_pwi_muliter f (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
              (Qabs s * (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c))).
      * apply qeq_leT'. apply qeqT_imp_qeq.
        exact (lw0_pitB_conv_pwi_muliter_scalar f s m k c).
      * apply (lw0_pitB_conv_mult_le_l (Qabs s)
                 (lw0_pitB_conv_pwi_muliter f (lw0_pitB_conv_zero_shift m (cons 1%Q nil)) k c)
                 (q_pow (Qabs c) m * lw0_pitB_conv_pwi_muliter f (cons 1%Q nil) k c)
                 (lw0_pitB_conv_pwi_muliter_shift f m k c)).
        apply Qle_to_QleT'. apply Qabs_nonneg.
  - apply qeq_leT'.
    rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_pwi_muliter_eq f k c)).
    ring.
Qed.

Lemma lw0_pitB_conv_pair_deltamul_weight : forall (F : QPoly) (M : nat) (c : Q),
  QleT' 0 c ->
  QleT' (lw0_pitB_conv_pwi
          (qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                         (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M)) (cons 1%Q nil)))) 0 c)
        ((1 + lw0_pitB_conv_pwi F 0 c)
         * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q).
Proof.
  intros F M c Hc0.
  assert (H01 : Qlt 0 1%Q) by (apply QltT_to_Qlt; unfold QltT; reflexivity).
  assert (Hs0 : QleT' 0 (1 / q_fact (Datatypes.S (2 * M)))).
  { apply Qle_to_QleT'. apply Qmult_le_0_compat.
    - exact (Qlt_le_weak 0%Q 1%Q H01).
    - apply Qinv_le_0_compat.
      apply (Qle_trans 0%Q 1%Q (q_fact (Datatypes.S (2 * M)))).
      + exact (Qlt_le_weak 0%Q 1%Q H01).
      + exact (QleT'_to_Qle _ _ (lw0_q_fact_ge_one (Datatypes.S (2 * M)))). }
  apply (qleT'_trans
          (lw0_pitB_conv_pwi
            (qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                           (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M)) (cons 1%Q nil)))) 0 c)
          (lw0_pitB_conv_pwi F 0 c
           * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)
          ((1 + lw0_pitB_conv_pwi F 0 c)
           * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)).
  - apply (qleT'_trans
            (lw0_pitB_conv_pwi
              (qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                             (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M)) (cons 1%Q nil)))) 0 c)
            (Qabs (1 / q_fact (Datatypes.S (2 * M)))
             * (q_pow (Qabs c) (Datatypes.S (2 * M)) * lw0_pitB_conv_pwi F 0 c))
            (lw0_pitB_conv_pwi F 0 c
             * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)).
    + exact (lw0_pitB_conv_pwi_mul_shift_domin F (1 / q_fact (Datatypes.S (2 * M)))
               (Datatypes.S (2 * M)) 0 c).
    + apply qeq_leT'.
      rewrite (lw0_Qabs_pos_eq (1 / q_fact (Datatypes.S (2 * M))) Hs0).
      rewrite (q_pow_wd (Qabs c) c (Datatypes.S (2 * M))
                 (lw0_Qabs_pos_eq c Hc0)).
      unfold Qdiv. ring.
  - apply (qleT'_trans
            (lw0_pitB_conv_pwi F 0 c
             * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)
            ((q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q
             * lw0_pitB_conv_pwi F 0 c)
            ((1 + lw0_pitB_conv_pwi F 0 c)
             * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)).
    + apply qeq_leT'. apply Qmult_comm.
    + apply (qleT'_trans
              ((q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q
               * lw0_pitB_conv_pwi F 0 c)
              ((q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q
               * (1 + lw0_pitB_conv_pwi F 0 c))
              ((1 + lw0_pitB_conv_pwi F 0 c)
               * (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q)).
      * apply (lw0_pitB_conv_mult_le_l
                 (q_pow c (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))%Q
                 (lw0_pitB_conv_pwi F 0 c) (1 + lw0_pitB_conv_pwi F 0 c)).
        -- apply Qle_to_QleT'.
           assert (Hle : Qle (lw0_pitB_conv_pwi F 0 c)
                             (lw0_pitB_conv_pwi F 0 c + 1%Q)).
           { apply (Qle_trans (lw0_pitB_conv_pwi F 0 c)
                              (lw0_pitB_conv_pwi F 0 c + 0%Q)
                              (lw0_pitB_conv_pwi F 0 c + 1%Q)).
             - rewrite Qplus_0_r. apply Qle_refl.
             - apply Qplus_le_compat.
               + apply Qle_refl.
               + exact (Qlt_le_weak 0%Q 1%Q H01). }
           rewrite (Qplus_comm 1%Q (lw0_pitB_conv_pwi F 0 c)). exact Hle.
        -- apply Qle_to_QleT'. apply Qmult_le_0_compat.
           ++ exact (q_pow_nonneg c (Datatypes.S (2 * M)) (QleT'_to_Qle _ _ Hc0)).
           ++ apply Qinv_le_0_compat.
              apply (Qle_trans 0%Q 1%Q (q_fact (Datatypes.S (2 * M)))).
              ** exact (Qlt_le_weak 0%Q 1%Q H01).
              ** exact (QleT'_to_Qle _ _ (lw0_q_fact_ge_one (Datatypes.S (2 * M)))).
      * apply qeq_leT'. apply Qmult_comm.
Qed.

Lemma lw0_pitB_conv_pair_vanish_deltam : forall (F : QPoly) (eps q : Q),
  QltT 0 eps ->
  sigT (fun M0 : nat => forall M : nat, (M0 <= M)%nat ->
    QltT (Qabs (Qabs q * qpoly_eval (lw0_qp_ai
             (qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                            (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M))
                               (cons 1%Q nil)))) 0)
             (Qabs q))) eps).
Proof.
  intros F eps q Heps.
  apply (lw0_pitB_conv_pair_vanish
           (fun M : nat => qpoly_mul F (qpoly_scalar (1 / q_fact (Datatypes.S (2 * M)))
                          (lw0_pitB_conv_zero_shift (Datatypes.S (2 * M))
                             (cons 1%Q nil))))
           (1 + lw0_pitB_conv_pwi F 0 (Qabs q)) (Qabs q) eps).
  - apply Qle_to_QleT'. apply Qabs_nonneg.
  - exact Heps.
  - apply Qlt_to_QltT.
    apply (Qlt_le_trans 0%Q 1%Q (1 + lw0_pitB_conv_pwi F 0 (Qabs q))).
    + apply QltT_to_Qlt. unfold QltT. reflexivity.
    + apply (Qle_trans 1%Q (1 + 0%Q) (1 + lw0_pitB_conv_pwi F 0 (Qabs q))).
      * rewrite Qplus_0_r. apply Qle_refl.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- exact (QleT'_to_Qle _ _ (lw0_pitB_conv_pwi_nonneg F 0 (Qabs q))).
  - intro M. exact (lw0_pitB_conv_pair_deltamul_weight F M (Qabs q)
             (Qle_to_QleT' 0 (Qabs q) (Qabs_nonneg q))).
Qed.

Lemma lw0_pitB_pair_conv : forall (q : Q) (n : nat),
  forall eps : Q, QltT 0 eps ->
  sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
    QltT (Qabs (lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp m) q
                - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
                - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
                  * qpoly_eval (lw0_sin_qp m) q
                + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
                  * qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q)) eps).
Proof.
  intros q n eps Heps.
  assert (HF2 := lw385_pair_F_plus_deriv2_niven q (Zpos (Qden q) # 1)%Q n).
  assert (Hcore := lw0_pitB_pair_conv_core q n).
  assert (Hsig2 := lw0_pitB_pair_conv_sig2 q n).
  assert (Hsinc := lw0_pitB_pair_conv_sinc q n).
  destruct (Qle_bool 0 q) eqn:Hqb.
  -                                                                    
    destruct (lw0_pitB_conv_pair_vanish_deltam
                (lw0_F (lw0_pitB_pair_conv_f q n) n) eps q Heps) as [M0 HM0].
    exists (Datatypes.S M0). intros m Hm.
    destruct m as [|j].
    + exfalso. assert (Hle := NatLe_drop _ _ Hm).
        exact (Nat.nle_succ_0 M0 Hle).
    + assert (Hj : (M0 <= Datatypes.S j)%nat).
      { assert (Hle := NatLe_drop _ _ Hm).
        exact (Nat.le_trans M0 (Datatypes.S M0) (Datatypes.S j)
                 (Nat.le_succ_diag_r M0) Hle). }
      assert (Hchain :
        lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp (Datatypes.S j)) q
        - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
        - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
          * qpoly_eval (lw0_sin_qp (Datatypes.S j)) q
        + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
          * qpoly_eval (qpoly_deriv (lw0_sin_qp (Datatypes.S j))) q
        == (q_pow (-1) (Datatypes.S j))%Q
           * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
               (lw0_pitB_pair_conv_delta (Datatypes.S j)) q).
      { rewrite (Hcore (Datatypes.S j) (HF2 (Datatypes.S j))).
        assert (HSneg : lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) q
                        == (- lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q)%Q).
        { transitivity (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) q
                          + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q
                          - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q)%Q.
          - ring.
          - rewrite (qeqT_imp_qeq _ _ (Hsig2 j q)). ring. }
        rewrite HSneg.
        rewrite <- (qeqT_imp_qeq _ _ (Hsinc j q)).
        ring. }
      assert (Habs : QeqT
        (Qabs (lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp (Datatypes.S j)) q
              - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
              - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
                * qpoly_eval (lw0_sin_qp (Datatypes.S j)) q
              + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
                * qpoly_eval (qpoly_deriv (lw0_sin_qp (Datatypes.S j))) q))
        (Qabs ((q_pow (-1) (Datatypes.S j))%Q
               * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                   (lw0_pitB_pair_conv_delta (Datatypes.S j)) q))).
      { apply qeq_imp_qeqT. apply lw0_pitB_pair_conv_qabs_wd. exact Hchain. }
      assert (Hfin :
        QeqT (Qabs ((q_pow (-1) (Datatypes.S j))%Q
                      * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (lw0_pitB_pair_conv_delta (Datatypes.S j)) q))
             (Qabs (Qabs q * qpoly_eval (lw0_qp_ai
                         (qpoly_mul (lw0_F (lw0_pitB_pair_conv_f q n) n)
                            (lw0_pitB_pair_conv_delta (Datatypes.S j))) 0)
                     (Qabs q)))).
      { apply qeq_imp_qeqT.
        transitivity (Qabs (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_pitB_pair_conv_delta (Datatypes.S j)) q)).
        - rewrite Qabs_Qmult.
          rewrite lw0_pitB_pair_conv_qabs_sign1. ring.
        - apply lw0_pitB_pair_conv_qabs_wd.
          transitivity (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (lw0_pitB_pair_conv_delta (Datatypes.S j)) (Qabs q)).
          + exact (qeqT_imp_qeq _ _
                     (lw385_pair_abs_shore (lw0_F (lw0_pitB_pair_conv_f q n) n)
                        (lw0_pitB_pair_conv_delta (Datatypes.S j)) q
                        (Qle_to_QleT' 0 q (Qle_bool_imp_le 0 q Hqb)))).
          + unfold lw0_qp_pair, lw0_qp_antideriv. cbn [qpoly_eval]. ring. }
      exact (lw0_pitB_conv_qeqL_ltT _ _ _ Habs
               (lw0_pitB_conv_qeqL_ltT _ _ _ Hfin (HM0 (Datatypes.S j) Hj))).
  -                                                                
    assert (Hnle : ~ (0 <= q)%Q).
    { intros Hc. rewrite (proj2 (Qle_bool_iff 0 q) Hc) in Hqb. discriminate Hqb. }
    assert (Hq_u : q == (- Qabs q)%Q).
    { apply (Qabs_case q (fun z => (q == - z)%Q)).
      - intros Hc. rewrite (proj2 (Qle_bool_iff 0 q) Hc) in Hqb. discriminate Hqb.
      - intros Hq0. ring. }
    destruct (lw0_pitB_conv_pair_vanish_deltam
                (lw385_flip_aux false (lw0_F (lw0_pitB_pair_conv_f q n) n)) eps q Heps)
      as [M0 HM0].
    exists (Datatypes.S M0). intros m Hm.
    destruct m as [|j].
    + exfalso. assert (Hle := NatLe_drop _ _ Hm).
        exact (Nat.nle_succ_0 M0 Hle).
    + assert (Hj : (M0 <= Datatypes.S j)%nat).
      { assert (Hle := NatLe_drop _ _ Hm).
        exact (Nat.le_trans M0 (Datatypes.S M0) (Datatypes.S j)
                 (Nat.le_succ_diag_r M0) Hle). }
      assert (Hchain :
        lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp (Datatypes.S j)) q
        - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
        - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
          * qpoly_eval (lw0_sin_qp (Datatypes.S j)) q
        + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
          * qpoly_eval (qpoly_deriv (lw0_sin_qp (Datatypes.S j))) q
        == (q_pow (-1) (Datatypes.S j))%Q
           * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
               (lw0_pitB_pair_conv_delta (Datatypes.S j)) q).
      { rewrite (Hcore (Datatypes.S j) (HF2 (Datatypes.S j))).
        assert (HSneg : lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) q
                        == (- lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q)%Q).
        { transitivity (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (qpoly_deriv_iter 2 (lw0_sin_qp (Datatypes.S j))) q
                          + lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q
                          - lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_sin_qp j) q)%Q.
          - ring.
          - rewrite (qeqT_imp_qeq _ _ (Hsig2 j q)). ring. }
        rewrite HSneg.
        rewrite <- (qeqT_imp_qeq _ _ (Hsinc j q)).
        ring. }
      assert (Habs : QeqT
        (Qabs (lw0_qp_pair (lw0_pitB_pair_conv_f q n) (lw0_sin_qp (Datatypes.S j)) q
              - qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) 0
              - qpoly_eval (qpoly_deriv (lw0_F (lw0_pitB_pair_conv_f q n) n)) q
                * qpoly_eval (lw0_sin_qp (Datatypes.S j)) q
              + qpoly_eval (lw0_F (lw0_pitB_pair_conv_f q n) n) q
                * qpoly_eval (qpoly_deriv (lw0_sin_qp (Datatypes.S j))) q))
        (Qabs ((q_pow (-1) (Datatypes.S j))%Q
               * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                   (lw0_pitB_pair_conv_delta (Datatypes.S j)) q))).
      { apply qeq_imp_qeqT. apply lw0_pitB_pair_conv_qabs_wd. exact Hchain. }
      assert (Hfin :
        QeqT (Qabs ((q_pow (-1) (Datatypes.S j))%Q
                      * lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                          (lw0_pitB_pair_conv_delta (Datatypes.S j)) q))
             (Qabs (Qabs q * qpoly_eval (lw0_qp_ai
                         (qpoly_mul (lw385_flip_aux false
                                       (lw0_F (lw0_pitB_pair_conv_f q n) n))
                            (lw0_pitB_pair_conv_delta (Datatypes.S j))) 0)
                     (Qabs q)))).
      { apply qeq_imp_qeqT.
        transitivity (Qabs (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                              (lw0_pitB_pair_conv_delta (Datatypes.S j)) q)).
        - rewrite Qabs_Qmult.
          rewrite lw0_pitB_pair_conv_qabs_sign1. ring.
        - transitivity (Qabs (lw0_qp_pair (lw0_F (lw0_pitB_pair_conv_f q n) n)
                                (lw0_pitB_pair_conv_delta (Datatypes.S j))
                                (- Qabs q)%Q)).
          + apply lw0_pitB_pair_conv_qabs_wd.
            exact (qeqT_imp_qeq _ _
                     (lw385_pair_q_wd (lw0_F (lw0_pitB_pair_conv_f q n) n)
                        (lw0_pitB_pair_conv_delta (Datatypes.S j)) q
                        (- Qabs q)%Q Hq_u)).
          + transitivity (Qabs (- lw0_qp_pair (lw385_flip_aux false
                                    (lw0_F (lw0_pitB_pair_conv_f q n) n))
                                (lw0_pitB_pair_conv_delta (Datatypes.S j))
                                (Qabs q))%Q).
            * apply lw0_pitB_pair_conv_qabs_wd.
              exact (qeqT_imp_qeq _ _
                       (lw385_pair_flip_shore_mono (Datatypes.S j)
                          (1 / q_fact (Datatypes.S (2 * Datatypes.S j)))%Q
                          (lw0_F (lw0_pitB_pair_conv_f q n) n) (Qabs q))).
            * change (lw0_pitB_pair_conv_delta (Datatypes.S j))
                with (qpoly_scalar (1 / q_fact (Datatypes.S (2 * Datatypes.S j)))%Q
                        (lw0_pitB_conv_zero_shift (Datatypes.S (2 * Datatypes.S j))
                           (cons 1%Q nil))).
              rewrite Qabs_opp.
              apply lw0_pitB_pair_conv_qabs_wd.
              unfold lw0_qp_pair, lw0_qp_antideriv. cbn [qpoly_eval]. ring. }
      exact (lw0_pitB_conv_qeqL_ltT _ _ _ Habs
               (lw0_pitB_conv_qeqL_ltT _ _ _ Hfin (HM0 (Datatypes.S j) Hj))).
Qed.

Lemma lw0_pitB_pair_rtail_vanish : forall (q : Q) (n : nat), forall eps : Q, QltT 0 eps ->
  sigT (fun Mt : nat => forall m : nat, NatLe Mt m ->
    QltT (Qabs (lw0_pitB_pair_rtail q n m)) eps).
Proof.
  intros q n eps Heps.
  exact (lw0_pitB_pair_rtail_vanish_hpair q n (lw0_pitB_pair_conv q n) eps Heps).
Qed.
(* ---------- The K integer witness chain (carried verbatim from the
   region [L5217-L5375] of [LW0PiIrrational.v]) ---------- *)

Lemma lw0_z_lo_integer : forall (a b : Z) (n k : nat),
  sigT (fun w : Z => Qeq (lw0_z_lo a b n k) ((w # 1)%Q)).
Proof.
  intros a b n k.
  exists (lw0_zsign (k - n) * Z.of_nat (lw0_binom n (k - n))
          * Zpower_nat a ((2 * n) - k) * Zpower_nat b (k - n)
          * Z.of_nat (lw0_ratio n k))%Z.
  unfold lw0_z_lo.
  apply (lw0_Qmake_mul
          (lw0_zsign (k - n) * Z.of_nat (lw0_binom n (k - n))
            * Zpower_nat a ((2 * n) - k) * Zpower_nat b (k - n))
          (Z.of_nat (lw0_ratio n k))).
Qed.

Lemma lw0_z_hi_integer : forall (a b : Z) (n k : nat), (k <= n)%nat ->
  sigT (fun w : Z => Qeq (lw0_z_hi a b n k) ((w # 1)%Q)).
Proof.
  intros a b n k Hk.
  exists (lw0_zsign (n - k) * Z.of_nat (lw0_binom n (n - k))
          * Zpower_nat a k * Zpower_nat b (n - k)
          * Z.of_nat (lw0_ratio n (2 * n - k)))%Z.
  unfold lw0_z_hi.
  apply (lw0_Qmake_mul
          (lw0_zsign (n - k) * Z.of_nat (lw0_binom n (n - k))
            * Zpower_nat a k * Zpower_nat b (n - k))
          (Z.of_nat (lw0_ratio n (2 * n - k)))).
Qed.

Lemma lw0_sigT_plus : forall v1 v2 : Q,
  sigT (fun w : Z => Qeq v1 ((w # 1)%Q)) ->
  sigT (fun w : Z => Qeq v2 ((w # 1)%Q)) ->
  sigT (fun w : Z => Qeq (v1 + v2) ((w # 1)%Q)).
Proof.
  intros v1 v2 [z1 Hz1] [z2 Hz2].
  exists (z1 + z2)%Z.
  assert (Hs : v1 + v2 == (z1 # 1)%Q + (z2 # 1)%Q)
    by (apply Qplus_comp; assumption).
  transitivity ((z1 # 1)%Q + (z2 # 1)%Q)%Q.
  - exact Hs.
  - apply lw0_Qmake_plus.
Qed.

Lemma lw0_sigT_Zscale : forall (u : Z) (v : Q),
  sigT (fun w : Z => Qeq v ((w # 1)%Q)) ->
  sigT (fun w : Z => Qeq ((u # 1)%Q * v) ((w # 1)%Q)).
Proof.
  intros u v [z Hz].
  exists (u * z)%Z.
  assert (Hm : (u # 1)%Q * v == (u # 1)%Q * (z # 1)%Q)
    by (apply Qmult_comp; [apply Qeq_refl | exact Hz]).
  transitivity ((u # 1)%Q * (z # 1)%Q)%Q.
  - exact Hm.
  - apply lw0_Qmake_mul.
Qed.

Lemma lw0_qsum_integer : forall (g : nat -> Q) (m : nat),
  (forall j : nat, sigT (fun w : Z => Qeq (g j) ((w # 1)%Q))) ->
  sigT (fun w : Z => Qeq (lw0_qsum g m) ((w # 1)%Q)).
Proof.
  intros g m.
  induction m as [|m' IH]; intros Hg.
  - exact (Hg 0%nat).
  - change (lw0_qsum g (Datatypes.S m'))
      with (lw0_qsum g m' + g (Datatypes.S m'))%Q.
    apply lw0_sigT_plus.
    + apply IH. exact Hg.
    + exact (Hg (Datatypes.S m')).
Qed.

Lemma lw0_K_leg_integer : forall (a b : Z) (n j : nat),
  sigT (fun w : Z => Qeq (lw0_K_leg a b n j) ((w # 1)%Q)).
Proof.
  intros a b n j. unfold lw0_K_leg.
  destruct (Nat.leb n (2 * j)) eqn:Hg.
  - apply Nat.leb_le in Hg.
    change (if true then lw0_z_lo a b n (2 * j) + lw0_z_hi a b n (2 * (n - j))
            else (0 # 1)%Q)
      with (lw0_z_lo a b n (2 * j) + lw0_z_hi a b n (2 * (n - j)))%Q.
    apply lw0_sigT_Zscale.
    apply lw0_sigT_plus.
    + exact (lw0_z_lo_integer a b n (2 * j)).
    + assert (Hhi : (2 * (n - j) <= n)%nat).
      { replace (2 * (n - j))%nat with (2 * n - 2 * j)%nat
          by (symmetry; apply Nat.mul_sub_distr_l).
        apply (Nat.le_trans (2 * n - 2 * j)%nat (2 * n - n)%nat n).
        - exact (Nat.sub_le_mono_l n (2 * j) (2 * n) Hg).
        - replace (2 * n)%nat with (n + n)%nat by ring.
          rewrite Nat.add_sub. apply Nat.le_refl. }
      exact (lw0_z_hi_integer a b n (2 * (n - j)) Hhi).
  - exists 0%Z.
    change (if false then lw0_z_lo a b n (2 * j) + lw0_z_hi a b n (2 * (n - j))
            else (0 # 1)%Q)
      with ((0 # 1)%Q)%Q.
    transitivity (((lw0_zsign j * 0)%Z # 1)%Q).
    + apply lw0_Qmake_mul.
    + rewrite Z.mul_0_r. reflexivity.
Qed.

Lemma lw0_K_integer : forall (a b : Z) (n : nat),
  sigT (fun w : Z => Qeq (lw0_K a b n) ((w # 1)%Q)).
Proof.
  intros a b n. unfold lw0_K.
  apply lw0_qsum_integer.
  intros j. apply lw0_K_leg_integer.
Qed.

Lemma lw0_pi_contra_gate : forall (v : Q) (z : Z),
  QltT 0 v -> QltT v 1 -> Qeq v ((z # 1)%Q) -> Id false true.
Proof.
  intros v z Hv0 Hv1 Hz.
  destruct z as [| p | p].
  - assert (Hc : (0 ?= v)%Q = (0 ?= (0 # 1))%Q).
    { exact (Qcompare_comp 0 0 (Qeq_refl 0) v (0 # 1) Hz). }
    unfold QltT, Qlt_bool in Hv0. rewrite Hc in Hv0. cbn in Hv0. inversion Hv0.
  - assert (Hc : ((Z.pos p # 1) ?= 1)%Q = (v ?= 1)%Q).
    { exact (Qcompare_comp (Z.pos p # 1) v (Qeq_sym v (Z.pos p # 1) Hz) 1 1 (Qeq_refl 1)). }
    assert (Hge : QleT' 1 ((Z.pos p) # 1)%Q).
    { unfold QleT'. destruct p; reflexivity. }
    unfold QltT, Qlt_bool in Hv1. rewrite <- Hc in Hv1.
    assert (Hbad : QltT 1 1).
    { apply (lw0_leT'_ltT_trans 1 ((Z.pos p) # 1) 1); assumption. }
    unfold QltT, Qlt_bool in Hbad. cbn in Hbad. inversion Hbad.
  - assert (Hc : (0 ?= v)%Q = (0 ?= (Z.neg p # 1))%Q).
    { exact (Qcompare_comp 0 0 (Qeq_refl 0) v (Z.neg p # 1) Hz). }
    unfold QltT, Qlt_bool in Hv0. rewrite Hc in Hv0. cbn in Hv0. inversion Hv0.
Qed.

(* ---------- The contradiction chain (carried verbatim from
   [Local/LW0LeibSeparation.v]; source coordinates of the migrated
   statements) ---------- *)

(* ============================================================ *)

(* Tool piece one: the three-term [Qabs] triangle (the generic-form
   core of the three-point inequality of the main gap piece). *)

Lemma leibsep_abs3_split : forall A B C : Q,
  QleT' (Qabs (A + B + C)) (Qabs A + Qabs B + Qabs C).
Proof.
  intros A B C. apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs A + Qabs (B + C))).
  - setoid_replace (A + B + C) with (A + (B + C)) by ring.
    apply Qabs_triangle.
  - setoid_replace (Qabs A + Qabs B + Qabs C)
      with (Qabs A + (Qabs B + Qabs C)) by ring.
    apply Qplus_le_compat.
    + apply Qle_refl.
    + apply Qabs_triangle.
Qed.

(* ---------- The telescope identity and endpoint-correction squeeze
   engine (carried verbatim from the source) ---------- *)

Lemma lw0_pitB_pair_telescope : forall (q : Q) (n m : nat),
  lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp m) q
  == lw0_K (Qnum q) (Zpos (Qden q)) n
     + (-1)%Q * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
         * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
     + qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
         * qpoly_eval (lw0_sin_qp m) q
     + lw0_pitB_pair_rtail q n m.
Proof.
  intros q n m.
  unfold lw0_pitB_pair_rtail.
  ring.
Qed.

Lemma leibsep_pair_slack_bound : forall (q : Q) (n m : nat),
  QleT' (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                           (lw0_sin_qp m) q
                - lw0_K (Qnum q) (Zpos (Qden q)) n))
        (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
         * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
         + Qabs (qpoly_eval (qpoly_deriv
                  (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
           * Qabs (qpoly_eval (lw0_sin_qp m) q)
         + Qabs (lw0_pitB_pair_rtail q n m))%Q.
Proof.
  intros q n m.
  pose proof (lw0_pitB_pair_telescope q n m) as HT.
  assert (HE : (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                            (lw0_sin_qp m) q
                - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q
               == ((-1)%Q
                    * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                    * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                   + qpoly_eval (qpoly_deriv
                          (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                     * qpoly_eval (lw0_sin_qp m) q
                   + lw0_pitB_pair_rtail q n m)%Q)
    by (rewrite HT; ring).
  apply (qleT'_trans
          (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp m) q
                  - lw0_K (Qnum q) (Zpos (Qden q)) n))
          (Qabs ((-1)%Q
                  * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                  * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                 + qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                   * qpoly_eval (lw0_sin_qp m) q
                 + lw0_pitB_pair_rtail q n m))).
  - apply qeq_leT'. apply Qabs_wd. exact HE.
  - apply (qleT'_trans
            (Qabs ((-1)%Q
                    * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                    * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
                   + qpoly_eval (qpoly_deriv
                          (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                     * qpoly_eval (lw0_sin_qp m) q
                   + lw0_pitB_pair_rtail q n m))
            (Qabs ((-1)%Q
                    * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q
                    * (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q))
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q
                     * qpoly_eval (lw0_sin_qp m) q)
             + Qabs (lw0_pitB_pair_rtail q n m))
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * Qabs (qpoly_eval (lw0_sin_qp m) q)
             + Qabs (lw0_pitB_pair_rtail q n m))).
    + exact (leibsep_abs3_split _ _ _).
    + apply qeq_leT'.
      rewrite (Qabs_Qmult
                ((-1)%Q * qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
                (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)).
      rewrite (Qabs_Qmult (-1)%Q
                (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)).
      rewrite (Qabs_Qmult
                (qpoly_eval (qpoly_deriv
                       (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
                (qpoly_eval (lw0_sin_qp m) q)).
      assert (E1 : Qabs (-1)%Q == 1%Q) by reflexivity.
      rewrite E1. ring.
Qed.

Lemma leibsep_G4c_pair_slack_window_from : forall (q : Q) (n : nat) (s t : Q) (M0 : nat),
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t) ->
  forall eps : Q, QltT 0 eps ->
  sigT (fun M : nat => forall m : nat, NatLe M m ->
    QleT' (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp m) q
                  - lw0_K (Qnum q) (Zpos (Qden q)) n))
          (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
           * t
           + Qabs (qpoly_eval (qpoly_deriv
                      (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
             * s
           + eps)%Q).
Proof.
  intros q n s t M0 Hs Ht eps Heps.
  destruct (lw0_pitB_pair_rtail_vanish q n eps Heps) as [Mt HMt].
  exists (Nat.max M0 Mt). intros m Hm.
  pose proof (NatLe_drop (Nat.max M0 Mt) m Hm) as Hmax.
  assert (HmM0 : (M0 <= m)%nat).
  { apply (Nat.le_trans M0 (Nat.max M0 Mt) m (Nat.le_max_l M0 Mt) Hmax). }
  assert (HmMt : (Mt <= m)%nat).
  { apply (Nat.le_trans Mt (Nat.max M0 Mt) m (Nat.le_max_r M0 Mt) Hmax). }
  pose proof (leibsep_pair_slack_bound q n m) as HB.
  apply (qleT'_trans
          (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp m) q
                  - lw0_K (Qnum q) (Zpos (Qden q)) n))
          (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
           * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
           + Qabs (qpoly_eval (qpoly_deriv
                      (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
             * Qabs (qpoly_eval (lw0_sin_qp m) q)
           + Qabs (lw0_pitB_pair_rtail q n m))
          (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
           * t
           + Qabs (qpoly_eval (qpoly_deriv
                      (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
             * s
           + eps)).
  - exact HB.
  - apply (qleT'_trans
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * Qabs (qpoly_eval (lw0_sin_qp m) q)
             + Qabs (lw0_pitB_pair_rtail q n m))
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * t
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * s
             + Qabs (lw0_pitB_pair_rtail q n m))
            (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)
             * t
             + Qabs (qpoly_eval (qpoly_deriv
                        (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)
               * s
             + eps)).
    + apply qleT'_plus_compat.
      * apply qleT'_plus_compat.
        -- exact (lw0_qcompat_l
                    (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q
                           + (1 # 1)%Q))
                    t
                    (Qabs (qpoly_eval
                             (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)
                             q))
                    (Ht m HmM0)
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))).
        -- exact (lw0_qcompat_l
                    (Qabs (qpoly_eval (lw0_sin_qp m) q))
                    s
                    (Qabs (qpoly_eval
                             (qpoly_deriv
                                (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n))
                             q))
                    (Hs m HmM0)
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))
                    (Qle_to_QleT' _ _ (Qabs_nonneg _))).
      * apply qleT'_refl.
    + apply qleT'_plus_compat.
      * apply qleT'_refl.
      * apply Qle_to_QleT'. apply Qlt_le_weak. apply QltT_to_Qlt.
        exact (HMt m (NatLe_lift _ _ HmMt)).
Qed.

Lemma leibsep_beta_contra : forall (q : Q) (n : nat) (s t : Q) (M0 : nat) (eps : Q),
  QltT 0 ((Zpos (Qden q) # 1)%Q) ->
  QltT 0 q ->
  QleT' q (10 / 3)%Q ->
  (2 <= n)%nat ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t) ->
  QltT 0 eps ->
  QltT (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
        + (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q) * t
           + Qabs (qpoly_eval (qpoly_deriv
                    (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q) * s
           + eps)%Q) 1 ->
  QltT (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q) * t
        + Qabs (qpoly_eval (qpoly_deriv
                 (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q) * s
        + eps)
       (q_fact n * (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                    - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat))%Q ->
  Id false true.
Proof.
  intros q n s t M0 eps Hb Hq Hq103 Hn Hs Ht Heps Hup Hlow.
  pose (c := (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q) * t
              + Qabs (qpoly_eval (qpoly_deriv
                       (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q) * s
              + eps)%Q).
  assert (Hb0 : QleT' 0 ((Zpos (Qden q) # 1)%Q))
    by (apply lw0_QltT_le; exact Hb).
  assert (Hnn : forall k : nat, QleT' 0 (lw0_Wb (Zpos (Qden q) # 1)%Q q n k)).
  { intros k. apply lw0_Wb_seq_nonneg; [exact Hb0 | exact Hq]. }
  assert (Hdc : forall k : nat,
    QleT' (lw0_Wb (Zpos (Qden q) # 1)%Q q n (Datatypes.S k))
          (lw0_Wb (Zpos (Qden q) # 1)%Q q n k)).
  { intros k. apply lw0_Wb_seq_decr;
      [exact Hb0 | exact Hq | exact Hq103 | exact Hn]. }
  destruct (leibsep_G4c_pair_slack_window_from q n s t M0 Hs Ht eps Heps) as [Mt HMt].
  pose proof (HMt Mt (NatLe_lift Mt Mt (Nat.le_refl Mt))) as Hg.
  assert (Hr0le : Qle 0%Q (q_fact n)).
  { apply Qlt_le_weak. exact (q_fact_pos n). }
  assert (Hr0 : ~ q_fact n == 0%Q).
  { intro Hc. apply (Qlt_not_eq 0 (q_fact n) (q_fact_pos n)). symmetry. exact Hc. }
  assert (HE0 : forall x : Q, ((1 / q_fact n) * x) * q_fact n == x).
  { intros x. unfold Qdiv.
    rewrite Qmult_1_l.
    rewrite (Qmult_comm (/ q_fact n) x).
    rewrite <- Qmult_assoc.
    rewrite (Qmult_comm (/ q_fact n) (q_fact n)).
    rewrite (Qmult_inv_r (q_fact n) Hr0).
    apply Qmult_1_r. }
  destruct (leibsep_altsum_two_shore (lw0_Wb (Zpos (Qden q) # 1)%Q q n) Hnn Hdc Mt)
    as [HloA HhiA].
  pose proof (lw0_pitB_bridge Mt (Zpos (Qden q) # 1)%Q q n) as Hbr.
  assert (HA : QleT' (1 / q_fact n
                      * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                    (lw0_sin_qp Mt) q)%Q
                     (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
  { apply (qleT'_trans
            (1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                          (lw0_sin_qp Mt) q)%Q
            (altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) (Datatypes.S Mt))
            (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
    - apply qeq_leT'. symmetry. exact Hbr.
    - exact HhiA. }
  assert (HB : QleT' ((1 / q_fact n
                       * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                     (lw0_sin_qp Mt) q) * q_fact n)%Q
                     (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat * q_fact n)%Q).
  { apply Qle_to_QleT'.
    apply Qmult_le_compat_r.
    - exact (QleT'_to_Qle _ _ HA).
    - exact Hr0le. }
  assert (HU : QleT' (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                           (lw0_sin_qp Mt) q)
                     (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
  { apply (qleT'_trans
            (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q)
            ((1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                              (lw0_sin_qp Mt) q) * q_fact n)%Q
            (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
    - apply qeq_leT'. symmetry. apply HE0.
    - apply (qleT'_trans
              ((1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                (lw0_sin_qp Mt) q) * q_fact n)%Q
              (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat * q_fact n)%Q
              (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat)).
      + exact HB.
      + apply qeq_leT'. ring. }
  assert (HA2 : QleT' (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                       - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat)%Q
                      (1 / q_fact n
                       * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                     (lw0_sin_qp Mt) q)%Q).
  { apply (qleT'_trans
            (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
             - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat)%Q
            (altsum (lw0_Wb (Zpos (Qden q) # 1)%Q q n) (Datatypes.S Mt))
            (1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                          (lw0_sin_qp Mt) q)%Q).
    - exact HloA.
    - apply qeq_leT'. exact Hbr. }
  assert (HB2 : QleT' ((lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                        - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat) * q_fact n)%Q
                      ((1 / q_fact n
                        * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                      (lw0_sin_qp Mt) q) * q_fact n)%Q).
  { apply Qle_to_QleT'.
    apply Qmult_le_compat_r.
    - exact (QleT'_to_Qle _ _ HA2).
    - exact Hr0le. }
  assert (HL : QleT' (q_fact n * (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                                  - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat))%Q
                     (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                   (lw0_sin_qp Mt) q)).
  { apply (qleT'_trans
            (q_fact n * (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                         - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat))%Q
            ((lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
              - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat) * q_fact n)%Q
            (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q)).
    - apply qeq_leT'. ring.
    - apply (qleT'_trans
              ((lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat) * q_fact n)%Q
              ((1 / q_fact n * lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                (lw0_sin_qp Mt) q) * q_fact n)%Q
              (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q)).
      + exact HB2.
      + apply qeq_leT'. apply HE0. }
  assert (Hdom : QleT' ((lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                              (lw0_sin_qp Mt) q
                        - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q) c).
  { exact (qleT'_trans _ _ _ (leibsep_abs_ge_self _) Hg). }
  assert (Hdom' : QleT' ((lw0_K (Qnum q) (Zpos (Qden q)) n
                          - lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                        (lw0_sin_qp Mt) q)%Q) c).
  { apply (qleT'_trans
            ((lw0_K (Qnum q) (Zpos (Qden q)) n
              - lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                            (lw0_sin_qp Mt) q)%Q)
            (Qopp (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp Mt) q
                   - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)
            c).
    - apply qeq_leT'. ring.
    - apply (qleT'_trans
              (Qopp (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                 (lw0_sin_qp Mt) q
                     - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)
              (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                 (lw0_sin_qp Mt) q
                     - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)
              c).
      + apply (qleT'_trans
                (Qopp (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                   (lw0_sin_qp Mt) q
                       - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)
                (Qopp (Qopp (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                                (lw0_sin_qp Mt) q
                                    - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)))
                (Qabs (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                                   (lw0_sin_qp Mt) q
                       - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q)).
        * apply lw0_opp_le_swap.
          exact (leibsep_abs_ge_opp
                  (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp Mt) q
                    - lw0_K (Qnum q) (Zpos (Qden q)) n)%Q).
        * apply qeq_leT'. ring.
      + exact Hg. }
  assert (HPU1 : QleT' (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                             (lw0_sin_qp Mt) q)
                       (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q).
  { apply (qleT'_trans
            (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q)
            ((lw0_K (Qnum q) (Zpos (Qden q)) n
              + (lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q
                 - lw0_K (Qnum q) (Zpos (Qden q)) n))%Q)
            (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat; [apply qleT'_refl | exact Hdom]. }
  assert (HKU : QleT' (lw0_K (Qnum q) (Zpos (Qden q)) n)
                      (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat + c)%Q).
  { apply (qleT'_trans
            (lw0_K (Qnum q) (Zpos (Qden q)) n)
            ((lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) (lw0_sin_qp Mt) q
              + (lw0_K (Qnum q) (Zpos (Qden q)) n
                 - lw0_qp_pair (lw0_niven_f q (Zpos (Qden q) # 1)%Q n)
                               (lw0_sin_qp Mt) q))%Q)
            (q_fact n * lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat + c)%Q).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat; [exact HU | exact Hdom']. }
  assert (H1K : QltT (lw0_K (Qnum q) (Zpos (Qden q)) n) 1).
  { apply Qlt_to_QltT.
    exact (Qle_lt_trans _ _ _ (QleT'_to_Qle _ _ HKU) (QltT_to_Qlt _ _ Hup)). }
  assert (HLOW2 : QleT' (q_fact n * (lw0_Wb (Zpos (Qden q) # 1)%Q q n 0%nat
                                     - lw0_Wb (Zpos (Qden q) # 1)%Q q n 1%nat))%Q
                        (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q).
  { exact (qleT'_trans _ _ _ HL HPU1). }
  assert (Hlt1 : Qlt c (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q).
  { exact (Qlt_le_trans _ _ _ (QltT_to_Qlt _ _ Hlow) (QleT'_to_Qle _ _ HLOW2)). }
  assert (H0K : Qlt 0%Q (lw0_K (Qnum q) (Zpos (Qden q)) n)).
  { apply (leibsep_qlt_wd2 0%Q
             ((lw0_K (Qnum q) (Zpos (Qden q)) n + c) - c)%Q
             0%Q (lw0_K (Qnum q) (Zpos (Qden q)) n)).
    - apply Qeq_refl.
    - assert (HE : ((lw0_K (Qnum q) (Zpos (Qden q)) n + c) - c)%Q
                   == lw0_K (Qnum q) (Zpos (Qden q)) n) by ring.
      exact HE.
    - exact (proj1 (Qlt_minus_iff c
                      (lw0_K (Qnum q) (Zpos (Qden q)) n + c)%Q) Hlt1). }
  destruct (lw0_K_integer (Qnum q) (Zpos (Qden q)) n) as [z Hz].
  exact (lw0_pi_contra_gate (lw0_K (Qnum q) (Zpos (Qden q)) n) z
           (Qlt_to_QltT _ _ H0K) H1K Hz).
Qed.

Lemma leibsep_false_branch_contra :
  forall (q : Q) (k j : nat) (s t : Q) (M0 : nat) (eps : Q),
  QltT 0 q ->
  QleT' q (10 / 3)%Q ->
  QltT 0 eps ->
  (1 <= j)%nat ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t) ->
  QleT' (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                             (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))
                           (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j)) q) * t
         + Qabs (qpoly_eval (qpoly_deriv
                  (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))
                  (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))) q) * s
         + eps)%Q
        (1 # 2)%Q ->
  QltT (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                            (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))
                          (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j)) q) * t
        + Qabs (qpoly_eval (qpoly_deriv
                 (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                   (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))
                 (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j))) q) * s
        + eps)%Q
       (q_fact (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j)
        * (lw0_Wb (Zpos (Qden q) # 1)%Q q
             (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j) 0%nat
           - lw0_Wb (Zpos (Qden q) # 1)%Q q
             (lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) k + j) 1%nat))%Q ->
  Id false true.
Proof.
  intros q k j s t M0 eps Hq Hq103 Heps Hj Hs Ht HCA HCB.
  pose (b := (Zpos (Qden q) # 1)%Q).
  pose (n0 := (lw0_n_select (10 * lw0_pi_d0_of b) k + j)%nat).
  pose (C := (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b n0) n0) q) * t
             + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b n0) n0)) q) * s
             + eps)%Q).
  assert (Hbh : QltT 0 b) by apply lw0_pi_b_den_pos.
  assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
  assert (Hbabs : b == Qabs b).
  { symmetry. apply Qabs_pos. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hbh. }
  assert (Hbd0 : QleT' b (lw0_q_of_nat (lw0_pi_d0_of b))).
  { apply (qleT'_trans _ (Qabs b) _).
    - apply qeq_leT'. exact Hbabs.
    - apply lw0_pi_d0_absorb. exact (qeq_ltT b (Qabs b) Hbabs Hbh). }
  assert (Hn : (2 <= n0)%nat).
  { unfold n0, lw0_n_select.
    replace ((22 + 2 * Nat.max k (10 * lw0_pi_d0_of b) + j)%nat)
      with ((2 + (20 + (2 * Nat.max k (10 * lw0_pi_d0_of b) + j)))%nat) by ring.
    apply Nat.le_add_r. }
  assert (Hv : QltT (q_fact n0 * lw0_Wb b q n0 0)%Q (1 # 2)%Q).
  { exact (leibsep_w0n_half b q (lw0_pi_d0_of b) k j Hbh Hq0 Hq103 Hbd0 Hj). }
  assert (Hup : QltT (q_fact n0 * lw0_Wb b q n0 0 + C)%Q 1%Q).
  { apply Qlt_to_QltT.
    assert (Hvlt : Qlt (q_fact n0 * lw0_Wb b q n0 0)%Q (1 # 2)%Q)
      by (apply QltT_to_Qlt; exact Hv).
    assert (HvC : Qlt (q_fact n0 * lw0_Wb b q n0 0 + C)%Q ((1 # 2) + C)%Q).
    { exact (proj2 (Qplus_lt_l (q_fact n0 * lw0_Wb b q n0 0) (1 # 2)%Q C) Hvlt). }
    assert (HleC : Qle ((1 # 2) + C)%Q 1%Q).
    { apply QleT'_to_Qle.
      apply (qleT'_trans _ ((1 # 2) + (1 # 2))%Q _).
      - apply qleT'_plus_compat; [apply qleT'_refl | exact HCA].
      - apply qeq_leT'. ring. }
    exact (Qlt_le_trans _ _ _ HvC HleC). }
  exact (leibsep_beta_contra q n0 s t M0 eps Hbh Hq Hq103 Hn Hs Ht Heps Hup HCB).
Qed.

(* ---------- The four gate pieces plus the self-supplied tail_bounded
   (the gate definition and the true piece verbatim from source
   [L53]/[L182]; the guarded/false proof bodies verbatim from
   [L226-L256]/[L2765-L2783]; tail_bounded proved anew, carried by the
   four-case [leiblw_S_tail_bound], isomorphic to the slot-1 statement
   of [LW0MLicBridge]) ---------- *)

Definition leibsep_gate_open (q : Q) (N : nat) (c0 : Q) : bool :=
  match (lw0m_e N + 2 * c0) ?= Qabs ((lw0m_xL N - q)%Q) with
  | Lt => true
  | _ => false
  end.

Lemma leibsep_gate_open_true : forall (q : Q) (N : nat) (c0 : Q),
  leibsep_gate_open q N c0 = true ->
  QltT (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - q)%Q)).
Proof.
  intros q N c0 H. unfold leibsep_gate_open in H.
  destruct (lw0m_e N + 2 * c0 ?= Qabs ((lw0m_xL N - q)%Q))%Q eqn:Hcmp.
  - discriminate H.
  - apply Qlt_to_QltT. apply Qlt_alt. exact Hcmp.
  - discriminate H.
Qed.

Lemma lw0m_tail_bounded_pi : forall (N m : nat), (1 <= N)%nat -> NatLe N m ->
  Qlt (Qabs ((lw0m_xL m - lw0m_xL N)%Q)) (lw0m_e N).
Proof.
  intros N m HN1 Hm.
  assert (Hnm : (N <= m)%nat) by exact (NatLe_drop N m Hm).
  apply (Qle_lt_trans (Qabs ((lw0m_xL m - lw0m_xL N)%Q))
           (4 # Pos.of_succ_nat (4 * N + 4)) (lw0m_e N)).
  - apply (Qle_trans (Qabs ((lw0m_xL m - lw0m_xL N)%Q))
             (Qabs (PiWindowCore.leiblw_t (2 * N + 2)))
             (4 # Pos.of_succ_nat (4 * N + 4))).
    + unfold lw0m_xL. rewrite !leiblw_xL_eq_S.
      rewrite piL_qabs_sym.
      apply (piL_seq_pair_bound N m Hnm).
    + rewrite (piL_t_2p2_even N).
      assert (HX : QleT' 0 (4 # Pos.of_succ_nat (4 * N + 4))).
      { apply Qle_to_QleT'. apply (Qlt_le_weak 0%Q).
        unfold Qlt. cbn. reflexivity. }
      rewrite (lw0_Qabs_pos_eq _ HX). apply Qle_refl.
  - unfold lw0m_e, PiWindowCore.leiblw_nivwin.
    replace (5 * (1 # Pos.of_succ_nat (N + N + 1)))%Q
      with (5 # Pos.of_succ_nat (N + N + 1))%Q by reflexivity.
    apply (proj2 (PiWindowCore.leiblw_qmake_lt 4 5
              (Pos.of_succ_nat (4 * N + 4)) (Pos.of_succ_nat (N + N + 1)))).
    rewrite !piL_pos_succ1.
    apply (Z.lt_le_trans (4 * (Z.of_nat (N + N + 1) + 1))
             (4 * (Z.of_nat (N + N + 1) + 1) + 17)
             (5 * (Z.of_nat (4 * N + 4) + 1))).
    + replace (4 * (Z.of_nat (N + N + 1) + 1) + 17)%Z
        with (Z.succ (4 * (Z.of_nat (N + N + 1) + 1)) + 16)%Z by ring.
      apply (Z.lt_le_trans _ (Z.succ (4 * (Z.of_nat (N + N + 1) + 1)))
                (Z.succ (4 * (Z.of_nat (N + N + 1) + 1)) + 16)).
      * apply Z.lt_succ_diag_r.
      * replace (Z.succ (4 * (Z.of_nat (N + N + 1) + 1)))%Z
          with ((4 * (Z.of_nat (N + N + 1) + 1)) + 1)%Z by ring.
        apply Zplus_le_compat;
          [ apply Z.le_succ_diag_r | vm_compute; discriminate ].
    + assert (Hz0 : (0 <= 12 * Z.of_nat N)%Z).
      { apply Z.mul_nonneg_nonneg.
        - vm_compute. discriminate.
        - apply Nat2Z.is_nonneg. }
      assert (Hz2N : Z.of_nat (N + N + 1) = (2 * Z.of_nat N + 1)%Z).
      { rewrite !Nat2Z.inj_add. replace (Z.of_nat 1)%Z with 1%Z by reflexivity. ring. }
      assert (Hz4N : Z.of_nat (4 * N + 4) = (4 * Z.of_nat N + 4)%Z).
      { rewrite Nat2Z.inj_add. rewrite Nat2Z.inj_mul.
        replace (Z.of_nat 4)%Z with 4%Z by reflexivity. ring. }
      replace (4 * (Z.of_nat (N + N + 1) + 1) + 17)%Z
        with (8 * Z.of_nat N + 25)%Z by (rewrite Hz2N; ring).
      replace (5 * (Z.of_nat (4 * N + 4) + 1))%Z
        with (20 * Z.of_nat N + 25)%Z by (rewrite Hz4N; ring).
      apply (Z.le_trans (8 * Z.of_nat N + 25)
               (8 * Z.of_nat N + 25 + 12 * Z.of_nat N)
               (20 * Z.of_nat N + 25)).
      * apply (Z.le_trans (8 * Z.of_nat N + 25)
               ((8 * Z.of_nat N + 25) + 0)%Z
               ((8 * Z.of_nat N + 25) + 12 * Z.of_nat N)%Z);
        [ rewrite Z.add_0_r; apply Z.le_refl
        | apply (Z.add_le_mono (8 * Z.of_nat N + 25) (8 * Z.of_nat N + 25)
                  0 (12 * Z.of_nat N));
          [ apply Z.le_refl | exact Hz0 ] ].
      * replace (8 * Z.of_nat N + 25 + 12 * Z.of_nat N)%Z
          with (20 * Z.of_nat N + 25)%Z by ring.
        apply Z.le_refl.
Qed.

Lemma leibsep_q_kernel_guarded :
  forall (q : Q) (N : nat) (c0 : Q),
    (1 <= N)%nat ->
    QltT (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - q)%Q)) ->
    sigT (fun M : nat => forall m : nat, NatLe M m ->
      QltT (2 * c0)%Q (Qabs ((lw0m_xL m - q)%Q))).
Proof.
  intros q N c0 HN1 Hguard.
  exists N. intros m Hm.
  apply Qlt_to_QltT.
  assert (Htail : Qlt (Qabs ((lw0m_xL m - lw0m_xL N)%Q)) (lw0m_e N)).
  { exact (lw0m_tail_bounded_pi N m HN1 Hm). }
  assert (Hgr : Qlt (lw0m_e N + 2 * c0) (Qabs ((lw0m_xL N - q)%Q)))
    by (apply QltT_to_Qlt; exact Hguard).
  assert (Htri0 : Qle (Qabs (((lw0m_xL m - q) + (lw0m_xL N - lw0m_xL m))%Q))
                      (Qabs ((lw0m_xL m - q)%Q)
                       + Qabs ((lw0m_xL N - lw0m_xL m)%Q)))
    by apply Qabs_triangle.
  assert (HabsEq : Qabs (((lw0m_xL m - q) + (lw0m_xL N - lw0m_xL m))%Q)
                   == Qabs ((lw0m_xL N - q)%Q))
    by (apply Qabs_wd; ring).
  rewrite HabsEq in Htri0.
  rewrite (Qabs_Qminus (lw0m_xL N) (lw0m_xL m)) in Htri0.
  pose proof (Qlt_le_trans _ _ _ Hgr Htri0) as H1.
  pose proof (proj2 (Qplus_lt_r (Qabs ((lw0m_xL m - lw0m_xL N)%Q))
                      (lw0m_e N) (Qabs ((lw0m_xL m - q)%Q))) Htail) as H2.
  pose proof (leibsep_qlt_minus _ _ (Qlt_trans _ _ _ H1 H2)) as Hp.
  assert (E : ((Qabs ((lw0m_xL m - q)%Q)
                + lw0m_e N)
               - (lw0m_e N + 2 * c0))%Q
              == (Qabs ((lw0m_xL m - q)%Q) - 2 * c0)%Q) by ring.
  rewrite E in Hp.
  exact (leibsep_qlt_of_minus _ _ Hp).
Qed.

Lemma leibsep_gate_open_false : forall (q : Q) (N : nat) (c0 : Q),
  leibsep_gate_open q N c0 = false ->
  QleT' (Qabs ((lw0m_xL N - q)%Q)) (lw0m_e N + 2 * c0)%Q.
Proof.
  intros q N c0 H. unfold leibsep_gate_open in H.
  destruct (lw0m_e N + 2 * c0 ?= Qabs ((lw0m_xL N - q)%Q))%Q eqn:Hcmp.
  - (* Eq: [e+2c0 == |x|] implies [|x| <= e+2c0] *)
    apply Qle_to_QleT'.
    rewrite <- (proj2 (Qeq_alt (lw0m_e N + 2 * c0)%Q
                         (Qabs ((lw0m_xL N - q)%Q))) Hcmp).
    apply Qle_refl.
  - (* Lt: contradiction with the gate-open arm *)
    discriminate H.
  - (* Gt: [|x| < e+2c0] implies [<=] *)
    apply Qle_to_QleT'.
    apply Qlt_le_weak.
    exact (proj2 (Qgt_alt (lw0m_e N + 2 * c0)%Q
                    (Qabs ((lw0m_xL N - q)%Q))) Hcmp).
Qed.
(* ---------- The closed band (statements carried verbatim from the
   source; proof streamlined and done anew) ---------- *)

Lemma leibsep_closedband_of_gate_false :
  forall (q : Q) (N : nat) (c0 s eps : Q),
    (1 <= N)%nat ->
    leibsep_gate_open q N c0 = false ->
    QltT 0 s -> QltT 0 eps ->
    sigT (fun N2 : nat => forall m : nat, NatLe N2 m ->
      QleT' (Qabs ((lw0m_xL m - q)%Q))
            ((lw0m_e N + 2 * c0 + s + lw0m_e N + eps)%Q)).
Proof.
  intros q N c0 s eps HN1 Hgate Hs Heps.
  exists N. intros m Hm.
  apply Qle_to_QleT'.
  pose proof (leibsep_gate_open_false q N c0 Hgate) as Hgf.
  pose proof (QleT'_to_Qle _ _ Hgf) as Hgfq.
  assert (Htail : Qle (Qabs ((lw0m_xL m - lw0m_xL N)%Q)) (lw0m_e N))
    by exact (Qlt_le_weak _ _ (lw0m_tail_bounded_pi N m HN1 Hm)).
  assert (Htri : Qle (Qabs ((lw0m_xL m - q)%Q))
                      (Qabs ((lw0m_xL m - lw0m_xL N)%Q)
                       + Qabs ((lw0m_xL N - q)%Q))).
  { assert (Htri0 : Qle (Qabs (((lw0m_xL m - lw0m_xL N) + (lw0m_xL N - q))%Q))
                        (Qabs ((lw0m_xL m - lw0m_xL N)%Q)
                         + Qabs ((lw0m_xL N - q)%Q)))
      by apply Qabs_triangle.
    assert (HabsEq : Qabs (((lw0m_xL m - lw0m_xL N) + (lw0m_xL N - q))%Q)
                     == Qabs ((lw0m_xL m - q)%Q))
      by (apply Qabs_wd; ring).
    rewrite HabsEq in Htri0. exact Htri0. }
  assert (Hs0 : Qle 0 (s + eps)%Q).
  { apply (Qle_trans 0 s (s + eps)).
    - apply (Qlt_le_weak 0). apply QltT_to_Qlt. exact Hs.
    - apply (Qle_trans s (s + 0) (s + eps)).
      + rewrite Qplus_0_r. apply Qle_refl.
      + apply (proj2 (Qplus_le_r 0 eps s)).
        apply (Qlt_le_weak 0). apply QltT_to_Qlt. exact Heps. }
  apply (Qle_trans _ _ _ Htri).
  apply (Qle_trans _ (lw0m_e N + (lw0m_e N + 2 * c0)%Q)%Q).
  - apply Qplus_le_compat.
    + exact Htail.
    + exact Hgfq.
  - assert (Hre : ((lw0m_e N + 2 * c0 + s + lw0m_e N + eps)%Q)
                  == ((lw0m_e N + (lw0m_e N + 2 * c0)) + (s + eps))%Q) by ring.
    rewrite Hre.
    apply (Qle_trans _ ((lw0m_e N + (lw0m_e N + 2 * c0)) + 0)%Q).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (proj2 (Qplus_le_r 0 (s + eps) (lw0m_e N + (lw0m_e N + 2 * c0))%Q)).
      exact Hs0.
Qed.
(* Restated: the proof is done anew via the [gate_open_false] +
   [lw0m_tail_bounded_pi] tail-control triangle chain, collapsed by
   [Qabs_triangle]. *)

(* ---------- The two shore pieces, restated and reproved (proof
   bodies pasted byte for byte with zero changes from the source)
   ---------- *)

(* The G brick, restated and reproved (source [L3558]; the premise
   order is pinned to the carrier call shape
   [q eps0 N0 Nv Heps0 HN0 HNv Egate] -- the consumption shape of the
   source [L3984-L3986])                                        *)
(* ============================================================ *)
Lemma leibsep_shore_q_le_ten_thirds :
  forall (q eps0 : Q) (N0 Nv : nat),
    QltT 0 eps0 ->
    (forall n : nat, NatLe N0 n ->
       QltT eps0 ((10 / 3)%Q - lw0m_xL n)%Q) ->
    (forall n : nat, (Nv <= n)%nat -> QltT (lw0m_e n) (eps0 * (1 # 4))%Q) ->
    leibsep_gate_open q (Nat.max Nv 1) (eps0 * (1 # 8))%Q = false ->
    QleT' q (10 / 3)%Q.
Proof.
  intros q eps0 N0 Nv Hpos Hgap Hvan Hgate.
  assert (HNw1 : (1 <= Nat.max Nv 1)%nat) by apply Nat.le_max_r.
  assert (Hpos8 : QltT 0 (eps0 * (1 # 8))%Q).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps0 (1 # 8)%Q).
    - apply QltT_to_Qlt. exact Hpos.
    - compute. reflexivity. }
  destruct (leibsep_closedband_of_gate_false q (Nat.max Nv 1)
             (eps0 * (1 # 8))%Q (eps0 * (1 # 8))%Q (eps0 * (1 # 8))%Q
             HNw1 Hgate Hpos8 Hpos8) as [N2 HN2].
  pose proof (Hvan (Nat.max Nv 1) (Nat.le_max_l Nv 1)) as HvNw.
  pose proof (leibsep_shore_W_le (lw0m_e (Nat.max Nv 1)) eps0 HvNw) as HW.
  assert (Hm2 : (N2 <= Nat.max N2 (Nat.max N0 1))%nat) by apply Nat.le_max_l.
  assert (Hm0 : (N0 <= Nat.max N2 (Nat.max N0 1))%nat).
  { apply (Nat.le_trans N0 (Nat.max N0 1) (Nat.max N2 (Nat.max N0 1))).
    - apply Nat.le_max_l.
    - apply Nat.le_max_r. }
  pose proof (HN2 (Nat.max N2 (Nat.max N0 1))
              (NatLe_lift N2 (Nat.max N2 (Nat.max N0 1)) Hm2)) as Hband.
  pose proof (Hgap (Nat.max N2 (Nat.max N0 1))
              (NatLe_lift N0 (Nat.max N2 (Nat.max N0 1)) Hm0)) as Hgapm.
  pose proof (leibsep_shore_gap_upper eps0 (10 / 3)%Q
              (lw0m_xL (Nat.max N2 (Nat.max N0 1))) Hgapm) as Hpi.
  exact (leibsep_shore_upper q _ eps0 (Nat.max N2 (Nat.max N0 1)) Hband Hpi HW).
Qed.
(* ============================================================ *)
(* The H brick, restated and reproved (source [L3591]; about 60 atom  *)
(* renamings, the destruct anchor swapped to [piL_three_supply], and  *)
(* the linear-solver slots replaced by direct [Nat] chains)           *)
(* ============================================================ *)
Lemma leibsep_shore_q_pos :
  forall (q eps0 : Q) (N0 Nv : nat),
    QltT 0 eps0 ->
    (forall n : nat, NatLe N0 n ->
       QltT eps0 ((10 / 3)%Q - lw0m_xL n)%Q) ->
    (forall n : nat, (Nv <= n)%nat -> QltT (lw0m_e n) (eps0 * (1 # 4))%Q) ->
    leibsep_gate_open q (Nat.max Nv 1) (eps0 * (1 # 8))%Q = false ->
    QltT 0 q.
Proof.
  intros q eps0 N0 Nv Hpos Hgap Hvan Hgate.
  destruct piL_three_supply as [e3 [He3p [N3 HN3]]].
  assert (HNw1 : (1 <= Nat.max Nv 1)%nat) by apply Nat.le_max_r.
  assert (Hpos8 : QltT 0 (eps0 * (1 # 8))%Q).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps0 (1 # 8)%Q).
    - apply QltT_to_Qlt. exact Hpos.
    - compute. reflexivity. }
  destruct (leibsep_closedband_of_gate_false q (Nat.max Nv 1)
             (eps0 * (1 # 8))%Q (eps0 * (1 # 8))%Q (eps0 * (1 # 8))%Q
             HNw1 Hgate Hpos8 Hpos8) as [N2 HN2].
  pose proof (Hvan (Nat.max Nv 1) (Nat.le_max_l Nv 1)) as HvNw.
  pose proof (leibsep_shore_W_le (lw0m_e (Nat.max Nv 1)) eps0 HvNw) as HW.
  assert (Hm2 : (N2 <= Nat.max N2 (Nat.max (Nat.max N0 N3) 1))%nat)
    by apply Nat.le_max_l.
  assert (Hm0 : (N0 <= Nat.max N2 (Nat.max (Nat.max N0 N3) 1))%nat).
  { apply (Nat.le_trans N0 (Nat.max N0 N3)
             (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))).
    - apply Nat.le_max_l.
    - apply (Nat.le_trans (Nat.max N0 N3) (Nat.max (Nat.max N0 N3) 1)
               (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))).
      + apply Nat.le_max_l.
      + apply Nat.le_max_r. }
  assert (Hm3 : (N3 <= Nat.max N2 (Nat.max (Nat.max N0 N3) 1))%nat).
  { apply (Nat.le_trans N3 (Nat.max N0 N3)
             (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))).
    - apply Nat.le_max_r.
    - apply (Nat.le_trans (Nat.max N0 N3) (Nat.max (Nat.max N0 N3) 1)
               (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))).
      + apply Nat.le_max_l.
      + apply Nat.le_max_r. }
  pose proof (HN2 (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
              (NatLe_lift N2 (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) Hm2)) as Hband.
  pose proof (Hgap (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
              (NatLe_lift N0 (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) Hm0)) as Hgapm.
  pose proof (HN3 (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
              (NatLe_lift N3 (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) Hm3)) as Hgt.
  pose proof (QltT_to_Qlt _ _ Hgapm) as Hgapq.
  pose proof (QltT_to_Qlt _ _ Hgt) as Hgtq.
  assert (Hgt3 : Qlt 3%Q (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q).
  { assert (Hgt2 : Qlt (3 + e3)%Q
                 (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q).
    { apply (leibsep_qlt_wd2 (e3 + 3)%Q
               ((lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) - 3%Q)
                + 3%Q)%Q
               (3 + e3)%Q
               (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q).
      - ring.
      - ring.
      - exact (proj2 (Qplus_lt_l e3 _ 3%Q) Hgtq). }
    apply (Qlt_trans 3%Q (3 + e3)%Q _).
    - apply (leibsep_qlt_wd2 (0 + 3)%Q (e3 + 3)%Q 3%Q (3 + e3)%Q).
      + ring.
      + ring.
      + exact (proj2 (Qplus_lt_l 0%Q e3 3%Q) (QltT_to_Qlt _ _ He3p)).
    - exact Hgt2. }
  assert (Hanti : Qlt ((10 / 3)%Q
                  - lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q
                  ((10 / 3)%Q - 3%Q)%Q).
  { pose proof (Qopp_lt_compat 3%Q
        (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))) Hgt3) as Hopp.
    apply (leibsep_qlt_wd2 (Qopp (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))
                            + (10 / 3)%Q)%Q
               (Qopp 3%Q + (10 / 3)%Q)%Q
               ((10 / 3)%Q
                - lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q
               ((10 / 3)%Q - 3%Q)%Q).
    - ring.
    - ring.
    - exact (proj2 (Qplus_lt_l _ _ (10 / 3)%Q) Hopp). }
  assert (Hep : Qlt eps0 ((10 / 3)%Q - 3%Q)%Q)
    by exact (Qlt_trans eps0 _ _ Hgapq Hanti).
  assert (Hnum : Qlt ((10 / 3)%Q - 3%Q)%Q 3%Q).
  { apply (leibsep_qlt_wd2 (1 # 3)%Q 3%Q ((10 / 3)%Q - 3%Q)%Q 3%Q).
    - field.
    - apply Qeq_refl.
    - compute. reflexivity. }
  assert (Hep3 : Qlt eps0 3%Q) by exact (Qlt_trans eps0 _ _ Hep Hnum).
  (* band lower side: 3 - eps0 <= xL M - W <= q *)
  assert (Hbandq : Qle (Qabs ((lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) - q)%Q))
                       (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                        + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8)))%Q)
    by exact (QleT'_to_Qle _ _ Hband).
  assert (HWq : Qle (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                     + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8)))%Q eps0)
    by exact (QleT'_to_Qle _ _ HW).
  assert (T2abs : Qabs ((q - lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q)
                  == Qabs ((lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) - q)%Q)).
  { assert (Hneg : (q - lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q
                   == (-(lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) - q))%Q) by ring.
    rewrite Hneg. apply Qabs_opp. }
  assert (Hlow1 : QleT' (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                         + Qopp (Qabs ((lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) - q)%Q)))%Q q).
  { assert (E1 : (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                  + Qopp (Qabs ((lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) - q)%Q)))%Q
                 == (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                  + Qopp (Qabs ((q - lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q)))%Q).
    { rewrite T2abs. reflexivity. }
    assert (E2 : (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                  + (q - lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q)%Q
                 == q%Q) by ring.
    apply (qleT'_trans _ (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
            + Qopp (Qabs ((q - lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q)))%Q).
    - apply qeq_leT'. exact E1.
    - apply (qleT'_trans _ (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
              + (q - lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q)%Q).
      + apply qleT'_plus_compat.
        * apply qleT'_refl.
        * apply leibsep_abs_ge_opp.
      + apply qeq_leT'. exact E2. }
  assert (S4 : QleT' (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                    + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                     + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q
                (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                 + Qopp (Qabs ((lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) - q)%Q)))%Q).
  { apply qleT'_plus_compat.
    - apply qleT'_refl.
    - apply lw0_opp_le_swap. exact Hband. }
  pose proof (QleT'_to_Qle _ _ S4) as S4q.
  pose proof (QleT'_to_Qle _ _ Hlow1) as Hlow1q.
  assert (S1 : Qle (3%Q + Qopp eps0)%Q
                (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                 + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                  + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q).
  { apply (Qplus_le_compat 3%Q
             (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q).
    - apply Qlt_le_weak. exact Hgt3.
    - apply (QleT'_to_Qle _ _ (lw0_opp_le_swap _ _ HW)). }
  assert (S2 : Qle (3%Q - eps0)%Q (3%Q + Qopp eps0)%Q)
    by (apply leibsep_qeq_le; ring).
  assert (S3 : Qle (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                 + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q
                (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                 + Qopp (Qabs ((lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) - q)%Q)))%Q)
    by exact S4q.
  assert (Salt : Qle (3%Q - eps0)%Q q).
  { apply (Qle_trans _ (3%Q + Qopp eps0)%Q).
    - exact S2.
    - apply (Qle_trans _ (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
               + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q).
      + exact S1.
      + apply (Qle_trans _ (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                 + Qopp (Qabs ((lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)) - q)%Q)))%Q).
        * exact S3.
        * exact Hlow1q. }
  assert (Hpos03 : Qlt 0%Q (3%Q - eps0)%Q).
  { assert (Hlt1 : Qlt (eps0 + Qopp 3%Q)%Q (3%Q + Qopp 3%Q)%Q)
      by exact (proj2 (Qplus_lt_l eps0 3%Q (Qopp 3%Q)) Hep3).
    assert (Hlt2 : Qlt (eps0 - 3%Q)%Q 0%Q).
    { apply (leibsep_qlt_wd2 (eps0 + Qopp 3%Q)%Q (3%Q + Qopp 3%Q)%Q
               (eps0 - 3%Q)%Q 0%Q); [ring | ring | exact Hlt1]. }
    pose proof (Qopp_lt_compat (eps0 - 3%Q)%Q 0%Q Hlt2) as Hneg.
    apply (leibsep_qlt_wd2 (Qopp 0%Q)%Q (Qopp (eps0 - 3%Q)%Q) 0%Q (3%Q - eps0)%Q).
    - ring.
    - ring.
    - exact Hneg. }
  assert (Hf1 : Qlt (3%Q - eps0)%Q
                 (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                  + Qopp eps0)%Q).
  { apply (leibsep_qlt_wd2 (3%Q + Qopp eps0)%Q
             (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
              + Qopp eps0)%Q
             (3%Q - eps0)%Q
             (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
              + Qopp eps0)%Q).
    - ring.
    - apply Qeq_refl.
    - exact (proj2 (Qplus_lt_l 3%Q
                      (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))
                      (Qopp eps0)) Hgt3). }
  assert (Hf2 : Qle (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                 + Qopp eps0)%Q
                (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1))
                 + Qopp (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8)) + (eps0 * (1 # 8))
                  + lw0m_e (Nat.max Nv 1) + (eps0 * (1 # 8))))%Q).
  { apply (Qplus_le_compat (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q
             (lw0m_xL (Nat.max N2 (Nat.max (Nat.max N0 N3) 1)))%Q).
    - apply Qle_refl.
    - exact (QleT'_to_Qle _ _ (lw0_opp_le_swap _ _ HW)). }
  apply Qlt_to_QltT.
  exact (Qlt_trans 0%Q (3%Q - eps0)%Q _ Hpos03
          (Qlt_le_trans _ _ _ Hf1
             (Qle_trans _ _ _ Hf2 (Qle_trans _ _ _ S4q Hlow1q)))).
Qed.
(* ---------- The [gate_carrier] restatement introduced here (the
   slot shape of the restatement: the second premise moved to the
   pointwise side; proof body verbatim from the source
   [L3961-L4021], two spots closed by direct arithmetic chains, the
   evaluation step kept as in the source) ---------- *)

Lemma leibsep_q_kernel_gate_carrier :
  forall (q : Q) (eps0 : Q) (N0 Nv : nat) (s t : Q) (M0 : nat),
  QltT 0 eps0 ->
  (forall n : nat, NatLe N0 n ->
     QltT eps0 ((10 / 3)%Q - lw0m_xL n)%Q) ->
  (forall n : nat, (Nv <= n)%nat -> QltT (lw0m_e n) (eps0 * (1 # 4))%Q) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s) ->
  (forall m : nat, (M0 <= m)%nat ->
     QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t) ->
     QleT' (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))
                  ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat)) q) * t
          + Qabs (qpoly_eval (qpoly_deriv
                  (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))
                  ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))) q) * s
          + eps0 * (1 # 8))%Q (1 # 2)%Q ->
     QltT (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))
                  ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat)) q) * t
          + Qabs (qpoly_eval (qpoly_deriv
                  (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q
                    ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))
                  ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat))) q) * s
          + eps0 * (1 # 8))%Q
         (q_fact ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat)
        * (lw0_Wb (Zpos (Qden q) # 1)%Q q ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat) 0%nat
         - lw0_Wb (Zpos (Qden q) # 1)%Q q ((lw0_n_select (10 * lw0_pi_d0_of ((Zpos (Qden q) # 1)%Q)) 0 + 1)%nat) 1%nat))%Q ->
  sigT (fun c : Q => And (QltT 0 c)
    (sigT (fun N : nat => forall m : nat, NatLe N m ->
      QltT c (Qabs ((lw0m_xL m - q)%Q))))).
Proof.
  intros q eps0 N0 Nv s t M0 Heps0 HN0 HNv Hs Ht HP1 HP2.
  assert (HN1 : (1 <= Nat.max Nv 1)%nat) by apply Nat.le_max_r.
  assert (Hc8lt : Qlt 0 (eps0 * (1 # 8)))
    by (apply (Qmult_lt_0_compat eps0 (1 # 8));
        [ apply QltT_to_Qlt; exact Heps0 | vm_compute; reflexivity ]).
  assert (Hc8ltT : QltT 0 (eps0 * (1 # 8))%Q) by (apply Qlt_to_QltT; exact Hc8lt).
  assert (Hj01 : (1 <= 1)%nat) by apply Nat.le_refl.
  destruct (leibsep_gate_open q (Nat.max Nv 1) (eps0 * (1 # 8))%Q) eqn:Egate.
  - (* gate true: guarded kernel with witness c := 2*c0 *)
    assert (Hcpos : QltT 0 (2 * (eps0 * (1 # 8)))%Q).
    { apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat 2 (eps0 * (1 # 8)));
        [ vm_compute; reflexivity | exact Hc8lt ]. }
    assert (Hguard : QltT (lw0m_e (Nat.max Nv 1) + 2 * (eps0 * (1 # 8))%Q)
                          (Qabs ((lw0m_xL (Nat.max Nv 1) - q)%Q)))
      by (apply leibsep_gate_open_true; exact Egate).
    destruct (leibsep_q_kernel_guarded q (Nat.max Nv 1) (eps0 * (1 # 8))%Q HN1 Hguard)
      as [M HM].
    exists (2 * (eps0 * (1 # 8)))%Q. split.
    + exact Hcpos.
    + exists M. exact HM.
  - (* gate false: shore double-landing + P1/P2 slots + w0n_half + slot A/B *)
    assert (Hq103 : QleT' q (10 / 3)%Q)
      by exact (leibsep_shore_q_le_ten_thirds q eps0 N0 Nv Heps0 HN0 HNv Egate).
    assert (Hq : QltT 0 q)
      by exact (leibsep_shore_q_pos q eps0 N0 Nv Heps0 HN0 HNv Egate).
    assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
    pose (b := (Zpos (Qden q) # 1)%Q).
    pose (n0 := ((lw0_n_select (10 * lw0_pi_d0_of b) 0 + 1)%nat)).
    assert (Hbh : QltT 0 b) by apply lw0_pi_b_den_pos.
    assert (Hbabs : b == Qabs b).
    { symmetry. apply Qabs_pos. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hbh. }
    assert (Hbd0 : QleT' b (lw0_q_of_nat (lw0_pi_d0_of b))).
    { apply (qleT'_trans b (Qabs b) (lw0_q_of_nat (lw0_pi_d0_of b))).
      - apply qeq_leT'. exact Hbabs.
      - apply lw0_pi_d0_absorb. exact (qeq_ltT b (Qabs b) Hbabs Hbh). }
    assert (Hv : QltT (q_fact n0 * lw0_Wb b q n0 0)%Q (1 # 2)%Q)
      by exact (leibsep_w0n_half b q (lw0_pi_d0_of b) 0 1 Hbh Hq0 Hq103 Hbd0 Hj01).
    (* upper composite C: the endpoint caps s and t enter as premises *)
    pose (C := (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b n0) n0) q) * t
              + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b n0) n0)) q) * s
              + (eps0 * (1 # 8))%Q)%Q).
    assert (HCA : QleT' C (1 # 2)%Q)
      by exact HP1.
    assert (Hvlt : Qlt (q_fact n0 * lw0_Wb b q n0 0)%Q (1 # 2)%Q)
      by (apply QltT_to_Qlt; exact Hv).
    assert (HvC : Qlt (q_fact n0 * lw0_Wb b q n0 0 + C)%Q ((1 # 2) + C)%Q)
      by exact (proj2 (Qplus_lt_l (q_fact n0 * lw0_Wb b q n0 0) (1 # 2)%Q C) Hvlt).
    assert (HleC : Qle ((1 # 2) + C)%Q 1%Q).
    { apply QleT'_to_Qle.
      apply (qleT'_trans ((1 # 2) + C)%Q ((1 # 2) + (1 # 2))%Q 1%Q).
      - apply qleT'_plus_compat; [apply qleT'_refl | exact HCA].
      - apply qeq_leT'. ring. }
    assert (Hup : QltT (q_fact n0 * lw0_Wb b q n0 0 + C)%Q 1%Q)
      by (apply Qlt_to_QltT; exact (Qlt_le_trans _ _ _ HvC HleC)).
    assert (HCB : QltT C (q_fact n0 * (lw0_Wb b q n0 0%nat - lw0_Wb b q n0 1%nat))%Q)
      by exact HP2.
    assert (Hcontra : Id false true).
    { exact (leibsep_false_branch_contra q 0 1 s t M0
             (eps0 * (1 # 8))%Q Hq Hq103 Hc8ltT Hj01 Hs Ht HCA HCB). }
    discriminate Hcontra || inversion Hcontra.
Qed.
(* ---- Merged segment 1: PiKernelSlack_D1_identity (md5 5c0f7348) ---- *)
Lemma piL_q_pow_0 : forall x : Q, q_pow x 0 == 1.
Proof. intros x. reflexivity. Qed.

Lemma piL_q_fact_0 : q_fact 0 == 1.
Proof. reflexivity. Qed.

Lemma piL_qdiv_1_r : forall x : Q, (x / 1)%Q == x.
Proof.
  intros x. unfold Qdiv, Qeq. cbn. destruct x as [xn xd]. cbn.
  rewrite Z.mul_1_r. rewrite (Pos.mul_1_r xd). reflexivity.
Qed.

Lemma piL_sin_term_0 : forall x : Q, sin_term 0 x == x.
Proof.
  intros x. unfold sin_term.
  rewrite (piL_q_pow_0 (-1)%Q).
  rewrite (q_pow_succ x 0).
  rewrite (piL_q_pow_0 x).
  rewrite (q_fact_succ 0).
  rewrite piL_q_fact_0.
  change (Z.of_nat 1) with 1%Z.
  rewrite (Qmult_1_r x).
  rewrite (Qmult_1_r (1 # 1)%Q).
  rewrite (piL_qdiv_1_r x).
  apply Qmult_1_l.
Qed.

Lemma piL_cos_term_0 : forall x : Q, cos_term 0 x == 1.
Proof.
  intros x. unfold cos_term.
  change (2 * 0)%nat with 0%nat.
  rewrite (piL_q_pow_0 (-1)%Q).
  rewrite (piL_q_pow_0 x).
  rewrite piL_q_fact_0.
  rewrite (piL_qdiv_1_r 1%Q).
  apply Qmult_1_l.
Qed.

(* Qeq congruence in the point arguments at term level and at
   partial-sum level (the reshaping master lemma consumed by the
   composite stratification and the window-point substitution). *)
Lemma piL_sin_term_congr : forall (j : nat) (u v : Q),
  u == v -> sin_term j u == sin_term j v.
Proof.
  intros j u v Huv. unfold sin_term, Qdiv.
  rewrite (q_pow_wd u v (Datatypes.S (2 * j)) Huv).
  reflexivity.
Qed.

Lemma piL_cos_term_congr : forall (j : nat) (u v : Q),
  u == v -> cos_term j u == cos_term j v.
Proof.
  intros j u v Huv. unfold cos_term, Qdiv.
  rewrite (q_pow_wd u v (2 * j) Huv).
  reflexivity.
Qed.

Lemma piL_sin_partial_congr : forall (m : nat) (x y : Q),
  x == y -> sin_partial m x == sin_partial m y.
Proof.
  intros m x y Hxy. induction m as [| p IH].
  - exact (Qeq_trans (sin_term 0 x) x (sin_term 0 y)
             (piL_sin_term_0 x)
             (Qeq_trans x y (sin_term 0 y) Hxy
                (Qeq_sym (sin_term 0 y) y (piL_sin_term_0 y)))).
  - cbn [sin_partial]. apply Qplus_comp.
    + exact IH.
    + apply piL_sin_term_congr. exact Hxy.
Qed.

Lemma piL_cos_partial_congr : forall (m : nat) (x y : Q),
  x == y -> cos_partial m x == cos_partial m y.
Proof.
  intros m x y Hxy. induction m as [| p IH].
  - exact (Qeq_trans (cos_term 0 x) 1%Q (cos_term 0 y)
             (piL_cos_term_0 x)
             (Qeq_sym (cos_term 0 y) 1%Q (piL_cos_term_0 y))).
  - cbn [cos_partial]. apply Qplus_comp.
    + exact IH.
    + apply piL_cos_term_congr. exact Hxy.
Qed.

(* ========== Section 2. Stratification of the sin double-angle partial sums ========== *)

(* The truncation residual [dres]: the coefficient bookkeeping of the
   power series -- the difference recursion between 2*S_p*C_p and
   S_p(2x) at the order-p truncation; the step increment is the cross
   products 2*S_p*c + 2*C_p*s + 2*s*c minus the new sin term at the
   point 2x. *)
Fixpoint piL_sin_dres (m : nat) (x : Q) : Q :=
  match m with
  | 0%nat => 0
  | Datatypes.S p =>
      piL_sin_dres p x
      + 2 * sin_partial p x * cos_term (Datatypes.S p) x
      + 2 * cos_partial p x * sin_term (Datatypes.S p) x
      + 2 * sin_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
      - sin_term (Datatypes.S p) (2 * x)
  end.

Lemma piL_sin_partial_double : forall (m : nat) (x : Q),
  sin_partial m (2 * x) + piL_sin_dres m x
  == 2 * sin_partial m x * cos_partial m x.
Proof.
  induction m as [| p IH]; intros x.
  - cbn [sin_partial cos_partial piL_sin_dres].
    repeat rewrite piL_sin_term_0.
    repeat rewrite piL_cos_term_0.
    ring.
  - cbn [sin_partial cos_partial piL_sin_dres].
    assert (Hre : (sin_partial p (2 * x) + sin_term (Datatypes.S p) (2 * x))
                  + (piL_sin_dres p x
                     + 2 * sin_partial p x * cos_term (Datatypes.S p) x
                     + 2 * cos_partial p x * sin_term (Datatypes.S p) x
                     + 2 * sin_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
                     - sin_term (Datatypes.S p) (2 * x))
                  == (sin_partial p (2 * x) + piL_sin_dres p x)
                     + (2 * sin_partial p x * cos_term (Datatypes.S p) x
                        + 2 * cos_partial p x * sin_term (Datatypes.S p) x
                        + 2 * sin_term (Datatypes.S p) x * cos_term (Datatypes.S p) x))
      by ring.
    rewrite Hre, IH. ring.
Qed.

Lemma piL_sin_partial_double_at : forall (m : nat) (x : Q),
  sin_partial m (2 * x)
  == 2 * sin_partial m x * cos_partial m x - piL_sin_dres m x.
Proof.
  intros m x. rewrite <- piL_sin_partial_double. ring.
Qed.

(* ========== Section 3. Stratification of the cos double-angle partial sums ========== *)

(* The truncation residual [dcos]: the difference recursion between
   C_p(2x) and C_p^2 - S_p^2 at the order-p truncation; the step
   increment is the new cos term ct plus the bookkeeping term
   2*C_p*c - 2*S_p*s - (c^2 - s^2). *)
Fixpoint piL_cos_dres (m : nat) (x : Q) : Q :=
  match m with
  | 0%nat => x * x
  | Datatypes.S p =>
      piL_cos_dres p x
      + cos_term (Datatypes.S p) (2 * x)
      - 2 * cos_partial p x * cos_term (Datatypes.S p) x
      + 2 * sin_partial p x * sin_term (Datatypes.S p) x
      - (cos_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
         - sin_term (Datatypes.S p) x * sin_term (Datatypes.S p) x)
  end.

Lemma piL_cos_partial_double : forall (m : nat) (x : Q),
  cos_partial m (2 * x)
  == cos_partial m x * cos_partial m x
     - sin_partial m x * sin_partial m x + piL_cos_dres m x.
Proof.
  induction m as [| p IH]; intros x.
  - cbn [cos_partial sin_partial piL_cos_dres].
    repeat rewrite piL_cos_term_0.
    repeat rewrite piL_sin_term_0.
    ring.
  - cbn [cos_partial sin_partial piL_cos_dres].
    rewrite IH. ring.
Qed.

(* ========== Section 4. Stratification of the Pythagorean partial sums ========== *)

(* The truncation residual [dpit]: the difference recursion between
   S_p^2 + C_p^2 and 1 at the order-p truncation; the step increment
   is the cross terms 2*S_p*s + s^2 + 2*C_p*c + c^2.
   Seeds: the sin^2 + cos^2 = 1 vertex bookkeeping pair, stratified
   at the [Q] level. *)
Fixpoint piL_pyth_dres (m : nat) (x : Q) : Q :=
  match m with
  | 0%nat => x * x
  | Datatypes.S p =>
      piL_pyth_dres p x
      + 2 * sin_partial p x * sin_term (Datatypes.S p) x
      + sin_term (Datatypes.S p) x * sin_term (Datatypes.S p) x
      + 2 * cos_partial p x * cos_term (Datatypes.S p) x
      + cos_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
  end.

Lemma piL_pythag_partial : forall (m : nat) (x : Q),
  sin_partial m x * sin_partial m x + cos_partial m x * cos_partial m x
  == 1 + piL_pyth_dres m x.
Proof.
  induction m as [| p IH]; intros x.
  - cbn [sin_partial cos_partial piL_pyth_dres].
    rewrite (piL_sin_term_0 x).
    rewrite (piL_cos_term_0 x).
    ring.
  - cbn [sin_partial cos_partial piL_pyth_dres].
    assert (Hre : (sin_partial p x + sin_term (Datatypes.S p) x)
                  * (sin_partial p x + sin_term (Datatypes.S p) x)
                  + (cos_partial p x + cos_term (Datatypes.S p) x)
                  * (cos_partial p x + cos_term (Datatypes.S p) x)
                  == sin_partial p x * sin_partial p x
                     + cos_partial p x * cos_partial p x
                     + (2 * sin_partial p x * sin_term (Datatypes.S p) x
                        + sin_term (Datatypes.S p) x * sin_term (Datatypes.S p) x
                        + 2 * cos_partial p x * cos_term (Datatypes.S p) x
                        + cos_term (Datatypes.S p) x * cos_term (Datatypes.S p) x))
      by ring.
    rewrite Hre, IH. ring.
Qed.

(* ========== Section 5. The quadruple-angle composite stratification ========== *)

(* The composite residual: the difference between sin_partial m (4x)
   and the vertex-factorized 4*S*C*(C^2 - S^2) -- the composition of
   the double-angle residual at the point 2x plus the coefficient
   bookkeeping; a pure [Q] definition (no [Fixpoint]). *)
Definition piL_quad_dres (m : nat) (x : Q) : Q :=
  2 * (2 * sin_partial m x * cos_partial m x - piL_sin_dres m x)
      * (cos_partial m x * cos_partial m x
         - sin_partial m x * sin_partial m x + piL_cos_dres m x)
  - piL_sin_dres m (2 * x)
  - 4 * sin_partial m x * cos_partial m x
      * (cos_partial m x * cos_partial m x
         - sin_partial m x * sin_partial m x).

Lemma piL_sin_partial_quad : forall (m : nat) (x : Q),
  sin_partial m (4 * x)
  == 4 * sin_partial m x * cos_partial m x
     * (cos_partial m x * cos_partial m x - sin_partial m x * sin_partial m x)
     + piL_quad_dres m x.
Proof.
  intros m x. unfold piL_quad_dres.
  assert (H4 : (4 * x)%Q == (2 * (2 * x))%Q) by ring.
  rewrite (piL_sin_partial_congr m (4 * x) (2 * (2 * x)) H4).
  rewrite (piL_sin_partial_double_at m (2 * x)).
  rewrite (piL_sin_partial_double_at m x).
  rewrite piL_cos_partial_double.
  ring.
Qed.

(* The composite residual: the difference between cos_partial m (4x)
   and the vertex-factorized (C^2 - S^2)^2 - (2*S*C)^2. *)
Definition piL_cos_quad_dres (m : nat) (x : Q) : Q :=
  piL_cos_dres m (2 * x)
  + (cos_partial m x * cos_partial m x - sin_partial m x * sin_partial m x
     + piL_cos_dres m x)
    * (cos_partial m x * cos_partial m x - sin_partial m x * sin_partial m x
       + piL_cos_dres m x)
  - (2 * sin_partial m x * cos_partial m x - piL_sin_dres m x)
    * (2 * sin_partial m x * cos_partial m x - piL_sin_dres m x)
  - (cos_partial m x * cos_partial m x - sin_partial m x * sin_partial m x)
    * (cos_partial m x * cos_partial m x - sin_partial m x * sin_partial m x)
  + (2 * sin_partial m x * cos_partial m x)
    * (2 * sin_partial m x * cos_partial m x).

Lemma piL_cos_partial_quad : forall (m : nat) (x : Q),
  cos_partial m (4 * x)
  == (cos_partial m x * cos_partial m x - sin_partial m x * sin_partial m x)
     * (cos_partial m x * cos_partial m x - sin_partial m x * sin_partial m x)
     - (2 * sin_partial m x * cos_partial m x)
       * (2 * sin_partial m x * cos_partial m x)
     + piL_cos_quad_dres m x.
Proof.
  intros m x. unfold piL_cos_quad_dres.
  assert (H4 : (4 * x)%Q == (2 * (2 * x))%Q) by ring.
  rewrite (piL_cos_partial_congr m (4 * x) (2 * (2 * x)) H4).
  rewrite piL_cos_partial_double.
  rewrite (piL_sin_partial_double_at m x).
  rewrite piL_cos_partial_double.
  ring.
Qed.

(* The vertex factor form: C^2 - S^2 = (C - S)*(C + S) -- the
   vanishing factor made explicit (consumed for the smallness side
   inside the window). *)
Lemma piL_quad_vertex_factor : forall a b : Q,
  4 * a * b * (b * b - a * a) == 4 * a * b * (b + a) * (b - a).
Proof.
  intros a b. ring.
Qed.

(* ========== Section 6. Substitution at the pi_L window points (lw0m_xL) ========== *)

(* Substitution at the window points xL m = 4*lp_odd m, the Leibniz
   partial sums of 4*arctan 1: the instances of the Section 5 master
   identities at the sampling points -- the identity donors of the
   two-index synthesis. *)
Lemma piL_sin_quad_xL : forall (k m : nat),
  sin_partial k (lw0m_xL m)
  == 4 * sin_partial k (lp_odd m) * cos_partial k (lp_odd m)
     * (cos_partial k (lp_odd m) * cos_partial k (lp_odd m)
        - sin_partial k (lp_odd m) * sin_partial k (lp_odd m))
     + piL_quad_dres k (lp_odd m).
Proof.
  intros k m. unfold lw0m_xL.
  assert (H4 : lp_four * lp_odd m == (4 * lp_odd m)%Q)
    by (unfold lp_four; ring).
  rewrite (piL_sin_partial_congr k (lp_four * lp_odd m) (4 * lp_odd m) H4).
  apply piL_sin_partial_quad.
Qed.

Lemma piL_cos_quad_xL : forall (k m : nat),
  cos_partial k (lw0m_xL m)
  == (cos_partial k (lp_odd m) * cos_partial k (lp_odd m)
      - sin_partial k (lp_odd m) * sin_partial k (lp_odd m))
     * (cos_partial k (lp_odd m) * cos_partial k (lp_odd m)
        - sin_partial k (lp_odd m) * sin_partial k (lp_odd m))
     - (2 * sin_partial k (lp_odd m) * cos_partial k (lp_odd m))
       * (2 * sin_partial k (lp_odd m) * cos_partial k (lp_odd m))
     + piL_cos_quad_dres k (lp_odd m).
Proof.
  intros k m. unfold lw0m_xL.
  assert (H4 : lp_four * lp_odd m == (4 * lp_odd m)%Q)
    by (unfold lp_four; ring).
  rewrite (piL_cos_partial_congr k (lp_four * lp_odd m) (4 * lp_odd m) H4).
  apply piL_cos_partial_quad.
Qed.
(* ---- Merged segment 2: PiKernelSlack_D2_remainder (md5 4812ad70) ---- *)
Lemma piL_qabs_zero : Qabs 0 == 0.
Proof. unfold Qabs. simpl. reflexivity. Qed.

Lemma piL_qabs_two : Qabs (2 # 1)%Q == (2 # 1)%Q.
Proof. unfold Qabs. simpl. reflexivity. Qed.

Lemma piL_qabs_four : Qabs (4 # 1)%Q == (4 # 1)%Q.
Proof. unfold Qabs. simpl. reflexivity. Qed.

(* Concrete constants are nonnegative: 0 <= 2 and 0 <= 4 (in stdlib
   9.1 [Qle] is defined directly at the [Z] level, and the closure
   goes through the computation [Z.leb_le]). *)
Lemma piL_qle_0_two : QleT' 0 (2 # 1)%Q.
Proof. apply Qle_to_QleT'. unfold Qle. exact (proj1 (Z.leb_le 0 2) eq_refl). Qed.

Lemma piL_qle_0_four : QleT' 0 (4 # 1)%Q.
Proof. apply Qle_to_QleT'. unfold Qle. exact (proj1 (Z.leb_le 0 4) eq_refl). Qed.

(* Left multiplication preserves the order (the transposed form of
   [Qmult_le_compat_r]: z*x <= z*y; a pure term-level chain with no
   goal rewriting). *)
Lemma piL_mult_le_l : forall x y z : Q,
  Qle x y -> Qle 0 z -> Qle (z * x) (z * y).
Proof.
  intros x y z Hxy Hz.
  pose proof (Qmult_le_compat_r x y z Hxy Hz) as H.
  pose proof (qeq_le (z * x) (x * z) (Qmult_comm z x)) as H1.
  pose proof (qeq_le (y * z) (z * y) (Qmult_comm y z)) as H2.
  exact (Qle_trans (z * x) (x * z) (z * y)
          H1 (Qle_trans (x * z) (y * z) (z * y) H H2)).
Qed.

(* Division by a positive denominator preserves absolute values:
   0 < d implies |a/d| == |a|/d. *)
Lemma piL_abs_div_pos_den : forall a d : Q,
  Qlt 0 d -> Qabs (a / d) == Qabs a / d.
Proof.
  intros a d Hd. unfold Qdiv.
  rewrite (Qabs_Qmult a (Qinv d)).
  rewrite (Qabs_pos (Qinv d)
            (Qlt_le_weak 0 (/ d) (Qinv_lt_0_compat d Hd))).
  reflexivity.
Qed.

(* Bridge for reshaping one side at the equality type ([Qeq]
   rewriting does not pierce [QleT'] or [Id] goals, so the step
   routes through the bridge lemma): reshape the left-hand side. *)
Lemma piL_leT'_eq_intro_l : forall a a' m : Q,
  a == a' -> QleT' a' m -> QleT' a m.
Proof.
  intros a a' m Haa H. apply Qle_to_QleT'.
  apply (Qle_trans a a' m).
  - apply qeq_le. exact Haa.
  - exact (QleT'_to_Qle _ _ H).
Qed.

(* Bridge for reshaping one side at the equality type: reshape the
   right-hand side. *)
Lemma piL_leT'_eq_intro_r : forall b b' m : Q,
  b == b' -> QleT' m b -> QleT' m b'.
Proof.
  intros b b' m Hbb H. apply Qle_to_QleT'.
  apply (Qle_trans m b b').
  - exact (QleT'_to_Qle _ _ H).
  - apply qeq_le. exact Hbb.
Qed.

(* Absolute-value product bound (two factors). *)
Lemma piL_abs_mult_le : forall a b u v : Q,
  QleT' (Qabs a) u -> QleT' (Qabs b) v ->
  QleT' (Qabs (a * b)) (u * v).
Proof.
  intros a b u v Ha Hb.
  apply Qle_to_QleT'.
  rewrite (Qabs_Qmult a b).
  apply Qmult_le_compat_nonneg.
  - split; [apply Qabs_nonneg | exact (QleT'_to_Qle _ _ Ha)].
  - split; [apply Qabs_nonneg | exact (QleT'_to_Qle _ _ Hb)].
Qed.

(* Absolute-value product bound (coefficient 2, two factors: |2ab| <= 2uv). *)
Lemma piL_abs_coeff2_2 : forall a b u v : Q,
  QleT' (Qabs a) u -> QleT' (Qabs b) v ->
  QleT' (Qabs (2 * a * b)) (2 * u * v).
Proof.
  intros a b u v Ha Hb.
  apply Qle_to_QleT'.
  rewrite (Qabs_Qmult (2 * a) b).
  rewrite (Qabs_Qmult (2 # 1)%Q a).
  rewrite piL_qabs_two.
  apply Qmult_le_compat_nonneg.
  - split.
    + apply Qmult_le_0_compat.
      * exact (QleT'_to_Qle _ _ piL_qle_0_two).
      * apply Qabs_nonneg.
    + apply piL_mult_le_l.
      * exact (QleT'_to_Qle _ _ Ha).
      * exact (QleT'_to_Qle _ _ piL_qle_0_two).
  - split; [apply Qabs_nonneg | exact (QleT'_to_Qle _ _ Hb)].
Qed.

(* Absolute-value product bound (coefficient 4, three factors: |4abc| <= 4uvw). *)
Lemma piL_abs_coeff4_3 : forall a b c u v w : Q,
  QleT' (Qabs a) u -> QleT' (Qabs b) v -> QleT' (Qabs c) w ->
  QleT' (Qabs (4 * a * b * c)) (4 * u * v * w).
Proof.
  intros a b c u v w Ha Hb Hc.
  apply Qle_to_QleT'.
  rewrite (Qabs_Qmult ((4 * a) * b) c).
  rewrite (Qabs_Qmult (4 * a) b).
  rewrite (Qabs_Qmult (4 # 1)%Q a).
  rewrite piL_qabs_four.
  apply Qmult_le_compat_nonneg.
  - split.
    + apply Qmult_le_0_compat.
      * apply Qmult_le_0_compat.
        -- exact (QleT'_to_Qle _ _ piL_qle_0_four).
        -- apply Qabs_nonneg.
      * apply Qabs_nonneg.
    + apply Qmult_le_compat_nonneg.
      * split.
        -- apply Qmult_le_0_compat.
           ++ exact (QleT'_to_Qle _ _ piL_qle_0_four).
           ++ apply Qabs_nonneg.
        -- apply piL_mult_le_l.
           ++ exact (QleT'_to_Qle _ _ Ha).
           ++ exact (QleT'_to_Qle _ _ piL_qle_0_four).
      * split; [apply Qabs_nonneg | exact (QleT'_to_Qle _ _ Hb)].
  - split; [apply Qabs_nonneg | exact (QleT'_to_Qle _ _ Hc)].
Qed.

(* Absolute-value sum bound (two-factor assembly). *)
Lemma piL_abs2_plus_le : forall a1 a2 m1 m2 : Q,
  QleT' (Qabs a1) m1 -> QleT' (Qabs a2) m2 ->
  QleT' (Qabs (a1 + a2)) (m1 + m2).
Proof.
  intros a1 a2 m1 m2 H1 H2.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (Qabs a1 + Qabs a2)).
  - apply Qabs_triangle.
  - apply Qplus_le_compat;
      [exact (QleT'_to_Qle _ _ H1) | exact (QleT'_to_Qle _ _ H2)].
Qed.

(* Absolute-value sum bound (three-factor assembly; right-associated form). *)
Lemma piL_abs3_plus_le : forall a1 a2 a3 m1 m2 m3 : Q,
  QleT' (Qabs a1) m1 -> QleT' (Qabs a2) m2 -> QleT' (Qabs a3) m3 ->
  QleT' (Qabs (a1 + (a2 + a3))) (m1 + (m2 + m3)).
Proof.
  intros a1 a2 a3 m1 m2 m3 H1 H2 H3.
  apply piL_abs2_plus_le.
  - exact H1.
  - apply piL_abs2_plus_le; assumption.
Qed.

(* Absolute-value sum bound (four-factor assembly; right-associated form). *)
Lemma piL_abs4_plus_le : forall a1 a2 a3 a4 m1 m2 m3 m4 : Q,
  QleT' (Qabs a1) m1 -> QleT' (Qabs a2) m2 ->
  QleT' (Qabs a3) m3 -> QleT' (Qabs a4) m4 ->
  QleT' (Qabs (a1 + (a2 + (a3 + a4)))) (m1 + (m2 + (m3 + m4))).
Proof.
  intros a1 a2 a3 a4 m1 m2 m3 m4 H1 H2 H3 H4.
  apply piL_abs2_plus_le.
  - exact H1.
  - apply piL_abs2_plus_le.
    + exact H2.
    + apply piL_abs2_plus_le; [exact H3 | exact H4].
Qed.

(* Sign flip under absolute value: |a| <= m implies |-a| <= m. *)
Lemma piL_abs_opp_le : forall a m : Q,
  QleT' (Qabs a) m -> QleT' (Qabs (- a)) m.
Proof.
  intros a m H.
  apply (piL_leT'_eq_intro_l _ _ _ (Qabs_opp a)).
  exact H.
Qed.

(* Absolute value at the doubled point argument: |x| <= B implies
   |2x| <= 2B (the identity |2x| = |2|*|x| enters through the product
   bound). *)
Lemma piL_abs2_le : forall x B : Q,
  QleT' (Qabs x) B -> QleT' (Qabs (2 * x)) (2 * B).
Proof.
  intros x B Hx.
  apply (piL_abs_mult_le (2 # 1)%Q x (2 # 1)%Q B).
  - apply qeq_leT'. apply piL_qabs_two.
  - exact Hx.
Qed.

(* Doubling preserves strict positivity: 0 < B implies 0 < 2B (the
   premise piece of the doubled evaluation point instance). *)
Lemma piL_qltT_0_double : forall B : Q,
  QltT 0 B -> QltT 0 (2 * B).
Proof.
  intros B HB. apply Qlt_to_QltT.
  apply (leibsep_qlt_wd2 (0 + 0)%Q (B + B)%Q 0 (2 * B)%Q).
  - ring.
  - ring.
  - exact (Qplus_lt_compat 0 B 0 B (QltT_to_Qlt _ _ HB) (QltT_to_Qlt _ _ HB)).
Qed.

(* ========== Section 2. Term-level and partial-sum-level absolute value bounds (|x| <= B) ========== *)

(* The sin term absolute value bound: |sin_term j x| <= B^(2j+1)/(2j+1)!. *)
Lemma piL_sin_term_abs_bound : forall (j : nat) (x B : Q),
  QleT' (Qabs x) B ->
  QleT' (Qabs (sin_term j x))
        (q_pow B (Datatypes.S (2 * j))%nat / q_fact (Datatypes.S (2 * j))%nat).
Proof.
  intros j x B Hx.
  assert (Heq : Qabs (sin_term j x)
                == q_pow (Qabs x) (Datatypes.S (2 * j))%nat
                   / q_fact (Datatypes.S (2 * j))%nat).
  { unfold sin_term.
    rewrite (Qabs_Qmult (q_pow (-1) j)
              (q_pow x (Datatypes.S (2 * j))%nat
               / q_fact (Datatypes.S (2 * j))%nat)).
    rewrite (sc_abs_sign j).
    rewrite (piL_abs_div_pos_den (q_pow x (Datatypes.S (2 * j))%nat)
              (q_fact (Datatypes.S (2 * j))%nat)
              (q_fact_pos (Datatypes.S (2 * j))%nat)).
    rewrite (q_pow_abs x (Datatypes.S (2 * j))%nat).
    ring. }
  apply (piL_leT'_eq_intro_l _ _ _ Heq).
  apply Qle_to_QleT'.
  apply Qle_div_same_denom.
  - apply q_fact_pos.
  - apply q_pow_mono.
    + apply Qabs_nonneg.
    + exact (QleT'_to_Qle _ _ Hx).
Qed.

(* The cos term absolute value bound: |cos_term j x| <= B^(2j)/(2j)!. *)
Lemma piL_cos_term_abs_bound : forall (j : nat) (x B : Q),
  QleT' (Qabs x) B ->
  QleT' (Qabs (cos_term j x))
        (q_pow B (2 * j)%nat / q_fact (2 * j)%nat).
Proof.
  intros j x B Hx.
  assert (Heq : Qabs (cos_term j x)
                == q_pow (Qabs x) (2 * j)%nat / q_fact (2 * j)%nat).
  { unfold cos_term.
    rewrite (Qabs_Qmult (q_pow (-1) j)
              (q_pow x (2 * j)%nat / q_fact (2 * j)%nat)).
    rewrite (sc_abs_sign j).
    rewrite (piL_abs_div_pos_den (q_pow x (2 * j)%nat)
              (q_fact (2 * j)%nat) (q_fact_pos (2 * j)%nat)).
    rewrite (q_pow_abs x (2 * j)%nat).
    ring. }
  apply (piL_leT'_eq_intro_l _ _ _ Heq).
  apply Qle_to_QleT'.
  apply Qle_div_same_denom.
  - apply q_fact_pos.
  - apply q_pow_mono.
    + apply Qabs_nonneg.
    + exact (QleT'_to_Qle _ _ Hx).
Qed.

(* The sin partial-sum absolute value bound: |sin_partial p x| <=
   sum_{j<=p} B^(2j+1)/(2j+1)! = [leibsep_abssum_cos B (S p)]. *)
Lemma piL_sin_partial_abs_bound : forall (p : nat) (x B : Q),
  QleT' (Qabs x) B ->
  QleT' (Qabs (sin_partial p x))
        (leibsep_abssum_cos B (Datatypes.S p)).
Proof.
  intros p x B Hx. induction p as [| n IH].
  - cbn [sin_partial leibsep_abssum_cos].
    apply (qleT'_trans _
      (q_pow B (Datatypes.S (2 * 0))%nat / q_fact (Datatypes.S (2 * 0))%nat)).
    + exact (piL_sin_term_abs_bound 0 x B Hx).
    + apply qeq_leT'. ring.
  - assert (Hstep : leibsep_abssum_cos B (Datatypes.S n)
                    + q_pow B (Datatypes.S (2 * Datatypes.S n))%nat
                      / q_fact (Datatypes.S (2 * Datatypes.S n))%nat
                    == leibsep_abssum_cos B (Datatypes.S (Datatypes.S n)))
      by (cbn [leibsep_abssum_cos]; ring).
    cbn [sin_partial].
    apply (piL_leT'_eq_intro_r _ _ _ Hstep).
    apply piL_abs2_plus_le.
    + exact IH.
    + exact (piL_sin_term_abs_bound (Datatypes.S n) x B Hx).
Qed.

(* The cos partial-sum absolute value bound: |cos_partial p x| <=
   sum_{j<=p} B^(2j)/(2j)! = [leibsep_abssum B p]. *)
Lemma piL_cos_partial_abs_bound : forall (p : nat) (x B : Q),
  QleT' (Qabs x) B ->
  QleT' (Qabs (cos_partial p x)) (leibsep_abssum B p).
Proof.
  intros p x B Hx. induction p as [| n IH].
  - cbn [cos_partial leibsep_abssum].
    exact (piL_cos_term_abs_bound 0 x B Hx).
  - assert (Hstep : leibsep_abssum B n
                    + q_pow B (2 * Datatypes.S n)%nat / q_fact (2 * Datatypes.S n)%nat
                    == leibsep_abssum B (Datatypes.S n))
      by (cbn [leibsep_abssum]; ring).
    cbn [cos_partial].
    apply (piL_leT'_eq_intro_r _ _ _ Hstep).
    apply piL_abs2_plus_le.
    + exact IH.
    + exact (piL_cos_term_abs_bound (Datatypes.S n) x B Hx).
Qed.

(* ========== Section 3. Residual per-term majorants (closing constant forms) ========== *)

(* The sin residual majorant: the step term splits into four blocks
   2|S_p|*|c_{p+1}| + 2|C_p|*|s_{p+1}| + 2|s_{p+1}|*|c_{p+1}| +
   |sin_term (S p) (2x)|; each block is accounted with
   [leibsep_abssum_cos B (S p)], [leibsep_abssum B p] and explicit
   power-ratio constants (the candidate form with the shared common
   denominator falls short of a (2p+3)/B factor; the present form is
   the settled closing form). *)
Fixpoint piL_dres_majorant (m : nat) (B : Q) : Q :=
  match m with
  | 0%nat => 0
  | Datatypes.S p =>
      piL_dres_majorant p B
      + 2 * leibsep_abssum_cos B (Datatypes.S p)
            * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
      + 2 * leibsep_abssum B p
            * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
               / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
      + 2 * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
             / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
            * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
      + q_pow (2 * B) (Datatypes.S (2 * Datatypes.S p))%nat
        / q_fact (Datatypes.S (2 * Datatypes.S p))%nat
  end.

(* The cos residual majorant: the step term splits into four blocks
   |cos_term (S p) (2x)| + 2|C_p|*|c_{p+1}| + 2|S_p|*|s_{p+1}| +
   (|c_{p+1}|^2 + |s_{p+1}|^2); the candidate form shares the sin
   majorant and lacks the |c|^2 + |s|^2 block, while the present form
   closes independently. *)
Fixpoint piL_cos_dres_majorant (m : nat) (B : Q) : Q :=
  match m with
  | 0%nat => 0
  | Datatypes.S p =>
      piL_cos_dres_majorant p B
      + q_pow (2 * B) (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat
      + 2 * leibsep_abssum B p
            * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
      + 2 * leibsep_abssum_cos B (Datatypes.S p)
            * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
               / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
      + (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
            * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
      + (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
         / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
            * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
               / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
  end.

(* The quadruple-angle composite residual majorant: the constant form
   |2UV| + |dres_s(2x)| + 4|S||C||D| with U = 2|S||C| + M_s,
   V = |C|^2 + |S|^2 + B^2 + M_c and D = |C|^2 + |S|^2 (the
   letter-exact refinement of the candidate A/A'/M notation). *)
Definition piL_quad_dres_majorant (m : nat) (B : Q) : Q :=
  2 * (2 * leibsep_abssum_cos B (Datatypes.S m) * leibsep_abssum B m
       + piL_dres_majorant m B)
      * (leibsep_abssum B m * leibsep_abssum B m
         + leibsep_abssum_cos B (Datatypes.S m) * leibsep_abssum_cos B (Datatypes.S m)
         + B * B + piL_cos_dres_majorant m B)
  + piL_dres_majorant m (2 * B)
  + 4 * leibsep_abssum_cos B (Datatypes.S m) * leibsep_abssum B m
      * (leibsep_abssum B m * leibsep_abssum B m
         + leibsep_abssum_cos B (Datatypes.S m) * leibsep_abssum_cos B (Datatypes.S m)).

(* ========== Section 4. The three master bounds ========== *)

(* The sin residual factor control bound:
   |piL_sin_dres m x| <= piL_dres_majorant m B. *)
Lemma piL_sin_dres_majorant_bound : forall (m : nat) (x B : Q),
  QltT 0 B -> QleT' (Qabs x) B ->
  QleT' (Qabs (piL_sin_dres m x)) (piL_dres_majorant m B).
Proof.
  intros m x B HB Hx. induction m as [| p IH].
  - cbn [piL_sin_dres piL_dres_majorant].
    apply (piL_leT'_eq_intro_l _ _ _ piL_qabs_zero).
    apply qleT'_refl.
  - cbn [piL_sin_dres].
    assert (Hnorm : Qabs (piL_sin_dres p x
                    + 2 * sin_partial p x * cos_term (Datatypes.S p) x
                    + 2 * cos_partial p x * sin_term (Datatypes.S p) x
                    + 2 * sin_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
                    - sin_term (Datatypes.S p) (2 * x))
                    == Qabs (piL_sin_dres p x
                       + ((2 * sin_partial p x * cos_term (Datatypes.S p) x)
                          + ((2 * cos_partial p x * sin_term (Datatypes.S p) x)
                             + ((2 * sin_term (Datatypes.S p) x * cos_term (Datatypes.S p) x)
                                + (- (sin_term (Datatypes.S p) (2 * x))))))))
      by (apply Qabs_wd; ring).
    apply (piL_leT'_eq_intro_l _ _ _ Hnorm).
    apply (qleT'_trans _
      (Qabs (piL_sin_dres p x)
       + (2 * leibsep_abssum_cos B (Datatypes.S p)
          * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
          + (2 * leibsep_abssum B p
             * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
             + (2 * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                     / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
                * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                + q_pow (2 * B) (Datatypes.S (2 * Datatypes.S p))%nat
                  / q_fact (Datatypes.S (2 * Datatypes.S p))%nat))))).
    + apply piL_abs2_plus_le.
      * apply qleT'_refl.
      * apply (piL_abs4_plus_le
                 (2 * sin_partial p x * cos_term (Datatypes.S p) x)
                 (2 * cos_partial p x * sin_term (Datatypes.S p) x)
                 (2 * sin_term (Datatypes.S p) x * cos_term (Datatypes.S p) x)
                 (- (sin_term (Datatypes.S p) (2 * x)))
                 (2 * leibsep_abssum_cos B (Datatypes.S p)
                  * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat))
                 (2 * leibsep_abssum B p
                  * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                     / q_fact (Datatypes.S (2 * Datatypes.S p))%nat))
                 (2 * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                       / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
                  * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat))
                 (q_pow (2 * B) (Datatypes.S (2 * Datatypes.S p))%nat
                  / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)).
        -- apply (piL_abs_coeff2_2 (sin_partial p x) (cos_term (Datatypes.S p) x)).
           ++ apply piL_sin_partial_abs_bound; exact Hx.
           ++ apply piL_cos_term_abs_bound; exact Hx.
        -- apply (piL_abs_coeff2_2 (cos_partial p x) (sin_term (Datatypes.S p) x)).
           ++ apply piL_cos_partial_abs_bound; exact Hx.
           ++ apply piL_sin_term_abs_bound; exact Hx.
        -- apply (piL_abs_coeff2_2 (sin_term (Datatypes.S p) x) (cos_term (Datatypes.S p) x)).
           ++ apply piL_sin_term_abs_bound; exact Hx.
           ++ apply piL_cos_term_abs_bound; exact Hx.
        -- apply piL_abs_opp_le.
           apply (piL_sin_term_abs_bound (Datatypes.S p) (2 * x) (2 * B)).
           ++ apply piL_abs2_le. exact Hx.
    + apply (qleT'_trans _
        (piL_dres_majorant p B
         + (2 * leibsep_abssum_cos B (Datatypes.S p)
            * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
            + (2 * leibsep_abssum B p
               * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                  / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
               + (2 * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                       / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
                  * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                  + q_pow (2 * B) (Datatypes.S (2 * Datatypes.S p))%nat
                    / q_fact (Datatypes.S (2 * Datatypes.S p))%nat))))).
      * apply qleT'_plus_compat.
        -- exact IH.
        -- apply qleT'_refl.
      * apply qeq_leT'. cbn [piL_dres_majorant]. ring.
Qed.

(* The cos residual factor control bound:
   |piL_cos_dres m x| <= B*B + piL_cos_dres_majorant m B. *)
Lemma piL_cos_dres_majorant_bound : forall (m : nat) (x B : Q),
  QltT 0 B -> QleT' (Qabs x) B ->
  QleT' (Qabs (piL_cos_dres m x))
        (B * B + piL_cos_dres_majorant m B).
Proof.
  intros m x B HB Hx. induction m as [| p IH].
  - cbn [piL_cos_dres piL_cos_dres_majorant].
    apply (qleT'_trans _ (B * B)%Q).
    + apply piL_abs_mult_le; [exact Hx | exact Hx].
    + apply qeq_leT'. ring.
  - cbn [piL_cos_dres].
    assert (Hnorm : Qabs (piL_cos_dres p x
                    + cos_term (Datatypes.S p) (2 * x)
                    - 2 * cos_partial p x * cos_term (Datatypes.S p) x
                    + 2 * sin_partial p x * sin_term (Datatypes.S p) x
                    - (cos_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
                       - sin_term (Datatypes.S p) x * sin_term (Datatypes.S p) x))
                    == Qabs (piL_cos_dres p x
                       + (cos_term (Datatypes.S p) (2 * x)
                          + (- (2 * cos_partial p x * cos_term (Datatypes.S p) x)
                             + (2 * sin_partial p x * sin_term (Datatypes.S p) x
                                + (- (cos_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
                                      - sin_term (Datatypes.S p) x * sin_term (Datatypes.S p) x)))))))
      by (apply Qabs_wd; ring).
    apply (piL_leT'_eq_intro_l _ _ _ Hnorm).
    assert (Hsq : QleT' (Qabs (cos_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
                               - sin_term (Datatypes.S p) x * sin_term (Datatypes.S p) x))
                        ((q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                         * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                         + (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                            / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
                         * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                            / q_fact (Datatypes.S (2 * Datatypes.S p))%nat))).
    { assert (Hn2 : Qabs (cos_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
                     - sin_term (Datatypes.S p) x * sin_term (Datatypes.S p) x)
                    == Qabs ((cos_term (Datatypes.S p) x * cos_term (Datatypes.S p) x)
                       + (- (sin_term (Datatypes.S p) x * sin_term (Datatypes.S p) x))))
      by (apply Qabs_wd; ring).
      apply (piL_leT'_eq_intro_l _ _ _ Hn2).
      apply piL_abs2_plus_le.
      - apply piL_abs_mult_le.
        + apply piL_cos_term_abs_bound; exact Hx.
        + apply piL_cos_term_abs_bound; exact Hx.
      - apply piL_abs_opp_le.
        apply piL_abs_mult_le.
        + apply piL_sin_term_abs_bound; exact Hx.
        + apply piL_sin_term_abs_bound; exact Hx. }
    apply (qleT'_trans _
      (Qabs (piL_cos_dres p x)
       + (q_pow (2 * B) (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat
          + (2 * leibsep_abssum B p
             * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
             + (2 * leibsep_abssum_cos B (Datatypes.S p)
                * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                   / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
                + ((q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                   * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                   + (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                      / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
                   * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                      / q_fact (Datatypes.S (2 * Datatypes.S p))%nat))))))).
    + apply piL_abs2_plus_le.
      * apply qleT'_refl.
      * apply (piL_abs4_plus_le
                 (cos_term (Datatypes.S p) (2 * x))
                 (- (2 * cos_partial p x * cos_term (Datatypes.S p) x))
                 (2 * sin_partial p x * sin_term (Datatypes.S p) x)
                 (- (cos_term (Datatypes.S p) x * cos_term (Datatypes.S p) x
                     - sin_term (Datatypes.S p) x * sin_term (Datatypes.S p) x))
                 (q_pow (2 * B) (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                 (2 * leibsep_abssum B p
                  * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat))
                 (2 * leibsep_abssum_cos B (Datatypes.S p)
                  * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                     / q_fact (Datatypes.S (2 * Datatypes.S p))%nat))
                 ((q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                  * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                  + (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                     / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
                  * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                     / q_fact (Datatypes.S (2 * Datatypes.S p))%nat))).
        -- apply (piL_cos_term_abs_bound (Datatypes.S p) (2 * x) (2 * B)).
           ++ apply piL_abs2_le. exact Hx.
        -- apply piL_abs_opp_le.
           apply (piL_abs_coeff2_2 (cos_partial p x) (cos_term (Datatypes.S p) x)).
           ++ apply piL_cos_partial_abs_bound; exact Hx.
           ++ apply piL_cos_term_abs_bound; exact Hx.
        -- apply (piL_abs_coeff2_2 (sin_partial p x) (sin_term (Datatypes.S p) x)).
           ++ apply piL_sin_partial_abs_bound; exact Hx.
           ++ apply piL_sin_term_abs_bound; exact Hx.
        -- apply piL_abs_opp_le. exact Hsq.
    + apply (qleT'_trans _
        ((B * B + piL_cos_dres_majorant p B)
         + (q_pow (2 * B) (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat
            + (2 * leibsep_abssum B p
               * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
               + (2 * leibsep_abssum_cos B (Datatypes.S p)
                  * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                     / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
                  + ((q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                     * (q_pow B (2 * Datatypes.S p)%nat / q_fact (2 * Datatypes.S p)%nat)
                     + (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                        / q_fact (Datatypes.S (2 * Datatypes.S p))%nat)
                     * (q_pow B (Datatypes.S (2 * Datatypes.S p))%nat
                        / q_fact (Datatypes.S (2 * Datatypes.S p))%nat))))))).
      * apply qleT'_plus_compat.
        -- exact IH.
        -- apply qleT'_refl.
      * apply qeq_leT'. cbn [piL_cos_dres_majorant]. ring.
Qed.

(* The quadruple-angle composite bound:
   |piL_quad_dres m x| <= piL_quad_dres_majorant m B. *)
Lemma piL_quad_dres_majorant_bound : forall (m : nat) (x B : Q),
  QltT 0 B -> QleT' (Qabs x) B ->
  QleT' (Qabs (piL_quad_dres m x)) (piL_quad_dres_majorant m B).
Proof.
  intros m x B HB Hx.
  pose proof (piL_sin_dres_majorant_bound m x B HB Hx) as IHs.
  pose proof (piL_cos_dres_majorant_bound m x B HB Hx) as IHc.
  assert (Hs : QleT' (Qabs (sin_partial m x))
                     (leibsep_abssum_cos B (Datatypes.S m)))
    by (apply piL_sin_partial_abs_bound; assumption).
  assert (Hc : QleT' (Qabs (cos_partial m x)) (leibsep_abssum B m))
    by (apply piL_cos_partial_abs_bound; assumption).
  assert (HD : QleT' (Qabs (cos_partial m x * cos_partial m x
                            - sin_partial m x * sin_partial m x))
                     (leibsep_abssum B m * leibsep_abssum B m
                      + leibsep_abssum_cos B (Datatypes.S m)
                        * leibsep_abssum_cos B (Datatypes.S m))).
  { assert (Hn : Qabs (cos_partial m x * cos_partial m x
                  - sin_partial m x * sin_partial m x)
                 == Qabs ((cos_partial m x * cos_partial m x)
                    + (- (sin_partial m x * sin_partial m x)))) by (apply Qabs_wd; ring).
    apply (piL_leT'_eq_intro_l _ _ _ Hn).
    apply piL_abs2_plus_le.
    - apply piL_abs_mult_le; [exact Hc | exact Hc].
    - apply piL_abs_opp_le. apply piL_abs_mult_le; [exact Hs | exact Hs]. }
  assert (HU : QleT' (Qabs (2 * sin_partial m x * cos_partial m x
                            - piL_sin_dres m x))
                     (2 * leibsep_abssum_cos B (Datatypes.S m) * leibsep_abssum B m
                      + piL_dres_majorant m B)).
  { assert (Hn : Qabs (2 * sin_partial m x * cos_partial m x - piL_sin_dres m x)
                 == Qabs ((2 * sin_partial m x * cos_partial m x)
                    + (- (piL_sin_dres m x)))) by (apply Qabs_wd; ring).
    apply (piL_leT'_eq_intro_l _ _ _ Hn).
    apply piL_abs2_plus_le.
    - apply (piL_abs_coeff2_2 (sin_partial m x) (cos_partial m x)).
      + exact Hs.
      + exact Hc.
    - apply piL_abs_opp_le. exact IHs. }
  assert (HV : QleT' (Qabs (cos_partial m x * cos_partial m x
                            - sin_partial m x * sin_partial m x
                            + piL_cos_dres m x))
                     (leibsep_abssum B m * leibsep_abssum B m
                      + leibsep_abssum_cos B (Datatypes.S m)
                        * leibsep_abssum_cos B (Datatypes.S m)
                      + B * B + piL_cos_dres_majorant m B)).
  { assert (Hn : Qabs (cos_partial m x * cos_partial m x
                  - sin_partial m x * sin_partial m x + piL_cos_dres m x)
                 == Qabs ((cos_partial m x * cos_partial m x
                     - sin_partial m x * sin_partial m x)
                    + piL_cos_dres m x)) by (apply Qabs_wd; ring).
    apply (piL_leT'_eq_intro_l _ _ _ Hn).
    apply (qleT'_trans _
      ((leibsep_abssum B m * leibsep_abssum B m
        + leibsep_abssum_cos B (Datatypes.S m)
          * leibsep_abssum_cos B (Datatypes.S m))
       + (B * B + piL_cos_dres_majorant m B))).
    - apply piL_abs2_plus_le.
      + exact HD.
      + exact IHc.
    - apply qeq_leT'. ring. }
  assert (HW : QleT' (Qabs (piL_sin_dres m (2 * x)))
                     (piL_dres_majorant m (2 * B))).
  { apply (piL_sin_dres_majorant_bound m (2 * x) (2 * B)).
    - apply piL_qltT_0_double. exact HB.
    - apply piL_abs2_le. exact Hx. }
  unfold piL_quad_dres.
  assert (Hnorm : Qabs (2 * (2 * sin_partial m x * cos_partial m x - piL_sin_dres m x)
                   * (cos_partial m x * cos_partial m x
                      - sin_partial m x * sin_partial m x + piL_cos_dres m x)
                   - piL_sin_dres m (2 * x)
                   - 4 * sin_partial m x * cos_partial m x
                     * (cos_partial m x * cos_partial m x
                        - sin_partial m x * sin_partial m x))
                  == Qabs ((2 * (2 * sin_partial m x * cos_partial m x - piL_sin_dres m x)
                      * (cos_partial m x * cos_partial m x
                         - sin_partial m x * sin_partial m x + piL_cos_dres m x))
                     + ((- piL_sin_dres m (2 * x))
                        + (- (4 * sin_partial m x * cos_partial m x
                              * (cos_partial m x * cos_partial m x
                                 - sin_partial m x * sin_partial m x)))))) by (apply Qabs_wd; ring).
  apply (piL_leT'_eq_intro_l _ _ _ Hnorm).
  apply (qleT'_trans _
    (2 * (2 * leibsep_abssum_cos B (Datatypes.S m) * leibsep_abssum B m
          + piL_dres_majorant m B)
         * (leibsep_abssum B m * leibsep_abssum B m
            + leibsep_abssum_cos B (Datatypes.S m)
              * leibsep_abssum_cos B (Datatypes.S m)
            + B * B + piL_cos_dres_majorant m B)
     + (piL_dres_majorant m (2 * B)
        + 4 * leibsep_abssum_cos B (Datatypes.S m) * leibsep_abssum B m
          * (leibsep_abssum B m * leibsep_abssum B m
             + leibsep_abssum_cos B (Datatypes.S m)
               * leibsep_abssum_cos B (Datatypes.S m))))).
  - apply (piL_abs3_plus_le
             (2 * (2 * sin_partial m x * cos_partial m x - piL_sin_dres m x)
              * (cos_partial m x * cos_partial m x
                 - sin_partial m x * sin_partial m x + piL_cos_dres m x))
             (- piL_sin_dres m (2 * x))
             (- (4 * sin_partial m x * cos_partial m x
                 * (cos_partial m x * cos_partial m x
                    - sin_partial m x * sin_partial m x)))
             (2 * (2 * leibsep_abssum_cos B (Datatypes.S m) * leibsep_abssum B m
                   + piL_dres_majorant m B)
                  * (leibsep_abssum B m * leibsep_abssum B m
                     + leibsep_abssum_cos B (Datatypes.S m)
                       * leibsep_abssum_cos B (Datatypes.S m)
                     + B * B + piL_cos_dres_majorant m B))
             (piL_dres_majorant m (2 * B))
             (4 * leibsep_abssum_cos B (Datatypes.S m) * leibsep_abssum B m
              * (leibsep_abssum B m * leibsep_abssum B m
                 + leibsep_abssum_cos B (Datatypes.S m)
                   * leibsep_abssum_cos B (Datatypes.S m)))).
    + apply (piL_abs_coeff2_2
               (2 * sin_partial m x * cos_partial m x - piL_sin_dres m x)
               (cos_partial m x * cos_partial m x
                - sin_partial m x * sin_partial m x + piL_cos_dres m x)).
      * exact HU.
      * exact HV.
    + apply piL_abs_opp_le. exact HW.
    + apply piL_abs_opp_le.
      apply (piL_abs_coeff4_3 (sin_partial m x) (cos_partial m x)
               (cos_partial m x * cos_partial m x
                - sin_partial m x * sin_partial m x)).
      * exact Hs.
      * exact Hc.
      * exact HD.
  - apply qeq_leT'. unfold piL_quad_dres_majorant. ring.
Qed.
(* ---- Merged segment 3: PiKernelSlack_D25_reduction (md5 9259fbab) ---- *)
Lemma piLred_qle_wd_l : forall u v w : Q, u == v -> Qle u w -> Qle v w.
Proof.
  intros u v w Heq H.
  exact (Qle_trans v u w (qeq_le v u (Qeq_sym u v Heq)) H).
Qed.

Lemma piLred_qle_wd_r : forall u v w : Q, u == v -> Qle w u -> Qle w v.
Proof.
  intros u v w Heq H. exact (Qle_trans w u v H (qeq_le u v Heq)).
Qed.

(* ========== Section 0'. Multiplicativity of [Qabs] (proof body delegates to [Qabs_Qmult]) ========== *)

Lemma piLred_abs_mult : forall x y : Q, Qabs (x * y) == Qabs x * Qabs y.
Proof. apply Qabs_Qmult. Qed.

(* ========== Section 1. The main piece: |C-S| <= |C^2-S^2| (premise 1 <= C+S) ========== *)

Lemma piLred_abs_CmS_le : forall C S : Q,
  QleT' 1 (C + S) -> QleT' (Qabs (C - S)) (Qabs (C * C - S * S)).
Proof.
  intros C S Hge.
  assert (H01 : Qle 0 1)
    by (unfold Qle; cbn; exact (proj1 (Z.leb_le 0 1) eq_refl)).
  assert (Hge' : Qle 1 (C + S)) by (apply QleT'_to_Qle; exact Hge).
  assert (Hpos : Qle 0 (C + S)) by (apply (Qle_trans 0 1 (C + S) H01 Hge')).
  assert (Hmon : Qle (1 * Qabs (C - S)) ((C + S) * Qabs (C - S))).
  { apply Qmult_le_compat_r.
    - exact Hge'.
    - apply Qabs_nonneg. }
  assert (Hfold : Qabs (C * C - S * S) == (C + S) * Qabs (C - S)).
  { assert (Hfac : C * C - S * S == (C + S) * (C - S)) by ring.
    rewrite Hfac. rewrite piLred_abs_mult.
    rewrite (Qabs_pos (C + S) Hpos). reflexivity. }
  apply Qle_to_QleT'.
  apply (piLred_qle_wd_r ((C + S) * Qabs (C - S))
           (Qabs (C * C - S * S))).
  - exact (Qeq_sym (Qabs (C * C - S * S)) ((C + S) * Qabs (C - S)) Hfold).
  - apply (piLred_qle_wd_l (1 * Qabs (C - S))).
    + exact (Qmult_1_l (Qabs (C - S))).
    + exact Hmon.
Qed.

(* ========== Section 2. The minimal interface consuming the vertex zero anchor ========== *)
(* The vertex coordinates are lp_odd m (= xL/4, a neighborhood of *)
(* pi/4), not lw0m_xL m (= lp_four * lp_odd m, the pi window *)
(* point); the identity layer states [piL_sin_quad_xL] at the *)
(* lw0m_xL coordinates, so consumers must instantiate at the *)
(* vertex lp_odd m. The donor of the vertex zero anchor *)
(* |C^2-S^2|(lp_odd m) -> 0 (the vertex smallness side) is consumed in *)
(* one step through this interface as |C-S|(lp_odd m) -> 0, with the
   vertex premise [QleT'] 1 (C+S) (lp_odd m) kept as an explicit slot;
   dt > 0 is the consumer-side dtail slot form. *)

Lemma piLred_vtx_anchor_xL : forall (dt : Q) (k m : nat),
  QltT 0 dt ->
  QleT' 1 (cos_partial k (lp_odd m) + sin_partial k (lp_odd m)) ->
  QltT (Qabs (cos_partial k (lp_odd m) * cos_partial k (lp_odd m)
              - sin_partial k (lp_odd m) * sin_partial k (lp_odd m))) dt ->
  QltT (Qabs (cos_partial k (lp_odd m) - sin_partial k (lp_odd m))) dt.
Proof.
  intros dt k m Hdt Hge Hfac.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans
           (Qabs (cos_partial k (lp_odd m) - sin_partial k (lp_odd m)))
           (Qabs (cos_partial k (lp_odd m) * cos_partial k (lp_odd m)
                  - sin_partial k (lp_odd m) * sin_partial k (lp_odd m)))
           dt).
  - apply QleT'_to_Qle.
    apply (piLred_abs_CmS_le
             (cos_partial k (lp_odd m)) (sin_partial k (lp_odd m)) Hge).
  - apply QltT_to_Qlt. exact Hfac.
Qed.
(* ---- Merged segment 4: PiKernelSlack_D3_prereq (md5 9cb5a2e0) ---- *)
Definition d3p_inject_nat (n : nat) : Q := (Z.of_nat n) # 1.

(* Additivity of [d3p_inject_nat] (the direct [Nat2Z] chain). *)
Lemma d3p_inject_add : forall a b : nat,
  d3p_inject_nat (a + b) == d3p_inject_nat a + d3p_inject_nat b.
Proof.
  intros a b. unfold d3p_inject_nat, Qplus, Qeq. cbn.
  rewrite Nat2Z.inj_add. ring.
Qed.

(* Multiplicativity of [d3p_inject_nat] (the direct [Nat2Z] chain). *)
Lemma d3p_inject_mul : forall a b : nat,
  d3p_inject_nat (a * b) == d3p_inject_nat a * d3p_inject_nat b.
Proof.
  intros a b. unfold d3p_inject_nat, Qmult, Qeq. cbn.
  rewrite Nat2Z.inj_mul. ring.
Qed.

(* [d3p_inject_nat] sends a successor to addition by one. *)
Lemma d3p_inject_succ : forall k : nat,
  d3p_inject_nat (Datatypes.S k) == d3p_inject_nat k + 1.
Proof.
  intros k. unfold d3p_inject_nat.
  replace (Z.of_nat (Datatypes.S k)) with (Z.of_nat k + 1)%Z
    by (rewrite Nat2Z.inj_succ; reflexivity).
  apply (eq_sym (piL_inject_add1 (Z.of_nat k))).
Qed.

(* Monotonicity of [d3p_inject_nat] ([Nat2Z.inj_le] plus a closed one at the [Z] level). *)
Lemma d3p_inject_mono : forall a b : nat,
  (a <= b)%nat -> Qle (d3p_inject_nat a) (d3p_inject_nat b).
Proof.
  intros a b Hab. unfold d3p_inject_nat, Qle. cbn.
  rewrite !Z.mul_1_r. exact (proj1 (Nat2Z.inj_le a b) Hab).
Qed.

(* The ceiling embedding bounds from below: 0 <= B implies
   B <= [d3p_inject_nat] of the nat image of [Qceiling] B. *)
Lemma d3p_inject_ceiling_ge : forall B : Q,
  Qle 0 B -> QleT' B (d3p_inject_nat (Z.to_nat (Qceiling B))).
Proof.
  intros B H0B.
  assert (Hz0 : (0 <= Qceiling B)%Z).
  { pose proof (Qle_trans 0%Q B (QArith_base.inject_Z (Qceiling B))
                  H0B (Qle_ceiling B)) as Hz.
    unfold Qle in Hz. cbn in Hz. rewrite Z.mul_1_r in Hz. exact Hz. }
  apply Qle_to_QleT'.
  apply (leibsep_qle_wd2 B (QArith_base.inject_Z (Qceiling B)) B
                         (d3p_inject_nat (Z.to_nat (Qceiling B)))).
  - apply Qeq_refl.
  - unfold d3p_inject_nat. rewrite (Z2Nat.id (Qceiling B) Hz0). reflexivity.
  - exact (Qle_ceiling B).
Qed.

(* The nat-power floor fuel: 2^n >= n+1 (explicit induction). *)
Lemma d3p_nat_pow2_ge_succ : forall n : nat, (n + 1 <= 2 ^ n)%nat.
Proof.
  induction n as [| n IH].
  - apply Nat.le_refl.
  - cbn [Nat.pow].
    rewrite Nat.mul_succ_l, Nat.mul_1_l.
    replace (Datatypes.S n + 1)%nat with (n + 1 + 1)%nat
      by (rewrite (Nat.add_comm n 1); rewrite Nat.add_1_r;
          rewrite Nat.add_1_r; reflexivity).
    apply (Nat.le_trans (n + 1 + 1) (2 ^ n + 1)).
    + apply (proj1 (Nat.add_le_mono_r (n + 1) (2 ^ n) 1)). exact IH.
    + apply (proj1 (Nat.add_le_mono_l 1 (2 ^ n) (2 ^ n))).
      exact (piL_nat_pow2_ge1 n).
Qed.

(* A power with zero base and positive exponent vanishes (the B = 0 branch). *)
Lemma d3p_q_pow_0_succ : forall k : nat, q_pow 0 (Datatypes.S k) == 0.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - cbn [q_pow]. rewrite IH. ring.
Qed.

(* Splitting a power over a sum of exponents. *)
Lemma d3p_q_pow_add : forall (x : Q) (d e : nat),
  q_pow x (d + e) == q_pow x d * q_pow x e.
Proof.
  intros x d e. induction d as [| d IH].
  - cbn [Nat.add q_pow]. ring.
  - replace (Datatypes.S d + e)%nat with (Datatypes.S (d + e))%nat
      by reflexivity.
    cbn [q_pow]. rewrite IH. ring.
Qed.

(* The factorial step: q_fact (S n) = (S n) * q_fact n (embedded form). *)
Lemma d3p_q_fact_step : forall n : nat,
  q_fact (Datatypes.S n) == d3p_inject_nat (Datatypes.S n) * q_fact n.
Proof.
  intros n. cbn [q_fact]. unfold d3p_inject_nat. reflexivity.
Qed.

(* The 1/4 power stepping (fuel for the geometric tail control). *)
Lemma d3p_q_pow_quarter_step : forall k : nat,
  q_pow (1 # 4)%Q (Datatypes.S k) == (1 # 4)%Q * q_pow (1 # 4)%Q k.
Proof.
  intros k. cbn [q_pow]. reflexivity.
Qed.

(* Antitonicity of the 1/4 power: d <= e implies (1/4)^e <= (1/4)^d. *)
Lemma d3p_q_pow_quarter_antitone : forall d e : nat,
  (d <= e)%nat -> Qle (q_pow (1 # 4)%Q e) (q_pow (1 # 4)%Q d).
Proof.
  intros d e. induction e as [| e IH]; intros Hde.
  - assert (Hd0 : d = 0%nat)
      by (apply Nat.le_antisymm; [exact Hde | apply Nat.le_0_l]).
    subst d. apply Qle_refl.
  - destruct (Nat.eq_dec d (Datatypes.S e)) as [Heq | Hne].
    + subst d. apply Qle_refl.
    + assert (Hde' : (d <= e)%nat).
      { destruct (Nat.le_gt_cases d e) as [H | H].
        - exact H.
        - exfalso. apply Hne.
          apply Nat.le_antisymm.
          ++ exact Hde.
          ++ exact H. }
      apply (Qle_trans _ (q_pow (1 # 4)%Q e)).
      * rewrite d3p_q_pow_quarter_step.
        apply (Qle_trans _ (1 * q_pow (1 # 4)%Q e)).
        -- apply (Qmult_le_compat_r (1 # 4)%Q 1 (q_pow (1 # 4)%Q e)).
           ++ unfold Qle. cbn. apply Z.leb_le; reflexivity.
           ++ apply q_pow_nonneg.
              unfold Qle. cbn. apply Z.leb_le; reflexivity.
        -- apply qeq_le. ring.
      * apply IH. exact Hde'.
Qed.

(* Right multiplication preserves the order (positive factor). *)
Lemma d3p_mult_le_r_pos : forall x y u : Q,
  Qle x y -> Qlt 0 u -> Qle (x * u) (y * u).
Proof.
  intros x y u Hxy Hu.
  apply (Qmult_le_compat_r x y u Hxy).
  apply (Qlt_le_weak 0%Q u). exact Hu.
Qed.

(* Right multiplication distributes over division: a/b*c = a*c/b (nonzero denominator). *)
Lemma d3p_qdiv_mul_r : forall a b c : Q,
  Qlt 0 b -> (a / b) * c == (a * c) / b.
Proof.
  intros a b c Hb. unfold Qdiv. ring.
Qed.

(* A product of nonzero factors is nonzero (the direct [Qmult_integral] chain). *)
Lemma d3p_qmult_neq0 : forall x y : Q,
  ~ (x == 0) -> ~ (y == 0) -> ~ (x * y == 0).
Proof.
  intros x y Hx Hy H.
  destruct (Qmult_integral x y H) as [Hxx | Hyy].
  - exact (Hx Hxx).
  - exact (Hy Hyy).
Qed.

(* ========== Section 1. The factorial-over-power core (explicit inductive lower bound) ========== *)

(* The core piece: for 2B <= n1+1, (2B)^(n-n1) * n1! <= n! -- an
   explicit induction chain through the step instance
   (S n) * n! >= 2B * n!, the [Q]-form lower-bound engine behind
   B^n <= n!. *)
Lemma d3p_fact_dom_pow : forall (B : Q) (n1 n : nat),
  QleT' 0 B -> QleT' (2 * B) (d3p_inject_nat (Datatypes.S n1)) ->
  (n1 <= n)%nat ->
  QleT' (q_pow (2 * B) (n - n1) * q_fact n1) (q_fact n).
Proof.
  intros B n1. induction n as [| n IH]; intros H0B H2B Hle.
  - assert (Hn1 : n1 = 0%nat)
      by (apply Nat.le_antisymm; [exact Hle | apply Nat.le_0_l]).
    subst n1. cbn [Nat.sub q_pow q_fact].
    apply qeq_leT'. ring.
  - destruct (Nat.leb n1 n) eqn:E.
    + apply Nat.leb_le in E.
      specialize (IH H0B H2B E).
      apply (piL_leT'_eq_intro_r _ _ _ (d3p_q_fact_step n)).
      rewrite Nat.sub_succ_l by exact E.
      assert (Hlhs : q_pow (2 * B) (Datatypes.S (n - n1)) * q_fact n1
                     == (2 * B) * (q_pow (2 * B) (n - n1) * q_fact n1))
        by (cbn [q_pow]; ring).
      apply (piL_leT'_eq_intro_l _ _ _ Hlhs).
      apply Qle_to_QleT'.
      apply (Qle_trans _ ((2 * B) * q_fact n)).
      * apply (piL_mult_le_l (q_pow (2 * B) (n - n1) * q_fact n1)
                 (q_fact n) (2 * B)).
        -- exact (QleT'_to_Qle _ _ IH).
        -- apply Qmult_le_0_compat.
           ++ exact (QleT'_to_Qle _ _ piL_qle_0_two).
           ++ exact (QleT'_to_Qle _ _ H0B).
      * apply (Qmult_le_compat_r (2 * B) (d3p_inject_nat (Datatypes.S n))
                 (q_fact n)).
        -- exact (QleT'_to_Qle _ _
             (qleT'_trans (2 * B) (d3p_inject_nat (Datatypes.S n1))
                (d3p_inject_nat (Datatypes.S n)) H2B
                (Qle_to_QleT' _ _
                  (d3p_inject_mono (Datatypes.S n1) (Datatypes.S n)
                     (proj1 (Nat.succ_le_mono n1 n) E))))).
        -- apply (Qlt_le_weak 0%Q _). apply q_fact_pos.
    + apply Nat.leb_gt in E.
      assert (Heq : n1 = Datatypes.S n)
        by (apply Nat.le_antisymm; [exact Hle | exact E]).
      subst n1.
      replace (Datatypes.S n - Datatypes.S n)%nat with 0%nat
        by (symmetry; apply Nat.sub_diag).
      cbn [q_pow].
      apply (piL_leT'_eq_intro_r _ _ _ (d3p_q_fact_step n)).
      apply qeq_leT'. ring.
Qed.

(* ========== Section 2. Geometric decay of the Taylor terms (step ratio <= 1/4) ========== *)

(* The absolute-value prototype of the sin Taylor term: B^(2m+1)/(2m+1)!. *)
Definition d3p_sin_term (B : Q) (m : nat) : Q :=
  q_pow B (Datatypes.S (2 * m))%nat / q_fact (Datatypes.S (2 * m))%nat.

(* The absolute-value prototype of the cos Taylor term: B^(2m)/(2m)!. *)
Definition d3p_cos_term (B : Q) (m : nat) : Q :=
  q_pow B (2 * m)%nat / q_fact (2 * m)%nat.

(* Strictly positive powers (the [Q]-side transport of [lw0_q_pow_pos]). *)
Lemma d3p_q_pow_pos : forall (x : Q) (k : nat),
  QltT 0 x -> Qlt 0 (q_pow x k).
Proof.
  intros x k H. exact (QltT_to_Qlt _ _ (lw0_q_pow_pos x k H)).
Qed.

(* Positively embedded and strictly positive (replayed from [q_lt_0_succ_den]). *)
Lemma d3p_inject_pos : forall k : nat,
  Qlt 0 (d3p_inject_nat (Datatypes.S k)).
Proof.
  intros k. exact (q_lt_0_succ_den k).
Qed.

(* The sin term is strictly positive. *)
Lemma d3p_sin_term_pos : forall (B : Q) (m : nat),
  Qlt 0 B -> Qlt 0 (d3p_sin_term B m).
Proof.
  intros B m HB. unfold d3p_sin_term. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - exact (d3p_q_pow_pos B (Datatypes.S (2 * m))%nat
             (Qlt_to_QltT _ _ HB)).
  - apply Qinv_lt_0_compat. exact (q_fact_pos (Datatypes.S (2 * m))%nat).
Qed.

(* The sin term is nonnegative (the 0 <= B face). *)
Lemma d3p_sin_term_nonneg : forall (B : Q) (m : nat),
  QleT' 0 B -> Qle 0 (d3p_sin_term B m).
Proof.
  intros B m H0B. unfold d3p_sin_term, Qdiv. apply Qmult_le_0_compat.
  - apply q_pow_nonneg. exact (QleT'_to_Qle _ _ H0B).
  - apply Qinv_le_0_compat. apply (Qlt_le_weak 0%Q _).
    exact (q_fact_pos (Datatypes.S (2 * m))%nat).
Qed.

(* The cos term is nonnegative (the 0 <= B face). *)
Lemma d3p_cos_term_nonneg : forall (B : Q) (m : nat),
  QleT' 0 B -> Qle 0 (d3p_cos_term B m).
Proof.
  intros B m H0B. unfold d3p_cos_term, Qdiv. apply Qmult_le_0_compat.
  - apply q_pow_nonneg. exact (QleT'_to_Qle _ _ H0B).
  - apply Qinv_le_0_compat. apply (Qlt_le_weak 0%Q _).
    exact (q_fact_pos (2 * m)%nat).
Qed.

(* The cos term is strictly positive. *)
Lemma d3p_cos_term_pos : forall (B : Q) (m : nat),
  Qlt 0 B -> Qlt 0 (d3p_cos_term B m).
Proof.
  intros B m HB. unfold d3p_cos_term. unfold Qdiv.
  apply Qmult_lt_0_compat.
  - exact (d3p_q_pow_pos B (2 * m)%nat (Qlt_to_QltT _ _ HB)).
  - apply Qinv_lt_0_compat. exact (q_fact_pos (2 * m)%nat).
Qed.

(* Even-double embedding order: k <= j implies inject(2k) <= inject(2j). *)
Lemma d3p_two_le_inject : forall k j : nat, (k <= j)%nat ->
  Qle (d3p_inject_nat (2 * k)) (d3p_inject_nat (2 * j)).
Proof.
  intros k j Hkj.
  apply (leibsep_qle_wd2 (2 * d3p_inject_nat k) (2 * d3p_inject_nat j)
                         (d3p_inject_nat (2 * k)) (d3p_inject_nat (2 * j))).
  - exact (eq_sym (d3p_inject_mul 2 k)).
  - exact (eq_sym (d3p_inject_mul 2 j)).
  - apply piL_mult_le_l.
    + exact (d3p_inject_mono k j Hkj).
    + exact (QleT'_to_Qle _ _ piL_qle_0_two).
Qed.

(* Double threshold: B <= k implies 2B <= inject(2k). *)
Lemma d3p_B_le_two_inject : forall (B : Q) (k : nat),
  QleT' B (d3p_inject_nat k) -> Qle (2 * B) (d3p_inject_nat (2 * k)).
Proof.
  intros B k Hbk.
  apply (leibsep_qle_wd2 (2 * B) (2 * d3p_inject_nat k)
                         (2 * B) (d3p_inject_nat (2 * k))).
  - apply Qeq_refl.
  - symmetry. apply d3p_inject_mul.
  - apply piL_mult_le_l.
    + exact (QleT'_to_Qle _ _ Hbk).
    + exact (QleT'_to_Qle _ _ piL_qle_0_two).
Qed.

(* The sin term step ratio: B <= m implies t(S m) <= t(m)/4
   (the account 4B^2 <= (2m+2)*(2m+3)). *)
Lemma d3p_sin_term_quarter : forall (B : Q) (m : nat),
  QleT' 0 B -> QleT' B (d3p_inject_nat m) ->
  QleT' (d3p_sin_term B (Datatypes.S m)) (d3p_sin_term B m * (1 # 4)%Q).
Proof.
  intros B m H0B Hbm.
  destruct (Qeq_dec B 0) as [Hz | Hnz].
  - assert (Hl0 : d3p_sin_term B (Datatypes.S m)
                  == d3p_sin_term 0 (Datatypes.S m)).
    { unfold d3p_sin_term.
      rewrite (q_pow_wd B 0 (Datatypes.S (2 * Datatypes.S m))%nat Hz).
      reflexivity. }
    assert (Hr0 : d3p_sin_term B m * (1 # 4)%Q
                  == d3p_sin_term 0 m * (1 # 4)%Q).
    { unfold d3p_sin_term.
      rewrite (q_pow_wd B 0 (Datatypes.S (2 * m))%nat Hz). reflexivity. }
    assert (Hrhs : Qle 0 (d3p_sin_term 0 m * (1 # 4)%Q)).
    { unfold d3p_sin_term, Qdiv. apply Qmult_le_0_compat.
      - apply Qmult_le_0_compat.
        + apply q_pow_nonneg.
          unfold Qle. cbn. apply Z.leb_le; reflexivity.
        + apply Qinv_le_0_compat. apply (Qlt_le_weak 0%Q _).
          exact (q_fact_pos (Datatypes.S (2 * m))%nat).
      - unfold Qle. cbn. apply Z.leb_le; reflexivity. }
    apply (piL_leT'_eq_intro_l _ _ _ Hl0).
    apply Qle_to_QleT'.
    apply (leibsep_qle_wd2 (d3p_sin_term 0 (Datatypes.S m))
                           (d3p_sin_term 0 m * (1 # 4)%Q)
                           (d3p_sin_term 0 (Datatypes.S m))
                           (d3p_sin_term B m * (1 # 4)%Q)).
    + apply Qeq_refl.
    + exact (eq_sym Hr0).
    + apply (Qle_trans _ 0%Q).
      * apply qeq_le. unfold d3p_sin_term, Qdiv.
        rewrite (d3p_q_pow_0_succ (Datatypes.S (2 * Datatypes.S m))%nat).
        ring.
      * exact Hrhs.
  - assert (HBpos : Qlt 0 B).
    { destruct (Qlt_le_dec 0 B) as [Hp | Hn].
      - exact Hp.
      - exfalso. apply Hnz. apply (Qle_antisym B 0).
        + exact Hn.
        + exact (QleT'_to_Qle _ _ H0B). }
    assert (Hidx : (2 * Datatypes.S m)%nat
                   = Datatypes.S (Datatypes.S (2 * m))%nat)
      by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_1_r; reflexivity).
    assert (H2b2 : Qle (2 * B) (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m))))).
    { apply (Qle_trans _ (d3p_inject_nat (2 * m))).
      - exact (d3p_B_le_two_inject B m Hbm).
      - apply d3p_inject_mono.
        apply (Nat.le_trans (2 * m) (Datatypes.S (2 * m))
                            (Datatypes.S (Datatypes.S (2 * m)))).
        + apply Nat.le_succ_diag_r.
        + apply Nat.le_succ_diag_r. }
    assert (H2b3 : Qle (2 * B) (d3p_inject_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))).
    { apply (Qle_trans _ (d3p_inject_nat (2 * m))).
      - exact (d3p_B_le_two_inject B m Hbm).
      - apply d3p_inject_mono.
        apply (Nat.le_trans (2 * m) (Datatypes.S (Datatypes.S (2 * m)))
                            (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))).
        + apply (Nat.le_trans (2 * m) (Datatypes.S (2 * m))
                  (Datatypes.S (Datatypes.S (2 * m)))).
          * apply Nat.le_succ_diag_r.
          * apply Nat.le_succ_diag_r.
        + apply Nat.le_succ_diag_r. }
    assert (Hcore : Qle (B * B)
      ((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))
                    * d3p_inject_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))))).
    { pose proof (Qmult_le_0_compat 2 B (QleT'_to_Qle _ _ piL_qle_0_two)
                    (QleT'_to_Qle _ _ H0B)) as Hp2b.
      pose proof (Qmult_le_compat_r (2 * B)
                    (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))) (2 * B)
                    H2b2 Hp2b) as Hs1.
      pose proof (Qlt_le_weak 0%Q _
                    (d3p_inject_pos (Datatypes.S (2 * m)))) as Hpj2.
      pose proof (piL_mult_le_l (2 * B)
                    (d3p_inject_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))
                    (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m))))
                    H2b3 Hpj2) as Hs2.
      pose proof (Qle_trans ((2 * B) * (2 * B))
                    (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m))) * (2 * B))
                    (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))
                     * d3p_inject_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m)))))
                    Hs1 Hs2) as Hcc.
      apply (leibsep_qle_wd2
        ((1 # 4)%Q * ((2 * B) * (2 * B)))
        ((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))
                      * d3p_inject_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))))
        (B * B) ((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))
                               * d3p_inject_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))))).
      - ring.
      - apply Qeq_refl.
      - apply piL_mult_le_l.
        + exact Hcc.
        + unfold Qle. cbn. apply Z.leb_le; reflexivity. }
    assert (Hden2 : Qlt 0 (d3p_inject_nat (Datatypes.S (2 * m)) * q_fact (2 * m))).
    { apply Qmult_lt_0_compat.
      - apply d3p_inject_pos.
      - exact (q_fact_pos (2 * m)%nat). }
    assert (Hneq1 : Qlt 0 (q_fact (Datatypes.S (2 * m))%nat))
      by exact (q_fact_pos (Datatypes.S (2 * m))%nat).
    unfold d3p_sin_term. rewrite Hidx.
    apply Qle_to_QleT'.
    rewrite (d3p_qdiv_mul_r (q_pow B (Datatypes.S (2 * m))%nat)
               (q_fact (Datatypes.S (2 * m))%nat) (1 # 4)%Q Hneq1).
    rewrite !d3p_q_fact_step. cbn [q_pow].
    apply q_le_div_le.
    + apply Qmult_lt_0_compat.
      * apply d3p_inject_pos.
      * apply Qmult_lt_0_compat.
        -- apply d3p_inject_pos.
        -- apply Qmult_lt_0_compat.
           ++ apply d3p_inject_pos.
           ++ exact (q_fact_pos (2 * m)%nat).
    + exact Hden2.
    + apply (Qle_trans _ ((B * B) * ((B * q_pow B (2 * m))
                                     * (d3p_inject_nat (Datatypes.S (2 * m))
                                        * q_fact (2 * m))))).
      * apply qeq_le. ring.
      * apply (Qle_trans _
          (((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))
                         * d3p_inject_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))))
             * ((B * q_pow B (2 * m))
                * (d3p_inject_nat (Datatypes.S (2 * m)) * q_fact (2 * m))))).
        -- apply (d3p_mult_le_r_pos (B * B)
             ((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))
                           * d3p_inject_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * m))))))).
           ++ exact Hcore.
           ++ apply Qmult_lt_0_compat.
              ** apply Qmult_lt_0_compat.
                 --- exact HBpos.
                 --- exact (d3p_q_pow_pos B (2 * m)%nat (Qlt_to_QltT _ _ HBpos)).
              ** exact Hden2.
        -- apply qeq_le. ring.
Qed.

(* The cos term step ratio: B <= m implies t'(S m) <= t'(m)/4
   (the account 4B^2 <= (2m+1)*(2m+2)). *)
Lemma d3p_cos_term_quarter : forall (B : Q) (m : nat),
  QleT' 0 B -> QleT' B (d3p_inject_nat m) ->
  QleT' (d3p_cos_term B (Datatypes.S m)) (d3p_cos_term B m * (1 # 4)%Q).
Proof.
  intros B m H0B Hbm.
  destruct (Qeq_dec B 0) as [Hz | Hnz].
  - assert (Hl0 : d3p_cos_term B (Datatypes.S m)
                  == d3p_cos_term 0 (Datatypes.S m)).
    { unfold d3p_cos_term.
      replace (2 * Datatypes.S m)%nat
        with (Datatypes.S (Datatypes.S (2 * m)))%nat
        by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_1_r; reflexivity).
      rewrite (q_pow_wd B 0 (Datatypes.S (Datatypes.S (2 * m)))%nat Hz).
      reflexivity. }
    assert (Hr0 : d3p_cos_term B m * (1 # 4)%Q
                  == d3p_cos_term 0 m * (1 # 4)%Q).
    { unfold d3p_cos_term.
      rewrite (q_pow_wd B 0 (2 * m)%nat Hz). reflexivity. }
    assert (Hrhs : Qle 0 ((q_pow 0 (2 * m)%nat / q_fact (2 * m)%nat)
                          * (1 # 4)%Q)).
    { apply Qmult_le_0_compat.
      - unfold Qdiv. apply Qmult_le_0_compat.
        + apply q_pow_nonneg.
          unfold Qle. cbn. apply Z.leb_le; reflexivity.
        + apply Qinv_le_0_compat. apply (Qlt_le_weak 0%Q _).
          exact (q_fact_pos (2 * m)%nat).
      - unfold Qle. cbn. apply Z.leb_le; reflexivity. }
    apply (piL_leT'_eq_intro_l _ _ _ Hl0).
    apply Qle_to_QleT'.
    apply (leibsep_qle_wd2 (d3p_cos_term 0 (Datatypes.S m))
                           (d3p_cos_term 0 m * (1 # 4)%Q)
                           (d3p_cos_term 0 (Datatypes.S m))
                           (d3p_cos_term B m * (1 # 4)%Q)).
    + apply Qeq_refl.
    + exact (eq_sym Hr0).
    + apply (Qle_trans _ 0%Q).
      * apply qeq_le. unfold d3p_cos_term, Qdiv.
        replace (2 * Datatypes.S m)%nat
          with (Datatypes.S (Datatypes.S (2 * m)))%nat
          by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_1_r; reflexivity).
        rewrite (d3p_q_pow_0_succ (Datatypes.S (2 * m))%nat).
        ring.
      * exact Hrhs.
  - assert (HBpos : Qlt 0 B).
    { destruct (Qlt_le_dec 0 B) as [Hp | Hn].
      - exact Hp.
      - exfalso. apply Hnz. apply (Qle_antisym B 0).
        + exact Hn.
        + exact (QleT'_to_Qle _ _ H0B). }
    assert (Hidx : (2 * Datatypes.S m)%nat
                   = Datatypes.S (Datatypes.S (2 * m))%nat)
      by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_1_r; reflexivity).
    assert (H2b1 : Qle (2 * B) (d3p_inject_nat (Datatypes.S (2 * m)))).
    { apply (Qle_trans _ (d3p_inject_nat (2 * m))).
      - exact (d3p_B_le_two_inject B m Hbm).
      - apply d3p_inject_mono. apply Nat.le_succ_diag_r. }
    assert (H2b2 : Qle (2 * B)
                     (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m))))).
    { apply (Qle_trans _ (d3p_inject_nat (2 * m))).
      - exact (d3p_B_le_two_inject B m Hbm).
      - apply d3p_inject_mono.
        apply (Nat.le_trans (2 * m) (Datatypes.S (2 * m))
                            (Datatypes.S (Datatypes.S (2 * m)))).
        + apply Nat.le_succ_diag_r.
        + apply Nat.le_succ_diag_r. }
    assert (Hcore : Qle (B * B)
      ((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (2 * m))
                    * d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))))).
    { pose proof (Qmult_le_0_compat 2 B (QleT'_to_Qle _ _ piL_qle_0_two)
                    (QleT'_to_Qle _ _ H0B)) as Hp2b.
      pose proof (Qmult_le_compat_r (2 * B)
                    (d3p_inject_nat (Datatypes.S (2 * m))) (2 * B)
                    H2b1 Hp2b) as Hs1.
      pose proof (Qlt_le_weak 0%Q _
                    (d3p_inject_pos (2 * m))) as Hpj.
      pose proof (piL_mult_le_l (2 * B)
                    (d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m))))
                    (d3p_inject_nat (Datatypes.S (2 * m)))
                    H2b2 Hpj) as Hs2.
      pose proof (Qle_trans ((2 * B) * (2 * B))
                    (d3p_inject_nat (Datatypes.S (2 * m)) * (2 * B))
                    (d3p_inject_nat (Datatypes.S (2 * m))
                     * d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m))))
                    Hs1 Hs2) as Hcc.
      apply (leibsep_qle_wd2
        ((1 # 4)%Q * ((2 * B) * (2 * B)))
        ((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (2 * m))
                      * d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))))
        (B * B) ((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (2 * m))
                              * d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))))).
      - ring.
      - apply Qeq_refl.
      - apply piL_mult_le_l.
        + exact Hcc.
        + unfold Qle. cbn. apply Z.leb_le; reflexivity. }
    assert (Hneq1 : Qlt 0 (q_fact (2 * m)%nat))
      by exact (q_fact_pos (2 * m)%nat).
    unfold d3p_cos_term. rewrite Hidx.
    apply Qle_to_QleT'.
    rewrite (d3p_qdiv_mul_r (q_pow B (2 * m)%nat) (q_fact (2 * m)%nat)
               (1 # 4)%Q Hneq1).
    rewrite !d3p_q_fact_step. cbn [q_pow].
    apply q_le_div_le.
    + apply Qmult_lt_0_compat.
      * apply d3p_inject_pos.
      * apply Qmult_lt_0_compat.
        -- apply d3p_inject_pos.
        -- exact (q_fact_pos (2 * m)%nat).
    + exact (q_fact_pos (2 * m)%nat).
    + apply (Qle_trans _ ((B * B) * (q_pow B (2 * m) * q_fact (2 * m)))).
      * apply qeq_le. ring.
      * apply (Qle_trans _
          (((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (2 * m))
                         * d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))))
             * (q_pow B (2 * m) * q_fact (2 * m)))).
        -- apply (d3p_mult_le_r_pos (B * B)
             ((1 # 4)%Q * (d3p_inject_nat (Datatypes.S (2 * m))
                           * d3p_inject_nat (Datatypes.S (Datatypes.S (2 * m)))))).
           ++ exact Hcore.
           ++ apply Qmult_lt_0_compat.
              ** exact (d3p_q_pow_pos B (2 * m)%nat (Qlt_to_QltT _ _ HBpos)).
              ** exact (q_fact_pos (2 * m)%nat).
        -- apply qeq_le. ring.
Qed.

(* The iterated sin step ratio: B <= m implies t(m+d) <= t(m)/4^d. *)
Lemma d3p_sin_term_iter : forall (B : Q) (d m : nat),
  QleT' 0 B -> QleT' B (d3p_inject_nat m) ->
  QleT' (d3p_sin_term B (m + d)) (d3p_sin_term B m * q_pow (1 # 4)%Q d).
Proof.
  intros B d. induction d as [| d IH]; intros m H0B Hbm.
  - replace (m + 0)%nat with m by (symmetry; apply Nat.add_0_r).
    cbn [q_pow]. apply qeq_leT'. ring.
  - assert (HbmS : QleT' B (d3p_inject_nat (Datatypes.S m))).
    { apply (qleT'_trans _ (d3p_inject_nat m)).
      - exact Hbm.
      - apply Qle_to_QleT'. apply d3p_inject_mono. apply Nat.le_succ_diag_r. }
    pose proof (d3p_sin_term_quarter B m H0B Hbm) as Hq.
    pose proof (IH (Datatypes.S m) H0B HbmS) as HIH.
    replace (m + Datatypes.S d)%nat with (Datatypes.S m + d)%nat
      by exact (eq_trans (Nat.add_succ_l m d) (plus_n_Sm m d)).
    apply (piL_leT'_eq_intro_r (d3p_sin_term B m * ((1 # 4)%Q * q_pow (1 # 4)%Q d))
                               (d3p_sin_term B m * q_pow (1 # 4)%Q (Datatypes.S d))
                               (d3p_sin_term B (Datatypes.S m + d))).
    + cbn [q_pow]. ring.
    + apply (qleT'_trans
               (d3p_sin_term B (Datatypes.S m + d))
               (d3p_sin_term B (Datatypes.S m) * q_pow (1 # 4)%Q d)
               (d3p_sin_term B m * ((1 # 4)%Q * q_pow (1 # 4)%Q d))).
      * exact HIH.
      * apply Qle_to_QleT'.
        apply (leibsep_qle_wd2 (d3p_sin_term B (Datatypes.S m) * q_pow (1 # 4)%Q d)
                               ((d3p_sin_term B m * (1 # 4)%Q) * q_pow (1 # 4)%Q d)
                               (d3p_sin_term B (Datatypes.S m) * q_pow (1 # 4)%Q d)
                               (d3p_sin_term B m * ((1 # 4)%Q * q_pow (1 # 4)%Q d))).
        -- apply Qeq_refl.
        -- ring.
        -- apply (Qmult_le_compat_r (d3p_sin_term B (Datatypes.S m))
                     (d3p_sin_term B m * (1 # 4)%Q) (q_pow (1 # 4)%Q d)).
           ++ exact (QleT'_to_Qle _ _ Hq).
           ++ apply q_pow_nonneg. unfold Qle. cbn. apply Z.leb_le; reflexivity.
Qed.

(* The iterated cos step ratio: B <= m implies t'(m+d) <= t'(m)/4^d. *)
Lemma d3p_cos_term_iter : forall (B : Q) (d m : nat),
  QleT' 0 B -> QleT' B (d3p_inject_nat m) ->
  QleT' (d3p_cos_term B (m + d)) (d3p_cos_term B m * q_pow (1 # 4)%Q d).
Proof.
  intros B d. induction d as [| d IH]; intros m H0B Hbm.
  - replace (m + 0)%nat with m by (symmetry; apply Nat.add_0_r).
    cbn [q_pow]. apply qeq_leT'. ring.
  - assert (HbmS : QleT' B (d3p_inject_nat (Datatypes.S m))).
    { apply (qleT'_trans _ (d3p_inject_nat m)).
      - exact Hbm.
      - apply Qle_to_QleT'. apply d3p_inject_mono. apply Nat.le_succ_diag_r. }
    pose proof (d3p_cos_term_quarter B m H0B Hbm) as Hq.
    pose proof (IH (Datatypes.S m) H0B HbmS) as HIH.
    replace (m + Datatypes.S d)%nat with (Datatypes.S m + d)%nat
      by exact (eq_trans (Nat.add_succ_l m d) (plus_n_Sm m d)).
    apply (piL_leT'_eq_intro_r (d3p_cos_term B m * ((1 # 4)%Q * q_pow (1 # 4)%Q d))
                               (d3p_cos_term B m * q_pow (1 # 4)%Q (Datatypes.S d))
                               (d3p_cos_term B (Datatypes.S m + d))).
    + cbn [q_pow]. ring.
    + apply (qleT'_trans
               (d3p_cos_term B (Datatypes.S m + d))
               (d3p_cos_term B (Datatypes.S m) * q_pow (1 # 4)%Q d)
               (d3p_cos_term B m * ((1 # 4)%Q * q_pow (1 # 4)%Q d))).
      * exact HIH.
      * apply Qle_to_QleT'.
        apply (leibsep_qle_wd2 (d3p_cos_term B (Datatypes.S m) * q_pow (1 # 4)%Q d)
                               ((d3p_cos_term B m * (1 # 4)%Q) * q_pow (1 # 4)%Q d)
                               (d3p_cos_term B (Datatypes.S m) * q_pow (1 # 4)%Q d)
                               (d3p_cos_term B m * ((1 # 4)%Q * q_pow (1 # 4)%Q d))).
        -- apply Qeq_refl.
        -- ring.
        -- apply (Qmult_le_compat_r (d3p_cos_term B (Datatypes.S m))
                     (d3p_cos_term B m * (1 # 4)%Q) (q_pow (1 # 4)%Q d)).
           ++ exact (QleT'_to_Qle _ _ Hq).
           ++ apply q_pow_nonneg. unfold Qle. cbn. apply Z.leb_le; reflexivity.
Qed.

(* ========== Section 3. Tail sums bounded by 4/3 times the first omitted term ========== *)

(* The sin tail sum (K terms starting at index m). *)
Fixpoint d3p_sin_powtail (B : Q) (m K : nat) : Q :=
  match K with
  | 0%nat => 0
  | Datatypes.S r => d3p_sin_term B m + d3p_sin_powtail B (Datatypes.S m) r
  end.

(* The cos tail sum (K terms starting at index m). *)
Fixpoint d3p_cos_powtail (B : Q) (m K : nat) : Q :=
  match K with
  | 0%nat => 0
  | Datatypes.S r => d3p_cos_term B m + d3p_cos_powtail B (Datatypes.S m) r
  end.

(* The sin tail sum vanishes at B = 0 (for any index). *)
Lemma d3p_sin_powtail_zero : forall m K : nat, d3p_sin_powtail 0 m K == 0.
Proof.
  intros m K. revert m. induction K as [| K IH]; intros m.
  - reflexivity.
  - cbn [d3p_sin_powtail].
    unfold d3p_sin_term. rewrite d3p_q_pow_0_succ.
    unfold Qdiv. rewrite (IH (Datatypes.S m)). ring.
Qed.

(* The cos tail sum vanishes at B = 0 (successor-form index; the 2m
   index position with 0^0 = 1 stays outside this face). *)
Lemma d3p_cos_powtail_zero : forall m K : nat,
  d3p_cos_powtail 0 (Datatypes.S m) K == 0.
Proof.
  intros m K. revert m. induction K as [| K IH]; intros m.
  - reflexivity.
  - cbn [d3p_cos_powtail]. unfold d3p_cos_term.
    replace (2 * Datatypes.S m)%nat
      with (Datatypes.S (Datatypes.S (2 * m)))%nat
      by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_1_r; reflexivity).
    rewrite d3p_q_pow_0_succ.
    unfold Qdiv. rewrite (IH (Datatypes.S m)). ring.
Qed.

(* The sin tail sum is dominated by (4/3) times the first omitted
   term: sum_{i<K} t(m+i) <= (4/3)*t(m). *)
Lemma d3p_sin_powtail_quarter : forall (B : Q) (K m : nat),
  QleT' 0 B -> QleT' B (d3p_inject_nat m) ->
  QleT' (d3p_sin_powtail B m K) ((4 # 3)%Q * d3p_sin_term B m).
Proof.
  intros B K. induction K as [| K IH]; intros m H0B Hbm.
  - cbn [d3p_sin_powtail]. apply Qle_to_QleT'.
    apply Qmult_le_0_compat.
    + unfold Qle. cbn. apply Z.leb_le; reflexivity.
    + exact (d3p_sin_term_nonneg B m H0B).
  - assert (HbmS : QleT' B (d3p_inject_nat (Datatypes.S m))).
    { apply (qleT'_trans _ (d3p_inject_nat m)).
      - exact Hbm.
      - apply Qle_to_QleT'. apply d3p_inject_mono. apply Nat.le_succ_diag_r. }
    pose proof (IH (Datatypes.S m) H0B HbmS) as HIH.
    pose proof (d3p_sin_term_quarter B m H0B Hbm) as Hq.
    cbn [d3p_sin_powtail].
    apply (qleT'_trans
             (d3p_sin_term B m + d3p_sin_powtail B (Datatypes.S m) K)
             (d3p_sin_term B m
              + (4 # 3)%Q * (d3p_sin_term B m * (1 # 4)%Q))
             ((4 # 3)%Q * d3p_sin_term B m)).
    + apply qleT'_plus_compat.
      * apply qleT'_refl.
      * apply (qleT'_trans (d3p_sin_powtail B (Datatypes.S m) K)
                           ((4 # 3)%Q * d3p_sin_term B (Datatypes.S m))
                           ((4 # 3)%Q * (d3p_sin_term B m * (1 # 4)%Q))).
        -- exact HIH.
        -- apply Qle_to_QleT'.
           apply (piL_mult_le_l (d3p_sin_term B (Datatypes.S m))
                   (d3p_sin_term B m * (1 # 4)%Q) (4 # 3)%Q).
           ++ exact (QleT'_to_Qle _ _ Hq).
           ++ unfold Qle. cbn. apply Z.leb_le; reflexivity.
    + apply qeq_leT'. ring.
Qed.

(* The cos tail sum is dominated by (4/3) times the first omitted
   term (the mirror of the sin face). *)
Lemma d3p_cos_powtail_quarter : forall (B : Q) (K m : nat),
  QleT' 0 B -> QleT' B (d3p_inject_nat m) ->
  QleT' (d3p_cos_powtail B m K) ((4 # 3)%Q * d3p_cos_term B m).
Proof.
  intros B K. induction K as [| K IH]; intros m H0B Hbm.
  - cbn [d3p_cos_powtail]. apply Qle_to_QleT'.
    apply Qmult_le_0_compat.
    + unfold Qle. cbn. apply Z.leb_le; reflexivity.
    + exact (d3p_cos_term_nonneg B m H0B).
  - assert (HbmS : QleT' B (d3p_inject_nat (Datatypes.S m))).
    { apply (qleT'_trans _ (d3p_inject_nat m)).
      - exact Hbm.
      - apply Qle_to_QleT'. apply d3p_inject_mono. apply Nat.le_succ_diag_r. }
    pose proof (IH (Datatypes.S m) H0B HbmS) as HIH.
    pose proof (d3p_cos_term_quarter B m H0B Hbm) as Hq.
    cbn [d3p_cos_powtail].
    apply (qleT'_trans
             (d3p_cos_term B m + d3p_cos_powtail B (Datatypes.S m) K)
             (d3p_cos_term B m
              + (4 # 3)%Q * (d3p_cos_term B m * (1 # 4)%Q))
             ((4 # 3)%Q * d3p_cos_term B m)).
    + apply qleT'_plus_compat.
      * apply qleT'_refl.
      * apply (qleT'_trans (d3p_cos_powtail B (Datatypes.S m) K)
                           ((4 # 3)%Q * d3p_cos_term B (Datatypes.S m))
                           ((4 # 3)%Q * (d3p_cos_term B m * (1 # 4)%Q))).
        -- exact HIH.
        -- apply Qle_to_QleT'.
           apply (piL_mult_le_l (d3p_cos_term B (Datatypes.S m))
                   (d3p_cos_term B m * (1 # 4)%Q) (4 # 3)%Q).
           ++ exact (QleT'_to_Qle _ _ Hq).
           ++ unfold Qle. cbn. apply Z.leb_le; reflexivity.
    + apply qeq_leT'. ring.
Qed.

(* ========== Section 4. The half-power witness (explicit construction of d) ========== *)

(* x < x+1 (strict self-addition on [Q]). *)
Lemma d3p_qlt_plus_1 : forall x : Q, Qlt x (x + 1).
Proof.
  intros x.
  apply (leibsep_qlt_wd2 (x + 0) (x + 1) x (x + 1)).
  - apply Qplus_0_r.
  - apply Qeq_refl.
  - exact (proj2 (Qplus_lt_r 0 1 x) leibsep_qlt_1).
Qed.

(* The witness piece: 0 < c and 0 < eps imply the existence of a d
   with c*(1/4)^d < eps (d given by an explicit construction). *)
Lemma d3p_quarter_pow_lt : forall c eps : Q,
  Qlt 0 c -> Qlt 0 eps ->
  sigT (fun d : nat => Qlt (c * q_pow (1 # 4)%Q d) eps).
Proof.
  intros c eps Hc Hep.
  assert (Hne : ~ (eps == 0)).
  { apply q_neq_of_lt. exact Hep. }
  assert (Hr0 : Qlt 0 (c / eps)%Q).
  { unfold Qdiv. apply Qmult_lt_0_compat.
    - exact Hc.
    - apply Qinv_lt_0_compat. exact Hep. }
  assert (Hc0 : (0 <= Qceiling (c / eps)%Q)%Z).
  { apply Z.lt_le_incl. rewrite Zlt_Qlt.
    apply (Qlt_le_trans 0%Q (c / eps)%Q (QArith_base.inject_Z (Qceiling (c / eps)%Q))).
    - exact Hr0.
    - exact (Qle_ceiling (c / eps)%Q). }
  assert (Hr1 : Qlt (c / eps)%Q
                  (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
  { apply (Qle_lt_trans (c / eps)%Q
             (d3p_inject_nat (Z.to_nat (Qceiling (c / eps)%Q)))
             (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
    - apply (leibsep_qle_wd2 (c / eps)%Q (QArith_base.inject_Z (Qceiling (c / eps)%Q))
                             (c / eps)%Q
                             (d3p_inject_nat (Z.to_nat (Qceiling (c / eps)%Q)))).
      + apply Qeq_refl.
      + unfold d3p_inject_nat. rewrite Z2Nat.id by exact Hc0. apply Qeq_refl.
      + exact (Qle_ceiling (c / eps)%Q).
    - apply (leibsep_qlt_wd2
               (d3p_inject_nat (Z.to_nat (Qceiling (c / eps)%Q)))
               (d3p_inject_nat (Z.to_nat (Qceiling (c / eps)%Q)) + 1)
               (d3p_inject_nat (Z.to_nat (Qceiling (c / eps)%Q)))
               (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
      + apply Qeq_refl.
      + symmetry. apply d3p_inject_succ.
      + apply d3p_qlt_plus_1. }
  assert (Hce : (c / eps)%Q * eps == c).
  { unfold Qdiv.
    rewrite (Qmult_comm (c * Qinv eps) eps), Qmult_assoc, (Qmult_comm eps c).
    rewrite <- Qmult_assoc.
    rewrite (Qmult_inv_r eps) by exact Hne.
    rewrite Qmult_1_r. reflexivity. }
  assert (Hinv : forall d : nat, d3p_inject_nat (4 ^ d) * q_pow (1 # 4)%Q d == 1).
  { induction d as [| d IH].
    - reflexivity.
    - cbn [Nat.pow q_pow].
      rewrite (d3p_inject_mul 4 (4 ^ d)).
      assert (Hi4 : d3p_inject_nat 4 == 4) by reflexivity.
      rewrite Hi4.
      assert (Hsh : (4 * d3p_inject_nat (4 ^ d))
                    * ((1 # 4)%Q * q_pow (1 # 4)%Q d)
                    == ((1 # 4)%Q * 4)
                       * (d3p_inject_nat (4 ^ d) * q_pow (1 # 4)%Q d)) by ring.
      rewrite Hsh, IH. ring. }
  assert (Hpow2 : (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)) + 1
                   <= 4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)))%nat).
  { apply (Nat.le_trans (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)) + 1)
                        (2 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)))
                        (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)))).
    - apply d3p_nat_pow2_ge_succ.
    - replace (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)))%nat
        with (2 ^ (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))
                   + Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))%nat
        by (rewrite Nat.pow_add_r, <- Nat.pow_mul_l; reflexivity).
      apply Nat.pow_le_mono_r.
      + discriminate.
      + apply Nat.le_add_r. }
  assert (Hge : Qle (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1)
                     (d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
  { apply (leibsep_qle_wd2
             (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)) + 1))
             (d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
             (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1)
             (d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
    - rewrite (d3p_inject_add (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) 1).
      assert (Hi1 : d3p_inject_nat 1 == 1) by reflexivity.
      rewrite Hi1. reflexivity.
    - apply Qeq_refl.
    - apply d3p_inject_mono. exact Hpow2. }
  assert (HcM : Qlt c
                  (eps * d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
  { assert (Ht1 : Qlt ((c / eps)%Q * eps)
                      (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)))
                       * eps)).
    { apply (Qmult_lt_compat_r (c / eps)%Q
               (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)))) eps).
      - exact Hep.
      - exact Hr1. }
    assert (Ht2 : Qlt (eps * (c / eps)%Q)
                      (eps * d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
    { apply (leibsep_qlt_wd2 ((c / eps)%Q * eps)
                             (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)))
                              * eps)
                             (eps * (c / eps)%Q)
                             (eps * d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
      - apply Qmult_comm.
      - apply Qmult_comm.
      - exact Ht1. }
    assert (Hx1 : Qlt (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
                      (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1))
      by apply d3p_qlt_plus_1.
    assert (Ht3 : Qlt (eps * d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
                      (eps * (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1))).
    { apply (leibsep_qlt_wd2
               (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) * eps)
               ((d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1) * eps)
               (eps * d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
               (eps * (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1))).
      - apply Qmult_comm.
      - apply Qmult_comm.
      - exact (Qmult_lt_compat_r
                 (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
                 (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1) eps
                 Hep Hx1). }
    assert (Ht4 : Qle (eps * (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1))
                      (eps * d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
    { apply (piL_mult_le_l (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1)
              (d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)))) eps).
      - exact Hge.
      - exact (Qlt_le_weak 0%Q eps Hep). }
    assert (Hce2 : eps * (c / eps)%Q == c).
    { rewrite (Qmult_comm eps (c / eps)%Q). exact Hce. }
    apply (Qlt_trans c
             (eps * d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
             (eps * d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))).
    - exact (leibsep_qlt_wd2 (eps * (c / eps)%Q)
               (eps * d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
               c
               (eps * d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
               Hce2 (Qeq_refl _) Ht2).
    - exact (Qlt_le_trans
               (eps * d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
               (eps * (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))) + 1))
               (eps * d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
               Ht3 Ht4). }
  exists (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))).
  pose proof (Qmult_lt_compat_r c
                (eps * d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
                (q_pow (1 # 4)%Q (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
                (d3p_q_pow_pos (1 # 4)%Q _
                   (Qlt_to_QltT _ _ leibsep_qlt_half))
                HcM) as Hlt.
  apply (leibsep_qlt_wd2
           (c * q_pow (1 # 4)%Q (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
           ((eps * d3p_inject_nat (4 ^ Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
            * q_pow (1 # 4)%Q (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
           (c * q_pow (1 # 4)%Q (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q))))
           eps).
  - apply Qeq_refl.
  - rewrite <- Qmult_assoc, (Hinv (Datatypes.S (Z.to_nat (Qceiling (c / eps)%Q)))),
      Qmult_1_r. reflexivity.
  - exact Hlt.
Qed.

(* ========== Section 5. The uniform Cauchy face of the partial sums (the decay consumer) ========== *)

(* The defining step equation of the partial sums (sin/cos). *)
Lemma d3p_sin_partial_step : forall (n : nat) (x : Q),
  sin_partial (Datatypes.S n) x == sin_partial n x + sin_term (Datatypes.S n) x.
Proof. reflexivity. Qed.

Lemma d3p_cos_partial_step : forall (n : nat) (x : Q),
  cos_partial (Datatypes.S n) x == cos_partial n x + cos_term (Datatypes.S n) x.
Proof. reflexivity. Qed.

(* k = (k-j)+j (for j <= k; used in the tail-difference index conversion). *)
Lemma d3p_sub_add_eq : forall j k : nat, (j <= k)%nat ->
  (k = (k - j) + j)%nat.
Proof.
  intros j k Hjk. induction k as [| k IH].
  - assert (Hj : j = 0%nat)
      by (apply Nat.le_antisymm; [exact Hjk | apply Nat.le_0_l]).
    subst j. reflexivity.
  - destruct (Nat.eq_dec j (Datatypes.S k)) as [Heq | Hne].
    + subst j. rewrite Nat.sub_diag. reflexivity.
    + assert (Hjk' : (j <= k)%nat).
      { destruct (Nat.leb j k) eqn:E;
          [apply Nat.leb_le in E
          | apply Nat.leb_gt in E;
            exfalso; apply Hne; apply Nat.le_antisymm;
            [exact Hjk | exact E]].
        exact E. }
      replace (Datatypes.S k - j)%nat with (Datatypes.S (k - j))%nat
        by (symmetry; apply Nat.sub_succ_l; exact Hjk').
      rewrite Nat.add_succ_l. f_equal. exact (IH Hjk').
Qed.

(* The sin partial-sum tail-difference bound: |x| <= B implies
   |S_k - S_j| <= the tail sum of the k-j terms starting at S j. *)
Lemma d3p_sin_partial_tail_abs : forall (B : Q) (d j : nat) (x : Q),
  QleT' (Qabs x) B ->
  QleT' (Qabs (sin_partial (j + d) x - sin_partial j x))
        (d3p_sin_powtail B (Datatypes.S j) d).
Proof.
  intros B d. induction d as [| d IH]; intros j x Hx.
  - replace (j + 0)%nat with j by (symmetry; apply Nat.add_0_r).
    cbn [d3p_sin_powtail].
    assert (Hzz : sin_partial j x - sin_partial j x == 0) by ring.
    apply (piL_leT'_eq_intro_l _ _ _ (Qabs_wd _ _ Hzz)).
    apply qeq_leT'. reflexivity.
  - replace (j + Datatypes.S d)%nat with (Datatypes.S j + d)%nat
      by exact (eq_trans (Nat.add_succ_l j d) (plus_n_Sm j d)).
    assert (Hsplit : sin_partial (Datatypes.S j + d) x - sin_partial j x
                     == (sin_partial (Datatypes.S j + d) x
                         - sin_partial (Datatypes.S j) x)
                        + sin_term (Datatypes.S j) x).
    { rewrite (d3p_sin_partial_step j x). ring. }
    apply (piL_leT'_eq_intro_l _ _ _ (Qabs_wd _ _ Hsplit)).
    apply (qleT'_trans
             (Qabs ((sin_partial (Datatypes.S j + d) x
                     - sin_partial (Datatypes.S j) x)
                    + sin_term (Datatypes.S j) x))
             (d3p_sin_powtail B (Datatypes.S (Datatypes.S j)) d
              + d3p_sin_term B (Datatypes.S j))
             (d3p_sin_powtail B (Datatypes.S j) (Datatypes.S d))).
    + apply piL_abs2_plus_le.
      * exact (IH (Datatypes.S j) x Hx).
      * exact (piL_sin_term_abs_bound (Datatypes.S j) x B Hx).
    + apply qeq_leT'. cbn [d3p_sin_powtail]. ring.
Qed.

(* The cos partial-sum tail-difference bound. *)
Lemma d3p_cos_partial_tail_abs : forall (B : Q) (d j : nat) (x : Q),
  QleT' (Qabs x) B ->
  QleT' (Qabs (cos_partial (j + d) x - cos_partial j x))
        (d3p_cos_powtail B (Datatypes.S j) d).
Proof.
  intros B d. induction d as [| d IH]; intros j x Hx.
  - replace (j + 0)%nat with j by (symmetry; apply Nat.add_0_r).
    cbn [d3p_cos_powtail].
    assert (Hzz : cos_partial j x - cos_partial j x == 0) by ring.
    apply (piL_leT'_eq_intro_l _ _ _ (Qabs_wd _ _ Hzz)).
    apply qeq_leT'. reflexivity.
  - replace (j + Datatypes.S d)%nat with (Datatypes.S j + d)%nat
      by exact (eq_trans (Nat.add_succ_l j d) (plus_n_Sm j d)).
    assert (Hsplit : cos_partial (Datatypes.S j + d) x - cos_partial j x
                     == (cos_partial (Datatypes.S j + d) x
                         - cos_partial (Datatypes.S j) x)
                        + cos_term (Datatypes.S j) x).
    { rewrite (d3p_cos_partial_step j x). ring. }
    apply (piL_leT'_eq_intro_l _ _ _ (Qabs_wd _ _ Hsplit)).
    apply (qleT'_trans
             (Qabs ((cos_partial (Datatypes.S j + d) x
                     - cos_partial (Datatypes.S j) x)
                    + cos_term (Datatypes.S j) x))
             (d3p_cos_powtail B (Datatypes.S (Datatypes.S j)) d
              + d3p_cos_term B (Datatypes.S j))
             (d3p_cos_powtail B (Datatypes.S j) (Datatypes.S d))).
    + apply piL_abs2_plus_le.
      * exact (IH (Datatypes.S j) x Hx).
      * exact (piL_cos_term_abs_bound (Datatypes.S j) x B Hx).
    + apply qeq_leT'. cbn [d3p_cos_powtail]. ring.
Qed.

(* Monotonicity of the absolute-value summator (B >= 0; used for the uniform partial-sum bound). *)
Lemma d3p_abssum_mono : forall (B : Q) (p q : nat),
  QleT' 0 B -> (p <= q)%nat ->
  Qle (leibsep_abssum B p) (leibsep_abssum B q).
Proof.
  intros B p q H0B Hpq. induction q as [| q IH].
  - assert (Hp : p = 0%nat)
      by (apply Nat.le_antisymm; [exact Hpq | apply Nat.le_0_l]).
    subst p. apply Qle_refl.
  - destruct (Nat.eq_dec p (Datatypes.S q)) as [Heq | Hne].
    + subst p. apply Qle_refl.
    + assert (Hpq' : (p <= q)%nat).
      { destruct (Nat.leb p q) eqn:E;
          [apply Nat.leb_le in E
          | apply Nat.leb_gt in E;
            exfalso; apply Hne; apply Nat.le_antisymm;
            [exact Hpq | exact E]].
        exact E. }
      apply (Qle_trans _ (leibsep_abssum B q)).
      * exact (IH Hpq').
      * unfold leibsep_abssum.
        replace (2 * Datatypes.S q)%nat
          with (Datatypes.S (Datatypes.S (2 * q)))%nat
          by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_1_r; reflexivity).
        unfold d3p_cos_term. unfold Qdiv.
        apply Qle_plus_nonneg_r.
        apply Qmult_le_0_compat.
        -- apply q_pow_nonneg. exact (QleT'_to_Qle _ _ H0B).
        -- apply Qinv_le_0_compat. apply (Qlt_le_weak 0%Q _).
           exact (q_fact_pos (Datatypes.S (Datatypes.S (2 * q)))%nat).
Qed.

Lemma d3p_abssum_cos_mono : forall (B : Q) (p q : nat),
  QleT' 0 B -> (p <= q)%nat ->
  Qle (leibsep_abssum_cos B p) (leibsep_abssum_cos B q).
Proof.
  intros B p q H0B Hpq. induction q as [| q IH].
  - assert (Hp : p = 0%nat)
      by (apply Nat.le_antisymm; [exact Hpq | apply Nat.le_0_l]).
    subst p. apply Qle_refl.
  - destruct (Nat.eq_dec p (Datatypes.S q)) as [Heq | Hne].
    + subst p. apply Qle_refl.
    + assert (Hpq' : (p <= q)%nat).
      { destruct (Nat.leb p q) eqn:E;
          [apply Nat.leb_le in E
          | apply Nat.leb_gt in E;
            exfalso; apply Hne; apply Nat.le_antisymm;
            [exact Hpq | exact E]].
        exact E. }
      apply (Qle_trans _ (leibsep_abssum_cos B q)).
      * exact (IH Hpq').
      * unfold leibsep_abssum_cos.
        unfold d3p_sin_term. unfold Qdiv.
        apply Qle_plus_nonneg_r.
        apply Qmult_le_0_compat.
        -- apply q_pow_nonneg. exact (QleT'_to_Qle _ _ H0B).
        -- apply Qinv_le_0_compat. apply (Qlt_le_weak 0%Q _).
           exact (q_fact_pos (Datatypes.S (2 * q))%nat).
Qed.

(* Exponential decay from the first omitted term: n1 <= j implies
   t(S j) <= t(S n1)*(1/4)^(j-n1). *)
Lemma d3p_sin_term_dec : forall (B : Q) (r n1 j : nat),
  QleT' 0 B -> QleT' B (d3p_inject_nat n1) -> (n1 <= j)%nat ->
  (j - n1 <= r)%nat ->
  QleT' (d3p_sin_term B (Datatypes.S j))
        (d3p_sin_term B (Datatypes.S n1) * q_pow (1 # 4)%Q (j - n1)).
Proof.
  intros B r. induction r as [| r IH]; intros n1 j H0B Hbn Hnj Hr.
  - assert (Hj : j = n1).
    { assert (Hja : (j = (j - n1) + n1)%nat) by exact (d3p_sub_add_eq n1 j Hnj).
      assert (Hs : (j - n1 = 0)%nat)
        by (apply Nat.le_antisymm; [exact Hr | apply Nat.le_0_l]).
      rewrite Hs, Nat.add_0_l in Hja. exact Hja. }
    subst j. replace (n1 - n1)%nat with 0%nat by (symmetry; apply Nat.sub_diag).
    cbn [q_pow]. apply qeq_leT'. ring.
  - destruct (Nat.eq_dec (j - n1) 0) as [Hz | Hnz].
    + assert (Hj : j = n1).
      { assert (Hja : (j = (j - n1) + n1)%nat) by exact (d3p_sub_add_eq n1 j Hnj).
        rewrite Hz, Nat.add_0_l in Hja. exact Hja. }
      subst j. replace (n1 - n1)%nat with 0%nat by (symmetry; apply Nat.sub_diag).
      cbn [q_pow]. apply qeq_leT'. ring.
    + destruct (j - n1)%nat as [| rr] eqn:E.
      * exfalso. apply Hnz. reflexivity.
      * destruct j as [| j'] eqn: Ej.
        -- exfalso. apply Hnz. discriminate.
        -- assert (Hj' : (j' - n1 = rr)%nat).
           { destruct (Nat.le_gt_cases n1 j') as [Hle | Hgt].
             - rewrite (Nat.sub_succ_l n1 j' Hle) in E.
               injection E. intro H. exact H.
             - assert (Hn1 : n1 = Datatypes.S j')
                 by (apply Nat.le_antisymm; [exact Hnj | exact Hgt]).
               rewrite Hn1 in E. rewrite Nat.sub_diag in E.
               discriminate E. }
           assert (Hr' : (j' - n1 <= r)%nat).
           { rewrite Hj'. apply (proj2 (Nat.succ_le_mono rr r)). exact Hr. }
           assert (Hnj' : (n1 <= j')%nat).
           { destruct (Nat.le_gt_cases n1 j') as [H | Hc].
             - exact H.
             - exfalso. apply Hnz.
               assert (Heq : n1 = Datatypes.S j')
                 by (apply Nat.le_antisymm; [exact Hnj | exact Hc]).
               rewrite Heq in E. rewrite Nat.sub_diag in E.
               symmetry. exact E. }
           assert (Hbj' : QleT' B (d3p_inject_nat j')).
           { apply (qleT'_trans _ (d3p_inject_nat n1)).
             - exact Hbn.
             - apply Qle_to_QleT'. apply d3p_inject_mono. exact Hnj'. }
           assert (HbmS : QleT' B (d3p_inject_nat (Datatypes.S j'))).
           { apply (qleT'_trans _ (d3p_inject_nat j')).
             - exact Hbj'.
             - apply Qle_to_QleT'. apply d3p_inject_mono.
               apply Nat.le_succ_diag_r. }
           pose proof (IH n1 j' H0B Hbn Hnj' Hr') as HIH'.
           pose proof (d3p_sin_term_quarter B (Datatypes.S j') H0B HbmS) as Hq.
           replace (Datatypes.S j' - n1)%nat with (Datatypes.S (j' - n1))%nat
             by (symmetry; apply Nat.sub_succ_l; exact Hnj').
           rewrite <- Hj'.
           apply (qleT'_trans
                    (d3p_sin_term B (Datatypes.S (Datatypes.S j')))
                    (d3p_sin_term B (Datatypes.S j') * (1 # 4)%Q)
                    (d3p_sin_term B (Datatypes.S n1)
                     * q_pow (1 # 4)%Q (Datatypes.S (j' - n1)))).
           ++ exact Hq.
           ++ apply (piL_leT'_eq_intro_r (d3p_sin_term B (Datatypes.S n1)
                                            * ((1 # 4)%Q * q_pow (1 # 4)%Q (j' - n1)))
                                          (d3p_sin_term B (Datatypes.S n1)
                                           * q_pow (1 # 4)%Q (Datatypes.S (j' - n1)))
                                          (d3p_sin_term B (Datatypes.S j') * (1 # 4)%Q)).
              ** cbn [q_pow]. ring.
              ** apply Qle_to_QleT'.
                 apply (leibsep_qle_wd2 (d3p_sin_term B (Datatypes.S j') * (1 # 4)%Q)
                          ((d3p_sin_term B (Datatypes.S n1)
                            * q_pow (1 # 4)%Q (j' - n1)) * (1 # 4)%Q)
                          (d3p_sin_term B (Datatypes.S j') * (1 # 4)%Q)
                          (d3p_sin_term B (Datatypes.S n1)
                           * ((1 # 4)%Q * q_pow (1 # 4)%Q (j' - n1)))).
                 --- apply Qeq_refl.
                 --- ring.
                 --- apply (Qmult_le_compat_r (d3p_sin_term B (Datatypes.S j'))
                              (d3p_sin_term B (Datatypes.S n1)
                               * q_pow (1 # 4)%Q (j' - n1)) (1 # 4)%Q).
                     +++ exact (QleT'_to_Qle _ _ HIH').
                     +++ unfold Qle. cbn. apply Z.leb_le; reflexivity.
Qed.

(* ========== Section 6. The uniform Cauchy master face of the sin partial sums (the decay donor) ========== *)

(* The sin face: uniformly small for every x with |x| <= B and every
   deep difference -- the Taylor-leg donor of the two-index
   synthesis. *)
Lemma d3p_sin_partial_cauchy : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun M : nat => forall (j k : nat) (x : Q),
          (M <= j)%nat -> (j <= k)%nat -> QleT' (Qabs x) B ->
          QltT (Qabs (sin_partial k x - sin_partial j x)) eps).
Proof.
  intros B eps H0B Heps.
  assert (Hep0 : Qlt 0 eps) by exact (QltT_to_Qlt _ _ Heps).
  destruct (Qeq_dec B 0) as [Hz | Hnz].
  - exists 0%nat.
    intros j k x Hmj Hjk Hx.
    destruct (k - j)%nat as [| d] eqn:Ed.
    + assert (Hkj : k = j).
      { assert (Hka : (k = (k - j) + j)%nat) by exact (d3p_sub_add_eq j k Hjk).
        rewrite Ed, Nat.add_0_l in Hka. exact Hka. }
      subst k.
      assert (Hzz : sin_partial j x - sin_partial j x == 0) by ring.
      apply Qlt_to_QltT.
      exact (leibsep_qlt_wd2 0%Q eps
               (Qabs (sin_partial j x - sin_partial j x)) eps (eq_sym (Qabs_wd _ _ Hzz)) (Qeq_refl eps) Hep0).
    + assert (Hkj : (k = j + Datatypes.S d)%nat).
      { assert (Hka : (k = (k - j) + j)%nat) by exact (d3p_sub_add_eq j k Hjk).
        rewrite Ed, (Nat.add_comm (Datatypes.S d) j) in Hka. exact Hka. }
      subst k.
      assert (Hx0 : QleT' (Qabs x) 0)
        by (apply (qleT'_trans _ B); [exact Hx | apply qeq_leT'; exact Hz]).
      pose proof (d3p_sin_partial_tail_abs 0 (Datatypes.S d) j x Hx0) as Hta.
      assert (Hta0 : QleT' (Qabs (sin_partial (j + Datatypes.S d) x
                                 - sin_partial j x)) 0%Q).
      { apply (piL_leT'_eq_intro_r
                 (d3p_sin_powtail 0%Q (Datatypes.S j) (Datatypes.S d)) 0%Q
                 (Qabs (sin_partial (j + Datatypes.S d) x - sin_partial j x))).
        - exact (d3p_sin_powtail_zero (Datatypes.S j) (Datatypes.S d)).
        - exact Hta. }
      assert (Hz2 : Qabs (sin_partial (j + Datatypes.S d) x
                          - sin_partial j x) == 0).
      { apply (Qle_antisym _ 0).
        - exact (QleT'_to_Qle _ _ Hta0).
        - apply Qabs_nonneg. }
      apply Qlt_to_QltT.
      exact (leibsep_qlt_wd2
               0%Q eps
               (Qabs (sin_partial (j + Datatypes.S d) x - sin_partial j x)) eps (eq_sym Hz2) (Qeq_refl eps) Hep0).
  - assert (HBpos : Qlt 0 B).
    { destruct (Qlt_le_dec 0 B) as [Hp | Hn].
      - exact Hp.
      - exfalso. apply Hnz. apply (Qle_antisym B 0).
        + exact Hn.
        + exact (QleT'_to_Qle _ _ H0B). }
    assert (Hbn : QleT' B (d3p_inject_nat (Z.to_nat (Qceiling B)))).
    { apply d3p_inject_ceiling_ge. exact (QleT'_to_Qle _ _ H0B). }
    assert (Hcpos : Qlt 0 ((4 # 3)%Q
                           * d3p_sin_term B
                             (Datatypes.S (Z.to_nat (Qceiling B))))).
    { apply Qmult_lt_0_compat.
      - exact leibsep_qlt_half.
      - exact (d3p_sin_term_pos B (Datatypes.S (Z.to_nat (Qceiling B))) HBpos). }
    destruct (d3p_quarter_pow_lt ((4 # 3)%Q * d3p_sin_term B
                                    (Datatypes.S (Z.to_nat (Qceiling B))))
                eps Hcpos Hep0) as [d0 Hwit].
    exists (Z.to_nat (Qceiling B) + d0)%nat.
    intros j k x Hmj Hjk Hx.
    destruct (k - j)%nat as [| d] eqn:Ed.
    + assert (Hkj : k = j).
      { assert (Hka : (k = (k - j) + j)%nat) by exact (d3p_sub_add_eq j k Hjk).
        rewrite Ed, Nat.add_0_l in Hka. exact Hka. }
      subst k.
      assert (Hzz : sin_partial j x - sin_partial j x == 0) by ring.
      apply Qlt_to_QltT.
      exact (leibsep_qlt_wd2 0%Q eps
               (Qabs (sin_partial j x - sin_partial j x)) eps (eq_sym (Qabs_wd _ _ Hzz)) (Qeq_refl eps) Hep0).
    + assert (Hkj : (k = j + Datatypes.S d)%nat).
      { assert (Hka : (k = (k - j) + j)%nat) by exact (d3p_sub_add_eq j k Hjk).
        rewrite Ed, (Nat.add_comm (Datatypes.S d) j) in Hka. exact Hka. }
      subst k.
      assert (Hjn : (Z.to_nat (Qceiling B) <= j)%nat).
      { apply (Nat.le_trans (Z.to_nat (Qceiling B))
                            (Z.to_nat (Qceiling B) + d0) j).
        - apply Nat.le_add_r.
        - exact Hmj. }
      assert (Hbm : QleT' B (d3p_inject_nat j)).
      { apply (qleT'_trans _ (d3p_inject_nat (Z.to_nat (Qceiling B)))).
        - exact Hbn.
        - apply Qle_to_QleT'. apply d3p_inject_mono. exact Hjn. }
      pose proof (d3p_sin_partial_tail_abs B (Datatypes.S d) j x Hx) as Hta.
      assert (Hq1 : QleT' B (d3p_inject_nat (Datatypes.S j))).
      { apply (qleT'_trans _ (d3p_inject_nat j)).
        - exact Hbm.
        - apply Qle_to_QleT'. apply d3p_inject_mono. apply Nat.le_succ_diag_r. }
      pose proof (d3p_sin_powtail_quarter B (Datatypes.S d) (Datatypes.S j) H0B Hq1) as Hpq.
      pose proof (d3p_sin_term_dec B (j - Z.to_nat (Qceiling B))
                    (Z.to_nat (Qceiling B)) j H0B Hbn Hjn
                    (Nat.le_refl (j - Z.to_nat (Qceiling B)))) as Hdec.
      assert (Hdge : (d0 <= j - Z.to_nat (Qceiling B))%nat).
      { assert (Hja : (j = (j - Z.to_nat (Qceiling B))
                         + Z.to_nat (Qceiling B))%nat)
          by exact (d3p_sub_add_eq (Z.to_nat (Qceiling B)) j Hjn).
        apply (proj2 (Nat.add_le_mono_r d0
                        (j - Z.to_nat (Qceiling B))
                        (Z.to_nat (Qceiling B)))).
        rewrite <- Hja, <- (Nat.add_comm (Z.to_nat (Qceiling B)) d0).
        exact Hmj. }
      pose proof (d3p_q_pow_quarter_antitone d0 (j - Z.to_nat (Qceiling B))
                    Hdge) as Hanti.
      assert (Hsn0pos : Qlt 0 (d3p_sin_term B
                                  (Datatypes.S (Z.to_nat (Qceiling B)))))
        by exact (d3p_sin_term_pos B (Datatypes.S (Z.to_nat (Qceiling B))) HBpos).
      pose proof (Qmult_le_compat_r (d3p_sin_term B (Datatypes.S j))
                    (d3p_sin_term B (Datatypes.S (Z.to_nat (Qceiling B)))
                     * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))
                    (4 # 3)%Q
                    (QleT'_to_Qle _ _ Hdec)
                    (QleT'_to_Qle _ _ piL_qle_0_two)) as Hsc.
      assert (Hstep1 : Qle (Qabs (sin_partial (j + Datatypes.S d) x
                                  - sin_partial j x))
                           ((4 # 3)%Q * d3p_sin_term B (Datatypes.S j))).
      { apply (Qle_trans (Qabs (sin_partial (j + Datatypes.S d) x
                                   - sin_partial j x))
                 (d3p_sin_powtail B (Datatypes.S j) (Datatypes.S d))).
        - exact (QleT'_to_Qle _ _ Hta).
        - exact (QleT'_to_Qle _ _ Hpq). }
      assert (Hstep2 : Qle ((4 # 3)%Q * d3p_sin_term B (Datatypes.S j))
                         (((4 # 3)%Q * d3p_sin_term B
                            (Datatypes.S (Z.to_nat (Qceiling B))))
                          * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))).
      { apply (leibsep_qle_wd2
                 (d3p_sin_term B (Datatypes.S j) * (4 # 3)%Q)
                 ((d3p_sin_term B (Datatypes.S (Z.to_nat (Qceiling B)))
                   * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B))) * (4 # 3)%Q)
                 ((4 # 3)%Q * d3p_sin_term B (Datatypes.S j))
                 (((4 # 3)%Q * d3p_sin_term B
                    (Datatypes.S (Z.to_nat (Qceiling B))))
                  * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))).
        - ring.
        - ring.
        - exact Hsc. }
      assert (Hstep3 : Qle (((4 # 3)%Q * d3p_sin_term B
                              (Datatypes.S (Z.to_nat (Qceiling B))))
                             * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))
                          (((4 # 3)%Q * d3p_sin_term B
                             (Datatypes.S (Z.to_nat (Qceiling B))))
                           * q_pow (1 # 4)%Q d0)).
      { apply (piL_mult_le_l (q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))
                 (q_pow (1 # 4)%Q d0)
                 ((4 # 3)%Q * d3p_sin_term B (Datatypes.S (Z.to_nat (Qceiling B))))).
        - exact Hanti.
        - exact (Qlt_le_weak 0%Q _ Hcpos). }
      apply Qlt_to_QltT.
      apply (Qle_lt_trans (Qabs (sin_partial (j + Datatypes.S d) x
                                 - sin_partial j x))
               (((4 # 3)%Q * d3p_sin_term B
                  (Datatypes.S (Z.to_nat (Qceiling B))))
                * q_pow (1 # 4)%Q d0)).
      * apply (Qle_trans _ (((4 # 3)%Q * d3p_sin_term B
                              (Datatypes.S (Z.to_nat (Qceiling B))))
                             * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))).
        -- apply (Qle_trans _ ((4 # 3)%Q * d3p_sin_term B (Datatypes.S j))).
           ++ exact Hstep1.
           ++ exact Hstep2.
        -- exact Hstep3.
      * exact Hwit.
Qed.

(* The cos face: the mirror image (the cos tail-sum donor). *)
Lemma d3p_cos_partial_cauchy : forall (B eps : Q),
  QleT' 0 B -> QltT 0 eps ->
  sigT (fun M : nat => forall (j k : nat) (x : Q),
          (M <= j)%nat -> (j <= k)%nat -> QleT' (Qabs x) B ->
          QltT (Qabs (cos_partial k x - cos_partial j x)) eps).
Proof.
  intros B eps H0B Heps.
  assert (Hep0 : Qlt 0 eps) by exact (QltT_to_Qlt _ _ Heps).
  destruct (Qeq_dec B 0) as [Hz | Hnz].
  - exists 0%nat.
    intros j k x Hmj Hjk Hx.
    destruct (k - j)%nat as [| d] eqn:Ed.
    + assert (Hkj : k = j).
      { assert (Hka : (k = (k - j) + j)%nat) by exact (d3p_sub_add_eq j k Hjk).
        rewrite Ed, Nat.add_0_l in Hka. exact Hka. }
      subst k.
      assert (Hzz : cos_partial j x - cos_partial j x == 0) by ring.
      apply Qlt_to_QltT.
      exact (leibsep_qlt_wd2 0%Q eps
               (Qabs (cos_partial j x - cos_partial j x)) eps (eq_sym (Qabs_wd _ _ Hzz)) (Qeq_refl eps) Hep0).
    + assert (Hkj : (k = j + Datatypes.S d)%nat).
      { assert (Hka : (k = (k - j) + j)%nat) by exact (d3p_sub_add_eq j k Hjk).
        rewrite Ed, (Nat.add_comm (Datatypes.S d) j) in Hka. exact Hka. }
      subst k.
      assert (Hx0 : QleT' (Qabs x) 0)
        by (apply (qleT'_trans _ B); [exact Hx | apply qeq_leT'; exact Hz]).
      pose proof (d3p_cos_partial_tail_abs 0 (Datatypes.S d) j x Hx0) as Hta.
      assert (Hta0 : QleT' (Qabs (cos_partial (j + Datatypes.S d) x
                                 - cos_partial j x)) 0%Q).
      { apply (piL_leT'_eq_intro_r
                 (d3p_cos_powtail 0%Q (Datatypes.S j) (Datatypes.S d)) 0%Q
                 (Qabs (cos_partial (j + Datatypes.S d) x - cos_partial j x))).
        - exact (d3p_cos_powtail_zero j (Datatypes.S d)).
        - exact Hta. }
      assert (Hz2 : Qabs (cos_partial (j + Datatypes.S d) x
                          - cos_partial j x) == 0).
      { apply (Qle_antisym _ 0).
        - exact (QleT'_to_Qle _ _ Hta0).
        - apply Qabs_nonneg. }
      apply Qlt_to_QltT.
      exact (leibsep_qlt_wd2
               0%Q eps
               (Qabs (cos_partial (j + Datatypes.S d) x - cos_partial j x)) eps (eq_sym Hz2) (Qeq_refl eps) Hep0).
  - assert (HBpos : Qlt 0 B).
    { destruct (Qlt_le_dec 0 B) as [Hp | Hn].
      - exact Hp.
      - exfalso. apply Hnz. apply (Qle_antisym B 0).
        + exact Hn.
        + exact (QleT'_to_Qle _ _ H0B). }
    assert (Hbn : QleT' B (d3p_inject_nat (Z.to_nat (Qceiling B)))).
    { apply d3p_inject_ceiling_ge. exact (QleT'_to_Qle _ _ H0B). }
    assert (Hcpos : Qlt 0 ((4 # 3)%Q
                           * d3p_cos_term B
                             (Datatypes.S (Z.to_nat (Qceiling B))))).
    { apply Qmult_lt_0_compat.
      - exact leibsep_qlt_half.
      - exact (d3p_cos_term_pos B (Datatypes.S (Z.to_nat (Qceiling B))) HBpos). }
    destruct (d3p_quarter_pow_lt ((4 # 3)%Q * d3p_cos_term B
                                    (Datatypes.S (Z.to_nat (Qceiling B))))
                eps Hcpos Hep0) as [d0 Hwit].
    exists (Z.to_nat (Qceiling B) + d0)%nat.
    intros j k x Hmj Hjk Hx.
    destruct (k - j)%nat as [| d] eqn:Ed.
    + assert (Hkj : k = j).
      { assert (Hka : (k = (k - j) + j)%nat) by exact (d3p_sub_add_eq j k Hjk).
        rewrite Ed, Nat.add_0_l in Hka. exact Hka. }
      subst k.
      assert (Hzz : cos_partial j x - cos_partial j x == 0) by ring.
      apply Qlt_to_QltT.
      exact (leibsep_qlt_wd2 0%Q eps
               (Qabs (cos_partial j x - cos_partial j x)) eps (eq_sym (Qabs_wd _ _ Hzz)) (Qeq_refl eps) Hep0).
    + assert (Hkj : (k = j + Datatypes.S d)%nat).
      { assert (Hka : (k = (k - j) + j)%nat) by exact (d3p_sub_add_eq j k Hjk).
        rewrite Ed, (Nat.add_comm (Datatypes.S d) j) in Hka. exact Hka. }
      subst k.
      assert (Hjn : (Z.to_nat (Qceiling B) <= j)%nat).
      { apply (Nat.le_trans (Z.to_nat (Qceiling B))
                            (Z.to_nat (Qceiling B) + d0) j).
        - apply Nat.le_add_r.
        - exact Hmj. }
      assert (Hbm : QleT' B (d3p_inject_nat j)).
      { apply (qleT'_trans _ (d3p_inject_nat (Z.to_nat (Qceiling B)))).
        - exact Hbn.
        - apply Qle_to_QleT'. apply d3p_inject_mono. exact Hjn. }
      pose proof (d3p_cos_partial_tail_abs B (Datatypes.S d) j x Hx) as Hta.
      assert (Hq1 : QleT' B (d3p_inject_nat (Datatypes.S j))).
      { apply (qleT'_trans _ (d3p_inject_nat j)).
        - exact Hbm.
        - apply Qle_to_QleT'. apply d3p_inject_mono. apply Nat.le_succ_diag_r. }
      pose proof (d3p_cos_powtail_quarter B (Datatypes.S d) (Datatypes.S j) H0B Hq1) as Hpq.
      assert (Hdec0 : (Z.to_nat (Qceiling B) <= j)%nat) by exact Hjn.
      assert (Hdec' : QleT' (d3p_cos_term B (Datatypes.S j))
                        (d3p_cos_term B (Datatypes.S (Z.to_nat (Qceiling B)))
                         * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))).
      { pose proof (d3p_cos_term_iter B (j - Z.to_nat (Qceiling B))
                      (Datatypes.S (Z.to_nat (Qceiling B))) H0B
                      (qleT'_trans B (d3p_inject_nat (Z.to_nat (Qceiling B)))
                         (d3p_inject_nat (Datatypes.S (Z.to_nat (Qceiling B))))
                         Hbn
                         (Qle_to_QleT' _ _
                            (d3p_inject_mono (Z.to_nat (Qceiling B))
                               (Datatypes.S (Z.to_nat (Qceiling B)))
                               (Nat.le_succ_diag_r
                                  (Z.to_nat (Qceiling B))))))) as HI.
        replace (Datatypes.S (Z.to_nat (Qceiling B))
                 + (j - Z.to_nat (Qceiling B)))%nat
          with (Datatypes.S j)%nat in HI.
        - exact HI.
        - rewrite Nat.add_succ_l. f_equal. symmetry.
          rewrite (Nat.add_comm (Z.to_nat (Qceiling B))
                     (j - Z.to_nat (Qceiling B))).
          exact (eq_sym (d3p_sub_add_eq (Z.to_nat (Qceiling B)) j Hjn)). }
      assert (Hdge : (d0 <= j - Z.to_nat (Qceiling B))%nat).
      { assert (Hja : (j = (j - Z.to_nat (Qceiling B))
                         + Z.to_nat (Qceiling B))%nat)
          by exact (d3p_sub_add_eq (Z.to_nat (Qceiling B)) j Hjn).
        apply (proj2 (Nat.add_le_mono_r d0
                        (j - Z.to_nat (Qceiling B))
                        (Z.to_nat (Qceiling B)))).
        rewrite <- Hja, <- (Nat.add_comm (Z.to_nat (Qceiling B)) d0).
        exact Hmj. }
      pose proof (d3p_q_pow_quarter_antitone d0 (j - Z.to_nat (Qceiling B))
                    Hdge) as Hanti.
      assert (Hsn0pos : Qlt 0 (d3p_cos_term B
                                  (Datatypes.S (Z.to_nat (Qceiling B)))))
        by exact (d3p_cos_term_pos B (Datatypes.S (Z.to_nat (Qceiling B))) HBpos).
      pose proof (Qmult_le_compat_r (d3p_cos_term B (Datatypes.S j))
                    (d3p_cos_term B (Datatypes.S (Z.to_nat (Qceiling B)))
                     * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))
                    (4 # 3)%Q
                    (QleT'_to_Qle _ _ Hdec')
                    (QleT'_to_Qle _ _ piL_qle_0_two)) as Hsc.
      assert (Hstep1 : Qle (Qabs (cos_partial (j + Datatypes.S d) x
                                  - cos_partial j x))
                           ((4 # 3)%Q * d3p_cos_term B (Datatypes.S j))).
      { apply (Qle_trans (Qabs (cos_partial (j + Datatypes.S d) x
                                   - cos_partial j x))
                 (d3p_cos_powtail B (Datatypes.S j) (Datatypes.S d))).
        - exact (QleT'_to_Qle _ _ Hta).
        - exact (QleT'_to_Qle _ _ Hpq). }
      assert (Hstep2 : Qle ((4 # 3)%Q * d3p_cos_term B (Datatypes.S j))
                         (((4 # 3)%Q * d3p_cos_term B
                            (Datatypes.S (Z.to_nat (Qceiling B))))
                          * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))).
      { apply (leibsep_qle_wd2
                 (d3p_cos_term B (Datatypes.S j) * (4 # 3)%Q)
                 ((d3p_cos_term B (Datatypes.S (Z.to_nat (Qceiling B)))
                   * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B))) * (4 # 3)%Q)
                 ((4 # 3)%Q * d3p_cos_term B (Datatypes.S j))
                 (((4 # 3)%Q * d3p_cos_term B
                    (Datatypes.S (Z.to_nat (Qceiling B))))
                  * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))).
        - ring.
        - ring.
        - exact Hsc. }
      assert (Hstep3 : Qle (((4 # 3)%Q * d3p_cos_term B
                              (Datatypes.S (Z.to_nat (Qceiling B))))
                             * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))
                          (((4 # 3)%Q * d3p_cos_term B
                             (Datatypes.S (Z.to_nat (Qceiling B))))
                           * q_pow (1 # 4)%Q d0)).
      { apply (piL_mult_le_l (q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))
                 (q_pow (1 # 4)%Q d0)
                 ((4 # 3)%Q * d3p_cos_term B (Datatypes.S (Z.to_nat (Qceiling B))))).
        - exact Hanti.
        - exact (Qlt_le_weak 0%Q _ Hcpos). }
      apply Qlt_to_QltT.
      apply (Qle_lt_trans (Qabs (cos_partial (j + Datatypes.S d) x
                                 - cos_partial j x))
               (((4 # 3)%Q * d3p_cos_term B
                  (Datatypes.S (Z.to_nat (Qceiling B))))
                * q_pow (1 # 4)%Q d0)).
      * apply (Qle_trans _ (((4 # 3)%Q * d3p_cos_term B
                              (Datatypes.S (Z.to_nat (Qceiling B))))
                             * q_pow (1 # 4)%Q (j - Z.to_nat (Qceiling B)))).
        -- apply (Qle_trans _ ((4 # 3)%Q * d3p_cos_term B (Datatypes.S j))).
           ++ exact Hstep1.
           ++ exact Hstep2.
        -- exact Hstep3.
      * exact Hwit.
Qed.
(* ---- Merged segment 5: PiKernelSlack_D3_synth (md5 a0c2d506) ---- *)
(** * The double-index vanishing synthesis of the sine and cosine
      partial sums at the window points

    Mission.  This segment synthesizes the double-index vanishing of
    the sine and cosine partial sums at the window points ([lw0m_xL m]
    equals [lp_four * lp_odd m]) into two statements,
    [piL_sin_xL_vanish] and [piL_cos_xL_neg1_vanish].  The
    mathematical core is the pair of synthesis identities (checked
    exactly on numeric samples): [sin_partial m (4*u)] equals
    [2 * S(2*u) * C(2*u) - dres(2*u)], and [cos_partial m (4*u) + 1]
    equals [dcos(2*u) + 2 * (1 - S(2*u)^2) + dpit(2*u)], where [S] and
    [C] abbreviate [sin_partial m] and [cos_partial m], and [dres],
    [dcos] and [dpit] abbreviate [piL_sin_dres m], [piL_cos_dres m]
    and [piL_pyth_dres m], each at [2*u].  The double-index smallness
    reduces to three explicit seed slots (the half-window pair, the
    sine double-angle remainder, the cosine double-angle remainder)
    plus real glue: identity folding, trigonometric assembly, and the
    split of a strict-order budget.  The seed slots are explicit named
    premises at the [Set] level -- seed-slot premises (constructive
    [forall] assumptions carried by the statements themselves) --
    discharged by the closing sections of this file.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [Arith.PeanoNat]; [PiCompareT]; [PiKernelSlack] (the [Q]-level
    partial sums [sin_partial]/[cos_partial], the shore family, the
    reflected orders [QltT]/[QleT'], the [Set]-level product [And]);
    [PiLeibnizCReal] (the [lp]/[lw0m] family);
    [PiKernelSlack_D1_identity] (the double-angle identity layer);
    [PiKernelSlack_D2_remainder] (the remainder majorants);
    [PiKernelSlack_D25_reduction] (the absolute-value product
    bridges); [PiKernelSlack_D3_prereq] (the tail-sum machine of the
    prerequisite bundle).  The [Require] face imports no forbidden
    fragment: no external decision procedure.

    References.  This segment consumes the window-point face of
    [PiKernelSlack] ([sc_lp_pair_nonneg], [sc_lp_odd_chain],
    [sc_lp_odd_le_s6]); the [lp]/[lw0m] face of [PiLeibnizCReal]
    ([lp_odd], [lp_a], [lp_four], [lw0m_xL], [piL_qabs_le_nonneg],
    [piL_lp_a_S]); the identity layer of
    [PiKernelSlack_D1_identity] ([piL_sin_partial_congr],
    [piL_sin_partial_double_at], [piL_cos_partial_congr],
    [piL_cos_partial_double], [piL_pythag_partial], [piL_pyth_dres]);
    the majorant face of [PiKernelSlack_D2_remainder] ([piL_sin_dres],
    [piL_cos_dres], [piL_abs2_le], [piL_mult_le_l], [piL_qabs_two],
    [piL_qle_0_two], [piL_qle_0_four]); and the reduction bridges of
    [PiKernelSlack_D25_reduction] ([piLred_abs_mult],
    [piLred_qle_wd_r]).

    Constructivity.  Statements at the [Set] level: conclusions in
    [QltT], premises of the shapes [QltT]/[QleT']/[Qeq], and the seed
    slots as [Set]-level [forall] types -- seed-slot premises
    (constructive [forall] assumptions carried by the statements
    themselves; every statement stays closed under
    [Print Assumptions]).  Assumption-free and fully proved with no
    non-constructive principles; the order arithmetic runs along
    direct [QArith] lemma chains (no external decision procedure;
    [ring] only to reorganize [Qeq] sides).  The proofs are
    non-trivial: identity folding, trigonometric assembly, and a
    genuine two-branch budget split.

    Build.  [rocq c -native-compiler no -q -Q . ""
    PiKernelSlack_D3_synth.v] compiles cleanly (exit 0); the first
    eight bytes of the artifact are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

(* Context note.  In this file the prerequisite bundles consumed by this
   segment ([PiKernelSlack_D1_identity], [PiKernelSlack_D2_remainder],
   [PiKernelSlack_D25_reduction], [PiKernelSlack_D3_prereq]) are mounted
   inline at their separator lines earlier in the file rather than required
   as separate modules; the dependency list in the segment document below
   names them under those module names. *)


(* ========== Section 0. Uniform-bound glue at the window points ========== *)

(* The odd-subsequence partial sums are nonnegative:
   [lp_odd m] >= [lp_pair 0] >= 0. *)
Lemma piLd3_lp_odd_nonneg : forall m : nat, Qle 0 (lp_odd m).
Proof.
  intros m.
  pose proof (sc_lp_odd_chain 0 m (Nat.le_0_l m)) as Hc.
  pose proof (sc_lp_pair_nonneg 0) as Hp.
  exact (Qle_trans 0 (lp_odd 0) (lp_odd m) Hp Hc).
Qed.
(* A uniform absolute-value bound for the odd subsequence:
   |[lp_odd m]| <= S6 := [lp_odd 2 + lp_a 6]. *)
Lemma piLd3_u_abs_le_s6 : forall m : nat,
  QleT' (Qabs (lp_odd m)) (lp_odd 2 + lp_a 6)%Q.
Proof.
  intros m. apply Qle_to_QleT'. apply piL_qabs_le_nonneg.
  - exact (piLd3_lp_odd_nonneg m).
  - exact (sc_lp_odd_le_s6 m).
Qed.
(* [lp_a 6] = 1/13 is strictly positive (the donor leg for the strict
   positivity of S6). *)
Lemma piLd3_lp_a6_pos : Qlt 0 (lp_a 6).
Proof.
  rewrite (piL_lp_a_S 5).
  unfold Qlt. cbn. reflexivity.
Qed.
(* S6 := [lp_odd 2 + lp_a 6] is strictly positive. *)
Lemma piLd3_s6_pos : Qlt 0 (lp_odd 2 + lp_a 6)%Q.
Proof.
  apply (Qlt_le_trans 0 (lp_a 6) (lp_odd 2 + lp_a 6)%Q).
  - exact piLd3_lp_a6_pos.
  - apply (Qle_trans (lp_a 6) (0 + lp_a 6)%Q (lp_odd 2 + lp_a 6)%Q).
    + apply qeq_le. ring.
    + apply Qplus_le_compat.
      * exact (piLd3_lp_odd_nonneg 2).
      * apply Qle_refl.
Qed.
(* Adding a strictly positive term on the right preserves strictness on
   the [Qlt] side (a compatibility lemma of that shape is absent in
   stdlib 9.1; the iff form [Qplus_lt_r] is used instead). *)
Lemma piLd3_qlt_add_r : forall x y : Q, Qlt 0 y -> Qlt x (x + y)%Q.
Proof.
  intros x y Hy.
  apply (leibsep_qlt_wd2 (x + 0)%Q (x + y)%Q x (x + y)%Q).
  - ring.
  - apply Qeq_refl.
  - exact (proj2 (Qplus_lt_r 0 y x) Hy).
Qed.
(* Two strictly positive constants (the [QltT] instances for the
   premises of the seed slots). *)
Lemma piLd3_c16_pos : Qlt 0 (1 # 16)%Q.
Proof. unfold Qlt. cbn. reflexivity. Qed.

Lemma piLd3_c32_pos : Qlt 0 (1 # 32)%Q.
Proof. unfold Qlt. cbn. reflexivity. Qed.
(* ========== Section 1. The seed-slot types ========== *)
(* The three seed slots are explicit named premises at the [Set]       *)
(* level: seed-slot premises (constructive [forall] assumptions        *)
(* carried by the statements themselves; every statement of this block *)
(* stays closed under [Print Assumptions]).                            *)

(* The first seed slot, the half-window pair:
   |[C_k(2 * lp_odd m)]| -> 0 and |[S_k(2 * lp_odd m) - 1]| -> 0
   (double-index).  The analytic core is the identification of the
   Leibniz limit with the trigonometric zero.  No donor for this
   content exists in the companion pieces yet: the slot stands as an
   explicit named premise (a constructive [forall] assumption carried
   by the statements) and awaits the vertex-zero route together with
   the alternating-tail bound supply. *)
Definition piLd3_seed_halfwin : Set :=
  forall dt : Q, QltT 0 dt ->
    sigT (fun K : nat => forall k m : nat, (K <= k)%nat -> (K <= m)%nat ->
      And (QltT (Qabs (cos_partial k (2 * lp_odd m))) dt)
          (QltT (Qabs (sin_partial k (2 * lp_odd m) - (1 # 1)%Q)) dt)).
(* The second seed slot: the sine double-angle truncation remainder
   vanishes (uniformly in the depth index, uniformly on
   |[x]| <= [B]). *)
Definition piLd3_seed_dres : Set :=
  forall (B dt : Q), QltT 0 B -> QltT 0 dt ->
    sigT (fun j : nat => forall (k : nat) (x : Q), (j <= k)%nat ->
      QleT' (Qabs x) B -> QltT (Qabs (piL_sin_dres k x)) dt).
(* The third seed slot: the cosine double-angle truncation remainder
   vanishes (same shape). *)
Definition piLd3_seed_dcos : Set :=
  forall (B dt : Q), QltT 0 B -> QltT 0 dt ->
    sigT (fun j : nat => forall (k : nat) (x : Q), (j <= k)%nat ->
      QleT' (Qabs x) B -> QltT (Qabs (piL_cos_dres k x)) dt).
(* ========== Section 2. The window radius ========== *)
(* B := 2 * S6 bounds every half-window point [2 * lp_odd m].          *)

Definition piLd3_B : Q := (2 * (lp_odd 2 + lp_a 6))%Q.

Lemma piLd3_B_pos : QltT 0 piLd3_B.
Proof.
  apply Qlt_to_QltT. unfold piLd3_B.
  apply Qmult_lt_0_compat.
  - unfold Qlt. cbn. reflexivity.
  - exact piLd3_s6_pos.
Qed.

Lemma piLd3_abs_2u_le_B : forall m : nat, QleT' (Qabs (2 * lp_odd m)) piLd3_B.
Proof.
  intros m. unfold piLd3_B.
  exact (piL_abs2_le (lp_odd m) (lp_odd 2 + lp_a 6) (piLd3_u_abs_le_s6 m)).
Qed.
(* ========== Section 3. The synthesis identities ========== *)
(* (the double-angle identity layer folded at the window points)       *)

(* The sine side: [sin_partial m (4*u)] equals twice the product of the
   two partial sums at [2*u] minus the sine remainder
   [piL_sin_dres m (2*u)]. *)
Lemma piLd3_sin_xL_eq : forall (m : nat) (u : Q),
  sin_partial m (lp_four * u)%Q
  == (2 * sin_partial m (2 * u) * cos_partial m (2 * u)
      - piL_sin_dres m (2 * u))%Q.
Proof.
  intros m u.
  assert (H4 : (lp_four * u)%Q == (2 * (2 * u))%Q) by (unfold lp_four; ring).
  rewrite (piL_sin_partial_congr m (lp_four * u) (2 * (2 * u)) H4).
  apply (piL_sin_partial_double_at m (2 * u)).
Qed.
(* The cosine side: [cos_partial m (4*u) + 1] equals the cosine
   remainder plus [2 * (1 - S*S)] plus the Pythagorean remainder
   [piL_pyth_dres m (2*u)]; this shape carries the Pythagorean
   remainder with a plus sign, and agrees with the minus-sign shape
   through [piL_pythag_partial] and [ring]. *)
Lemma piLd3_cos_xL_plus1_eq : forall (m : nat) (u : Q),
  cos_partial m (lp_four * u)%Q + (1 # 1)%Q
  == (piL_cos_dres m (2 * u)
      + 2 * ((1 # 1)%Q - sin_partial m (2 * u) * sin_partial m (2 * u))
      + piL_pyth_dres m (2 * u))%Q.
Proof.
  intros m u.
  assert (H4 : (lp_four * u)%Q == (2 * (2 * u))%Q) by (unfold lp_four; ring).
  rewrite (piL_cos_partial_congr m (lp_four * u) (2 * (2 * u)) H4).
  rewrite (piL_cos_partial_double m (2 * u)).
  assert (Hs2 : (sin_partial m (2 * u) * sin_partial m (2 * u))%Q
                == ((1 # 1)%Q + piL_pyth_dres m (2 * u)
                    - cos_partial m (2 * u) * cos_partial m (2 * u))%Q).
  { apply (Qeq_trans _ ((sin_partial m (2 * u) * sin_partial m (2 * u)
                         + cos_partial m (2 * u) * cos_partial m (2 * u))
                        - cos_partial m (2 * u) * cos_partial m (2 * u))).
    - ring.
    - rewrite (piL_pythag_partial m (2 * u)). ring. }
  rewrite Hs2. ring.
Qed.
(* ========== Section 4. Assembly auxiliaries ========== *)
(* (the [S] bounds, the half-square bound, the Pythagorean-remainder   *)
(* bound, and two product bounds)                                      *)

(* |[S]| <= 1 + q (from the half-window pair |[S - 1]| < q; here [S]
   abbreviates [sin_partial m (2*u)]). *)
Lemma piLd3_abs_S_le : forall (m : nat) (u q : Q),
  Qle (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)) q ->
  Qle (Qabs (sin_partial m (2 * u))) ((1 # 1)%Q + q).
Proof.
  intros m u q H.
  assert (Hle : Qle (Qabs (sin_partial m (2 * u)))
                    (Qabs (sin_partial m (2 * u) - (1 # 1)%Q) + (1 # 1)%Q)).
  { apply (Qle_trans _ (Qabs ((sin_partial m (2 * u) - (1 # 1)%Q)
                              + (1 # 1)%Q))).
    - apply qeq_le. apply Qabs_wd. ring.
    - apply Qabs_triangle. }
  apply (Qle_trans _ (q + (1 # 1)%Q)).
  - apply (Qle_trans _ (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)
                        + (1 # 1)%Q)).
    + exact Hle.
    + apply Qplus_le_compat.
      * exact H.
      * apply Qle_refl.
  - apply qeq_le. ring.
Qed.
(* |[S + 1]| <= 2 + q (from the half-window pair |[S - 1]| < q; the
   [S + 1] leg of the Pythagorean-remainder bound). *)
Lemma piLd3_abs_Splus_le : forall (m : nat) (u q : Q),
  Qle (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)) q ->
  Qle (Qabs (sin_partial m (2 * u) + (1 # 1)%Q)) ((2 # 1)%Q + q).
Proof.
  intros m u q H.
  assert (Hle : Qle (Qabs (sin_partial m (2 * u) + (1 # 1)%Q))
                    (Qabs (sin_partial m (2 * u) - (1 # 1)%Q) + (2 # 1)%Q)).
  { apply (Qle_trans _ (Qabs ((sin_partial m (2 * u) - (1 # 1)%Q)
                              + (2 # 1)%Q))).
    - apply qeq_le. apply Qabs_wd. ring.
    - apply Qabs_triangle. }
  apply (Qle_trans _ (q + (2 # 1)%Q)).
  - apply (Qle_trans _ (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)
                        + (2 # 1)%Q)).
    + exact Hle.
    + apply Qplus_le_compat.
      * exact H.
      * apply Qle_refl.
  - apply qeq_le. ring.
Qed.
(* The half-square bound: |2*(1 - S*S)| <= 2*q*(2 + q) (through
   1 - S*S = -(S - 1)*(S + 1) and the [Qabs_opp] bridge). *)
Lemma piLd3_halfsq_bound : forall (m : nat) (u q : Q),
  QltT 0 q ->
  Qle (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)) q ->
  Qle (Qabs (2 * ((1 # 1)%Q - sin_partial m (2 * u) * sin_partial m (2 * u))))
      (2 * (q * ((2 # 1)%Q + q)))%Q.
Proof.
  intros m u q Hq0 HS.
  assert (Heq : Qabs (2 * ((1 # 1)%Q - sin_partial m (2 * u) * sin_partial m (2 * u)))
                == (2 # 1)%Q * (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)
                                * Qabs (sin_partial m (2 * u) + (1 # 1)%Q))).
  { rewrite (piLred_abs_mult 2
              ((1 # 1)%Q - sin_partial m (2 * u) * sin_partial m (2 * u))).
    rewrite piL_qabs_two.
    assert (H1s : Qabs ((1 # 1)%Q - sin_partial m (2 * u) * sin_partial m (2 * u))
                  == Qabs ((sin_partial m (2 * u) - (1 # 1)%Q)
                           * (sin_partial m (2 * u) + (1 # 1)%Q))).
    { apply (Qeq_trans _ (Qabs (- ((sin_partial m (2 * u) - (1 # 1)%Q)
                                   * (sin_partial m (2 * u) + (1 # 1)%Q))))).
      - apply Qabs_wd. ring.
      - exact (Qabs_opp ((sin_partial m (2 * u) - (1 # 1)%Q)
                         * (sin_partial m (2 * u) + (1 # 1)%Q))). }
    rewrite H1s.
    rewrite (piLred_abs_mult (sin_partial m (2 * u) - (1 # 1)%Q)
                             (sin_partial m (2 * u) + (1 # 1)%Q)).
    apply Qeq_refl. }
  apply (Qle_trans _ ((2 # 1)%Q * (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)
                                  * Qabs (sin_partial m (2 * u) + (1 # 1)%Q)))).
  - apply qeq_le. exact Heq.
  - apply (Qle_trans _ ((2 # 1)%Q * (q * ((2 # 1)%Q + q)))).
    + apply (piL_mult_le_l (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)
                            * Qabs (sin_partial m (2 * u) + (1 # 1)%Q))
                           (q * ((2 # 1)%Q + q)) (2 # 1)%Q).
      * apply (Qle_trans _ (q * Qabs (sin_partial m (2 * u) + (1 # 1)%Q))).
        -- apply Qmult_le_compat_r; [exact HS | apply Qabs_nonneg].
        -- apply (piL_mult_le_l (Qabs (sin_partial m (2 * u) + (1 # 1)%Q))
                                ((2 # 1)%Q + q) q).
           ++ exact (piLd3_abs_Splus_le m u q HS).
           ++ apply Qlt_le_weak. apply QltT_to_Qlt. exact Hq0.
      * exact (QleT'_to_Qle _ _ piL_qle_0_two).
    + apply qeq_le. ring.
Qed.
(* The Pythagorean-remainder bound: |[piL_pyth_dres m (2*u)]| <=
   q*(2 + q) + q*q (in the ring shape (S - 1)*(S + 1) + C*C; the
   Pythagorean remainder is controlled by the half-window pair). *)
Lemma piLd3_dpit_bound : forall (m : nat) (u q : Q),
  QltT 0 q ->
  Qle (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)) q ->
  Qle (Qabs (cos_partial m (2 * u))) q ->
  Qle (Qabs (piL_pyth_dres m (2 * u)))
      (q * ((2 # 1)%Q + q) + q * q)%Q.
Proof.
  intros m u q Hq0 HS HC.
  assert (Hpyth : piL_pyth_dres m (2 * u)
                  == ((sin_partial m (2 * u) - (1 # 1)%Q)
                      * (sin_partial m (2 * u) + (1 # 1)%Q)
                      + cos_partial m (2 * u) * cos_partial m (2 * u))%Q).
  { apply (Qeq_trans _ ((sin_partial m (2 * u) * sin_partial m (2 * u)
                         + cos_partial m (2 * u) * cos_partial m (2 * u)
                         - (1 # 1)%Q))).
    - rewrite (piL_pythag_partial m (2 * u)). ring.
    - ring. }
  apply (Qle_trans _ (Qabs ((sin_partial m (2 * u) - (1 # 1)%Q)
                            * (sin_partial m (2 * u) + (1 # 1)%Q)
                            + cos_partial m (2 * u) * cos_partial m (2 * u)))).
  - apply qeq_le. apply Qabs_wd. exact Hpyth.
  - apply (Qle_trans _ (Qabs ((sin_partial m (2 * u) - (1 # 1)%Q)
                              * (sin_partial m (2 * u) + (1 # 1)%Q))
                        + Qabs (cos_partial m (2 * u) * cos_partial m (2 * u)))).
    + apply Qabs_triangle.
    + apply (Qle_trans _ (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)
                          * Qabs (sin_partial m (2 * u) + (1 # 1)%Q)
                          + Qabs (cos_partial m (2 * u))
                          * Qabs (cos_partial m (2 * u)))).
      * apply Qplus_le_compat.
        -- apply qeq_le. exact (piLred_abs_mult (sin_partial m (2 * u) - (1 # 1)%Q)
                                 (sin_partial m (2 * u) + (1 # 1)%Q)).
        -- apply qeq_le. exact (piLred_abs_mult (cos_partial m (2 * u))
                                 (cos_partial m (2 * u))).
      * apply (Qle_trans _ (q * Qabs (sin_partial m (2 * u) + (1 # 1)%Q)
                            + q * Qabs (cos_partial m (2 * u)))).
        -- apply Qplus_le_compat.
           ++ apply Qmult_le_compat_r; [exact HS | apply Qabs_nonneg].
           ++ apply Qmult_le_compat_r; [exact HC | apply Qabs_nonneg].
        -- apply Qplus_le_compat.
           ++ apply (piL_mult_le_l (Qabs (sin_partial m (2 * u) + (1 # 1)%Q))
                                   ((2 # 1)%Q + q) q).
              ** exact (piLd3_abs_Splus_le m u q HS).
              ** apply Qlt_le_weak. apply QltT_to_Qlt. exact Hq0.
           ++ apply (piL_mult_le_l (Qabs (cos_partial m (2 * u))) q q).
              ** exact HC.
              ** apply Qlt_le_weak. apply QltT_to_Qlt. exact Hq0.
Qed.
(* Doubling preserves nonnegativity: 0 <= a implies 0 <= 2*a (the
   nonnegativity donor of the monotone multiplication chain). *)
Lemma piLd3_qle_0_mult2 : forall a : Q, Qle 0 a -> Qle 0 ((2 # 1)%Q * a).
Proof.
  intros a Ha. apply (Qle_trans _ (0 * a)).
  - apply qeq_le. ring.
  - apply Qmult_le_compat_r; [exact (QleT'_to_Qle _ _ piL_qle_0_two) | exact Ha].
Qed.
(* The doubled two-arm product bound: a <= c, b <= d, 0 <= a and
   0 <= d imply 2*a*b <= 2*c*d.  In the first hop, multiplying
   (2*a)*b <= (2*a)*d by b <= d requires 2*a >= 0: the nonnegativity
   arm sits on [a], not on [b] or [c]. *)
Lemma piLd3_mult2_le : forall a b c d : Q,
  Qle a c -> Qle b d -> Qle 0 a -> Qle 0 d ->
  Qle ((2 # 1)%Q * a * b) ((2 # 1)%Q * c * d).
Proof.
  intros a b c d Hac Hbd Ha Hd.
  apply (Qle_trans _ ((2 # 1)%Q * a * d)).
  - apply (piL_mult_le_l b d ((2 # 1)%Q * a)).
    + exact Hbd.
    + apply piLd3_qle_0_mult2. exact Ha.
  - apply (Qle_trans _ ((2 # 1)%Q * (a * d))).
    + apply qeq_le. ring.
    + apply (Qle_trans _ ((2 # 1)%Q * (c * d))).
      * apply (piL_mult_le_l (a * d) (c * d) (2 # 1)%Q).
        -- apply Qmult_le_compat_r; [exact Hac | exact Hd].
        -- exact (QleT'_to_Qle _ _ piL_qle_0_two).
      * apply qeq_le. ring.
Qed.
(* 0 <= q implies 0 <= 1 + q (a double hop 0 <= q <= 1 + q; the hop
   q <= 1 + q departs from q + 0 <= q + 1 and crosses to the other
   side through two [ring] bridges of the wide-form comparison
   lemmas). *)
Lemma piLd3_qle_0_plus1 : forall q : Q, Qle 0 q -> Qle 0 ((1 # 1)%Q + q).
Proof.
  intros q Hq.
  apply (Qle_trans 0 q ((1 # 1)%Q + q)).
  - exact Hq.
  - apply (leibsep_qle_wd2 (q + 0)%Q (q + (1 # 1)%Q)%Q q ((1 # 1)%Q + q)%Q).
    + ring.
    + ring.
    + apply Qplus_le_compat.
      * apply Qle_refl.
      * apply Qlt_le_weak. unfold Qlt. cbn. reflexivity.
Qed.
(* 2*s*c <= 2*(1 + q)*q (the direct shape of the right-hand side in the
   sine assembly; consumes both arms of the half-window bound at q). *)
Lemma piLd3_2SC_le : forall s c q : Q,
  Qle 0 q ->
  Qle s ((1 # 1)%Q + q) -> Qle c q -> Qle 0 s -> Qle 0 c ->
  Qle ((2 # 1)%Q * s * c) ((2 # 1)%Q * ((1 # 1)%Q + q) * q).
Proof.
  intros s c q Hq Hs Hc Hs0 Hc0.
  exact (piLd3_mult2_le s c ((1 # 1)%Q + q) q Hs Hc Hs0 Hq).
Qed.
(* The sine assembly: |[sin_partial m (4*u)]| <= 2*(1 + q)*q + e2. *)
Lemma piLd3_sin_bound : forall (m : nat) (u q e2 : Q),
  QltT 0 q ->
  Qle (Qabs (sin_partial m (2 * u))) ((1 # 1)%Q + q) ->
  Qle (Qabs (cos_partial m (2 * u))) q ->
  Qle (Qabs (piL_sin_dres m (2 * u))) e2 ->
  Qle (Qabs (sin_partial m (lp_four * u)%Q))
      ((2 # 1)%Q * ((1 # 1)%Q + q) * q + e2)%Q.
Proof.
  intros m u q e2 Hq0 HS HC HD.
  apply (Qle_trans _ (Qabs (2 * sin_partial m (2 * u) * cos_partial m (2 * u)
                            - piL_sin_dres m (2 * u)))).
  - apply qeq_le. apply Qabs_wd. apply piLd3_sin_xL_eq.
  - apply (Qle_trans _ (Qabs ((2 * sin_partial m (2 * u) * cos_partial m (2 * u))
                              + (- piL_sin_dres m (2 * u))))).
    + apply qeq_le. apply Qabs_wd. ring.
    + apply (Qle_trans _ (Qabs (2 * sin_partial m (2 * u) * cos_partial m (2 * u))
                          + Qabs (- piL_sin_dres m (2 * u)))).
      * apply Qabs_triangle.
      * apply (Qle_trans _ (Qabs (2 * sin_partial m (2 * u) * cos_partial m (2 * u))
                            + Qabs (piL_sin_dres m (2 * u)))).
        -- apply Qplus_le_compat.
           ++ apply Qle_refl.
           ++ apply qeq_le. exact (Qabs_opp (piL_sin_dres m (2 * u))).
        -- (* Transport of |2*S*C| == 2*|S|*|C| plus two monotone hops. *)
           assert (Hsum : Qabs (2 * sin_partial m (2 * u) * cos_partial m (2 * u))
                          == ((2 # 1)%Q * Qabs (sin_partial m (2 * u))
                              * Qabs (cos_partial m (2 * u)))).
           { apply (Qeq_trans _ (Qabs (2 * sin_partial m (2 * u))
                                 * Qabs (cos_partial m (2 * u)))).
             - exact (piLred_abs_mult (2 * sin_partial m (2 * u))
                                      (cos_partial m (2 * u))).
             - rewrite (piLred_abs_mult (2 # 1)%Q (sin_partial m (2 * u))).
               rewrite piL_qabs_two. apply Qeq_refl. }
           apply (Qle_trans _ ((2 # 1)%Q * Qabs (sin_partial m (2 * u))
                               * Qabs (cos_partial m (2 * u))
                               + Qabs (piL_sin_dres m (2 * u)))).
           ++ apply qeq_le. rewrite Hsum. apply Qeq_refl.
           ++ apply Qplus_le_compat.
              ** exact (piLd3_2SC_le (Qabs (sin_partial m (2 * u)))
                                     (Qabs (cos_partial m (2 * u))) q
                                     (Qlt_le_weak 0 q (QltT_to_Qlt 0 q Hq0))
                                     HS HC (Qabs_nonneg (sin_partial m (2 * u)))
                                     (Qabs_nonneg (cos_partial m (2 * u)))).
              ** exact HD.
Qed.
(* The cosine assembly: |[cos_partial m (4*u) + 1]| <=
   e3 + 2*q*(2 + q) + (q*(2 + q) + q*q). *)
Lemma piLd3_cos_bound : forall (m : nat) (u q e3 : Q),
  QltT 0 q ->
  Qle (Qabs (sin_partial m (2 * u) - (1 # 1)%Q)) q ->
  Qle (Qabs (cos_partial m (2 * u))) q ->
  Qle (Qabs (piL_cos_dres m (2 * u))) e3 ->
  Qle (Qabs (cos_partial m (lp_four * u)%Q + (1 # 1)%Q))
      (e3 + 2 * (q * ((2 # 1)%Q + q))
       + (q * ((2 # 1)%Q + q) + q * q))%Q.
Proof.
  intros m u q e3 Hq0 HS HC HD.
  apply (Qle_trans _ (Qabs (piL_cos_dres m (2 * u)
                            + 2 * ((1 # 1)%Q - sin_partial m (2 * u) * sin_partial m (2 * u))
                            + piL_pyth_dres m (2 * u)))).
  - apply qeq_le. apply Qabs_wd. apply piLd3_cos_xL_plus1_eq.
  - apply (Qle_trans _ (Qabs (piL_cos_dres m (2 * u)
                              + 2 * ((1 # 1)%Q - sin_partial m (2 * u) * sin_partial m (2 * u)))
                        + Qabs (piL_pyth_dres m (2 * u)))).
    + apply Qabs_triangle.
    + apply (Qle_trans _ (Qabs (piL_cos_dres m (2 * u))
                          + Qabs (2 * ((1 # 1)%Q - sin_partial m (2 * u) * sin_partial m (2 * u)))
                          + Qabs (piL_pyth_dres m (2 * u)))).
      * apply Qplus_le_compat.
        -- apply Qabs_triangle.
        -- apply Qle_refl.
      * apply Qplus_le_compat.
        -- apply Qplus_le_compat.
           ++ exact HD.
           ++ exact (piLd3_halfsq_bound m u q Hq0 HS).
        -- exact (piLd3_dpit_bound m u q Hq0 HS HC).
Qed.
(* ========== Section 5. Budget lemmas ========== *)
(* (the constant identities and the two scaled budget branches)        *)

Lemma piLd3_Hc1 : ((16 # 1)%Q * (1 # 16)%Q)%Q == (1 # 1)%Q.
Proof. reflexivity. Qed.

Lemma piLd3_Hc32 : ((32 # 1)%Q * (1 # 32)%Q)%Q == (1 # 1)%Q.
Proof. reflexivity. Qed.

Lemma piLd3_H82 : ((16 # 1)%Q * (1 # 2)%Q)%Q == (8 # 1)%Q.
Proof. reflexivity. Qed.

Lemma piLd3_H328 : ((32 # 1)%Q * (1 # 8)%Q)%Q == (4 # 1)%Q.
Proof. reflexivity. Qed.

Lemma piLd3_H412 : ((4 # 1)%Q * (1 # 2)%Q)%Q == (2 # 1)%Q.
Proof. reflexivity. Qed.
(* The sine-side scaled budget: 2*(1 + q)*q + e2 < dt (q = dt/16 and
   e2 = dt/2; dt < 16 implies 12*q < 16*q = dt). *)
Lemma piLd3_budget_v1 : forall d q e2 : Q,
  q == d * (1 # 16)%Q ->
  e2 == d * (1 # 2)%Q ->
  QltT 0 d -> QleT' d (16 # 1)%Q ->
  Qlt ((2 # 1)%Q * ((1 # 1)%Q + q) * q + e2) d.
Proof.
  intros d q e2 Hq He2 Hd0 Hd16.
  assert (Hq0 : Qlt 0 q).
  { rewrite Hq. apply Qmult_lt_0_compat.
    - exact (QltT_to_Qlt _ _ Hd0).
    - exact piLd3_c16_pos. }
  assert (Hq1 : Qle q (1 # 1)%Q).
  { apply (leibsep_qle_wd2 (d * (1 # 16)%Q) ((16 # 1)%Q * (1 # 16)%Q)%Q
                           q (1 # 1)%Q).
    - exact (Qeq_sym q (d * (1 # 16)%Q) Hq).
    - exact piLd3_Hc1.
    - apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ Hd16).
      + apply Qlt_le_weak. exact piLd3_c16_pos. }
  assert (Hqq : Qle (q * q) q).
  { apply (Qle_trans _ ((1 # 1)%Q * q)).
    - apply Qmult_le_compat_r; [exact Hq1 | apply Qlt_le_weak; exact Hq0].
    - apply qeq_le. ring. }
  assert (H2qq : Qle ((2 # 1)%Q * (q * q)) ((2 # 1)%Q * q)).
  { apply (piL_mult_le_l (q * q) q (2 # 1)%Q).
    - exact Hqq.
    - exact (QleT'_to_Qle _ _ piL_qle_0_two). }
  assert (Hdq : ((16 # 1)%Q * q)%Q == d).
  { rewrite Hq.
    apply (Qeq_trans _ (((16 # 1)%Q * (1 # 16)%Q) * d)).
    - ring.
    - rewrite piLd3_Hc1. ring. }
  assert (He8 : (d * (1 # 2)%Q)%Q == ((8 # 1)%Q * q)).
  { rewrite <- Hdq.
    apply (Qeq_trans _ (((16 # 1)%Q * (1 # 2)%Q) * q)).
    - ring.
    - rewrite piLd3_H82. ring. }
  apply (Qle_lt_trans ((2 # 1)%Q * ((1 # 1)%Q + q) * q + e2)%Q
                      (((2 # 1)%Q * q + (2 # 1)%Q * (q * q))
                       + d * (1 # 2)%Q)%Q d).
  - apply (Qle_trans _ (((2 # 1)%Q * q + (2 # 1)%Q * (q * q)) + e2)%Q).
    + apply qeq_le. ring.
    + apply (piLred_qle_wd_r (((2 # 1)%Q * q + (2 # 1)%Q * (q * q)) + e2)%Q).
      * rewrite He2. apply Qeq_refl.
      * apply Qle_refl.
  - apply (Qle_lt_trans (((2 # 1)%Q * q + (2 # 1)%Q * (q * q))
                         + d * (1 # 2)%Q)%Q
                        (((2 # 1)%Q * q + (2 # 1)%Q * q) + ((8 # 1)%Q * q))%Q d).
    + apply (Qle_trans _ (((2 # 1)%Q * q + (2 # 1)%Q * (q * q))
                          + ((8 # 1)%Q * q))).
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- apply qeq_le. exact He8.
      * apply Qplus_le_compat.
        -- apply Qplus_le_compat; [apply Qle_refl | exact H2qq].
        -- apply Qle_refl.
    + apply (leibsep_qlt_wd2 ((12 # 1)%Q * q)%Q d
                             (((2 # 1)%Q * q + (2 # 1)%Q * q)
                              + ((8 # 1)%Q * q))%Q d).
      * ring.
      * apply Qeq_refl.
      * apply (leibsep_qlt_wd2 ((12 # 1)%Q * q)%Q ((16 # 1)%Q * q)%Q
                               ((12 # 1)%Q * q)%Q d).
        -- apply Qeq_refl.
        -- exact Hdq.
        -- apply (leibsep_qlt_wd2 ((12 # 1)%Q * q)%Q
                                  ((12 # 1)%Q * q + (4 # 1)%Q * q)%Q
                                  ((12 # 1)%Q * q)%Q ((16 # 1)%Q * q)%Q).
           ++ apply Qeq_refl.
           ++ ring.
           ++ apply piLd3_qlt_add_r.
              ** apply Qmult_lt_0_compat.
                 --- unfold Qlt. cbn. reflexivity.
                 --- exact Hq0.
Qed.
(* The cosine-side scaled budget: e3 + 2*q*(2 + q) + q*(2 + q) + q*q
   < dt (q = dt/32 and e3 = dt/8; dt < 16 implies 12*q < 32*q = dt). *)
Lemma piLd3_budget_v2 : forall d q e3 : Q,
  q == d * (1 # 32)%Q ->
  e3 == d * (1 # 8)%Q ->
  QltT 0 d -> QleT' d (16 # 1)%Q ->
  Qlt (e3 + 2 * (q * ((2 # 1)%Q + q))
       + (q * ((2 # 1)%Q + q) + q * q)) d.
Proof.
  intros d q e3 Hq He3 Hd0 Hd16.
  assert (Hq0 : Qlt 0 q).
  { rewrite Hq. apply Qmult_lt_0_compat.
    - exact (QltT_to_Qlt _ _ Hd0).
    - exact piLd3_c32_pos. }
  assert (Hq1 : Qle q (1 # 2)%Q).
  { apply (leibsep_qle_wd2 (d * (1 # 32)%Q) ((16 # 1)%Q * (1 # 32)%Q)%Q
                           q (1 # 2)%Q).
    - exact (Qeq_sym q (d * (1 # 32)%Q) Hq).
    - reflexivity.
    - apply Qmult_le_compat_r.
      + exact (QleT'_to_Qle _ _ Hd16).
      + apply Qlt_le_weak. exact piLd3_c32_pos. }
  assert (H4qq : Qle ((4 # 1)%Q * (q * q)) ((2 # 1)%Q * q)).
  { apply (Qle_trans _ ((4 # 1)%Q * (q * (1 # 2)%Q))).
    - apply (piL_mult_le_l (q * q) (q * (1 # 2)%Q) (4 # 1)%Q).
      + apply (piL_mult_le_l q (1 # 2)%Q q); [exact Hq1 | apply Qlt_le_weak; exact Hq0].
      + exact (QleT'_to_Qle _ _ piL_qle_0_four).
    - apply qeq_le.
      apply (Qeq_trans _ (((4 # 1)%Q * (1 # 2)%Q) * q)).
      * ring.
      * rewrite piLd3_H412. apply Qeq_refl. }
  assert (Hsp2 : (e3 + 2 * (q * ((2 # 1)%Q + q))
                  + (q * ((2 # 1)%Q + q) + q * q))%Q
                 == (e3 + (6 # 1)%Q * q + (4 # 1)%Q * (q * q))) by ring.
  assert (Hdq : ((32 # 1)%Q * q)%Q == d).
  { rewrite Hq.
    apply (Qeq_trans _ (((32 # 1)%Q * (1 # 32)%Q) * d)).
    - ring.
    - rewrite piLd3_Hc32. ring. }
  assert (He4 : (d * (1 # 8)%Q)%Q == ((4 # 1)%Q * q)).
  { rewrite <- Hdq.
    apply (Qeq_trans _ (((32 # 1)%Q * (1 # 8)%Q) * q)).
    - ring.
    - rewrite piLd3_H328. ring. }
  assert (He34 : e3 == ((4 # 1)%Q * q)).
  { rewrite He3. exact He4. }
  apply (leibsep_qlt_wd2 (e3 + (6 # 1)%Q * q + (4 # 1)%Q * (q * q))%Q d
                         (e3 + 2 * (q * ((2 # 1)%Q + q))
                          + (q * ((2 # 1)%Q + q) + q * q))%Q d).
  - apply Qeq_sym. exact Hsp2.
  - apply Qeq_refl.
  - apply (Qle_lt_trans (e3 + (6 # 1)%Q * q + (4 # 1)%Q * (q * q))%Q
                        ((4 # 1)%Q * q + (6 # 1)%Q * q + (2 # 1)%Q * q)%Q d).
    + apply Qplus_le_compat.
      * apply qeq_le. rewrite He34. apply Qeq_refl.
      * exact H4qq.
    + apply (leibsep_qlt_wd2 ((12 # 1)%Q * q)%Q d
                             ((4 # 1)%Q * q + (6 # 1)%Q * q + (2 # 1)%Q * q)%Q d).
      * ring.
      * apply Qeq_refl.
      * apply (leibsep_qlt_wd2 ((12 # 1)%Q * q)%Q ((32 # 1)%Q * q)%Q
                               ((12 # 1)%Q * q)%Q d).
        -- apply Qeq_refl.
        -- exact Hdq.
        -- apply (leibsep_qlt_wd2 ((12 # 1)%Q * q)%Q
                                  ((12 # 1)%Q * q + (20 # 1)%Q * q)%Q
                                  ((12 # 1)%Q * q)%Q ((32 # 1)%Q * q)%Q).
           ++ apply Qeq_refl.
           ++ ring.
           ++ apply piLd3_qlt_add_r.
              ** apply Qmult_lt_0_compat.
                 --- unfold Qlt. cbn. reflexivity.
                 --- exact Hq0.
Qed.
(* ========== Section 6. The two main vanishing statements ========== *)
(* (canonical-form names; carried by explicit seed-slot premises:      *)
(*  constructive [forall] assumptions carried by the statements        *)
(*  themselves)                                                        *)

(* The sine side: double-index vanishing of the sine partial sums at
   the window points (carried by the half-window pair slot and the
   sine remainder slot). *)
Lemma piLd3_sin_xL_vanish_carry :
  forall (H1 : piLd3_seed_halfwin) (H2 : piLd3_seed_dres) (dt : Q),
    QltT 0 dt ->
    sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
      QltT (Qabs (sin_partial m (lw0m_xL m))) dt).
Proof.
  intros H1 H2 dt Hdt.
  destruct (Qlt_le_dec dt (16 # 1)%Q) as [Hsmall | Hbig].
  - (* Branch 1: dt < 16 -- q := dt/16, e2 := dt/2; the budget yields
       12*q < 16*q = dt. *)
    pose (q := (dt * (1 # 16)%Q)%Q).
    pose (e2 := (dt * (1 # 2)%Q)%Q).
    assert (Hq0 : QltT 0 q).
    { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      - exact (QltT_to_Qlt _ _ Hdt).
      - exact piLd3_c16_pos. }
    assert (He20 : QltT 0 e2).
    { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      - exact (QltT_to_Qlt _ _ Hdt).
      - unfold Qlt. cbn. reflexivity. }
    destruct (H1 q Hq0) as [K1 HK1].
    destruct (H2 piLd3_B e2 piLd3_B_pos He20) as [j2 Hj2].
    exists (Nat.max K1 j2). intros m Hm.
    assert (Hm1 : (K1 <= m)%nat).
    { apply (Nat.le_trans K1 (Nat.max K1 j2) m).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hm). }
    assert (Hm2 : (j2 <= m)%nat).
    { apply (Nat.le_trans j2 (Nat.max K1 j2) m).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hm). }
    destruct (HK1 m m Hm1 Hm1) as [HClt HSl].
    pose proof (Hj2 m (2 * lp_odd m) Hm2 (piLd3_abs_2u_le_B m)) as HDlt.
    assert (HSle : Qle (Qabs (sin_partial m (2 * lp_odd m) - (1 # 1)%Q)) q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HSl).
    assert (HS : Qle (Qabs (sin_partial m (2 * lp_odd m))) ((1 # 1)%Q + q))
      by exact (piLd3_abs_S_le m (lp_odd m) q HSle).
    assert (HC : Qle (Qabs (cos_partial m (2 * lp_odd m))) q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HClt).
    assert (HD : Qle (Qabs (piL_sin_dres m (2 * lp_odd m))) e2)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HDlt).
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (sin_partial m (lw0m_xL m)))
                        ((2 # 1)%Q * ((1 # 1)%Q + q) * q + e2)%Q dt).
    + exact (piLd3_sin_bound m (lp_odd m) q e2 Hq0 HS HC HD).
    + apply (piLd3_budget_v1 dt q e2).
      * reflexivity.
      * reflexivity.
      * exact Hdt.
      * apply Qle_to_QleT'. apply Qlt_le_weak. exact Hsmall.
  - (* Branch 2: dt >= 16 -- the fixed budget q := 1, e2 := 8;
       12 < 16 <= dt. *)
    pose (q := (1 # 1)%Q).
    pose (e2 := (8 # 1)%Q).
    assert (Hq0 : QltT 0 q)
      by (apply Qlt_to_QltT; unfold Qlt; cbn; reflexivity).
    assert (He20 : QltT 0 e2)
      by (apply Qlt_to_QltT; unfold Qlt; cbn; reflexivity).
    destruct (H1 q Hq0) as [K1 HK1].
    destruct (H2 piLd3_B e2 piLd3_B_pos He20) as [j2 Hj2].
    exists (Nat.max K1 j2). intros m Hm.
    assert (Hm1 : (K1 <= m)%nat).
    { apply (Nat.le_trans K1 (Nat.max K1 j2) m).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hm). }
    assert (Hm2 : (j2 <= m)%nat).
    { apply (Nat.le_trans j2 (Nat.max K1 j2) m).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hm). }
    destruct (HK1 m m Hm1 Hm1) as [HClt HSl].
    pose proof (Hj2 m (2 * lp_odd m) Hm2 (piLd3_abs_2u_le_B m)) as HDlt.
    assert (HSle : Qle (Qabs (sin_partial m (2 * lp_odd m) - (1 # 1)%Q)) q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HSl).
    assert (HS : Qle (Qabs (sin_partial m (2 * lp_odd m))) ((1 # 1)%Q + q))
      by exact (piLd3_abs_S_le m (lp_odd m) q HSle).
    assert (HC : Qle (Qabs (cos_partial m (2 * lp_odd m))) q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HClt).
    assert (HD : Qle (Qabs (piL_sin_dres m (2 * lp_odd m))) e2)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HDlt).
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (sin_partial m (lw0m_xL m))) (12 # 1)%Q dt).
    + apply (Qle_trans _ (((2 # 1)%Q * ((1 # 1)%Q + q) * q + e2)%Q)).
      * exact (piLd3_sin_bound m (lp_odd m) q e2 Hq0 HS HC HD).
      * apply qeq_le. reflexivity.
    + apply (Qlt_le_trans (12 # 1)%Q (16 # 1)%Q dt).
      * unfold Qlt. cbn. reflexivity.
      * exact Hbig.
Qed.
(* Carrier of the canonical-form name on the sine side; the two seed
   slots travel as explicit premises (seed-slot premises:
   constructive [forall] assumptions carried by the statements
   themselves). *)
Lemma piL_sin_xL_vanish :
  forall (H1 : piLd3_seed_halfwin) (H2 : piLd3_seed_dres) (dt : Q),
    QltT 0 dt ->
    sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
      QltT (Qabs (sin_partial m (lw0m_xL m))) dt).
Proof. exact piLd3_sin_xL_vanish_carry. Qed.
(* The cosine side: double-index vanishing of the shifted cosine
   partial sums at the window points (carried by the half-window pair
   slot and the cosine remainder slot). *)
Lemma piLd3_cos_xL_vanish_carry :
  forall (H1 : piLd3_seed_halfwin) (H3 : piLd3_seed_dcos) (dt : Q),
    QltT 0 dt ->
    sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
      QltT (Qabs (cos_partial m (lw0m_xL m) + (1 # 1)%Q)) dt).
Proof.
  intros H1 H3 dt Hdt.
  destruct (Qlt_le_dec dt (16 # 1)%Q) as [Hsmall | Hbig].
  - (* Branch 1: dt < 16 -- q := dt/32, e3 := dt/8; the budget yields
       12*q < 32*q = dt. *)
    pose (q := (dt * (1 # 32)%Q)%Q).
    pose (e3 := (dt * (1 # 8)%Q)%Q).
    assert (Hq0 : QltT 0 q).
    { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      - exact (QltT_to_Qlt _ _ Hdt).
      - exact piLd3_c32_pos. }
    assert (He30 : QltT 0 e3).
    { apply Qlt_to_QltT. apply Qmult_lt_0_compat.
      - exact (QltT_to_Qlt _ _ Hdt).
      - unfold Qlt. cbn. reflexivity. }
    destruct (H1 q Hq0) as [K1 HK1].
    destruct (H3 piLd3_B e3 piLd3_B_pos He30) as [j3 Hj3].
    exists (Nat.max K1 j3). intros m Hm.
    assert (Hm1 : (K1 <= m)%nat).
    { apply (Nat.le_trans K1 (Nat.max K1 j3) m).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hm). }
    assert (Hm3 : (j3 <= m)%nat).
    { apply (Nat.le_trans j3 (Nat.max K1 j3) m).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hm). }
    destruct (HK1 m m Hm1 Hm1) as [HClt HSl].
    pose proof (Hj3 m (2 * lp_odd m) Hm3 (piLd3_abs_2u_le_B m)) as HDlt.
    assert (HS : Qle (Qabs (sin_partial m (2 * lp_odd m) - (1 # 1)%Q)) q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HSl).
    assert (HC : Qle (Qabs (cos_partial m (2 * lp_odd m))) q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HClt).
    assert (HD : Qle (Qabs (piL_cos_dres m (2 * lp_odd m))) e3)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HDlt).
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (cos_partial m (lw0m_xL m) + (1 # 1)%Q))
                        (e3 + 2 * (q * ((2 # 1)%Q + q))
                         + (q * ((2 # 1)%Q + q) + q * q))%Q dt).
    + exact (piLd3_cos_bound m (lp_odd m) q e3 Hq0 HS HC HD).
    + apply (piLd3_budget_v2 dt q e3).
      * reflexivity.
      * reflexivity.
      * exact Hdt.
      * apply Qle_to_QleT'. apply Qlt_le_weak. exact Hsmall.
  - (* Branch 2: dt >= 16 -- the fixed budget q := 1, e3 := 4;
       14 < 16 <= dt. *)
    pose (q := (1 # 1)%Q).
    pose (e3 := (4 # 1)%Q).
    assert (Hq0 : QltT 0 q)
      by (apply Qlt_to_QltT; unfold Qlt; cbn; reflexivity).
    assert (He30 : QltT 0 e3)
      by (apply Qlt_to_QltT; unfold Qlt; cbn; reflexivity).
    destruct (H1 q Hq0) as [K1 HK1].
    destruct (H3 piLd3_B e3 piLd3_B_pos He30) as [j3 Hj3].
    exists (Nat.max K1 j3). intros m Hm.
    assert (Hm1 : (K1 <= m)%nat).
    { apply (Nat.le_trans K1 (Nat.max K1 j3) m).
      - apply Nat.le_max_l.
      - exact (NatLe_drop _ _ Hm). }
    assert (Hm3 : (j3 <= m)%nat).
    { apply (Nat.le_trans j3 (Nat.max K1 j3) m).
      - apply Nat.le_max_r.
      - exact (NatLe_drop _ _ Hm). }
    destruct (HK1 m m Hm1 Hm1) as [HClt HSl].
    pose proof (Hj3 m (2 * lp_odd m) Hm3 (piLd3_abs_2u_le_B m)) as HDlt.
    assert (HS : Qle (Qabs (sin_partial m (2 * lp_odd m) - (1 # 1)%Q)) q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HSl).
    assert (HC : Qle (Qabs (cos_partial m (2 * lp_odd m))) q)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HClt).
    assert (HD : Qle (Qabs (piL_cos_dres m (2 * lp_odd m))) e3)
      by (apply Qlt_le_weak; apply QltT_to_Qlt; exact HDlt).
    apply Qlt_to_QltT.
    apply (Qle_lt_trans (Qabs (cos_partial m (lw0m_xL m) + (1 # 1)%Q))
                        (14 # 1)%Q dt).
    + apply (Qle_trans _ ((e3 + 2 * (q * ((2 # 1)%Q + q))
                           + (q * ((2 # 1)%Q + q) + q * q))%Q)).
      * exact (piLd3_cos_bound m (lp_odd m) q e3 Hq0 HS HC HD).
      * apply qeq_le. reflexivity.
    + apply (Qlt_le_trans (14 # 1)%Q (16 # 1)%Q dt).
      * unfold Qlt. cbn. reflexivity.
      * exact Hbig.
Qed.
(* Carrier of the canonical-form name on the cosine side; the two seed
   slots travel as explicit premises (seed-slot premises:
   constructive [forall] assumptions carried by the statements
   themselves). *)
Lemma piL_cos_xL_neg1_vanish :
  forall (H1 : piLd3_seed_halfwin) (H3 : piLd3_seed_dcos) (dt : Q),
    QltT 0 dt ->
    sigT (fun N1 : nat => forall m : nat, NatLe N1 m ->
      QltT (Qabs (cos_partial m (lw0m_xL m) + (1 # 1)%Q)) dt).
Proof. exact piLd3_cos_xL_vanish_carry. Qed.
(* ---- Merged segment 6: PiKernelLeibsep (md5 208cb007) ---- *)
Lemma lw0_pitB_conv_m1_cases : forall j : nat,
  sigT (fun b : bool => QeqT (q_pow (-1)%Q j) (if b then 1%Q else (-1)%Q)).
Proof.
  intro j. induction j as [| j IH].
  - exists true. unfold QeqT. cbn. reflexivity.
  - destruct IH as [b Hb]. exists (negb b). apply qeq_imp_qeqT.
    pose proof (qeqT_imp_qeq _ _ Hb) as Hb'.
    rewrite (q_pow_succ (-1)%Q j). destruct b.
    + rewrite Hb'. reflexivity.
    + rewrite Hb'. reflexivity.
Qed.

Lemma lw0_pitB_conv_cos_term_abs : forall (j : nat) (q : Q),
  QeqT (Qabs (cos_term j q))
       (q_pow (Qabs q) (2 * j) / q_fact (2 * j)).
Proof.
  intros j q. apply qeq_imp_qeqT. unfold cos_term, Qdiv.
  rewrite Qabs_Qmult, Qabs_Qmult.
  rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_qabs_pow q (2 * j))).
  rewrite (lw0_Qabs_pos_eq (Qinv (q_fact (2 * j))))
    by (apply Qle_to_QleT'; apply Qinv_le_0_compat;
        apply (Qlt_le_weak 0%Q); apply q_fact_pos).
  destruct (lw0_pitB_conv_m1_cases j) as [b Hc]. destruct b;
    rewrite (qeqT_imp_qeq _ _ Hc); simpl; ring.
Qed.

Lemma lw0_pitB_conv_tail_gen : forall (P Pd w : nat -> Q) (D M : nat),
  (forall n : nat, P (Datatypes.S n) == P n + Pd n) ->
  (forall n : nat, Qabs (Pd n) == w n) ->
  (forall n : nat, QleT' 0 (w n)) ->
  (forall j : nat, (M <= j)%nat -> QleT' (w (Datatypes.S j)) ((1#2) * w j)) ->
  QleT' (Qabs (P (M + D)%nat - P M)) (2 * w M).
Proof.
  intros P Pd w D.
  induction D as [| D IH]; intros M Hstep Habs Hw0 Hhalf.
  - assert (E0 : (M + 0)%nat = M) by apply Nat.add_0_r.
    assert (Hbase : QleT' (Qabs (P M - P M)) (2 * w M)).
    { apply (qleT'_trans (Qabs (P M - P M)) 0%Q (2 * w M)).
      - apply qeq_leT'. assert (Hzz : (P M - P M)%Q == 0%Q) by ring. rewrite Hzz. reflexivity.
      - apply Qle_to_QleT'. apply Qmult_le_0_compat.
        + apply (Qlt_le_weak 0%Q (2#1)%Q).
          apply (QltT_to_Qlt 0%Q (2#1)%Q). unfold QltT. reflexivity.
        + exact (QleT'_to_Qle _ _ (Hw0 M)). }
    exact (eq_rect_r (fun n0 : nat => QleT' (Qabs (P n0 - P M)) (2 * w M)) Hbase E0).
  - assert (E1 : (M + Datatypes.S D)%nat = (Datatypes.S M + D)%nat)
      by (rewrite Nat.add_succ_r, Nat.add_succ_l; reflexivity).
    assert (Hmain : QleT' (Qabs (P (Datatypes.S M + D)%nat - P M)) (2 * w M)).
    { assert (Hz : (P (Datatypes.S M + D)%nat - P M)%Q
                   == Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))).
      { rewrite (Hstep M). ring. }
      apply (qleT'_trans (Qabs (P (Datatypes.S M + D)%nat - P M))
                         (Qabs (Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))
                         (2 * w M)).
      - apply (qeq_leT' (Qabs (P (Datatypes.S M + D)%nat - P M))
                        (Qabs (Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))).
        rewrite Hz. apply Qeq_refl.
      - assert (Htri : Qle (Qabs (Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))
                           (Qabs (Pd M) + Qabs (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))
          by apply Qabs_triangle.
        assert (Hih := IH (Datatypes.S M) Hstep Habs Hw0
                          (fun j1 Hj1 => Hhalf j1
                             (Nat.le_trans M (Datatypes.S M) j1
                                (Nat.le_succ_diag_r M) Hj1))).
        apply (qleT'_trans (Qabs (Pd M + (P (Datatypes.S M + D)%nat - P (Datatypes.S M))))
                           (w M + 2 * w (Datatypes.S M)) (2 * w M)).
        + apply Qle_to_QleT'.
          apply (Qle_trans _ (Qabs (Pd M) + Qabs (P (Datatypes.S M + D)%nat - P (Datatypes.S M))) _).
          * exact Htri.
          * apply Qplus_le_compat.
            -- rewrite (Habs M). apply Qle_refl.
            -- exact (QleT'_to_Qle _ _ Hih).
        + apply Qle_to_QleT'.
          apply (Qle_trans (w M + 2 * w (Datatypes.S M))
                           (w M + w M) (2 * w M)).
          * apply Qplus_le_compat.
            -- apply Qle_refl.
            -- apply QleT'_to_Qle.
               apply (qleT'_trans (2 * w (Datatypes.S M))
                                  (2%Q * ((1#2) * w M))
                                  (w M)).
               ++ apply (lw0_pitB_conv_mult_le_l 2%Q (w (Datatypes.S M))
                           ((1#2) * w M) (Hhalf M (Nat.le_refl M))).
                  unfold QleT'. reflexivity.
               ++ apply (qeq_leT' (2%Q * ((1#2) * w M)) (w M)).
                  (* The settled final form of [Qmult_comp]: the instance
   [Proper (Qeq==>Qeq==>Qeq) Qmult] with the four explicit arguments
   x x' y y' returning x==x' -> y==y' -> x*y==x'*y'. The constant leg
   goes through a closed [QeqT] certificate. *)
                  assert (Ec2h : QeqT (2%Q * (1#2))%Q 1%Q)
                    by (unfold QeqT; cbn; reflexivity).
                  rewrite (Qmult_assoc 2%Q (1#2) (w M)).
                  rewrite (qeqT_imp_qeq _ _ Ec2h).
                  apply (Qmult_1_l (w M)).
          * apply QleT'_to_Qle.
            apply (qeq_leT' (w M + w M) (2 * w M)).
            assert (Ec2q : QeqT 2%Q (1%Q + 1%Q))
              by (unfold QeqT; cbn; reflexivity).
            rewrite (qeqT_imp_qeq _ _ Ec2q).
            rewrite (Qmult_plus_distr_l 1%Q 1%Q (w M)).
            rewrite (Qmult_1_l (w M)).
            apply Qeq_refl.
    }
    exact (eq_rect_r (fun n0 : nat => QleT' (Qabs (P n0 - P M)) (2 * w M)) Hmain E1).
Qed.

Lemma lw0_pitB_conv_cos_tail : forall (q : Q) (M D : nat),
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  QleT' (Qabs (cos_partial (M + D) q - cos_partial M q))
        (2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
Proof.
  intros q M D Hr.
  assert (Hqnn : QleT' 0 (Qabs q))
    by (apply Qle_to_QleT'; apply Qabs_nonneg).
  assert (Hhalf : forall j : nat, (M <= j)%nat ->
           QleT' (q_pow (Qabs q) (2 * Datatypes.S (Datatypes.S j))
                   / q_fact (2 * Datatypes.S (Datatypes.S j)))
                 ((1#2) * (q_pow (Qabs q) (2 * Datatypes.S j)
                            / q_fact (2 * Datatypes.S j)))).
  { intros j Hj.
    assert (E2j : (2 * Datatypes.S j)%nat = Datatypes.S (Datatypes.S (2 * j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * j) 1).
      rewrite (Nat.add_succ_r (2 * j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    assert (E2j2 : (2 * Datatypes.S (Datatypes.S j))%nat
                   = Datatypes.S (Datatypes.S (2 * Datatypes.S j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * Datatypes.S j) 1).
      rewrite (Nat.add_succ_r (2 * Datatypes.S j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    rewrite E2j2, E2j.
    apply (lw0_pitB_conv_tstep (Qabs q)
                 (Datatypes.S (Datatypes.S (2 * j)))).
    - exact Hqnn.
    - apply (qleT'_trans (2 * q_pow (Qabs q) 2)
                         (lw0_q_of_nat (Datatypes.S (2 * j))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
      + exact (Hr j Hj).
      + apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
        * apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (2 * j)))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
          -- apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (2 * j))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (2 * j)))
                             (Qmult_comm (lw0_q_of_nat (Datatypes.S (2 * j)))
                                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))))).
          -- apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                       (lw0_q_of_nat (Datatypes.S (2 * j)))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
             ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j)))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))).
                ** apply lw0_q_of_nat_le_succ.
                ** apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_nonneg.
        * apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
          -- apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (Qmult_comm (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
          -- apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
             ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
                ** apply lw0_q_of_nat_le_succ.
                ** apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_nonneg. }
  assert (HhalfM : QleT' (q_pow (Qabs q) (2 * Datatypes.S M)
                            / q_fact (2 * Datatypes.S M))
                         ((1#2) * (q_pow (Qabs q) (2 * M)
                                    / q_fact (2 * M)))).
  { assert (E2M : (2 * Datatypes.S M)%nat = Datatypes.S (Datatypes.S (2 * M))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * M) 1).
      rewrite (Nat.add_succ_r (2 * M) 0).
      rewrite Nat.add_0_r. reflexivity. }
    rewrite E2M.
    apply (lw0_pitB_conv_tstep (Qabs q) (2 * M)).
    - exact Hqnn.
    - exact (Hr M (Nat.le_refl M)). }
  assert (Ec2h : QeqT (2%Q * (1#2))%Q 1%Q) by (unfold QeqT; cbn; reflexivity).
  apply (qleT'_trans (Qabs (cos_partial (M + D) q - cos_partial M q))
                     (2%Q * ((1#2) * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))))
                     (2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))).
  - apply (qleT'_trans (Qabs (cos_partial (M + D) q - cos_partial M q))
                       (2%Q * (q_pow (Qabs q) (2 * Datatypes.S M)
                                 / q_fact (2 * Datatypes.S M)))
                       (2%Q * ((1#2) * (q_pow (Qabs q) (2 * M)
                                          / q_fact (2 * M))))).
    + apply (lw0_pitB_conv_tail_gen (fun n => cos_partial n q)
                                    (fun n => cos_term (Datatypes.S n) q)
                                    (fun n => q_pow (Qabs q) (2 * Datatypes.S n)
                                                / q_fact (2 * Datatypes.S n))
                                    D M).
      * intros n. reflexivity.
      * intros n. exact (qeqT_imp_qeq _ _ (lw0_pitB_conv_cos_term_abs (Datatypes.S n) q)).
      * intros n. apply lw0_pitB_conv_t_nonneg. exact Hqnn.
      * intros j Hj. exact (Hhalf j Hj).
    + apply (lw0_pitB_conv_mult_le_l 2%Q
               (q_pow (Qabs q) (2 * Datatypes.S M) / q_fact (2 * Datatypes.S M))
               ((1#2) * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))) HhalfM).
      unfold QleT'. reflexivity.
  - apply (qleT'_trans (2%Q * ((1#2) * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))))
                       (q_pow (Qabs q) (2 * M) / q_fact (2 * M))
                       (2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))).
    + apply (qeq_leT' (2%Q * ((1#2) * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))))
                      (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
      rewrite (Qmult_assoc 2%Q (1#2) (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
      rewrite (qeqT_imp_qeq _ _ Ec2h).
      apply (Qmult_1_l (q_pow (Qabs q) (2 * M) / q_fact (2 * M))).
    + apply (qleT'_trans (q_pow (Qabs q) (2 * M) / q_fact (2 * M))
                         (1%Q * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))
                         (2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))).
      * apply (qeq_leT' (q_pow (Qabs q) (2 * M) / q_fact (2 * M))
                        (1%Q * (q_pow (Qabs q) (2 * M) / q_fact (2 * M)))
                        (Qeq_sym _ _ (Qmult_1_l (q_pow (Qabs q) (2 * M)
                                              / q_fact (2 * M))))).
      * apply Qle_to_QleT'. apply Qmult_le_compat_r.
        -- assert (H12 : QltT 1%Q 2%Q) by (unfold QltT, Qlt_bool; reflexivity).
           exact (Qlt_le_weak 1%Q 2%Q (QltT_to_Qlt 1%Q 2%Q H12)).
        -- exact (QleT'_to_Qle _ _
                    (lw0_pitB_conv_t_nonneg (Qabs q) (2 * M) Hqnn)).
Qed.
Lemma leibsep_cos_qp_deriv_tail_stable : forall (q : Q) (M D : nat),
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q + (1 # 1)%Q))
        (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q + (1 # 1)%Q)
         + 2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))%Q)%Q.
Proof.
  intros q M D Hr.
  pose proof (lw0_pitB_conv_cos_tail q M D Hr) as Htail.
  apply (qleT'_trans
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q + (1 # 1)%Q))
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                 - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)%Q
           + Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q + (1 # 1)%Q))
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q + (1 # 1)%Q)
           + 2 * (q_pow (Qabs q) (2 * M) / q_fact (2 * M))%Q)%Q).
  - apply Qle_to_QleT'.
    assert (Heq2 : Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                         + (1 # 1)%Q)
                   == Qabs ((qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                             - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)
                            + (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q
                               + (1 # 1)%Q))%Q)
      by (apply Qabs_wd; ring).
    rewrite Heq2. apply Qabs_triangle.
  - assert (Hbrg : QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                              - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)%Q)
                           (Qabs (cos_partial (M + D) q - cos_partial M q))).
    { apply qeq_leT'.
      rewrite (lw0_sin_qp_deriv_eval (M + D) q).
      rewrite (lw0_sin_qp_deriv_eval M q). reflexivity. }
    assert (Hswap : QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                              - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)%Q
                        + Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q
                                + (1 # 1)%Q))
                       (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q
                              + (1 # 1)%Q)
                        + Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (M + D))) q
                               - qpoly_eval (qpoly_deriv (lw0_sin_qp M)) q)%Q)).
    { apply qeq_leT'. ring. }
    apply (qleT'_trans _ _ _ Hswap).
    apply qleT'_plus_compat.
    + apply qleT'_refl.
    + exact (qleT'_trans _ _ _ Hbrg Htail).
Qed.
Lemma leibsep_ratio_slot : forall (q : Q) (d0 : nat),
  QleT' (Qabs q) (lw0_q_of_nat d0) ->
  forall j : nat, (d0 <= j)%nat ->
  QleT' (2 * q_pow (Qabs q) 2)%Q
        (lw0_q_of_nat (Datatypes.S (2 * j))
         * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))%Q.
Proof.
  intros q d0 Habs j Hj.
  assert (Htwo : QleT' 0 2%Q).
  { apply Qle_to_QleT'. compute. discriminate. }
  assert (Hmono : QleT' (q_pow (Qabs q) 2) (q_pow (lw0_q_of_nat d0) 2)).
  { apply Qle_to_QleT'. apply q_pow_mono.
    - apply Qabs_nonneg.
    - apply QleT'_to_Qle. exact Habs. }
  assert (Hsq2 : q_pow (lw0_q_of_nat d0) 2 == lw0_q_of_nat d0 * lw0_q_of_nat d0).
  { cbn [q_pow]. ring. }
  assert (Hstep1 : QleT' (2 * q_pow (Qabs q) 2) (2 * q_pow (lw0_q_of_nat d0) 2)).
  { apply Qle_to_QleT'.
    rewrite (Qmult_comm 2 (q_pow (Qabs q) 2)).
    rewrite (Qmult_comm 2 (q_pow (lw0_q_of_nat d0) 2)).
    apply (Qmult_le_compat_r (q_pow (Qabs q) 2) (q_pow (lw0_q_of_nat d0) 2) 2%Q).
    - apply QleT'_to_Qle. exact Hmono.
    - apply QleT'_to_Qle. exact Htwo. }
  assert (Hstep2 : (2 * q_pow (lw0_q_of_nat d0) 2)%Q
                   == lw0_q_of_nat (2 * (d0 * d0))%nat).
  { rewrite Hsq2. change (2%Q) with (lw0_q_of_nat 2).
    rewrite (lw0_pitS_qof_mul 2 (d0 * d0)).
    rewrite (lw0_pitS_qof_mul d0 d0).
    reflexivity. }
  assert (Hstep3 : QleT' (lw0_q_of_nat (2 * (d0 * d0))%nat)
                         (lw0_q_of_nat (Datatypes.S (2 * j)
                                        * Datatypes.S (Datatypes.S (2 * j)))%nat)).
  { apply lw0_q_of_nat_le_mono.
    apply Nat.le_trans with (m := ((2 * j) * j)%nat).
    - apply Nat.le_trans with (m := (2 * (j * j))%nat).
      + apply Nat.mul_le_mono_l. exact (Nat.mul_le_mono d0 j d0 j Hj Hj).
      + rewrite (Nat.mul_assoc 2 j j). apply Nat.le_refl.
    - apply (Nat.mul_le_mono (2 * j) (Datatypes.S (2 * j)) j
               (Datatypes.S (Datatypes.S (2 * j)))).
      + apply Nat.le_succ_diag_r.
      + apply (Nat.le_trans j (2 * j) (Datatypes.S (Datatypes.S (2 * j)))).
        * replace (2 * j)%nat with (j + j)%nat
            by (cbn [Nat.mul]; rewrite Nat.add_0_r; reflexivity).
          apply Nat.le_add_l.
        * apply (Nat.le_trans (2 * j) (Datatypes.S (2 * j))
                  (Datatypes.S (Datatypes.S (2 * j)))).
          -- apply Nat.le_succ_diag_r.
          -- apply Nat.le_succ_diag_r. }
  apply (qleT'_trans _ (lw0_q_of_nat (2 * (d0 * d0))%nat) _).
  - apply (qleT'_trans _ (2 * q_pow (lw0_q_of_nat d0) 2)%Q _).
    + exact Hstep1.
    + apply qeq_leT'. exact Hstep2.
  - apply (qleT'_trans _ (lw0_q_of_nat (Datatypes.S (2 * j)
                                        * Datatypes.S (Datatypes.S (2 * j)))%nat) _).
    + exact Hstep3.
    + apply qeq_leT'. apply lw0_pitS_qof_mul.
Qed.
Lemma lw0_pitB_conv_sin_term_abs : forall (j : nat) (q : Q),
  QeqT (Qabs (sin_term j q))
       (q_pow (Qabs q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))).
Proof.
  intros j q. apply qeq_imp_qeqT. unfold sin_term, Qdiv.
  rewrite Qabs_Qmult, Qabs_Qmult.
  rewrite (qeqT_imp_qeq _ _ (lw0_pitB_conv_qabs_pow q (Datatypes.S (2 * j)))).
  rewrite (lw0_Qabs_pos_eq (Qinv (q_fact (Datatypes.S (2 * j)))))
    by (apply Qle_to_QleT'; apply Qinv_le_0_compat;
        apply (Qlt_le_weak 0%Q); apply q_fact_pos).
  destruct (lw0_pitB_conv_m1_cases j) as [b Hc]. destruct b;
    rewrite (qeqT_imp_qeq _ _ Hc); simpl; ring.
Qed.

Lemma lw0_pitB_conv_sin_tail : forall (q : Q) (M D : nat),
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  QleT' (Qabs (sin_partial (M + D) q - sin_partial M q))
        (2 * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))).
Proof.
  intros q M D Hr.
  assert (Hqnn : QleT' 0 (Qabs q))
    by (apply Qle_to_QleT'; apply Qabs_nonneg).
  (* sin_partial (S m) = sin_partial m + sin_term (S m): shift the whole
   Pd/w face by S (the Section 6.1 recipe). *)
  assert (Hhalf : forall j : nat, (M <= j)%nat ->
           QleT' (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S (Datatypes.S j)))
                   / q_fact (Datatypes.S (2 * Datatypes.S (Datatypes.S j))))
                 ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S j))
                            / q_fact (Datatypes.S (2 * Datatypes.S j))))).
  { intros j Hj.
    (* Normalize 2*S to the plain 2*j syntax (add does not reduce on
   symbolic variables; stay within one syntactic form). *)
    assert (E2j : (2 * Datatypes.S j)%nat = Datatypes.S (Datatypes.S (2 * j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * j) 1).
      rewrite (Nat.add_succ_r (2 * j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    assert (E2j2 : (2 * Datatypes.S (Datatypes.S j))%nat
                   = Datatypes.S (Datatypes.S (2 * Datatypes.S j))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * Datatypes.S j) 1).
      rewrite (Nat.add_succ_r (2 * Datatypes.S j) 0).
      rewrite Nat.add_0_r. reflexivity. }
    rewrite E2j2, E2j.
    apply (lw0_pitB_conv_tstep (Qabs q)
                 (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))).
    - exact Hqnn.
    - (* Hr: shift 2q^2 <= (2j+1)*(2j+2) up two steps to (2j+4)*(2j+5)
   (pure 2*j syntax). *)
      apply (qleT'_trans (2 * q_pow (Qabs q) 2)
                         (lw0_q_of_nat (Datatypes.S (2 * j))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
      + exact (Hr j Hj).
      + apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
        * apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (2 * j)))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
          -- apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (2 * j))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (2 * j)))
                             (Qmult_comm (lw0_q_of_nat (Datatypes.S (2 * j)))
                                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))))).
          -- apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                       (lw0_q_of_nat (Datatypes.S (2 * j)))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
             ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * j)))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
                ** apply lw0_q_of_nat_le_succ.
                ** apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))).
                   --- apply lw0_q_of_nat_le_succ.
                   --- apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_nonneg.
        * apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
          -- apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                             (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                              * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                             (Qmult_comm (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
          -- apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                       (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
             ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                                   (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
                ** apply lw0_q_of_nat_le_succ.
                ** apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j))))))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S (2 * j)))))))).
                   --- apply lw0_q_of_nat_le_succ.
                   --- apply lw0_q_of_nat_le_succ.
             ++ apply lw0_q_of_nat_nonneg. }
  assert (HhalfM : QleT' (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S M))
                            / q_fact (Datatypes.S (2 * Datatypes.S M)))
                         ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                    / q_fact (Datatypes.S (2 * M))))).
  { assert (E2M : (2 * Datatypes.S M)%nat = Datatypes.S (Datatypes.S (2 * M))).
    { rewrite Nat.mul_succ_r.
      rewrite (Nat.add_succ_r (2 * M) 1).
      rewrite (Nat.add_succ_r (2 * M) 0).
      rewrite Nat.add_0_r. reflexivity. }
    rewrite E2M.
    apply (lw0_pitB_conv_tstep (Qabs q) (Datatypes.S (2 * M))).
    - exact Hqnn.
    - (* Hr M: shift 2q^2 <= (2M+1)*(2M+2) up one step to (2M+2)*(2M+3)
   (pure 2*M syntax). *)
      apply (qleT'_trans (2 * q_pow (Qabs q) 2)
                         (lw0_q_of_nat (Datatypes.S (2 * M))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                         (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))
                          * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
      + exact (Hr M (Nat.le_refl M)).
      + apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * M))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))
                            * lw0_q_of_nat (Datatypes.S (2 * M)))
                           (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))
                            * lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
        * apply (qeq_leT' (lw0_q_of_nat (Datatypes.S (2 * M))
                           * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                          (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))
                           * lw0_q_of_nat (Datatypes.S (2 * M)))
                          (Qmult_comm (lw0_q_of_nat (Datatypes.S (2 * M)))
                                      (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M)))))).
        * apply (lw0_pitB_conv_mult_le_l (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                     (lw0_q_of_nat (Datatypes.S (2 * M)))
                     (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
           ++ apply (qleT'_trans (lw0_q_of_nat (Datatypes.S (2 * M)))
                                 (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * M))))
                                 (lw0_q_of_nat (Datatypes.S (Datatypes.S (Datatypes.S (2 * M)))))).
              ** apply lw0_q_of_nat_le_succ.
              ** apply lw0_q_of_nat_le_succ.
           ++ apply lw0_q_of_nat_nonneg. }
  assert (Ec2h : QeqT (2%Q * (1#2))%Q 1%Q) by (unfold QeqT; cbn; reflexivity).
  apply (qleT'_trans (Qabs (sin_partial (M + D) q - sin_partial M q))
                     (2%Q * ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                               / q_fact (Datatypes.S (2 * M)))))
                     (2 * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))).
  - apply (qleT'_trans (Qabs (sin_partial (M + D) q - sin_partial M q))
                       (2%Q * (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S M))
                                 / q_fact (Datatypes.S (2 * Datatypes.S M))))
                       (2%Q * ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                          / q_fact (Datatypes.S (2 * M)))))).
    + apply (lw0_pitB_conv_tail_gen (fun n => sin_partial n q)
                                    (fun n => sin_term (Datatypes.S n) q)
                                    (fun n => q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S n))
                                                / q_fact (Datatypes.S (2 * Datatypes.S n)))
                                    D M).
      * intros n. reflexivity.
      * intros n. exact (qeqT_imp_qeq _ _ (lw0_pitB_conv_sin_term_abs (Datatypes.S n) q)).
      * intros n. apply lw0_pitB_conv_t_nonneg. exact Hqnn.
      * intros j Hj. exact (Hhalf j Hj).
    + apply (lw0_pitB_conv_mult_le_l 2%Q
               (q_pow (Qabs q) (Datatypes.S (2 * Datatypes.S M))
                 / q_fact (Datatypes.S (2 * Datatypes.S M)))
               ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                          / q_fact (Datatypes.S (2 * M)))) HhalfM).
      unfold QleT'. reflexivity.
  - apply (qleT'_trans (2%Q * ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                          / q_fact (Datatypes.S (2 * M)))))
                       (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                       (2 * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))).
    + apply (qeq_leT' (2%Q * ((1#2) * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                        / q_fact (Datatypes.S (2 * M)))))
                      (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))).
      rewrite (Qmult_assoc 2%Q (1#2) (q_pow (Qabs q) (Datatypes.S (2 * M))
                                          / q_fact (Datatypes.S (2 * M)))).
      rewrite (qeqT_imp_qeq _ _ Ec2h).
      apply (Qmult_1_l (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))).
    + apply (qleT'_trans (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                         (1%Q * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
                         (2 * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))).
      * apply (qeq_leT' (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M)))
                        (1%Q * (q_pow (Qabs q) (Datatypes.S (2 * M)) / q_fact (Datatypes.S (2 * M))))
                        (Qeq_sym _ _ (Qmult_1_l (q_pow (Qabs q) (Datatypes.S (2 * M))
                                              / q_fact (Datatypes.S (2 * M)))))).
      * apply Qle_to_QleT'. apply Qmult_le_compat_r.
        -- assert (H12 : QltT 1%Q 2%Q) by (unfold QltT, Qlt_bool; reflexivity).
           exact (Qlt_le_weak 1%Q 2%Q (QltT_to_Qlt 1%Q 2%Q H12)).
        -- exact (QleT'_to_Qle _ _
                    (lw0_pitB_conv_t_nonneg (Qabs q) (Datatypes.S (2 * M)) Hqnn)).
Qed.
Lemma leibsep_sin_qp_tail_stable : forall (q : Q) (M D : nat),
  (forall j : nat, (M <= j)%nat ->
     QleT' (2 * q_pow (Qabs q) 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))) ->
  QleT' (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q))
        (Qabs (qpoly_eval (lw0_sin_qp M) q)
         + 2 * (q_pow (Qabs q) (Datatypes.S (2 * M))
                / q_fact (Datatypes.S (2 * M)))%Q)%Q.
Proof.
  intros q M D Hr.
  pose proof (lw0_pitB_conv_sin_tail q M D Hr) as Htail.
  assert (Htri : QleT' (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q))
                       (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                              - qpoly_eval (lw0_sin_qp M) q)%Q
                        + Qabs (qpoly_eval (lw0_sin_qp M) q))).
  { apply Qle_to_QleT'.
    assert (Ht2 : Qle (Qabs ((qpoly_eval (lw0_sin_qp (M + D)) q
                              - qpoly_eval (lw0_sin_qp M) q)%Q
                             + qpoly_eval (lw0_sin_qp M) q))
                      (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                             - qpoly_eval (lw0_sin_qp M) q)%Q
                       + Qabs (qpoly_eval (lw0_sin_qp M) q)))
      by apply Qabs_triangle.
    assert (Heq : (qpoly_eval (lw0_sin_qp (M + D)) q
                   - qpoly_eval (lw0_sin_qp M) q)%Q
                  + qpoly_eval (lw0_sin_qp M) q
                  == qpoly_eval (lw0_sin_qp (M + D)) q) by ring.
    rewrite Heq in Ht2. exact Ht2. }
  assert (Hbrg : QleT' (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                              - qpoly_eval (lw0_sin_qp M) q)%Q)
                       (Qabs (sin_partial (M + D) q - sin_partial M q))).
  { apply qeq_leT'.
    rewrite (lw0_sin_qp_eval (M + D) q). rewrite (lw0_sin_qp_eval M q).
    reflexivity. }
  assert (Hswap : QleT' (Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                              - qpoly_eval (lw0_sin_qp M) q)%Q
                        + Qabs (qpoly_eval (lw0_sin_qp M) q))
                       (Qabs (qpoly_eval (lw0_sin_qp M) q)
                        + Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                               - qpoly_eval (lw0_sin_qp M) q)%Q)).
  { apply qeq_leT'. ring. }
  assert (Hstep : QleT' (Qabs (qpoly_eval (lw0_sin_qp M) q)
                         + Qabs (qpoly_eval (lw0_sin_qp (M + D)) q
                                - qpoly_eval (lw0_sin_qp M) q)%Q)
                        (Qabs (qpoly_eval (lw0_sin_qp M) q)
                         + 2 * (q_pow (Qabs q) (Datatypes.S (2 * M))
                                / q_fact (Datatypes.S (2 * M)))%Q)).
  { apply qleT'_plus_compat.
    - apply qleT'_refl.
    - exact (qleT'_trans _ _ _ Hbrg Htail). }
  exact (qleT'_trans _ _ _ Htri (qleT'_trans _ _ _ Hswap Hstep)).
Qed.
Lemma lw62_qdiv_nonneg : forall a b : Q,
  QleT' 0 a -> Qlt 0 b -> QleT' 0 (a / b).
Proof.
  intros a b Ha Hb. apply Qle_to_QleT'. unfold Qdiv.
  apply (Qle_trans _ (0 * / b)%Q).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply Qmult_le_compat_r.
    + exact (QleT'_to_Qle _ _ Ha).
    + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hb.
Qed.
Lemma lw95_mul0 : forall x y : Q,
  Qle 0 x -> Qle 0 y -> Qle 0 (x * y).
Proof.
  intros x y Hx Hy.
  apply (Qle_trans 0 (0 * y) (x * y)).
  - rewrite Qmult_0_l. apply Qle_refl.
  - apply Qmult_le_compat_r; assumption.
Qed.

Lemma lw95_qpow_nonneg : forall (x : Q) (m : nat),
  Qle 0 x -> Qle 0 (q_pow x m).
Proof.
  intros x m Hx. induction m as [|m IHm].
  - change (q_pow x 0) with 1%Q. compute. discriminate.
  - rewrite q_pow_succ. apply lw95_mul0; assumption.
Qed.

Lemma lw1131_abssum_cos_nonneg : forall (B : Q) (n : nat),
  Qle 0 B -> Qle 0 (leibsep_abssum_cos B n).
Proof.
  intros B n HB. induction n as [| n IHn].
  - simpl. apply Qle_refl.
  - simpl leibsep_abssum_cos.
    apply (Qle_trans 0 (leibsep_abssum_cos B n)
             (leibsep_abssum_cos B n
              + B * q_pow B (n + (n + 0))
                / ((Z.pos (PosDef.Pos.of_succ_nat (n + (n + 0))) # 1)
                   * q_fact (n + (n + 0))))%Q); [exact IHn |].
    apply (Qle_trans (leibsep_abssum_cos B n)
             (leibsep_abssum_cos B n + 0)%Q
             (leibsep_abssum_cos B n
              + B * q_pow B (n + (n + 0))
                / ((Z.pos (PosDef.Pos.of_succ_nat (n + (n + 0))) # 1)
                   * q_fact (n + (n + 0))))%Q).
    * rewrite Qplus_0_r. apply Qle_refl.
    * apply (Qplus_le_compat (leibsep_abssum_cos B n) (leibsep_abssum_cos B n) 0
               (B * q_pow B (n + (n + 0))
                / ((Z.pos (PosDef.Pos.of_succ_nat (n + (n + 0))) # 1)
                   * q_fact (n + (n + 0))))%Q).
      -- apply Qle_refl.
      -- apply QleT'_to_Qle.
         apply (lw62_qdiv_nonneg _ ((Z.pos (PosDef.Pos.of_succ_nat (n + (n + 0))) # 1)
                                    * q_fact (n + (n + 0)))%Q).
         { apply Qle_to_QleT'. apply Qmult_le_0_compat.
           - exact HB.
           - apply lw95_qpow_nonneg. exact HB. }
         { apply Qmult_lt_0_compat.
           - exact (q_lt_0_succ_den (n + (n + 0))).
           - apply q_fact_pos. }
Qed.
Lemma lw62_qpow_abs : forall (B : Q) (k : nat),
  Qabs (q_pow B k) == q_pow (Qabs B) k.
Proof.
  intros B k. induction k as [|k IHk].
  - reflexivity.
  - rewrite q_pow_succ, q_pow_succ, Qabs_Qmult, IHk. reflexivity.
Qed.

Lemma lw62_cos_term_dom : forall (B : Q) (m : nat),
  Qle (q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))%nat)%Q
      (q_pow (Qabs B) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))%nat)%Q.
Proof.
  intros B m. unfold Qdiv.
  apply Qmult_le_compat_r.
  - apply QleT'_to_Qle.
    apply (qleT'_trans _ (Qabs (q_pow B (Datatypes.S (2 * m))))).
    + apply leibsep_abs_ge_self.
    + apply qeq_leT'. apply lw62_qpow_abs.
  - apply Qlt_le_weak. apply Qinv_lt_0_compat. apply q_fact_pos.
Qed.

Lemma lw62_abssum_cos_dom : forall (B : Q) (n : nat),
  Qle (leibsep_abssum_cos B n) (leibsep_abssum_cos (Qabs B) n).
Proof.
  intros B n. induction n as [|n IHn].
  - simpl leibsep_abssum_cos. apply Qle_refl.
  - simpl leibsep_abssum_cos.
    apply Qplus_le_compat.
    + exact IHn.
    + apply lw62_cos_term_dom.
Qed.

Lemma lw62_abssum_S : forall (B : Q) (n : nat),
  leibsep_abssum B (Datatypes.S n)
  == leibsep_abssum B n
     + q_pow B (2 * Datatypes.S n) / q_fact (2 * Datatypes.S n)%nat.
Proof. intros B n. reflexivity. Qed.

(* Nonnegativity of the sum (even powers are nonnegative term by term). *)
Lemma lw62_qdiv_den_id : forall x y z : Q,
  Qlt 0 y -> Qlt 0 z -> (x / y == x * z * (/ (y * z)))%Q.
Proof.
  intros x y z Hy Hz.
  assert (Hz0 : (~ z == 0)%Q)
    by (intro Hc; apply (Qlt_not_eq 0 z Hz); symmetry; exact Hc).
  unfold Qdiv.
  rewrite (Qinv_mult_distr y z), <- (Qmult_assoc x z (/ y * / z)),
          (Qmult_assoc z (/ y) (/ z)), (Qmult_comm z (/ y)),
          <- (Qmult_assoc (/ y) z (/ z)), (Qmult_inv_r z Hz0), Qmult_1_r.
  reflexivity.
Qed.

Lemma lw62_qdiv_le : forall a b c d : Q,
  Qlt 0 b -> Qlt 0 d -> Qle (a * d) (c * b) -> Qle (a / b) (c / d).
Proof.
  intros a b c d Hb Hd Hle.
  assert (Hbd : Qlt 0 (b * d)%Q) by (apply Qmult_lt_0_compat; assumption).
  assert (Hinv : Qle 0 (/ (b * d))%Q).
  { apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hbd. }
  assert (Hdb : Qlt 0 (d * b)%Q) by (apply Qmult_lt_0_compat; [exact Hd | exact Hb]).
  assert (Heq1 : (a / b)%Q == (a * d * (/ (b * d)))%Q)
    by (apply lw62_qdiv_den_id; assumption).
  assert (Heq2 : (c / d)%Q == (c * b * (/ (b * d)))%Q).
  { rewrite (Qmult_comm b d).
    apply lw62_qdiv_den_id; assumption. }
  rewrite Heq1. apply (Qle_trans _ (c * b * (/ (b * d)))%Q).
  - apply Qmult_le_compat_r; assumption.
  - rewrite Heq2. apply Qle_refl.
Qed.
Lemma lw95_qfact_mono : forall (d i : nat), Qle (q_fact i) (q_fact (i + d)%nat).
Proof.
  induction d as [|d IHd]; intros i.
  - rewrite <- plus_n_O. apply Qle_refl.
  - rewrite <- (plus_n_Sm i d).
    apply (Qle_trans (q_fact i) (q_fact (i + d)%nat)
                     (q_fact (Datatypes.S (i + d)))).
    + apply IHd.
    + pose proof (q_fact_succ (i + d)%nat) as Hs.
      rewrite Hs.
      apply (Qle_trans _ (1 * q_fact (i + d)) _).
      * rewrite Qmult_1_l. apply Qle_refl.
      * apply Qmult_le_compat_r.
        -- unfold Qle. cbn [Qnum Qden]. apply Z.leb_le.
           rewrite !Z.mul_1_r.
           apply (proj2 (Z.leb_le _ _)).
           assert (Hn : (1 <= Datatypes.S (i + d))%nat)
             by (apply le_n_S; apply Nat.le_0_l).
           exact (proj1 (Nat2Z.inj_le 1 (Datatypes.S (i + d))) Hn).
        -- apply Qlt_le_weak. apply q_fact_pos.
Qed.


(* The odd subsequence of partial sums stays nonnegative: lp_odd m >= lp_pair 0 >= 0. *)
Lemma lw95_qfact_le : forall (a b : nat), (a <= b)%nat -> Qle (q_fact a) (q_fact b).
Proof.
  intros a b Hle.
  assert (Heq : (a + (b - a))%nat = b).
  { rewrite Nat.add_comm. apply Nat.sub_add. exact Hle. }
  rewrite <- Heq.
  apply lw95_qfact_mono.
Qed.

Lemma lw62_abssum_cos_le : forall (B : Q) (n : nat),
  Qle 0 B -> Qle (leibsep_abssum_cos B n) (B * leibsep_abssum B n)%Q.
Proof.
  intros B n HB.
  assert (Haux : forall m : nat,
    Qle (leibsep_abssum_cos B m
         + q_pow B (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m))%nat)%Q
        (B * leibsep_abssum B m)%Q).
  { intro m. induction m as [|m IHm].
    - apply qeq_imp_qle. cbn [leibsep_abssum_cos leibsep_abssum q_pow q_fact].
      unfold Qdiv. cbn. ring.
    - simpl leibsep_abssum_cos.
      apply (Qle_trans _ ((B * leibsep_abssum B m
                           + q_pow B (Datatypes.S (2 * Datatypes.S m))
                             / q_fact (2 * Datatypes.S m)%nat))%Q).
      + apply Qplus_le_compat.
        * exact IHm.
        * apply (lw62_qdiv_le (q_pow B (Datatypes.S (2 * Datatypes.S m)))
                              (q_fact (Datatypes.S (2 * Datatypes.S m)))
                              (q_pow B (Datatypes.S (2 * Datatypes.S m)))
                              (q_fact (2 * Datatypes.S m))).
          -- apply q_fact_pos.
          -- apply q_fact_pos.
          -- rewrite (Qmult_comm (q_pow B (Datatypes.S (2 * Datatypes.S m)))
                                 (q_fact (2 * Datatypes.S m))),
                     (Qmult_comm (q_pow B (Datatypes.S (2 * Datatypes.S m)))
                                 (q_fact (Datatypes.S (2 * Datatypes.S m)))).
             apply Qmult_le_compat_r.
             ++ apply lw95_qfact_le. apply Nat.le_succ_diag_r.
             ++ apply lw95_qpow_nonneg. exact HB.
      + apply qeq_imp_qle. rewrite (lw62_abssum_S B m).
        rewrite q_pow_succ. unfold Qdiv. ring. }
  apply (Qle_trans _ (leibsep_abssum_cos B n
                      + q_pow B (Datatypes.S (2 * n)) / q_fact (Datatypes.S (2 * n))%nat)%Q).
  - apply (Qle_trans _ (leibsep_abssum_cos B n + 0)%Q).
    + apply qeq_le. rewrite Qplus_0_r. reflexivity.
    + apply Qplus_le_compat; [apply Qle_refl |].
      apply (QleT'_to_Qle 0 (q_pow B (Datatypes.S (2 * n))
                             / q_fact (Datatypes.S (2 * n))%nat)%Q).
      apply lw62_qdiv_nonneg.
      * apply Qle_to_QleT'. apply lw95_qpow_nonneg. exact HB.
      * apply q_fact_pos.
  - apply Haux.
Qed.

Lemma lw62_zsquare_nonneg : forall n : Z, (0 <= n * n)%Z.
Proof.
  intros n.
  assert (Htri : (n = 0 \/ 0 < n \/ n < 0)%Z).
  { destruct (Z.lt_trichotomy n 0) as [Hlt | [Heq | Hgt]].
    - right; right; exact Hlt.
    - left; exact Heq.
    - right; left; exact Hgt. }
  destruct Htri as [H0 | Hrest].
  - rewrite H0. apply Z.le_refl.
  - destruct Hrest as [Hpos | Hneg].
    + apply Z.mul_nonneg_nonneg; apply Z.lt_le_incl; exact Hpos.
    + assert (Hnn : (0 <= - n)%Z).
      { pose proof (proj1 (Z.opp_lt_mono n 0) Hneg) as H0n.
        rewrite Z.opp_0 in H0n. apply Z.lt_le_incl. exact H0n. }
      replace (n * n)%Z with ((- n) * (- n))%Z by ring.
      apply Z.mul_nonneg_nonneg; assumption.
Qed.

Lemma lw62_sq_nonneg : forall x : Q, Qle 0 (x * x).
Proof.
  intros [nx dx]. unfold Qle. simpl.
  rewrite Z.mul_1_r.
  apply lw62_zsquare_nonneg.
Qed.

Lemma lw62_qpow_even_nonneg : forall (x : Q) (j : nat),
  QleT' 0 (q_pow x (2 * j)%nat).
Proof.
  intros x j. induction j as [|j IHj].
  - apply Qle_to_QleT'. compute. intro Hc. discriminate Hc.
  - replace (2 * Datatypes.S j)%nat
      with (Datatypes.S (Datatypes.S (2 * j)))
      by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r; reflexivity).
    apply Qle_to_QleT'.
    rewrite q_pow_succ, q_pow_succ.
    rewrite (Qmult_assoc x x (q_pow x (2 * j))).
    apply lw95_mul0.
    + apply lw62_sq_nonneg.
    + apply QleT'_to_Qle. exact IHj.
Qed.

Lemma lw62_abssum_step_mono : forall (B : Q) (k : nat),
  QleT' (leibsep_abssum B k) (leibsep_abssum B (Datatypes.S k)).
Proof.
  intros B k.
  pose proof (QleT'_to_Qle _ _ (lw62_qdiv_nonneg
                  (q_pow B (2 * Datatypes.S k)) (q_fact (2 * Datatypes.S k))
                  (lw62_qpow_even_nonneg B (Datatypes.S k))
                  (q_fact_pos (2 * Datatypes.S k)))) as Hterm.
  apply (qleT'_trans (leibsep_abssum B k)
                     (leibsep_abssum B k + 0%Q)%Q
                     (leibsep_abssum B k
                      + (q_pow B (2 * Datatypes.S k) / q_fact (2 * Datatypes.S k))%Q)%Q).
  - apply qeq_leT'. ring.
  - apply qleT'_plus_compat.
    + apply qleT'_refl.
    + apply Qle_to_QleT'. exact Hterm.
Qed.

Lemma lw62_abssum_mono : forall (B : Q) (n m : nat),
  (n <= m)%nat -> QleT' (leibsep_abssum B n) (leibsep_abssum B m).
Proof.
  intros B n m Hle. induction m as [|m IHm].
  - assert (Hn : n = 0%nat).
    { apply Nat.le_antisymm; [exact Hle | apply Nat.le_0_l]. }
    subst n. apply qleT'_refl.
  - destruct (Nat.eq_dec n (Datatypes.S m)) as [Heq|Hne].
    + rewrite Heq. apply qleT'_refl.
    + assert (Hnm : (n <= m)%nat).
      { destruct (Nat.lt_trichotomy (Datatypes.S m) n) as [Hgt | [Heq2 | Hlt]].
        - exfalso. apply (Nat.lt_irrefl n).
          exact (Nat.le_lt_trans n (Datatypes.S m) n Hle Hgt).
        - exfalso. apply Hne. symmetry. exact Heq2.
        - apply (proj1 (Nat.lt_succ_r n m)). exact Hlt. }
      apply (qleT'_trans _ (leibsep_abssum B m)).
      * exact (IHm Hnm).
      * apply lw62_abssum_step_mono.
Qed.

Lemma lw62_q30_pos : Qlt 0 (30 # 1)%Q.
Proof. compute. reflexivity. Qed.

Lemma lw95_mul_le_compat : forall w x y z : Q,
  Qle 0 w -> Qle w x -> Qle 0 y -> Qle y z -> Qle (w * y) (x * z).
Proof.
  intros w x y z Hw0 Hwx Hy0 Hyz.
  apply (Qle_trans (w * y) (x * y) (x * z)).
  - apply Qmult_le_compat_r; assumption.
  - rewrite (Qmult_comm x y), (Qmult_comm x z).
    apply Qmult_le_compat_r;
      [exact Hyz | exact (Qle_trans 0 w x Hw0 Hwx)].
Qed.

Lemma lw62_georatio : forall m : nat,
  QleT' ((24 # 1) * q_pow (30 # 1) m)%Q (q_fact (2 * m + 4)%nat).
Proof.
  induction m as [|m IHm].
  - apply Qle_to_QleT'. compute. intro Hc. discriminate Hc.
  - apply Qle_to_QleT'.
    replace (2 * Datatypes.S m + 4)%nat
      with (Datatypes.S (Datatypes.S (2 * m + 4)))
      by (symmetry; rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_succ_r, <- Nat.add_assoc; reflexivity).
    rewrite q_fact_succ, q_fact_succ.
    apply (Qle_trans _ ((30 # 1) * ((24 # 1) * q_pow (30 # 1) m))%Q).
    + rewrite q_pow_succ. apply qeq_imp_qle. ring.
    + apply (Qle_trans _ ((30 # 1) * q_fact (2 * m + 4))%Q).
      * rewrite (Qmult_comm (30 # 1) ((24 # 1) * q_pow (30 # 1) m)),
                (Qmult_comm (30 # 1) (q_fact (2 * m + 4))).
        apply Qmult_le_compat_r.
        -- apply QleT'_to_Qle. exact IHm.
        -- apply Qlt_le_weak. apply lw62_q30_pos.
      * rewrite Qmult_assoc.
        apply (lw95_mul_le_compat (30 # 1)
                 ((Z.of_nat (Datatypes.S (Datatypes.S (2 * m + 4))) # 1)
                  * (Z.of_nat (Datatypes.S (2 * m + 4)) # 1))
                 (q_fact (2 * m + 4)) (q_fact (2 * m + 4))).
        -- apply Qlt_le_weak. apply lw62_q30_pos.
        -- apply (Qle_trans _ ((6 # 1) * (5 # 1))%Q).
           ++ compute. intro Hc. discriminate Hc.
           ++ apply (lw95_mul_le_compat (6 # 1)
                       (Z.of_nat (Datatypes.S (Datatypes.S (2 * m + 4))) # 1)
                       (5 # 1)
                       (Z.of_nat (Datatypes.S (2 * m + 4)) # 1)).
              ** compute. discriminate.
              ** unfold Qle. cbn [Qnum Qden]. apply Z.leb_le.
                 rewrite !Z.mul_1_r.
                 apply (proj2 (Z.leb_le _ _)).
                 replace (2 * m + 4)%nat with (4 + 2 * m)%nat
                   by (rewrite Nat.add_comm; reflexivity).
                 change (Datatypes.S (Datatypes.S (4 + 2 * m))) with (6 + 2 * m)%nat.
                 assert (Hn : (6 <= 6 + 2 * m)%nat) by apply Nat.le_add_r.
                 exact (proj1 (Nat2Z.inj_le 6 (6 + 2 * m)) Hn).
              ** compute. discriminate.
              ** unfold Qle. cbn [Qnum Qden]. apply Z.leb_le.
                 rewrite !Z.mul_1_r.
                 apply (proj2 (Z.leb_le _ _)).
                 replace (2 * m + 4)%nat with (4 + 2 * m)%nat
                   by (rewrite Nat.add_comm; reflexivity).
                 change (Datatypes.S (4 + 2 * m)) with (5 + 2 * m)%nat.
                 assert (Hn : (5 <= 5 + 2 * m)%nat) by apply Nat.le_add_r.
                 exact (proj1 (Nat2Z.inj_le 5 (5 + 2 * m)) Hn).
        -- apply Qlt_le_weak. apply q_fact_pos.
        -- apply Qle_refl.
Qed.

Lemma lw62_qpow_add : forall (x : Q) (n m : nat),
  q_pow x (n + m)%nat == q_pow x n * q_pow x m.
Proof.
  intros x n m. induction n as [|n IHn].
  - cbn [q_pow]. rewrite Nat.add_0_l, Qmult_1_l. reflexivity.
  - replace (Datatypes.S n + m)%nat with (Datatypes.S (n + m))
      by apply Nat.add_succ_l.
    rewrite q_pow_succ, q_pow_succ, IHn. ring.
Qed.

Lemma lw65_qdiv_le_prod : forall a b c : Q,
  Qlt 0 b -> Qle a (c * b) -> Qle (a / b) c.
Proof.
  intros a b c Hb Hle. unfold Qdiv.
  assert (Hz : (~ b == 0)%Q)
    by (intro Hc; apply (Qlt_not_eq 0 b Hb); symmetry; exact Hc).
  apply (Qle_trans _ ((c * b) * / b)%Q).
  - apply Qmult_le_compat_r.
    + exact Hle.
    + apply Qlt_le_weak. apply Qinv_lt_0_compat. exact Hb.
  - rewrite <- (Qmult_assoc c b (/ b)), (Qmult_inv_r b Hz), Qmult_1_r.
    apply Qle_refl.
Qed.

Lemma lw65_qpow_inv_pair : forall (x : Q) (k : nat),
  (~ x == 0)%Q -> q_pow x k * q_pow (/ x) k == 1%Q.
Proof.
  intros x k Hx0. induction k as [|k IHk].
  - reflexivity.
  - rewrite (q_pow_succ x k), (q_pow_succ (/ x) k).
    rewrite <- (Qmult_assoc x (q_pow x k) (/ x * q_pow (/ x) k)).
    rewrite (Qmult_comm (q_pow x k) (/ x * q_pow (/ x) k)).
    rewrite <- (Qmult_assoc (/ x) (q_pow (/ x) k) (q_pow x k)).
    rewrite (Qmult_assoc x (/ x) (q_pow (/ x) k * q_pow x k)).
    rewrite (Qmult_inv_r x Hx0), Qmult_1_l.
    rewrite (Qmult_comm (q_pow (/ x) k) (q_pow x k)).
    exact IHk.
Qed.

Lemma lw65_qpow_mul : forall (u v : Q) (k : nat),
  q_pow (u * v) k == (q_pow u k * q_pow v k)%Q.
Proof.
  intros u v k. induction k as [|k IHk].
  - reflexivity.
  - rewrite q_pow_succ, (q_pow_succ u k), (q_pow_succ v k), IHk. ring.
Qed.

Lemma lw62_item_dom : forall (B : Q) (n : nat),
  Qle (q_pow B (2 * Datatypes.S (Datatypes.S (Datatypes.S n)))
       / q_fact (2 * Datatypes.S (Datatypes.S (Datatypes.S n)))%nat)%Q
      (B * B * B * B * (1 # 24)
       * q_pow (B * B * (1 # 30)) (Datatypes.S n))%Q.
Proof.
  intros B n.
  assert (Hgeo := lw62_georatio (Datatypes.S n)).
  assert (Hid : (2 * Datatypes.S n + 4)%nat
              = (2 * Datatypes.S (Datatypes.S (Datatypes.S n)))%nat).
  { repeat rewrite Nat.mul_succ_r. repeat rewrite <- Nat.add_assoc. reflexivity. }
  rewrite Hid in Hgeo.
  assert (Ha : q_pow B (2 * Datatypes.S (Datatypes.S (Datatypes.S n)))%nat
             == (B * B * B * B * q_pow B (2 * Datatypes.S n))%Q).
  { assert (H4 : q_pow B (2 * 2)%nat == (B * B * B * B)%Q).
    { change (2 * 2)%nat with 4%nat.
      cbn [q_pow]. ring. }
    replace (2 * Datatypes.S (Datatypes.S (Datatypes.S n)))%nat
      with (2 * 2 + 2 * Datatypes.S n)%nat
      by (assert (H2n : forall k : nat, (2 * k)%nat = (k + k)%nat)
            by (intro k; destruct k as [|k]; [reflexivity | simpl; rewrite Nat.add_0_r; reflexivity]);
          repeat rewrite Nat.mul_succ_r;
          repeat rewrite Nat.add_succ_r;
          repeat rewrite Nat.add_0_r;
          rewrite H2n; reflexivity).
    rewrite lw62_qpow_add, H4. reflexivity. }
  assert (HW : q_pow B (2 * Datatypes.S n)%nat
             == (q_pow B (Datatypes.S n) * q_pow B (Datatypes.S n))%Q).
  { replace (2 * Datatypes.S n)%nat
      with (Datatypes.S n + Datatypes.S n)%nat
      by (assert (H2n : forall k : nat, (2 * k)%nat = (k + k)%nat)
            by (intro k; destruct k as [|k]; [reflexivity | simpl; rewrite Nat.add_0_r; reflexivity]);
          repeat rewrite Nat.mul_succ_r;
          repeat rewrite Nat.add_succ_r;
          repeat rewrite Nat.add_0_r;
          rewrite H2n; reflexivity).
    apply lw62_qpow_add. }
  assert (Hpsplit : q_pow (B * B * (1 # 30))%Q (Datatypes.S n)
                 == (q_pow B (Datatypes.S n) * q_pow B (Datatypes.S n)
                     * q_pow (1 # 30)%Q (Datatypes.S n))%Q).
  { rewrite lw65_qpow_mul, (lw65_qpow_mul B B (Datatypes.S n)). reflexivity. }
  assert (Hne30 : (~ (30 # 1) == 0)%Q).
  { intro Hc. apply (Qlt_not_eq 0 (30 # 1) lw62_q30_pos). symmetry. exact Hc. }
  assert (Hp130 : q_pow (30 # 1)%Q (Datatypes.S n) * q_pow (1 # 30)%Q (Datatypes.S n)
                == 1%Q).
  { change (q_pow (1 # 30)%Q (Datatypes.S n))
      with (q_pow (/ (30 # 1))%Q (Datatypes.S n)).
    exact (lw65_qpow_inv_pair (30 # 1) (Datatypes.S n) Hne30). }
  assert (H24 : ((1 # 24) * (24 # 1))%Q == 1%Q) by reflexivity.
  assert (Hpair : ((24 # 1) * q_pow (30 # 1)%Q (Datatypes.S n)
                   * ((1 # 24) * q_pow (1 # 30)%Q (Datatypes.S n)))%Q == 1%Q).
  { rewrite <- (Qmult_assoc (24 # 1) (q_pow (30 # 1) (Datatypes.S n))
                  ((1 # 24) * q_pow (1 # 30) (Datatypes.S n))).
    rewrite (Qmult_assoc (q_pow (30 # 1) (Datatypes.S n)) (1 # 24)
                         (q_pow (1 # 30) (Datatypes.S n))).
    rewrite (Qmult_comm (q_pow (30 # 1) (Datatypes.S n)) (1 # 24)).
    rewrite <- (Qmult_assoc (1 # 24) (q_pow (30 # 1) (Datatypes.S n))
                            (q_pow (1 # 30) (Datatypes.S n))).
    rewrite (Qmult_assoc (24 # 1) (1 # 24)
                         (q_pow (30 # 1) (Datatypes.S n)
                          * q_pow (1 # 30) (Datatypes.S n))).
    rewrite H24, Hp130. apply Qmult_1_l. }
  assert (Htgt
    : (B * B * B * B * (1 # 24)
       * (q_pow B (Datatypes.S n) * q_pow B (Datatypes.S n)
          * q_pow (1 # 30) (Datatypes.S n)))
      * q_fact (2 * Datatypes.S (Datatypes.S (Datatypes.S n)))
      == (B * B * B * B)
         * ((1 # 24) * q_pow (1 # 30) (Datatypes.S n)
            * q_fact (2 * Datatypes.S (Datatypes.S (Datatypes.S n)))
            * (q_pow B (Datatypes.S n) * q_pow B (Datatypes.S n)))).
  { ring. }
  rewrite Ha, Hpsplit, HW.
  apply lw65_qdiv_le_prod.
  - apply q_fact_pos.
  - rewrite Htgt.
    apply (lw95_mul_le_compat (B * B * B * B) (B * B * B * B)
             (q_pow B (Datatypes.S n) * q_pow B (Datatypes.S n))
             ((1 # 24) * q_pow (1 # 30) (Datatypes.S n)
              * q_fact (2 * Datatypes.S (Datatypes.S (Datatypes.S n)))
              * (q_pow B (Datatypes.S n) * q_pow B (Datatypes.S n)))).
    + apply (Qle_trans _ ((B * B) * (B * B))%Q).
      * apply lw95_mul0; [apply lw62_sq_nonneg | apply lw62_sq_nonneg].
      * apply qeq_imp_qle. ring.
    + apply Qle_refl.
    + apply lw62_sq_nonneg.
    + apply (Qle_trans _ ((1 # 1)
                * (q_pow B (Datatypes.S n) * q_pow B (Datatypes.S n)))%Q).
      * rewrite Qmult_1_l. apply Qle_refl.
      * apply Qmult_le_compat_r.
        -- apply (Qle_trans _ (((24 # 1) * q_pow (30 # 1) (Datatypes.S n))
                               * ((1 # 24) * q_pow (1 # 30) (Datatypes.S n)))%Q).
           ++ rewrite Hpair. apply Qle_refl.
           ++ rewrite (Qmult_comm ((1 # 24) * q_pow (1 # 30) (Datatypes.S n)
                                  ) (q_fact (2 * Datatypes.S (Datatypes.S (Datatypes.S n))))).
              apply Qmult_le_compat_r.
              ** exact (QleT'_to_Qle _ _ Hgeo).
              ** apply lw95_mul0.
                 --- compute. discriminate.
                 --- apply lw95_qpow_nonneg. compute. discriminate.
        -- apply lw62_sq_nonneg.
Qed.

Fixpoint lw62_rsum (r : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S m => lw62_rsum r m + q_pow r (Datatypes.S m)
  end.

Lemma lw62_abssum_shift : forall (B : Q) (n : nat),
  QleT' (leibsep_abssum B (Datatypes.S (Datatypes.S n)))
        ((1 + B * B * (1 # 2)
          + B * B * B * B * (1 # 24)
            * lw62_rsum (B * B * (1 # 30)) n)%Q).
Proof.
  intros B n. induction n as [|n IHn].
  - assert (HL : leibsep_abssum B (Datatypes.S (Datatypes.S 0))%nat
               == (1 + B * B * (1 # 2) + B * B * B * B * (1 # 24))%Q).
    { cbn [leibsep_abssum q_pow q_fact]. unfold Qdiv. cbn. ring. }
    apply Qle_to_QleT'.
    rewrite HL.
    change (lw62_rsum (B * B * (1 # 30)) 0) with 1%Q.
    apply qeq_le. ring.
  - apply Qle_to_QleT'.
    rewrite (lw62_abssum_S B (Datatypes.S (Datatypes.S n))).
    apply (Qle_trans
             _ ((1 + B * B * (1 # 2)
                 + B * B * B * B * (1 # 24)
                   * lw62_rsum (B * B * (1 # 30)) n
                 + (B * B * B * B * (1 # 24)
                    * q_pow (B * B * (1 # 30)) (Datatypes.S n)))%Q)).
    + apply Qplus_le_compat.
      * exact (QleT'_to_Qle _ _ IHn).
      * exact (lw62_item_dom B n).
    + apply qeq_imp_qle. cbn [lw62_rsum]. ring.
Qed.

Lemma lw62_qinv30_pos : Qlt 0 (1 # 30)%Q.
Proof. compute. reflexivity. Qed.

(* ---------- helpers for squares and absolute values ---------- *)

(* Integer squares are nonnegative (the three-way sign split at the [Z] level). *)
Lemma lw62_rsum_nonneg : forall (r : Q) (n : nat),
  Qle 0 r -> Qle 0 (lw62_rsum r n).
Proof.
  intros r n Hr. induction n as [|n IHn].
  - cbn [lw62_rsum]. compute. intro Hc. discriminate Hc.
  - simpl lw62_rsum. apply (Qle_trans _ (0 + 0)%Q).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply Qplus_le_compat.
      * exact IHn.
      * apply lw95_mul0; [exact Hr | apply lw95_qpow_nonneg; exact Hr].
Qed.

Lemma lw62_rsum_tele : forall (r : Q) (n : nat),
  (lw62_rsum r n * (1 - r))%Q == (1 - q_pow r (Datatypes.S n))%Q.
Proof.
  intros r n. induction n as [|n IHn].
  - cbn [lw62_rsum q_pow]. ring.
  - simpl lw62_rsum. rewrite Qmult_plus_distr_l. rewrite IHn.
    rewrite q_pow_succ, q_pow_succ, q_pow_succ. ring.
Qed.

Lemma lw62_abssum_env : forall (B : Q) (n : nat),
  QleT' (Qabs B) ((11 # 3)%Q) ->
  QleT' (leibsep_abssum B n) ((1 + (121 # 18) + (73205 # 5364))%Q).
Proof.
  intros B n HB.
  apply (qleT'_trans _ (leibsep_abssum B (Datatypes.S (Datatypes.S n)))).
  - apply lw62_abssum_mono.
    apply (Nat.le_trans n (Datatypes.S n) (Datatypes.S (Datatypes.S n)));
      apply Nat.le_succ_diag_r.
  - apply (qleT'_trans _ ((1 + B * B * (1 # 2)
            + B * B * B * B * (1 # 24)
              * lw62_rsum (B * B * (1 # 30)) n)%Q)).
    + apply lw62_abssum_shift.
    + apply Qle_to_QleT'.
      assert (HB2 : Qle (B * B) ((121 # 9))%Q).
      { apply (Qle_trans _ (Qabs B * Qabs B)%Q).
        - apply qeq_le. rewrite <- Qabs_Qmult.
          symmetry. apply Qabs_pos. apply lw62_sq_nonneg.
        - apply (lw95_mul_le_compat (Qabs B) (11 # 3) (Qabs B) (11 # 3));
            [apply Qabs_nonneg | exact (QleT'_to_Qle _ _ HB)
            | apply Qabs_nonneg | exact (QleT'_to_Qle _ _ HB)]. }
      assert (HB4 : Qle (B * B * B * B) ((14641 # 81))%Q).
      { apply (Qle_trans _ ((121 # 9) * (121 # 9))%Q).
        - apply (Qle_trans _ ((B * B) * (B * B))%Q).
          + apply qeq_imp_qle. ring.
          + apply (lw95_mul_le_compat (B * B) (121 # 9) (B * B) (121 # 9));
              [apply lw62_sq_nonneg | exact HB2 | apply lw62_sq_nonneg | exact HB2].
        - apply qeq_le. ring. }
      assert (Hr149 : Qle (lw62_rsum (B * B * (1 # 30)) n) ((270 # 149))%Q).
      { assert (Hte : Qle (lw62_rsum (B * B * (1 # 30)) n
                           * (1 - B * B * (1 # 30)))%Q 1%Q).
        { rewrite (lw62_rsum_tele (B * B * (1 # 30)) n).
          assert (Hp : Qle 0 (q_pow (B * B * (1 # 30)) (Datatypes.S n))).
          { apply lw95_qpow_nonneg. apply lw95_mul0;
              [apply lw62_sq_nonneg | apply Qlt_le_weak; apply lw62_qinv30_pos]. }
          apply (Qle_trans _ (1 + (- (q_pow (B * B * (1 # 30))
                                        (Datatypes.S n)))%Q)%Q).
          - apply qeq_le. ring.
          - apply (Qle_trans _ (1 + (- 0))%Q).
            + apply (Qplus_le_compat 1%Q 1%Q
                       (- (q_pow (B * B * (1 # 30)) (Datatypes.S n)))%Q (- 0)%Q).
              * apply Qle_refl.
              * apply (Qopp_le_compat 0%Q
                         (q_pow (B * B * (1 # 30)) (Datatypes.S n)) Hp).
            + apply qeq_le. ring. }
        assert (H1m : Qle ((149 # 270)) (1 - B * B * (1 # 30))%Q).
        { assert (Hb30 : Qle (B * B * (1 # 30)) ((121 # 270))%Q).
          { apply (Qle_trans _ ((121 # 9) * (1 # 30))%Q).
            - apply (lw95_mul_le_compat (B * B) (121 # 9) (1 # 30) (1 # 30));
                [apply lw62_sq_nonneg | exact HB2
                | apply Qlt_le_weak; apply lw62_qinv30_pos | apply Qle_refl].
            - apply qeq_le. ring. }
          apply (Qle_trans _ (1 - (121 # 270))%Q).
          - apply qeq_le. ring.
          - apply (Qplus_le_compat 1%Q 1%Q (- (121 # 270))%Q
                     (- (B * B * (1 # 30)))%Q).
            + apply Qle_refl.
            + apply (Qopp_le_compat (B * B * (1 # 30)) (121 # 270) Hb30). }
        assert (Hrs : Qle (lw62_rsum (B * B * (1 # 30)) n * (149 # 270))%Q 1%Q).
        { apply (Qle_trans _ (lw62_rsum (B * B * (1 # 30)) n
                                * (1 - B * B * (1 # 30)))%Q).
          - rewrite (Qmult_comm (lw62_rsum (B * B * (1 # 30)) n) (149 # 270)),
                    (Qmult_comm (lw62_rsum (B * B * (1 # 30)) n)
                                (1 - B * B * (1 # 30))).
            apply Qmult_le_compat_r.
            + exact H1m.
            + apply lw62_rsum_nonneg. apply lw95_mul0;
                [apply lw62_sq_nonneg | apply Qlt_le_weak; apply lw62_qinv30_pos].
          - exact Hte. }
        apply (Qle_trans _ (lw62_rsum (B * B * (1 # 30)) n
                              * ((149 # 270) * (270 # 149)))%Q).
        - apply qeq_le. ring.
        - apply (Qle_trans _ ((1 # 1) * (270 # 149))%Q).
          + rewrite (Qmult_assoc (lw62_rsum (B * B * (1 # 30)) n)
                              (149 # 270) (270 # 149)).
            apply (Qmult_le_compat_r (lw62_rsum (B * B * (1 # 30)) n
                                       * (149 # 270)) 1%Q (270 # 149) Hrs).
            compute. intro Hc. discriminate Hc.
          + apply qeq_le. ring. }
      assert (H2 : Qle (B * B * (1 # 2)) ((121 # 18))%Q).
      { apply (Qle_trans _ ((121 # 9) * (1 # 2))%Q).
        - apply (lw95_mul_le_compat (B * B) (121 # 9) (1 # 2) (1 # 2));
            [apply lw62_sq_nonneg | exact HB2 | apply Qlt_le_weak; compute; reflexivity
            | apply Qle_refl].
        - apply qeq_le. ring. }
      assert (H4r : Qle (B * B * B * B * (1 # 24)
                         * lw62_rsum (B * B * (1 # 30)) n) ((73205 # 5364))%Q).
      { apply (Qle_trans _ ((14641 # 81) * (1 # 24) * (270 # 149))%Q).
        - apply (lw95_mul_le_compat
                   (B * B * B * B * (1 # 24))
                   ((14641 # 81) * (1 # 24))
                   (lw62_rsum (B * B * (1 # 30)) n) (270 # 149)).
          + apply lw95_mul0.
            * apply (Qle_trans _ ((B * B) * (B * B))%Q).
              -- apply lw95_mul0; [apply lw62_sq_nonneg | apply lw62_sq_nonneg].
              -- apply qeq_imp_qle. ring.
            * apply Qlt_le_weak; compute; reflexivity.
          + apply (lw95_mul_le_compat (B * B * B * B) (14641 # 81) (1 # 24) (1 # 24)).
            * apply (Qle_trans _ ((B * B) * (B * B))%Q).
              -- apply lw62_sq_nonneg.
              -- apply qeq_imp_qle. ring.
            * exact HB4.
            * apply Qlt_le_weak; compute; reflexivity.
            * apply Qle_refl.
          + apply lw62_rsum_nonneg. apply lw95_mul0;
              [apply lw62_sq_nonneg | apply Qlt_le_weak; apply lw62_qinv30_pos].
          + exact Hr149.
        - apply qeq_le. ring. }
      apply Qplus_le_compat.
      * apply Qplus_le_compat.
        -- apply Qle_refl.
        -- exact H2.
      * exact H4r.
Qed.
Lemma lw62_abssum_nonneg : forall (B : Q) (n : nat),
  Qle 0 (leibsep_abssum B n).
Proof.
  intros B n. induction n as [|n IHn].
  - compute. intro Hc. discriminate Hc.
  - rewrite (lw62_abssum_S B n).
    pose proof (QleT'_to_Qle _ _ (lw62_qdiv_nonneg
                    (q_pow B (2 * Datatypes.S n)) (q_fact (2 * Datatypes.S n))
                    (lw62_qpow_even_nonneg B (Datatypes.S n))
                    (q_fact_pos (2 * Datatypes.S n)))) as Hterm.
    apply (Qle_trans _ ((0 + 0)%Q)).
    + apply Qle_refl.
    + apply Qplus_le_compat; [exact IHn | exact Hterm].
Qed.
Lemma lw62_abssum_cos_env : forall (B : Q) (n : nat),
  QleT' (Qabs B) ((11 # 3)%Q) ->
  QleT' (leibsep_abssum_cos B n)
        ((11 # 3) * (1 + (121 # 18) + (73205 # 5364)))%Q.
Proof.
  intros B n HB.
  apply (qleT'_trans _ (leibsep_abssum_cos (Qabs B) n)).
  - apply Qle_to_QleT'. apply lw62_abssum_cos_dom.
  - apply Qle_to_QleT'.
    apply (Qle_trans _ (Qabs B * leibsep_abssum (Qabs B) n)%Q).
    + apply lw62_abssum_cos_le. apply Qabs_nonneg.
    + apply (lw95_mul_le_compat (Qabs B) (11 # 3)
               (leibsep_abssum (Qabs B) n)
               (1 + (121 # 18) + (73205 # 5364))).
      * apply Qabs_nonneg.
      * exact (QleT'_to_Qle _ _ HB).
      * apply lw62_abssum_nonneg.
      * assert (Henv : QleT' (leibsep_abssum (Qabs B) n)
                         (1 + (121 # 18) + (73205 # 5364))).
        { apply (lw62_abssum_env (Qabs B) n).
          apply (qleT'_trans _ (Qabs B)).
          - apply qeq_leT'. apply Qabs_pos, Qabs_nonneg.
          - exact HB. }
        exact (QleT'_to_Qle _ _ Henv).
Qed.
Lemma qltw_pc_pw : forall x y : Q, QltT x y -> PiCompareT.QltT x y.
Proof.
  intros x y H.
  exact (match H in Id _ b
         return PiCompareT.Id (PiCompareT.Qlt_bool x y) b with
         | id_refl => @PiCompareT.id_refl _ (PiCompareT.Qlt_bool x y)
         end).
Qed.

Lemma qltw_pw_pc : forall x y : Q, PiCompareT.QltT x y -> QltT x y.
Proof.
  intros x y H.
  exact (match H in PiCompareT.Id _ b
         return Id (PiCompareT.Qlt_bool x y) b with
         | PiCompareT.id_refl => @id_refl _ (PiCompareT.Qlt_bool x y)
         end).
Qed.

(* ========== Section 1b. Companion pieces (the Wb lower bound, the C upper bound, division elimination) ========== *)

Lemma leibsep_Wb01_diff_lower : forall (b q : Q) (n : nat),
  QleT' 0 b -> QltT 0 q -> QleT' q (10 # 3) -> (2 <= n)%nat ->
  QleT' (lw0_Wb b q n 0 * (2 # 27))%Q
        (lw0_Wb b q n 0 - lw0_Wb b q n 1)%Q.
Proof.
  intros b q n Hb0 Hq Hq103 Hn.
  pose proof (lw0_Wb_ratio_bound b q n 0 Hb0 Hq Hq103 Hn) as Hratio.
  assert (Hq0 : QleT' 0 q) by (apply lw0_QltT_le; exact Hq).
  apply Qle_to_QleT'.
  assert (Heq : (lw0_Wb b q n 0 * (2 # 27))%Q ==
                (lw0_Wb b q n 0 - lw0_Wb b q n 0 * (25 # 27))%Q) by ring.
  rewrite Heq.
  apply QleT'_to_Qle in Hratio.
  apply (Qplus_le_compat (lw0_Wb b q n 0) (lw0_Wb b q n 0)
                         (- (lw0_Wb b q n 0 * (25 # 27)))%Q
                         (- (lw0_Wb b q n 1))%Q).
  - apply Qle_refl.
  - apply Qopp_le_compat. exact Hratio.
Qed.

Lemma lw1131_C_le_eps0K : forall (q : Q) (eps0 s t BF BFd : Q) (n : nat),
  QleT' 0 s -> QleT' 0 t ->
  QleT' (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)) BF ->
  QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)) BFd ->
  QleT' s (eps0 * (S973 + (1 # 4))%Q)%Q ->
  QleT' t (eps0 * ((11 # 3)%Q * S973 + (1 # 4))%Q)%Q ->
  QleT' (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q) * t
         + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q) * s
         + eps0 * (1 # 8))%Q
        (eps0 * (BF * ((11 # 3)%Q * S973 + (1 # 4)) + BFd * (S973 + (1 # 4)) + (1 # 8)))%Q.
Proof.
  intros q eps0 s t BF BFd n Hs0 Ht0 HF HFd Hscap Htcap.
  apply Qle_to_QleT'.
  assert (HBF0 : Qle 0 BF).
  { apply (Qle_trans 0 (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)) BF).
    - apply Qabs_nonneg.
    - exact (QleT'_to_Qle _ _ HF). }
  assert (Hterm1 : Qle (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q) * t)
                       (BF * (eps0 * ((11 # 3)%Q * S973 + (1 # 4)))%Q)).
  { apply (Qle_trans _ (BF * t%Q)).
    - apply (lw95_mul_le_compat
               (Qabs (qpoly_eval (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n) q)) BF t t).
      + apply Qabs_nonneg.
      + exact (QleT'_to_Qle _ _ HF).
      + exact (QleT'_to_Qle _ _ Ht0).
      + apply Qle_refl.
    - apply (lw95_mul_le_compat BF BF t (eps0 * ((11 # 3)%Q * S973 + (1 # 4)))%Q).
      + exact HBF0.
      + apply Qle_refl.
      + exact (QleT'_to_Qle _ _ Ht0).
      + exact (QleT'_to_Qle _ _ Htcap). }
  assert (HBFD0 : Qle 0 BFd).
  { apply (Qle_trans 0 (Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)) BFd).
    - apply Qabs_nonneg.
    - exact (QleT'_to_Qle _ _ HFd). }
  assert (Hterm2 : Qle (Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q) * s)
                       (BFd * (eps0 * (S973 + (1 # 4)))%Q)).
  { apply (Qle_trans _ (BFd * s%Q)).
    - apply (lw95_mul_le_compat
               (Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q (Zpos (Qden q) # 1)%Q n) n)) q)) BFd s s).
      + apply Qabs_nonneg.
      + exact (QleT'_to_Qle _ _ HFd).
      + exact (QleT'_to_Qle _ _ Hs0).
      + apply Qle_refl.
    - apply (lw95_mul_le_compat BFd BFd s (eps0 * (S973 + (1 # 4)))%Q).
      + exact HBFD0.
      + apply Qle_refl.
      + exact (QleT'_to_Qle _ _ Hs0).
      + exact (QleT'_to_Qle _ _ Hscap). }
  assert (Hring : (BF * (eps0 * ((11 # 3)%Q * S973 + (1 # 4)))%Q
                   + BFd * (eps0 * (S973 + (1 # 4)))%Q + eps0 * (1 # 8))%Q
                  == (eps0 * (BF * ((11 # 3)%Q * S973 + (1 # 4))
                              + BFd * (S973 + (1 # 4)) + (1 # 8)))%Q) by ring.
  apply (Qle_trans _ (BF * (eps0 * ((11 # 3)%Q * S973 + (1 # 4)))%Q
                      + BFd * (eps0 * (S973 + (1 # 4)))%Q + eps0 * (1 # 8))%Q).
  - apply Qplus_le_compat.
    + apply Qplus_le_compat; [exact Hterm1 | exact Hterm2].
    + apply Qle_refl.
  - rewrite Hring. apply Qle_refl.
Qed.

Lemma lw1190_div_mul_cancel : forall a b : Q, ~ b == 0 -> (a / b) * b == a.
Proof.
  intros a b Hb. unfold Qdiv. field. exact Hb.
Qed.

(* ========== Section 2. The triangular-window vanishing shore (three seed premises, Section discharge form) ========== *)

Section LeibsepDistilled.

Variable H1 : piLd3_seed_halfwin.
Variable H2 : piLd3_seed_dres.
Variable H3 : piLd3_seed_dcos.
Variable q : Q.

Let tq : Q := Qabs q.
Definition tsl (m : nat) : Q :=
  (2 * (q_pow tq (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)))%Q)%Q.
Definition tcl (m : nat) : Q :=
  (2 * (q_pow tq (2 * m) / q_fact (2 * m))%Q)%Q.

Lemma sin_slot_eps0 : forall (eps0 : Q) (N2 Nt : nat) (dtail : Q),
  QltT 0 eps0 -> QltT 0 dtail ->
  (forall m : nat, (N2 <= m)%nat ->
     QleT' (Qabs ((lw0m_xL m - q)%Q)) eps0) ->
  QleT' (Qabs q + eps0) ((11 # 3)%Q) ->
  (forall j : nat, (Nat.max N2 (Nat.max Nt 4) <= j)%nat ->
     QleT' (2 * q_pow tq 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))%Q) ->
  (forall m : nat, (Nt <= m)%nat -> QleT' (tsl m) dtail) ->
  sigT (fun M2 : nat => forall m : nat, (M2 <= m)%nat ->
    QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q))
          ((eps0 * S973 + dtail + dtail)%Q)).
Proof.
  intros eps0 N2 Nt dtail Heps0 Hdt Hband HB113 HR Htail.
  destruct (piL_sin_xL_vanish H1 H2 dtail Hdt) as [N1 HN1].
  exists (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1).
  assert (HmM : (Nat.max N2 (Nat.max Nt 4)
                 <= Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat) by apply Nat.le_max_l.
  assert (HmN1 : (N1 <= Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat) by apply Nat.le_max_r.
  assert (HmN2 : (N2 <= Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat).
  { apply (Nat.le_trans N2 (Nat.max N2 (Nat.max Nt 4))
             (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1));
      [apply Nat.le_max_l | exact HmM]. }
  assert (HmNt : (Nt <= Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat).
  { apply (Nat.le_trans Nt (Nat.max Nt 4)
             (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)).
    - apply Nat.le_max_l.
    - apply (Nat.le_trans (Nat.max Nt 4)
              (Nat.max N2 (Nat.max Nt 4))
              (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)).
      + apply Nat.le_max_r.
      + exact HmM. }
  pose proof (Hband (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) HmN2) as Hbx2.
  intros m Hm.
  assert (HB0 : QleT' 0 (Qabs q + eps0)%Q).
  { apply (qleT'_trans 0%Q ((0 + 0)%Q) ((Qabs q + eps0)%Q)).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat.
      + apply Qle_to_QleT'. apply Qabs_nonneg.
      + apply lw0_QltT_le. exact Heps0. }
  assert (Hpos2 : Qlt 0 (Qabs q + eps0)%Q).
  { apply (Qlt_le_trans 0 eps0 (Qabs q + eps0)%Q).
    - exact (QltT_to_Qlt 0 eps0 Heps0).
    - apply (Qle_trans eps0 ((0 + eps0)%Q) (Qabs q + eps0)%Q).
      + rewrite Qplus_0_l. apply Qle_refl.
      + apply Qplus_le_compat; [apply Qabs_nonneg | apply Qle_refl]. }
  assert (Habsabs : Qabs (Qabs q + eps0) == (Qabs q + eps0)%Q)
    by (apply Qabs_pos; apply Qlt_le_weak; exact Hpos2).
  assert (HBq : QleT' (Qabs q) (Qabs q + eps0)%Q).
  { apply (qleT'_trans (Qabs q) ((Qabs q + 0)%Q) ((Qabs q + eps0)%Q)).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat.
      + apply qleT'_refl.
      + apply lw0_QltT_le. exact Heps0. }
  assert (HBx : QleT' (Qabs (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))
                      (Qabs q + eps0)%Q).
  { apply (qleT'_trans (Qabs (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))
                       (Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q + q)%Q))
                       ((Qabs q + eps0)%Q)).
    - apply qeq_leT'. apply Qabs_wd. ring.
    - apply (qleT'_trans
              (Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q + q)%Q))
              ((Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q)%Q)
                + Qabs q)%Q)
              ((Qabs q + eps0)%Q)).
      + apply Qle_to_QleT'. apply Qabs_triangle.
      + apply (qleT'_trans
                ((Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q)%Q)
                  + Qabs q)%Q)
                ((eps0 + Qabs q)%Q)
                ((Qabs q + eps0)%Q)).
        * apply qleT'_plus_compat; [exact Hbx2 | apply qleT'_refl].
        * apply qeq_leT'. ring. }
  assert (Hr2 : forall j : nat,
            (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1 <= j)%nat ->
            QleT' (2 * q_pow tq 2)
                  (lw0_q_of_nat (Datatypes.S (2 * j))
                   * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))%Q).
  { intros j Hj. apply HR. exact (Nat.le_trans _ _ _ HmM Hj). }
  assert (Hex : sigT (fun D : nat =>
              m = (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1 + D)%nat)).
  { exists (m - Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat.
    rewrite Nat.add_comm. symmetry. apply Nat.sub_add. exact Hm. }
  destruct Hex as [D HD]. subst m.
  apply (qleT'_trans
          (Qabs (qpoly_eval (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1 + D)) q))
          (Qabs (qpoly_eval (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)) q)
           + 2 * (q_pow tq (Datatypes.S (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                  / q_fact (Datatypes.S (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))%Q)
          ((eps0 * S973 + dtail + dtail)%Q)).
  - exact (leibsep_sin_qp_tail_stable q (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) D Hr2).
  - apply (qleT'_trans
            (Qabs (qpoly_eval (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)) q)
             + 2 * (q_pow tq (Datatypes.S (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                    / q_fact (Datatypes.S (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))%Q)
            (Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q)
             * leibsep_abssum (Qabs q + eps0) (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
             + dtail
             + 2 * (q_pow tq (Datatypes.S (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                    / q_fact (Datatypes.S (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))%Q)
            ((eps0 * S973 + dtail + dtail)%Q)).
    + apply qleT'_plus_compat.
      * apply (qleT'_trans
                (Qabs (qpoly_eval (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)) q))
                (Qabs ((sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q
                        - sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                          (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))%Q)
                 + Qabs (sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                           (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))))
                ((Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q)
                 * leibsep_abssum (Qabs q + eps0) (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                 + dtail)%Q)).
             ** apply (qleT'_trans
                       (Qabs (qpoly_eval (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)) q))
                       (Qabs ((sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q
                               - sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                                 (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))
                              + sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                                (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))%Q)
                       ((Qabs ((sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q
                               - sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                                 (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))%Q)
                         + Qabs (sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                                   (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))))%Q)).
                -- apply qeq_leT'.
                   apply Qabs_wd.
                   rewrite (lw0_sin_qp_eval (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q). ring.
                -- apply Qle_to_QleT'.
                   exact (Qabs_triangle
                           (sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q
                            - sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                              (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))
                           (sin_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                              (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))).
             ** apply Qle_to_QleT'.
                apply Qplus_le_compat.
                -- exact (QleT'_to_Qle _ _
                            (leibsep_sin_partial_lipschitz q
                               (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                               (Qabs q + eps0)%Q (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                               HB0 HBq HBx)).
                -- apply Qlt_le_weak.
                   apply QltT_to_Qlt.
                   exact (HN1 (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                              (NatLe_lift _ _ HmN1)).
      * apply qleT'_refl.
    + apply qleT'_plus_compat.
      * apply (qleT'_trans
                ((Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q)
                  * leibsep_abssum (Qabs q + eps0) (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                  + dtail)%Q)
                (eps0 * S973 + dtail)%Q).
        -- apply qleT'_plus_compat.
           ++ apply Qle_to_QleT'.
              apply (lw95_mul_le_compat
                       (Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q))
                       eps0
                       (leibsep_abssum (Qabs q + eps0)
                          (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                       S973).
              ** apply Qabs_nonneg.
              ** apply QleT'_to_Qle.
                 apply (qleT'_trans
                         (Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q))
                         (Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q)%Q))
                         eps0).
                 *** apply qeq_leT'.
                     rewrite <- (Qabs_opp (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q)%Q).
                     apply Qabs_wd. ring.
                 *** exact Hbx2.
              ** apply lw62_abssum_nonneg.
              ** apply QleT'_to_Qle. apply lw62_abssum_env.
                 apply (qleT'_trans (Qabs (Qabs q + eps0)) (Qabs q + eps0) ((11 # 3)%Q)).
                 *** apply qeq_leT'. exact Habsabs.
                 *** exact HB113.
           ++ apply qleT'_refl.
        -- apply qleT'_refl.
      * apply (Htail (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) HmNt).
Qed.

Lemma cos_slot_eps0 : forall (eps0 : Q) (N2 Nt : nat) (dtail : Q),
  QltT 0 eps0 -> QltT 0 dtail ->
  (forall m : nat, (N2 <= m)%nat ->
     QleT' (Qabs ((lw0m_xL m - q)%Q)) eps0) ->
  QleT' (Qabs q + eps0) ((11 # 3)%Q) ->
  (forall j : nat, (Nat.max N2 (Nat.max Nt 4) <= j)%nat ->
     QleT' (2 * q_pow tq 2)
           (lw0_q_of_nat (Datatypes.S (2 * j))
            * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))%Q) ->
  (forall m : nat, (Nt <= m)%nat -> QleT' (tcl m) dtail) ->
  sigT (fun M2 : nat => forall m : nat, (M2 <= m)%nat ->
    QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q))
          ((eps0 * ((11 # 3)%Q * S973) + dtail + dtail)%Q)).
Proof.
  intros eps0 N2 Nt dtail Heps0 Hdt Hband HB113 HR Htail.
  destruct (piL_cos_xL_neg1_vanish H1 H3 dtail Hdt) as [N1 HN1].
  exists (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1).
  assert (HmM : (Nat.max N2 (Nat.max Nt 4)
                 <= Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat) by apply Nat.le_max_l.
  assert (HmN1 : (N1 <= Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat) by apply Nat.le_max_r.
  assert (HmN2 : (N2 <= Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat).
  { apply (Nat.le_trans N2 (Nat.max N2 (Nat.max Nt 4))
             (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1));
      [apply Nat.le_max_l | exact HmM]. }
  assert (HmNt : (Nt <= Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat).
  { apply (Nat.le_trans Nt (Nat.max Nt 4)
             (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)).
    - apply Nat.le_max_l.
    - apply (Nat.le_trans (Nat.max Nt 4)
              (Nat.max N2 (Nat.max Nt 4))
              (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)).
      + apply Nat.le_max_r.
      + exact HmM. }
  pose proof (Hband (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) HmN2) as Hbx2.
  intros m Hm.
  assert (HB0 : QleT' 0 (Qabs q + eps0)%Q).
  { apply (qleT'_trans 0%Q ((0 + 0)%Q) ((Qabs q + eps0)%Q)).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat.
      + apply Qle_to_QleT'. apply Qabs_nonneg.
      + apply lw0_QltT_le. exact Heps0. }
  assert (Hpos2 : Qlt 0 (Qabs q + eps0)%Q).
  { apply (Qlt_le_trans 0 eps0 (Qabs q + eps0)%Q).
    - exact (QltT_to_Qlt 0 eps0 Heps0).
    - apply (Qle_trans eps0 ((0 + eps0)%Q) (Qabs q + eps0)%Q).
      + rewrite Qplus_0_l. apply Qle_refl.
      + apply Qplus_le_compat; [apply Qabs_nonneg | apply Qle_refl]. }
  assert (Habsabs : Qabs (Qabs q + eps0) == (Qabs q + eps0)%Q)
    by (apply Qabs_pos; apply Qlt_le_weak; exact Hpos2).
  assert (HBq : QleT' (Qabs q) (Qabs q + eps0)%Q).
  { apply (qleT'_trans (Qabs q) ((Qabs q + 0)%Q) ((Qabs q + eps0)%Q)).
    - apply qeq_leT'. ring.
    - apply qleT'_plus_compat.
      + apply qleT'_refl.
      + apply lw0_QltT_le. exact Heps0. }
  assert (HBx : QleT' (Qabs (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))
                      (Qabs q + eps0)%Q).
  { apply (qleT'_trans (Qabs (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))
                       (Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q + q)%Q))
                       ((Qabs q + eps0)%Q)).
    - apply qeq_leT'. apply Qabs_wd. ring.
    - apply (qleT'_trans
              (Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q + q)%Q))
              ((Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q)%Q)
                + Qabs q)%Q)
              ((Qabs q + eps0)%Q)).
      + apply Qle_to_QleT'. apply Qabs_triangle.
      + apply (qleT'_trans
                ((Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q)%Q)
                  + Qabs q)%Q)
                ((eps0 + Qabs q)%Q)
                ((Qabs q + eps0)%Q)).
        * apply qleT'_plus_compat; [exact Hbx2 | apply qleT'_refl].
        * apply qeq_leT'. ring. }
  assert (Hr2 : forall j : nat,
            (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1 <= j)%nat ->
            QleT' (2 * q_pow tq 2)
                  (lw0_q_of_nat (Datatypes.S (2 * j))
                   * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))%Q).
  { intros j Hj. apply HR. exact (Nat.le_trans _ _ _ HmM Hj). }
  assert (Hex : sigT (fun D : nat =>
              m = (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1 + D)%nat)).
  { exists (m - Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)%nat.
    rewrite Nat.add_comm. symmetry. apply Nat.sub_add. exact Hm. }
  destruct Hex as [D HD]. subst m.
  apply (qleT'_trans
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1 + D))) q + (1 # 1)%Q))
          (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))) q + (1 # 1)%Q)
           + 2 * (q_pow tq (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                  / q_fact (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q)
          ((eps0 * ((11 # 3)%Q * S973) + dtail + dtail)%Q)).
  - exact (leibsep_cos_qp_deriv_tail_stable q (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) D Hr2).
  - apply (qleT'_trans
            (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))) q + (1 # 1)%Q)
             + 2 * (q_pow tq (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                    / q_fact (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q)
            (Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q)
             * leibsep_abssum_cos (Qabs q + eps0) (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
             + dtail
             + 2 * (q_pow tq (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                    / q_fact (2 * Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q)
            ((eps0 * ((11 # 3)%Q * S973) + dtail + dtail)%Q)).
    + apply qleT'_plus_compat.
      * apply (qleT'_trans
                (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))) q + (1 # 1)%Q))
                (Qabs ((cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q
                        - cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                          (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))%Q)
                 + Qabs (cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                           (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                         + (1 # 1)%Q))
                ((Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q)
                 * leibsep_abssum_cos (Qabs q + eps0) (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                 + dtail)%Q)).
             ** apply (qleT'_trans
                       (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))) q + (1 # 1)%Q))
                       (Qabs ((cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q
                               - cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                                 (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))
                              + (cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                                   (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                                 + (1 # 1)%Q))%Q)
                       ((Qabs ((cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q
                               - cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                                 (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))%Q)
                         + Qabs (cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                                   (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                                 + (1 # 1)%Q))%Q)).
                -- apply qeq_leT'.
                   apply Qabs_wd.
                   rewrite (lw0_sin_qp_deriv_eval (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q). ring.
                -- apply Qle_to_QleT'.
                   exact (Qabs_triangle
                           (cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) q
                            - cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                              (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)))
                           (cos_partial (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                              (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                            + (1 # 1)%Q)).
             ** apply Qle_to_QleT'.
                apply Qplus_le_compat.
                -- exact (QleT'_to_Qle _ _
                            (leibsep_cos_partial_lipschitz q
                               (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                               (Qabs q + eps0)%Q (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                               HB0 HBq HBx)).
                -- apply Qlt_le_weak.
                   apply QltT_to_Qlt.
                   exact (HN1 (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                              (NatLe_lift _ _ HmN1)).
      * apply qleT'_refl.
    + apply qleT'_plus_compat.
      * apply (qleT'_trans
                ((Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q)
                  * leibsep_abssum_cos (Qabs q + eps0) (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1)
                  + dtail)%Q)
                (eps0 * ((11 # 3)%Q * S973) + dtail)%Q).
        -- apply qleT'_plus_compat.
           ++ apply Qle_to_QleT'.
              apply (lw95_mul_le_compat
                       (Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q))
                       eps0
                       (leibsep_abssum_cos (Qabs q + eps0)
                          (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))
                       ((11 # 3)%Q * S973)).
              ** apply Qabs_nonneg.
              ** apply QleT'_to_Qle.
                 apply (qleT'_trans
                         (Qabs ((q - lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1))%Q))
                         (Qabs ((lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q)%Q))
                         eps0).
                 *** apply qeq_leT'.
                     rewrite <- (Qabs_opp (lw0m_xL (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) - q)%Q).
                     apply Qabs_wd. ring.
                 *** exact Hbx2.
              ** apply lw1131_abssum_cos_nonneg.
                 exact (QleT'_to_Qle _ _ HB0).
              ** apply QleT'_to_Qle. apply lw62_abssum_cos_env.
                 apply (qleT'_trans (Qabs (Qabs q + eps0)) (Qabs q + eps0) ((11 # 3)%Q)).
                 *** apply qeq_leT'. exact Habsabs.
                 *** exact HB113.
           ++ apply qleT'_refl.
        -- apply qleT'_refl.
      * apply (Htail (Nat.max (Nat.max N2 (Nat.max Nt 4)) N1) HmNt).
Qed.

End LeibsepDistilled.

(* ========== Section 3. The tail rescaling [caps_scaled] (three explicit seed premises) ========== *)

(* The tail-scale gauge in function form (q explicit): used only
   within the proof body of [caps_scaled]. *)
Definition tqF (q : Q) : Q := Qabs q.
Definition tslF (q : Q) (m : nat) : Q :=
  (2 * (q_pow (tqF q) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)))%Q)%Q.
Definition tclF (q : Q) (m : nat) : Q :=
  (2 * (q_pow (tqF q) (2 * m) / q_fact (2 * m))%Q)%Q.

Lemma caps_scaled :
  forall (H1 : piLd3_seed_halfwin) (H2 : piLd3_seed_dres) (H3 : piLd3_seed_dcos)
    (q : Q) (eps0 : Q) (N0 Nv : nat),
  QltT 0 eps0 ->
  QleT' eps0 ((1 # 3)%Q) ->
  (forall n : nat, NatLe N0 n ->
     QltT eps0 ((10 / 3)%Q - lw0m_xL n)%Q) ->
  (forall n : nat, (Nv <= n)%nat -> QltT (lw0m_e n) (eps0 * (1 # 4))%Q) ->
  leibsep_gate_open q (Nat.max Nv 1) (eps0 * (1 # 8))%Q = false ->
  sigT (fun s : Q => sigT (fun t : Q => sigT (fun M0 : nat =>
    And (forall m : nat, (M0 <= m)%nat ->
           QleT' (Qabs (qpoly_eval (lw0_sin_qp m) q)) s)
        (And (forall m : nat, (M0 <= m)%nat ->
               QleT' (Qabs (qpoly_eval (qpoly_deriv (lw0_sin_qp m)) q + (1 # 1)%Q)) t)
        (And (QleT' 0 s)
             (And (QleT' 0 t)
                  (And (QleT' s (eps0 * (S973 + (1 # 4))%Q)%Q)
                       (QleT' t (eps0 * ((11 # 3)%Q * S973 + (1 # 4))%Q)%Q)))))))).
Proof.
  intros H1 H2 H3 q eps0 N0 Nv Heps0 HE13 HN0 HNv Hgate.
  assert (HNw1 : (1 <= Nat.max Nv 1)%nat) by apply Nat.le_max_r.
  assert (Hc8ltT : QltT 0 (eps0 * (1 # 8))%Q).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps0 (1 # 8)%Q).
    - apply QltT_to_Qlt. exact Heps0.
    - compute. reflexivity. }
  assert (Htq0 : QleT' 0 (tqF q)).
  { apply Qle_to_QleT'. apply Qabs_nonneg. }
  assert (Hc113 : QleT' (Qabs q) ((11 # 3)%Q)).
  { apply (qleT'_trans (Qabs q) (Qabs q + eps0) ((11 # 3)%Q)).
    - apply (qleT'_trans (Qabs q) (Qabs q + 0)%Q (Qabs q + eps0)%Q).
      + apply (qeq_leT' (Qabs q) (Qabs q + 0)%Q). ring.
      + apply qleT'_plus_compat; [apply qleT'_refl | apply lw0_QltT_le; exact Heps0].
    - pose proof (leibsep_shore_q_le_ten_thirds q eps0 N0 Nv Heps0 HN0 HNv Hgate) as Hq103.
      pose proof (leibsep_shore_q_pos q eps0 N0 Nv Heps0 HN0 HNv Hgate) as Hq.
      assert (Hqa : (Qabs q)%Q == q).
      { apply Qabs_pos. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hq. }
      assert (HB113 : QleT' (Qabs q + eps0) ((11 # 3)%Q)).
      { apply (qleT'_trans (Qabs q + eps0) (q + eps0) ((11 # 3)%Q)).
        - apply (qleT'_plus_compat (Qabs q) q eps0 eps0).
          + apply (qeq_leT' (Qabs q) q). exact Hqa.
          + apply qleT'_refl.
        - apply (qleT'_trans (q + eps0) ((10 # 3)%Q + (1 # 3)%Q) ((11 # 3)%Q)).
          + apply qleT'_plus_compat; [exact Hq103 | exact HE13].
          + apply qeq_leT'. ring. }
      exact HB113. }
  destruct (leibsep_closedband_of_gate_false q (Nat.max Nv 1)
             (eps0 * (1 # 8))%Q (eps0 * (1 # 8))%Q (eps0 * (1 # 8))%Q
             HNw1 Hgate Hc8ltT Hc8ltT) as [N2 HN2].
  pose proof (leibsep_shore_W_le (lw0m_e (Nat.max Nv 1)) eps0
              (HNv (Nat.max Nv 1) (Nat.le_max_l Nv 1))) as HWle.
  assert (HbandE : forall m : nat, (N2 <= m)%nat ->
            QleT' (Qabs ((lw0m_xL m - q)%Q)) eps0).
  { intros m Hm.
    exact (qleT'_trans _ _ _ (HN2 m (NatLe_lift N2 m Hm)) HWle). }
  pose proof (leibsep_shore_q_le_ten_thirds q eps0 N0 Nv Heps0 HN0 HNv Hgate) as Hq103.
  pose proof (leibsep_shore_q_pos q eps0 N0 Nv Heps0 HN0 HNv Hgate) as Hq.
  assert (HB113 : QleT' (Qabs q + eps0) ((11 # 3)%Q)).
  { assert (Hqa : (Qabs q)%Q == q).
    { apply Qabs_pos. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hq. }
    apply (qleT'_trans (Qabs q + eps0) (q + eps0) ((11 # 3)%Q)).
    - apply (qleT'_plus_compat (Qabs q) q eps0 eps0).
      + apply (qeq_leT' (Qabs q) q). exact Hqa.
      + apply qleT'_refl.
    - apply (qleT'_trans (q + eps0) ((10 # 3)%Q + (1 # 3)%Q) ((11 # 3)%Q)).
      + apply qleT'_plus_compat; [exact Hq103 | exact HE13].
      + apply qeq_leT'. ring. }
  assert (Hab4 : QleT' (Qabs q) (lw0_q_of_nat 4)).
  { assert (Habsq : Qabs q == q).
    { apply Qabs_pos. apply Qlt_le_weak. apply QltT_to_Qlt. exact Hq. }
    apply (qleT'_trans (Qabs q) q (lw0_q_of_nat 4)).
    - apply qeq_leT'. exact Habsq.
    - apply (qleT'_trans q (10 / 3)%Q (lw0_q_of_nat 4)).
      + exact Hq103.
      + change (lw0_q_of_nat 4) with (4 # 1)%Q.
        apply Qle_to_QleT'. compute. discriminate. }
  assert (Heps16 : QltT 0 (eps0 * (1 # 16))%Q).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps0 (1 # 16)%Q).
    - apply QltT_to_Qlt. exact Heps0.
    - compute. reflexivity. }
  destruct (lw0_pitB_conv_t_vanish (tqF q) (eps0 * (1 # 16))%Q Htq0 Heps16) as [Msin [Hbnd Hvan]].
  assert (HtaillS : forall m : nat, (Msin <= m)%nat -> QleT' (tslF q m) (eps0 * (1 # 8))%Q).
  { intros m Hm. specialize (Hvan m Hm). unfold tslF.
    apply Qle_to_QleT'.
    apply (leibsep_qle_wd2 (2 * (q_pow (tqF q) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)))%Q)
                           (2 * (eps0 * (1 # 16))%Q)%Q
                           (2 * (q_pow (tqF q) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)))%Q)
                           (eps0 * (1 # 8))%Q).
    - apply Qeq_refl.
    - ring.
    - rewrite (Qmult_comm 2 (q_pow (tqF q) (Datatypes.S (2 * m)) / q_fact (Datatypes.S (2 * m)))%Q).
      rewrite (Qmult_comm 2 (eps0 * (1 # 16))%Q).
      apply Qmult_le_compat_r.
      + apply Qlt_le_weak. apply QltT_to_Qlt. exact Hvan.
      + compute. intro Hc. discriminate Hc. }
  assert (HtaillC : forall m : nat, (Datatypes.S Msin <= m)%nat ->
            QleT' (tclF q m) (eps0 * (1 # 8))%Q).
  { intros m Hm. destruct m as [| j]. { exfalso. exact (Nat.nle_succ_0 Msin Hm). }
    assert (Hj : (Msin <= j)%nat) by (apply le_S_n; exact Hm).
    specialize (Hvan j Hj).
    unfold tclF.
    replace (2 * Datatypes.S j)%nat
      with (Datatypes.S (Datatypes.S (2 * j)))%nat
      by (rewrite Nat.mul_succ_r, Nat.add_succ_r, Nat.add_succ_r, Nat.add_0_r; reflexivity).
    assert (E1 : (q_pow (tqF q) (Datatypes.S (Datatypes.S (2 * j)))
                  / q_fact (Datatypes.S (Datatypes.S (2 * j))))%Q
                 == ((q_pow (tqF q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))
                     * ((tqF q) / (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)))%Q).
    { rewrite (q_pow_succ (tqF q) (Datatypes.S (2 * j))).
      rewrite (q_fact_succ (Datatypes.S (2 * j))).
      unfold Qdiv.
      rewrite Qinv_mult_distr.
      ring.
      all: try (apply Qlt_not_eq; apply q_fact_pos). }
    assert (HpowN : forall n : nat, Qle 0 (q_pow (tqF q) n)).
    { intro n. induction n as [| n IHn].
      - cbn [q_pow]. compute. intro Hc. discriminate Hc.
      - rewrite (q_pow_succ (tqF q) n). apply Qmult_le_0_compat.
        + exact (QleT'_to_Qle _ _ Htq0).
        + exact IHn. }
    assert (Hd1 : Qle ((tqF q) / (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)) (1 # 1)%Q).
    { apply (lw62_qdiv_le (tqF q) (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1) (1 # 1) (1 # 1)).
      - apply QltT_to_Qlt.
        change (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)%Q
          with (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))).
        apply lw0_q_of_nat_lt0T_S.
      - compute. reflexivity.
      - rewrite Qmult_1_r, Qmult_1_l.
        apply (Qle_trans _ (lw0_q_of_nat (Datatypes.S Msin))).
        + exact (QleT'_to_Qle _ _ Hbnd).
        + apply QleT'_to_Qle.
          change (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)%Q
            with (lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j)))).
          apply lw0_q_of_nat_le_mono.
          apply (Nat.le_trans (Datatypes.S Msin) (Datatypes.S j)
                  (Datatypes.S (Datatypes.S (2 * j)))).
          * exact Hm.
           * apply le_n_S.
             rewrite (Nat.mul_comm 2 j).
             apply (Nat.le_trans j (j * 2) (Datatypes.S (j * 2))).
             -- apply (Nat.le_mul_r j 2). intro Hc. discriminate Hc.
             -- apply Nat.le_succ_diag_r. }
    assert (HXd : Qle 0 (q_pow (tqF q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))).
    { apply QleT'_to_Qle.
      apply (lw62_qdiv_nonneg (q_pow (tqF q) (Datatypes.S (2 * j))) (q_fact (Datatypes.S (2 * j)))).
      - apply Qle_to_QleT'. apply HpowN.
      - apply q_fact_pos. }
    assert (HX1 : Qle (((tqF q) / (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))
                       * (q_pow (tqF q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))))%Q
                      (q_pow (tqF q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))%Q).
    { apply (Qle_trans _ ((1 # 1)%Q
                           * (q_pow (tqF q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))%Q)%Q).
      - apply Qmult_le_compat_r.
        + exact Hd1.
        + exact HXd.
      - rewrite Qmult_1_l. apply Qle_refl. }
    apply Qle_to_QleT'.
    rewrite E1.
    apply Qlt_le_weak.
    assert (Heq8 : (eps0 * (1 # 8))%Q == (eps0 * (1 # 16))%Q * (2 # 1)) by ring.
    rewrite Heq8.
    rewrite (Qmult_comm (q_pow (tqF q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))
                        ((tqF q) / (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1))).
    rewrite (Qmult_comm 2 ((tqF q) / (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)
                           * (q_pow (tqF q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))))%Q).
    apply (Qmult_lt_compat_r ((tqF q) / (Z.of_nat (Datatypes.S (Datatypes.S (2 * j))) # 1)
                              * (q_pow (tqF q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j))))%Q
                             (eps0 * (1 # 16))%Q (2 # 1)).
    - vm_compute. reflexivity.
    - apply (Qle_lt_trans _ (q_pow (tqF q) (Datatypes.S (2 * j)) / q_fact (Datatypes.S (2 * j)))%Q).
      + exact HX1.
      + exact (QltT_to_Qlt _ _ Hvan). }
  assert (HRr : forall j : nat, (Nat.max N2 (Nat.max (Datatypes.S Msin) 4) <= j)%nat ->
            QleT' (2 * q_pow (tqF q) 2)
                  (lw0_q_of_nat (Datatypes.S (2 * j))
                   * lw0_q_of_nat (Datatypes.S (Datatypes.S (2 * j))))%Q).
  { intros j Hj. apply (leibsep_ratio_slot q 4 Hab4 j).
    exact (Nat.le_trans 4 (Nat.max (Datatypes.S Msin) 4) j
             (Nat.le_max_r (Datatypes.S Msin) 4)
             (Nat.le_trans (Nat.max (Datatypes.S Msin) 4)
                           (Nat.max N2 (Nat.max (Datatypes.S Msin) 4)) j
                           (Nat.le_max_r N2 (Nat.max (Datatypes.S Msin) 4)) Hj)). }
  destruct (sin_slot_eps0 H1 H2 q eps0 N2 (Datatypes.S Msin) (eps0 * (1 # 8))%Q
                   Heps0 Hc8ltT HbandE HB113 HRr
                   (fun m Hm => HtaillS m
                      (Nat.le_trans Msin (Datatypes.S Msin) m
                         (Nat.le_succ_diag_r Msin) Hm))) as [M2s HM2s].
  destruct (cos_slot_eps0 H1 H3 q eps0 N2 (Datatypes.S Msin) (eps0 * (1 # 8))%Q
                   Heps0 Hc8ltT HbandE HB113 HRr HtaillC) as [M2c HM2c].
  exists (eps0 * (S973 + (1 # 4))%Q)%Q.
  exists (eps0 * ((11 # 3)%Q * S973 + (1 # 4))%Q)%Q.
  exists (Nat.max M2s M2c).
  split.
  - intros m Hm.
    apply (qleT'_trans _ (eps0 * S973 + eps0 * (1 # 8) + eps0 * (1 # 8))%Q).
    + exact (HM2s m
               (Nat.le_trans M2s (Nat.max M2s M2c) m (Nat.le_max_l M2s M2c) Hm)).
    + apply qeq_leT'. ring.
  - split.
    + intros m Hm.
      apply (qleT'_trans _
               (eps0 * ((11 # 3)%Q * S973) + eps0 * (1 # 8) + eps0 * (1 # 8))%Q).
      * exact (HM2c m
                 (Nat.le_trans M2c (Nat.max M2s M2c) m (Nat.le_max_r M2s M2c) Hm)).
      * apply qeq_leT'. ring.
    + split.
      * apply Qle_to_QleT'.
        apply (Qmult_le_0_compat eps0 (S973 + (1 # 4))%Q).
        -- apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps0.
        -- vm_compute. intro Hc. discriminate Hc.
      * split.
        -- apply Qle_to_QleT'.
           apply (Qmult_le_0_compat eps0 ((11 # 3)%Q * S973 + (1 # 4))%Q).
           ++ apply Qlt_le_weak. apply QltT_to_Qlt. exact Heps0.
           ++ vm_compute. intro Hc. discriminate Hc.
        -- split.
           ++ apply qleT'_refl.
           ++ apply qleT'_refl.
Qed.

(* ========== Section 4. The separation kernel [leibsep_q_kernel] (carried by the three seed [Section] premises) ========== *)

Section KernelDistilled.

Variable H1 : piLd3_seed_halfwin.
Variable H2 : piLd3_seed_dres.
Variable H3 : piLd3_seed_dcos.

(* ---- the kernel statement face (source coordinates :5452-:5456, transcribed verbatim) ---- *)
Theorem leibsep_q_kernel :
  forall q : Q,
    sigT (fun c : Q => And (QltT 0 c)
      (sigT (fun N : nat => forall m : nat, NatLe N m ->
        QltT c (Qabs ((lw0m_xL m - q)%Q))))).
(* ---- the kernel proof body (source coordinates :5457-:5695, transcribed verbatim; the break points are marked) ---- *)
Proof.
  intros q.
  destruct piL_ten_thirds_supply as [eg [Hegp [N0g HN0g]]].
  destruct piL_leibniz_ten_thirds_supply as [el [Help [N0l HN0l]]].
  destruct piL_three_supply as [e3 [He3p [N3 HN3]]].
  pose proof (QltT_to_Qlt 0 eg Hegp) as Hegp'.
  pose proof (QltT_to_Qlt 0 el Help) as Help'.
  pose proof (QltT_to_Qlt 0 e3 He3p) as He3p'.
  set (b0 := (Z.pos (Qden q) # 1)%Q).
  set (n_sel := (lw0_n_select (10 * lw0_pi_d0_of b0) 0 + 1)%nat).
  set (BF := Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0 n_sel) n_sel) q)).
  set (BFd := Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0 n_sel) n_sel)) q)).
  set (K := (BF * ((11 # 3)%Q * S973 + (1 # 4)) + BFd * (S973 + (1 # 4)) + (1 # 8))%Q).
  assert (Hb0 : QltT 0 b0).
  { apply Qlt_to_QltT. unfold b0, Qlt. cbn. reflexivity. }
  assert (HBF0 : Qle 0 BF) by (apply Qabs_nonneg).
  assert (HBFd0 : Qle 0 BFd) by (apply Qabs_nonneg).
  assert (Hns2 : (2 <= n_sel)%nat).
  { unfold n_sel, lw0_n_select. apply le_n_S. apply le_n_S. apply Nat.le_0_l. }
  assert (HK1 : Qle (1 # 8) K).
  { unfold K. assert (Hc1 : Qle 0 ((11 # 3)%Q * S973 + (1 # 4))%Q).
    { assert (Hp : Qlt 0 ((11 # 3)%Q * S973 + (1 # 4))%Q)
        by (unfold S973; vm_compute; reflexivity).
      apply Qlt_le_weak. exact Hp. }
    assert (Hc2 : Qle 0 (S973 + (1 # 4))%Q).
    { assert (Hp : Qlt 0 (S973 + (1 # 4))%Q) by (unfold S973; vm_compute; reflexivity).
      apply Qlt_le_weak. exact Hp. }
    unfold S973.
    assert (Hp1 : Qle 0 (BF * ((11 # 3)%Q * S973 + (1 # 4))%Q)%Q).
    { apply Qmult_le_0_compat; assumption. }
    assert (Hp2 : Qle 0 (BFd * (S973 + (1 # 4))%Q)%Q).
    { apply Qmult_le_0_compat; [exact HBFd0 | exact Hc2]. }
    apply (Qle_trans (1 # 8)
             ((1 # 8)%Q + (BF * ((11 # 3)%Q * S973 + (1 # 4))
                           + BFd * (S973 + (1 # 4)))%Q)%Q K).
    - apply QleT'_to_Qle.
      apply (qleT'_plus_nonneg_rT (1 # 8)%Q
               (BF * ((11 # 3)%Q * S973 + (1 # 4)) + BFd * (S973 + (1 # 4)))%Q).
      apply Qle_to_QleT'.
      apply (Qplus_le_compat 0%Q (BF * ((11 # 3)%Q * S973 + (1 # 4))%Q)%Q 0%Q
               (BFd * (S973 + (1 # 4))%Q)%Q).
      + exact Hp1.
      + exact Hp2.
    - unfold K. apply QleT'_to_Qle. apply qeq_leT'. ring. }
  assert (HKpos : Qlt 0 K).
  { apply (Qlt_le_trans 0 (1 # 8) K).
    - vm_compute. reflexivity.
    - exact HK1. }
  assert (HK0 : Qle 0 K) by (apply Qlt_le_weak; exact HKpos).
  assert (Hinv : Qle 0 ((1 # 2)%Q / K)).
  { apply Qlt_le_weak. apply (Qmult_lt_0_compat (1 # 2) (/ K)).
    - vm_compute. reflexivity.
    - apply Qinv_lt_0_compat. exact HKpos. }
  pose (eps1 := Qmin eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K)))).
  assert (Hep1lt : Qlt 0 eps1).
  { apply (Q.min_glb_lt _ _ 0); [exact Hegp' |].
    apply (Q.min_glb_lt _ _ 0); [exact Help' |].
    apply (Q.min_glb_lt _ _ 0).
    - vm_compute. reflexivity.
    - apply (Qmult_lt_0_compat (1 # 2) (/ K)).
      + vm_compute. reflexivity.
      + apply Qinv_lt_0_compat. exact HKpos. }
  assert (Hep1eg : Qle eps1 eg).
  { apply (Q.min_glb_l eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) eps1).
    apply Qle_refl. }
  assert (Hep1el : Qle eps1 el).
  { apply (Qle_trans _ (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) _).
    - apply (Q.min_glb_r eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) eps1).
      apply Qle_refl.
    - apply (Q.min_glb_l el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))
                    (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K)))).
      apply Qle_refl. }
  assert (Hep1e3 : Qle eps1 (1 # 3)%Q).
  { apply (Qle_trans _ (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) _).
    - apply (Q.min_glb_r eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) eps1).
      apply Qle_refl.
    - apply (Qle_trans _ (Qmin (1 # 3)%Q ((1 # 2)%Q / K)) _).
      + apply (Q.min_glb_r el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))
                      (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K)))).
        apply Qle_refl.
      + apply (Q.min_glb_l (1 # 3)%Q ((1 # 2)%Q / K)
                    (Qmin (1 # 3)%Q ((1 # 2)%Q / K))).
        apply Qle_refl. }
  assert (Hep1inv : Qle eps1 ((1 # 2)%Q / K)).
  { apply (Qle_trans _ (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) _).
    - apply (Q.min_glb_r eg (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))) eps1).
      apply Qle_refl.
    - apply (Qle_trans _ (Qmin (1 # 3)%Q ((1 # 2)%Q / K)) _).
      + apply (Q.min_glb_r el (Qmin (1 # 3)%Q ((1 # 2)%Q / K))
                      (Qmin el (Qmin (1 # 3)%Q ((1 # 2)%Q / K)))).
        apply Qle_refl.
      + apply (Q.min_glb_r (1 # 3)%Q ((1 # 2)%Q / K)
                    (Qmin (1 # 3)%Q ((1 # 2)%Q / K))).
        apply Qle_refl. }
  assert (Hep1q4 : QltT 0 (eps1 * (1 # 4))%Q).
  { apply Qlt_to_QltT.
    apply (Qmult_lt_0_compat eps1 (1 # 4)%Q).
    - exact Hep1lt.
    - vm_compute. reflexivity. }
  destruct (lw0m_vanish_pi (eps1 * (1 # 4))%Q (qltw_pc_pw _ _ Hep1q4))
    as [Nv1 HNv1].
  set (N1 := Nat.max 1 (Nat.max Nv1 (Nat.max N3 N0l))).
  assert (HN1b : (Nat.max N3 N0l <= N1)%nat)
    by (apply (Nat.le_trans (Nat.max N3 N0l) (Nat.max Nv1 (Nat.max N3 N0l)) N1);
        [apply Nat.le_max_r | apply Nat.le_max_r]).
  assert (HNN3 : (N3 <= N1)%nat)
    by (apply (Nat.le_trans N3 (Nat.max N3 N0l) N1); [apply Nat.le_max_l | exact HN1b]).
  assert (HNN0l : (N0l <= N1)%nat)
    by (apply (Nat.le_trans N0l (Nat.max N3 N0l) N1); [apply Nat.le_max_r | exact HN1b]).
  assert (HNv1le : (Nv1 <= N1)%nat).
  { apply (Nat.le_trans Nv1 (Nat.max Nv1 (Nat.max N3 N0l)) N1).
    - apply Nat.le_max_l.
    - apply Nat.le_max_r. }
  assert (HNv1N : QltT (lw0m_e N1) (eps1 * (1 # 4))%Q).
  { apply (qltw_pw_pc _ _ (HNv1 N1 HNv1le)). }
  pose proof (QltT_to_Qlt _ _ HNv1N) as HNv1N'.
  assert (HN1 : (1 <= N1)%nat) by apply Nat.le_max_l.
  destruct (leibsep_gate_open q N1 (eps1 * (1 # 8))%Q) eqn:E1.
  - (* gate true: guarded kernel direct (1131 assembly true leg, verbatim) *)
    assert (Hc0 : QltT 0 (2 * (eps1 * (1 # 8)))%Q).
    { apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat 2 (eps1 * (1 # 8))%Q).
      - vm_compute. reflexivity.
      - apply (Qmult_lt_0_compat eps1 (1 # 8)%Q).
        + exact Hep1lt.
        + vm_compute. reflexivity. }
    assert (Hguard : QltT (lw0m_e N1 + 2 * (eps1 * (1 # 8))%Q)
                          (Qabs ((lw0m_xL N1 - q)%Q)))
      by (apply leibsep_gate_open_true; exact E1).
    destruct (leibsep_q_kernel_guarded q N1 (eps1 * (1 # 8))%Q HN1 Hguard) as [M HM].
    exists (2 * (eps1 * (1 # 8)))%Q. split; [exact Hc0 |].
    exists M. exact HM.
  - (* gate false: band location, Wb shrink, second gate split, carrier *)
    assert (Hwin : QleT' (Qabs ((lw0m_xL N1 - q)%Q))
                         (lw0m_e N1 + 2 * (eps1 * (1 # 8))%Q))
      by (apply leibsep_gate_open_false; exact E1).
    pose proof (QleT'_to_Qle _ _ Hwin) as Hwin'.
    assert (Hx3 : QltT e3 ((lw0m_xL N1 - 3)%Q)).
    { pose proof (HN3 N1 (NatLe_lift _ _ HNN3)) as H0. exact H0. }
    pose proof (QltT_to_Qlt _ _ Hx3) as Hx3'.
    assert (HxL : QltT el ((10 # 3)%Q - lw0m_xL N1)%Q).
    { pose proof (HN0l N1 (NatLe_lift _ _ HNN0l)) as H0. exact H0. }
    pose proof (QltT_to_Qlt _ _ HxL) as HxL'.
    pose proof (leibsep_qabs_le_two (lw0m_xL N1 - q)
                  (lw0m_e N1 + 2 * (eps1 * (1 # 8)))%Q Hwin') as Htwo.
    destruct Htwo as [Hshore1T Hshore2T].
    pose proof (QleT'_to_Qle _ _ Hshore1T) as Hshore1.
    pose proof (QleT'_to_Qle _ _ Hshore2T) as Hshore2.
    assert (E1m : leibsep_gate_open q (Nat.max N1 1) (eps1 * (1 # 8))%Q = false).
    { rewrite (Nat.max_l N1 1 HN1). exact E1. }
    assert (HN0e : forall n : nat, NatLe (Nat.max N0g N0l) n ->
              QltT eps1 ((10 / 3)%Q - lw0m_xL n)%Q).
    { intros n Hn. apply Qlt_to_QltT.
      apply (Qle_lt_trans eps1 el ((10 / 3)%Q - lw0m_xL n)%Q).
      - exact Hep1el.
      - apply QltT_to_Qlt. apply HN0l.
        apply NatLe_lift.
        apply (Nat.le_trans N0l (Nat.max N0g N0l) n).
        + apply Nat.le_max_r.
        + apply NatLe_drop. exact Hn. }
    assert (Hq0 : Qlt 0 q).
    { apply QltT_to_Qlt.
      apply (leibsep_shore_q_pos q eps1 (Nat.max N0g N0l) N1
               (Qlt_to_QltT 0 eps1 Hep1lt) HN0e
               (fun n Hn => qltw_pw_pc _ _ (HNv1 n (Nat.le_trans _ _ _ HNv1le Hn))) E1m). }
    assert (HQ103 : Qle q (10 # 3)%Q).
    { apply QleT'_to_Qle.
      apply (leibsep_shore_q_le_ten_thirds q eps1 (Nat.max N0g N0l) N1
               (Qlt_to_QltT 0 eps1 Hep1lt) HN0e
               (fun n Hn => qltw_pw_pc _ _ (HNv1 n (Nat.le_trans _ _ _ HNv1le Hn))) E1m). }
    assert (HQ0t : QltT 0 q) by (apply Qlt_to_QltT; exact Hq0).
    assert (HQ103T : QleT' q (10 # 3)%Q) by (apply Qle_to_QleT'; exact HQ103).
    pose proof (leibsep_Wb01_diff_lower b0 q n_sel (lw0_QltT_le b0 Hb0) HQ0t HQ103T Hns2) as HWbd.
    assert (HWb0 : QltT 0 (lw0_Wb b0 q n_sel 0)) by (apply lw0_Wb_pos; assumption).
    pose proof (QltT_to_Qlt _ _ HWb0) as HWb0'.
    pose (WING := (q_fact n_sel * (lw0_Wb b0 q n_sel 0 * (2 # 27))%Q)%Q).
    assert (HX : Qlt 0 WING).
    { unfold WING. apply Qmult_lt_0_compat.
      - apply q_fact_pos.
      - apply Qmult_lt_0_compat.
        + exact HWb0'.
        + vm_compute. reflexivity. }
    assert (Hinv2 : Qlt 0 (WING / (2 * K)%Q)).
    { apply (Qmult_lt_0_compat WING (/ (2 * K)%Q)).
      - exact HX.
      - apply Qinv_lt_0_compat. apply (Qlt_le_trans 0 (1 # 8) (2 * K)).
        + vm_compute. reflexivity.
        + rewrite (Qmult_comm 2 K).
          apply (Qle_trans (1 # 8)%Q ((1 # 16) * (2 # 1))%Q (K * 2)%Q).
          * apply (qeq_le (1 # 8)%Q ((1 # 16) * (2 # 1))%Q). ring.
          * apply (Qmult_le_compat_r (1 # 16)%Q K (2 # 1)).
            -- apply (Qle_trans (1 # 16)%Q (1 # 8) K).
               ++ apply Qlt_le_weak. vm_compute. reflexivity.
               ++ exact HK1.
            -- apply Qlt_le_weak. vm_compute. reflexivity. }
    pose (eps2 := Qmin eps1 (WING / (2 * K)%Q)).
    assert (Hep2lt : Qlt 0 eps2).
    { apply (Q.min_glb_lt _ _ 0); [exact Hep1lt | exact Hinv2]. }
  assert (Hep2le1 : Qle eps2 eps1).
  { apply (Q.min_glb_l eps1 (WING / (2 * K)%Q) eps2). apply Qle_refl. }
  assert (Hep2leW : Qle eps2 (WING / (2 * K)%Q)).
  { apply (Q.min_glb_r eps1 (WING / (2 * K)%Q) eps2). apply Qle_refl. }
    assert (Hep2e3 : QleT' eps2 (1 # 3)%Q).
    { apply Qle_to_QleT'. apply (Qle_trans eps2 eps1 (1 # 3)); [exact Hep2le1 | exact Hep1e3]. }
    assert (HEp2 : QltT 0 eps2) by (apply Qlt_to_QltT; exact Hep2lt).
    assert (HN0g2 : forall n : nat, NatLe N0g n ->
               QltT eps2 ((10 / 3)%Q - lw0m_xL n)%Q).
    { intros n Hn.
      apply (piL_hn0g2_under_ten_thirds eg eps2 N0g HN0g
               (Qle_trans eps2 eps1 eg Hep2le1 Hep1eg) n Hn). }
    assert (Hep2q4 : QltT 0 (eps2 * (1 # 4))%Q).
    { apply Qlt_to_QltT.
      apply (Qmult_lt_0_compat eps2 (1 # 4)%Q).
      - exact Hep2lt.
      - vm_compute. reflexivity. }
    destruct (lw0m_vanish_pi (eps2 * (1 # 4))%Q (qltw_pc_pw _ _ Hep2q4))
    as [Nv2 HNv2].
    set (N2 := Nat.max Nv2 1).
    assert (HN21 : (1 <= N2)%nat) by apply Nat.le_max_r.
    destruct (leibsep_gate_open q N2 (eps2 * (1 # 8))%Q) eqn:E2.
    + (* second gate true: same true leg at the shrunk eps2 *)
      assert (Hc0 : QltT 0 (2 * (eps2 * (1 # 8)))%Q).
      { apply Qlt_to_QltT.
        apply (Qmult_lt_0_compat 2 (eps2 * (1 # 8))%Q).
        - vm_compute. reflexivity.
        - apply (Qmult_lt_0_compat eps2 (1 # 8)%Q).
          + exact Hep2lt.
          + vm_compute. reflexivity. }
      assert (Hguard : QltT (lw0m_e N2 + 2 * (eps2 * (1 # 8))%Q)
                            (Qabs ((lw0m_xL N2 - q)%Q)))
        by (apply leibsep_gate_open_true; exact E2).
      destruct (leibsep_q_kernel_guarded q N2 (eps2 * (1 # 8))%Q HN21 Hguard) as [M HM].
      exists (2 * (eps2 * (1 # 8)))%Q. split; [exact Hc0 |].
      exists M. exact HM.
    + (* second gate false: caps chain then the carrier black box *)
      destruct (caps_scaled H1 H2 H3 q eps2 N0g Nv2 HEp2 Hep2e3 HN0g2
             (fun n Hn => qltw_pw_pc _ _ (HNv2 n Hn)) E2)
        as [s [t [M0 [Hs [Ht [Hs0 [Ht0 [Hscap Htcap]]]]]]]].
      assert (HCle : QleT'
               (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0 n_sel) n_sel) q) * t
                + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0 n_sel) n_sel)) q) * s
                + eps2 * (1 # 8))%Q
               (eps2 * (BF * ((11 # 3)%Q * S973 + (1 # 4))
                         + BFd * (S973 + (1 # 4)) + (1 # 8)))%Q)
        by exact (lw1131_C_le_eps0K q eps2 s t BF BFd n_sel Hs0 Ht0
                    (qleT'_refl BF) (qleT'_refl BFd) Hscap Htcap).
      assert (Hcan : ((1 # 2)%Q / K) * K == (1 # 2)%Q)
        by (apply lw1190_div_mul_cancel; intro Hz; apply (Qlt_not_eq 0 K HKpos);
            apply Qeq_sym; exact Hz).
      assert (HK1' : QleT' (eps2 * K) (1 # 2)%Q).
      { apply Qle_to_QleT'.
        pose proof (lw95_mul_le_compat eps2 ((1 # 2)%Q / K) K K
                      (Qlt_le_weak 0 eps2 Hep2lt)
                      (Qle_trans eps2 eps1 ((1 # 2)%Q / K) Hep2le1 Hep1inv)
                      HK0 (Qle_refl K)) as Hmul.
        rewrite <- Hcan. exact Hmul. }
      assert (HtwoK : Qlt 0 (2 * K)%Q).
      { apply (Qlt_le_trans 0 ((1 # 8) * (2 # 1))%Q (2 * K)).
        - vm_compute. reflexivity.
        - rewrite (Qmult_comm 2 K).
          apply (Qmult_le_compat_r (1 # 8)%Q K (2 # 1)).
          + exact HK1.
          + apply Qlt_le_weak. vm_compute. reflexivity. }
      assert (Hcan2 : (WING / (2 * K)%Q) * K == WING * (1 # 2)%Q)
        by (unfold Qdiv; field; intro Hz; apply (Qlt_not_eq 0 K HKpos);
            apply Qeq_sym; exact Hz).
      assert (HWle : Qle WING (q_fact n_sel * (lw0_Wb b0 q n_sel 0 - lw0_Wb b0 q n_sel 1))).
      { pose proof (QleT'_to_Qle _ _ HWbd) as HWbd'.
        unfold WING.
        rewrite (Qmult_comm (q_fact n_sel)).
        rewrite (Qmult_comm (q_fact n_sel)).
        apply (Qmult_le_compat_r (lw0_Wb b0 q n_sel 0 * (2 # 27))%Q _ (q_fact n_sel)).
        - exact HWbd'.
        - apply Qlt_le_weak. apply q_fact_pos. }
      assert (HP2 : QltT
               (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0 n_sel) n_sel) q) * t
                + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0 n_sel) n_sel)) q) * s
                + eps2 * (1 # 8))%Q
               (q_fact n_sel * (lw0_Wb b0 q n_sel 0 - lw0_Wb b0 q n_sel 1))).
      { apply Qlt_to_QltT. apply (Qle_lt_trans _ (eps2 * K) _).
        - exact (QleT'_to_Qle _ _ HCle).
        - pose proof (lw95_mul_le_compat eps2 (WING / (2 * K)%Q) K K
                        (Qlt_le_weak 0 eps2 Hep2lt) Hep2leW HK0 (Qle_refl K)) as Hmul2.
          rewrite Hcan2 in Hmul2.
          assert (Hhalf : Qlt (WING * (1 # 2))%Q WING).
          { apply (Qlt_le_trans (WING * (1 # 2)) (WING * 1) WING).
            - rewrite (Qmult_comm WING (1 # 2)). rewrite (Qmult_comm WING 1).
              apply (Qmult_lt_compat_r (1 # 2) 1 WING).
              + exact HX.
              + vm_compute. reflexivity.
            - apply qeq_le. ring. }
          apply (Qlt_le_trans _ WING _).
          + apply (Qle_lt_trans _ (WING * (1 # 2))%Q _).
            * exact Hmul2.
            * exact Hhalf.
          + exact HWle. }
      assert (HP1 : QleT'
               (Qabs (qpoly_eval (lw0_F (lw0_niven_f q b0 n_sel) n_sel) q) * t
                + Qabs (qpoly_eval (qpoly_deriv (lw0_F (lw0_niven_f q b0 n_sel) n_sel)) q) * s
                + eps2 * (1 # 8))%Q
               (1 # 2)%Q).
      { apply (qleT'_trans _ (eps2 * K)%Q).
        - exact HCle.
        - exact HK1'. }
      exact (leibsep_q_kernel_gate_carrier q eps2 N0g Nv2 s t M0 HEp2 HN0g2
             (fun n Hn => qltw_pw_pc _ _ (HNv2 n Hn)) Hs Ht HP1 HP2).
Qed.

End KernelDistilled.

(* -----------------------------------------------------------------------
   Statement provenance: each entry lists a statement of this file and,
   where the statement restates a result of the source development, the
   source file and line recorded at migration time (coordinates frozen
   as recorded).  Entries marked "new in this file" are statements
   introduced here.
   ----------------------------------------------------------------------- *)
(*
   1. [And] -- new in this file
   2. [NatLe] -- new in this file
   3. [NatLe_drop] -- source: S01_BaseRing.v@91
   4. [NatLe_lift] -- new in this file
   5. [QltT_to_Qlt] -- source: S02_CauchyComplete.v@50
   6. [Qlt_to_QltT] -- new in this file
   7. [QleT'_to_Qle] -- source: S02_CauchyComplete.v@103
   8. [Qle_to_QleT'] -- source: S02_CauchyComplete.v@115
   9. [qleT'_refl] -- source: S02_CauchyComplete.v@182
  10. [qleT'_trans] -- source: S02_CauchyComplete.v@201
  11. [qeq_le] -- new in this file
  12. [Qle_plus_nonneg_r] -- source: S02_CauchyComplete.v@529
  13. [qleT'_plus_nonneg_rT] -- source: S02_CauchyComplete.v@227
  14. [qeq_leT'] -- new in this file
  15. [qleT'_plus_compat] -- new in this file
  16. [q_neq_of_lt] -- source: S03_QExp.v@84
  17. [Qle_div_same_denom] -- source: S03_QExp.v@110
  18. [q_le_div_le] -- new in this file
  19. [q_lt_0_odd_den] -- new in this file
  20. [sc_lpa_decr_le] -- source: S10_KVQuantTrig.v@2710
  21. [sc_lpa_nonneg] -- source: S10_KVQuantTrig.v@2719
  22. [sc_lp_pair_nonneg] -- source: S10_KVQuantTrig.v@2727
  23. [sc_lp_odd_mono] -- source: S10_KVQuantTrig.v@2734
  24. [sc_lp_odd_chain] -- new in this file
  25. [nat_le_Sn_n_absurd] -- new in this file
  26. [sc_lp_ev_decr] -- new in this file
  27. [sc_lp_ev_le_s6] -- new in this file
  28. [sc_lp_odd_le_s6] -- source: S10_KVQuantTrig.v@8775
  29. [sc_lp_four_nonneg] -- new in this file
  30. [sc_lp_three_value] -- new in this file
  31. [sc_lp_three_margin] -- new in this file
  32. [sc_lp_six_value] -- new in this file
  33. [sc_lp_six_margin] -- new in this file
  34. [piL_xL_under_ten_thirds] -- new in this file
  35. [piL_xL_over_three] -- new in this file
  36. [piL_ten_thirds_supply] -- new in this file
  37. [piL_leibniz_ten_thirds_supply] -- new in this file
  38. [piL_three_supply] -- new in this file
  39. [piL_hn0g2_under_ten_thirds] -- new in this file
  40. [QPoly] -- source: LW0PiIrrational.v@48
  41. [qpoly_add] -- source: LW0PiIrrational.v@51
  42. [qpoly_scalar] -- source: LW0PiIrrational.v@59
  43. [qpoly_mul] -- new in this file
  44. [qpoly_eval] -- source: LW0PiIrrational.v@77
  45. [qpoly_deriv] -- source: LW0PiIrrational.v@101
  46. [qpoly_deriv_iter] -- new in this file
  47. [q_pow] -- source: S03_QExp.v@36
  48. [q_fact] -- new in this file
  49. [q_lt_0_succ_den] -- source: S03_QExp.v@70
  50. [q_fact_pos] -- new in this file
  51. [lw0_alt] -- source: LW0PiIrrational.v@4292
  52. [lw0_q_pow_pos] -- new in this file
  53. [lw0_QltT_le] -- new in this file
  54. [lw0_Wb] -- source: LW0PiIrrational.v@1336
  55. [lw0_Wb_pos] -- new in this file
  56. [lw0_sin_aux] -- source: LW0PiIrrational.v@3473
  57. [lw0_sin_qp] -- new in this file
  58. [lw0_F_aux] -- source: LW0PiIrrational.v@4337
  59. [lw0_F] -- new in this file
  60. [lw0_pi_mono] -- new in this file
  61. [lw0_pi_qminus_pow] -- new in this file
  62. [lw0_niven_f] -- new in this file
  63. [lw0_n_select] -- new in this file
  64. [lw0_pi_d0_of] -- new in this file
  65. [leibsep_qlt_wd2] -- source: LW0LeibSeparation.v@67
  66. [leibsep_qle_wd2] -- source: LW0LeibSeparation.v@74
  67. [leibsep_qlt_minus] -- source: LW0LeibSeparation.v@81
  68. [leibsep_qlt_of_minus] -- source: LW0LeibSeparation.v@84
  69. [leibsep_qle_minus] -- source: LW0LeibSeparation.v@87
  70. [leibsep_qle_of_minus] -- source: LW0LeibSeparation.v@90
  71. [leibsep_qlt_1] -- source: LW0LeibSeparation.v@93
  72. [leibsep_qlt_half] -- source: LW0LeibSeparation.v@96
  73. [leibsep_qlt_half_1] -- new in this file
  74. [leibsep_qabs_le_two] -- new in this file
  75. [lw0_opp_le_swap] -- new in this file
  76. [leibsep_abs_ge_self] -- source: LW0LeibSeparation.v@1896
  77. [leibsep_abs_ge_opp] -- new in this file
  78. [leibsep_qeq_le] -- new in this file
  79. [leibsep_abssum] -- source: LW0LeibSeparation.v@914
  80. [leibsep_abssum_cos] -- new in this file
  81. [leibsep_shore_upper] -- new in this file
  82. [leibsep_shore_W_le] -- new in this file
  83. [leibsep_shore_gap_upper] -- new in this file
  84. [q_pow_succ] -- source: S03_QExp.v@64
  85. [q_fact_succ] -- source: S03_QExp.v@67
  86. [q_pow_abs] -- source: S03_QExp.v@54
  87. [q_pow_nonneg] -- source: S03_QExp.v@77
  88. [q_pow_mono] -- source: S03_QExp.v@774
  89. [q_pow_wd] -- new in this file
  90. [q_succ_add] -- new in this file
  91. [q_pow_diff_bound] -- new in this file
  92. [q_ratio_cancel_succ] -- new in this file
  93. [sin_term] -- new in this file
  94. [cos_term] -- source: S10_KVQuantTrig.v@1213
  95. [sin_partial] -- source: S10_KVQuantTrig.v@1217
  96. [cos_partial] -- source: S10_KVQuantTrig.v@1224
  97. [sc_q_pow_one] -- source: S10_KVQuantTrig.v@1231
  98. [sc_abs_sign] -- new in this file
  99. [sc_sin_term_diff] -- new in this file
 100. [sc_cos_term_diff] -- new in this file
 101. [leibsep_sin_partial_lipschitz] -- source: LW0LeibSeparation.v@929
 102. [leibsep_cos_partial_lipschitz] -- new in this file
 103. [qeq_imp_qle] -- source: S02_CauchyComplete.v@130
 104. [qeq_ltT] -- source: S02_CauchyComplete.v@297
 105. [lw0_q_eq_le] -- source: LW0PiIrrational.v@4034
 106. [lw0_q_of_nat] -- source: LW0PiIrrational.v@397
 107. [lw0_q_of_nat_nonneg] -- source: LW0PiIrrational.v@400
 108. [lw0_q_of_nat_ge_one] -- source: LW0PiIrrational.v@407
 109. [lw0_q_of_nat_le_succ] -- source: LW0PiIrrational.v@414
 110. [lw0_q_of_nat_le_add] -- source: LW0PiIrrational.v@421
 111. [lw0_q_of_nat_le_mono] -- source: LW0PiIrrational.v@1141
 112. [lw0_q_of_nat_succ] -- source: LW0PiIrrational.v@1145
 113. [lw0_q_of_nat_add] -- source: LW0PiIrrational.v@1149
 114. [lw0_q_mult_le_l] -- new in this file
 115. [lw0_pitS_qne0_of_pos] -- source: LW0PiIrrational.v@8949
 116. [lw0_pitS_qof_add] -- source: LW0PiIrrational.v@8962
 117. [lw0_pitS_qof_mul] -- source: LW0PiIrrational.v@8969
 118. [lw0_pitS_qmult_reg_r] -- new in this file
 119. [lw0_pi_d0_absorb] -- source: LW0PiIrrational.v@9530
 120. [lw0_pi_b_den_pos] -- new in this file
 121. [qpoly_eval_add] -- new in this file
 122. [qpoly_eval_scalar] -- new in this file
 123. [qpoly_eval_deriv_cons] -- new in this file
 124. [lw0_q_int_inv] -- new in this file
 125. [lw0_q_div_int_mul] -- new in this file
 126. [lw0_qp_ai] -- new in this file
 127. [lw0_qp_antideriv] -- new in this file
 128. [lw0_qp_ai_cons_eval] -- new in this file
 129. [lw0_qp_ai_zero_head_eval] -- new in this file
 130. [lw0_qp_ai_add] -- new in this file
 131. [lw0_qp_ai_scalar] -- new in this file
 132. [lw0_qp_ai_deriv_pair] -- new in this file
 133. [lw0_qp_antideriv_deriv] -- new in this file
 134. [lw0_qp_ai_deriv_ft] -- new in this file
 135. [lw0_qp_antideriv_deriv_at] -- new in this file
 136. [lw0_qp_deriv_iter_plus] -- new in this file
 137. [lw0_qp_pair] -- new in this file
 138. [lw0_qp_ai_mul_add_l] -- new in this file
 139. [lw0_qp_pair_add_l] -- new in this file
 140. [lw0_q_pow_zero_succ] -- new in this file
 141. [lw0_qp_ai_deriv_ft_pow] -- new in this file
 142. [lw0_qp_pair_ibp_family] -- new in this file
 143. [lw0_qp_pair_ibp] -- new in this file
 144. [lw0_cos_aux] -- new in this file
 145. [lw0_cos_qp] -- new in this file
 146. [lw0_sin_aux_eval] -- new in this file
 147. [lw0_sin_partial_zero] -- new in this file
 148. [lw0_sin_qp_eval] -- new in this file
 149. [lw0_sin_qp_zero_eval] -- new in this file
 150. [lw0_cos_aux_eval] -- new in this file
 151. [lw0_cos_partial_zero] -- new in this file
 152. [lw0_cos_qp_eval] -- new in this file
 153. [lw0_cos_qp_zero_eval] -- new in this file
 154. [lw0_q_div_int_mul_gen] -- new in this file
 155. [lw0_sin_aux_deriv_eval] -- new in this file
 156. [lw0_cos_aux_deriv_eval_S] -- new in this file
 157. [lw0_sin_qp_deriv_eval] -- new in this file
 158. [lw0_cos_qp_deriv_eval] -- new in this file
 159. [qpoly_map] -- new in this file
 160. [lw0_q_abs_div] -- new in this file
 161. [lw0_qp_ai_abs_bound] -- new in this file
 162. [lw0_die] -- new in this file
 163. [lw0_alt_opp] -- new in this file
 164. [lw0_Qmake_succ_eq] -- new in this file
 165. [lw0_coef] -- new in this file
 166. [lw0_coef_add] -- new in this file
 167. [lw0_coef_scalar] -- new in this file
 168. [lw0_coef_deriv] -- new in this file
 169. [lw0_coef_iter_mul] -- new in this file
 170. [lw0_coef_iter_add] -- new in this file
 171. [lw0_coef_iter_scalar] -- new in this file
 172. [lw0_die_budget_mono] -- new in this file
 173. [lw0_die_scalar] -- new in this file
 174. [lw0_die_add] -- new in this file
 175. [lw0_die_mul_sharp] -- new in this file
 176. [lw0_pi_mono_die] -- new in this file
 177. [lw0_pi_qminus_pow_die] -- new in this file
 178. [lw0_niven_f_die] -- new in this file
 179. [lw0_qpoly_eq] -- new in this file
 180. [qpoly_shift] -- new in this file
 181. [lw0_qmake_Z_succ] -- new in this file
 182. [lw0_qmake_add] -- new in this file
 183. [lw0_qmake_2] -- new in this file
 184. [lw0_qmake_1] -- new in this file
 185. [lw0_qpoly_eq_refl] -- new in this file
 186. [lw0_qpoly_eq_sym] -- new in this file
 187. [lw0_qpoly_eq_trans] -- new in this file
 188. [lw0_cons_congr] -- new in this file
 189. [lw0_qpoly_eq_add] -- new in this file
 190. [lw0_qpoly_add_assoc] -- new in this file
 191. [lw0_qpoly_eq_deriv] -- new in this file
 192. [lw0_coef_shift] -- new in this file
 193. [lw0_coef_shift_1] -- new in this file
 194. [lw0_coef_shift_2] -- new in this file
 195. [lw0_coef_shift_lt] -- new in this file
 196. [lw0_shift1_deriv_coef] -- new in this file
 197. [lw0_shift_add] -- new in this file
 198. [lw0_shift_shift] -- new in this file
 199. [lw0_shift_congr] -- new in this file
 200. [lw0_cons2_shift2] -- new in this file
 201. [lw0_scal_pair_shift] -- new in this file
 202. [lw0_sin_aux_scal_append] -- new in this file
 203. [lw0_cos_aux_congr] -- new in this file
 204. [lw0_sin_aux_congr] -- new in this file
 205. [lw0_Wp] -- new in this file
 206. [lw0_Xc] -- new in this file
 207. [lw0_Wp_nil] -- new in this file
 208. [lw0_Xc_nil] -- new in this file
 209. [lw0_Wp_push] -- new in this file
 210. [lw0_Xc_push] -- new in this file
 211. [lw0_sin_qmake_key] -- new in this file
 212. [lw0_cos_qmake_key] -- new in this file
 213. [lw0_sin_aux_deriv_poly_gen] -- new in this file
 214. [lw0_cos_aux_deriv_S_poly_gen] -- new in this file
 215. [lw0_sin_qp_deriv_poly] -- new in this file
 216. [lw0_cos_qp_deriv_poly] -- new in this file
 217. [lw0_sin_qp_deriv2] -- new in this file
 218. [lw0_pitB_conv_zero_shift] -- new in this file
 219. [QeqT] -- source: S02_CauchyComplete.v@303
 220. [qeq_imp_qeqT] -- source: S02_CauchyComplete.v@309
 221. [qeqT_imp_qeq] -- new in this file
 222. [lw0_qpoly_eqT] -- new in this file
 223. [lw385_q_fact_neq] -- new in this file
 224. [lw385_Qplus_eq_compat_r] -- new in this file
 225. [lw385_Qplus_eq_compat2] -- new in this file
 226. [lw385_eq_Id] -- new in this file
 227. [lw385_andb_Id] -- new in this file
 228. [lw385_die_length] -- new in this file
 229. [lw385_coef_len_zero] -- new in this file
 230. [lw385_die_coef_zero] -- new in this file
 231. [lw385_F_aux_plus_deriv2_coef] -- new in this file
 232. [lw385_F_plus_deriv2_coef] -- new in this file
 233. [lw385_F_plus_deriv2_coef_niven] -- new in this file
 234. [lw385_ai_mul_zero] -- new in this file
 235. [lw385_ai_mul_congr_eval] -- new in this file
 236. [lw385_pair_congr_l] -- new in this file
 237. [lw385_pair_F_plus_deriv2] -- new in this file
 238. [lw385_pair_F_plus_deriv2_niven] -- new in this file
 239. [lw385_flip_aux] -- new in this file
 240. [lw385_q_pow_neg_even] -- new in this file
 241. [lw385_q_pow_neg_odd] -- new in this file
 242. [lw385_ai_zero_shift] -- new in this file
 243. [lw385_ai_delta_odd] -- new in this file
 244. [lw385_ai_mul_flip_aux] -- new in this file
 245. [lw385_ai_mul_flip] -- new in this file
 246. [lw385_qp_eval_q_wd] -- new in this file
 247. [lw385_pair_q_wd] -- new in this file
 248. [lw385_pair_abs_shore] -- new in this file
 249. [lw385_pair_flip_shore] -- new in this file
 250. [lw385_pair_flip_shore_mono] -- new in this file
 251. [lw0_ltT_leT_trans] -- new in this file
 252. [lw0_leT'_ltT_trans] -- new in this file
 253. [lw0_Qlt_le] -- new in this file
 254. [lw0_qmul_le0T] -- new in this file
 255. [lw0_qcompat4] -- new in this file
 256. [lw0_qcompat_r] -- new in this file
 257. [lw0_qcompat_l] -- new in this file
 258. [qltT_not_eq_zero] -- new in this file
 259. [qmult_ltT_0_compat] -- new in this file
 260. [lw0_q_pow_nonnegT] -- new in this file
 261. [lw0_q_of_nat_lt0T_S] -- new in this file
 262. [lw0_q_of_nat_lt0T] -- new in this file
 263. [lw0_mul_lt_one] -- new in this file
 264. [lw0_div_lt] -- new in this file
 265. [lw0_inv_le] -- new in this file
 266. [lw0_q_pow_mono_base] -- new in this file
 267. [lw0_q_fact_step] -- new in this file
 268. [lw0_fact_range] -- new in this file
 269. [lw0_q_fact_split] -- new in this file
 270. [lw0_fact_range_ge_pow] -- new in this file
 271. [lw0_q_pow_S] -- new in this file
 272. [lw0_q_fact_ne0] -- new in this file
 273. [lw0_Wb_nonneg] -- new in this file
 274. [lw0_Wb_ratio_eq] -- new in this file
 275. [lw0_frac_le] -- new in this file
 276. [lw0_lin_beat2] -- new in this file
 277. [lw0_lin_beat3] -- new in this file
 278. [lw0_twelve_AB_le] -- new in this file
 279. [lw0_Wb_ratio_bound] -- new in this file
 280. [lw0_Wb_seq_nonneg] -- new in this file
 281. [lw0_Wb_seq_decr] -- new in this file
 282. [altsum_qleT'_neg_le0] -- new in this file
 283. [altsum_qleT'_ge_sub] -- new in this file
 284. [altsum_acc] -- new in this file
 285. [altsum] -- new in this file
 286. [altsum_sgp] -- new in this file
 287. [altsum_acc_T] -- new in this file
 288. [altsum_acc_F] -- new in this file
 289. [altsum_acc_0_eq] -- new in this file
 290. [lw0_acc_add_gen] -- new in this file
 291. [lw0_altsum_add] -- new in this file
 292. [lw0_acc_quad] -- new in this file
 293. [lw0_pitS_q_pow_mul] -- new in this file
 294. [lw0_pitS_qmul_div_cancel] -- new in this file
 295. [lw0_pitS_div_lt_one] -- new in this file
 296. [lw0_pitS_pow_dec_helper] -- new in this file
 297. [lw0_pitS_pow_le_base] -- new in this file
 298. [lw0_pitS_Wbn0_scale_eq] -- new in this file
 299. [lw0_q_pow_add] -- new in this file
 300. [lw0_pitS_w0n_core] -- new in this file
 301. [lw0_pi_w0n_lt1] -- new in this file
 302. [leibsep_altsum_two_shore] -- new in this file
 303. [leibsep_w0n_xfer] -- new in this file
 304. [leibsep_w0n_step] -- new in this file
 305. [leibsep_w0n_pow] -- new in this file
 306. [leibsep_w0n_half] -- new in this file
 307. [qpoly_eval_mul] -- source: LW0PiIrrational.v@226
 308. [qpoly_deriv_iter_commute] -- source: LW0PiIrrational.v@381
 309. [lw0_q_fact_ge_one] -- source: LW0PiIrrational.v@470
 310. [lw0_q_fact_step2] -- source: LW0PiIrrational.v@482
 311. [lw0_q_pow_mult] -- source: LW0PiIrrational.v@1159
 312. [lw0_Qabs_pos_eq] -- source: LW0PiIrrational.v@1200
 313. [lw0_q_pow_one] -- source: LW0PiIrrational.v@1281
 314. [qpoly_opp] -- source: LW0PiIrrational.v@2491
 315. [lw0_mono] -- source: LW0PiIrrational.v@2874
 316. [lw0_qp_ai_mul_scalar_l] -- source: LW0PiIrrational.v@2939
 317. [lw0_qp_ai_mul_add_r] -- source: LW0PiIrrational.v@2967
 318. [lw0_qp_ai_mul_scalar_r] -- source: LW0PiIrrational.v@3001
 319. [lw0_qp_pair_add_r] -- source: LW0PiIrrational.v@3046
 320. [lw0_qp_pair_scalar_l] -- source: LW0PiIrrational.v@3062
 321. [lw0_qp_pair_scalar_r] -- source: LW0PiIrrational.v@3075
 322. [lw0_eval_opp] -- source: LW0PiIrrational.v@4508
 323. [lw0_Qmake_plus] -- source: LW0PiIrrational.v@4516
 324. [lw0_Qmake_succ] -- source: LW0PiIrrational.v@4525
 325. [lw0_coef_opp] -- source: LW0PiIrrational.v@4592
 326. [lw0_coef_iter_opp] -- source: LW0PiIrrational.v@4669
 327. [lw0_eval_at_zero] -- source: LW0PiIrrational.v@4684
 328. [lw0_eval_deriv_coef0] -- source: LW0PiIrrational.v@4689
 329. [lw0_eval_zero_coef] -- source: LW0PiIrrational.v@4706
 330. [lw0_eval_len_indep] -- source: LW0PiIrrational.v@4717
 331. [lw0_coef_iter_congr] -- source: LW0PiIrrational.v@4737
 332. [lw0_eval_iter_congr] -- source: LW0PiIrrational.v@4747
 333. [lw0_eval_deriv_iter_add] -- source: LW0PiIrrational.v@4758
 334. [lw0_eval_deriv_iter_scalar] -- source: LW0PiIrrational.v@4770
 335. [lw0_eval_iter_opp] -- source: LW0PiIrrational.v@4781
 336. [lw0_pred_iter] -- source: LW0PiIrrational.v@4796
 337. [lw0_shift_deriv] -- source: LW0PiIrrational.v@4802
 338. [lw0_qtail] -- source: LW0PiIrrational.v@4841
 339. [lw0_qtail_deriv_congr] -- source: LW0PiIrrational.v@4846
 340. [lw0_qtail_step] -- source: LW0PiIrrational.v@4873
 341. [lw0_coef_mul_mono_lt] -- source: LW0PiIrrational.v@4918
 342. [lw0_coef_mul_mono_ge] -- source: LW0PiIrrational.v@4943
 343. [lw0_qminus_pow] -- source: LW0PiIrrational.v@4966
 344. [lw0_niven_f_z] -- source: LW0PiIrrational.v@4976
 345. [lw0_niven_deriv_zero_0] -- source: LW0PiIrrational.v@4981
 346. [lw0_coef_mul_h0] -- source: LW0PiIrrational.v@4994
 347. [lw0_coef_mul_hS] -- new in this file
 348. [bpa_binom] -- source: UpReqBanachAdd.v@53
 349. [bpa_binom_pascal] -- source: UpReqBanachAdd.v@68
 350. [bpa_binom_0] -- source: UpReqBanachAdd.v@74
 351. [bpa_binom_out] -- source: UpReqBanachAdd.v@78
 352. [lw0_sub_succ_eq] -- new in this file
 353. [lw0_coef_qminus_pow] -- source: LW0PiIrrational.v@5042
 354. [lw0_ratio] -- source: LW0PiIrrational.v@5088
 355. [lw0_fact_ratio] -- source: LW0PiIrrational.v@5095
 356. [lw0_Qmake_mul] -- source: LW0PiIrrational.v@5119
 357. [lw0_qfact_Z] -- source: LW0PiIrrational.v@5122
 358. [lw0_binom] -- source: LW0PiIrrational.v@5162
 359. [lw0_binom_out] -- source: LW0PiIrrational.v@5184
 360. [lw0_zsign] -- source: LW0PiIrrational.v@5198
 361. [lw0_zsign_step] -- source: LW0PiIrrational.v@5204
 362. [lw0_z_lo] -- source: LW0PiIrrational.v@5212
 363. [lw0_z_hi] -- source: LW0PiIrrational.v@5237
 364. [lw0_qsum] -- source: LW0PiIrrational.v@5269
 365. [lw0_K_leg] -- source: LW0PiIrrational.v@5323
 366. [lw0_K] -- source: LW0PiIrrational.v@5329
 367. [lw0_pi_mono_eval] -- source: LW0PiIrrational.v@5468
 368. [lw0_pi_qminus_pow_eval] -- source: LW0PiIrrational.v@5485
 369. [Powpos] -- source: LW0PiIrrational.v@5952
 370. [lw0_posnat_zeq] -- source: LW0PiIrrational.v@5958
 371. [lw0_zpower_nat_add] -- source: LW0PiIrrational.v@5967
 372. [lw0_zpos_pospow] -- source: LW0PiIrrational.v@5976
 373. [lw0_q_pow_qmake] -- source: LW0PiIrrational.v@5985
 374. [lw0_q_pow_m1] -- source: LW0PiIrrational.v@5996
 375. [lw0_bpa_binom_eq] -- source: LW0PiIrrational.v@6009
 376. [lw0_sub_sub_shift] -- new in this file
 377. [lw0_conn_lo] -- source: LW0PiIrrational.v@6027
 378. [lw0_conn_hi] -- source: LW0PiIrrational.v@6063
 379. [lw0_alt_zsign] -- source: LW0PiIrrational.v@6319
 380. [lw0_pitB_ibp_dbl] -- source: LW0PiIrrational.v@6627
 381. [lw0_pitB_ai_mul01] -- source: LW0PiIrrational.v@6653
 382. [lw0_pitB_ai_mulA] -- source: LW0PiIrrational.v@6674
 383. [lw0_pitB_ai_monoL] -- source: LW0PiIrrational.v@6703
 384. [lw0_pitB_ai_pair2] -- source: LW0PiIrrational.v@6730
 385. [lw0_pitB_div_scale] -- source: LW0PiIrrational.v@6756
 386. [lw0_pitB_E] -- source: LW0PiIrrational.v@6768
 387. [lw0_pitB_ai_sin_aux] -- source: LW0PiIrrational.v@6829
 388. [lw0_pitB_ai_mul_sin_aux] -- source: LW0PiIrrational.v@6875
 389. [lw0_pitB_ai_mul_cons0] -- source: LW0PiIrrational.v@6919
 390. [lw0_pitB_ai_mul_cons1] -- source: LW0PiIrrational.v@6948
 391. [lw0_pitB_acc_S] -- source: LW0PiIrrational.v@6972
 392. [lw0_pitB_altsum_S] -- source: LW0PiIrrational.v@6995
 393. [lw0_pitB_q_pow_add] -- source: LW0PiIrrational.v@7005
 394. [lw0_pitB_Qeq_cancel_l] -- source: LW0PiIrrational.v@7016
 395. [lw0_pitB_bridge_aux] -- source: LW0PiIrrational.v@7032
 396. [lw0_pitB_bridge] -- source: LW0PiIrrational.v@7138
 397. [lw0_pitB_conv_lw0_succ] -- source: LW0PiIrrational.v@7231
 398. [lw0_pitB_conv_mult_le_l] -- source: LW0PiIrrational.v@7240
 399. [lw0_pitB_conv_pow2_ge] -- source: LW0PiIrrational.v@7250
 400. [lw0_pitB_conv_half_le1] -- source: LW0PiIrrational.v@7284
 401. [lw0_pitB_conv_half_mono] -- source: LW0PiIrrational.v@7296
 402. [lw0_pitB_conv_div_mul_cancel] -- source: LW0PiIrrational.v@7354
 403. [lw0_pitB_conv_geomscale] -- source: LW0PiIrrational.v@7367
 404. [lw0_pitB_conv_qabs_pow] -- source: LW0PiIrrational.v@7424
 405. [lw0_pitB_conv_t_nonneg] -- source: LW0PiIrrational.v@7445
 406. [lw0_pitB_conv_tstep] -- source: LW0PiIrrational.v@7456
 407. [lw0_pitB_conv_half_iter] -- source: LW0PiIrrational.v@7799
 408. [lw0_pitB_conv_qthr] -- source: LW0PiIrrational.v@7837
 409. [lw0_pitB_conv_qeqL_ltT] -- source: LW0PiIrrational.v@7930
 410. [lw0_pitB_conv_qeqR_ltT] -- source: LW0PiIrrational.v@7939
 411. [lw0_pitB_conv_t_vanish] -- source: LW0PiIrrational.v@7948
 412. [lw0_pitB_conv_pwi] -- source: LW0PiIrrational.v@8539
 413. [lw0_pitB_conv_pwi_scalar] -- source: LW0PiIrrational.v@8554
 414. [lw0_pitB_conv_pwi_add_le] -- source: LW0PiIrrational.v@8585
 415. [lw0_pitB_conv_pwi_mul_le] -- source: LW0PiIrrational.v@8649
 416. [lw0_pitB_conv_pwi_ai_le] -- source: LW0PiIrrational.v@8681
 417. [lw0_pitB_conv_pair_vanish] -- source: LW0PiIrrational.v@8745
 418. [lw0_pi_qeq_ltT_r] -- source: LW0PiIrrational.v@9709
 419. [lw0_pitB_pair_rtail] -- source: LW0PiIrrational.v@10001
 420. [lw0_pitB_pair_rtail_vanish_gap] -- source: LW0PiIrrational.v@10026
 421. [lw0_add_nil_r] -- source: LW0PiIrrational.v@10290
 422. [lw0_mul_nil_r_coef] -- source: LW0PiIrrational.v@10298
 423. [lw0_mul_scalar_left] -- source: LW0PiIrrational.v@10312
 424. [lw0_mul_add_left] -- source: LW0PiIrrational.v@10332
 425. [lw0_mul_cons0_left] -- source: LW0PiIrrational.v@10359
 426. [lw0_mul_assoc] -- source: LW0PiIrrational.v@10371
 427. [lw0_mul_unit_right] -- source: LW0PiIrrational.v@10403
 428. [lw0_mul_cons0_right] -- source: LW0PiIrrational.v@10418
 429. [lw0_mul_comm] -- source: LW0PiIrrational.v@10438
 430. [lw0_lintail_qtail] -- source: LW0PiIrrational.v@10470
 431. [lw0_cons0_congr] -- source: LW0PiIrrational.v@10485
 432. [lw0_pi_mono_cons0] -- source: LW0PiIrrational.v@10495
 433. [lw0_pi_qminus_qtail] -- source: LW0PiIrrational.v@10507
 434. [lw0_mul_tshift] -- source: LW0PiIrrational.v@10515
 435. [lw0_qtail_eval_0] -- source: LW0PiIrrational.v@10526
 436. [lw0_deriv_iter_one] -- source: LW0PiIrrational.v@10542
 437. [lw0_alt_double] -- source: LW0PiIrrational.v@10556
 438. [lw0_q_pow_m0] -- source: LW0PiIrrational.v@10567
 439. [lw0_pi_mirror_bnd] -- source: LW0PiIrrational.v@10580
 440. [lw0_niven_mirror] -- source: LW0PiIrrational.v@10619
 441. [lw0_niven_deriv_mirror_even] -- source: LW0PiIrrational.v@10689
 442. [lw0_coef_mul_congr] -- source: LW0PiIrrational.v@10750
 443. [lw0_pi_qminus_z_bridge] -- source: LW0PiIrrational.v@10768
 444. [lw0_pi_mono_z_bridge] -- source: LW0PiIrrational.v@10780
 445. [lw0_q_pow_one_base] -- source: LW0PiIrrational.v@10791
 446. [lw0_niven_scalar_bridge] -- source: LW0PiIrrational.v@10805
 447. [lw0_niven_pi_z_bridge] -- source: LW0PiIrrational.v@10832
 448. [lw0_niven_deriv_zero_0_ab] -- source: LW0PiIrrational.v@10852
 449. [lw0_niven_deriv_conn_lo_ab] -- source: LW0PiIrrational.v@10863
 450. [lw0_niven_deriv_conn_hi_ab] -- source: LW0PiIrrational.v@10875
 451. [lw0_F_eval_qsum] -- source: LW0PiIrrational.v@10887
 452. [lw0_qsum_ext2] -- source: LW0PiIrrational.v@10903
 453. [lw0_K_closure_F0Fq] -- source: LW0PiIrrational.v@10916
 454. [lw0_pitB_pair_rtail_vanish_hpair] -- source: LW0PiIrrational.v@10976
 455. [lw0_pitB_pair_conv_f] -- source: LW0PiIrrational.v@11840
 456. [lw0_pitB_pair_conv_delta] -- source: LW0PiIrrational.v@11851
 457. [lw0_pitB_pair_conv_delta'] -- source: LW0PiIrrational.v@11856
 458. [lw0_qpoly_eqT_of_prop] -- source: LW0PiIrrational.v@11865
 459. [lw0_qpoly_eq_prop_of_eqT] -- source: LW0PiIrrational.v@11871
 460. [lw0_qpoly_eqT_refl] -- source: LW0PiIrrational.v@11877
 461. [lw0_qpoly_eqT_sym] -- source: LW0PiIrrational.v@11882
 462. [lw0_qpoly_eqT_trans] -- source: LW0PiIrrational.v@11889
 463. [lw0_qpoly_eqT_add] -- source: LW0PiIrrational.v@11898
 464. [lw0_qpoly_eqT_cons_congr] -- source: LW0PiIrrational.v@11908
 465. [lw0_pitB_pair_conv_scalar_congr] -- source: LW0PiIrrational.v@11919
 466. [lw0_pitB_pair_conv_mul_r] -- source: LW0PiIrrational.v@11927
 467. [lw0_pitB_pair_conv_coef_ai] -- source: LW0PiIrrational.v@11959
 468. [lw0_pitB_pair_conv_ai_congr] -- source: LW0PiIrrational.v@11974
 469. [lw0_pitB_pair_conv_pair_congr_r] -- source: LW0PiIrrational.v@11984
 470. [lw0_pitB_pair_conv_zshift_bridge] -- source: LW0PiIrrational.v@12013
 471. [lw0_pitB_pair_conv_delta_br] -- source: LW0PiIrrational.v@12024
 472. [lw0_pitB_pair_conv_sin_aux_hi] -- source: LW0PiIrrational.v@12033
 473. [lw0_pitB_pair_conv_sin_aux_lo] -- source: LW0PiIrrational.v@12055
 474. [lw0_pitB_pair_conv_qdiv_mult_inv] -- source: LW0PiIrrational.v@12097
 475. [lw0_pitB_pair_conv_sin_inc] -- source: LW0PiIrrational.v@12102
 476. [lw0_pitB_pair_conv_qabs_sign1] -- source: LW0PiIrrational.v@12152
 477. [lw0_pitB_pair_conv_sig2] -- source: LW0PiIrrational.v@12162
 478. [lw0_pitB_pair_conv_sinc] -- source: LW0PiIrrational.v@12182
 479. [lw0_pitB_pair_conv_core] -- source: LW0PiIrrational.v@12216
 480. [lw0_pitB_pair_conv_qabs_canon] -- source: LW0PiIrrational.v@12262
 481. [lw0_pitB_pair_conv_qabs_wd] -- source: LW0PiIrrational.v@12277
 482. [lw0_pitB_conv_pwi_shift1_eq] -- source: LW0PiIrrational.v@12300
 483. [lw0_pitB_conv_pwi_zero_shift_eq] -- source: LW0PiIrrational.v@12314
 484. [lw0_pitB_conv_div_den_mono] -- source: LW0PiIrrational.v@12337
 485. [lw0_pitB_conv_pwi_k_mono] -- source: LW0PiIrrational.v@12382
 486. [lw0_pitB_conv_pwi_add_k_mono] -- source: LW0PiIrrational.v@12426
 487. [lw0_pitB_conv_pwi_nonneg] -- source: LW0PiIrrational.v@12443
 488. [lw0_pitB_conv_pwi_one_eq] -- source: LW0PiIrrational.v@12474
 489. [lw0_pitB_conv_pwi_muliter] -- source: LW0PiIrrational.v@12489
 490. [lw0_pitB_conv_pwi_mul_le_iter] -- source: LW0PiIrrational.v@12497
 491. [lw0_pitB_conv_pwi_shift_one_domin] -- source: LW0PiIrrational.v@12524
 492. [lw0_pitB_conv_pwi_muliter_scalar] -- source: LW0PiIrrational.v@12543
 493. [lw0_pitB_conv_pwi_muliter_shift] -- source: LW0PiIrrational.v@12571
 494. [lw0_pitB_conv_pwi_muliter_eq] -- source: LW0PiIrrational.v@12615
 495. [lw0_pitB_conv_pwi_mul_shift_domin] -- source: LW0PiIrrational.v@12636
 496. [lw0_pitB_conv_pair_deltamul_weight] -- source: LW0PiIrrational.v@12672
 497. [lw0_pitB_conv_pair_vanish_deltam] -- source: LW0PiIrrational.v@12752
 498. [lw0_pitB_pair_conv] -- source: LW0PiIrrational.v@13267
 499. [lw0_pitB_pair_rtail_vanish] -- new in this file
 500. [lw0_z_lo_integer] -- new in this file
 501. [lw0_z_hi_integer] -- new in this file
 502. [lw0_sigT_plus] -- new in this file
 503. [lw0_sigT_Zscale] -- new in this file
 504. [lw0_qsum_integer] -- new in this file
 505. [lw0_K_leg_integer] -- new in this file
 506. [lw0_K_integer] -- new in this file
 507. [lw0_pi_contra_gate] -- new in this file
 508. [leibsep_abs3_split] -- new in this file
 509. [lw0_pitB_pair_telescope] -- new in this file
 510. [leibsep_pair_slack_bound] -- new in this file
 511. [leibsep_G4c_pair_slack_window_from] -- new in this file
 512. [leibsep_beta_contra] -- new in this file
 513. [leibsep_false_branch_contra] -- new in this file
 514. [leibsep_gate_open] -- source: LW0LeibSeparation.v@53
 515. [leibsep_gate_open_true] -- source: LW0LeibSeparation.v@182
 516. [lw0m_tail_bounded_pi] -- new in this file (internal design ledger)
 517. [leibsep_q_kernel_guarded] -- source: LW0LeibSeparation.v@220
 518. [leibsep_gate_open_false] -- new in this file
 519. [leibsep_closedband_of_gate_false] -- new in this file
 520. [leibsep_shore_q_le_ten_thirds] -- new in this file (internal design ledger)
 521. [leibsep_shore_q_pos] -- new in this file (internal design ledger)
 522. [leibsep_q_kernel_gate_carrier] -- source: LW0LeibSeparation.v@3928
 523. [piL_q_pow_0] -- new in this file (internal design ledger)
 524. [piL_q_fact_0] -- new in this file (internal design ledger)
 525. [piL_qdiv_1_r] -- new in this file (internal design ledger)
 526. [piL_sin_term_0] -- new in this file (internal design ledger)
 527. [piL_cos_term_0] -- new in this file (internal design ledger)
 528. [piL_sin_term_congr] -- new in this file (internal design ledger)
 529. [piL_cos_term_congr] -- new in this file (internal design ledger)
 530. [piL_sin_partial_congr] -- new in this file (internal design ledger)
 531. [piL_cos_partial_congr] -- new in this file (internal design ledger)
 532. [piL_sin_dres] -- source: S12_B5RecycleSF.v@8294
 533. [piL_sin_partial_double] -- new in this file (internal design ledger)
 534. [piL_sin_partial_double_at] -- new in this file (internal design ledger)
 535. [piL_cos_dres] -- source: S12_B5RecycleSF.v@8315
 536. [piL_cos_partial_double] -- new in this file (internal design ledger)
 537. [piL_pyth_dres] -- source: S12_B5RecycleSF.v@8138
 538. [piL_pythag_partial] -- new in this file (internal design ledger)
 539. [piL_quad_dres] -- source: S12_B5RecycleSF.v@8122
 540. [piL_sin_partial_quad] -- new in this file (internal design ledger)
 541. [piL_cos_quad_dres] -- source: S12_B5RecycleSF.v@8299
 542. [piL_cos_partial_quad] -- new in this file (internal design ledger)
 543. [piL_quad_vertex_factor] -- new in this file (internal design ledger)
 544. [piL_sin_quad_xL] -- new in this file (internal design ledger)
 545. [piL_cos_quad_xL] -- new in this file (internal design ledger)
 546. [piL_qabs_zero] -- new in this file (internal design ledger)
 547. [piL_qabs_two] -- new in this file (internal design ledger)
 548. [piL_qabs_four] -- new in this file (internal design ledger)
 549. [piL_qle_0_two] -- new in this file (internal design ledger)
 550. [piL_qle_0_four] -- new in this file (internal design ledger)
 551. [piL_mult_le_l] -- new in this file (internal design ledger)
 552. [piL_abs_div_pos_den] -- new in this file (internal design ledger)
 553. [piL_leT'_eq_intro_l] -- new in this file (internal design ledger)
 554. [piL_leT'_eq_intro_r] -- new in this file (internal design ledger)
 555. [piL_abs_mult_le] -- new in this file (internal design ledger)
 556. [piL_abs_coeff2_2] -- new in this file (internal design ledger)
 557. [piL_abs_coeff4_3] -- new in this file (internal design ledger)
 558. [piL_abs2_plus_le] -- new in this file (internal design ledger)
 559. [piL_abs3_plus_le] -- new in this file (internal design ledger)
 560. [piL_abs4_plus_le] -- new in this file (internal design ledger)
 561. [piL_abs_opp_le] -- new in this file (internal design ledger)
 562. [piL_abs2_le] -- new in this file (internal design ledger)
 563. [piL_qltT_0_double] -- new in this file (internal design ledger)
 564. [piL_sin_term_abs_bound] -- new in this file (internal design ledger)
 565. [piL_cos_term_abs_bound] -- new in this file (internal design ledger)
 566. [piL_sin_partial_abs_bound] -- new in this file (internal design ledger)
 567. [piL_cos_partial_abs_bound] -- new in this file (internal design ledger)
 568. [piL_dres_majorant] -- new in this file (internal design ledger)
 569. [piL_cos_dres_majorant] -- new in this file (internal design ledger)
 570. [piL_quad_dres_majorant] -- new in this file (internal design ledger)
 571. [piL_sin_dres_majorant_bound] -- new in this file (internal design ledger)
 572. [piL_cos_dres_majorant_bound] -- new in this file (internal design ledger)
 573. [piL_quad_dres_majorant_bound] -- new in this file (internal design ledger)
 574. [piLred_qle_wd_l] -- new in this file (internal design ledger)
 575. [piLred_qle_wd_r] -- new in this file (internal design ledger)
 576. [piLred_abs_mult] -- new in this file (internal design ledger)
 577. [piLred_abs_CmS_le] -- new in this file (internal design ledger)
 578. [piLred_vtx_anchor_xL] -- new in this file (internal design ledger)
 579. [d3p_inject_nat] -- new in this file
 580. [d3p_inject_add] -- new in this file (internal design ledger)
 581. [d3p_inject_mul] -- new in this file (internal design ledger)
 582. [d3p_inject_succ] -- new in this file (internal design ledger)
 583. [d3p_inject_mono] -- new in this file (internal design ledger)
 584. [d3p_inject_ceiling_ge] -- new in this file (internal design ledger)
 585. [d3p_nat_pow2_ge_succ] -- new in this file (internal design ledger)
 586. [d3p_q_pow_0_succ] -- new in this file (internal design ledger)
 587. [d3p_q_pow_add] -- new in this file (internal design ledger)
 588. [d3p_q_fact_step] -- new in this file (internal design ledger)
 589. [d3p_q_pow_quarter_step] -- new in this file (internal design ledger)
 590. [d3p_q_pow_quarter_antitone] -- new in this file (internal design ledger)
 591. [d3p_mult_le_r_pos] -- new in this file (internal design ledger)
 592. [d3p_qdiv_mul_r] -- new in this file (internal design ledger)
 593. [d3p_qmult_neq0] -- new in this file (internal design ledger)
 594. [d3p_fact_dom_pow] -- new in this file
 595. [d3p_sin_term] -- new in this file
 596. [d3p_cos_term] -- new in this file
 597. [d3p_q_pow_pos] -- new in this file (internal design ledger)
 598. [d3p_inject_pos] -- new in this file (internal design ledger)
 599. [d3p_sin_term_pos] -- new in this file (internal design ledger)
 600. [d3p_sin_term_nonneg] -- new in this file (internal design ledger)
 601. [d3p_cos_term_nonneg] -- new in this file (internal design ledger)
 602. [d3p_cos_term_pos] -- new in this file (internal design ledger)
 603. [d3p_two_le_inject] -- new in this file (internal design ledger)
 604. [d3p_B_le_two_inject] -- new in this file (internal design ledger)
 605. [d3p_sin_term_quarter] -- new in this file
 606. [d3p_cos_term_quarter] -- new in this file (internal design ledger)
 607. [d3p_sin_term_iter] -- new in this file (internal design ledger)
 608. [d3p_cos_term_iter] -- new in this file (internal design ledger)
 609. [d3p_sin_powtail] -- new in this file
 610. [d3p_cos_powtail] -- new in this file
 611. [d3p_sin_powtail_zero] -- new in this file (internal design ledger)
 612. [d3p_cos_powtail_zero] -- new in this file (internal design ledger)
 613. [d3p_sin_powtail_quarter] -- new in this file (internal design ledger)
 614. [d3p_cos_powtail_quarter] -- new in this file (internal design ledger)
 615. [d3p_qlt_plus_1] -- new in this file (internal design ledger)
 616. [d3p_quarter_pow_lt] -- new in this file (internal design ledger)
 617. [d3p_sin_partial_step] -- new in this file
 618. [d3p_cos_partial_step] -- new in this file (internal design ledger)
 619. [d3p_sub_add_eq] -- new in this file (internal design ledger)
 620. [d3p_sin_partial_tail_abs] -- new in this file (internal design ledger)
 621. [d3p_cos_partial_tail_abs] -- new in this file (internal design ledger)
 622. [d3p_abssum_mono] -- new in this file (internal design ledger)
 623. [d3p_abssum_cos_mono] -- new in this file (internal design ledger)
 624. [d3p_sin_term_dec] -- new in this file (internal design ledger)
 625. [d3p_sin_partial_cauchy] -- new in this file (internal design ledger)
 626. [d3p_cos_partial_cauchy] -- new in this file (internal design ledger)
 627. [piLd3_lp_odd_nonneg] -- new in this file
 628. [piLd3_u_abs_le_s6] -- new in this file
 629. [piLd3_lp_a6_pos] -- new in this file
 630. [piLd3_s6_pos] -- new in this file
 631. [piLd3_qlt_add_r] -- new in this file
 632. [piLd3_c16_pos] -- new in this file (internal design ledger)
 633. [piLd3_c32_pos] -- new in this file
 634. [piLd3_seed_halfwin] -- new in this file
 635. [piLd3_seed_dres] -- new in this file
 636. [piLd3_seed_dcos] -- new in this file
 637. [piLd3_B] -- new in this file (internal design ledger)
 638. [piLd3_B_pos] -- new in this file (internal design ledger)
 639. [piLd3_abs_2u_le_B] -- new in this file
 640. [piLd3_sin_xL_eq] -- new in this file
 641. [piLd3_cos_xL_plus1_eq] -- new in this file
 642. [piLd3_abs_S_le] -- new in this file
 643. [piLd3_abs_Splus_le] -- new in this file
 644. [piLd3_halfsq_bound] -- new in this file
 645. [piLd3_dpit_bound] -- new in this file
 646. [piLd3_qle_0_mult2] -- new in this file
 647. [piLd3_mult2_le] -- new in this file
 648. [piLd3_qle_0_plus1] -- new in this file
 649. [piLd3_2SC_le] -- new in this file
 650. [piLd3_sin_bound] -- new in this file
 651. [piLd3_cos_bound] -- new in this file
 652. [piLd3_Hc1] -- new in this file (internal design ledger)
 653. [piLd3_Hc32] -- new in this file (internal design ledger)
 654. [piLd3_H82] -- new in this file (internal design ledger)
 655. [piLd3_H328] -- new in this file (internal design ledger)
 656. [piLd3_H412] -- new in this file
 657. [piLd3_budget_v1] -- new in this file
 658. [piLd3_budget_v2] -- new in this file
 659. [piLd3_sin_xL_vanish_carry] -- new in this file
 660. [piL_sin_xL_vanish] -- new in this file
 661. [piLd3_cos_xL_vanish_carry] -- new in this file
 662. [piL_cos_xL_neg1_vanish] -- new in this file (internal design ledger)
 663. [lw0_pitB_conv_m1_cases] -- new in this file
 664. [lw0_pitB_conv_cos_term_abs] -- new in this file
 665. [lw0_pitB_conv_tail_gen] -- new in this file
 666. [lw0_pitB_conv_cos_tail] -- new in this file
 667. [leibsep_cos_qp_deriv_tail_stable] -- new in this file
 668. [leibsep_ratio_slot] -- new in this file
 669. [lw0_pitB_conv_sin_term_abs] -- new in this file
 670. [lw0_pitB_conv_sin_tail] -- new in this file
 671. [leibsep_sin_qp_tail_stable] -- new in this file
 672. [lw62_qdiv_nonneg] -- new in this file
 673. [lw95_mul0] -- new in this file
 674. [lw95_qpow_nonneg] -- new in this file
 675. [lw1131_abssum_cos_nonneg] -- new in this file
 676. [lw62_qpow_abs] -- new in this file
 677. [lw62_cos_term_dom] -- new in this file
 678. [lw62_abssum_cos_dom] -- new in this file
 679. [lw62_abssum_S] -- new in this file
 680. [lw62_qdiv_den_id] -- new in this file
 681. [lw62_qdiv_le] -- new in this file
 682. [lw95_qfact_mono] -- new in this file
 683. [lw95_qfact_le] -- new in this file
 684. [lw62_abssum_cos_le] -- new in this file
 685. [lw62_zsquare_nonneg] -- new in this file
 686. [lw62_sq_nonneg] -- new in this file
 687. [lw62_qpow_even_nonneg] -- new in this file
 688. [lw62_abssum_step_mono] -- new in this file
 689. [lw62_abssum_mono] -- new in this file
 690. [lw62_q30_pos] -- new in this file
 691. [lw95_mul_le_compat] -- new in this file
 692. [lw62_georatio] -- new in this file
 693. [lw62_qpow_add] -- new in this file
 694. [lw65_qdiv_le_prod] -- new in this file
 695. [lw65_qpow_inv_pair] -- new in this file
 696. [lw65_qpow_mul] -- new in this file
 697. [lw62_item_dom] -- new in this file
 698. [lw62_rsum] -- new in this file
 699. [lw62_abssum_shift] -- new in this file
 700. [lw62_qinv30_pos] -- new in this file
 701. [lw62_rsum_nonneg] -- new in this file
 702. [lw62_rsum_tele] -- new in this file
 703. [lw62_abssum_env] -- new in this file
 704. [lw62_abssum_nonneg] -- new in this file
 705. [lw62_abssum_cos_env] -- new in this file
 706. [qltw_pc_pw] -- new in this file
 707. [qltw_pw_pc] -- new in this file
 708. [leibsep_Wb01_diff_lower] -- new in this file
 709. [lw1131_C_le_eps0K] -- new in this file
 710. [lw1190_div_mul_cancel] -- new in this file
 711. [tsl] -- new in this file
 712. [tcl] -- new in this file
 713. [sin_slot_eps0] -- new in this file
 714. [cos_slot_eps0] -- new in this file
 715. [tqF] -- new in this file
 716. [tslF] -- new in this file
 717. [tclF] -- new in this file
 718. [caps_scaled] -- new in this file
 719. [leibsep_q_kernel] -- new in this file
*)
