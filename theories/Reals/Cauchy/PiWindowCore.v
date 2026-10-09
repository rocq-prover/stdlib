(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Window core of the Leibniz alternating series

    Mission.  This file is the window core of the Leibniz alternating
    series: the parity decomposition, the series terms [t_k] and the
    partial sums [S_n], the [Q] fractional-arithmetic working layer,
    two-sided bounds on the alternating remainder, the explicit gap
    [leiblw_gap], and the window-distance main theorems
    [leiblw_dist]/[leiblw_dist_set] (delivered at the [Set] level);
    thin wrappers for the [Q] order decisions ([QltT]/[QleT'], in
    [Id]-[bool] form) with their semantic-equivalence self-check and
    the four order bridges.  Four further segments are merged in: the
    divisibility witness ([q'_n * S_n] is an integer), the residual
    law and the natural window, the escape segment delivered at the
    [Set] level, and the unboundedness of the margin; comparison
    material for the family theorems (the [nivwin] bound and
    [family_separation]); and the computational certificate builder
    of Section 9 ([pof]/[cert_core]/[cert]).

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
    [ZArith.ZArith]; order arithmetic goes through the direct
    [QArith] lemma chain, with no dependency on an external decision
    procedure.

    References.  This development, [LW0LeibWindow.v:L32-L754] (source
    coordinates of the migrated statements); this development,
    [S01_BaseRing.v:L41-L62] and [S02_CauchyComplete.v:L42-L99] (the
    decision definitions and the equivalence self-check, the same
    text as [PiCompareT.v]); this development,
    [S02_CauchyComplete.v:L51-L122] (the four order bridges); stdlib
    [QArith_base.v] at [L100], [L108], [L180], [L183] ([Qle_bool],
    the native [Z.leb] form), [L204].

    Constructivity.  Statements at the [Set] level; assumption-free
    and fully proved, with no non-constructive principles; within
    proofs, [Qlt]/[Qle] occur only on the auxiliary-premise side;
    extractable.

    Build.  [rocq c -native-compiler no -q -Q . "" PiWindowCore.v]
    compiles cleanly (exit 0); the first eight bytes of the artifact
    are [436f7121 00015ff4].

    WARNING: this file is experimental and likely to change in future
    releases. *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import ZArith.ZArith.

Local Open Scope nat_scope.

(* ================= Section 1. The Set-valued identity type ================= *)

Inductive Id {A : Set} (x : A) : A -> Set :=
| id_refl : Id x x.

Arguments id_refl {A} {x}.

Definition id_trans {A : Set} {x y z : A} (p : Id x y) (q : Id y z) : Id x z :=
  match p, q with
  | id_refl, id_refl => id_refl
  end.

(* ================= Section 2. Thin wrappers for the Q order decisions ================= *)

(* The strict-order Boolean comes with its own three-way form: the
   stdlib [QArith_base] file has no [Qlt_bool] of its own (the single
   same-named item in the stdlib tree lives in a dependency domain
   that this file must not import); the non-strict order and the
   equality use the native [QArith_base] Booleans directly. *)

Definition Qlt_bool (x y : Q) : bool :=
  match (x ?= y)%Q with Lt => true | _ => false end.
(* [(x ?= y)%Q] is the [Qcompare] notation. *)

Definition QltT (x y : Q) : Set := Id (Qlt_bool x y) true.

Definition QleT' (x y : Q) : Set := Id (Qle_bool x y) true.

(* ================= Section 3. Semantic-equivalence self-check of the decisions ================= *)

(* Same-shaped comparison copies of the library originals: the
   definition bodies are transcribed verbatim from
   [S02_CauchyComplete.v] and serve as the comparison side of the
   equivalence statements; the wrappers and the comparison copies
   coincide under the conversion check. *)

Definition qltw_S02_Qlt_bool (x y : Q) : bool :=
  match Qcompare x y with Lt => true | _ => false end.

Definition qltw_S02_Qle_bool (x y : Q) : bool :=
  match Qcompare x y with Gt => false | _ => true end.

(** Strict order: the wrapped Boolean coincides with the three-way
    [Qcompare] split at the conversion level. *)
Lemma qltw_Qlt_bool_Qcompare :
  forall x y : Q,
    Id (Qlt_bool x y) (match Qcompare x y with Lt => true | _ => false end).
Proof. intros x y. reflexivity. Defined.

(** Non-strict order: the stdlib native [Qle_bool] (the [Z.leb] form)
    coincides with the reflected form of [Qcompare] at the conversion
    level. *)
Lemma qltw_Qle_bool_Qcompare :
  forall x y : Q,
    Id (Qle_bool x y) (match Qcompare x y with Gt => false | _ => true end).
Proof. intros x y. reflexivity. Defined.

(** Equality: the stdlib native [Qeq_bool] (its [Z.eqb] body is a
    direct two-argument double match that never goes through
    [compare]; it agrees with the equal branch of [Qcompare]
    extensionally, not definitionally) -- verified branch by branch
    along the three-way [Qcompare] split: the equal branch closes
    through an equality chain via [Z.compare_eq_iff] and
    [Z.eqb_refl], the other two branches close directly.  The
    statement level remains [Set]-valued; the equality equation is
    used only inside proofs. *)
Lemma qltw_Qeq_bool_Qcompare :
  forall x y : Q,
    Id (Qeq_bool x y) (match Qcompare x y with Eq => true | _ => false end).
Proof.
  intros x y.
  destruct (Qcompare x y) eqn:E.
  - unfold Qeq_bool. rewrite (proj1 (Z.compare_eq_iff _ _) E). rewrite Z.eqb_refl.
    exact (@id_refl bool true).
  - assert (Hlt : (Qnum x * QDen y < Qnum y * QDen x)%Z)
      by exact (proj1 (Z.compare_lt_iff _ _) E).
    assert (Hne : ((Qnum x * QDen y) <> (Qnum y * QDen x))%Z)
      by (intro Hc; rewrite Hc in Hlt; exact (Z.lt_irrefl _ Hlt)).
    unfold Qeq_bool. rewrite (proj2 (Z.eqb_neq _ _) Hne).
    exact (@id_refl bool false).
  - assert (Hlt : (Qnum y * QDen x < Qnum x * QDen y)%Z)
      by exact (proj1 (Z.compare_gt_iff _ _) E).
    assert (Hne : ((Qnum x * QDen y) <> (Qnum y * QDen x))%Z)
      by (intro Hc; rewrite Hc in Hlt; exact (Z.lt_irrefl _ Hlt)).
    unfold Qeq_bool. rewrite (proj2 (Z.eqb_neq _ _) Hne).
    exact (@id_refl bool false).
Defined.

(** Wrapped Boolean <-> the library original (item by item at the
    [bool] level): strict-order side. *)
Lemma qltw_Qlt_bool_orig :
  forall x y : Q, Id (Qlt_bool x y) (qltw_S02_Qlt_bool x y).
Proof. intros x y. reflexivity. Defined.

(** Wrapped Boolean <-> the library original (item by item at the
    [bool] level): non-strict-order side. *)
Lemma qltw_Qle_bool_orig :
  forall x y : Q, Id (Qle_bool x y) (qltw_S02_Qle_bool x y).
Proof. intros x y. reflexivity. Defined.

(** Statement-level interchange (strict order): this file's [QltT]
    statement and the same-shaped [Id] statement of the original
    imply each other. *)
Lemma qltw_QltT_orig :
  forall x y : Q, QltT x y -> Id (qltw_S02_Qlt_bool x y) true.
Proof. intros x y H. exact (id_trans (@id_refl _ (qltw_S02_Qlt_bool x y)) H). Defined.

Lemma qltw_S02_QltT :
  forall x y : Q, Id (qltw_S02_Qlt_bool x y) true -> QltT x y.
Proof. intros x y H. exact (id_trans (@id_refl _ (Qlt_bool x y)) H). Defined.

(** Statement-level interchange (non-strict order): this file's
    [QleT'] statement and the same-shaped [Id] statement of the
    original imply each other. *)
Lemma qltw_QleT'_orig :
  forall x y : Q, QleT' x y -> Id (qltw_S02_Qle_bool x y) true.
Proof. intros x y H. exact (id_trans (@id_refl _ (qltw_S02_Qle_bool x y)) H). Defined.

Lemma qltw_S02_QleT' :
  forall x y : Q, Id (qltw_S02_Qle_bool x y) true -> QleT' x y.
Proof. intros x y H. exact (id_trans (@id_refl _ (Qle_bool x y)) H). Defined.

(* ================= Section 4. Concrete numeric spot-check computations ================= *)

Definition qltw_samp_QltT_0_1 : QltT 0 1 := @id_refl bool true.

Definition qltw_samp_QleT'_1_1 : QleT' 1 1 := @id_refl bool true.

Definition qltw_samp_Qeq_bool_2_2 : Id (Qeq_bool 2 2) true := @id_refl bool true.

(* ================= Section 5. The four order bridges ([Id] helpers on [bool] and the two-way bridges) ================= *)

Lemma leiblw_id_eq : forall b : bool, b = true -> Id b true.
Proof. intros b H. rewrite H. apply id_refl. Qed.

Lemma leiblw_id_inv : forall b : bool, Id b true -> b = true.
Proof. intros b H. destruct H. reflexivity. Qed.

(** Strict order, downward direction: from the [QltT] statement to
    the [Prop]-level strict order (the three-way [Qcompare]
    decision). *)
Lemma QltT_to_Qlt : forall x y : Q, QltT x y -> Qlt x y.
Proof.
  intros x y H.
  unfold QltT in H.
  unfold Qlt_bool in H.
  destruct (Qcompare x y) eqn:E; try (inversion H).
  apply Qlt_alt. exact E.
Qed.

(** Strict order, upward direction: from the [Prop]-level strict
    order to the [QltT] statement. *)
Lemma Qlt_to_QltT : forall x y : Q, Qlt x y -> QltT x y.
Proof.
  intros x y H.
  unfold QltT, Qlt_bool.
  destruct (Qcompare x y) eqn:E.
  - exfalso.
    apply (Qlt_irrefl y).
    assert (Heq : x == y) by (apply Qeq_alt; exact E).
    rewrite Heq in H.
    exact H.
  - reflexivity.
  - exfalso.
    apply (Qlt_irrefl x).
    assert (Hyx : (y < x)%Q) by (apply Qgt_alt; exact E).
    eapply Qlt_trans.
    exact H.
    exact Hyx.
Qed.

(** Non-strict order, downward direction: from the [QleT'] statement
    to the [Prop]-level non-strict order (the stdlib [Qle_bool_iff]
    bridge). *)
Lemma QleT'_to_Qle : forall x y : Q, QleT' x y -> Qle x y.
Proof.
  intros x y H.
  apply (proj1 (Qle_bool_iff x y)).
  apply leiblw_id_inv. exact H.
Qed.

(** Non-strict order, upward direction: from the [Prop]-level
    non-strict order to the [QleT'] statement. *)
Lemma Qle_to_QleT' : forall x y : Q, Qle x y -> QleT' x y.
Proof.
  intros x y H.
  apply leiblw_id_eq. apply (proj2 (Qle_bool_iff x y)). exact H.
Qed.

(* ================= Section 6. The window-core toolbox: parity, [Z] bridges, comparison on the native [Q] representation, [Qabs] ================= *)

Fixpoint leiblw_even (n : nat) : bool :=
  match n with
  | 0 => true
  | S k => negb (leiblw_even k)
  end.

Lemma leiblw_even_2m : forall m : nat, leiblw_even (2 * m) = true.
Proof.
  induction m as [|m IH]; [reflexivity|].
  replace (2 * S m) with (S (S (2 * m)))
    by (rewrite Nat.mul_succ_r, <- (plus_n_Sm (2 * m) 1); f_equal;
        rewrite <- (plus_n_Sm (2 * m) 0); f_equal; apply plus_n_O).
  cbn [leiblw_even]. rewrite IH. reflexivity.
Qed.

Lemma leiblw_even_2m1 : forall m : nat, leiblw_even (2 * m + 1) = false.
Proof.
  intros m. replace (2 * m + 1) with (S (2 * m))
    by (rewrite <- (plus_n_Sm (2 * m) 0); f_equal; apply plus_n_O).
  cbn [leiblw_even]. rewrite leiblw_even_2m. reflexivity.
Qed.

(* Constructive dichotomy: [k = 2*j] or [k = 2*j+1]. *)
Lemma leiblw_par_decomp : forall k : nat,
  sum (sigT (fun j : nat => k = 2 * j)) (sigT (fun j : nat => k = 2 * j + 1)).
Proof.
  induction k as [|k IH].
  - left. exists 0. reflexivity.
  - destruct IH as [[j Hj]|[j Hj]].
    + right. exists j. rewrite Hj.
      rewrite <- (plus_n_Sm (2 * j) 0). f_equal. apply plus_n_O.
    + left. exists (S j). rewrite Hj.
      rewrite Nat.mul_succ_r, (plus_n_Sm (2 * j) 1). reflexivity.
Qed.

(* Positivity bridge for [Z.of_nat]: premise [1 <= n] ([Z.of_nat 0 = 0] cannot work). *)
Lemma leiblw_znat_pos : forall n : nat, (1 <= n)%nat -> (0 < Z.of_nat n)%Z.
Proof.
  intros n Hn. destruct n as [|k]; [inversion Hn|].
  cbn [Z.of_nat]. apply Pos2Z.is_pos.
Qed.

(* [Z.pos (Pos.of_succ_nat k) = k+1]: the base lemma for linearizing [Q] denominators (both sides coincide after unfolding the definitions; closed by a single [reflexivity]). *)
Lemma leiblw_pos_succ : forall k : nat, Z.pos (Pos.of_succ_nat k) = Z.of_nat (S k).
Proof. reflexivity. Qed.

(* Linearization tactic: [pos_succ] -> [inj_succ]/[inj_add]/[inj_mul]/[inj_sub]/[Pos2Z.inj_mul]. *)
Ltac leiblw_zlin :=
  rewrite ?leiblw_pos_succ, ?Nat2Z.inj_succ, ?Nat2Z.inj_add,
          ?Nat2Z.inj_mul, ?Pos2Z.inj_mul, ?Nat2Z.inj_sub in *.

(* Direct +1 form of [pos_succ] (bypasses the second [inj_succ] reduction in the [zlin] chain). *)
Lemma leiblw_pos_succ1 : forall k : nat, Z.pos (Pos.of_succ_nat k) = (Z.of_nat k + 1)%Z.
Proof. intros k. rewrite leiblw_pos_succ, Nat2Z.inj_succ. reflexivity. Qed.

Lemma leiblw_qmake_eq : forall (a b : Z) (p q : positive),
  (a # p)%Q == (b # q)%Q <-> (a * Z.pos q = b * Z.pos p)%Z.
Proof.
  intros a b p q. unfold Qeq. cbn [Qnum Qden]. tauto.
Qed.

Lemma leiblw_qmake_lt : forall (a b : Z) (p q : positive),
  Qlt (a # p)%Q (b # q)%Q <-> (a * Z.pos q < b * Z.pos p)%Z.
Proof.
  intros a b p q. unfold Qlt. cbn [Qnum Qden]. split.
  - intro H. apply Z.compare_lt_iff in H. exact H.
  - intro H. apply Z.compare_lt_iff. exact H.
Qed.

Lemma leiblw_qmake_le : forall (a b : Z) (p q : positive),
  Qle (a # p)%Q (b # q)%Q <-> (a * Z.pos q <= b * Z.pos p)%Z.
Proof.
  intros a b p q. unfold Qle. cbn [Qnum Qden]. split.
  - intro H. apply Z.compare_le_iff in H. exact H.
  - intro H. apply Z.compare_le_iff. exact H.
Qed.

Lemma leiblw_qabs_id : forall q : Q, Qle 0%Q q -> Qabs q == q.
Proof. intros q H. exact (Qabs_pos q H). Qed.
(* Reuses the stdlib [QArith.Qabs] lemma [Qabs_pos]. *)

Lemma leiblw_qabs_neg : forall q : Q, Qle q 0%Q -> Qabs q == (- q)%Q.
Proof. intros q H. exact (Qabs_neg q H). Qed.
(* Reuses the stdlib [QArith.Qabs] lemma [Qabs_neg]. *)

(* ================= Section 7. The series body: [t_k := 4(-1)^k/(2k+1)] and [S_n := t_0 + ... + t_(n-1)] ================= *)

Definition leiblw_t (k : nat) : Q :=
  if leiblw_even k
  then (4 # Pos.of_succ_nat (2 * k))%Q
  else ((-4) # Pos.of_succ_nat (2 * k))%Q.

Fixpoint leiblw_S (n : nat) : Q :=
  match n with
  | 0 => 0%Q
  | S m => leiblw_S m + leiblw_t m
  end.

Lemma leiblw_S_SS : forall n : nat,
  leiblw_S (S (S n)) == leiblw_S n + leiblw_t n + leiblw_t (S n).
Proof. intros n. cbn [leiblw_S]. reflexivity. Qed.

Lemma leiblw_S_step : forall n : nat, leiblw_S (S n) == leiblw_S n + leiblw_t n.
Proof. intros n. reflexivity. Qed.

Lemma leiblw_t_pos_case : forall k : nat,
  leiblw_even k = true -> leiblw_t k == (4 # Pos.of_succ_nat (2 * k))%Q.
Proof. intros k H. unfold leiblw_t. rewrite H. reflexivity. Qed.

Lemma leiblw_t_neg_case : forall k : nat,
  leiblw_even k = false -> leiblw_t k == ((-4) # Pos.of_succ_nat (2 * k))%Q.
Proof. intros k H. unfold leiblw_t. rewrite H. reflexivity. Qed.

Lemma leiblw_t_even : forall m : nat,
  leiblw_t (2 * m) == (4 # Pos.of_succ_nat (4 * m))%Q.
Proof.
  intros m. rewrite (leiblw_t_pos_case (2 * m) (leiblw_even_2m m)).
  replace (2 * (2 * m)) with (4 * m) by (rewrite Nat.mul_assoc; reflexivity).
  reflexivity.
Qed.

Lemma leiblw_t_odd : forall m : nat,
  leiblw_t (2 * m + 1) == ((-4) # Pos.of_succ_nat (4 * m + 2))%Q.
Proof.
  intros m. rewrite (leiblw_t_neg_case (2 * m + 1) (leiblw_even_2m1 m)).
  replace (2 * (2 * m + 1)) with (4 * m + 2)
    by (rewrite Nat.mul_add_distr_l, Nat.mul_assoc, Nat.mul_1_r; reflexivity).
  reflexivity.
Qed.

Lemma leiblw_t_even_pos : forall m : nat, Qlt 0%Q (leiblw_t (2 * m))%Q.
Proof.
  intros m. rewrite leiblw_t_even. apply leiblw_qmake_lt.
  rewrite Z.mul_0_l, Z.mul_1_r.
  apply Pos2Z.is_pos.
Qed.

Lemma leiblw_t_odd_neg : forall m : nat, Qlt (leiblw_t (2 * m + 1))%Q 0%Q.
Proof.
  intros m. rewrite leiblw_t_odd. apply leiblw_qmake_lt.
  rewrite Z.mul_1_r, Z.mul_0_l.
  exact (Pos2Z.neg_is_neg 4).
Qed.

(* ================= Section 8. The [Q] fractional-arithmetic working layer: additive normal form, shunting, comparators ================= *)

(* Additive normal form: [(a#p)+(b#q) == ((a*q'+b*p')#(p*q))]. *)
Lemma leiblw_qplus_norm : forall (a b : Z) (p q : positive),
  ((a # p) + (b # q))%Q == ((a * Z.pos q + b * Z.pos p) # (Pos.mul p q))%Q.
Proof.
  intros a b p q. unfold Qeq. cbn [Qnum Qden Qplus Qmult Pos.mul].
  rewrite Pos2Z.inj_mul. ring.
Qed.

Lemma leiblw_qplus_lt0 : forall (a b : Z) (p q : positive),
  (0 < a * Z.pos q + b * Z.pos p)%Z -> Qlt 0%Q (((a # p) + (b # q))%Q).
Proof.
  intros a b p q H. rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_lt. rewrite Z.mul_0_l, Z.mul_1_r. exact H.
Qed.

Lemma leiblw_qplus_lt0b : forall (a b : Z) (p q : positive),
  (a * Z.pos q + b * Z.pos p < 0)%Z -> Qlt ((a # p) + (b # q))%Q 0%Q.
Proof.
  intros a b p q H.
  rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_lt. rewrite Z.mul_1_r, Z.mul_0_l. exact H.
Qed.

Lemma leiblw_qplus_le0 : forall (a b : Z) (p q : positive),
  (a * Z.pos q + b * Z.pos p <= 0)%Z -> Qle (((a # p) + (b # q))%Q) 0%Q.
Proof.
  intros a b p q H. rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_le. rewrite Z.mul_1_r, Z.mul_0_l. exact H.
Qed.

Lemma leiblw_qplus_eq : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  ((a * Z.pos q + b * Z.pos p) * Z.pos r = c * Z.pos (Pos.mul p q))%Z ->
  ((a # p) + (b # q))%Q == (c # r)%Q.
Proof.
  intros a b p q c r H. rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_eq. exact H.
Qed.

Lemma leiblw_qopp_distr : forall x y : Q, (-(x + y))%Q == ((- x) + (- y))%Q.
Proof.
  intros x y. unfold Qeq. cbn [Qnum Qden Qplus Qopp]. ring.
Qed.

(* Signed normal form: [-((a#p)+(b#q)) == (c#r)]. *)
Lemma leiblw_qneg_plus_eq : forall (a b : Z) (p q : positive) (c : Z) (r : positive),
  (((- a) * Z.pos q + (- b) * Z.pos p) * Z.pos r = c * Z.pos (Pos.mul p q))%Z ->
  (-((a # p) + (b # q)))%Q == (c # r)%Q.
Proof.
  intros a b p q c r H.
  rewrite leiblw_qopp_distr. unfold Qopp.
  apply leiblw_qplus_eq. exact H.
Qed.

(* Shunt: [((A+U)+V)-A == U+V]. *)
Lemma leiblw_qshunt : forall A U V : Q, (((A + U) + V) - A)%Q == (U + V)%Q.
Proof.
  intros A U V. unfold Qminus.
  rewrite <- (Qplus_assoc (A + U)%Q V (- A)%Q).
  rewrite <- (Qplus_assoc A U (V + (- A))%Q).
  rewrite (Qplus_assoc U V (- A)%Q).
  rewrite (Qplus_assoc A (U + V)%Q (- A)%Q).
  rewrite (Qplus_comm A (U + V)%Q).
  rewrite <- (Qplus_assoc (U + V)%Q A (- A)%Q).
  rewrite Qplus_opp_r. apply Qplus_0_r.
Qed.

Lemma leiblw_qplus_opp_l0 : forall A X : Q, (A + (-(A + X)))%Q == (- X)%Q.
Proof.
  intros A X. rewrite leiblw_qopp_distr, Qplus_assoc, Qplus_opp_r.
  apply Qplus_0_l.
Qed.

(* Reverse shunt: [A-((A+U)+V) == -(U+V)]. *)
Lemma leiblw_qshunt_neg : forall A U V : Q, (A - ((A + U) + V))%Q == (-(U + V))%Q.
Proof.
  intros A U V.
  rewrite <- (Qplus_assoc A U V).
  unfold Qminus. apply leiblw_qplus_opp_l0.
Qed.

Lemma leiblw_qopp_lt : forall x : Q, Qlt 0%Q x -> Qlt (- x)%Q 0%Q.
Proof.
  intros x H. unfold Qlt in *. cbn [Qnum Qden Qopp] in *.
  rewrite Z.mul_0_l, Z.mul_1_r in *.
  apply (Z.opp_lt_mono 0%Z (Qnum x)).
  exact H.
Qed.

Lemma leiblw_qminus_flip : forall x y : Q, (y - x)%Q == (-(x - y))%Q.
Proof.
  intros x y. unfold Qminus.
  rewrite leiblw_qopp_distr, Qopp_involutive.
  apply Qplus_comm.
Qed.

Lemma leiblw_qle_add_r : forall A U : Q, Qle U 0%Q -> Qle (A + U)%Q A.
Proof.
  intros A U H.
  assert (H2 : Qle ((A + U)%Q) ((A + 0)%Q))
    by (apply Qplus_le_compat; [apply Qle_refl | exact H]).
  rewrite Qplus_0_r in H2. exact H2.
Qed.

Lemma leiblw_qle_add2_r : forall A U V : Q, Qle (U + V)%Q 0%Q -> Qle ((A + U) + V)%Q A.
Proof.
  intros A U V H.
  assert (H2 : Qle ((A + (U + V))%Q) ((A + 0)%Q))
    by (apply Qplus_le_compat; [apply Qle_refl | exact H]).
  rewrite Qplus_0_r in H2. rewrite <- Qplus_assoc. exact H2.
Qed.

Lemma leiblw_qle_add_l : forall A W : Q, Qle 0%Q W -> Qle A (A + W)%Q.
Proof.
  intros A W H.
  assert (H2 : Qle ((A + 0)%Q) ((A + W)%Q))
    by (apply Qplus_le_compat; [apply Qle_refl | exact H]).
  rewrite Qplus_0_r in H2. exact H2.
Qed.

Lemma leiblw_qplus_le0b : forall (a b : Z) (p q : positive),
  (0 <= a * Z.pos q + b * Z.pos p)%Z -> Qle 0%Q ((a # p) + (b # q))%Q.
Proof.
  intros a b p q H. rewrite (leiblw_qplus_norm a b p q).
  apply leiblw_qmake_le. rewrite Z.mul_0_l, Z.mul_1_r. exact H.
Qed.

Lemma leiblw_zpos_mul : forall j k : nat,
  Z.pos (Pos.mul (Pos.of_succ_nat j) (Pos.of_succ_nat k)) =
  (Z.of_nat (S j) * Z.of_nat (S k))%Z.
Proof.
  intros j k. rewrite Pos2Z.inj_mul. rewrite !leiblw_pos_succ. reflexivity.
Qed.

(* ================= Section 9. Two-sided bounds on the alternating remainder: even steps rise, odd steps fall, interlacing ================= *)

Lemma leiblw_step_even_pos : forall m : nat,
  Qlt 0%Q (leiblw_S (2 * m + 2) - leiblw_S (2 * m))%Q.
Proof.
  intros m.
  replace (2 * m + 2) with (S (S (2 * m)))
    by (rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  cbn [leiblw_S]. rewrite leiblw_qshunt.
  rewrite leiblw_t_even. replace (2 * (2 * m)) with (4 * m) by (rewrite Nat.mul_assoc; reflexivity).
  replace (S (2 * m)) with (2 * m + 1)
    by (symmetry; rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  rewrite leiblw_t_odd.
  apply leiblw_qplus_lt0.
  rewrite (leiblw_pos_succ1 (4 * m)), (leiblw_pos_succ1 (4 * m + 2)).
  rewrite (Nat2Z.inj_add (4 * m) 2).
  replace (4 * (Z.of_nat (4 * m) + Z.of_nat 2 + 1) + -4 * (Z.of_nat (4 * m) + 1))%Z
    with 8%Z by ring.
  apply Z.ltb_lt. reflexivity.
Qed.

Lemma leiblw_step_odd_neg : forall m : nat,
  Qlt (leiblw_S (2 * m + 3) - leiblw_S (2 * m + 1))%Q 0%Q.
Proof.
  intros m.
  replace (2 * m + 3) with (S (S (2 * m + 1)))
    by (rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  cbn [leiblw_S]. rewrite leiblw_qshunt.
  rewrite leiblw_t_odd.
  replace (S (2 * m + 1)) with (2 * m + 2)
    by (symmetry; rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  replace (2 * m + 2) with (2 * (m + 1))
    by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
  rewrite leiblw_t_even.
  replace (4 * (m + 1)) with (4 * m + 4)
    by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
  apply leiblw_qplus_lt0b.
  rewrite (leiblw_pos_succ1 (4 * m + 4)), (leiblw_pos_succ1 (4 * m + 2)).
  rewrite (Nat2Z.inj_add (4 * m) 4), (Nat2Z.inj_add (4 * m) 2).
  replace (-4 * (Z.of_nat (4 * m) + Z.of_nat 4 + 1) + 4 * (Z.of_nat (4 * m) + Z.of_nat 2 + 1))%Z
    with (-8)%Z by ring.
  apply Z.ltb_lt. reflexivity.
Qed.

Lemma leiblw_interlace : forall m : nat,
  Qle (leiblw_S (2 * m + 2)) (leiblw_S (2 * m + 1))%Q.
Proof.
  intros m.
  replace (2 * m + 2) with (S (2 * m + 1))
    by (symmetry; rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  cbn [leiblw_S].
  apply leiblw_qle_add_r.
  rewrite leiblw_t_odd.
  apply leiblw_qmake_le.
  rewrite Z.mul_0_l, Z.mul_1_r.
  apply Z.leb_le. reflexivity.
Qed.

Lemma leiblw_mono_even : forall j m : nat, (m <= j)%nat ->
  Qle (leiblw_S (2 * m)) (leiblw_S (2 * j))%Q.
Proof.
  induction j as [|j IH]; intros m Hm.
  - destruct m as [|k]; [apply Qle_refl | inversion Hm].
  - destruct (Nat.eq_dec m (S j)) as [He|Hne].
    + subst. apply Qle_refl.
    + assert (Hmj : (m <= j)%nat).
      { destruct (Nat.le_gt_cases m j) as [Hle | Hgt].
        - exact Hle.
        - exfalso. apply Hne. exact (Nat.le_antisymm m (S j) Hm Hgt). }
      apply (Qle_trans _ (leiblw_S (2 * j))).
      * apply IH. exact Hmj.
      * replace (2 * S j) with (S (S (2 * j)))
          by (rewrite Nat.mul_succ_r, <- (plus_n_Sm (2 * j) 1); f_equal;
              rewrite <- (plus_n_Sm (2 * j) 0); f_equal; apply plus_n_O).
        cbn [leiblw_S].
        rewrite <- (Qplus_assoc (leiblw_S (2 * j)) (leiblw_t (2 * j)) (leiblw_t (S (2 * j)))).
        apply leiblw_qle_add_l.
        rewrite leiblw_t_even.
        replace (2 * (2 * j)) with (4 * j) by (rewrite Nat.mul_assoc; reflexivity).
        replace (S (2 * j)) with (2 * j + 1)
          by (symmetry; rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
        rewrite leiblw_t_odd.
        apply leiblw_qplus_le0b.
        rewrite (leiblw_pos_succ1 (4 * j + 2)), (leiblw_pos_succ1 (4 * j)).
        rewrite (Nat2Z.inj_add (4 * j) 2).
        replace (4 * (Z.of_nat (4 * j) + Z.of_nat 2 + 1) + -4 * (Z.of_nat (4 * j) + 1))%Z
          with 8%Z by ring.
        apply Z.leb_le. reflexivity.
Qed.

Lemma leiblw_mono_odd : forall j m : nat, (m <= j)%nat ->
  Qle (leiblw_S (2 * j + 1)) (leiblw_S (2 * m + 1))%Q.
Proof.
  induction j as [|j IH]; intros m Hm.
  - destruct m as [|k]; [apply Qle_refl | inversion Hm].
  - destruct (Nat.eq_dec m (S j)) as [He|Hne].
    + subst. apply Qle_refl.
    + assert (Hmj : (m <= j)%nat).
      { destruct (Nat.le_gt_cases m j) as [Hle | Hgt].
        - exact Hle.
        - exfalso. apply Hne. exact (Nat.le_antisymm m (S j) Hm Hgt). }
      apply (Qle_trans _ (leiblw_S (2 * j + 1))).
      * replace (2 * S j + 1) with (S (S (2 * j + 1)))
          by (rewrite Nat.mul_succ_r, <- (plus_n_Sm (2 * j) 1),
              (Nat.add_1_r (S (2 * j + 1))); reflexivity).
        cbn [leiblw_S].
        apply leiblw_qle_add2_r.
        replace (S (2 * j + 1)) with (2 * j + 2)
          by (symmetry; rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
        replace (2 * j + 2) with (2 * (j + 1))
          by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
        rewrite leiblw_t_odd.
        rewrite leiblw_t_even.
        replace (4 * (j + 1)) with (4 * j + 4)
          by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
        apply leiblw_qplus_le0.
        rewrite (leiblw_pos_succ1 (4 * j + 4)), (leiblw_pos_succ1 (4 * j + 2)).
        rewrite (Nat2Z.inj_add (4 * j) 4), (Nat2Z.inj_add (4 * j) 2).
        replace (-4 * (Z.of_nat (4 * j) + Z.of_nat 4 + 1) + 4 * (Z.of_nat (4 * j) + Z.of_nat 2 + 1))%Z
          with (-8)%Z by ring.
        apply Z.leb_le. reflexivity.
      * apply IH. exact Hmj.
Qed.

(* ================= Section 10. The explicit gap: [gap n := 8/((2n+1)(2n+3))], the step between adjacent same-side partial sums ================= *)

Definition leiblw_gap (n : nat) : Q :=
  (8 # (Pos.mul (Pos.of_succ_nat (2 * n)) (Pos.of_succ_nat (2 * n + 2))))%Q.

Lemma leiblw_gap_pos : forall n : nat, Qlt 0%Q (leiblw_gap n).
Proof. intros n. unfold leiblw_gap. apply leiblw_qmake_lt. apply Pos2Z.is_pos. Qed.

Lemma leiblw_gap_even_step : forall m : nat,
  (leiblw_S (2 * m + 2) - leiblw_S (2 * m))%Q == leiblw_gap (2 * m).
Proof.
  intros m. unfold leiblw_gap.
  replace (2 * m + 2) with (S (S (2 * m)))
    by (rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  cbn [leiblw_S]. rewrite leiblw_qshunt.
  rewrite leiblw_t_even. replace (2 * (2 * m)) with (4 * m) by (rewrite Nat.mul_assoc; reflexivity).
  replace (S (2 * m)) with (2 * m + 1)
    by (symmetry; rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  rewrite leiblw_t_odd.
  apply leiblw_qplus_eq.
  rewrite (leiblw_pos_succ1 (4 * m)), (leiblw_pos_succ1 (4 * m + 2)).
  rewrite (Nat2Z.inj_add (4 * m) 2).
  assert (Hw : (Z.pos (Pos.mul (Pos.of_succ_nat (4 * m)) (Pos.of_succ_nat (4 * m + 2))) =
                Z.of_nat (4 * m + 1) * Z.of_nat (4 * m + 3))%Z)
    by (rewrite leiblw_zpos_mul; f_equal;
        rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  rewrite Hw.
  rewrite (Nat2Z.inj_add (4 * m) 1), (Nat2Z.inj_add (4 * m) 3).
  ring.
Qed.

Lemma leiblw_gap_odd_step : forall m : nat,
  (leiblw_S (2 * m + 1) - leiblw_S (2 * m + 3))%Q == leiblw_gap (2 * m + 1).
Proof.
  intros m. unfold leiblw_gap.
  replace (2 * m + 3) with (S (S (2 * m + 1)))
    by (rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  cbn [leiblw_S]. rewrite leiblw_qshunt_neg.
  rewrite leiblw_t_odd.
  replace (S (2 * m + 1)) with (2 * m + 2)
    by (symmetry; rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  replace (2 * m + 2) with (2 * (m + 1))
    by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
  rewrite leiblw_t_even.
  replace (4 * (m + 1)) with (4 * m + 4)
    by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
  replace (2 * (2 * m + 1)) with (4 * m + 2)
    by (rewrite Nat.mul_add_distr_l, Nat.mul_assoc, Nat.mul_1_r; reflexivity).
  replace (2 * (2 * m + 1) + 2) with (4 * m + 4)
    by (rewrite Nat.mul_add_distr_l, Nat.mul_assoc, Nat.mul_1_r, <- Nat.add_assoc;
        reflexivity).
  apply leiblw_qneg_plus_eq.
  rewrite (leiblw_pos_succ1 (4 * m + 4)), (leiblw_pos_succ1 (4 * m + 2)).
  replace (4 * m + 2 + 2) with (4 * m + 4)
    by (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; reflexivity).
  assert (Hw : (Z.pos (Pos.mul (Pos.of_succ_nat (4 * m + 2)) (Pos.of_succ_nat (4 * m + 4))) =
                Z.of_nat (4 * m + 3) * Z.of_nat (4 * m + 5))%Z)
    by (rewrite leiblw_zpos_mul; f_equal;
        rewrite ?Nat.add_succ_r, Nat.add_0_r; reflexivity).
  rewrite Hw.
  rewrite (Nat2Z.inj_add (4 * m) 2), (Nat2Z.inj_add (4 * m) 4),
          (Nat2Z.inj_add (4 * m) 3), (Nat2Z.inj_add (4 * m) 5).
  ring.
Qed.

(* ================= Section 11. The window-distance main theorems: distance >= [gap n] (one per branch) and the [Set]-level packaging ================= *)

(* Even side, even step: [j >= m+1] implies [S_2j - S_2m >= gap(2m)]. *)
Lemma leiblw_lower_even_e : forall j m : nat, (m + 1 <= j)%nat ->
  Qle (leiblw_gap (2 * m)) (leiblw_S (2 * j) - leiblw_S (2 * m))%Q.
Proof.
  intros j m Hj. rewrite <- (leiblw_gap_even_step m).
  replace (2 * m + 2) with (2 * (m + 1))
    by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
  assert (Hme : Qle (leiblw_S (2 * (m + 1))) (leiblw_S (2 * j)))
    by (apply leiblw_mono_even; exact Hj).
  unfold Qminus. apply Qplus_le_compat; [exact Hme | apply Qle_refl].
Qed.

(* Even side, odd step: [j >= m] implies [S_2j+1 - S_2m >= gap(2m)]. *)
Lemma leiblw_lower_even_o : forall j m : nat, (m <= j)%nat ->
  Qle (leiblw_gap (2 * m)) (leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q.
Proof.
  intros j m Hj. rewrite <- (leiblw_gap_even_step m).
  assert (Hme : Qle (leiblw_S (2 * m + 2)) (leiblw_S (2 * j + 2))).
  { replace (2 * m + 2) with (2 * (m + 1))
      by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
    replace (2 * j + 2) with (2 * (j + 1))
      by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
    apply leiblw_mono_even.
    rewrite (Nat.add_1_r m), (Nat.add_1_r j).
    exact (proj1 (Nat.succ_le_mono m j) Hj). }
  assert (Hi : Qle (leiblw_S (2 * j + 2)) (leiblw_S (2 * j + 1)))
    by apply leiblw_interlace.
  unfold Qminus.
  apply (Qle_trans _ ((leiblw_S (2 * j + 2) + (- leiblw_S (2 * m)))%Q)).
  - apply Qplus_le_compat; [exact Hme | apply Qle_refl].
  - apply Qplus_le_compat; [exact Hi | apply Qle_refl].
Qed.

(* Odd side, even step: [j >= m+1] implies [S_2m+1 - S_2j >= gap(2m+1)]. *)
Lemma leiblw_lower_odd_e : forall j m : nat, (m + 1 <= j)%nat ->
  Qle (leiblw_gap (2 * m + 1)) ((leiblw_S (2 * m + 1) - leiblw_S (2 * j))%Q).
Proof.
  intros j m Hj.
  pose proof (leiblw_gap_odd_step m) as Hstep.
  pose proof (leiblw_mono_odd j (m + 1) Hj) as Hmo.
  replace (2 * (m + 1) + 1) with (2 * m + 3) in Hmo
    by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r, <- Nat.add_assoc; reflexivity).
  pose proof (leiblw_t_even_pos j) as Hp.
  assert (HB : Qle (leiblw_S (2 * j)) (leiblw_S (2 * (m + 1) + 1))).
  { apply (Qle_trans _ (leiblw_S (2 * j + 1))).
    - replace (2 * j + 1) with (S (2 * j)) by (rewrite Nat.add_1_r; reflexivity).
      rewrite (leiblw_S_step (2 * j)).
      apply leiblw_qle_add_l. exact (Qlt_le_weak _ _ Hp).
    - replace (2 * (m + 1) + 1) with (2 * m + 3)
        by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r, <- Nat.add_assoc; reflexivity).
      exact Hmo. }
  rewrite <- Hstep.
  unfold Qminus.
  apply Qplus_le_compat; [apply Qle_refl |].
  apply (Qopp_le_compat (leiblw_S (2 * j)) (leiblw_S (2 * m + 3))).
  replace (2 * m + 3) with (2 * (m + 1) + 1)
    by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r, <- Nat.add_assoc; reflexivity).
  exact HB.
Qed.

(* Odd side, odd step: [j >= m+1] implies [S_2m+1 - S_2j+1 >= gap(2m+1)]. *)
Lemma leiblw_lower_odd_o : forall j m : nat, (m + 1 <= j)%nat ->
  Qle (leiblw_gap (2 * m + 1)) (leiblw_S (2 * m + 1) - leiblw_S (2 * j + 1))%Q.
Proof.
  intros j m Hj. rewrite <- (leiblw_gap_odd_step m).
  replace (2 * m + 3) with (2 * (m + 1) + 1)
    by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r, <- Nat.add_assoc; reflexivity).
  assert (Hle : Qle (leiblw_S (2 * j + 1)) (leiblw_S (2 * (m + 1) + 1)))
    by (apply leiblw_mono_odd; exact Hj).
  unfold Qminus.
  apply Qplus_le_compat; [apply Qle_refl |].
  apply Qopp_le_compat. exact Hle.
Qed.

(* The main distance theorem ([Q] level, both branches united): [k >= n+1] implies [gap n <= |S_k - S_n|]. *)
Theorem leiblw_dist : forall n k : nat, (S n <= k)%nat ->
  Qle (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n))%Q.
Proof.
  intros n k Hk.
  destruct (leiblw_par_decomp n) as [[m Hm]|Hm].
  - destruct (leiblw_par_decomp k) as [[j Hj]|Hj].
    + rewrite Hm, Hj in Hk.
      assert (Hc : (m + 1 <= j)%nat).
      { destruct (Nat.le_gt_cases j m) as [Hle | Hgt].
        - exfalso.
          assert (H1 : (2 * j <= 2 * m)%nat) by (apply Nat.mul_le_mono_l; exact Hle).
          exact (Nat.lt_irrefl (2 * m) (Nat.lt_le_trans (2 * m) (2 * j) (2 * m) Hk H1)).
        - rewrite Nat.add_1_r. exact Hgt. }
      pose proof (leiblw_lower_even_e j m Hc) as L.
      assert (Hy : Qle 0%Q ((leiblw_S (2 * j) - leiblw_S (2 * m))%Q)).
      { apply (Qle_trans _ (leiblw_gap (2 * m))).
        - exact (Qlt_le_weak _ _ (leiblw_gap_pos (2 * m))).
        - exact L. }
      pose proof (leiblw_qabs_id _ Hy) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m))
                       (Qabs ((leiblw_S (2 * j) - leiblw_S (2 * m))%Q)))
        by (rewrite E1; exact L).
      exact (eq_ind (2 * m)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j)
                 (fun v => Qle (leiblw_gap (2 * m))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
    + destruct Hj as [j Hj].
      rewrite Hm, Hj in Hk.
      assert (Hc : (m <= j)%nat).
      { assert (H0 : (2 * m <= 2 * j)%nat).
        { rewrite Nat.add_1_r in Hk. exact (proj2 (Nat.succ_le_mono (2 * m) (2 * j)) Hk). }
        destruct (Nat.le_gt_cases m j) as [Hle | Hgt].
        - exact Hle.
        - exfalso.
          assert (H1 : (2 * j < 2 * m)%nat)
            by exact (proj1 (Nat.mul_lt_mono_pos_l 2 j m (Nat.lt_0_succ 1)) Hgt).
          exact (Nat.lt_irrefl (2 * j) (Nat.lt_le_trans (2 * j) (2 * m) (2 * j) H1 H0)). }
      pose proof (leiblw_lower_even_o j m Hc) as L.
      assert (Hy : Qle 0%Q ((leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q)).
      { apply (Qle_trans _ (leiblw_gap (2 * m))).
        - exact (Qlt_le_weak _ _ (leiblw_gap_pos (2 * m))).
        - exact L. }
      pose proof (leiblw_qabs_id _ Hy) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m))
                       (Qabs ((leiblw_S (2 * j + 1) - leiblw_S (2 * m))%Q)))
        by (rewrite E1; exact L).
      exact (eq_ind (2 * m)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j + 1)
                 (fun v => Qle (leiblw_gap (2 * m))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
  - destruct Hm as [m Hm].
    destruct (leiblw_par_decomp k) as [[j Hj]|Hj].
    + rewrite Hm, Hj in Hk.
      assert (Hc : (m + 1 <= j)%nat).
      { assert (H0 : (2 * (m + 1) <= 2 * j)%nat).
        { rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
          replace (2 * m + 2) with (S (2 * m + 1))
            by (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; reflexivity).
          exact Hk. }
        destruct (Nat.le_gt_cases (m + 1) j) as [Hle | Hgt].
        - exact Hle.
        - exfalso.
          assert (H2 : (2 * j < 2 * (m + 1))%nat)
            by exact (proj1 (Nat.mul_lt_mono_pos_l 2 j (m + 1) (Nat.lt_0_succ 1)) Hgt).
          exact (Nat.lt_irrefl (2 * (m + 1))
                  (Nat.le_lt_trans (2 * (m + 1)) (2 * j) (2 * (m + 1)) H0 H2)). }
      pose proof (leiblw_lower_odd_e j m Hc) as L0.
      assert (Hy2 : Qle ((leiblw_S (2 * j) - leiblw_S (2 * m + 1))%Q) 0%Q).
      { pose proof (Qlt_le_weak _ _ (leiblw_gap_pos (2 * m + 1))) as Hgp.
        pose proof (Qle_trans 0%Q (leiblw_gap (2 * m + 1))
                      (leiblw_S (2 * m + 1) - leiblw_S (2 * j))%Q Hgp L0) as Hp2.
        rewrite (leiblw_qminus_flip (leiblw_S (2 * m + 1)) (leiblw_S (2 * j))).
        exact (Qopp_le_compat 0%Q ((leiblw_S (2 * m + 1) - leiblw_S (2 * j))%Q) Hp2). }
      pose proof (leiblw_qabs_neg _ Hy2) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m + 1))
                       (Qabs ((leiblw_S (2 * j) - leiblw_S (2 * m + 1))%Q))).
      { rewrite E1.
        rewrite <- (leiblw_qminus_flip (leiblw_S (2 * j)) (leiblw_S (2 * m + 1))).
        exact L0. }
      exact (eq_ind (2 * m + 1)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j)
                 (fun v => Qle (leiblw_gap (2 * m + 1))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m + 1))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
    + destruct Hj as [j Hj].
      rewrite Hm, Hj in Hk.
      assert (Hc : (m + 1 <= j)%nat).
      { destruct (Nat.le_gt_cases j m) as [Hle | Hgt].
        - exfalso.
          assert (H1 : (2 * j <= 2 * m)%nat) by (apply Nat.mul_le_mono_l; exact Hle).
          assert (H2 : (2 * m + 1 <= 2 * j)%nat).
          { rewrite (Nat.add_1_r (2 * j)) in Hk.
            exact (proj2 (Nat.succ_le_mono (2 * m + 1) (2 * j)) Hk). }
          apply (Nat.nle_succ_diag_l (2 * m)).
          rewrite <- Nat.add_1_r.
          exact (Nat.le_trans (2 * m + 1) (2 * j) (2 * m) H2 H1).
        - rewrite Nat.add_1_r. exact Hgt. }
      pose proof (leiblw_lower_odd_o j m Hc) as L0.
      assert (Hy : Qle ((leiblw_S (2 * j + 1) - leiblw_S (2 * m + 1))%Q) 0%Q).
      { pose proof (Qlt_le_weak _ _ (leiblw_gap_pos (2 * m + 1))) as Hgp.
        pose proof (Qle_trans 0%Q (leiblw_gap (2 * m + 1))
                      ((leiblw_S (2 * m + 1) - leiblw_S (2 * j + 1))%Q) Hgp L0) as Hp2.
        rewrite (leiblw_qminus_flip (leiblw_S (2 * m + 1)) (leiblw_S (2 * j + 1))).
        exact (Qopp_le_compat 0%Q ((leiblw_S (2 * m + 1) - leiblw_S (2 * j + 1))%Q) Hp2). }
      pose proof (leiblw_qabs_neg _ Hy) as E1.
      assert (L2 : Qle (leiblw_gap (2 * m + 1))
                       (Qabs ((leiblw_S (2 * j + 1) - leiblw_S (2 * m + 1))%Q))).
      { rewrite E1.
        rewrite <- (leiblw_qminus_flip (leiblw_S (2 * j + 1)) (leiblw_S (2 * m + 1))).
        exact L0. }
      exact (eq_ind (2 * m + 1)
              (fun v => Qle (leiblw_gap v) (Qabs ((leiblw_S k - leiblw_S v)%Q)))
              (eq_ind (2 * j + 1)
                 (fun v => Qle (leiblw_gap (2 * m + 1))
                             (Qabs ((leiblw_S v - leiblw_S (2 * m + 1))%Q)))
                 L2 k (eq_sym Hj))
              n (eq_sym Hm)).
Qed.

(* Set-level packaging of the window distance: the gap lower bound is
   delivered as the non-strict-order decision (the strict-order form
   fails, equality being attained at [k = n + 2]). *)
Theorem leiblw_dist_set : forall n : nat,
  sigT (fun N : nat => forall k : nat, (N <= k)%nat ->
    QleT' (leiblw_gap n) (Qabs (leiblw_S k - leiblw_S n))).
Proof.
  intros n. exists (S n). intros k Hk.
  apply Qle_to_QleT'. apply leiblw_dist. exact Hk.
Qed.

(* ============================================================ *)
(* Section 12. Common-denominator divisibility: [q'_n := (2n+1)!] and [q'_n * S_n] in [Z] (the witness [P_n]) *)
(* ============================================================ *)

(* The factorial cofactor: [zf 0 = 1], [zf (S k) = (k+1)*zf k]. *)
Fixpoint leiblw_zf (n : nat) : Z :=
  match n with
  | 0 => 1%Z
  | S k => Z.pos (Pos.of_succ_nat k) * leiblw_zf k
  end.

Definition leiblw_qf (n : nat) : Q := (leiblw_zf n # 1)%Q.

(* Structural unfolding of the [S] step of [zf] (helper: one-step conversion of the fixpoint body). *)
Lemma leiblw_zf_S : forall m : nat,
  leiblw_zf (S m) = (Z.pos (Pos.of_succ_nat m) * leiblw_zf m)%Z.
Proof. intros m. cbn [leiblw_zf]. reflexivity. Qed.

Lemma leiblw_zf_ge1 : forall n : nat, (1 <= leiblw_zf n)%Z.
Proof.
  induction n as [|n IH].
  - cbn [leiblw_zf]. apply Z.le_refl.
  - cbn [leiblw_zf].
    apply (Z.le_trans _ (Z.pos (Pos.of_succ_nat n) * 1)%Z).
    + rewrite Z.mul_1_r.
      rewrite leiblw_pos_succ, Nat2Z.inj_succ.
      exact (proj1 (Z.succ_le_mono 0 (Z.of_nat n)) (Nat2Z.is_nonneg n)).
    + apply Z.mul_le_mono_nonneg_l.
      * apply Z.leb_le. reflexivity.
      * exact IH.
Qed.

Lemma leiblw_zf_ge_id : forall n : nat, (1 <= n)%nat -> (Z.of_nat n <= leiblw_zf n)%Z.
Proof.
  intros n Hn.
  assert (Hp : n = S (n - 1)).
  { rewrite Nat.sub_1_r. symmetry. apply Nat.succ_pred_pos. exact Hn. }
  rewrite Hp.
  cbn [leiblw_zf].
  rewrite leiblw_pos_succ, Nat2Z.inj_succ.
  assert (Hm : (Z.succ (Z.of_nat (n - 1)) * 1
                <= Z.succ (Z.of_nat (n - 1)) * leiblw_zf (n - 1))%Z).
  { apply Z.mul_le_mono_nonneg_l.
    - apply (Z.le_trans _ (Z.of_nat (n - 1))).
      + apply Nat2Z.is_nonneg.
      + apply Z.le_succ_diag_r.
    - exact (leiblw_zf_ge1 (n - 1)). }
  rewrite Z.mul_1_r in Hm.
  exact Hm.
Qed.

(* [zf(2n) >= (2n-1)*(2n)] for [n >= 1] -- the fuel for the divergence of the margin. *)
Lemma leiblw_zf_lower : forall n : nat, (1 <= n)%nat ->
  (Z.of_nat (2 * n - 1) * Z.of_nat (2 * n) <= leiblw_zf (2 * n))%Z.
Proof.
  intros n Hn.
  assert (H2pos : (0 < 2 * n)%nat)
    by exact (proj1 (Nat.mul_lt_mono_pos_l 2 0 n (Nat.lt_0_succ 1)) Hn).
  assert (Hsub : (2 * n - 1)%nat = Nat.pred (2 * n)) by apply Nat.sub_1_r.
  assert (Hp : (2 * n)%nat = S (2 * n - 1)).
  { rewrite Hsub. symmetry. apply Nat.succ_pred_pos. exact H2pos. }
  assert (H21 : (1 <= 2 * n - 1)%nat).
  { apply (proj2 (Nat.succ_le_mono 1 (2 * n - 1))).
    replace (S (2 * n - 1)) with (2 * n) by (rewrite <- Hp; reflexivity).
    replace 2 with (2 * 1)%nat by reflexivity.
    apply Nat.mul_le_mono_l. exact Hn. }
  assert (Hge : (Z.of_nat (2 * n - 1) <= leiblw_zf (2 * n - 1))%Z)
    by exact (leiblw_zf_ge_id (2 * n - 1) H21).
  replace (leiblw_zf (2 * n)) with (leiblw_zf (S (2 * n - 1)))
    by (rewrite <- Hp; reflexivity).
  rewrite (leiblw_zf_S (2 * n - 1)), leiblw_pos_succ.
  rewrite <- Hp.
  rewrite (Z.mul_comm (Z.of_nat (2 * n - 1)) (Z.of_nat (2 * n))).
  apply Z.mul_le_mono_nonneg_l.
  - apply Nat2Z.is_nonneg.
  - exact Hge.
Qed.

(* One-step native unfolding of [zf] ([2n+k] is not a constructor head; needs [replace] and [cbn]). *)
Lemma leiblw_zf_2n1 : forall n : nat,
  leiblw_zf (2 * n + 1) = (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))%Z.
Proof.
  intros n.
  replace (2 * n + 1) with (S (2 * n)) by (rewrite Nat.add_1_r; reflexivity).
  cbn [leiblw_zf]. reflexivity.
Qed.

(* Native three-factor unfolding of [(2n+1)!]: [zf(2n+3) = (2n+3)*(2n+2)*((2n+1)*zf(2n))]. *)
Lemma leiblw_zf_2n3 : forall n : nat,
  leiblw_zf (2 * n + 3) =
  (Z.pos (Pos.of_succ_nat (S (S (2 * n)))) *
   (Z.pos (Pos.of_succ_nat (S (2 * n))) *
    (Z.pos (Pos.of_succ_nat (2 * n)) * leiblw_zf (2 * n))))%Z.
Proof.
  intros n.
  replace (2 * n + 3) with (S (S (S (2 * n))))
    by (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; reflexivity).
  cbn [leiblw_zf]. reflexivity.
Qed.

Theorem leiblw_integrality : forall n : nat,
  sigT (fun p : Z => (leiblw_qf (2 * n + 1) * leiblw_S n)%Q == (p # 1)%Q).
Proof.
  induction n as [|n IH].
  - exists 0%Z. unfold leiblw_qf. cbn [leiblw_zf leiblw_S].
    unfold Qeq. cbn [Qnum Qden Qmult Pos.mul]. ring.
  - destruct IH as [p Hp].
    replace (2 * S n + 1) with (2 * n + 3)
      by (rewrite Nat.mul_succ_r, <- Nat.add_assoc; reflexivity).
    unfold leiblw_qf in Hp. rewrite leiblw_zf_2n1 in Hp.
    destruct (leiblw_even n) eqn:Hev.
    + exists (Z.pos (Pos.of_succ_nat (S (S (2 * n)))) *
              (Z.pos (Pos.of_succ_nat (S (2 * n))) *
               (p + 4 * leiblw_zf (2 * n)))%Z)%Z.
      cbn [leiblw_S]. rewrite leiblw_t_pos_case by exact Hev.
      unfold leiblw_qf at 1. rewrite leiblw_zf_2n3.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (S (S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) Hp) as Hp2.
      rewrite Z.mul_1_r in Hp2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) + (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite Hp2. ring.
    + exists (Z.pos (Pos.of_succ_nat (S (S (2 * n)))) *
              (Z.pos (Pos.of_succ_nat (S (2 * n))) *
               (p - 4 * leiblw_zf (2 * n)))%Z)%Z.
      cbn [leiblw_S]. rewrite leiblw_t_neg_case by exact Hev.
      unfold leiblw_qf at 1. rewrite leiblw_zf_2n3.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (S (S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) Hp) as Hp2.
      rewrite Z.mul_1_r in Hp2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) - (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite Hp2. ring.
Qed.

(* ============================================================ *)
(* Section 13. The residual law and the natural certification window ([W b n = b*q'_n*|t_n| = 4b*(2n)!]) *)
(* ============================================================ *)

(* [margin_n := q'_n*gap_n = 8*(2n)!/(2n+3)] (the natural witness-level residual lower bound for divisibility and the window distance). *)
Definition leiblw_margin (n : nat) : Q := (leiblw_qf (2 * n + 1) * leiblw_gap n)%Q.

(* The natural certification window: [W b n := 4b*(2n)!] (=[b*q'_n*|t_n|]; residual law below). *)
Definition leiblw_natwin (b n : nat) : Q :=
  (4 * Z.of_nat b * leiblw_zf (2 * n) # 1)%Q.

Lemma leiblw_qabs_make : forall q : Q,
  Qabs q == ((Z.abs (Qnum q)) # (Qden q))%Q.
Proof. intros [z p]. reflexivity. Qed.

(* The residual law (promoted to a lemma): [W b n == b*q'_n*|t_n|]. *)
Lemma leiblw_natwin_residual : forall b n : nat,
  (leiblw_natwin b n)%Q
  == ((Z.of_nat b # 1) * (leiblw_qf (2 * n + 1) * Qabs (leiblw_t n)))%Q.
Proof.
  intros b n. unfold leiblw_natwin, leiblw_qf.
  destruct (leiblw_even n) eqn:Hev.
  - rewrite leiblw_t_pos_case by exact Hev.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp Pos.mul Qabs Z.abs].
    rewrite leiblw_zf_2n1. ring.
  - rewrite leiblw_t_neg_case by exact Hev.
    unfold Qeq. cbn [Qnum Qden Qmult Qopp Pos.mul Qabs Z.abs].
    rewrite leiblw_zf_2n1. ring.
Qed.

Lemma leiblw_natwin_ge : forall b n : nat,
  (1 <= b)%nat -> Qle (4 # 1)%Q (leiblw_natwin b n).
Proof.
  intros b n Hb. unfold leiblw_natwin. apply leiblw_qmake_le.
  rewrite Z.mul_1_r, Z.mul_1_r.
  assert (Hb1 : (1 <= Z.of_nat b)%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity.
    exact (proj1 (Nat2Z.inj_le 1 b) Hb). }
  apply (Z.le_trans _ (4 * Z.of_nat b)%Z).
  - replace 4%Z with (4 * 1)%Z by reflexivity.
    apply Z.mul_le_mono_nonneg_l.
    + apply Z.leb_le. reflexivity.
    + exact Hb1.
  - apply (Z.le_trans _ ((4 * Z.of_nat b) * 1)%Z).
    + rewrite Z.mul_1_r. apply Z.le_refl.
    + apply Z.mul_le_mono_nonneg_l.
      * exact (Z.mul_nonneg_nonneg 4 (Z.of_nat b) (Zle_0_pos 4) (Nat2Z.is_nonneg b)).
      * exact (leiblw_zf_ge1 (2 * n)).
Qed.

(* [z <= 1*z] (helper: by case analysis on the constructors of [z], [1*z] reduces computationally). *)
Lemma leiblw_zle_mul1 : forall z : Z, (0 <= z)%Z -> (z <= 1 * z)%Z.
Proof.
  intros z Hz. destruct z.
  - apply Z.le_refl.
  - apply Z.le_refl.
  - apply Z.le_refl.
Qed.

Lemma leiblw_natwin_mono : forall b n : nat,
  Qle (leiblw_natwin b n) (leiblw_natwin b (S n)).
Proof.
  intros b n. unfold leiblw_natwin. apply leiblw_qmake_le.
  rewrite Z.mul_1_r, Z.mul_1_r.
  replace (2 * S n) with (S (S (2 * n)))
    by (rewrite Nat.mul_succ_r, ?Nat.add_succ_r, ?Nat.add_0_r; reflexivity).
  cbn [leiblw_zf].
  rewrite (leiblw_pos_succ (S (2 * n))), (leiblw_pos_succ (2 * n)).
  assert (Hx1 : (1 <= Z.of_nat (S (2 * n)))%Z).
  { replace (Z.of_nat (S (2 * n))) with (Z.succ (Z.of_nat (2 * n)))
      by (rewrite Nat2Z.inj_succ; reflexivity).
    exact (proj1 (Z.succ_le_mono 0 (Z.of_nat (2 * n))) (Nat2Z.is_nonneg (2 * n))). }
  assert (Hx2 : (1 <= Z.of_nat (S (S (2 * n))))%Z).
  { replace (Z.of_nat (S (S (2 * n)))) with (Z.succ (Z.succ (Z.of_nat (2 * n))))
      by (rewrite Nat2Z.inj_succ, Nat2Z.inj_succ; reflexivity).
    apply (Z.le_trans _ (Z.succ (Z.of_nat (2 * n)))).
    - exact (proj1 (Z.succ_le_mono 0 (Z.of_nat (2 * n))) (Nat2Z.is_nonneg (2 * n))).
    - apply Z.le_succ_diag_r. }
  assert (Hzf : (1 <= leiblw_zf (2 * n))%Z) by exact (leiblw_zf_ge1 (2 * n)).
  assert (Hzf0 : (0 <= leiblw_zf (2 * n))%Z).
  { apply (Z.le_trans _ 1%Z).
    - apply Z.leb_le. reflexivity.
    - exact Hzf. }
  assert (Hprod1 : (1 <= Z.of_nat (S (2 * n)) * leiblw_zf (2 * n))%Z).
  { apply (Z.le_trans _ (Z.of_nat (S (2 * n)) * 1)%Z).
    - rewrite Z.mul_1_r. exact Hx1.
    - apply Z.mul_le_mono_nonneg_l.
      * apply Nat2Z.is_nonneg.
      * exact Hzf. }
  assert (Hprod2 : (1 <= Z.of_nat (S (S (2 * n)))
                              * (Z.of_nat (S (2 * n)) * leiblw_zf (2 * n)))%Z).
  { apply (Z.le_trans _ (Z.of_nat (S (S (2 * n))) * 1)%Z).
    - rewrite Z.mul_1_r. exact Hx2.
    - apply Z.mul_le_mono_nonneg_l.
      * apply Nat2Z.is_nonneg.
      * exact Hprod1. }
  assert (Hwle : (leiblw_zf (2 * n) <= Z.of_nat (S (S (2 * n)))
                                            * (Z.of_nat (S (2 * n)) * leiblw_zf (2 * n)))%Z).
  { apply (Z.le_trans _ (1 * leiblw_zf (2 * n))).
    - exact (leiblw_zle_mul1 (leiblw_zf (2 * n)) Hzf0).
    - apply (Z.le_trans _ (Z.of_nat (S (2 * n)) * leiblw_zf (2 * n))).
      + exact (Z.mul_le_mono_nonneg_r 1 (Z.of_nat (S (2 * n)))
                 (leiblw_zf (2 * n)) Hzf0 Hx1).
      + apply (Z.le_trans _ (1 * (Z.of_nat (S (2 * n)) * leiblw_zf (2 * n)))).
        * exact (leiblw_zle_mul1 (Z.of_nat (S (2 * n)) * leiblw_zf (2 * n))
                   (Z.mul_nonneg_nonneg (Z.of_nat (S (2 * n))) (leiblw_zf (2 * n))
                      (Nat2Z.is_nonneg (S (2 * n))) Hzf0)).
        * exact (Z.mul_le_mono_nonneg_r 1 (Z.of_nat (S (S (2 * n))))
                   (Z.of_nat (S (2 * n)) * leiblw_zf (2 * n))
                   (Z.mul_nonneg_nonneg (Z.of_nat (S (2 * n))) (leiblw_zf (2 * n))
                      (Nat2Z.is_nonneg (S (2 * n))) Hzf0)
                   Hx2). }
  apply Z.mul_le_mono_nonneg_l.
  - exact (Z.mul_nonneg_nonneg 4 (Z.of_nat b) (Zle_0_pos 4) (Nat2Z.is_nonneg b)).
  - exact Hwle.
Qed.

Lemma leiblw_S1_4 : leiblw_S 1 == (4 # 1)%Q.
Proof. cbn [leiblw_S leiblw_t leiblw_even]. reflexivity. Qed.

Lemma leiblw_S_le4 : forall n : nat, Qle (leiblw_S n) (4 # 1)%Q.
Proof.
  intros n. destruct (leiblw_par_decomp n) as [[j Hj]|[j Hj]].
  - rewrite Hj. destruct j as [|j'].
    + cbn [leiblw_S]. apply leiblw_qmake_le.
      rewrite Z.mul_0_l, Z.mul_1_r. apply Z.leb_le. reflexivity.
    + replace (2 * S j') with (S (2 * j' + 1))
        by (rewrite Nat.mul_succ_r, <- (plus_n_Sm (2 * j') 1); reflexivity).
      cbn [leiblw_S].
      assert (Ht : Qle (leiblw_t (2 * j' + 1)) 0%Q).
      { rewrite leiblw_t_odd. apply leiblw_qmake_le.
        rewrite Z.mul_1_r, Z.mul_0_l. apply Z.leb_le. reflexivity. }
      pose proof (leiblw_mono_odd j' 0 (Nat.le_0_l j')) as Hm.
      replace (2 * 0 + 1) with 1 in Hm by reflexivity.
      apply (Qle_trans _ (leiblw_S (2 * j' + 1))).
      * apply leiblw_qle_add_r. exact Ht.
      * rewrite <- (leiblw_S1_4). exact Hm.
  - pose proof (leiblw_mono_odd j 0 (Nat.le_0_l j)) as Hm.
    replace (2 * 0 + 1) with 1 in Hm by reflexivity.
    rewrite Hj.
    rewrite <- (leiblw_S1_4). exact Hm.
Qed.

Lemma leiblw_S_ge0 : forall n : nat, Qle 0%Q (leiblw_S n).
Proof.
  intros n. destruct (leiblw_par_decomp n) as [[j Hj]|[j Hj]].
  - rewrite Hj.
    pose proof (leiblw_mono_even j 0 (Nat.le_0_l j)) as Hm.
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    rewrite <- H0. exact Hm.
  - rewrite Hj.
    pose proof (leiblw_interlace j) as Hi.
    pose proof (leiblw_mono_even (j + 1) 0 (Nat.le_0_l (j + 1))) as Hm.
    replace (2 * (j + 1)) with (2 * j + 2) in Hm
      by (rewrite Nat.mul_add_distr_l, Nat.mul_1_r; reflexivity).
    assert (H0 : leiblw_S (2 * 0) == 0%Q) by reflexivity.
    rewrite <- H0.
    exact (Qle_trans (leiblw_S (2 * 0)) (leiblw_S (2 * j + 2)) (leiblw_S (2 * j + 1))
                     Hm Hi).
Qed.

(* [|x| <= c]: two-sided squeeze (pointwise three-case analysis on [Qabs]; no non-constructive principles). *)
Lemma leiblw_qabs_bound : forall x c : Q,
  Qle x c -> Qle (- x)%Q c -> Qle (Qabs x) c.
Proof.
  intros [z p] c H1 H2. cbn [Qabs]. cbn [Qopp] in H2.
  destruct z as [|z'|z']; [exact H1 | exact H1 | exact H2].
Qed.

(* ============================================================ *)
(* Section 14. The natural window is unbounded ([Set]-level delivery; the decision procedure replaced by [QltT]) *)
(* ============================================================ *)

(* (iv) The natural window is unbounded ([Set] level): any [nat] bound
   [B] is surpassed by the natural window at [n := S (B+B)] --
   [zf(2n) >= 2n >= B+1 > B] and [4b >= 4]. *)
Theorem leiblw_natwin_unbounded : forall b B : nat, (1 <= b)%nat ->
  sigT (fun n : nat => QltT ((Z.of_nat B # 1)%Q) (leiblw_natwin b n)).
Proof.
  intros b B Hb. exists (S (B + B)).
  apply Qlt_to_QltT.
  unfold leiblw_natwin. apply leiblw_qmake_lt.
  rewrite Z.mul_1_r, Z.mul_1_r.
  assert (H1 : (1 <= 2 * S (B + B))%nat).
  { apply (Nat.le_trans 1 2%nat).
    - apply Nat.leb_le. reflexivity.
    - replace 2 with (2 * 1)%nat by reflexivity.
      apply Nat.mul_le_mono_l.
      exact (proj1 (Nat.succ_le_mono 0 (B + B)) (Nat.le_0_l (B + B))). }
  assert (Hf : (Z.of_nat (2 * S (B + B)) <= leiblw_zf (2 * S (B + B)))%Z)
    by exact (leiblw_zf_ge_id (2 * S (B + B)) H1).
  assert (Hb1 : (1 <= Z.of_nat b)%Z).
  { replace 1%Z with (Z.of_nat 1) by reflexivity.
    exact (proj1 (Nat2Z.inj_le 1 b) Hb). }
  assert (H4b : (1 <= 4 * Z.of_nat b)%Z).
  { apply (Z.le_trans _ (4 * 1)%Z).
    - apply Z.leb_le. reflexivity.
    - apply Z.mul_le_mono_nonneg_l.
      + apply Z.leb_le. reflexivity.
      + exact Hb1. }
  assert (HB : (B + 1 <= 2 * S (B + B))%nat).
  { apply (Nat.le_trans (B + 1) (S (B + B))).
    - rewrite Nat.add_1_r.
      exact (proj1 (Nat.succ_le_mono B (B + B)) (Nat.le_add_r B B)).
    - apply Nat.le_add_r. }
  assert (HZ : ((Z.of_nat B + 1)%Z <= Z.of_nat (2 * S (B + B)))%Z).
  { replace ((Z.of_nat B + 1)%Z) with (Z.of_nat (B + 1))
      by (rewrite Nat2Z.inj_add; reflexivity).
    exact (proj1 (Nat2Z.inj_le (B + 1) (2 * S (B + B))) HB). }
  apply (Z.lt_le_trans (Z.of_nat B) (Z.of_nat B + 1)).
  - exact (Z.lt_succ_diag_r (Z.of_nat B)).
  - rewrite <- (Z.mul_1_l (Z.of_nat B + 1)%Z).
    apply Z.mul_le_mono_nonneg.
    + apply Z.leb_le. reflexivity.
    + exact H4b.
    + apply (Z.le_trans _ (Z.of_nat B + 0)%Z).
      * rewrite Z.add_0_r. apply Nat2Z.is_nonneg.
      * apply (proj1 (Z.add_le_mono_l 0 1 (Z.of_nat B))).
        apply Z.leb_le. reflexivity.
    + exact (Z.le_trans _ _ _ HZ Hf).
Qed.

(* ============================================================ *)
(* Section 15. The margin is unbounded ([Set]-level delivery; the decision procedure replaced by [QltT]) *)
(* ============================================================ *)

Theorem leiblw_margin_unbounded : forall B : nat,
  sigT (fun n : nat => QltT ((Z.of_nat B # 1)%Q) (leiblw_margin n)).
Proof.
  intros B. exists (B + 2). apply Qlt_to_QltT.
  assert (Hnorm : leiblw_margin (B + 2) ==
                  (8 * leiblw_zf (2 * (B + 2)) # Pos.of_succ_nat (2 * (B + 2) + 2))%Q).
  { unfold leiblw_margin, leiblw_qf, leiblw_gap.
    change (((leiblw_zf (2 * (B + 2) + 1) * 8)%Z
             # (1 * Pos.of_succ_nat (2 * (B + 2))
                * Pos.of_succ_nat (2 * (B + 2) + 2)))%Q
            == (8 * leiblw_zf (2 * (B + 2))
                # Pos.of_succ_nat (2 * (B + 2) + 2))%Q).
    apply leiblw_qmake_eq.
    rewrite (Pos.mul_1_l (Pos.of_succ_nat (2 * (B + 2)))).
    rewrite (leiblw_zf_2n1 (B + 2)).
    rewrite (leiblw_zpos_mul (2 * (B + 2)) (2 * (B + 2) + 2)).
    rewrite (leiblw_pos_succ1 (2 * (B + 2))).
    replace (Z.of_nat (S (2 * (B + 2)))) with (Z.of_nat (2 * (B + 2)) + 1)%Z
      by (rewrite Nat2Z.inj_succ; reflexivity).
    replace (Z.of_nat (S (2 * (B + 2) + 2))) with (Z.of_nat (2 * (B + 2) + 2) + 1)%Z
      by (rewrite Nat2Z.inj_succ; reflexivity).
    rewrite (leiblw_pos_succ1 (2 * (B + 2) + 2)).
    ring. }
  rewrite Hnorm.
  assert (H1' : (1 <= 2 * B + 3)%nat).
  { replace (2 * B + 3) with (3 + 2 * B) by (rewrite Nat.add_comm; reflexivity).
    apply (Nat.le_trans 1 3%nat).
    - apply Nat.leb_le. reflexivity.
    - apply (proj1 (Nat.add_le_mono_l 0 (2 * B) 3)). apply Nat.le_0_l. }
  assert (Hlow : (Z.of_nat (2 * B + 4) * Z.of_nat (2 * B + 3)
                  <= leiblw_zf (2 * B + 4))%Z).
  { replace (2 * B + 4) with (S (2 * B + 3))
      by (rewrite (Nat.add_succ_r (2 * B) 3); reflexivity).
    rewrite leiblw_zf_S, leiblw_pos_succ.
    apply Z.mul_le_mono_nonneg_l.
    - apply Nat2Z.is_nonneg.
    - exact (leiblw_zf_ge_id (2 * B + 3) H1'). }
  assert (Hn1e : (B + (B + 4) = 2 * B + 4)%nat).
  { replace (2 * B) with (B + B)
      by (replace 2 with (1 + 1)%nat by reflexivity;
          rewrite Nat.mul_add_distr_r, ?Nat.mul_1_l; reflexivity).
    rewrite Nat.add_assoc. reflexivity. }
  assert (Hn3 : (B + 3 <= 2 * B + 4)%nat).
  { apply (Nat.le_trans (B + 3) (B + (B + 4))).
    - apply (proj1 (Nat.add_le_mono_l 3 (B + 4) B)).
      apply (Nat.le_trans 3 4%nat).
      + apply Nat.leb_le. reflexivity.
      + rewrite (Nat.add_comm B 4). apply Nat.le_add_r.
    - rewrite Hn1e. apply Nat.le_refl. }
  assert (HW8 : ((Z.of_nat (2 * B + 6) + 1)%Z <= 8 * Z.of_nat (2 * B + 3))%Z).
  { replace (8 * Z.of_nat (2 * B + 3))%Z
      with (Z.of_nat (2 * B + 3) + 7 * Z.of_nat (2 * B + 3))%Z by ring.
    replace 7%Z with (Z.of_nat 7) by reflexivity.
    apply (Z.le_trans _ (Z.of_nat (2 * B + 3) + Z.of_nat 7)).
    - replace ((Z.of_nat (2 * B + 6) + 1)%Z) with (Z.of_nat (2 * B + 7))
        by (replace 1%Z with (Z.of_nat 1) by reflexivity;
            rewrite <- (Nat2Z.inj_add (2 * B + 6) 1), <- Nat.add_assoc; reflexivity).
      replace ((Z.of_nat (2 * B + 3) + Z.of_nat 7)%Z) with (Z.of_nat (2 * B + 3 + 7))
        by (rewrite <- (Nat2Z.inj_add (2 * B + 3) 7); reflexivity).
      exact (proj1 (Nat2Z.inj_le (2 * B + 7) (2 * B + 3 + 7))
                   (proj1 (Nat.add_le_mono_r (2 * B) (2 * B + 3) 7)
                          (Nat.le_add_r (2 * B) 3))).
    - apply Z.add_le_mono.
      + apply Z.le_refl.
      + apply (Z.le_trans _ (Z.of_nat 7 * 1)%Z).
        * replace ((Z.of_nat 7 * 1)%Z) with (Z.of_nat 7)
            by (rewrite Z.mul_1_r; reflexivity).
          apply Z.le_refl.
        * apply Z.mul_le_mono_nonneg_l.
          -- apply Nat2Z.is_nonneg.
          -- replace 1%Z with (Z.of_nat 1) by reflexivity.
             exact (proj1 (Nat2Z.inj_le 1 (2 * B + 3)) H1'). }
  apply leiblw_qmake_lt.
  rewrite (leiblw_pos_succ1 (2 * (B + 2) + 2)), Z.mul_1_r.
  replace (2 * (B + 2)) with (2 * B + 4) by (rewrite Nat.mul_add_distr_l; reflexivity).
  replace (2 * B + 4 + 2) with (2 * B + 6)
    by (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; reflexivity).
  replace ((Z.of_nat (2 * B + 6) + 1)%Z) with (Z.of_nat (2 * B + 7))
    by (replace 1%Z with (Z.of_nat 1) by reflexivity;
        rewrite <- (Nat2Z.inj_add (2 * B + 6) 1), <- Nat.add_assoc; reflexivity).
  assert (H0lt7 : (0 < 2 * B + 7)%nat).
  { replace (2 * B + 7) with (S (2 * B + 6))
      by (rewrite (Nat.add_succ_r (2 * B) 6); reflexivity).
    apply (proj1 (Nat.succ_le_mono 0 (2 * B + 6))). apply Nat.le_0_l. }
  assert (HBlt : (B < 2 * B + 4)%nat).
  { apply (Nat.lt_le_trans B (B + 1) (2 * B + 4)).
    - rewrite Nat.add_1_r. exact (Nat.lt_succ_diag_r B).
    - apply (Nat.le_trans (B + 1) (B + (B + 4))).
      + apply (proj1 (Nat.add_le_mono_l 1 (B + 4) B)).
        apply (Nat.le_trans 1 4%nat).
        * apply Nat.leb_le. reflexivity.
        * rewrite (Nat.add_comm B 4). apply Nat.le_add_r.
      + rewrite Hn1e. apply Nat.le_refl. }
  apply (Z.lt_le_trans (Z.of_nat B * Z.of_nat (2 * B + 7))
                       (Z.of_nat (2 * B + 4) * Z.of_nat (2 * B + 7))).
  - replace ((Z.of_nat B) * (Z.of_nat (2 * B + 7)))%Z
      with ((Z.of_nat (2 * B + 7)) * (Z.of_nat B))%Z
      by (apply (Z.mul_comm (Z.of_nat (2 * B + 7)) (Z.of_nat B))).
    replace ((Z.of_nat (2 * B + 4)) * (Z.of_nat (2 * B + 7)))%Z
      with ((Z.of_nat (2 * B + 7)) * (Z.of_nat (2 * B + 4)))%Z
      by (apply (Z.mul_comm (Z.of_nat (2 * B + 7)) (Z.of_nat (2 * B + 4)))).
    apply (proj1 (Z.mul_lt_mono_pos_l (Z.of_nat (2 * B + 7)) (Z.of_nat B)
                     (Z.of_nat (2 * B + 4))
                     (proj1 (Nat2Z.inj_lt 0 (2 * B + 7)) H0lt7))).
    exact (proj1 (Nat2Z.inj_lt B (2 * B + 4)) HBlt).
  - apply (Z.le_trans _ (Z.of_nat (2 * B + 4) * (8 * Z.of_nat (2 * B + 3)))).
    + apply Z.mul_le_mono_nonneg_l.
      * apply Nat2Z.is_nonneg.
      * replace (Z.of_nat (2 * B + 7)) with ((Z.of_nat (2 * B + 6) + 1)%Z)
          by (replace 1%Z with (Z.of_nat 1) by reflexivity;
              rewrite <- (Nat2Z.inj_add (2 * B + 6) 1), <- Nat.add_assoc; reflexivity).
        exact HW8.
    + replace ((Z.of_nat (2 * B + 4)) * (8 * Z.of_nat (2 * B + 3)))%Z
        with (8 * ((Z.of_nat (2 * B + 4)) * (Z.of_nat (2 * B + 3))))%Z by ring.
      apply Z.mul_le_mono_nonneg_l.
      * apply Z.leb_le. reflexivity.
      * exact Hlow.
Qed.

(* ============================================================ *)
(* Section 16. Comparison material for the non-trivialized family theorems (the factorial-family certification window vs. the Leibniz natural window; verbatim at the [Q] level) *)
(* ============================================================ *)

(* The factorial-family certification window (Niven-style): [w_niv n := 1/(2n+1)]. *)
Definition leiblw_nivwin (n : nat) : Q := (1 # Pos.of_succ_nat (n + n + 1))%Q.

(* The factorial-family window is always <= 1 (bounded) -- separated from [leiblw_natwin_unbounded]. *)
Theorem leiblw_nivwin_bounded : forall n : nat, Qle (leiblw_nivwin n) 1%Q.
Proof.
  intros n. unfold leiblw_nivwin. apply leiblw_qmake_le.
  rewrite Z.mul_1_r, Z.mul_1_l.
  rewrite (leiblw_pos_succ (n + n + 1)).
  exact (proj1 (Nat2Z.inj_le 1 (S (n + n + 1)))
               (proj1 (Nat.succ_le_mono 0 (n + n + 1)) (Nat.le_0_l (n + n + 1)))).
Qed.

(* The main separation statement ([Set] level): the Leibniz natural
   window exceeds 1 already at [n = 1] ([4*(2*1)! = 8 > 1]), while the
   factorial-family window is always <= 1 ([leiblw_nivwin_bounded]). *)
Theorem leiblw_family_separation :
  sigT (fun n : nat => QltT 1%Q (leiblw_natwin 1 n)).
Proof.
  exists 1. apply Qlt_to_QltT.
  unfold leiblw_natwin. apply leiblw_qmake_lt.
  rewrite Z.mul_1_r, Z.mul_1_r.
  replace (2 * 1) with 2 by reflexivity.
  apply Z.ltb_lt. reflexivity.
Qed.

(* ============================================================ *)
(* Section 17. Variant B: the computational certificate builder (tactic-free core: *)
(*     [pof]/[cert_core] are pure programs; [Set]-level specification statements; in-proof arithmetic closes via [ring], no external decision procedure) *)
(* ============================================================ *)

(* The common-denominator divisibility witness [P_n]: a tactic-free
   [Fixpoint] (mirroring the constructive step of [integrality]:
   [p_{k+1} = (2k+3)*(2k+2)*(p_k +/- 4*zf(2k))], the sign chosen by
   the parity of [k]). *)
Fixpoint leiblw_pof (n : nat) : Z :=
  match n with
  | 0 => 0%Z
  | S k =>
      Z.pos (Pos.of_succ_nat (S (S (2 * k)))) *
      (Z.pos (Pos.of_succ_nat (S (2 * k))) *
       (match leiblw_even k with
        | true => leiblw_pof k + 4 * leiblw_zf (2 * k)
        | false => leiblw_pof k - 4 * leiblw_zf (2 * k)
        end)%Z)
  end.

(* The [Nat.div2] bridge (the [2m]/[2m+1] dichotomy; equality conclusions at the [Set] level). *)
Lemma leiblw_div2_even : forall m : nat, Nat.div2 (2 * m) = m.
Proof. intros m. apply Nat.div2_double. Qed.

Lemma leiblw_div2_odd : forall m : nat, Nat.div2 (2 * m + 1) = m.
Proof.
  intros m.
  replace (2 * m + 1) with (S (2 * m)) by (rewrite Nat.add_1_r; reflexivity).
  apply Nat.div2_succ_double.
Qed.

(* A one-step [Q] difference identity: [((A + U) - A) == U] (the closing piece of the first check of the certificate). *)
Lemma leiblw_qstep_diff : forall A U : Q, ((A + U) - A)%Q == U%Q.
Proof.
  intros A U. unfold Qminus.
  rewrite <- (Qplus_assoc A U (- A)%Q).
  rewrite (Qplus_comm U (- A)%Q).
  rewrite (Qplus_assoc A (- A)%Q U).
  rewrite Qplus_opp_r. apply Qplus_0_l.
Qed.

(* The specification of [P_n] (a [Set]-level statement; induction with a [Set]-valued IH; computational closure via [Qeq_bool]). *)
Lemma leiblw_pof_spec : forall n : nat,
  Id (Qeq_bool (leiblw_qf (2 * n + 1) * leiblw_S n) (leiblw_pof n # 1)) true.
Proof.
  induction n as [|n IH].
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    cbn [leiblw_pof leiblw_qf leiblw_zf leiblw_S Qnum Qden Qmult]. ring.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    apply leiblw_id_inv in IH. apply (proj1 (Qeq_bool_iff _ _)) in IH.
    unfold leiblw_qf in IH. rewrite leiblw_zf_2n1 in IH.
    replace (2 * S n + 1) with (2 * n + 3)
      by (rewrite Nat.mul_succ_r, <- Nat.add_assoc; reflexivity).
    cbn [leiblw_pof]. destruct (leiblw_even n) eqn:Hev.
    + cbn [leiblw_S]. rewrite leiblw_t_pos_case by exact Hev.
      unfold leiblw_qf at 1. rewrite leiblw_zf_2n3.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (S (S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) IH) as IH2.
      rewrite Z.mul_1_r in IH2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) + (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite IH2. ring.
    + cbn [leiblw_S]. rewrite leiblw_t_neg_case by exact Hev.
      unfold leiblw_qf at 1. rewrite leiblw_zf_2n3.
      unfold Qeq in *. cbn [Qnum Qden Qmult Qplus Qminus Qopp Pos.mul] in *.
      rewrite (Pos2Z.inj_mul (Qden (leiblw_S n)) (Pos.of_succ_nat (2 * n))).
      set (Zp := Z.pos (Pos.of_succ_nat (2 * n))) in *.
      set (Zd := Z.pos (Qden (leiblw_S n))) in *.
      set (W := leiblw_zf (2 * n)) in *.
      set (N := Qnum (leiblw_S n)) in *.
      set (A := Z.pos (Pos.of_succ_nat (S (2 * n)))) in *.
      set (B := Z.pos (Pos.of_succ_nat (S (S (2 * n))))) in *.
      pose proof (f_equal (fun v : Z => (v * Zp)%Z) IH) as IH2.
      rewrite Z.mul_1_r in IH2.
      transitivity (((A * B) * ((Zp * W) * N * Zp) - (4 * (A * B)) * (Zp * W * Zd))%Z).
      * ring.
      * rewrite IH2. ring.
Qed.

(* The certificate core: a pure-data quadruple ([lo] lower-bound witness, [hi] upper-bound witness, [P_n], the [gap] value) -- tactic-free. *)
Definition leiblw_cert_core (n : nat) : (Q * (Q * (Z * Q)))%type :=
  (leiblw_S (2 * Nat.div2 n),
   (leiblw_S (2 * Nat.div2 n + 1),
    (leiblw_pof n, leiblw_gap n))).

(* The certificate (first form: [forall n] with [sigT] and product-type conjunction, at the [Set] level; the three core checks are all [Id] + [Qeq_bool]). *)
Theorem leiblw_cert : forall n : nat,
  sigT (fun lo : Q =>
    sigT (fun hi : Q =>
      sigT (fun p : Z =>
        sigT (fun g : Q =>
          (Id (Qeq_bool ((hi - lo)%Q) (leiblw_t (2 * Nat.div2 n))) true *
           (Id (Qeq_bool (leiblw_qf (2 * n + 1) * leiblw_S n) (p # 1)) true *
            Id (Qeq_bool (p # 1) (leiblw_qf (2 * n + 1) * leiblw_S n)) true))%type)))).
Proof.
  intros n.
  exists (leiblw_S (2 * Nat.div2 n)).
  exists (leiblw_S (2 * Nat.div2 n + 1)).
  exists (leiblw_pof n). exists (leiblw_gap n).
  split.
  - apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
    destruct (leiblw_par_decomp n) as [[m Hm]|[m Hm]].
    + rewrite Hm, !leiblw_div2_even.
      replace (2 * m + 1) with (S (2 * m)) by (rewrite Nat.add_1_r; reflexivity).
      rewrite (leiblw_S_step (2 * m)).
      apply leiblw_qstep_diff.
    + rewrite Hm, !leiblw_div2_odd.
      replace (2 * m + 1) with (S (2 * m)) by (rewrite Nat.add_1_r; reflexivity).
      rewrite (leiblw_S_step (2 * m)).
      apply leiblw_qstep_diff.
  - split.
    + exact (leiblw_pof_spec n).
    + apply leiblw_id_eq. apply (proj2 (Qeq_bool_iff _ _)).
      pose proof (leiblw_pof_spec n) as Hps.
      apply leiblw_id_inv in Hps. apply (proj1 (Qeq_bool_iff _ _)) in Hps.
      apply Qeq_sym. exact Hps.
Qed.

(* Statement provenance: for every statement of this file, the
   source statement of this development that it was migrated from,
   with the source coordinates.  Rows marked (new) are statements
   first stated in this file.

   [Id] <- [Id] at [S01_BaseRing.v:L41-L43]
   [id_trans] <- [id_trans] at [S01_BaseRing.v:L59-L62]
   [Qlt_bool] <- [Qlt_bool] at [S02_CauchyComplete.v:L42-L47]
   [QltT] <- [QltT] at [S02_CauchyComplete.v:L48]
   [QleT'] <- [QleT'] at [S02_CauchyComplete.v:L99]
   [qltw_S02_Qlt_bool] <- [Qlt_bool] (restated as [qltw_S02_Qlt_bool]) at [S02_CauchyComplete.v:L42-L47]
   [qltw_S02_Qle_bool] <- [Qle_bool] (restated as [qltw_S02_Qle_bool]) at [S02_CauchyComplete.v:L92-L96]
   [qltw_Qlt_bool_Qcompare] <- (new in this file)
   [qltw_Qle_bool_Qcompare] <- (new in this file)
   [qltw_Qeq_bool_Qcompare] <- (new in this file)
   [qltw_Qlt_bool_orig] <- (new in this file)
   [qltw_Qle_bool_orig] <- (new in this file)
   [qltw_QltT_orig] <- (new in this file)
   [qltw_S02_QltT] <- (new in this file)
   [qltw_QleT'_orig] <- (new in this file)
   [qltw_S02_QleT'] <- (new in this file)
   [qltw_samp_QltT_0_1] <- (new in this file)
   [qltw_samp_QleT'_1_1] <- (new in this file)
   [qltw_samp_Qeq_bool_2_2] <- (new in this file)
   [leiblw_id_eq] <- [leiblw_id_eq] at [LW0LeibWindow.v:L65-L66]
   [leiblw_id_inv] <- [leiblw_id_inv] at [LW0LeibWindow.v:L68-L69]
   [QltT_to_Qlt] <- [QltT_to_Qlt] at [S02_CauchyComplete.v:L51-L58]
   [Qlt_to_QltT] <- [Qlt_to_QltT] at [S02_CauchyComplete.v:L60-L80]
   [QleT'_to_Qle] <- [QleT'_to_Qle] at [S02_CauchyComplete.v:L103-L112]
   [Qle_to_QleT'] <- [Qle_to_QleT'] at [S02_CauchyComplete.v:L115-L122]
   [leiblw_even] <- [leiblw_even] at [LW0LeibWindow.v:L32-L36]
   [leiblw_even_2m] <- [leiblw_even_2m] at [LW0LeibWindow.v:L38-L43]
   [leiblw_even_2m1] <- [leiblw_even_2m1] at [LW0LeibWindow.v:L45-L49]
   [leiblw_par_decomp] <- [leiblw_par_decomp] at [LW0LeibWindow.v:L52-L60]
   [leiblw_znat_pos] <- [leiblw_znat_pos] at [LW0LeibWindow.v:L94-L98]
   [leiblw_pos_succ] <- [leiblw_pos_succ] at [LW0LeibWindow.v:L101-L105]; source at [LW0LeibWindow.v:L108-L110]
   [leiblw_pos_succ1] <- [leiblw_pos_succ1] at [LW0LeibWindow.v:L113-L114]
   [leiblw_qmake_eq] <- [leiblw_qmake_eq] at [LW0LeibWindow.v:L116-L120]
   [leiblw_qmake_lt] <- [leiblw_qmake_lt] at [LW0LeibWindow.v:L122-L128]
   [leiblw_qmake_le] <- [leiblw_qmake_le] at [LW0LeibWindow.v:L130-L136]
   [leiblw_qabs_id] <- [leiblw_qabs_id] at [LW0LeibWindow.v:L138-L145]
   [leiblw_qabs_neg] <- [leiblw_qabs_neg] at [LW0LeibWindow.v:L147-L154]
   [leiblw_t] <- [leiblw_t] at [LW0LeibWindow.v:L160-L163]
   [leiblw_S] <- [leiblw_S] at [LW0LeibWindow.v:L165-L169]
   [leiblw_S_SS] <- [leiblw_S_SS] at [LW0LeibWindow.v:L171-L173]
   [leiblw_S_step] <- [leiblw_S_step] at [LW0LeibWindow.v:L175-L176]
   [leiblw_t_pos_case] <- [leiblw_t_pos_case] at [LW0LeibWindow.v:L178-L180]
   [leiblw_t_neg_case] <- [leiblw_t_neg_case] at [LW0LeibWindow.v:L182-L184]
   [leiblw_t_even] <- [leiblw_t_even] at [LW0LeibWindow.v:L186-L191]
   [leiblw_t_odd] <- [leiblw_t_odd] at [LW0LeibWindow.v:L193-L198]
   [leiblw_t_even_pos] <- [leiblw_t_even_pos] at [LW0LeibWindow.v:L200-L205]
   [leiblw_t_odd_neg] <- [leiblw_t_odd_neg] at [LW0LeibWindow.v:L207-L211]
   [leiblw_qplus_norm] <- [leiblw_qplus_norm] at [LW0LeibWindow.v:L218-L223]
   [leiblw_qplus_lt0] <- [leiblw_qplus_lt0] at [LW0LeibWindow.v:L225-L230]
   [leiblw_qplus_lt0b] <- [leiblw_qplus_lt0b] at [LW0LeibWindow.v:L232-L238]
   [leiblw_qplus_le0] <- [leiblw_qplus_le0] at [LW0LeibWindow.v:L240-L245]
   [leiblw_qplus_eq] <- [leiblw_qplus_eq] at [LW0LeibWindow.v:L247-L253]
   [leiblw_qopp_distr] <- [leiblw_qopp_distr] at [LW0LeibWindow.v:L255-L258]
   [leiblw_qneg_plus_eq] <- [leiblw_qneg_plus_eq] at [LW0LeibWindow.v:L261-L268]
   [leiblw_qshunt] <- [leiblw_qshunt] at [LW0LeibWindow.v:L271-L281]
   [leiblw_qplus_opp_l0] <- [leiblw_qplus_opp_l0] at [LW0LeibWindow.v:L283-L284]
   [leiblw_qshunt_neg] <- [leiblw_qshunt_neg] at [LW0LeibWindow.v:L287-L292]
   [leiblw_qopp_lt] <- [leiblw_qopp_lt] at [LW0LeibWindow.v:L294-L297]
   [leiblw_qminus_flip] <- [leiblw_qminus_flip] at [LW0LeibWindow.v:L299-L300]
   [leiblw_qle_add_r] <- [leiblw_qle_add_r] at [LW0LeibWindow.v:L302-L303]
   [leiblw_qle_add2_r] <- [leiblw_qle_add2_r] at [LW0LeibWindow.v:L305-L310]
   [leiblw_qle_add_l] <- [leiblw_qle_add_l] at [LW0LeibWindow.v:L312-L313]
   [leiblw_qplus_le0b] <- [leiblw_qplus_le0b] at [LW0LeibWindow.v:L315-L320]
   [leiblw_zpos_mul] <- [leiblw_zpos_mul] at [LW0LeibWindow.v:L322-L327]
   [leiblw_step_even_pos] <- [leiblw_step_even_pos] at [LW0LeibWindow.v:L333-L347]
   [leiblw_step_odd_neg] <- [leiblw_step_odd_neg] at [LW0LeibWindow.v:L349-L365]
   [leiblw_interlace] <- [leiblw_interlace] at [LW0LeibWindow.v:L367-L377]
   [leiblw_mono_even] <- [leiblw_mono_even] at [LW0LeibWindow.v:L379-L402]
   [leiblw_mono_odd] <- [leiblw_mono_odd] at [LW0LeibWindow.v:L404-L427]
   [leiblw_gap] <- [leiblw_gap] at [LW0LeibWindow.v:L433-L434]
   [leiblw_gap_pos] <- [leiblw_gap_pos] at [LW0LeibWindow.v:L436-L437]
   [leiblw_gap_even_step] <- [leiblw_gap_even_step] at [LW0LeibWindow.v:L439-L461]
   [leiblw_gap_odd_step] <- [leiblw_gap_odd_step] at [LW0LeibWindow.v:L463-L489]
   [leiblw_lower_even_e] <- [leiblw_lower_even_e] at [LW0LeibWindow.v:L601-L609]
   [leiblw_lower_even_o] <- [leiblw_lower_even_o] at [LW0LeibWindow.v:L612-L623]
   [leiblw_lower_odd_e] <- [leiblw_lower_odd_e] at [LW0LeibWindow.v:L626-L638]
   [leiblw_lower_odd_o] <- [leiblw_lower_odd_o] at [LW0LeibWindow.v:L641-L649]
   [leiblw_dist] <- [leiblw_dist] at [LW0LeibWindow.v:L652-L719]
   [leiblw_dist_set] <- [leiblw_dist_set] at [LW0LeibWindow.v:L747-L754]
   [leiblw_zf] <- [leiblw_zf] at [LW0LeibWindow.v:L495-L500]
   [leiblw_qf] <- [leiblw_qf] at [LW0LeibWindow.v:L501-L502]
   [leiblw_zf_S] <- (new in this file)
   [leiblw_zf_ge1] <- [leiblw_zf_ge1] at [LW0LeibWindow.v:L503-L504]
   [leiblw_zf_ge_id] <- [leiblw_zf_ge_id] at [LW0LeibWindow.v:L506-L513]
   [leiblw_zf_lower] <- [leiblw_zf_lower] at [LW0LeibWindow.v:L515-L526]
   [leiblw_zf_2n1] <- [leiblw_zf_2n1] at [LW0LeibWindow.v:L528-L533]
   [leiblw_zf_2n3] <- [leiblw_zf_2n3] at [LW0LeibWindow.v:L536-L543]
   [leiblw_integrality] <- [leiblw_integrality] at [LW0LeibWindow.v:L546-L597]
   [leiblw_margin] <- [leiblw_margin] at [LW0LeibWindow.v:L761-L762]
   [leiblw_natwin] <- [leiblw_natwin] at [LW0LeibWindow.v:L769-L770]
   [leiblw_qabs_make] <- [leiblw_qabs_make] at [LW0LeibWindow.v:L772-L773]
   [leiblw_natwin_residual] <- [leiblw_natwin_residual] at [LW0LeibWindow.v:L777-L789]
   [leiblw_natwin_ge] <- [leiblw_natwin_ge] at [LW0LeibWindow.v:L791-L798]
   [leiblw_zle_mul1] <- (new in this file)
   [leiblw_natwin_mono] <- [leiblw_natwin_mono] at [LW0LeibWindow.v:L800-L814]
   [leiblw_S1_4] <- [leiblw_S1_4] at [LW0LeibWindow.v:L816-L817]
   [leiblw_S_le4] <- [leiblw_S_le4] at [LW0LeibWindow.v:L819-L838]
   [leiblw_S_ge0] <- [leiblw_S_ge0] at [LW0LeibWindow.v:L840-L852]
   [leiblw_qabs_bound] <- [leiblw_qabs_bound] at [LW0LeibWindow.v:L854-L860]
   [leiblw_natwin_unbounded] <- [leiblw_natwin_unbounded] at [LW0LeibWindow.v:L894-L908]
   [leiblw_margin_unbounded] <- [leiblw_margin_unbounded] at [LW0LeibWindow.v:L910-L921]
   [leiblw_nivwin] <- [leiblw_nivwin] at [LW0LeibWindow.v:L959-L960]
   [leiblw_nivwin_bounded] <- [leiblw_nivwin_bounded] at [LW0LeibWindow.v:L962-L966]
   [leiblw_family_separation] <- [leiblw_family_separation] at [LW0LeibWindow.v:L971-L978]
   [leiblw_pof] <- [leiblw_pof] at [LW0LeibWindow.v:L1030-L1041]
   [leiblw_div2_even] <- [leiblw_div2_even] at [LW0LeibWindow.v:L1043-L1045]
   [leiblw_div2_odd] <- [leiblw_div2_odd] at [LW0LeibWindow.v:L1048-L1050]
   [leiblw_qstep_diff] <- (new in this file)
   [leiblw_pof_spec] <- [leiblw_pof_spec] at [LW0LeibWindow.v:L1055-L1096]
   [leiblw_cert_core] <- [leiblw_cert_core] at [LW0LeibWindow.v:L1099-L1103]
   [leiblw_cert] <- [leiblw_cert] at [LW0LeibWindow.v:L1105-L1135]
*)
