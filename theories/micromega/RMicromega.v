(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria)                                       *)
(*                                                                      *)
(************************************************************************)

From Stdlib Require Import OrderedRing.
From Stdlib Require Import QMicromega RingMicromega MMicromega.
From Stdlib Require Import Refl.
From Stdlib Require Import Sumbool Raxioms Rfunctions RIneq Rpow_def.
From Stdlib Require Import BinNat.
From Stdlib Require Import QArith.
From Stdlib Require Import Qfield.
From Stdlib Require Import Qreals.
From Stdlib Require Import DeclConstant.
From Stdlib Require Import Znat.
From Stdlib Require Import MSetPositive.
From Stdlib Require Setoid.
From Stdlib Require Import isZ.
Set Implicit Arguments.


Definition Rsrt : ring_theory R0 R1 Rplus Rmult Rminus Ropp (@eq R).
Proof.
  constructor.
  - exact Rplus_0_l.
  - exact Rplus_comm.
  - intros. rewrite Rplus_assoc. auto.
  - exact Rmult_1_l.
  - exact Rmult_comm.
  - intros ; rewrite Rmult_assoc ; auto.
  - intros. rewrite Rmult_comm. rewrite Rmult_plus_distr_l.
    rewrite (Rmult_comm z).    rewrite (Rmult_comm z). auto.
  - reflexivity.
  - exact Rplus_opp_r.
Qed.


Lemma Rsor : SOR R0 R1 Rplus Rmult Rminus Ropp (@eq R)  Rle Rlt.
Proof.
  constructor; intros ; subst ; try (intuition (subst; try ring ; auto with real)).
  - constructor.
    + constructor.
    + unfold RelationClasses.Symmetric. auto.
    + unfold RelationClasses.Transitive. intros. subst. reflexivity.
  - apply Rsrt.
  - eapply Rle_trans ; eauto.
  - apply (Rlt_irrefl m) ; auto.
  - apply Rnot_le_lt. auto with real.
  - destruct (total_order_T n m) as [ [H1 | H1] | H1] ; auto.
  - now apply Rmult_lt_0_compat.
Qed.

Local Open Scope R_scope.


Lemma Rinv_1 : forall x, x * / 1 = x.
Proof.
  intro.
  rewrite Rinv_1.
  apply Rmult_1_r.
Qed.

Lemma Qeq_true : forall x y, Qeq_bool x y = true -> Q2R x = Q2R y.
Proof.
  intros.
  now apply Qeq_eqR, Qeq_bool_eq.
Qed.

Lemma Qeq_false : forall x y, Qeq_bool x y = false -> Q2R x <> Q2R y.
Proof.
  intros.
  apply Qeq_bool_neq in H.
  contradict H.
  now apply eqR_Qeq.
Qed.

Lemma Qle_true : forall x y : Q, Qle_bool x y = true -> Q2R x <= Q2R y.
Proof.
  intros.
  now apply Qle_Rle, Qle_bool_imp_le.
Qed.

Lemma Q2R_0 : Q2R 0 = 0.
Proof.
  apply Rmult_0_l.
Qed.

Lemma Q2R_1 : Q2R 1 = 1.
Proof.
  compute. apply Rinv_1.
Qed.

Lemma Q2R_inv_ext : forall x,
  Q2R (/ x) = (if Qeq_bool x 0 then 0 else / Q2R x).
Proof.
  intros.
  case_eq (Qeq_bool x 0).
  - intros.
    apply Qeq_bool_eq in H.
    destruct x ; simpl.
    unfold Qeq in H.
    simpl in H.
    rewrite Zmult_1_r in H.
    rewrite H.
    apply Rmult_0_l.
  - intros.
    now apply Q2R_inv, Qeq_bool_neq.
Qed.

Lemma QSORaddon :
  @SORaddon R
  R0 R1 Rplus Rmult Rminus Ropp  (@eq R)  Rle (* ring elements *)
  Q 0%Q 1%Q Qplus Qmult Qminus Qopp (* coefficients *)
  Qeq_bool Qle_bool
  Q2R nat N.to_nat pow.
Proof.
  constructor.
  - constructor ; intros ; try reflexivity.
    + apply Q2R_0.
    + apply Q2R_1.
    + apply Q2R_plus.
    + apply Q2R_minus.
    + apply Q2R_mult.
    + apply Q2R_opp.
    + apply Qeq_true ; auto.
  - apply R_power_theory.
  - apply Qeq_false.
  - apply Qle_true.
Qed.

Lemma IPR_2_eq : forall p,
    IPR_2 p = MMicromega.IPR R R1 Rplus p + MMicromega.IPR R R1 Rplus p.
Proof.
  induction p; simpl; auto.
  - rewrite <- IHp.
    ring.
  - rewrite <- IHp.
    ring.
Qed.

Lemma IPR_eq : forall p,
    IPR p = MMicromega.IPR R R1 Rplus p.
Proof.
  unfold IPR; destruct p; simpl;
    try rewrite IPR_2_eq; reflexivity.
Qed.


Lemma IZR_eq : forall x,
    MMicromega.IZR R R0 R1 Rplus Ropp x = IZR x.
Proof.
  destruct x ; simpl.
  - reflexivity.
  - unfold IZR.
    now rewrite  IPR_eq.
  - unfold IZR.
    f_equal.
    now rewrite  IPR_eq.
Qed.

Lemma isZ_eq : forall r,
    isZ.isZ r ->
    MMicromega.isZ R R0 R1 Rplus Ropp eq r.
Proof.
  intros.
  destruct H as (z & EQ).
  exists z.
  now rewrite IZR_eq.
Qed.






Lemma ZSORaddon :
  @SORaddon R
  R0 R1 Rplus Rmult Rminus Ropp  (@eq R)  Rle (* ring elements *)
  Z 0%Z 1%Z Z.add Z.mul Z.sub Z.opp (* coefficients *)
  Z.eqb Z.leb
  (MMicromega.IZR R R0 R1 Rplus Ropp)
  nat N.to_nat pow.
Proof.
  constructor.
  - constructor ; intros.
    + reflexivity.
    + reflexivity.
    +
      rewrite! IZR_eq.
      apply plus_IZR.
    + rewrite! IZR_eq.
      apply minus_IZR.
    + rewrite! IZR_eq.
      apply mult_IZR.
    + rewrite! IZR_eq.
      apply opp_IZR.
    + rewrite! IZR_eq.
      rewrite Z.eqb_eq in H. now f_equal.
  - apply R_power_theory.
  - intros.
    rewrite! IZR_eq.
    rewrite Z.eqb_neq in H.
    intro. apply H.
    apply eq_IZR; auto.
  - intros.
    rewrite! IZR_eq.
    apply IZR_le.
    now rewrite Z.leb_le in H.
Qed.


(* Syntactic ring coefficients. *)

Inductive Rcst :=
  | C0
  | C1
  | CQ (r : Q)
  | CZ (r : Z)
  | CPlus (r1 r2 : Rcst)
  | CMinus (r1  r2 : Rcst)
  | CMult (r1 r2 : Rcst)
  | CPow  (r1 : Rcst) (z:Z+nat)
  | CInv  (r : Rcst)
  | COpp  (r : Rcst).

Register Rcst   as micromega.Rcst.type.
Register C0     as micromega.Rcst.C0.
Register C1     as micromega.Rcst.C1.
Register CQ     as micromega.Rcst.CQ.
Register CZ     as micromega.Rcst.CZ.
Register CPlus  as micromega.Rcst.CPlus.
Register CMinus as micromega.Rcst.CMinus.
Register CMult  as micromega.Rcst.CMult.
Register CPow   as micromega.Rcst.CPow.
Register CInv   as micromega.Rcst.CInv.
Register COpp   as micromega.Rcst.COpp.

Definition z_of_exp (z : Z + nat) :=
  match z with
  | inl z => z
  | inr n => Z.of_nat n
  end.

Fixpoint Q_of_Rcst (r : Rcst) : Q :=
  match r with
    | C0 => 0 # 1
    | C1 => 1 # 1
    | CZ z => z # 1
    | CQ q => q
    | CPlus r1 r2 => Qplus (Q_of_Rcst r1) (Q_of_Rcst r2)
    | CMinus r1 r2 => Qminus (Q_of_Rcst r1) (Q_of_Rcst r2)
    | CMult r1 r2  => Qmult (Q_of_Rcst r1) (Q_of_Rcst r2)
    | CPow  r1 z   => Qpower (Q_of_Rcst r1) (z_of_exp z)
    | CInv r       => Qinv (Q_of_Rcst r)
    | COpp r       => Qopp (Q_of_Rcst r)
  end.


Definition is_neg (z: Z+nat) :=
  match z with
  | inl (Zneg _) => true
  |  _           => false
  end.

Lemma is_neg_true : forall z, is_neg z = true -> (z_of_exp z < 0)%Z.
Proof.
  destruct z ; simpl ; try congruence.
  destruct z ; try congruence.
  intros.
  reflexivity.
Qed.

Lemma is_neg_false : forall z, is_neg z = false -> (z_of_exp z >= 0)%Z.
Proof.
  destruct z ; simpl ; try congruence.
  - destruct z ; try congruence.
    + compute. congruence.
    + compute. congruence.
  - generalize (Znat.Nat2Z.is_nonneg n). auto using Z.le_ge.
Qed.

Definition CInvR0 (r : Rcst) := Qeq_bool (Q_of_Rcst r) (0 # 1).

Definition CPowR0 (z : Z) (r : Rcst) :=
  Z.ltb z Z0 && Qeq_bool (Q_of_Rcst r) (0 # 1).

Fixpoint R_of_Rcst (r : Rcst) : R :=
  match r with
    | C0 => R0
    | C1 => R1
    | CZ z => IZR z
    | CQ q => Q2R q
    | CPlus r1 r2  => (R_of_Rcst r1) + (R_of_Rcst r2)
    | CMinus r1 r2 => (R_of_Rcst r1) - (R_of_Rcst r2)
    | CMult r1 r2  => (R_of_Rcst r1) * (R_of_Rcst r2)
    | CPow r1 z    =>
      match z with
      | inl z =>
        if CPowR0 z r1
        then R0
        else  powerRZ (R_of_Rcst r1) z
      | inr n => pow (R_of_Rcst r1) n
      end
    | CInv r       =>
      if CInvR0 r then R0
      else Rinv (R_of_Rcst r)
    | COpp r       => - (R_of_Rcst r)
  end.

Add Morphism Q2R with signature Qeq ==> @eq R as Q2R_m.
  exact Qeq_eqR.
Qed.

Lemma Q2R_pow_pos : forall q p,
    Q2R (pow_pos Qmult q p) = pow_pos Rmult (Q2R q) p.
Proof.
  induction p ; simpl;auto;
    rewrite <- IHp;
    repeat rewrite Q2R_mult;
    reflexivity.
Qed.

Lemma Q2R_pow_N : forall q n,
  Q2R (pow_N 1%Q Qmult q n) = pow_N 1 Rmult (Q2R q) n.
Proof.
  destruct n ; simpl.
  - apply Q2R_1.
  - apply Q2R_pow_pos.
Qed.

Lemma Qmult_integral : forall q r, q * r ==  0 -> q == 0 \/ r == 0.
Proof.
  intros.
  destruct (Qeq_dec q 0)%Q.
  - left ; apply q0.
  - apply Qmult_integral_l in H ; tauto.
Qed.

Lemma Qpower_positive_eq_zero : forall q p,
    Qpower_positive q p == 0 -> q == 0.
Proof.
  unfold Qpower_positive.
  induction p ; simpl; intros;
    repeat match goal with
    | H : _ * _ == 0 |- _ =>
      apply Qmult_integral in H; destruct H
    end; tauto.
Qed.

Lemma Qpower_positive_zero : forall p,
    Qpower_positive 0 p == 0%Q.
Proof.
  induction p ; simpl;
    try rewrite IHp ; reflexivity.
Qed.


Lemma Q2RpowerRZ :
  forall q z
         (DEF : not (q == 0)%Q \/ (z >= Z0)%Z),
    Q2R (q ^ z) = powerRZ (Q2R q) z.
Proof.
  intros.
  destruct Qpower_theory.
  destruct R_power_theory.
  unfold Qpower, powerRZ.
  destruct z.
  - apply Q2R_1.

  - change (Qpower_positive q p)
      with (Qpower q (Zpos p)).
    rewrite <- N2Z.inj_pos.
    rewrite <- positive_N_nat.
    rewrite rpow_pow_N.
    rewrite rpow_pow_N0.
    apply Q2R_pow_N.

  - rewrite  Q2R_inv.
    + unfold Qpower_positive.
      rewrite <- positive_N_nat.
      rewrite rpow_pow_N0.
      unfold pow_N.
      rewrite Q2R_pow_pos.
      auto.
    + intro.
      apply Qpower_positive_eq_zero in H.
      destruct DEF ; auto with arith.
Qed.

Lemma Qpower0 : forall z, (z <> 0)%Z -> (0 ^ z == 0)%Q.
Proof.
  unfold Qpower.
  destruct z;intros.
  - congruence.
  - apply Qpower_positive_zero.
  - rewrite Qpower_positive_zero.
    reflexivity.
Qed.


Lemma Q_of_RcstR : forall c, Q2R (Q_of_Rcst c) = R_of_Rcst c.
Proof.
  induction c ; simpl ; try (rewrite <- IHc1 ; rewrite <- IHc2).
  - apply Q2R_0.
  - apply Q2R_1.
  - reflexivity.
  - unfold Q2R. simpl. rewrite Rinv_1. reflexivity.
  - apply Q2R_plus.
  - apply Q2R_minus.
  - apply Q2R_mult.
  - destruct z.
    1:destruct (CPowR0 z c) eqn:C; unfold CPowR0 in C.
    +
      rewrite andb_true_iff in C.
      destruct C as (C1 & C2).
      rewrite Z.ltb_lt in C1.
      apply Qeq_bool_eq in C2.
      rewrite C2.
      simpl.
      assert (z <> 0%Z).
      { intro ; subst. apply Z.lt_irrefl in C1. auto. }
      rewrite Qpower0 by auto.
      apply Q2R_0.
    + rewrite Q2RpowerRZ.
      * rewrite IHc.
        reflexivity.
      * rewrite andb_false_iff in C.
        destruct C.
        -- simpl. apply Z.ltb_ge in H.
           auto using Z.le_ge.
        -- left ; apply Qeq_bool_neq; auto.
    + simpl.
      rewrite <- IHc.
      destruct Qpower_theory.
      rewrite <- nat_N_Z.
      rewrite rpow_pow_N.
      destruct R_power_theory.
      rewrite <- (Nnat.Nat2N.id n) at 2.
      rewrite rpow_pow_N0.
      apply Q2R_pow_N.
  - rewrite <- IHc.
    unfold CInvR0.
    apply Q2R_inv_ext.
  - rewrite <- IHc.
    apply Q2R_opp.
Qed.

From Stdlib Require Import EnvRing.

Definition Reval_expr := eval_pexpr  Rplus Rmult Rminus Ropp R_of_Rcst N.to_nat pow.


Definition Reval_pop2 (o:Op2) : R -> R -> Prop :=
    match o with
      | OpEq =>  @eq R
      | OpNEq => fun x y  => ~ x = y
      | OpLe => Rle
      | OpGe => Rge
      | OpLt => Rlt
      | OpGt => Rgt
    end.

Definition sumboolb {A B : Prop} (x : @sumbool A B) : bool :=
  if x then true else false.


Definition Reval_bop2 (o : Op2) : R -> R -> bool :=
  match o with
  | OpEq  => fun x y => sumboolb (Req_dec_T x y)
  | OpNEq => fun x y => negb (sumboolb (Req_dec_T x y))
  | OpLe  => fun x y => (sumboolb (Rle_lt_dec x y))
  | OpGe  => fun x y => (sumboolb (Rge_gt_dec x y))
  | OpLt  => fun x y => (sumboolb (Rlt_le_dec x y))
  | OpGt  => fun x y => (sumboolb (Rgt_dec x y))
  end.

Lemma pop2_bop2 :
  forall (op : Op2) (r1 r2 : R), is_true (Reval_bop2 op r1 r2) <-> Reval_pop2 op r1 r2.
Proof.
  unfold is_true.
  destruct op ; simpl; intros;
  match goal with
  | |- context[sumboolb (?F ?X ?Y)] =>
    destruct (F X Y) ; simpl; intuition try congruence
  end.
  - apply Rlt_not_le in r. tauto.
  - apply Rgt_not_ge in r. tauto.
  - apply Rlt_not_le in H. tauto.
Qed.

Definition Reval_op2 (k: Tauto.kind) :  Op2 ->  R -> R -> Tauto.rtyp k:=
  if k as k0 return (Op2 -> R -> R -> Tauto.rtyp k0)
  then Reval_pop2 else Reval_bop2.

Lemma Reval_op2_hold : forall b op q1 q2,
    Tauto.hold b (Reval_op2 b op q1 q2) <-> Reval_pop2 op q1 q2.
Proof.
  destruct b.
  - simpl ; tauto.
  - simpl. apply pop2_bop2.
Qed.

Definition Reval_formula (e: PolEnv R) (k: Tauto.kind) (ff : Formula Rcst) :=
  let (lhs,o,rhs) := ff in Reval_op2 k o (Reval_expr e lhs) (Reval_expr e rhs).


Definition Reval_formula' :=
  eval_sformula  Rplus Rmult Rminus Ropp (@eq R) Rle Rlt N.to_nat pow R_of_Rcst.

Lemma Reval_pop2_eval_op2 : forall o e1 e2,
  Reval_pop2 o e1 e2  <->
  eval_op2 eq Rle Rlt o e1 e2.
Proof.
  destruct o ; simpl ; try tauto.
  split.
  - apply Rge_le.
  - apply Rle_ge.
Qed.

Lemma Reval_formula_compat : forall env b f, Tauto.hold b (Reval_formula env b f) <-> Reval_formula' env f.
Proof.
  intros.
  unfold Reval_formula.
  destruct f.
  unfold Reval_formula'.
  simpl.
  rewrite Reval_op2_hold.
  apply Reval_pop2_eval_op2.
Qed.

Definition QReval_expr := eval_pexpr Rplus Rmult Rminus Ropp Q2R N.to_nat pow.

Definition QReval_formula (e: PolEnv R) (k: Tauto.kind) (ff : Formula Q) :=
  let (lhs,o,rhs) := ff in Reval_op2 k o (QReval_expr e lhs) (QReval_expr e rhs).

Definition QReval_formula' :=
  RingMicromega.eval_formula  Rplus Rmult Rminus Ropp (@eq R) Rle Rlt Q2R N.to_nat pow.

Lemma QReval_formula_compat : forall env b f, Tauto.hold b (QReval_formula env b f) <-> QReval_formula' env f.
Proof.
  intros.
  unfold QReval_formula.
  destruct f.
  unfold QReval_formula'.
  rewrite Reval_op2_hold.
  apply Reval_pop2_eval_op2.
Qed.


Definition Qeval_nformula :=
  RingMicromega.eval_nformula 0 Rplus Rmult  (@eq R) Rle Rlt Q2R.

Lemma Reval_nformula_dec : forall env d, (Qeval_nformula env d) \/ ~ (Qeval_nformula env d).
Proof.
  exact (fun env d =>eval_nformula_dec Rsor Q2R env d).
Qed.


Definition RWitness := ZArithProof.

(*
Definition RWeakChecker := check_normalised_formulas 0%Q 1%Q Qplus Qmult  Qeq_bool Qle_bool.

From Stdlib Require Import List.

Lemma RWeakChecker_sound :   forall (l : list (NFormula Q)) (cm : RWitness),
  RWeakChecker l cm = true ->
  forall env, make_impl (Qeval_nformula env) l False.
Proof.
  intros l cm H.
  intro.
  unfold Qeval_nformula.
  apply (checker_nf_sound Rsor QSORaddon l cm).
  unfold RWeakChecker in H.
  exact H.
Qed.
 *)

From Stdlib.micromega Require Import Tauto.

Definition Rnormalise := @cnf_normalise Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool Qle_bool.
Definition Rnegate := @cnf_negate Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool Qle_bool.

Definition runsat := check_inconsistent 0%Q Qeq_bool Qle_bool.

Definition rdeduce := nformula_plus_nformula 0%Q Qplus Qeq_bool.

Inductive eFormula (Form :Type) :=
| IsZ (b:bool) (x:positive)
| IsF (f: Form).

Definition map_eFormula {S C :Type} (F: S -> C) (f: eFormula (Formula S)) : eFormula (Formula C) :=
  match f with
  | IsZ _ b x => IsZ _ b x
  | IsF f => IsF (map_Formula F f)
  end.

Fixpoint lcm (p: Pol Q) : Z :=
  match p with
  | Pc q => Zpos (Qden q)
  | Pinj x p => lcm p
  | PX p _ q  => Z.lcm (lcm p) (lcm q)
  end.

Fixpoint polZ (lcm:Z) (p:Pol Q) : Pol Z  :=
  match p with
  | Pc q => Pc (Z.div (Z.mul (Qnum q) lcm) (Z.pos (Qden q)))
  | Pinj x p => Pinj x (polZ lcm p)
  | PX p i q => PX (polZ lcm p) i (polZ lcm q)
  end.

Lemma xpolZ_eq : forall (p:Pol Q) a env
    (POS : (0 <= a)%Z)
    (DIV : (lcm p | a)%Z),
    Q2R (a # 1) *  (RingMicromega.eval_pol  Rplus Rmult Q2R env p) =
                       (RingMicromega.eval_pol  Rplus Rmult (MMicromega.IZR R R0 R1 Rplus Ropp) env (polZ a p)).
Proof.
  induction p.
  - simpl. intros.
    unfold Z.divide in DIV.
    destruct DIV as (z & EQ).
    subst.
    rewrite Z.mul_assoc.
    rewrite Zdiv.Z_div_mult.
    rewrite <- Q2R_mult.
    destruct c. simpl.
    destruct z.
    + simpl.
      rewrite Qmult_0_l.
      rewrite Z.mul_0_r.
      unfold Q2R. simpl.
      rewrite Rinv_1. reflexivity.
    +
      (*rewrite <- (Pos2Z.inj_mul p).  *)
      setoid_rewrite <- (Qmult_inject_Z_l (Z.pos Qden)).
      setoid_rewrite <- Qmult_assoc.
      setoid_rewrite Qreduce_den_l.
      simpl. unfold Q2R.
      rewrite IZR_eq.
      rewrite Rinv_1.
      rewrite Z.mul_comm.
      reflexivity.
    + simpl in POS.
      exfalso.
      revert POS. rewrite ZMicromega.le_neg.
      simpl.
      apply Pos2Z.pos_is_pos.
    + apply Zorder.Zgt_pos_0.
  - simpl.
    intros.
    rewrite IHp by auto. reflexivity.
  - intros.
    simpl.
    rewrite <- IHp1; try easy.
    rewrite <- IHp2; try easy.
    ring.
    + simpl in DIV.
      generalize (Z.divide_lcm_r (lcm p1) (lcm p3)).
      intros.
      eapply Z.divide_trans;eauto.
    + simpl in DIV.
      generalize (Z.divide_lcm_l (lcm p1) (lcm p3)).
      intros.
      eapply Z.divide_trans;eauto.
Qed.


Lemma lt_0_lcm : forall p,
    (0 < lcm p)%Z.
Proof.
  induction p.
  - simpl.
    destruct c ; simpl.
    apply Pos2Z.is_pos.
  - easy.
  - simpl.
    specialize (Z.lcm_nonneg (lcm p1) (lcm p3)).
    destruct (Z.eq_dec (Z.lcm (lcm p1) (lcm p3)) 0).
    apply Z.lcm_eq_0  in e.
    destruct e as [e|e]; rewrite e in *.
    apply Z.lt_irrefl  in IHp1; tauto.
    apply Z.lt_irrefl  in IHp2; tauto.
    intro H. apply Zorder.Zle_lt_or_eq in H.
    destruct H as [H | H] ;congruence.
Qed.



Lemma polZ_eq : forall (p:Pol Q) env,
    Q2R ((lcm p) # 1) *  (RingMicromega.eval_pol  Rplus Rmult Q2R env p) =
                       (RingMicromega.eval_pol  Rplus Rmult (MMicromega.IZR R R0 R1 Rplus Ropp) env (polZ (lcm p) p)).
Proof.
  intros.
  apply xpolZ_eq.
  apply Z.lt_le_incl.
  apply lt_0_lcm.
  apply Z.divide_refl.
Qed.


Definition nformulaZ (f : NFormula Q) : NFormula Z :=
  let (p,o) := f in
  (polZ (lcm p) p, o).


Lemma nformulaZ_sound : forall env f,
    Qeval_nformula env f ->
    eval_nformula R R0 R1 Rplus Rmult Ropp eq Rle Rlt env (nformulaZ f).
Proof.
  unfold Qeval_nformula.
  destruct f as (f & o).
  unfold nformulaZ.
  simpl.
  rewrite <- polZ_eq.
  assert (LCMPOS := lt_0_lcm f).
  destruct o ; simpl.
  - intros H. rewrite H.
    rewrite Rmult_0_r.
    reflexivity.
  - intro H. intro H'.
    apply H.
    apply Rmult_integral in H'.
    destruct H' as [H' | H'];[|easy].
    unfold Q2R in H'.
    unfold Qnum,Qden in H'.
    rewrite Rinv_1 in H'.
    apply eq_IZR in H'. rewrite H' in LCMPOS.
    apply Z.lt_irrefl in LCMPOS ; tauto.
  - intro H.
    replace R0 with (R0 * R0) by ring.
    apply Rmult_ge_0_gt_0_lt_compat; try easy.
    apply Rlt_gt.
    unfold Q2R. simpl. rewrite Rinv_1.
    now apply IZR_lt.
    unfold Q2R. simpl. rewrite Rinv_1.
    change R0 with (IZR 0).
    now apply IZR_lt.
  - intro H.
    replace R0 with (R0 * R0) by ring.
    apply Rmult_le_compat; try easy.
    unfold Q2R. simpl.
    rewrite Rinv_1.
    change R0 with (IZR 0).
    apply IZR_le.
    now apply Z.lt_le_incl.
Qed.


Fixpoint xcollect_isZ (s:PositiveSet.t) (acc : list (NFormula Z)) (l:list (eFormula (NFormula Q) * unit)) : PositiveSet.t * list (NFormula Z) :=
  match l with
  | nil => (s,acc)
  | cons (e,_) l => match e with
            | IsZ _ b x => xcollect_isZ (if b then (PositiveSet.add x s) else s) acc l
            | IsF f   => xcollect_isZ s (nformulaZ f :: acc) l
            end
  end.

Definition QCheck (l : list (eFormula (NFormula Q) * unit)) :=
  let (s,cl) := xcollect_isZ PositiveSet.empty nil l in
  ZChecker (Some s) cl.
  
Definition erunsat (f : eFormula (NFormula Q)) :=
  match f with
  | IsZ _ _ _ => false
  | IsF f  => runsat f
  end.

Definition erdeduce (f1 f2 : eFormula (NFormula Q)) :=
  match f1,f2 with
  | IsF f1, IsF f2  => match rdeduce f1 f2 with
                       | None => None
                       | Some f => Some (IsF f)
                       end
  | _  , _ => None
  end.

Definition map_cnf (T:Type) {A B:Type} (F : A -> B) (l : cnf A T) : cnf B T :=
  List.map (List.map (fun '(a,t) => (F a , t))) l.

Definition eRnormalise (T:Type) (f: eFormula (Formula Q)) (t:T) : cnf (eFormula (NFormula Q)) T :=
  match f with
  | IsZ _ b z => cons (cons (IsZ _ (negb b) z, t) nil)  nil
  | IsF f => map_cnf (@IsF (NFormula Q)) (Rnormalise  f t)
  end.

Definition eRnegate (T:Type) (f: eFormula (Formula Q)) (t:T) : cnf (eFormula (NFormula Q)) T :=
  match f with
  | IsZ _ b z => cons (cons (IsZ _ b z, t) nil)  nil
  | IsF f => map_cnf (@IsF (NFormula Q)) (Rnegate  f t)
  end.


Definition cnfR (Annot:Type) (TX : Tauto.kind -> Type) (AF:Type) (k:Tauto.kind)
  (f: TFormula (eFormula (Formula Q)) Annot TX AF k) :=
  rxcnf erunsat erdeduce (@eRnormalise Annot) (@eRnegate Annot) true f.

Definition RTautoChecker (f : BFormula (eFormula (Formula Rcst)) Tauto.isProp) (w: list RWitness)  : bool :=
  @tauto_checker (eFormula (Formula Q)) (eFormula (NFormula Q))
  unit erunsat erdeduce
  (@eRnormalise unit) (@eRnegate unit)
  RWitness (QCheck) (map_bformula (map_eFormula Q_of_Rcst)  f) w.

Definition Qeval_formula (e: PolEnv R) (k:kind) (ff : Formula Q) : rtyp k  :=
  let (lhs, o, rhs) := ff in Reval_op2 k o (QReval_expr e lhs) (QReval_expr e rhs).


Definition eval_eformula_k {F: Type} (eval : PolEnv R -> forall (k:kind),F -> rtyp k) (e:PolEnv R) (k:kind)  (f : eFormula F) :
  rtyp k :=
  match f with
  | IsZ _ b x => match k with
               | isProp => if b then isZ (e x) else ~ isZ (e x)
               | isBool => if b then isZb (e x) else negb (isZb (e x))
               end
  | IsF f     => eval e k f
  end.

Definition eval_eformula {F: Type} (eval : PolEnv R -> F -> Prop) (e:PolEnv R)  (f : eFormula F) : Prop :=
  match f with
  | IsZ _ b x => if b then isZ (e x) else ~ isZ (e x)
  | IsF f     => eval e f
  end.


Lemma  eval_eformula_morph : forall {F: Type} (eval1: PolEnv R -> forall (k:kind),F -> rtyp k)
                                    (eval2 : PolEnv R -> F -> Prop),
  (forall e k f, hold k (eval1 e k f ) <->  (eval2 e f)) ->
  forall e k f,
    hold k (eval_eformula_k eval1 e k f) <-> (eval_eformula eval2 e f).
Proof.
  destruct f; simpl.
  - destruct k; simpl. tauto.
    destruct b ;
      rewrite isZ_isZb. unfold is_true.
    tauto.
    unfold is_true. rewrite eq_true_not_negb_iff.
    tauto.
  -  apply H.
Qed.



Definition eQeval_formula (e : PolEnv R) (k:kind) (ff:eFormula (Formula Q)) : rtyp k :=
  eval_eformula_k  Qeval_formula e k ff.

Definition eQeval_nformula (e : PolEnv R)  (ff:eFormula (NFormula Q)) : Prop :=
  eval_eformula  Qeval_nformula e ff.


Lemma eval_eformula_dec : forall (T: Type) eval env (ff: eFormula T),
  (forall f, eval env f \/ ~ eval env f) ->
    eval_eformula eval env ff \/  ~ eval_eformula eval env ff.
Proof.
  intros.  destruct ff; simpl; auto.
  - destruct b;
      rewrite isZ_isZb;destruct (isZb (env x)); intuition congruence.
Qed.



Definition eReval_formula (e : PolEnv R) (k:kind) (ff:eFormula (Formula Rcst)) : rtyp k :=
  eval_eformula_k Reval_formula e k ff.


(*Definition eZeval_nformula (e : PolEnv R) (k:kind) (ff:eFormula (NFormula Z)) : rtyp k :=
  match ff with
  | IsZ _ x => match k with
               | isProp => isZ (e x)
               | isBool => isZb (e x)
               end
  | IsF f     => Qeval_nformula e k f
  end.
*)

Lemma eval_eformula_map_eFormula : forall env  a,
  eval_eformula QReval_formula' env (map_eFormula Q_of_Rcst a) <-> eval_eformula Reval_formula' env a.
Proof.
  destruct a; simpl.
  - tauto.
  - unfold QReval_formula'.
    rewrite <- eval_formulaSC with (phiS := R_of_Rcst).
    + tauto.
    + intro. now rewrite Q_of_RcstR.
Qed.

Lemma eval_cnf_map_cnf : forall (A:Type) eval env f,
    eval_cnf (Annot:=A) (eval_eformula eval) env (map_cnf (IsF (Form:=NFormula Q)) f) <->
      eval_cnf (Annot:=A) eval env f.
Proof.
  intros.
  unfold map_cnf.
  unfold eval_cnf.
  induction f.
  - simpl. tauto.
  -
    rewrite List.map_cons.
    rewrite ! make_conj_cons.
    rewrite IHf.
    assert (eval_clause (eval_eformula eval) env (ListDef.map (fun '(a0, t) => (IsF a0, t)) a)
            <-> eval_clause eval env a).
    { clear IHf.
      unfold eval_clause.
      induction a.
      - tauto.
      - rewrite List.map_cons.
        rewrite ! make_conj_cons.
        tauto.
    }
    tauto.
Qed.

Lemma xcollect_isZ_nformulaZ : forall cl s cz s' cz',
    xcollect_isZ s cz cl = (s', cz') ->
    forall f, List.In f cz' -> List.In f cz \/ exists f', List.In (IsF f',tt) cl /\ f = nformulaZ f'.
Proof.
  induction cl.
  - simpl. intros. inv H.
    tauto.
  - simpl. destruct a. destruct e.
    + intros.
      apply IHcl with (f:=f) in H;try easy.
      destruct H; [tauto|].
      destruct H as (f' & IN & EQ).
      right. exists f'.
      tauto.
    + intros.
      apply IHcl with (f:=f0) in H;try easy.
      destruct H.
      destruct H.
      * right.
        exists f.
        destruct u.
        split. tauto. congruence.
      * tauto.
      * destruct H as (f' & IN & EQ).
        right. exists f'. split;auto.
Qed.


Lemma collect_isZ_nformulaZ : forall cl  s' cz',
    xcollect_isZ PositiveSet.empty nil cl = (s', cz') ->
    forall f, List.In f cz' -> exists f', List.In (IsF f',tt) cl /\ f = nformulaZ f'.
Proof.
  intros.
  apply xcollect_isZ_nformulaZ with (f:=f) in H; try easy.
  simpl in H. tauto.
Qed.



Lemma xcollect_isZ_sound : forall cl s cz s' cz',
    xcollect_isZ s cz cl = (s', cz') ->
    forall x, PositiveSet.mem x s' = true ->
              PositiveSet.mem x s = true \/  List.In (IsZ _ true x,tt) cl.
Proof.
  induction cl.
  - simpl. intros. inv H. tauto.
  - simpl. destruct a. destruct e.
    + intros.
      apply IHcl with (x:= x0) in H;try easy.
      destruct H.
      destruct b.
      rewrite PositiveSetAddon.mem_add in H.
      destruct (Pos.eq_dec x0 x).
      subst.
      right. destruct u. tauto.
      tauto.
      tauto.
      tauto.
    + intros.
      apply IHcl with (x:=x) in H; tauto.
Qed.

Lemma collect_isZ_sound : forall cl s' cz',
    xcollect_isZ PositiveSet.empty nil cl = (s', cz') ->
    forall x, PositiveSet.mem x s' = true -> List.In (IsZ _ true x,tt) cl.
Proof.
  intros.
  eapply xcollect_isZ_sound with (x:=x) in H; try assumption.
  destruct H; [discriminate| assumption].
Qed.


Lemma RTautoChecker_sound : forall f w, RTautoChecker f w = true -> forall env, eval_bf  (eReval_formula env)  f.
Proof.
  intros f w.
  unfold RTautoChecker.
  intros TC env.
  eapply tauto_checker_sound with (eval:=eQeval_formula) (eval':=    eQeval_nformula) (env := env) in TC.
  - change (eval_f e_rtyp (eQeval_formula env))
      with
      (eval_bf  (eQeval_formula env)) in TC.
    rewrite eval_bf_map in TC.
    unfold eval_bf in TC.
    rewrite eval_f_morph with (ev':= eReval_formula env) in TC ; auto.
    intros.
    apply Tauto.hold_eiff.
    unfold eQeval_formula.
    rewrite eval_eformula_morph
      with (eval2 := QReval_formula') by apply QReval_formula_compat.
    unfold eReval_formula.
    rewrite eval_eformula_morph
      with (eval2 := Reval_formula') by apply Reval_formula_compat.
    apply eval_eformula_map_eFormula.
  -
    intros.
    apply eval_eformula_dec.
    apply Reval_nformula_dec.
  - destruct t as [|t]; try discriminate.
    simpl. destruct t.
    apply (check_inconsistent_sound Rsor QSORaddon) ; auto.
  - destruct t as [|t]; try discriminate.
    unfold erdeduce.
    intros. revert H.
    destruct t' ; try discriminate.
    simpl in H0,H1.
    destruct (rdeduce t f0) eqn:EQ;try discriminate.
    intro. inv H. revert EQ.
    eapply (nformula_plus_nformula_correct Rsor QSORaddon); eauto.
  - intros.
    unfold eQeval_formula.
    rewrite eval_eformula_morph by apply QReval_formula_compat.
    destruct t as [| t]; simpl in H; simpl.
    + rewrite <- eval_cnf_cons_iff in H.
      simpl in H.
      unfold eval_tt in H. simpl in H.
      destruct H.
      destruct b0; simpl in H;
      generalize (isZ_dec (env0 x)); tauto.
    + unfold eQeval_nformula in H.
      rewrite eval_cnf_map_cnf in H.
      eapply (cnf_normalise_correct Rsor QSORaddon) ; eauto.
  - intros. rewrite Tauto.hold_eNOT.
    destruct t as [| t]; simpl in H; simpl.
    + rewrite <- eval_cnf_cons_iff in H.
      simpl in H.
      unfold eval_tt in H. simpl in H.
      destruct b,b0; simpl in H; simpl; try tauto;
      rewrite isZ_isZb in H;unfold is_true.
      tauto.
      destruct (isZb (env0 x)); simpl; intuition congruence.
    + unfold eQeval_nformula in H.
      rewrite eval_cnf_map_cnf in H.
      rewrite QReval_formula_compat.
      now eapply (cnf_negate_correct Rsor QSORaddon); eauto.
  - intros t w0.
    unfold eval_tt.
    intros.
    rewrite make_impl_map with (eval := eQeval_nformula env0).
    + unfold QCheck in H.
      destruct (xcollect_isZ PositiveSet.empty nil t) as (s,cl) eqn:COLLECT.
      rewrite <- make_conj_impl.
      intro CONJ.
      apply ZChecker_sound with (1:=Rsor) (2:= ZSORaddon) (env:=env0) in H.
      rewrite <- make_conj_impl in H.
      apply H;clear H.
      * apply make_conj_in_rev.
        intros p IN.
        apply collect_isZ_nformulaZ with (f:=p) in COLLECT.
        destruct COLLECT as (p' & IN' & EQ).
        subst. apply make_conj_in with (p:= IsF p') in CONJ.
        simpl in CONJ.
        apply nformulaZ_sound;auto.
        rewrite List.in_map_iff.
        exists (IsF p',tt).
        simpl. split;auto. auto.
      * unfold isZenv.
        intros. simpl in H0.
        apply collect_isZ_sound with (x:=x) in COLLECT; auto.
        apply make_conj_in with (p:= (IsZ _ true x)) in CONJ.
        simpl in CONJ.
        now apply isZ_eq.
        rewrite List.in_map_iff.
        exists (IsZ _  true x, tt).
        split ;auto.
    + tauto.
Qed.

Register eFormula as micromega.eFormula.type.
Register IsZ      as micromega.eFormula.IsZ.
Register IsF      as micromega.eFormula.IsF.


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)

#[deprecated(since="9.0")]
Notation to_nat := N.to_nat.
