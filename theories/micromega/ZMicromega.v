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
(*  Frédéric Besson (Irisa/Inria) 2006-2011                             *)
(*                                                                      *)
(************************************************************************)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import OrderedRing.
From Stdlib Require Import RingMicromega.
From Stdlib Require Import MMicromega.
From Stdlib Require Import ZCoeff.
From Stdlib Require Import Refl.
From Stdlib Require Import BinInt.
From Stdlib Require InitialRing.
From Stdlib.micromega Require Import Tauto.
Local Open Scope Z_scope.
Set Implicit Arguments.


Ltac flatten_bool :=
  repeat match goal with
           [ id : (_ && _)%bool = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
         |  [ id : (_ || _)%bool = true |- _ ] =>  destruct (orb_prop _ _ id); clear id
         end.

Ltac inv H := inversion H ; try subst ; clear H.

Lemma eq_le_iff : forall x, 0 = x  <-> (0 <= x /\ x <= 0).
Proof.
  intros.
  split ; intros H.
  - subst.
    split; reflexivity.
  - destruct H.
    apply Z.le_antisymm; auto.
Qed.

Lemma lt_le_iff x : 0 < x <-> 0 <= x - 1.
Proof. rewrite <-Z.lt_succ_r, Z.sub_1_r, Z.succ_pred; reflexivity. Qed.

Lemma le_0_iff x y : x <= y <-> 0 <= y - x.
Proof. symmetry. apply Z.le_0_sub. Qed.

Lemma le_neg x : ((0 <= x) -> False) <-> 0 < -x.
Proof. setoid_rewrite Z.nle_gt. rewrite Z.opp_pos_neg. reflexivity. Qed.

Lemma eq_cnf x : (0 <= x - 1 -> False) /\ (0 <= -1 - x -> False) <-> x = 0.
Proof.
  rewrite (Z.sub_opp_l 1).
  setoid_rewrite <-lt_le_iff.
  rewrite Z.opp_pos_neg.
  setoid_rewrite Z.nlt_ge.
  split; intros.
  { apply Z.le_antisymm; try apply H. }
  { subst x. split; reflexivity. }
Qed.

Lemma IPR_eq : forall p,  IPR Z 1 Z.add p = Z.pos p.
Proof.
  induction p; simpl;auto.
  - rewrite IHp. rewrite Pos2Z.add_pos_pos.
    now rewrite Pos.add_diag.
  - rewrite IHp. rewrite Pos2Z.add_pos_pos.
    now rewrite Pos.add_diag.
Qed.

Lemma IZR_eq : forall c, IZR Z 0 1 Z.add Z.opp c = c.
Proof.
  destruct c; simpl;auto.
  - now rewrite IPR_eq.
  - now rewrite IPR_eq.
Qed.



Lemma ZSORaddon :
  SORaddon 0 1 Z.add Z.mul Z.sub Z.opp eq Z.le 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb Z.leb (IZR Z 0 1 Z.add Z.opp) (fun x => x) (Ring_theory.pow_N 1 Z.mul).
Proof.
(*  destruct ZSORaddon;*)  constructor;try assumption.
  - constructor;
    intros;  rewrite !IZR_eq; auto.
    now apply Z.eqb_eq.
  - constructor;intros; auto.
  - intros. rewrite !IZR_eq; auto.
    now apply Z.eqb_neq.
  - intros. rewrite !IZR_eq; auto.
    now apply Zbool.Zle_bool_imp_le.
Qed.

  
From Stdlib Require Import EnvRing.


Fixpoint Zeval_expr (env : PolEnv Z) (e: PExpr Z) : Z :=
  match e with
    | PEc c => c
    | PEX x => env x
    | PEadd e1 e2 => Zeval_expr env e1 + Zeval_expr env e2
    | PEmul e1 e2 => Zeval_expr env e1 * Zeval_expr env e2
    | PEpow e1 n  => Z.pow (Zeval_expr env e1) (Z.of_N n)
    | PEsub e1 e2 => (Zeval_expr env e1) - (Zeval_expr env e2)
    | PEopp e   => Z.opp (Zeval_expr env e)
  end.

Strategy expand [ Zeval_expr ].

Definition eval_expr := eval_pexpr  Z.add Z.mul Z.sub Z.opp (IZR Z 0 1 Z.add Z.opp) (fun x => x) (pow_N 1 Z.mul).

Fixpoint Zeval_const  (e: PExpr Z) : option Z :=
  match e with
  | PEc c => Some c
  | PEX x => None
  | PEadd e1 e2 => map_option2 (fun x y => Some (x + y))
                               (Zeval_const e1) (Zeval_const e2)
  | PEmul e1 e2 => map_option2 (fun x y => Some (x * y))
                               (Zeval_const e1) (Zeval_const e2)
  | PEpow e1 n  => map_option (fun x => Some (Z.pow x (Z.of_N n)))
                                 (Zeval_const e1)
  | PEsub e1 e2 => map_option2 (fun x y => Some (x - y))
                               (Zeval_const e1)  (Zeval_const e2)
  | PEopp e   => map_option (fun x => Some (Z.opp x)) (Zeval_const e)
  end.

Lemma ZNpower : forall r n, r ^ Z.of_N n = pow_N 1 Z.mul r n.
Proof.
  intros r n; destruct n as [|p].
  - reflexivity.
  - simpl.
    unfold Z.pow_pos.
    rewrite <-Z.mul_1_l.
    generalize 1.
    induction p as [p IHp|p IHp|]; simpl; intros ;
      rewrite ?IHp, ?Z.mul_assoc; auto using Z.mul_comm, f_equal2.
Qed.


Lemma Zeval_expr_compat : forall env e, Zeval_expr env e = eval_expr env e.
Proof.
  intros env e; induction e ; simpl ; try congruence.
  - now rewrite IZR_eq.
  - reflexivity.
  - rewrite ZNpower. congruence.
Qed.

Definition Zeval_pop2 (o : Op2) : Z -> Z -> Prop :=
match o with
| OpEq =>  @eq Z
| OpNEq => fun x y  => ~ x = y
| OpLe => Z.le
| OpGe => Z.ge
| OpLt => Z.lt
| OpGt => Z.gt
end.


Definition Zeval_bop2 (o : Op2) : Z -> Z -> bool :=
match o with
| OpEq =>  Z.eqb
| OpNEq => fun x y => negb (Z.eqb x y)
| OpLe => Z.leb
| OpGe => Z.geb
| OpLt => Z.ltb
| OpGt => Z.gtb
end.

Lemma pop2_bop2 :
  forall (op : Op2) (q1 q2 : Z), is_true (Zeval_bop2 op q1 q2) <-> Zeval_pop2 op q1 q2.
Proof.
  unfold is_true.
  intro op; destruct op ; simpl; intros q1 q2.
  - apply Z.eqb_eq.
  - rewrite <- Z.eqb_eq.
    rewrite negb_true_iff.
    destruct (q1 =? q2) ; intuition congruence.
  - apply Z.leb_le.
  - rewrite Z.geb_le. rewrite Z.ge_le_iff. tauto.
  - apply Z.ltb_lt.
  - rewrite <- Z.gtb_gt; tauto.
Qed.

Definition Zeval_op2 (k: Tauto.kind) :  Op2 ->  Z -> Z -> Tauto.rtyp k:=
  if k as k0 return (Op2 -> Z -> Z -> Tauto.rtyp k0)
  then Zeval_pop2 else Zeval_bop2.


Lemma Zeval_op2_hold : forall k op q1 q2,
    Tauto.hold k (Zeval_op2 k op q1 q2) <-> Zeval_pop2 op q1 q2.
Proof.
  intro k; destruct k.
  - simpl ; tauto.
  - simpl. apply pop2_bop2.
Qed.


Definition Zeval_formula (env : PolEnv Z) (k: Tauto.kind) (f : Formula Z):=
  let (lhs, op, rhs) := f in
    (Zeval_op2 k op) (Zeval_expr env lhs) (Zeval_expr env rhs).

Definition Zeval_formula' :=
  @MMicromega.eval_formula Z 0 1 Z.add Z.mul Z.sub Z.opp (@eq Z) Z.le Z.lt  N (fun x => x) (pow_N 1 Z.mul).

Lemma Zeval_formula_compat : forall env k f, Tauto.hold k (Zeval_formula env k f) <-> Zeval_formula env Tauto.isProp f.
Proof.
  intros env k; destruct k ; simpl.
  - tauto.
  - intros f; destruct f ; simpl.
    rewrite <- (Zeval_op2_hold Tauto.isBool).
    simpl. tauto.
Qed.

Lemma Zeval_formula_compat' : forall env f,  Zeval_formula env Tauto.isProp f <-> Zeval_formula' env f.
Proof.
  intros env f.
  unfold Zeval_formula.
  destruct f as [Flhs  Fop Frhs].
  repeat rewrite Zeval_expr_compat.
  unfold Zeval_formula' ; simpl.
  unfold eval_expr.
  generalize (eval_pexpr Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
        (fun x : N => x) (pow_N 1 Z.mul) env Flhs).
  generalize ((eval_pexpr Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
        (fun x : N => x) (pow_N 1 Z.mul) env Frhs)).
  destruct Fop ; simpl; intros;
    intuition auto using Z.le_ge, Z.ge_le, Z.lt_gt, Z.gt_lt.
Qed.

Definition eval_nformula :=
  eval_nformula Z 0 1 Z.add Z.mul Z.opp (@eq Z) Z.le Z.lt.

Definition Zeval_op1 (o : Op1) : Z -> Prop :=
match o with
| Equal => fun x : Z => x = 0
| NonEqual => fun x : Z => x <> 0
| Strict => fun x : Z => 0 < x
| NonStrict => fun x : Z => 0 <= x
end.


Lemma Zeval_nformula_dec : forall env d, (eval_nformula env d) \/ ~ (eval_nformula env d).
Proof.
  intros.
  apply (eval_nformula_dec Zsor).
Qed.

Definition ZWitness := Psatz Z.

Definition ZWeakChecker := check_normalised_formulas 0 1 Z.add Z.mul Z.eqb Z.leb.

Lemma ZWeakChecker_sound :   forall (l : list (NFormula Z)) (cm : ZWitness),
  ZWeakChecker l cm = true ->
  forall env, make_impl (eval_nformula env) l False.
Proof.
  intros l cm H.
  intro.
  unfold eval_nformula.
  apply (checker_nf_sound Zsor ZSORaddon l cm).
  unfold ZWeakChecker in H.
  exact H.
Qed.
(*
Definition psub  := psub Z0  Z.add Z.sub Z.opp Z.eqb.
Declare Equivalent Keys psub RingMicromega.psub.

Definition popp  := popp Z.opp.
Declare Equivalent Keys popp RingMicromega.popp.

Definition padd  := padd Z0  Z.add Z.eqb.
Declare Equivalent Keys padd RingMicromega.padd.

Definition pmul := pmul 0 1 Z.add Z.mul Z.eqb.
 *)
Definition normZ  := RingMicromega.norm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb.
Declare Equivalent Keys normZ RingMicromega.norm.
(*
Definition eval_pol := eval_pol Z.add Z.mul (fun x => x).
Declare Equivalent Keys eval_pol RingMicromega.eval_pol.

Lemma eval_pol_sub : forall env lhs rhs, eval_pol env (psub  lhs rhs) = eval_pol env lhs - eval_pol env rhs.
Proof.
  intros.
  apply (eval_pol_sub Zsor ZSORaddon).
Qed.

Lemma eval_pol_add : forall env lhs rhs, eval_pol env (padd  lhs rhs) = eval_pol env lhs + eval_pol env rhs.
Proof.
  intros.
  apply (eval_pol_add Zsor ZSORaddon).
Qed.

Lemma eval_pol_mul : forall env lhs rhs, eval_pol env (pmul  lhs rhs) = eval_pol env lhs * eval_pol env rhs.
Proof.
  intros.
  apply (eval_pol_mul Zsor ZSORaddon).
Qed.


Lemma eval_pol_norm : forall env e, eval_expr env e = eval_pol env (normZ e) .
Proof.
  intros.
  apply (eval_pol_norm Zsor ZSORaddon).
Qed.

Definition Zunsat := check_inconsistent 0  Z.eqb Z.leb.

 *)

(*Lemma Zunsat_sound : forall f,
    Zunsat f = true -> forall env, eval_nformula env f -> False.
Proof.
  unfold Zunsat.
  intros f H env ?.
  destruct f.
  eapply check_inconsistent_sound with (1 := Zsor) (2 := ZSORaddon) in H; eauto.
Qed.
*)


(*Definition xnnormalise (t : Formula Z) : NFormula Z :=
  let (lhs,o,rhs) := t in
  let lhs := normZ lhs in
  let rhs := normZ rhs in
  match o with
  | OpEq  => (psub rhs lhs,  Equal)
  | OpNEq => (psub rhs lhs,  NonEqual)
  | OpGt  => (psub lhs rhs,  Strict)
  | OpLt  => (psub rhs lhs,  Strict)
  | OpGe  => (psub lhs rhs,  NonStrict)
  | OpLe =>  (psub rhs lhs,  NonStrict)
  end.

Lemma xnnormalise_correct :
  forall env f,
    eval_nformula env (xnnormalise f) <-> Zeval_formula env Tauto.isProp f.
Proof.
  intros env f.
  rewrite Zeval_formula_compat'.
  unfold xnnormalise.
  destruct f as [lhs o rhs].
  destruct o eqn:O ; cbn ; rewrite ?eval_pol_sub;
    rewrite <- !eval_pol_norm ; simpl in *;
      unfold eval_expr;
      generalize (   eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
                                 (fun x : N => x) (pow_N 1 Z.mul) env lhs);
      generalize (eval_pexpr  Z.add Z.mul Z.sub Z.opp (fun x : Z => x)
                              (fun x : N => x) (pow_N 1 Z.mul) env rhs); intros z z0.
  - split ; intros.
    + assert (z0 + (z - z0) = z0 + 0) as H0 by congruence.
      rewrite Z.add_0_r in H0.
      rewrite <- H0.
      rewrite Z.add_sub_assoc, Z.add_comm, <-Z.add_sub_assoc, Z.sub_diag; apply Z.add_0_r.
    + subst.
      apply Z.sub_diag.
  - split ; intros H H0.
    + subst. apply H. apply Z.sub_diag.
    + apply H.
      assert (z0 + (z - z0) = z0 + 0) as H1 by congruence.
      rewrite Z.add_0_r in H1.
      rewrite <- H1.
      rewrite Z.add_sub_assoc, Z.add_comm, <-Z.add_sub_assoc, Z.sub_diag; apply Z.add_0_r.
  - symmetry. apply le_0_iff.
  - symmetry. apply le_0_iff.
  - apply Z.lt_0_sub.
  - apply Z.lt_0_sub.
Qed.
 *)
(*
Definition xnormalise (f: NFormula Z) : list (NFormula Z) :=
  let (e,o) := f in
  match o with
  | Equal     => (psub e (Pc 1),NonStrict) :: (psub (Pc (-1)) e, NonStrict) :: nil
  | NonStrict =>  ((psub (Pc (-1)) e,NonStrict)::nil)
  | Strict    =>  ((psub (Pc 0)) e, NonStrict)::nil
  | NonEqual  =>  (e, Equal)::nil
  end.

(*Lemma eval_pol_Pc : forall env z,
    eval_pol env (Pc z) = z.
Proof.
  reflexivity.
Qed.
 *)

Lemma xnormalise_correct : forall env f,
    (make_conj (fun x => eval_nformula env x -> False) (xnormalise f)) <-> eval_nformula env f.
Proof.
  intros env f.
  destruct f as [e o]; destruct o eqn:Op; cbn - [psub];
    repeat rewrite eval_pol_sub; fold eval_pol; repeat rewrite eval_pol_Pc;
      generalize (eval_pol env e) as x; intro.
  - apply eq_cnf.
  - unfold not. tauto.
  - rewrite le_neg. rewrite (Z.sub_0_l x), Z.opp_involutive; reflexivity.
  - rewrite le_neg, lt_le_iff.
    rewrite Z.sub_opp_l, Z.sub_sub_distr. reflexivity.
Qed.
*)


From Stdlib.micromega Require Import Tauto.
From Stdlib Require Import BinNums.

Definition cnf_of_list {T: Type} (tg : T) (l : list (NFormula Z)) :=
  List.fold_right (fun x acc =>
                     if Zunsat x then acc else ((x,tg)::nil)::acc)
                  (cnf_tt _ _)  l.

Lemma cnf_of_list_correct :
  forall {T : Type} (tg:T)  (f : list (NFormula Z)) env,
  eval_cnf eval_nformula env (cnf_of_list tg f) <->
  make_conj (fun x : NFormula Z => eval_nformula env x -> False) f.
Proof.
  unfold cnf_of_list.
  intros T tg f env.
  set (F := (fun (x : NFormula Z) (acc : list (list (NFormula Z * T))) =>
        if Zunsat x then acc else ((x, tg) :: nil) :: acc)).
  set (E := ((fun x : NFormula Z => eval_nformula env x -> False))).
  induction f as [|a f IHf].
  - compute.
    tauto.
  - rewrite make_conj_cons.
    simpl.
    unfold F at 1.
    destruct (Zunsat a) eqn:EQ.
    + rewrite IHf.
      assert (eval_nformula env a -> False).
      { now eapply Zunsat_sound with (1:= Zsor) (2:=ZSORaddon).  }
      unfold E at 2.
      tauto.
    +
      rewrite <- eval_cnf_cons_iff.
      rewrite IHf.
      simpl.
      unfold E at 2.
      unfold eval_tt. simpl.
      tauto.
Qed.


(** If all the variables range over the integers,
    we can turn a [e > 0] constraint into [e - 1 >= 0] *)

Definition xnormalise (f: NFormula Z) : list (NFormula Z) :=
  let (e,o) := f in
  match o with
  | Equal     => (psub e (Pc 1),NonStrict) :: (psub (Pc (-1)) e, NonStrict) :: nil
  | NonStrict =>  ((psub (Pc (-1)) e,NonStrict)::nil)
  | Strict    =>  ((psub (Pc 0)) e, NonStrict)::nil
  | NonEqual  =>  (e, Equal)::nil
  end.

Lemma xnormalise_correct : forall env f,
    (make_conj (fun x => Zeval_nformula env x -> False) (xnormalise f)) <-> Zeval_nformula env f.
Proof.
  intros env f.
  destruct f as [e o]; destruct o eqn:Op; cbn - [psub];
    repeat rewrite Zeval_pol_sub; fold Zeval_pol; repeat rewrite Zeval_pol_Pc;
      generalize (Zeval_pol env e) as x; intro.
  -
    apply eq_cnf.
  - unfold not. tauto.
  - rewrite le_neg. rewrite (Z.sub_0_l x), Z.opp_involutive; reflexivity.
  - rewrite le_neg, lt_le_iff.
    rewrite Z.sub_opp_l, Z.sub_sub_distr. reflexivity.
Qed.

Definition normalise {T : Type} (t:Formula Z) (tg:T) : cnf (NFormula Z) T :=
  let f := xnnormalise t in
  if Zunsat f then cnf_ff _ _
  else cnf_of_list tg (xnormalise f).

Lemma eval_pol_eq : forall p env,
  (RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x) env p) =
    (RingMicromega.eval_pol Z.add Z.mul (IZR Z 0 1 Z.add Z.opp) env p).
Proof.
  induction p; simpl; intros.
  - now rewrite IZR_eq.
  - now rewrite IHp.
  - now rewrite IHp1,IHp2.
Qed.

Lemma eval_nformula_compat : forall env f,
    eval_nformula env f = Zeval_nformula env f.
Proof.
  unfold eval_nformula,Zeval_nformula.
  unfold MMicromega.eval_nformula.
  destruct f; simpl.
  rewrite eval_pol_eq.
  reflexivity.
Qed.

Lemma normalise_correct : forall (T: Type) env t (tg:T), eval_cnf eval_nformula env (normalise t tg) <-> Zeval_formula env Tauto.isProp t.
Proof.
  intros T env t tg.
  rewrite Zeval_formula_compat'.
  unfold Zeval_formula'.
  rewrite <- xnnormalise_correct with (1:= Zsor) (2:=ZSORaddon).
  unfold normalise.
  generalize (xnnormalise t) as f;intro f.
  destruct (Zunsat f) eqn:U.
  -
    assert (eval_nformula env f -> False).
    { now eapply Zunsat_sound with (1:= Zsor) (2:=ZSORaddon).  }
    rewrite eval_cnf_ff.
    tauto.
  - rewrite cnf_of_list_correct.
    fold eval_nformula.
    rewrite eval_nformula_compat.
    rewrite <- xnormalise_correct.
    induction (xnormalise f).
    + simpl. tauto.
    + rewrite ! make_conj_cons.
      rewrite IHl.
      rewrite eval_nformula_compat.
      tauto.
Qed.


Definition xnegate (f:NFormula Z) : list (NFormula Z)  :=
  let (e,o) := f in
    match o with
      | Equal  => (e,Equal) :: nil
      | NonEqual => (psub e (Pc 1),NonStrict) :: (psub (Pc (-1)) e, NonStrict) :: nil
      | NonStrict => (e,NonStrict)::nil
      | Strict    => (psub e (Pc 1),NonStrict)::nil
    end.

Definition negate {T : Type} (t:Formula Z) (tg:T) : cnf (NFormula Z) T :=
  let f := xnnormalise t in
  if Zunsat f then cnf_tt _ _
  else cnf_of_list tg (xnegate f).

Lemma xnegate_correct : forall env f,
    (make_conj (fun x => eval_nformula env x -> False) (xnegate f)) <-> ~ eval_nformula env f.
Proof.
  intros env f.
  destruct f as [e o]; destruct o eqn:Op;cbn - [psub];
  rewrite <- !eval_pol_eq;
  repeat rewrite Zeval_pol_sub; fold Zeval_pol; repeat rewrite Zeval_pol_Pc;
      generalize (Zeval_pol env e) as x; intro.
  - tauto.
  - rewrite eq_cnf.
    destruct (Z.eq_decidable x 0);tauto.
  - rewrite lt_le_iff.
    tauto.
  - tauto.
Qed.

Lemma negate_correct : forall T env t (tg:T), eval_cnf eval_nformula env (negate t tg) <-> ~ Zeval_formula env Tauto.isProp t.
Proof.
  intros T env t tg.
  rewrite Zeval_formula_compat'.
  unfold Zeval_formula'.
  rewrite <- xnnormalise_correct with (1:=Zsor) (2:=ZSORaddon).
  unfold negate.
  generalize (xnnormalise t) as f;intro f.
  destruct (Zunsat f) eqn:U.
  - rewrite eval_cnf_tt.
    split;auto.
    intro. unfold not.
    now apply Zunsat_sound with (1:=Zsor) (2:=ZSORaddon).
  - rewrite cnf_of_list_correct.
    apply xnegate_correct.
Qed.

Definition cnfZ (Annot: Type) (TX : Tauto.kind -> Type)  (AF : Type) (k: Tauto.kind) (f : TFormula (Formula Z) Annot TX AF k) :=
  rxcnf Zunsat Zdeduce normalise negate true f.

Definition ZTautoChecker  (f : BFormula (Formula Z) Tauto.isProp) (w: list ZArithProof): bool :=
  @tauto_checker (Formula Z) (NFormula Z) unit Zunsat Zdeduce normalise negate  ZArithProof (fun cl => ZChecker None (List.map fst cl)) f w.

Lemma isZenv_None : forall env,
    isZenv Z 0 1 Z.add Z.opp eq None env.
Proof.
  intro.
  unfold isZenv.
  intros.
  exists (env x).
  rewrite IZR_eq. reflexivity.
Qed.


Lemma ZTautoChecker_sound : forall f w, ZTautoChecker f w = true -> forall env, eval_bf  (Zeval_formula env)  f.
Proof.
  intros f w.
  unfold ZTautoChecker.
  apply (tauto_checker_sound _ _ _ _ eval_nformula).
  - apply Zeval_nformula_dec.
  - intros t ? env.
  unfold eval_nformula. unfold RingMicromega.eval_nformula.
  destruct t.
  apply (check_inconsistent_sound Zsor ZSORaddon) ; auto.
  - unfold Zdeduce. intros ? ? ? H **. revert H.
     apply (nformula_plus_nformula_correct Zsor ZSORaddon); auto.
  -
    intros ? ? ? ? H.
    rewrite normalise_correct  in H.
    rewrite Zeval_formula_compat; auto.
  -
    intros ? ? ? ? H.
    rewrite negate_correct in H ; auto.
    rewrite Tauto.hold_eNOT.
    rewrite Zeval_formula_compat; auto.
  - intros t w0.
    unfold eval_tt.
    intros H env.
    rewrite (make_impl_map (eval_nformula env)).
    + eapply ZChecker_sound with (1:=Zsor) (2:=ZSORaddon); eauto.
      apply isZenv_None.
    + tauto.
Qed.
