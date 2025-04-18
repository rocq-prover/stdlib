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
(*  Frédéric Besson (Irisa/Inria) 2006-2025                             *)
(*                                                                      *)
(************************************************************************)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Ring OrderedRing.
From Stdlib Require Import RingMicromega.
From Stdlib Require Import Relation_Definitions.
From Stdlib Require Import Setoid.
From Stdlib Require Import Refl.
From Stdlib Require Import BinInt.
From Stdlib Require InitialRing.
From Stdlib Require Import EnvRing.
From Stdlib Require Import micromega.Tauto.
From Stdlib Require Import MSets.MSetPositive.
From Stdlib Require Import Zdiv Znumtheory.
From Stdlib Require Import PeanoNat Wf_nat.
From Stdlib Require Import ZArithRing.

Local Open Scope Z_scope.

Module PositiveSetAddon.

  Lemma mem_add : forall s y x,
      PositiveSet.mem x (PositiveSet.add y s) =
        if Pos.eq_dec x y then true
        else PositiveSet.mem x s.
  Proof.
    intros.
    specialize (PositiveSet.mem_spec (PositiveSet.add y s) x).
    specialize (PositiveSet.mem_spec s x).
    rewrite PositiveSet.add_spec.
    destruct (Pos.eq_dec x y).
    - tauto.
    - destruct (PositiveSet.mem x s);
        destruct (PositiveSet.mem x (PositiveSet.add y s));
        intuition congruence.
  Qed.

End PositiveSetAddon.
Import PositiveSetAddon.

(** We consider mixed problems where a subset of the variables have integral values i.e. range over Z.
    The polynomials have coefficients over Z but evaluate over a domain R.
    In ZMicromega.v, we have R = Z and we get lia,lra.
    In RMicromega.v, we have R = R (the reals) and we get lra, nra.
 *)

Ltac flatten_bool :=
  repeat match goal with
      [ id : (_ && _)%bool = true |- _ ] =>  destruct (andb_prop _ _ id); clear id
    |  [ id : (_ || _)%bool = true |- _ ] =>  destruct (orb_prop _ _ id); clear id
    end.

Ltac inv H := inversion H ; try subst ; clear H.

Section S.
  Variables R : Type.
  Variables rO rI : R.
  Variables rplus rtimes rminus: R -> R -> R.
  Variable ropp : R -> R.
  Variables req rle rlt : R -> R -> Prop.

  Variable Rsor : SOR rO rI rplus rtimes rminus ropp req rle rlt.

  (** Injection from Z and N towards R. *)

  Fixpoint IPR (p:positive) : R :=
    match p with
    | (p0~1)%positive => rplus rI  (rplus (IPR p0) (IPR p0))
    | (p0~0)%positive => rplus (IPR p0) (IPR p0)
    | 1%positive => rI
    end.

  Definition IZR (z:Z) : R :=
    match z with
    | Z0 => rO
    | Zpos p => IPR p
    | Zneg p => ropp (IPR p)
    end.

  Definition INR (n:N) : R :=
    match n with
    | N0 => rO
    | Npos p => IPR p
    end.

  Variable E : Type.

  Variable pow_phi : N -> E.

  Variable rpow : R -> E -> R.

  Variable RSORaddon :
    SORaddon rO rI rplus rtimes rminus ropp  req rle (* ring elements *)
      0%Z 1%Z Z.add Z.mul Z.sub Z.opp (* coefficients *)
      Z.eqb Z.leb
      IZR pow_phi rpow.



  Lemma Zsor : SOR 0 1 Z.add Z.mul Z.sub Z.opp (@eq Z) Z.le Z.lt.
  Proof.
    constructor ; intros ; subst; try reflexivity.
    - apply InitialRing.Zsth.
    - apply InitialRing.Zth.
    - auto using Z.le_antisymm.
    - eauto using Z.le_trans.
    - apply Z.le_neq.
    - apply Z.lt_trichotomy.
    - apply Z.add_le_mono_l; assumption.
    - apply Z.mul_pos_pos ; auto.
    - discriminate.
  Qed.

  Lemma ZSORaddon :
    SORaddon 0 1 Z.add Z.mul Z.sub Z.opp  (@eq Z) Z.le (* ring elements *)
      0%Z 1%Z Z.add Z.mul Z.sub Z.opp (* coefficients *)
      Z.eqb Z.leb
      (fun x => x) (fun x => x) (pow_N 1 Z.mul).
  Proof.
    constructor.
    - constructor ; intros ; try reflexivity.
      apply Z.eqb_eq ; auto.
    - constructor.
      reflexivity.
    - intros x y.
      rewrite <-Z.eqb_eq. congruence.
    - apply Z.leb_le.
  Qed.

  (* [isZ] defines what it means (for a variable) to range over the integers. *)
  Definition isZ (r:R) := exists z, req (IZR z)  r.

  Instance Eq_req : Equivalence req := SORsetoid Rsor.

  Add Morphism rplus with signature req ==> req ==> req as rplus_morph.
  Proof.
    exact (SORplus_wd Rsor).
  Qed.
  Add Morphism rtimes with signature req ==> req ==> req as rtimes_morph.
  Proof.
    exact (SORtimes_wd Rsor).
  Qed.
  Add Morphism ropp with signature req ==> req as ropp_morph.
  Proof.
    exact (SORopp_wd Rsor).
  Qed.
  Add Morphism rle with signature req ==> req ==> iff as rle_morph.
  Proof.
    exact (SORle_wd Rsor).
  Qed.
  Add Morphism rlt with signature req ==> req ==> iff as rlt_morph.
  Proof.
    exact (SORlt_wd Rsor).
  Qed.

  Add Morphism rminus with signature req ==> req ==> req as rminus_morph.
  Proof.
    exact (rminus_morph Rsor). (* We already proved that minus is a morphism in OrderedRing.v *)
  Qed.

  Definition Rbmorph (f1 f2: R -> R -> R) :=
    forall x1 x2 y1 y2, req x1 x2 -> req y1 y2 -> req (f1 x1 y1) (f2 x2 y2).


  Add Morphism (@pow_pos R) with signature (Rbmorph) ==> req ==> @eq positive ==> req as pow_pos_morph.
  Proof.
    intros rt1 rt2 M x y EQ p.
    induction p; simpl.
    - unfold Rbmorph in M.
      apply M; auto.
    - apply M; auto.
    - auto.
  Qed.

  Add Ring SORRing : (SORrt Rsor).

  Add Morphism isZ with signature req ==> iff as isZ_morph.
  Proof.
    intros. unfold isZ.
    split; intros; destruct H0 as (z & EQ); exists z; rewrite EQ; rewrite H; reflexivity.
  Qed.

  Lemma isZ_rplus : forall r1 r2,
      isZ r1 -> isZ r2 ->
      isZ (rplus r1 r2).
  Proof.
    unfold isZ.
    intros.
    destruct H as (z1 & EQ1).
    destruct H0 as (z2 & EQ2).
    exists (z1 + z2).
    rewrite (morph_add (SORrm RSORaddon)).
    rewrite EQ1. rewrite EQ2.
    reflexivity.
  Qed.

  Lemma isZ_rtimes : forall r1 r2,
      isZ r1 -> isZ r2 ->
      isZ (rtimes r1 r2).
  Proof.
    unfold isZ.
    intros.
    destruct H as (z1 & EQ1).
    destruct H0 as (z2 & EQ2).
    exists (z1 * z2).
    rewrite (morph_mul (SORrm RSORaddon)).
    rewrite EQ1. rewrite EQ2.
    reflexivity.
  Qed.

  Lemma isZ_pow_pos : forall r p,
      isZ r ->
      isZ (pow_pos rtimes r p).
  Proof.
    intros.
    induction p; simpl; now repeat apply isZ_rtimes.
  Qed.

  Lemma isZ_ropp : forall r,
      isZ r ->
      isZ (ropp r).
  Proof.
    unfold isZ.
    intros.
    destruct H as (z1 & EQ1).
    exists (- z1).
    rewrite (morph_opp (SORrm RSORaddon)).
    rewrite EQ1.
    reflexivity.
  Qed.

  Definition eval_expr := eval_pexpr  rplus rtimes rminus ropp IZR pow_phi rpow.

  Definition eval_formula :=
    eval_formula  rplus rtimes rminus ropp req rle rlt IZR pow_phi rpow.

  Definition Zeval_nformula :=
    eval_nformula Z0 Z.add Z.mul (@eq Z) Z.le Z.lt (fun x => x).

  Definition eval_nformula :=
    eval_nformula rO rplus rtimes req rle rlt IZR.

  Definition psub  := psub Z0  Z.add Z.sub Z.opp Z.eqb.
  Declare Equivalent Keys psub RingMicromega.psub.

  Definition popp  := popp Z.opp.
  Declare Equivalent Keys popp RingMicromega.popp.

  Definition padd  := padd Z0  Z.add Z.eqb.
  Declare Equivalent Keys padd RingMicromega.padd.

  Definition pmul := pmul 0 1 Z.add Z.mul Z.eqb.
  Declare Equivalent Keys pmul RingMicromega.pmul.

  Definition norm  := norm 0 1 Z.add Z.mul Z.sub Z.opp Z.eqb.
  Declare Equivalent Keys norm RingMicromega.norm.

  Definition Zeval_pol := eval_pol Z.add Z.mul (fun x => x).

  Definition eval_pol := eval_pol rplus rtimes IZR.
  Declare Equivalent Keys eval_pol RingMicromega.eval_pol.

  Lemma Zeval_pol_Pc : forall env z, (Zeval_pol env (Pc z)) = z.
  Proof.  intros. reflexivity.  Qed.


  Lemma Zeval_pol_add : forall env lhs rhs, (Zeval_pol env (padd  lhs rhs)) = (Zeval_pol env lhs) + (Zeval_pol env rhs).
  Proof. intros. apply (eval_pol_add Zsor ZSORaddon).  Qed.

  Lemma Zeval_pol_sub : forall env lhs rhs, (Zeval_pol env (psub  lhs rhs)) = (Zeval_pol env lhs) - (Zeval_pol env rhs).
  Proof. intros. apply (eval_pol_sub Zsor ZSORaddon).  Qed.

  Lemma eval_pol_add : forall env lhs rhs, req (eval_pol env (padd  lhs rhs)) (rplus (eval_pol env lhs) (eval_pol env rhs)).
  Proof. intros. apply (eval_pol_add Rsor RSORaddon). Qed.

  Lemma eval_pol_sub : forall env lhs rhs, req (eval_pol env (psub  lhs rhs))  (rminus (eval_pol env lhs)  (eval_pol env rhs)).
  Proof. intros. unfold eval_pol. eapply (eval_pol_sub Rsor RSORaddon). Qed.

  Lemma eval_pol_mul : forall env lhs rhs, req (eval_pol env (pmul  lhs rhs)) (rtimes (eval_pol env lhs) (eval_pol env rhs)).
  Proof. intros. apply (eval_pol_mul Rsor RSORaddon). Qed.


  Lemma eval_pol_norm : forall env e, req (eval_expr env e) (eval_pol env (norm e)).
  Proof. intros. apply (eval_pol_norm Rsor RSORaddon). Qed.

  Definition Zunsat := check_inconsistent 0  Z.eqb Z.leb.

  Definition Zdeduce := nformula_plus_nformula 0 Z.add Z.eqb.

  Lemma Zunsat_sound : forall f,
      Zunsat f = true -> forall env, eval_nformula env f -> False.
  Proof.
    unfold Zunsat.
    intros f H env ?.
    destruct f.
    eapply check_inconsistent_sound with (1 := Rsor) (2 := RSORaddon) in H; eauto.
  Qed.

  Lemma Zdeduce_sound : forall f1 f2 f,
      Zdeduce f1 f2 = Some f -> forall env, eval_nformula env f1 -> eval_nformula env f2 -> eval_nformula env f.
  Proof.
    unfold Zdeduce.
    intros.
    eapply nformula_plus_nformula_correct in H ;eauto.
  Qed.

  Definition xnnormalise (t : Formula Z) : NFormula Z :=
    let (lhs,o,rhs) := t in
    let lhs := norm lhs in
    let rhs := norm rhs in
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
      eval_nformula env (xnnormalise f) <-> eval_formula env  f.
  Proof.
    intros env f.
    unfold xnnormalise.
    destruct f as [lhs o rhs].
    destruct o eqn:O ; cbn ; rewrite ?eval_pol_sub;
      rewrite <- !eval_pol_norm ; simpl in *;
      unfold eval_expr;
      generalize (eval_pexpr rplus rtimes rminus ropp IZR pow_phi rpow env lhs) as z;
      generalize (eval_pexpr rplus rtimes rminus ropp IZR pow_phi rpow env rhs) as z1.
    - intros.
      rewrite (Rminus_eq_0 Rsor).
      split ; intro H ; rewrite H; reflexivity.
    - intros.
      rewrite (Rminus_eq_0 Rsor).
      split ; intro H ; intro H1; apply H; rewrite H1; reflexivity.
    - intros.
      symmetry. apply (Rle_le_minus Rsor).
    - intros. symmetry. apply (Rle_le_minus Rsor).
    - intros. symmetry. apply (Rlt_lt_minus Rsor).
    - intros. symmetry. apply (Rlt_lt_minus Rsor).
  Qed.

  Fixpoint vars (jmp : positive) (p : Pol Z) : list positive :=
    match p with
    | Pc c => nil
    | Pinj j p => vars (Pos.add j jmp) p
    | PX p j q => jmp::(vars jmp p)++vars (Pos.succ jmp) q
    end.


  Lemma eval_pol_jump : forall p j env pol,
      eval_pol (Env.jump p (Env.jump j env)) pol =
        eval_pol (Env.jump j (Env.jump p env)) pol.
  Proof.
    intros.
    apply env_morph.
    unfold Env.jump.
    intros.
    f_equal. rewrite <- !Pos.add_assoc.
    f_equal. apply Pos.add_comm.
  Qed.


  Lemma In_vars_add : forall pol (j x p:positive),
      In x (vars j pol) ->
      In (x + p)%positive (vars (p + j)%positive pol).
  Proof.
    induction pol.
    - simpl. auto.
    - simpl. intros.
      apply IHpol with (p:= p0) in H.
      replace (p + (p0 + j))%positive with (p0 + (p + j))%positive.
      auto.
      rewrite Pos.add_comm.
      rewrite <- Pos.add_assoc.
      f_equal. rewrite Pos.add_comm. reflexivity.
    - simpl. intros.
      rewrite in_app_iff in *.
      destruct H as [H | [ H | H]].
      + subst.
        rewrite Pos.add_comm. tauto.
      + right. left.
        apply IHpol1; auto.
      + right. right.
        rewrite <- Pos.add_succ_r.
        apply IHpol2.
        auto.
  Qed.


  Lemma has_var_eval : forall pol env env',
      (forall x, In x (vars xH pol) -> env x = env' x) ->
      eval_pol env pol = eval_pol  env' pol.
  Proof.
    induction pol.
    - simpl. reflexivity.
    - simpl.
      intros.
      apply IHpol.
      intros.
      unfold Env.jump.
      apply H.
      apply In_vars_add; auto.
    - simpl.
      intros.
      f_equal.
      f_equal.
      + eapply IHpol1.
        intros.
        apply H. rewrite! in_app_iff. tauto.
      + unfold Env.hd,Env.jump,Env.nth.
        rewrite H. reflexivity.
        rewrite in_app_iff. tauto.
      +
        unfold Env.tail.
        apply IHpol2.
        intros.
        unfold Env.jump.
        apply H.
        rewrite in_app_iff.
        right. right.
        change 2%positive with (1 + 1)%positive.
        apply In_vars_add; auto.
  Qed.


  Fixpoint xis_integral (e : positive -> bool) (jmp:positive)  (pol : Pol Z) : bool :=
    match pol with
    | Pc _ => true
    | Pinj j p0 => xis_integral e (j + jmp) p0
    | PX p0 j q => xis_integral e jmp p0 && e jmp && xis_integral e (Pos.succ jmp) q
    end.

  Definition get (s: PositiveSet.t) :=
    fun x => PositiveSet.mem x s.

  Definition oget (s:option PositiveSet.t) (x:positive) :=
    match s with
    | None => true
    | Some s => PositiveSet.mem x s
    end.

  Definition is_integral (e: option PositiveSet.t) (pol : Pol Z) :=
    match e with
    | None => true
    | Some e => xis_integral (get e) xH pol
    end.

  Lemma xis_integral_jump : forall pol eb p j,
      xis_integral eb (p + j) pol = true ->
      xis_integral (Env.jump p eb) j pol = true.
  Proof.
    induction pol.
    - simpl. reflexivity.
    - simpl. intros.
      apply IHpol.
      replace (p0 + (p + j))%positive with (p + (p0 + j))%positive.
      auto.
      symmetry.
      rewrite (Pos.add_comm p0).
      rewrite <- Pos.add_assoc.
      f_equal. rewrite Pos.add_comm. reflexivity.
    - simpl. intros.
      rewrite !andb_true_iff in *.
      destruct H as ((H1 & H2) & H3).
      repeat split.
      + eapply IHpol1. auto.
      + unfold Env.jump. rewrite Pos.add_comm. auto.
      + eapply IHpol2;auto.
        rewrite <- Pos.add_succ_r in H3. auto.
  Qed.

  Lemma xis_integral_sound : forall pol eb j,
      xis_integral eb j pol = true ->
      (forall x, In x (vars  j pol) -> eb x = true).
  Proof.
    induction pol.
    - simpl. tauto.
    - intros.
      simpl in H,H0.
      eapply IHpol;eauto.
    - intros.
      simpl in H,H0.
      rewrite !andb_true_iff in *.
      rewrite !in_app_iff in *.
      destruct H as ((H1 & H2) & H3).
      destruct H0 as [H0 | [H0 | H0]].
      + congruence.
      + eapply IHpol1;eauto.
      + eapply IHpol2;eauto.
  Qed.

  Lemma is_integral_sound : forall pol eb,
      is_integral eb  pol = true ->
      (forall x, In x (vars  1 pol) -> oget eb x = true).
  Proof.
    unfold is_integral.
    destruct eb.
    - simpl.
      intros.
      apply xis_integral_sound with (x:= x) in H; auto.
    - reflexivity.
  Qed.

  Local Open Scope Z_scope.

  Definition ceiling (a b:Z) : Z :=
    let (q,r) := Z.div_eucl a b in
    match r with
    | Z0 => q
    | _  => q + 1
    end.

  Lemma Zdivide_ceiling : forall a b, (b | a) -> ceiling a b = Z.div a b.
  Proof.
    unfold ceiling.
    intros a b H.
    apply Zdivide_mod in H.
    case_eq (Z.div_eucl a b).
    intros z z0 H0.
    change z with (fst (z,z0)).
    rewrite <- H0.
    change (fst (Z.div_eucl a b)) with (Z.div a b).
    change z0 with (snd (z,z0)).
    rewrite <- H0.
    change (snd (Z.div_eucl a b)) with (Z.modulo a b).
    rewrite H.
    reflexivity.
  Qed.

  Lemma narrow_interval_lower_bound a b x :
    a > 0 -> a * x  >= b -> x >= ceiling b a.
  Proof.
    rewrite !Z.ge_le_iff.
    unfold ceiling.
    intros Ha H.
    generalize (Z_div_mod b a Ha).
    destruct (Z.div_eucl b a) as (q,r). intros (->,(H1,H2)).
    destruct r as [|r|r].
    - rewrite Z.add_0_r in H.
      apply Z.mul_le_mono_pos_l in H; auto with zarith.
    - assert (0 < Z.pos r) by easy.
      rewrite Z.add_1_r, Z.le_succ_l.
      apply Z.mul_lt_mono_pos_l with a.
      + auto using Z.gt_lt.
      + eapply Z.lt_le_trans. 2: eassumption.
        now apply Z.lt_add_pos_r.
    - now elim H1.
  Qed.
  (** NB: narrow_interval_upper_bound is Zdiv.Zdiv_le_lower_bound *)

  Definition ZWitness := Psatz Z.

  Inductive ZArithProof :=
  | DoneProof
  | RatProof : ZWitness -> ZArithProof -> ZArithProof
  | CutProof : ZWitness -> ZArithProof -> ZArithProof
  | SplitProof : PolC Z -> ZArithProof -> ZArithProof -> ZArithProof
  | EnumProof : ZWitness -> ZWitness -> list ZArithProof -> ZArithProof
  | ExProof   : positive -> ZArithProof -> ZArithProof
  (*ExProof x : exists z t, x = z - t /\ z >= 0 /\ t >= 0 *)
  .


  Register ZArithProof as micromega.ZArithProof.type.
  Register DoneProof   as micromega.ZArithProof.DoneProof.
  Register RatProof    as micromega.ZArithProof.RatProof.
  Register CutProof    as micromega.ZArithProof.CutProof.
  Register SplitProof  as micromega.ZArithProof.SplitProof.
  Register EnumProof   as micromega.ZArithProof.EnumProof.
  Register ExProof     as micromega.ZArithProof.ExProof.


  (* In order to compute the 'cut', we need to express a polynomial P as a * Q + b.
   - b is the constant
   - a is the gcd of the other coefficient.
   *)

  Definition isZ0 (x:Z) :=
    match x with
    | Z0 => true
    | _  => false
    end.

  Lemma isZ0_0 : forall x, isZ0 x = true <-> x = 0.
  Proof.
    intros x; destruct x ; simpl ; intuition congruence.
  Qed.

  Lemma isZ0_n0 : forall x, isZ0 x = false <-> x <> 0.
  Proof.
    intros x; destruct x ; simpl ; intuition congruence.
  Qed.

  Definition ZgcdM (x y : Z) := Z.max (Z.gcd x y) 1.


  Fixpoint Zgcd_pol (p : PolC Z) : (Z * Z) :=
    match p with
    | Pc c => (0,c)
    | Pinj _ p => Zgcd_pol p
    | PX p _ q =>
        let (g1,c1) := Zgcd_pol p in
        let (g2,c2) := Zgcd_pol q in
        (ZgcdM (ZgcdM g1 c1) g2 , c2)
    end.

  Fixpoint Zdiv_pol (p:PolC Z) (x:Z) : PolC Z :=
    match p with
    | Pc c => Pc (Z.div c x)
    | Pinj j p => Pinj j (Zdiv_pol p x)
    | PX p j q => PX (Zdiv_pol p x) j (Zdiv_pol q x)
    end.

  Inductive Zdivide_pol (x:Z): PolC Z -> Prop :=
  | Zdiv_Pc : forall c, (x | c) -> Zdivide_pol x (Pc c)
  | Zdiv_Pinj : forall p, Zdivide_pol x p ->  forall j, Zdivide_pol x (Pinj j p)
  | Zdiv_PX   : forall p q, Zdivide_pol x p -> Zdivide_pol x q -> forall j, Zdivide_pol x (PX p j q).


  Lemma Zdiv_pol_correct : forall a p, 0 < a -> Zdivide_pol a p  ->
                                       forall env, Zeval_pol env p = a * Zeval_pol env (Zdiv_pol p a).
  Proof.
    intros a p H H0.
    induction H0 as [? ?|? ? IHZdivide_pol j|? ? ? IHZdivide_pol1 ? IHZdivide_pol2 j].
    - (* Pc *)
      simpl.
      intros.
      apply Zdivide_Zdiv_eq in H0 ; auto.
    - (* Pinj *)
      simpl.
      intros.
      apply IHZdivide_pol.
    - (* PX *)
      simpl.
      intros.
      rewrite IHZdivide_pol1.
      rewrite IHZdivide_pol2.
      ring.
  Qed.

  Lemma Zgcd_pol_ge : forall p, fst (Zgcd_pol p) >= 0.
  Proof.
    intros p; induction p as [c|p p1 IHp1|p1 IHp1 ? p3 IHp3]. 1-2: easy.
    simpl.
    case_eq (Zgcd_pol p1).
    case_eq (Zgcd_pol p3).
    intros.
    simpl.
    unfold ZgcdM.
    apply Z.le_ge; transitivity 1.
    - easy.
    - apply Z.le_max_r.
  Qed.

  Lemma Zdivide_pol_Zdivide : forall p x y, Zdivide_pol x p -> (y | x) ->  Zdivide_pol y p.
  Proof.
    intros p x y H H0.
    induction H.
    - constructor.
      apply Z.divide_trans with (1:= H0) ; assumption.
    - constructor. auto.
    - constructor ; auto.
  Qed.

  Lemma Zdivide_pol_one : forall p, Zdivide_pol 1 p.
  Proof.
    intros p; induction p as [c| |]; constructor ; auto.
    exists c. ring.
  Qed.

  Lemma Zgcd_minus : forall a b c, (a | c - b ) -> (Z.gcd a b | c).
  Proof.
    intros a b c (q,Hq).
    destruct (Zgcd_is_gcd a b) as [(a',Ha) (b',Hb) _].
    set (g:=Z.gcd a b) in *; clearbody g.
    exists (q * a' + b').
    symmetry in Hq. rewrite <- Z.add_move_r in Hq.
    rewrite <- Hq, Hb, Ha. ring.
  Qed.

  Lemma Zdivide_pol_sub : forall p a b,
      0 < Z.gcd a b ->
      Zdivide_pol a (PsubC Z.sub p b) ->
      Zdivide_pol (Z.gcd a b) p.
  Proof.
    intros p; induction p as [c|? p IHp|p ? ? ? IHp2].
    - simpl.
      intros a b H H0. inversion H0.
      constructor.
      apply Zgcd_minus ; auto.
    - intros ? ? H H0.
      constructor.
      simpl in H0. inversion H0 ; subst; clear H0.
      apply IHp ; auto.
    - simpl. intros a b H H0.
      inv H0.
      constructor.
      + apply Zdivide_pol_Zdivide with (1:= (ltac:(assumption) : Zdivide_pol a p)).
        destruct (Zgcd_is_gcd a b) ; assumption.
      + apply IHp2 ; assumption.
  Qed.

  Lemma Zdivide_pol_sub_0 : forall p a,
      Zdivide_pol a (PsubC Z.sub p 0) ->
      Zdivide_pol a p.
  Proof.
    intros p; induction p as [c|? p IHp|? IHp1 ? ? IHp2].
    - simpl.
      intros ? H. inversion H.
      constructor. rewrite Z.sub_0_r in *. assumption.
    - intros ? H.
      constructor.
      simpl in H. inversion H ; subst; clear H.
      apply IHp ; auto.
    - simpl. intros ? H.
      inv H.
      constructor.
      + auto.
      + apply IHp2 ; assumption.
  Qed.


  Lemma Zgcd_pol_div : forall p g c,
      Zgcd_pol p = (g, c) -> Zdivide_pol g (PsubC Z.sub p c).
  Proof.
    intros p; induction p as [c|? ? IHp|p1 IHp1 ? p3 IHp2]; simpl.
    - (* Pc *)
      intros ? ? H. inv H.
      constructor.
      exists 0. now ring.
    - (* Pinj *)
      intros.
      constructor.  apply IHp ; auto.
    - (* PX *)
      intros g c.
      case_eq (Zgcd_pol p1) ; case_eq (Zgcd_pol p3) ; intros z z0 H z1 z2 H0 H1.
      inv H1.
      unfold ZgcdM at 1.
      destruct (Z.max_spec (Z.gcd (ZgcdM z1 z2) z) 1) as [HH1 | HH1]; cycle 1;
        destruct HH1 as [HH1 HH1'] ; rewrite HH1'.
      + constructor.
        * apply (Zdivide_pol_Zdivide _ (ZgcdM z1 z2)).
          -- unfold ZgcdM.
             destruct (Z.max_spec  (Z.gcd z1 z2)  1) as [HH2 | HH2]; cycle 1.
             ++ destruct HH2 as [H1 H2].
                rewrite H2.
                apply Zdivide_pol_sub ; auto.
                apply Z.lt_le_trans with 1.
                ** reflexivity.
                ** trivial.
             ++ destruct HH2 as [H1 H2]. rewrite H2.
                apply Zdivide_pol_one.
          -- unfold ZgcdM in HH1. unfold ZgcdM.
             destruct (Z.max_spec  (Z.gcd z1 z2)  1) as [HH2 | HH2]; cycle 1.
             ++ destruct HH2 as [H1 H2]. rewrite H2 in *.
                destruct (Zgcd_is_gcd (Z.gcd z1 z2) z); auto.
             ++ destruct HH2 as [H1 H2]. rewrite H2.
                destruct (Zgcd_is_gcd 1  z); auto.
        * apply (Zdivide_pol_Zdivide _ z).
          -- apply (IHp2 _ _ H); auto.
          -- destruct (Zgcd_is_gcd (ZgcdM z1 z2) z); auto.
      + constructor.
        * apply Zdivide_pol_one.
        * apply Zdivide_pol_one.
  Qed.

  Lemma Zgcd_pol_correct_lt : forall p env g c,
      Zgcd_pol p = (g,c) -> 0 < g ->
      Zeval_pol env p =   g *  Zeval_pol env (Zdiv_pol (PsubC Z.sub p c) g) + c.
  Proof.
    intros.
    rewrite <- Zdiv_pol_correct ; auto.
    - rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).
      unfold Zeval_pol. ring.
    - apply Zgcd_pol_div ; auto.
  Qed.

  Definition phi_env (S : positive -> Prop)
    (env: positive -> Z)
    (env': positive -> R) :=
    forall x, S x -> req (IZR (env x)) (env' x).

  Definition mem (l:list positive) (x:positive) := In x l.

  Lemma IZR_pow_pos : forall x p,
      req (IZR (pow_pos Z.mul x p)) (pow_pos rtimes (IZR x) p).
  Proof.
    induction p; simpl.
    -  rewrite! (morph_mul (SORrm RSORaddon)).
       apply rtimes_morph.
       reflexivity.
       apply rtimes_morph; auto.
    - rewrite! (morph_mul (SORrm RSORaddon)).
      apply rtimes_morph;auto.
    - reflexivity.
  Qed.


  Lemma eval_Zpol_phi : forall pol env env',
      phi_env (mem  (vars xH pol)) env env' ->
      req (IZR (Zeval_pol env pol))  (eval_pol env' pol).
  Proof.
    unfold phi_env,mem.
    induction pol;intros env env' PHI.
    - simpl. reflexivity.
    - simpl.
      apply IHpol.
      intros x IN.
      apply PHI.
      now apply In_vars_add.
    - simpl; simpl in PHI.
      rewrite (morph_add (SORrm RSORaddon)).
      rewrite (morph_mul (SORrm RSORaddon)).
      apply rplus_morph.
      apply rtimes_morph.
      apply IHpol1.
      intros x IN. apply PHI.
      rewrite !in_app_iff. tauto.
      unfold Env.hd,Env.nth.
      rewrite IZR_pow_pos.
      apply pow_pos_morph. unfold Rbmorph. intros.
      rewrite H;rewrite H0;reflexivity.
      apply PHI. tauto. reflexivity.
      apply IHpol2.
      intros. apply PHI.
      rewrite !in_app_iff.
      right. right.
      change 2%positive with (1 + 1)%positive.
      now apply In_vars_add.
  Qed.

  Definition makeCuttingPlane (p : PolC Z) : PolC  Z * Z :=
    let (g,c) := Zgcd_pol p in
    if Z.gtb g Z0
    then (Zdiv_pol (PsubC Z.sub p c) g , Z.opp (ceiling (Z.opp c) g))
    else (p,Z0).


  Definition genCuttingPlane (f : NFormula Z) : option (PolC Z * Z * Op1) :=
    let (e,op) := f in
    match op with
    | Equal => let (g,c) := Zgcd_pol e in
               if andb (Z.gtb g Z0) (andb (negb (Z.eqb c Z0)) (negb (Z.eqb (Z.gcd g c) g)))
               then None (* inconsistent *)
               else (* Could be optimised Zgcd_pol is recomputed *)
                 let (p,c) := makeCuttingPlane e  in
                 Some (p,c,Equal)
    | NonEqual => Some (e,Z0,op)
    | Strict   =>  let (p,c) := makeCuttingPlane (PsubC Z.sub e 1) in
                   Some (p,c,NonStrict)
    | NonStrict => let (p,c) := makeCuttingPlane e  in
                   Some (p,c,NonStrict)
    end.

  Definition nformula_of_cutting_plane (t : PolC Z * Z * Op1) : NFormula Z :=
    let (e_z, o) := t in
    let (e,z) := e_z in
    (padd e (Pc z) , o).

  Definition is_pol_Z0 (p : PolC Z) : bool :=
    match p with
    | Pc Z0 => true
    |   _   => false
    end.

  Lemma is_pol_Z0_eval_pol : forall p, is_pol_Z0 p = true -> forall env, req (eval_pol env p)  rO.
  Proof.
    unfold is_pol_Z0.
    intros p; destruct p as [z| |]; try discriminate.
    destruct z ; try discriminate.
    simpl. intros. apply (morph0 (SORrm RSORaddon)).
  Qed.


  Lemma is_pol_Z0_Zeval_pol : forall p, is_pol_Z0 p = true -> forall env, Zeval_pol env p = 0.
  Proof.
    unfold is_pol_Z0.
    intros p; destruct p as [z| |]; try discriminate.
    destruct z ; try discriminate.
    simpl. reflexivity.
  Qed.

  Definition eval_Psatz  : list (NFormula Z) -> ZWitness ->  option (NFormula Z) :=
    eval_Psatz 0 1 Z.add Z.mul Z.eqb Z.leb.


  Definition valid_cut_sign (op:Op1) :=
    match op with
    | Equal => true
    | NonStrict => true
    | Strict    => true
    | _         => false
    end.

  Definition bound_var (v : positive) : Formula Z :=
    Build_Formula (PEX v) OpGe (PEc 0).

  Definition mk_eq_pos (x : positive) (y:positive) (t : positive) : Formula Z :=
    Build_Formula (PEX x) OpEq (PEsub (PEX y) (PEX t)).

  Fixpoint max_var (jmp : positive) (p : Pol Z) : positive :=
    match p with
    | Pc _ => jmp
    | Pinj j p => max_var (Pos.add j jmp) p
    | PX p j q => Pos.max (max_var jmp p) (max_var (Pos.succ jmp) q)
    end.

  Lemma pos_le_add : forall y x,
      (x <= y + x)%positive.
  Proof.
    intros y x.
    assert  ((Z.pos x) <= Z.pos (x + y))%Z as H.
    - rewrite <- (Z.add_0_r (Zpos x)).
      rewrite <- Pos2Z.add_pos_pos.
      apply Z.add_le_mono_l.
      compute. congruence.
    - rewrite Pos.add_comm in H.
      apply H.
  Qed.


  Lemma max_var_le : forall p v,
      (v <= max_var v p)%positive.
  Proof.
    intros p; induction p as [?|p ? IHp|? IHp1 ? ? IHp2]; simpl.
    - intros.
      apply Pos.le_refl.
    - intros v.
      specialize (IHp (p+v)%positive).
      eapply Pos.le_trans ; eauto.
      assert (xH + v <= p + v)%positive.
      { apply Pos.add_le_mono.
        - apply Pos.le_1_l.
        - apply Pos.le_refl.
      }
      eapply Pos.le_trans ; eauto.
      apply pos_le_add.
    - intros v.
      apply Pos.max_case_strong;intros ; auto.
      specialize (IHp2 (Pos.succ v)%positive).
      eapply Pos.le_trans ; eauto.
  Qed.

  Lemma max_var_correct : forall p j v,
      In v (vars j p) -> Pos.le v (max_var j p).
  Proof.
    intros p; induction p; simpl.
    - tauto.
    - auto.
    - intros j v H.
      rewrite in_app_iff in H.
      destruct H as [H |[ H | H]].
      + subst.
        apply Pos.max_case_strong;intros ; auto.
        * apply max_var_le.
        * eapply Pos.le_trans ; eauto.
          apply max_var_le.
      + apply Pos.max_case_strong;intros ; auto.
        eapply Pos.le_trans ; eauto.
      + apply Pos.max_case_strong;intros ; auto.
        eapply Pos.le_trans ; eauto.
  Qed.

  Definition max_var_nformulae (l : list (NFormula Z)) :=
    List.fold_left  (fun acc f => Pos.max acc (max_var xH (fst f))) l xH.

  Section MaxVar.

    Definition F (acc : positive) (f : Pol Z * Op1) := Pos.max acc (max_var 1 (fst f)).

    Lemma max_var_nformulae_mono_aux :
      forall l v acc,
        (v <= acc ->
         v <= fold_left F l acc)%positive.
    Proof.
      intros l; induction l as [|a l IHl] ; simpl ; [easy|].
      intros.
      apply IHl.
      unfold F.
      apply Pos.max_case_strong;intros ; auto.
      eapply Pos.le_trans ; eauto.
    Qed.

    Lemma max_var_nformulae_mono_aux' :
      forall l acc acc',
        (acc <= acc' ->
         fold_left F l acc <= fold_left F l acc')%positive.
    Proof.
      intros l; induction l as [|a l IHl]; simpl ; [easy|].
      intros.
      apply IHl.
      unfold F.
      apply Pos.max_le_compat_r; auto.
    Qed.

    Lemma max_var_nformulae_correct_aux : forall l p o v,
        In (p,o) l -> In v (vars xH p) -> Pos.le v (fold_left F l 1)%positive.
    Proof.
      intros l p o v H H0.
      generalize 1%positive as acc.
      revert p o v H H0.
      induction l as [|a l IHl].
      - simpl. tauto.
      - simpl.
        intros p o v H H0 ?.
        destruct H ; subst.
        + unfold F at 2.
          simpl.
          apply max_var_correct in H0.
          apply max_var_nformulae_mono_aux.
          apply Pos.max_case_strong;intros ; auto.
          eapply Pos.le_trans ; eauto.
        + eapply IHl ; eauto.
    Qed.

  End MaxVar.

  Lemma max_var_nformalae_correct : forall l p o v,
      In (p,o) l -> In v (vars xH p) -> Pos.le v (max_var_nformulae l)%positive.
  Proof.
    intros l p o v.
    apply max_var_nformulae_correct_aux.
  Qed.

  Fixpoint max_var_psatz (w : Psatz Z) : positive :=
    match w with
    | PsatzIn _ n => xH
    | PsatzSquare p => max_var xH (Psquare 0 1 Z.add Z.mul Z.eqb p)
    | PsatzMulC p w => Pos.max (max_var xH p) (max_var_psatz w)
    | PsatzMulE w1 w2 => Pos.max (max_var_psatz w1) (max_var_psatz w2)
    | PsatzAdd w1 w2  => Pos.max (max_var_psatz w1) (max_var_psatz w2)
    | _   => xH
    end.

  Fixpoint max_var_prf (w : ZArithProof) : positive :=
    match w with
    | DoneProof => xH
    | RatProof w pf | CutProof w pf => Pos.max (max_var_psatz w) (max_var_prf pf)
    | SplitProof p pf1 pf2 => Pos.max (max_var xH p) (Pos.max (max_var_prf pf1) (max_var_prf pf1))
    | EnumProof w1 w2 l => List.fold_left
                             (fun acc prf => Pos.max acc (max_var_prf prf)) l
                             (Pos.max (max_var_psatz w1) (max_var_psatz w2))
    | ExProof _ pf => max_var_prf pf
    end.

  Definition add (x:positive) (s : option PositiveSet.t) :=
    match s with
    | None => None
    | Some s => Some (PositiveSet.add x s)
    end.


  Fixpoint ZChecker (is_integer : option (PositiveSet.t)) (l:list (NFormula Z)) (pf : ZArithProof)  {struct pf} : bool :=
    match pf with
    | DoneProof => false
    | RatProof w pf =>
        match eval_Psatz l w  with
        | None => false
        | Some f =>
            if Zunsat f then true
            else ZChecker is_integer (f::l) pf
        end
    | CutProof w pf =>
        match eval_Psatz l w with
        | None => false
        | Some f =>
            if is_integral is_integer (fst f)
            then
              match genCuttingPlane f with
              | None => true
              | Some cp =>
                  let f := nformula_of_cutting_plane cp in
                  if Zunsat f then true
                  else ZChecker is_integer (f::l) pf
              end  else  false
        end
    | SplitProof p pf1 pf2 =>
        if is_integral is_integer p
        then
          match genCuttingPlane (p,NonStrict) , genCuttingPlane (popp p, NonStrict) with
          | None , _ | _ , None => false
          | Some cp1 , Some cp2 =>
              ZChecker is_integer (nformula_of_cutting_plane cp1::l) pf1
              &&
                ZChecker is_integer (nformula_of_cutting_plane cp2::l) pf2
          end
        else  false
    | ExProof x prf =>
        let fr := max_var_nformulae l in
        if Pos.leb x fr && oget is_integer x then
          let z    := Pos.succ fr in
          let t    := Pos.succ z in
          let nfx  := xnnormalise (mk_eq_pos x z t) in
          let posz := xnnormalise (bound_var z) in
          let post := xnnormalise (bound_var t) in
          ZChecker (add z (add t is_integer)) (nfx::posz::post::l) prf
        else false
    | EnumProof w1 w2 pf =>
        match eval_Psatz l w1 , eval_Psatz l w2 with
        |  Some f1 , Some f2 =>
             if is_integral is_integer (fst f1) && is_integral is_integer (fst f2)
             then
               match genCuttingPlane f1 , genCuttingPlane f2 with
               |Some (e1,z1,op1) , Some (e2,z2,op2) =>
                  if (valid_cut_sign op1 && valid_cut_sign op2 && is_pol_Z0 (padd e1 e2))
                  then
                    (fix label (pfs:list ZArithProof) :=
                       fun lb ub =>
                         match pfs with
                         | nil => if Z.gtb lb ub then true else false
                         | pf::rsr => andb (ZChecker is_integer ((psub e1 (Pc lb), Equal) :: l) pf) (label rsr (Z.add lb 1%Z) ub)
                         end)   pf (Z.opp z1)  z2
                  else false
               |   _    ,   _   => true
               end
             else false
        |   _   ,  _ => false
        end
    end.



  Fixpoint bdepth (pf : ZArithProof) : nat :=
    match pf with
    | DoneProof  => O
    | RatProof _ p =>  S (bdepth p)
    | CutProof _  p =>   S  (bdepth p)
    | SplitProof _ p1 p2 => S (Nat.max (bdepth p1) (bdepth p2))
    | EnumProof _ _ l => S (List.fold_right (fun pf x => Nat.max (bdepth pf) x)   O l)
    | ExProof _ p   => S (bdepth p)
    end.

  Lemma in_bdepth : forall l a b  y, In y l ->  ltof ZArithProof bdepth y (EnumProof a b  l).
  Proof.
    intros l; induction l as [|a l IHl].
    - (* nil *)
      simpl.
      tauto.
    - (* cons *)
      simpl.
      intros a0 b y H.
      destruct H as [H|H].
      + subst.
        unfold ltof.
        simpl.
        generalize (         (fold_right
                                (fun (pf : ZArithProof) (x : nat) => Nat.max (bdepth pf) x) 0%nat l)).
        intros.
        generalize (bdepth y) ; intros.
        rewrite Nat.lt_succ_r. apply Nat.le_max_l.
      + generalize (IHl a0 b  y  H).
        unfold ltof.
        simpl.
        generalize (      (fold_right (fun (pf : ZArithProof) (x : nat) => Nat.max (bdepth pf) x) 0%nat
                             l)).
        intros.
        eapply Nat.lt_le_trans.
        * eassumption.
        * rewrite <- Nat.succ_le_mono.
          apply Nat.le_max_r.
  Qed.

  Lemma ltof_bdepth_split_l :
    forall p pf1 pf2,
      ltof ZArithProof bdepth pf1 (SplitProof p pf1 pf2).
  Proof.
    intros.
    unfold ltof. simpl.
    rewrite Nat.lt_succ_r.
    apply Nat.le_max_l.
  Qed.

  Lemma ltof_bdepth_split_r :
    forall p pf1 pf2,
      ltof ZArithProof bdepth pf2 (SplitProof p pf1 pf2).
  Proof.
    intros.
    unfold ltof. simpl.
    rewrite Nat.lt_succ_r.
    apply Nat.le_max_r.
  Qed.


  Lemma eval_Psatz_sound : forall env w l f',
      make_conj (eval_nformula env) l ->
      eval_Psatz l w  = Some f' ->  eval_nformula env f'.
  Proof.
    intros env w l f' H H0.
    apply (fun H => eval_Psatz_Sound Rsor RSORaddon l _ H w) ; auto.
    apply make_conj_in ; auto.
  Qed.


  Lemma Zeval_Psatz_sound : forall env w l f',
      make_conj (Zeval_nformula env) l ->
      eval_Psatz l w  = Some f' ->  Zeval_nformula env f'.
  Proof.
    intros env w l f' H H0.
    apply (fun H => eval_Psatz_Sound Zsor ZSORaddon l _ H w) ; auto.
    apply make_conj_in ; auto.
  Qed.



  Lemma le_add_le_sub_l :
    forall n m p : R, rle (rplus n  p) m <-> rle p (rminus m  n).
  Proof.
    intros.
    split;intros.
    -
      apply (Rplus_le_mono_l Rsor) with (p := ropp n) in H.
      assert (R1 : req (rplus (ropp n) (rplus n p)) p) by ring.
      assert (R2 : req (rplus (ropp n) m) (rminus m n)) by ring.
      now rewrite R1,R2 in H.
    - apply (Rplus_le_mono_l Rsor) with (p := n) in H.
      assert (R1 : req m (rplus n (rminus m n))) by ring.
      now rewrite R1.
  Qed.

  Lemma ropp_rminus :
    forall n m : R, req (rminus m  n) (rplus m (ropp n)).
  Proof.
    intros.
    ring.
  Qed.

  Lemma req_sym : forall x y, req x y -> req y x.
  Proof.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma rplus_phi_inv_l : forall x y r,
      req (rplus y (IZR x)) (IZR r) ->
      req y (IZR (r - x)).
  Proof.
    intros.
    rewrite (morph_sub (SORrm RSORaddon)).
    rewrite <- H. ring.
  Qed.

  Lemma makeCuttingPlane_ns_sound :
    forall env e e' c,
      Zeval_nformula env (e, NonStrict) ->
      makeCuttingPlane e = (e',c) ->
      Zeval_nformula env (nformula_of_cutting_plane (e', c, NonStrict)).
  Proof.
    unfold nformula_of_cutting_plane.
    unfold Zeval_nformula. unfold RingMicromega.eval_nformula.
    unfold eval_op1.
    intros env e e' c H H0.
    rewrite (RingMicromega.eval_pol_add Zsor ZSORaddon).
    simpl.
    (**)
    unfold makeCuttingPlane in H0.
    revert H0.
    case_eq (Zgcd_pol e) ; intros g c0.
    case Z.gtb_spec.
    - intros H0 H1 H2.
      inv H2.
      change (RingMicromega.eval_pol Z.add Z.mul (fun x : Z => x)) with Zeval_pol in *.
      apply (Zgcd_pol_correct_lt _ env) in H1. 2: auto using Z.gt_lt.
      apply Z.le_add_le_sub_l, Z.ge_le; rewrite Z.add_0_r.
      apply (narrow_interval_lower_bound g (- c0) (Zeval_pol env (Zdiv_pol (PsubC Z.sub e c0) g))); auto using Z.lt_gt.
      apply Z.le_ge.
      rewrite <- Z.sub_0_l.
      apply Z.le_sub_le_add_r.
      rewrite <- H1.
      assumption.
    (* g <= 0 *)
    - intros H0 H1 H2. inv H2. auto with zarith.
  Qed.


  Lemma cutting_plane_sound : forall env f p,
      Zeval_nformula env f ->
      genCuttingPlane f = Some p ->
      Zeval_nformula env (nformula_of_cutting_plane p).
  Proof.
    unfold genCuttingPlane.
    intros env f; destruct f as [e op].
    destruct op.
    - (* Equal *)
      intros p; destruct p as [[e' z] op].
      case_eq (Zgcd_pol e) ; intros g c.
      case_eq (Z.gtb g 0 && (negb (Z.eqb c 0) && negb (Z.eqb (Z.gcd g c) g))) ; [discriminate|].
      case_eq (makeCuttingPlane e).
      intros ? ? H H0 H1 H2 H3.
      inv H3.
      unfold makeCuttingPlane in H.
      rewrite H1 in H.
      revert H.
      change (Zeval_pol env e = 0) in H2.
      case_eq (Z.gtb g 0).
      + intros H H3.
        rewrite Z.gtb_lt in H.
        rewrite Zgcd_pol_correct_lt with (1:= H1)  in H2. 2: auto using Z.gt_lt.
        unfold nformula_of_cutting_plane.
        change (Zeval_pol env (padd e' (Pc z)) = 0).
        inv H3.
        rewrite (RingMicromega.eval_pol_add Zsor ZSORaddon).
        fold Zeval_pol.
        set (x:=Zeval_pol env (Zdiv_pol (PsubC Z.sub e c) g)) in *; clearbody x.
        simpl.
        rewrite andb_false_iff in H0.
        destruct H0 as [H0|H0].
        * rewrite <-Z.gtb_lt in H ; congruence.
        * rewrite andb_false_iff in H0.
          destruct H0 as [H0|H0].
          -- rewrite negb_false_iff in H0.
             apply Z.eqb_eq in H0.
             subst. simpl.
             rewrite Z.add_0_r, Z.mul_eq_0 in H2.
             intuition subst; easy.
          -- rewrite negb_false_iff in H0.
             apply Z.eqb_eq in H0.
             rewrite Zdivide_ceiling; cycle 1.
             { apply Z.divide_opp_r. rewrite <-H0. apply Z.gcd_divide_r. }
             apply Z.sub_move_0_r.
             apply Z.div_unique_exact.
             ++ now intros ->.
             ++ now rewrite Z.add_move_0_r in H2.
      + intros H H3.
        unfold nformula_of_cutting_plane.
        inv H3.
        change (Zeval_pol env (padd e' (Pc 0)) = 0).
        rewrite (RingMicromega.eval_pol_add Zsor ZSORaddon).
        simpl.
        now rewrite Z.add_0_r.
    - (* NonEqual *)
      intros ? H H0.
      inv H0.
      unfold Zeval_nformula in *.
      unfold RingMicromega.eval_nformula in *.
      unfold nformula_of_cutting_plane.
      unfold eval_op1 in *.
      rewrite (RingMicromega.eval_pol_add Zsor ZSORaddon).
      simpl. now rewrite Z.add_0_r.
    - (* Strict *)
      intros p; destruct p as [[e' z] op].
      case_eq (makeCuttingPlane (PsubC Z.sub e 1)).
      intros ? ? H H0 H1.
      inv H1.
      apply (makeCuttingPlane_ns_sound env) with (2:= H).
      simpl in *.
      rewrite (RingMicromega.PsubC_ok Zsor ZSORaddon).
      now apply Z.lt_le_pred.
    - (* NonStrict *)
      intros p; destruct p as [[e' z] op].
      case_eq (makeCuttingPlane e).
      intros ? ? H H0 H1.
      inv H1.
      apply (makeCuttingPlane_ns_sound env) with (2:= H).
      assumption.
  Qed.

  Lemma  genCuttingPlaneNone : forall env f,
      genCuttingPlane f = None ->
      Zeval_nformula env f -> False.
  Proof.
    unfold genCuttingPlane.
    intros env f; destruct f as [p o].
    destruct o.
    - case_eq (Zgcd_pol p) ; intros g c.
      case_eq (Z.gtb g 0 && (negb (Z.eqb c 0) && negb (Z.eqb (Z.gcd g c) g))).
      + intros H H0 H1 H2.
        flatten_bool.
        match goal with [ H' : (g >? 0) = true |- ?G ] => rename H' into H3 end.
        match goal with [ H' : negb (Z.eqb c 0) = true |- ?G ] => rename H' into H end.
        match goal with [ H' : negb (Z.eqb (Z.gcd g c) g) = true |- ?G ] => rename H' into H5 end.
        rewrite negb_true_iff in H5.
        apply Z.eqb_neq in H5.
        rewrite Z.gtb_lt in H3.
        rewrite negb_true_iff in H.
        apply Z.eqb_neq in H.
        change (Zeval_pol env p = 0) in H2.
        rewrite Zgcd_pol_correct_lt with (1:= H0) in H2. 2: auto using Z.gt_lt.
        set (x:=Zeval_pol env (Zdiv_pol (PsubC Z.sub p c) g)) in *; clearbody x.
        contradict H5.
        apply Zis_gcd_gcd.
        * apply Z.lt_le_incl; assumption.
        * constructor; auto with zarith.
          exists (-x).
          rewrite Z.mul_opp_l, Z.mul_comm.
          now apply Z.add_move_0_l.
      (**)
      + destruct (makeCuttingPlane p);  discriminate.
    - discriminate.
    - destruct (makeCuttingPlane (PsubC Z.sub p 1)) ; discriminate.
    - destruct (makeCuttingPlane p) ; discriminate.
  Qed.


  Lemma eval_nformula_mk_eq_pos : forall env x z t,
      req (env x) (rminus (env z)  (env t)) ->
      eval_nformula env (xnnormalise (mk_eq_pos x z t)).
  Proof.
    intros.
    rewrite xnnormalise_correct.
    simpl. auto.
  Qed.

  Lemma eval_nformula_bound_var : forall env x,
      rle rO (env x) ->
      eval_nformula env (xnnormalise (bound_var x)).
  Proof.
    intros.
    rewrite xnnormalise_correct.
    simpl.
    easy.
  Qed.


  Definition agree_env (fr : positive) (env env' : positive -> R) : Prop :=
    forall x, Pos.le x fr -> env x = env' x.

  Lemma agree_env_subset : forall v1 v2 env env',
      agree_env v1 env env' ->
      Pos.le v2 v1 ->
      agree_env v2 env env'.
  Proof.
    unfold agree_env.
    intros v1 v2 env env' H ? ? ?.
    apply H.
    eapply Pos.le_trans ; eauto.
  Qed.


  Lemma agree_env_jump : forall fr j env env',
      agree_env (fr + j) env env' ->
      agree_env fr (Env.jump j env) (Env.jump j env').
  Proof.
    intros fr j env env' H.
    unfold agree_env ; intro.
    intros.
    unfold Env.jump.
    apply H.
    apply Pos.add_le_mono_r; auto.
  Qed.


  Lemma agree_env_tail : forall fr env env',
      agree_env (Pos.succ fr) env env' ->
      agree_env fr (Env.tail env) (Env.tail env').
  Proof.
    intros fr env env' H.
    unfold Env.tail.
    apply agree_env_jump.
    rewrite <- Pos.add_1_r in H.
    apply H.
  Qed.


  Lemma max_var_acc : forall p i j,
      (max_var (i + j) p = max_var i p + j)%positive.
  Proof.
    intros p; induction p as [|? ? IHp|? IHp1 ? ? IHp2]; simpl.
    - reflexivity.
    - intros.
      rewrite ! IHp.
      rewrite Pos.add_assoc.
      reflexivity.
    - intros.
      rewrite !Pplus_one_succ_l.
      rewrite ! IHp1.
      rewrite ! IHp2.
      rewrite ! Pos.add_assoc.
      rewrite <- Pos.add_max_distr_r.
      reflexivity.
  Qed.



  Lemma agree_env_eval_nformula :
    forall env env' e
           (AGREE : agree_env (max_var xH (fst e))  env env'),
      eval_nformula env e  <->  eval_nformula env' e.
  Proof.
    intros env env' e; destruct e as [p o].
    simpl; intros AGREE.
    fold  eval_pol.
    assert ((eval_pol env p)
            =
              (eval_pol env' p)) as H.
    {
      apply has_var_eval.
      intros.
      unfold agree_env in AGREE.
      apply AGREE. apply max_var_correct; auto.
    }
    rewrite H. tauto.
  Qed.

  Lemma agree_env_eval_nformulae :
    forall env env' l
           (AGREE : agree_env (max_var_nformulae l) env env'),
      make_conj (eval_nformula env) l <->
        make_conj (eval_nformula env') l.
  Proof.
    intros env env' l; induction l as [|a l IHl].
    - simpl. tauto.
    - intros.
      rewrite ! make_conj_cons.
      assert (eval_nformula env a <-> eval_nformula env' a) as H.
      {
        apply agree_env_eval_nformula.
        eapply agree_env_subset ; eauto.
        unfold max_var_nformulae.
        simpl.
        rewrite Pos.max_1_l.
        apply max_var_nformulae_mono_aux.
        apply Pos.le_refl.
      }
      rewrite H.
      apply  and_iff_compat_l.
      apply IHl.
      eapply agree_env_subset ; eauto.
      unfold max_var_nformulae.
      simpl.
      apply max_var_nformulae_mono_aux'.
      apply Pos.le_1_l.
  Qed.


  Lemma eq_true_iff_eq :
    forall b1 b2 : bool, (b1 = true <-> b2 = true) <-> b1 = b2.
  Proof.
    intros b1 b2; destruct b1,b2 ; intuition congruence.
  Qed.

  Lemma eval_nformula_split : forall env p,
      eval_nformula env (p,NonStrict) \/ eval_nformula env (popp p,NonStrict).
  Proof.
    unfold popp.
    simpl. intros. rewrite (eval_pol_opp Rsor RSORaddon).
    fold eval_pol.
    destruct (Rle_gt_cases Rsor rO (eval_pol env p)).
    tauto.
    rewrite <- (Ropp_pos_neg Rsor) in H.
    rewrite (SORlt_le_neq Rsor) in H.
    tauto.
  Qed.

  Definition isZenv (z : option PositiveSet.t) (env: positive -> R) :=
    forall x, oget z x = true -> isZ (env x).

  Lemma isZenv_phi_env : forall z env pol,
      isZenv z env ->
      is_integral z pol = true ->
      exists env',
        (phi_env (mem (vars xH pol)) env' env).
  Proof.
    unfold isZenv. intros.
    - pose proof (is_integral_sound pol z H0) as VARS.
      assert (VarsZ : forall x, In x (vars 1 pol) ->  isZ (env x)).
      {
        intros. apply H. now apply VARS.
      }
      assert (forall j,
                 (forall x : positive, In x (vars j pol) -> isZ (env x)) ->
                 exists env', forall x, In x (vars j pol) -> req (env x)  (IZR (env' x))).
      {
        clear H H0 VARS VarsZ.
        induction pol.
        - exists (fun x => Z0).
          simpl. tauto.
        - simpl.
          intros.
          apply IHpol;auto.
        - simpl ; intros.
          assert (Hpol1 : forall x, In x (vars j pol1) -> isZ (env x)).
          {
            intros. apply H.
            rewrite in_app_iff. tauto.
          }
          assert (Hpol2 : forall x, In x (vars (Pos.succ j) pol2) -> isZ (env x)).
          {
            intros. apply H.
            rewrite in_app_iff. tauto.
          }
          apply IHpol1 in Hpol1.
          apply IHpol2 in Hpol2.
          destruct Hpol1 as (e1 & P1).
          destruct Hpol2 as (e2 & P2).
          assert (exists e3, req (env j) (IZR (e3 j))).
          {
            assert (isZ (env j)).
            apply H. tauto.
            destruct H0. exists (fun v => x).
            rewrite H0;reflexivity.
          }
          destruct H0 as (e3 & P3).
          exists (fun x => if In_dec Pos.eq_dec x (vars j pol1)
                           then e1 x else
                             if In_dec Pos.eq_dec x (vars (Pos.succ j) pol2) then e2 x
                             else e3 x).
          intros.
          rewrite in_app_iff in H0.
          destruct (in_dec Pos.eq_dec x (vars j pol1)).
          apply P1; auto.
          destruct (in_dec Pos.eq_dec x (vars (Pos.succ j) pol2)).
          apply P2;auto.
          assert (j = x) by tauto.
          subst. assumption.
      }
      destruct (H1 _ VarsZ) as (env' & EQ).
      exists env'.
      unfold phi_env. intros. now symmetry; apply EQ.
  Qed.


  Lemma Rlt_0_2 : rlt rO (rplus rI rI).
  Proof.
    assert (H : rlt rO rI) by exact (Rlt_0_1 Rsor).
    apply (Rlt_trans Rsor _ rI); try easy.
    rewrite <-(Rplus_0_l Rsor rI) at 1.
    apply (Rplus_lt_le_mono Rsor);try easy.
    apply (SORle_refl Rsor).
  Qed.

  Lemma IPR_xI :
    forall p : positive,
      req (IPR (p~1))
        (rplus
           (rtimes
              (rplus rI rI) (IPR p)) rI).
  Proof.
    intros. simpl. ring.
  Qed.

  Lemma IPR_xO :
    forall p : positive,
      req (IPR (p~0))
        (rtimes
           (rplus rI rI) (IPR p)).
  Proof.
    intros. simpl. ring.
  Qed.

  Lemma Rle_0_1 : rle rO rI.
  Proof.
    rewrite (Rle_lt_eq Rsor).
    left. apply (Rlt_0_1 Rsor).
  Qed.


  Lemma IPR_ge_1 : forall p:positive, rle rI (IPR p).
  Proof.
    pose proof (Rlt_0_1) as H; pose proof (Rlt_0_2) as H'.
    induction p as [p IH | p IH |].
    - rewrite IPR_xI. rewrite  <-( Rplus_0_l Rsor rI) at 1.
      apply (Rplus_le_mono_r Rsor).
      apply (Rtimes_nonneg_nonneg Rsor).
      + generalize Rlt_0_2.
        rewrite (SORlt_le_neq Rsor). tauto.
      + apply (Rle_trans Rsor _ rI); try apply IH.
        apply Rle_0_1.
    - simpl. rewrite  <-(Rplus_0_l Rsor rI).
      apply (Rplus_le_mono Rsor) ; try easy.
      apply (Rle_trans Rsor _ rI); try apply IH.
      apply Rle_0_1.
    - simpl. apply (Rle_refl Rsor).
  Qed.


  Lemma IPR_gt_0 : forall p, rlt rO (IPR p).
  Proof.
    now intros p; apply (Rlt_le_trans Rsor _ rI); [apply (Rlt_0_1 Rsor) | apply IPR_ge_1].
  Qed.

  Lemma eq_IZR_R0 : forall n:Z, req (IZR n) rO -> n = 0%Z.
  Proof.
    intros.
    destruct n as [| p | p]; unfold IZR; simpl in H; try easy.
    - exfalso; apply (Rlt_neq Rsor rO (IPR p)). try easy; apply IPR_gt_0.
      rewrite H ; reflexivity.
    - exfalso; apply (Rlt_neq Rsor rO (IPR p)); try apply IPR_gt_0; symmetry.
      apply (SORopp_wd Rsor) in H.
      setoid_replace  (ropp (ropp (IPR p))) with (IPR p)  in H by ring.
      rewrite H. ring.
  Qed.

  Lemma eq_IZR : forall n m:Z, req (IZR n)  (IZR m) -> n = m.
  Proof.
    intros n m H.
    rewrite <- (Rminus_eq_0 Rsor) in H.
    rewrite <- (morph_sub (SORrm RSORaddon)) in H.
    apply Zminus_eq. now apply eq_IZR_R0.
  Qed.


  Lemma Rlt_irrefl : forall r, ~ rlt r r.
  Proof.
    intros r H.
    intros. rewrite (Rlt_nge Rsor) in H.
    apply H. apply (Rle_refl Rsor).
  Qed.

  Lemma lt_0_IZR : forall n:Z, rlt rO (IZR n) -> (0 < n)%Z.
  Proof.
    intros.
    revert n H.
    intros [| p | p]; simpl; intros H.
    - destruct (Rlt_irrefl _ H).
    - now constructor.
    -
      rewrite  (Rlt_nge Rsor _ _) in H.
      destruct H.
      apply (Rle_lt_eq Rsor).
      left.
      setoid_replace rO with (ropp rO) by ring.
      rewrite <- (Ropp_lt_mono Rsor).
      apply IPR_gt_0.
  Qed.



  Lemma lt_IZR : forall n m:Z, rlt (IZR n) (IZR m) -> (n < m)%Z.
  Proof.
    intros z1 z2 H; apply Z.lt_0_sub.
    apply lt_0_IZR.
    rewrite (morph_sub (SORrm RSORaddon)).
    apply (Rlt_lt_minus Rsor) in H;auto.
  Qed.

  Lemma le_IZR : forall n m:Z, rle (IZR n) (IZR m) -> (n <= m)%Z.
  Proof.
    intros.
    rewrite (Rle_lt_eq Rsor) in H.
    destruct H as [H%lt_IZR | ->%eq_IZR].
    - now apply Z.lt_le_incl.
    - now apply Z.le_refl.
  Qed.

  Lemma Zeval_nformula_iff : forall env' env f,
      phi_env (mem (vars 1 (fst f))) env' env ->
      eval_nformula env f <-> Zeval_nformula env' f.
  Proof.
    intros.
    unfold Zeval_nformula, eval_nformula,RingMicromega.eval_nformula.
    fold eval_pol. fold Zeval_pol.
    destruct f as (p,o).
    apply eval_Zpol_phi in H.
    destruct o ; simpl in *;
      fold Zeval_pol; rewrite <- H.
    - split ; intros.
      apply eq_IZR;auto.
      rewrite H0; reflexivity.
    - split ; repeat intro.
      apply H0. rewrite H1;reflexivity.
      apply H0. now apply eq_IZR.
    - split ; intros.
      apply lt_IZR;auto.
      rewrite (SORlt_le_neq Rsor).
      split.
      change rO with (IZR 0).
      apply (SORcleb_morph RSORaddon).
      apply Z.lt_le_incl in H0.
      now apply Zbool.Zle_is_le_bool.
      change rO with (IZR 0).
      apply (SORcneqb_morph RSORaddon).
      rewrite Z.eqb_neq.
      intro. rewrite <- H1 in H0.
      eapply Z.lt_irrefl;eauto.
    - split ; intros.
      apply le_IZR;auto.
      change rO with (IZR 0).
      apply (SORcleb_morph RSORaddon).
      now apply Zbool.Zle_is_le_bool.
  Qed.




  Lemma vars_of_Zdiv_pol : forall z pol j x,
      In x (vars j (Zdiv_pol pol z)) ->
      In x (vars j pol).
  Proof.
    induction pol; simpl.
    - auto.
    - simpl; auto.
    - intros.
      rewrite in_app_iff in *.
      destruct H as [H| [H |H]].
      + tauto.
      + right. left;auto.
      + right. right. auto.
  Qed.


  Lemma vars_of_PsubC : forall z pol j x,
      In x (vars j (PsubC Z.sub pol z)) ->
      In x (vars j pol).
  Proof.
    induction pol;simpl; auto.
    - intros.
      rewrite in_app_iff in *.
      intuition auto.
  Qed.

  Lemma vars_of_makeCuttingPlane : forall pol pol' c',
      makeCuttingPlane pol = (pol', c') ->
      forall x, In x (vars 1 pol') ->
                In x (vars 1 pol).
  Proof.
    unfold makeCuttingPlane.
    intros. destruct (Zgcd_pol pol).
    destruct (z >? 0); try congruence.
    inv H.
    now apply vars_of_Zdiv_pol, vars_of_PsubC   in H0.
  Qed.


  Lemma vars_of_cutting_plane : forall f p,
      genCuttingPlane f = Some p ->
      forall x,
        In x (vars xH (fst (fst p))) -> In x (vars xH (fst f)).
  Proof.
    unfold genCuttingPlane.
    destruct f as (pol,op).
    destruct op.
    - intros.
      destruct (Zgcd_pol pol) as (g,c) eqn:GCD.
      destruct ((g >? 0) && (negb (c =? 0) && negb (Z.gcd g c =? g)));
        try discriminate.
      simpl. destruct (makeCuttingPlane pol) as (pol',c') eqn:CUT.
      inv H.
      simpl in H0.
      now apply vars_of_makeCuttingPlane with (x:=x) in CUT.
    - intros. inv H.
      apply H0.
    - intros.
      destruct (makeCuttingPlane (PsubC Z.sub pol 1)) as (pol',c') eqn:CUT.
      inv H.
      simpl in H0.
      apply vars_of_makeCuttingPlane with (x:=x) in CUT;auto.
      now apply vars_of_PsubC in CUT.
    - intros.
      destruct (makeCuttingPlane pol) as (pol',c') eqn:CUT.
      inv H.
      apply vars_of_makeCuttingPlane with (x:=x) in CUT;auto.
  Qed.

  Lemma vars_of_PaddC : forall p j c x,
      In x (vars j (PaddC Z.add p c)) ->
      In x (vars j p).
  Proof.
    induction p; simpl;auto.
    - intros. now apply IHp in H.
    - intros.
      rewrite in_app_iff in *.
      destruct H as [H | [H | H]]; try tauto.
      right. right.
      now apply IHp2 in H.
  Qed.

  Lemma phi_env_subset : forall S1 S2 env' env,
      (forall x, S2 x -> S1 x) ->
      phi_env S1 env' env ->
      phi_env S2 env' env.
  Proof.
    unfold phi_env.
    intros. apply H0;auto.
  Qed.


  Lemma cutting_plane_sound_R : forall env z f p,
      isZenv z env ->
      eval_nformula env f ->
      is_integral z (fst f) = true ->
      genCuttingPlane f = Some p ->
      isZenv z env ->
      eval_nformula env (nformula_of_cutting_plane p).
  Proof.
    intros.
    destruct (isZenv_phi_env z env (fst f) H H1) as (env',EQ).
    rewrite Zeval_nformula_iff with (env':=env').
    apply cutting_plane_sound with (f:=f); auto.
    now rewrite <- Zeval_nformula_iff with (env:=env).
    apply phi_env_subset with (2:=EQ).
    intro.
    unfold mem.
    intros.
    eapply vars_of_cutting_plane ;eauto.
    unfold nformula_of_cutting_plane in H4. destruct p. destruct p.
    simpl in *.
    now apply vars_of_PaddC in H4.
  Qed.

  Lemma  genCuttingPlaneNone_R : forall z env f,
      isZenv z env ->
      is_integral z (fst f) = true ->
      genCuttingPlane f = None ->
      eval_nformula env f -> False.
  Proof.
    intros.
    destruct (isZenv_phi_env z env (fst f) H H0) as (env',EQ).
    rewrite Zeval_nformula_iff with (env':=env') in H2 by assumption.
    revert H2.
    now apply genCuttingPlaneNone.
  Qed.

  Lemma is_integral_popp : forall s p,
      is_integral s p = is_integral s (popp p).
  Proof.
    unfold is_integral.
    destruct s as [s|]; try reflexivity.
    intros  pol.
    generalize xH.
    induction pol; simpl;auto.
    - intros.
      rewrite IHpol1. rewrite IHpol2.
      reflexivity.
  Qed.


  Lemma valid_cut_sign_padd : forall env pol c op,
      valid_cut_sign op = true ->
      Zeval_nformula env (padd pol (Pc c), op) ->
      - c <= Zeval_pol env pol.
  Proof.
    unfold Zeval_nformula.
    unfold RingMicromega.eval_nformula.
    fold eval_pol. intros.
    destruct op; simpl in H ;unfold eval_op1 in H0; try discriminate.
    - intros. rewrite Zeval_pol_add in H0.
      simpl in H0.
      setoid_replace (-c)  with (-c + 0) by ring.
      rewrite <- H0.
      ring_simplify.
      apply (SORle_refl Zsor).
    - rewrite Zeval_pol_add in H0.
      simpl in H0.
      rewrite (SORlt_le_neq Zsor) in H0.
      destruct H0.
      apply (Rplus_le_mono_l Zsor) with (p:= -c) in H0.
      ring_simplify in H0. auto.
    - rewrite Zeval_pol_add in H0.
      simpl in H0.
      apply (Rplus_le_mono_l Zsor) with (p:= - c) in H0.
      ring_simplify in H0. auto.
  Qed.



  Lemma phi_env_merge : forall e1 e2 env S1 S2,
      phi_env (mem S1) e1 env ->
      phi_env (mem S2) e2 env ->
      exists e3, phi_env (mem (S1 ++ S2)) e3 env.
  Proof.
    unfold phi_env.
    intros.
    exists (fun x => if In_dec Pos.eq_dec x S1  then e1 x else e2 x).
    unfold mem in *.
    intros.
    destruct (in_dec Pos.eq_dec x S1).
    apply H;auto.
    rewrite in_app_iff in H1. destruct H1;try tauto.
    apply H0;auto.
  Qed.

  Lemma isZenv_add :
    forall x z env
           (ZX : isZ (env x)),
      isZenv z env ->
      isZenv (add x z) env.
  Proof.
    unfold isZenv in *.
    intros.
    unfold add,oget in H0.
    destruct z.
    - rewrite mem_add in H0.
      destruct (Pos.eq_dec x0 x).
      congruence.
      apply H;auto.
    - now apply H.
  Qed.


  Lemma ZChecker_sound : forall w z l,
      ZChecker z l w = true -> forall env, isZenv z env -> make_impl  (eval_nformula env)  l False.
  Proof.
    intros w; induction w as [w H] using (well_founded_ind (well_founded_ltof _ bdepth)).
    destruct w as [ | w pf | w pf | p pf1 pf2 | w1 w2 pf | x pf].
    - (* DoneProof *)
      simpl. discriminate.
    - (* RatProof *)
      simpl.
      intros z l. case_eq (eval_Psatz l w) ; [| discriminate].
      intros f Hf.
      case_eq (Zunsat f).
      + intros H0 ? ? _.
        apply (checker_nf_sound Rsor RSORaddon l w).
        unfold check_normalised_formulas.  unfold eval_Psatz in Hf. rewrite Hf.
        unfold Zunsat in H0. assumption.
      + intros H0 H1 env HZ.
        assert (make_impl  (eval_nformula env) (f::l) False) as H2.
        { apply H with (2:= H1);auto.
          unfold ltof.
          simpl.
          auto with arith.
        }
        destruct f.
        rewrite <- make_conj_impl in H2.
        rewrite make_conj_cons in H2.
        rewrite <- make_conj_impl.
        intro.
        apply H2.
        split ; auto.
        apply eval_Psatz_sound with (2:= Hf) ; assumption.
    - (* CutProof *)
      simpl.
      intros z l.
      case_eq (eval_Psatz l w) ; [ | discriminate].
      intros f' Hlc.
      destruct (is_integral z (fst f')) eqn:INT.
      case_eq (genCuttingPlane f').
      + intros p H0 H1 env HZ.
        rewrite <- make_conj_impl.
        intro.
        apply (eval_Psatz_sound env) in Hlc.
        apply cutting_plane_sound_R with (z:=z)(2:= Hlc) in H0;auto.
        destruct (Zunsat (nformula_of_cutting_plane p)) eqn:UNSAT.
        * eapply Zunsat_sound; eauto.
        *
          assert (make_impl (eval_nformula env) (nformula_of_cutting_plane p::l) False) as HN.
          { eapply (H pf) with (env:=env) in H1 ; auto.
            unfold ltof.
            simpl.
            auto with arith.
          }
          rewrite <- make_conj_impl in HN.
          rewrite make_conj_cons in HN.
          tauto.
        * auto.
      + (* genCuttingPlane = None *)
        intros H0 H1 env.
        rewrite <- make_conj_impl.
        intros ZENV H2.
        apply eval_Psatz_sound with (2:= Hlc) in H2.
        apply genCuttingPlaneNone_R with (z:=z) (4:= H2) ; auto.
      + discriminate.
    - (* SplitProof *)
      intros z l.
      cbn - [genCuttingPlane].
      destruct (is_integral z p) eqn:INT ; [| discriminate].
      case_eq (genCuttingPlane (p, NonStrict)) ; [| discriminate].
      case_eq (genCuttingPlane (popp p, NonStrict)) ; [| discriminate].
      intros cp1 GCP1 cp2 GCP2 ZC1 env ZENV.
      flatten_bool.
      match goal with [ H' : ZChecker _ _ pf1 = true |- _ ] => rename H' into H0 end.
      match goal with [ H' : ZChecker _ _ pf2 = true |- _ ] => rename H' into H1 end.
      destruct (eval_nformula_split env p).
      + apply H with (env:=env) in H0;auto.
        * rewrite <- make_conj_impl in *.
          intro ; apply H0.
          rewrite make_conj_cons. split; auto.
          apply (cutting_plane_sound_R _ z (p,NonStrict)) ; auto.
        * apply ltof_bdepth_split_l.
      + apply H with (env:=env) in H1;auto.
        * rewrite <- make_conj_impl in *.
          intro ; apply H1.
          rewrite make_conj_cons. split; auto.
          apply (cutting_plane_sound_R _ z (popp p,NonStrict)) ; auto.
          rewrite <- INT. symmetry. apply is_integral_popp.
        * apply ltof_bdepth_split_r.
    - (* EnumProof *)
      intros z l.
      simpl.
      case_eq (eval_Psatz l w1) ; [  | discriminate].
      case_eq (eval_Psatz l w2) ; [  | discriminate].
      intros f1 Hf1 f2 Hf2.
      destruct (is_integral z (fst f2) && is_integral z (fst f1)) eqn: isINT; try discriminate.
      rewrite andb_true_iff in isINT.
      destruct isINT as (INT1 & INT2).
      case_eq (genCuttingPlane f2).
      + intros p; destruct p as [ [p1 z1] op1].
        case_eq (genCuttingPlane f1).
        * intros p; destruct p as [ [p2 z2] op2].
          case_eq (valid_cut_sign op1 && valid_cut_sign op2 && is_pol_Z0 (padd p1 p2)).
          -- intros Hcond.
             flatten_bool.
             match goal with [ H1 : is_pol_Z0 (padd p1 p2) = true |- _ ] => rename H1 into HZ0 end.
             match goal with [ H2 : valid_cut_sign op1 = true |- _ ] => rename H2 into Hop1 end.
             match goal with [ H3 : valid_cut_sign op2 = true |- _ ] => rename H3 into Hop2 end.
             intros HCutL HCutR Hfix env.
             (* get the bounds of the enum *)
             rewrite <- make_conj_impl.
             intros isZ H0.
             assert (INT1':=INT1).
             assert (INT2':=INT2).
             apply isZenv_phi_env with (env:=env) in INT1.
             apply isZenv_phi_env with (env:=env) in INT2.
             destruct INT1 as (e1 & PHI1).
             destruct INT2 as (e2 & PHI2).
             destruct (phi_env_merge _ _ _ _ _ PHI1 PHI2) as (e3 & PHI3).
             assert (-z1 <=  Zeval_pol e3 p1 <= z2) as H1. {
               split.
               - apply  (eval_Psatz_sound env) in Hf2 ; auto.
                 assert (PHI1' :
                          phi_env (mem (vars 1 (fst f2))) e3 env).
                 { eapply phi_env_subset in PHI3 ;eauto.
                   intros. unfold mem in *.
                   rewrite in_app_iff. tauto.
                 }
                 rewrite Zeval_nformula_iff with (env':=e3)in Hf2 by easy.
                 apply cutting_plane_sound with (1:= Hf2) in HCutR;auto.
                 unfold nformula_of_cutting_plane in HCutR.
                 eapply valid_cut_sign_padd in HCutR; eauto.
               - apply  (eval_Psatz_sound env) in Hf1 ; auto.
                 assert (HCutL' := HCutL).
                 apply cutting_plane_sound_R with (z:=z) (2:= Hf1) in HCutL;auto.
                 unfold nformula_of_cutting_plane in HCutL.
                 rewrite Zeval_nformula_iff with (env':=e3)in HCutL.
                 eapply valid_cut_sign_padd in HCutL; eauto.
                 apply is_pol_Z0_Zeval_pol with (env:=e3) in HZ0.
                 rewrite Zeval_pol_add in HZ0.
                 apply (Rplus_le_mono_l Zsor) with (p:= z2) in HCutL.
                 ring_simplify in HCutL.
                 rewrite <- HZ0 in HCutL.
                 apply (Rplus_le_mono_l Zsor) with (p:= - (Zeval_pol e3 p2)) in HCutL.
                 ring_simplify in HCutL.
                 assumption.
                 {
                   eapply phi_env_subset in PHI3 ;eauto.
                   intros. unfold mem in H1. unfold mem.
                   rewrite in_app_iff. right.
                   simpl in H1.
                   apply vars_of_PaddC in H1.
                   eapply vars_of_cutting_plane in HCutL'; eauto.
                 }
             }
             revert Hfix.
             match goal with
             | |- context[?F pf (-z1) z2 = true] => set (FF := F)
             end.
             intros Hfix.
             assert (HH :forall x, -z1 <= x <= z2 -> exists pr,
                          (In pr pf /\
                             ZChecker z ((PsubC Z.sub p1 x,Equal) :: l) pr = true)%Z). {
               clear HZ0 Hop1 Hop2 HCutL HCutR H0 H1.
               revert Hfix.
               generalize (-z1). clear z1. intro z1.
               revert z1 z2.
               induction pf as [|a pf IHpf];simpl ;intros z1 z2 Hfix x **.
               - revert Hfix.
                 now case (Z.gtb_spec); [ | easy ]; intros LT; elim (Zorder.Zlt_not_le _ _ LT); transitivity x.
               - flatten_bool.
                 match goal with [ H' : _ <= x <= _ |- _ ] => rename H' into H0 end.
                 match goal with [ H' : FF pf (z1 + 1) z2 = true |- _ ] => rename H' into H2 end.
                 destruct (ZArith_dec.Z_le_lt_eq_dec _ _ (proj1 H0)) as [ LT | -> ].
                 2: exists a; auto.
                           rewrite <- Z.le_succ_l in LT.
                           assert (LE: (Z.succ z1 <= x <= z2)%Z) by intuition.
                           elim IHpf with (2:=H2) (3:= LE).
                           + intros x0 ?.
                             exists x0 ; split;tauto.
                           + intros until 1.
                             apply H ; auto.
                             cbv [ltof] in *.
                             cbn [bdepth] in *.
                             eauto using Nat.lt_le_trans, le_n_S, Nat.le_max_r.
             }
             (*/asser *)
             destruct (HH _ H1) as [pr [Hin Hcheker]].
             assert (make_impl (eval_nformula env) ((PsubC Z.sub p1 (Zeval_pol e3 p1),Equal) :: l) False) as H2. {
               eapply (H pr)  ;eauto.
               apply in_bdepth ; auto.
             }
             rewrite <- make_conj_impl in H2.
             apply H2.
             rewrite  make_conj_cons.
             split ;auto.
             unfold  eval_nformula.
             unfold RingMicromega.eval_nformula.
             simpl.
             rewrite (RingMicromega.PsubC_ok Rsor RSORaddon).
             rewrite eval_Zpol_phi with (env':=env).
             fold eval_pol.
             ring.
             eapply phi_env_subset in PHI3;eauto.
             intros. unfold mem in *. rewrite in_app_iff.
             left.
             eapply vars_of_cutting_plane in HCutR; eauto.
             auto. auto.
          -- discriminate.
        * (* No cutting plane *)
          intros H0 H1 H2 env isZ.
          rewrite <- make_conj_impl.
          intros H3.
          apply eval_Psatz_sound with (2:= Hf1) in H3.
          apply genCuttingPlaneNone_R with (z:=z)(4:= H3) ; auto.
      + (* No Cutting plane (bis) *)
        intros H0 H1 env isZ.
        rewrite <- make_conj_impl.
        intros H2.
        apply eval_Psatz_sound with (2:= Hf2) in H2.
        apply genCuttingPlaneNone_R with (z:=z)(4:= H2) ; auto.
    - intros z l.
      unfold ZChecker.
      fold ZChecker.
      set (fr := (max_var_nformulae l)%positive).
      set (z1 := (Pos.succ fr)) in *.
      set (t1 := (Pos.succ z1)) in *.
      destruct ((x <=? fr) && oget z x)%positive eqn:LE ; [|congruence].
      rewrite andb_true_iff in LE.
      destruct LE as (LE1 & LE2).
      intros H0 env isZE.
      assert (VX :=isZE x LE2). unfold isZ in VX.
      destruct VX as (vx & EQ).
      set (env':= fun v => if Pos.eqb v z1
                           then if Z.leb vx 0 then rO else env x
                           else if Pos.eqb v t1
                                then if Z.leb vx 0 then ropp (IZR vx) else rO
                                else env v).
      apply H with (env:=env')  in H0.
      + rewrite <- make_conj_impl in *.
        intro H1.
        rewrite !make_conj_cons in H0.
        apply H0 ; repeat split.
        *
          apply eval_nformula_mk_eq_pos.
          unfold env'.
          rewrite! Pos.eqb_refl.
          replace (x=?z1)%positive with false.
          1:replace (x=?t1)%positive with false.
          1:replace (t1=?z1)%positive with false.
          1:destruct (vx <=? 0); rewrite <- ?EQ; ring.
          { unfold t1.
            symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; symmetry; apply Pos.succ_discr.
          }
          {
            unfold t1, z1.
            symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; intros ->.
            apply Pos.leb_le, Pos.lt_succ_r in LE1; rewrite <-?Pos.succ_lt_mono in *.
            pose proof Pos.lt_not_add_l fr 1; rewrite Pos.add_1_r in *; contradiction.
          }
          {
            unfold z1.
            symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; intros ->.
            apply Pos.leb_le, Pos.lt_succ_r in LE1; rewrite <-?Pos.succ_lt_mono in *.
            case (Pos.lt_irrefl _ LE1).
          }
        *
          apply eval_nformula_bound_var.
          unfold env'.
          rewrite! Pos.eqb_refl.
          destruct (vx <=? 0) eqn:EQV.
          -- apply (Rle_refl Rsor).
          -- rewrite <- EQ.
             rewrite <- (morph0 (SORrm RSORaddon)).
             apply (SORcleb_morph RSORaddon).
             apply Z.leb_gt   in EQV.
             apply Z.leb_le.
             apply Z.lt_le_incl; trivial.
        *
          apply eval_nformula_bound_var.
          unfold env'.
          rewrite! Pos.eqb_refl.
          replace (t1 =? z1)%positive with false.
          -- destruct (vx <=? 0) eqn:EQ1.
             ++
               rewrite <- (morph0 (SORrm RSORaddon)).
               rewrite <- (morph_opp (SORrm RSORaddon)).
               apply (SORcleb_morph RSORaddon).
               rewrite Z.leb_le in *.
               rewrite Z.opp_le_mono, Z.opp_involutive; trivial.
             ++ apply (Rle_refl Rsor).
          -- unfold t1.
             clear.
             symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; symmetry; apply Pos.succ_discr.
        *
          rewrite (agree_env_eval_nformulae _ env') in H1;auto.
          unfold agree_env; intros x0 H2.
          unfold env'.
          replace (x0 =? z1)%positive with false.
          1:replace (x0 =? t1)%positive with false.
          1:reflexivity.
          {
            unfold t1, z1.
            symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; intros ->.
            apply Pos.lt_succ_r in H2; rewrite <-?Pos.succ_lt_mono in *.
            pose proof Pos.lt_not_add_l (max_var_nformulae l) 1; rewrite Pos.add_1_r in *; contradiction.
          }
          {
            unfold z1, fr in *.
            symmetry; apply not_true_iff_false; rewrite Pos.eqb_eq; intros ->.
            apply Pos.lt_succ_r in H2; rewrite <-?Pos.succ_lt_mono in *.
            case (Pos.lt_irrefl _ H2).
          }
      + unfold ltof.
        simpl.
        apply Nat.lt_succ_diag_r.
      + apply isZenv_add.
        unfold env'. rewrite Pos.eqb_refl.
        unfold isZ. exists (if vx <=? 0 then 0 else vx).
        destruct (vx <=? 0); try easy.
        apply isZenv_add.
        unfold env'.
        replace (t1 =?z1)%positive with false.
        rewrite Pos.eqb_refl.
        unfold isZ. exists (if vx <=? 0 then - vx else 0).
        destruct (vx <=? 0); try easy.
        apply (morph_opp (SORrm RSORaddon)).
        unfold t1,z1.
        symmetry. rewrite Pos.eqb_neq. intro.
        rewrite <- Pos.add_1_l in H1.
        eapply Pos.add_no_neutral; eauto.
        { unfold isZenv.
          intros.
          apply isZE in H1.
          unfold env'.
          destruct ((x0 =? z1)%positive).
          destruct (vx <=? 0); auto.
          exists 0. apply (morph0 (SORrm RSORaddon)).
          destruct ((x0 =? t1)%positive).
          destruct (vx <=? 0).
          apply isZ_ropp. exists vx; reflexivity.
          exists 0. apply (morph0 (SORrm RSORaddon)).
          auto.
        }
  Qed.

End S.

Fixpoint xhyps_of_pt (base:nat) (acc : list nat) (pt:ZArithProof)  : list nat :=
  match pt with
  | DoneProof => acc
  | RatProof c pt => xhyps_of_pt (S base ) (xhyps_of_psatz base acc c) pt
  | CutProof c pt => xhyps_of_pt (S base ) (xhyps_of_psatz base acc c) pt
  | SplitProof p pt1 pt2 => xhyps_of_pt (S base) (xhyps_of_pt (S base) acc pt1) pt2
  | EnumProof c1 c2 l =>
      let acc := xhyps_of_psatz base (xhyps_of_psatz base acc c2) c1 in
      List.fold_left (xhyps_of_pt (S base)) l acc
  | ExProof _ pt  =>  xhyps_of_pt (S (S (S base ))) acc pt
  end.

Definition hyps_of_pt (pt : ZArithProof) : list nat := xhyps_of_pt 0 nil pt.

Open Scope Z_scope.

(** To ease bindings from ml code **)
Definition make_impl := Refl.make_impl.
Definition make_conj := Refl.make_conj.

From Stdlib Require VarMap.

(*Definition varmap_type := VarMap.t Z. *)
Definition env := PolEnv Z.
Definition node := @VarMap.Branch Z.
Definition empty := @VarMap.Empty Z.
Definition leaf := @VarMap.Elt Z.

Definition coneMember := ZWitness.

Definition eval := eval_formula.

#[deprecated(note="Use [prod positive nat]", since="9.0")]
  Definition prod_pos_nat := prod positive nat.

#[deprecated(use=Z.to_N, since="9.0")]
  Notation n_of_Z := Z.to_N (only parsing).
