(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** An alternative to [zify] in ML parametrised by user-provided classes instances.

    The framework has currently several limitations that are in place for simplicity.
    For instance, we only consider binary operators of type [Op: S -> S -> S].
    Another limitation is that our injection theorems e.g. [TBOpInj],
    are using Leibniz equality; the payoff is that there is no need for morphisms...
 *)

(** An injection [InjTyp S T] declares an injection
    from source type S to target type T.
*)
Class InjTyp (S : Type) (T : Type) :=
  mkinj {
      (* [inj] is the injection function *)
      inj  : S -> T;
      pred : T -> Prop;
      (* [cstr] states that [pred] holds for any injected element.
         [cstr (inj x)] is introduced in the goal for any leaf
         term of the form [inj x]
       *)
      cstr : forall x, pred (inj x)
    }.

(** [BinOp Op] declares a source operator [Op: S1 -> S2 -> S3].
 *)
Class BinOp {S1 S2 S3 T1 T2 T3:Type} (Op : S1 -> S2 -> S3) {I1 : InjTyp S1 T1} {I2 : InjTyp S2 T2} {I3 : InjTyp S3 T3} :=
  mkbop {
      (* [TBOp] is the target operator after injection of operands. *)
      TBOp : T1 -> T2 -> T3;
      (* [TBOpInj] states the correctness of the injection. *)
      TBOpInj : forall (n:S1) (m:S2), inj (Op n m) = TBOp (inj n) (inj m)
    }.

(** [Unop Op] declares a source operator [Op : S1 -> S2]. *)
Class UnOp {S1 S2 T1 T2:Type} (Op : S1 -> S2) {I1 : InjTyp S1 T1} {I2 : InjTyp S2 T2}  :=
  mkuop {
      (* [TUOp] is the target operator after injection of operands. *)
      TUOp : T1 -> T2;
      (* [TUOpInj] states the correctness of the injection. *)
      TUOpInj : forall (x:S1), inj (Op x) = TUOp (inj x)
    }.

(** [CstOp Op] declares a source constant [Op : S]. *)
Class CstOp {S T:Type} (Op : S) {I : InjTyp S T} :=
  mkcst {
      (* [TCst] is the target constant. *)
      TCst : T;
      (* [TCstInj] states the correctness of the injection. *)
      TCstInj : inj Op = TCst
    }.

(** In the framework, [Prop] is mapped to [Prop] and the injection is phrased in
    terms  of [=] instead of [<->].
*)

(** [BinRel R] declares the injection of a binary relation. *)
Class BinRel {S:Type} {T:Type} (R : S -> S -> Prop) {I : InjTyp S T}  :=
    mkbrel {
        TR : T -> T -> Prop;
        TRInj : forall n m : S, R n m <->  TR (@inj _ _ I n) (inj m)
      }.

(** [PropOp Op] declares morphisms for [<->].
    This will be used to deal with e.g. [and], [or],... *)

Class PropOp (Op : Prop -> Prop -> Prop) :=
  mkprop {
      op_iff : forall (p1 p2 q1 q2:Prop), (p1 <-> q1) -> (p2 <-> q2) -> (Op p1 p2 <-> Op q1 q2)
    }.

Class PropUOp (Op : Prop -> Prop) :=
  mkuprop {
      uop_iff :   forall (p1 q1 :Prop), (p1 <-> q1) -> (Op p1 <-> Op q1)
    }.



(** Once the term is injected, terms can be replaced by their specification.
    NB1: The Ltac code is currently limited to (Op: Z -> Z -> Z)
    NB2: This is not sufficient to cope with [Z.div] or [Z.mod]
 *)
Class BinOpSpec {T1 T2 T3: Type} (Op : T1 -> T2 -> T3)  :=
  mkbspec {
      BPred : T1 -> T2 -> T3 -> Prop;
      BSpec : forall x y, BPred x y (Op x y)
    }.

Class UnOpSpec {T1 T2: Type} (Op : T1 -> T2)  :=
  mkuspec {
      UPred : T1 -> T2 -> Prop;
      USpec : forall x, UPred x (Op x)
    }.

(** After injections, e.g. nat -> Z,
    the fact that Z.of_nat x * Z.of_nat y is positive is lost.
    This information can be recovered using instance of the  [Saturate] class.
*)
Class Saturate {T: Type} (Op : T -> T -> T) :=
  mksat {
      (** Given [Op x y],
          - [PArg1] is the pre-condition of x
          - [PArg2] is the pre-condition of y
          - [PRes]  is the pos-condition of (Op x y) *)
      PArg1 : T -> Prop;
      PArg2 : T -> Prop;
      PRes  : T -> T -> T -> Prop;
      (** [SatOk] states the correctness of the reasoning *)
      SatOk : forall x y, PArg1 x -> PArg2 y -> PRes x y (Op x y)
    }.
(* )Arguments PRes {_ _} _. *)

(* The [ZifyInst.saturate] iterates over all the instances
   and for every pattern of the form
   [H1 : PArg1 ?x , H2 : PArg2 ?y , T : context[Op ?x ?y] |- _ ]
   [H1 : PArg1 ?x , H2 : PArg2 ?y |- context[Op ?x ?y] ]
   asserts  (SatOK x y H1 H2) *)

(** The rest of the file is for internal use by the ML tactic.
    There are  data-structures and lemmas used to inductively construct
    the injected terms. *)

(** The data-structures [injterm] and [injected_prop]
    are used to store source and target expressions together
    with a correctness proof. *)

Record injterm {S T: Type} (I : S -> T) :=
  mkinjterm { source : S ; target : T ; inj_ok : I source = target}.

Record injprop  :=
  mkinjprop {
      source_prop : Prop ; target_prop : Prop ;
      injprop_ok : source_prop <-> target_prop}.


(** Lemmas for building rewrite rules. *)

Definition PropOp_iff (Op : Prop -> Prop -> Prop) :=
  forall (p1 p2 q1 q2:Prop), (p1 <-> q1) -> (p2 <-> q2) -> (Op p1 p2 <-> Op q1 q2).

Definition PropUOp_iff (Op : Prop -> Prop) :=
  forall (p1 q1 :Prop), (p1 <-> q1) -> (Op p1 <-> Op q1).

Lemma mkapp2 (S1 S2 S3 T1 T2 T3 : Type) (Op : S1 -> S2 -> S3)
      (I1 : S1 -> T1) (I2 : S2 -> T2) (I3 : S3 -> T3)
      (TBOP : T1 -> T2 -> T3)
      (TBOPINJ : forall n m, I3 (Op n m) = TBOP (I1 n) (I2 m))
      (s1 : S1) (t1 : T1) (P1: I1 s1 = t1)
      (s2 : S2) (t2 : T2) (P2: I2 s2 = t2):  I3 (Op s1 s2) = TBOP t1 t2.
Proof.
  subst. apply TBOPINJ.
Qed.

Lemma mkapp (S1 S2 T1 T2 : Type) (OP : S1 -> S2)
      (I1 : S1 -> T1)
      (I2 : S2 -> T2)
      (TUOP : T1 -> T2)
      (TUOPINJ : forall n, I2 (OP n) = TUOP (I1 n))
      (s1: S1) (t1: T1) (P1: I1 s1 = t1): I2 (OP s1) = TUOP t1.
Proof.
  subst. apply TUOPINJ.
Qed.

Lemma mkrel (S T : Type) (R : S -> S -> Prop)
      (I : S -> T)
      (TR : T -> T -> Prop)
      (TRINJ : forall n m : S, R n m <->  TR (I n) (I m))
      (s1 : S) (t1 : T) (P1 : I s1 = t1)
      (s2 : S) (t2 : T) (P2 : I s2 = t2):
   R s1 s2 <-> TR t1 t2.
Proof.
  subst.
  apply TRINJ.
Qed.

(** Hardcoded support and lemma for propositional logic *)

Lemma and_morph : forall (s1 s2 t1 t2:Prop), s1 <-> t1 -> s2 <-> t2 -> ((s1 /\ s2) <-> (t1 /\ t2)).
Proof.
  intros. tauto.
Qed.

Lemma or_morph : forall (s1 s2 t1 t2:Prop), s1 <-> t1 -> s2 <-> t2 -> ((s1 \/ s2) <-> (t1 \/ t2)).
Proof.
  intros. tauto.
Qed.

Lemma impl_morph : forall (s1 s2 t1 t2:Prop), s1 <-> t1 -> s2 <-> t2 -> ((s1 -> s2) <-> (t1 -> t2)).
Proof.
  intros. tauto.
Qed.

Lemma iff_morph : forall (s1 s2 t1 t2:Prop), s1 <-> t1 -> s2 <-> t2 -> ((s1 <-> s2) <-> (t1 <-> t2)).
Proof.
  intros. tauto.
Qed.

Lemma not_morph : forall (s1 t1:Prop), s1 <-> t1 ->   (not s1) <-> (not t1).
Proof.
  intros. tauto.
Qed.

Lemma eq_iff : forall (P Q : Prop), P = Q -> (P <-> Q).
Proof.
  intros P Q H.
  rewrite H.
  apply iff_refl.
Defined.

Lemma rew_iff  (P Q : Prop) (IFF : P <-> Q) :  P -> Q.
Proof.
  exact (fun H => proj1 IFF H).
Qed.

Lemma rew_iff_rev  (P Q : Prop) (IFF : P <-> Q) :  Q -> P.
Proof.
  exact (fun H => proj2 IFF H).
Qed.



(** Registering constants for use by the plugin *)
Register eq_iff      as TifyClasses.eq_iff.
Register target_prop as TifyClasses.target_prop.
Register mkrel       as TifyClasses.mkrel.
Register target      as TifyClasses.target.
Register mkapp2      as TifyClasses.mkapp2.
Register mkapp       as TifyClasses.mkapp.
Register op_iff      as TifyClasses.op_iff.
Register uop_iff     as TifyClasses.uop_iff.
Register TR          as TifyClasses.TR.
Register TBOp        as TifyClasses.TBOp.
Register TUOp        as TifyClasses.TUOp.
Register TCst        as TifyClasses.TCst.
Register injprop_ok  as TifyClasses.injprop_ok.
Register inj_ok      as TifyClasses.inj_ok.
Register source      as TifyClasses.source.
Register source_prop as TifyClasses.source_prop.
Register inj         as TifyClasses.inj.
Register TRInj       as TifyClasses.TRInj.
Register TUOpInj     as TifyClasses.TUOpInj.
Register not         as TifyClasses.not.
Register mkinjterm   as TifyClasses.mkinjterm.
Register eq_refl     as TifyClasses.eq_refl.
Register eq          as TifyClasses.eq.
Register mkinjprop   as TifyClasses.mkinjprop.
Register iff_refl    as TifyClasses.iff_refl.
Register rew_iff     as TifyClasses.rew_iff.
Register rew_iff_rev as TifyClasses.rew_iff_rev.
Register source_prop as TifyClasses.source_prop.
Register injprop_ok  as TifyClasses.injprop_ok.
Register iff         as TifyClasses.iff.

Register InjTyp      as TifyClasses.InjTyp.
Register BinOp       as TifyClasses.BinOp.
Register UnOp        as TifyClasses.UnOp.
Register CstOp       as TifyClasses.CstOp.
Register BinRel      as TifyClasses.BinRel.
Register PropOp   as TifyClasses.PropOp.
Register PropUOp     as TifyClasses.PropUOp.
Register BinOpSpec   as TifyClasses.BinOpSpec.
Register UnOpSpec    as TifyClasses.UnOpSpec.
Register Saturate    as TifyClasses.Saturate.


(** Propositional logic *)
Register and as TifyClasses.and.
Register and_morph as TifyClasses.and_morph.
Register or as TifyClasses.or.
Register or_morph as TifyClasses.or_morph.
Register iff as TifyClasses.iff.
Register iff_morph as TifyClasses.iff_morph.
Register impl_morph as TifyClasses.impl_morph.
Register not as TifyClasses.not.
Register not_morph as TifyClasses.not_morph.
Register True as TifyClasses.True.
Register I as TifyClasses.I.
