(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


Set Implicit Arguments.
From Stdlib Require Export ring_checker.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import BinList BinPos BinNat BinInt.
From Stdlib Require Export Ring_theory.
#[local] Open Scope positive_scope.
Import RingSyntax.
(* Set Universe Polymorphism. *)

Section MakeRingPol.

 (* Ring elements *)
 Variable R:Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R->R).
 Variable req : R -> R -> Prop.

 (* Ring properties *)
 Variable Rsth : Equivalence req.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
 Variable ARth : almost_ring_theory rO rI radd rmul rsub ropp req.

 (* Coefficients *)
 Variable C: Type.
 Variable (cO cI: C) (cadd cmul csub : C->C->C) (copp : C->C).
 Variable ceqb : C->C->bool.
 Variable phi : C -> R.
 Variable CRmorph : ring_morph rO rI radd rmul rsub ropp req
                                cO cI cadd cmul csub copp ceqb phi.

 (* Power coefficients *)
 Variable Cpow : Type.
 Variable Cp_phi : N -> Cpow.
 Variable rpow : R -> Cpow -> R.
 Variable pow_th : power_theory rI rmul req Cp_phi rpow.

 (* division is ok *)
 Variable cdiv: C -> C -> C * C.
 Variable div_th: div_theory req cadd cmul phi cdiv.


 (* R notations *)
 Notation "0" := rO. Notation "1" := rI.
 Infix "+" := radd. Infix "*" := rmul.
 Infix "-" := rsub. Notation "- x" := (ropp x).
 Infix "==" := req.
 Infix "^" := (pow_pos rmul).

 (* C notations *)
 Infix "+!" := cadd. Infix "*!" := cmul.
 Infix "-! " := csub. Notation "-! x" := (copp x).
 Infix "?=!" := ceqb. Notation "[ x ]" := (phi x).

 (* Useful tactics *)
 Add Morphism radd with signature (req ==> req ==> req) as radd_ext.
 Proof. exact (Radd_ext Reqe). Qed.

 Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext.
 Proof. exact (Rmul_ext Reqe). Qed.

 Add Morphism ropp with signature (req ==> req) as ropp_ext.
 Proof. exact (Ropp_ext Reqe). Qed.

 Add Morphism rsub with signature (req ==> req ==> req) as rsub_ext.
 Proof. exact (ARsub_ext Rsth Reqe ARth). Qed.

 Ltac rsimpl := gen_srewrite Rsth Reqe ARth.

 Ltac add_push := gen_add_push radd Rsth Reqe ARth.
 Ltac mul_push := gen_mul_push rmul Rsth Reqe ARth.

 Ltac add_permut_rec t :=
   match t with
   | ?x + ?y => add_permut_rec y || add_permut_rec x
   | _ => add_push t; apply (Radd_ext Reqe); [|reflexivity]
   end.

 Ltac add_permut :=
  repeat (reflexivity ||
    match goal with |- ?t == _ => add_permut_rec t end).

 Ltac mul_permut_rec t :=
   match t with
   | ?x * ?y => mul_permut_rec y || mul_permut_rec x
   | _ => mul_push t; apply (Rmul_ext Reqe); [|reflexivity]
   end.

 Ltac mul_permut :=
  repeat (reflexivity ||
    match goal with |- ?t == _ => mul_permut_rec t end).


 (* Definition of multivariable polynomials with coefficients in C *)

 #[local] Notation Pol := (Pol C).
 #[local] Notation P0 := (P0 cO).
 #[local] Notation P1 := (P1 cI).
 #[local] Notation Peq := (Peq ceqb).
 #[local] Notation mkX := (mkX cO cI).
 #[local] Notation mkPinj := (@mkPinj C).
 #[local] Notation mkPX := (mkPX cO ceqb).
 #[local] Notation Popp := (Popp copp).
 #[local] Notation PaddC := (PaddC cadd).
 #[local] Notation PsubC := (PsubC csub).
 #[local] Notation Padd := (Padd cO cadd ceqb).
 #[local] Notation PaddI := (PaddI cadd Padd).
 #[local] Notation Psub := (Psub cO cadd csub copp ceqb).
 #[local] Notation PsubI := (PsubI cadd copp Psub).
 #[local] Notation PaddX := (PaddX cO ceqb Padd).
 #[local] Notation PsubX := (PsubX cO copp ceqb Psub).
 #[local] Notation PmulC_aux := (PmulC_aux cO cmul ceqb).
 #[local] Notation PmulC := (PmulC cO cI cmul ceqb).
 #[local] Notation Pmul := (Pmul cO cI cadd cmul ceqb).
 #[local] Notation PmulI := (PmulI cO cI cmul ceqb Pmul).

 Infix "?==" := Peq.
 Notation "-- P" := (Popp P).
 Infix "++" := Padd.
 Infix "--" := Psub.
 Infix "**" := Pmul.

 (** Monomial **)

 #[local] Notation CFactor := (CFactor cO ceqb cdiv).
 #[local] Notation MFactor := (MFactor cO cI ceqb cdiv).
 #[local] Notation POneSubst := (POneSubst cO cI cadd cmul ceqb cdiv).
 #[local] Notation PNSubst1 := (PNSubst1 cO cI cadd cmul ceqb cdiv).
 #[local] Notation PNSubst := (PNSubst cO cI cadd cmul ceqb cdiv).
 #[local] Notation PSubstL1 := (PSubstL1 cO cI cadd cmul ceqb cdiv).
 #[local] Notation PSubstL := (PSubstL cO cI cadd cmul ceqb cdiv).
 #[local] Notation PNSubstL := (PNSubstL cO cI cadd cmul ceqb cdiv).

 (** Evaluation of a polynomial towards R *)

 #[local] Notation hd := (List.hd 0).

 Fixpoint Pphi(l:list R) (P:Pol) : R :=
  match P with
  | Pc c => [c]
  | Pinj j Q => Pphi (jump j l) Q
  | PX P i Q => Pphi l P * (hd l) ^ i + Pphi (tail l) Q
  end.

 Reserved Notation "P @ l " (at level 10, no associativity).
 Notation "P @ l " := (Pphi l P).

 Definition Pequiv (P Q : Pol) := forall l, P@l == Q@l.
 Infix "===" := Pequiv (at level 70, no associativity).

 Instance Pequiv_eq : Equivalence Pequiv.
 Proof.
  unfold Pequiv; split; red; intros; [reflexivity|now symmetry|now etransitivity].
 Qed.

 Instance Pphi_ext : Proper (eq ==> Pequiv ==> req) Pphi.
 Proof.
  now intros l l' <- P Q H.
 Qed.

 Instance Pinj_ext : Proper (eq ==> Pequiv ==> Pequiv) Pinj.
 Proof.
  intros i j <- P P' HP l. simpl. now rewrite HP.
 Qed.

 Instance PX_ext : Proper (Pequiv ==> eq ==> Pequiv ==> Pequiv) PX.
 Proof.
  intros P P' HP p p' <- Q Q' HQ l. simpl. now rewrite HP, HQ.
 Qed.

 (** Evaluation of a monomial towards R *)

 Fixpoint Mphi(l:list R) (M: Mon) : R :=
  match M with
  | mon0 => rI
  | zmon j M1 => Mphi (jump j l) M1
  | vmon i M1 => Mphi (tail l) M1 * (hd l) ^ i
  end.

 Notation "M @@ l" := (Mphi l M) (at level 10, no associativity).

 (** Proofs *)

 Ltac destr_pos_sub :=
  match goal with |- context [Z.pos_sub ?x ?y] =>
   generalize (Z.pos_sub_discr x y); destruct (Z.pos_sub x y)
  end.

 Lemma jump_add' i j (l:list R) : jump (i + j) l = jump j (jump i l).
 Proof. rewrite Pos.add_comm. apply jump_add. Qed.

 Lemma Peq_ok P P' : (P ?== P') = true -> P === P'.
 Proof.
  unfold Pequiv.
  revert P';induction P as [|p P IHP|P2 IHP1 p P3 IHP2];
   intros P';destruct P' as [|p0 P'|P'1 p0 P'2];simpl;
   intros H l; try easy.
  - now apply (morph_eq CRmorph).
  - destruct (Pos.compare_spec p p0); [ subst | easy | easy ].
    now rewrite IHP.
  - specialize (IHP1 P'1); specialize (IHP2 P'2).
    destruct (Pos.compare_spec p p0); [ subst | easy | easy ].
    destruct (P2 ?== P'1); [|easy].
    rewrite H in *.
    now rewrite IHP1, IHP2.
 Qed.

 Lemma Peq_spec P P' : BoolSpec (P === P') True (P ?== P').
 Proof.
  generalize (Peq_ok P P'). destruct (P ?== P'); auto.
 Qed.

 Lemma Pphi0 l : P0@l == 0.
 Proof.
  simpl;apply (morph0 CRmorph).
 Qed.

 Lemma Pphi1 l : P1@l == 1.
 Proof.
  simpl;apply (morph1 CRmorph).
 Qed.

 Lemma mkPinj_ok j l P : (mkPinj j P)@l == P@(jump j l).
 Proof.
  destruct P;simpl;rsimpl.
  now rewrite jump_add'.
 Qed.

 Instance mkPinj_ext : Proper (eq ==> Pequiv ==> Pequiv) mkPinj.
 Proof.
  intros i j <- P Q H l. now rewrite !mkPinj_ok.
 Qed.

 Lemma pow_pos_add x i j : x^(j + i) == x^i * x^j.
 Proof.
  rewrite Pos.add_comm.
  apply (pow_pos_add Rsth (Rmul_ext Reqe) (ARmul_assoc ARth)).
 Qed.

 Lemma ceqb_spec c c' : BoolSpec ([c] == [c']) True (c ?=! c').
 Proof.
  generalize (morph_eq CRmorph c c').
  destruct (c ?=! c'); auto.
 Qed.

 Lemma mkPX_ok l P i Q :
  (mkPX P i Q)@l == P@l * (hd l)^i + Q@(tail l).
 Proof.
  unfold mkPX. destruct P.
  - case ceqb_spec; intros H; simpl; try reflexivity.
    rewrite H, (morph0 CRmorph), mkPinj_ok; rsimpl.
  - reflexivity.
  - case Peq_spec; intros H; simpl; try reflexivity.
    rewrite H, Pphi0, Pos.add_comm, pow_pos_add; rsimpl.
 Qed.

 Instance mkPX_ext : Proper (Pequiv ==> eq ==> Pequiv ==> Pequiv) mkPX.
 Proof.
  intros P P' HP i i' <- Q Q' HQ l. now rewrite !mkPX_ok, HP, HQ.
 Qed.

 Hint Rewrite
  Pphi0
  Pphi1
  mkPinj_ok
  mkPX_ok
  (morph0 CRmorph)
  (morph1 CRmorph)
  (morph0 CRmorph)
  (morph_add CRmorph)
  (morph_mul CRmorph)
  (morph_sub CRmorph)
  (morph_opp CRmorph)
  : Esimpl.

 (* Quicker than autorewrite with Esimpl :-) *)
 Ltac Esimpl := try rewrite_db Esimpl; rsimpl; simpl.

 Lemma PaddC_ok c P l : (PaddC P c)@l == P@l + [c].
 Proof.
  revert l;induction P as [| |P2 IHP1 p P3 IHP2];simpl;intros;Esimpl;trivial.
  rewrite IHP2;rsimpl.
 Qed.

 Lemma PsubC_ok c P l : (PsubC P c)@l == P@l - [c].
 Proof.
  revert l;induction P as [|p P IHP|P2 IHP1 p P3 IHP2];simpl;intros.
  - Esimpl.
  - rewrite IHP;rsimpl.
  - rewrite IHP2;rsimpl.
 Qed.

 Lemma PmulC_aux_ok c P l : (PmulC_aux P c)@l == P@l * [c].
 Proof.
  revert l;induction P as [| |P2 IHP1 p P3 IHP2];simpl;intros;Esimpl;trivial.
  rewrite IHP1, IHP2;rsimpl. add_permut. mul_permut.
 Qed.

 Lemma PmulC_ok c P l : (PmulC P c)@l == P@l * [c].
 Proof.
  unfold PmulC.
  case ceqb_spec; intros H.
  - rewrite H; Esimpl.
  - case ceqb_spec; intros H'.
    + rewrite H'; Esimpl.
    + apply PmulC_aux_ok.
 Qed.

 Lemma Popp_ok P l : (--P)@l == - P@l.
 Proof.
  revert l;induction P as [|p P IHP|P2 IHP1 p P3 IHP2];simpl;intros.
  - Esimpl.
  - apply IHP.
  - rewrite IHP1, IHP2;rsimpl.
 Qed.

 Hint Rewrite PaddC_ok PsubC_ok PmulC_ok Popp_ok : Esimpl.

 Lemma PaddX_ok P' P k l :
  (forall P l, (P++P')@l == P@l + P'@l) ->
  (PaddX P' k P) @ l == P@l + P'@l * (hd l)^k.
 Proof.
  intros IHP'.
  revert k l. induction P as [|p P IHP|P2 IHP1 p P3 IHP2];simpl;intros.
  - add_permut.
  - destruct p; simpl;
    rewrite ?jump_pred_double; add_permut.
  - destr_pos_sub; intros ->; Esimpl.
    + rewrite IHP';rsimpl. add_permut.
    + rewrite IHP', pow_pos_add;simpl;Esimpl. add_permut.
    + rewrite IHP1, pow_pos_add;rsimpl. add_permut.
 Qed.

 Lemma Padd_ok P' P l : (P ++ P')@l == P@l + P'@l.
 Proof.
  revert P l; induction P' as [|p P' IHP'|P'1 IHP'1 p P'2 IHP'2];
   simpl;intros P l;Esimpl.
  - revert p l; induction P as [|p P IHP|P2 IHP1 p P3 IHP2];simpl;intros p0 l.
    + Esimpl; add_permut.
    + destr_pos_sub; intros ->;Esimpl.
      * now rewrite IHP'.
      * rewrite IHP';Esimpl. now rewrite jump_add'.
      * rewrite IHP. now rewrite jump_add'.
    + destruct p0;simpl.
      * rewrite IHP2;simpl. rsimpl.
      * rewrite IHP2;simpl. rewrite jump_pred_double. rsimpl.
      * rewrite IHP'. rsimpl.
  - destruct P as [|p0 ?|? ? ?];simpl.
    + Esimpl. add_permut.
    + destruct p0;simpl;Esimpl; rewrite IHP'2; simpl.
      * rsimpl. add_permut.
      * rewrite jump_pred_double. rsimpl. add_permut.
      * rsimpl. add_permut.
    + destr_pos_sub; intros ->; Esimpl.
      * rewrite IHP'1, IHP'2;rsimpl. add_permut.
      * rewrite IHP'1, IHP'2;simpl;Esimpl.
        rewrite pow_pos_add;rsimpl. add_permut.
      * rewrite PaddX_ok by trivial; rsimpl.
        rewrite IHP'2, pow_pos_add; rsimpl. add_permut.
 Qed.

 Lemma Psub_opp P' P : P -- P' === P ++ (--P').
 Proof.
  revert P; induction P' as [|p P' IHP'|P'1 IHP'1 p P'2 IHP'2]; simpl; intros P.
  - intro l; Esimpl.
  - revert p; induction P; simpl; intros p0; try reflexivity.
    + destr_pos_sub; intros ->; now apply mkPinj_ext.
    + destruct p0; now apply PX_ext.
  - destruct P as [|p0 P|P2 p0 P3]; simpl; try reflexivity.
    + destruct p0; now apply PX_ext.
    + destr_pos_sub; intros ->; apply mkPX_ext; auto.
      revert p1. induction P2; simpl; intros; try reflexivity.
      destr_pos_sub; intros ->; now apply mkPX_ext.
 Qed.

 Lemma Psub_ok P' P l : (P -- P')@l == P@l - P'@l.
 Proof.
  rewrite Psub_opp, Padd_ok, Popp_ok. rsimpl.
 Qed.

 Lemma PmulI_ok P' :
   (forall P l, (Pmul P P') @ l == P @ l * P' @ l) ->
   forall P p l, (PmulI P' p P) @ l == P @ l * P' @ (jump p l).
 Proof.
  intros IHP' P.
  induction P as [|p P IHP|? IHP1 ? ? IHP2];simpl;intros p0 l.
  - Esimpl; mul_permut.
  - destr_pos_sub; intros ->;Esimpl.
    + now rewrite IHP'.
    + now rewrite IHP', jump_add'.
    + now rewrite IHP, jump_add'.
  - destruct p0;Esimpl; rewrite ?IHP1, ?IHP2; rsimpl.
    + f_equiv. mul_permut.
    + rewrite jump_pred_double. f_equiv. mul_permut.
    + rewrite IHP'. f_equiv. mul_permut.
 Qed.

 Lemma Pmul_ok P P' l : (P**P')@l == P@l * P'@l.
 Proof.
  revert P l;induction P' as [| |? IHP'1 ? ? IHP'2];simpl;intros P l.
  - apply PmulC_ok.
  - apply PmulI_ok;trivial.
  - destruct P as [|p0|].
    + rewrite (ARmul_comm ARth). Esimpl.
    + Esimpl. f_equiv.
      * rewrite IHP'1; Esimpl.
      * destruct p0;rewrite IHP'2;Esimpl.
        rewrite jump_pred_double; Esimpl.
    + rewrite Padd_ok, !mkPX_ok, Padd_ok, !mkPX_ok,
       !IHP'1, !IHP'2, PmulI_ok; trivial. simpl. Esimpl.
      add_permut; f_equiv; mul_permut.
 Qed.

 Lemma mkZmon_ok M j l :
   (mkZmon j M) @@ l == (zmon j M) @@ l.
 Proof.
 destruct M; simpl; rsimpl.
 Qed.

 Lemma zmon_pred_ok M j l :
   (zmon_pred j M) @@ (tail l) == (zmon j M) @@ l.
 Proof.
   destruct j; simpl; rewrite ?mkZmon_ok; simpl; rsimpl.
   rewrite jump_pred_double; rsimpl.
 Qed.

 Lemma mkVmon_ok M i l :
   (mkVmon i M)@@l == M@@l * (hd l)^i.
 Proof.
  destruct M;simpl;intros;rsimpl.
  - rewrite zmon_pred_ok;simpl;rsimpl.
  - rewrite pow_pos_add;rsimpl.
 Qed.

 Ltac destr_factor := match goal with
  | H : context [CFactor ?P _] |- context [CFactor ?P ?c] =>
    destruct (CFactor P c); destr_factor; rewrite H; clear H
  | H : context [MFactor ?P _ _] |- context [MFactor ?P ?c ?M] =>
    specialize (H M); destruct (MFactor P c M); destr_factor; rewrite H; clear H
  | _ => idtac
 end.

 Lemma Mcphi_ok P c l :
   let (Q,R) := CFactor P c in
     P@l == Q@l + [c] * R@l.
 Proof.
 revert l.
 induction P as [c0 | j P IH | P1 IH1 i P2 IH2]; intros l; Esimpl.
 - assert (H := (div_eucl_th div_th) c0 c).
   destruct cdiv as (q,r). rewrite H; Esimpl. add_permut.
 - destr_factor. Esimpl.
 - destr_factor. Esimpl. add_permut.
 Qed.

 Lemma Mphi_ok P (cM: C * Mon) l :
   let (c,M) := cM in
   let (Q,R) := MFactor P c M in
     P@l == Q@l + [c] * M@@l * R@l.
 Proof.
 destruct cM as (c,M). revert M l.
 induction P as [c0|p P ?|P2 ? ? P3 ?]; intros M; destruct M; intros l;
  simpl; auto;
 try (case ceqb_spec; intro He);
  try (case Pos.compare_spec; intros He);
  rewrite ?He;
   destr_factor; simpl; Esimpl.
 - assert (H := div_eucl_th div_th c0 c).
   destruct cdiv as (q,r). rewrite H; Esimpl. add_permut.
 - assert (H := Mcphi_ok P c). destr_factor. Esimpl.
 - now rewrite <- jump_add, Pos.sub_add.
 - assert (H2 := Mcphi_ok P2 c). assert (H3 := Mcphi_ok P3 c).
   destr_factor. Esimpl. add_permut.
 - rewrite zmon_pred_ok. simpl. add_permut.
 - rewrite mkZmon_ok. simpl. add_permut. mul_permut.
 - add_permut. mul_permut.
   rewrite <- pow_pos_add, Pos.add_comm, Pos.sub_add by trivial; rsimpl.
 - rewrite mkZmon_ok. simpl. Esimpl. add_permut. mul_permut.
   rewrite <- pow_pos_add, Pos.sub_add by trivial; rsimpl.
 Qed.

 Lemma POneSubst_ok P1 cM1 P2 P3 l :
   POneSubst P1 cM1 P2 = Some P3 ->
   [fst cM1] * (snd cM1)@@l == P2@l -> P1@l == P3@l.
 Proof.
 destruct cM1 as (cc,M1).
 unfold POneSubst.
 assert (H := Mphi_ok P1 (cc, M1) l). simpl in H.
 destruct MFactor as (R1,S1); simpl. rewrite H. clear H.
 intros EQ EQ'. replace P3 with (R1 ++ P2 ** S1).
 - rewrite EQ', Padd_ok, Pmul_ok; rsimpl.
 - revert EQ. destruct S1; try now injection 1.
   case ceqb_spec; now inversion 2.
 Qed.

 Lemma PNSubst1_ok n P1 cM1 P2 l :
   [fst cM1] * (snd cM1)@@l == P2@l ->
   P1@l == (PNSubst1 P1 cM1 P2 n)@l.
 Proof.
 revert P1. induction n as [|n IHn]; simpl; intros P1;
 generalize (POneSubst_ok P1 cM1 P2); destruct POneSubst;
   intros; rewrite <- ?IHn; auto; reflexivity.
 Qed.

 Lemma PNSubst_ok n P1 cM1 P2 l P3 :
   PNSubst P1 cM1 P2 n = Some P3 ->
   [fst cM1] * (snd cM1)@@l == P2@l -> P1@l == P3@l.
 Proof.
 unfold PNSubst.
 assert (H := POneSubst_ok P1 cM1 P2); destruct POneSubst; try discriminate.
 destruct n; inversion_clear 1.
 intros. rewrite <- PNSubst1_ok; auto.
 Qed.

 Fixpoint MPcond (LM1: list (C * Mon * Pol)) (l: list R) : Prop :=
   match LM1 with
   | (M1,P2) :: LM2 => ([fst M1] * (snd M1)@@l == P2@l) /\ MPcond LM2 l
   | _ => True
   end.

 Lemma PSubstL1_ok n LM1 P1 l :
   MPcond LM1 l -> P1@l == (PSubstL1 P1 LM1 n)@l.
 Proof.
 revert P1; induction LM1 as [|(M2,P2) LM2 IH]; simpl; intros.
 - reflexivity.
 - rewrite <- IH by intuition; now apply PNSubst1_ok.
 Qed.

 Lemma PSubstL_ok n LM1 P1 P2 l :
   PSubstL P1 LM1 n = Some P2 -> MPcond LM1 l -> P1@l == P2@l.
 Proof.
 revert P1. induction LM1 as [|(M2,P2') LM2 IH]; simpl; intros P3 H **.
 - discriminate.
 - assert (H':=PNSubst_ok n P3 M2 P2'). destruct PNSubst.
   * injection H as [= <-]. rewrite <- PSubstL1_ok; intuition.
   * now apply IH.
 Qed.

 Lemma PNSubstL_ok m n LM1 P1 l :
    MPcond LM1 l -> P1@l == (PNSubstL P1 LM1 m n)@l.
 Proof.
 revert LM1 P1. induction m as [|m IHm]; simpl; intros LM1 P2 H;
 assert (H' := PSubstL_ok n LM1 P2); destruct PSubstL;
 auto; try reflexivity.
 rewrite <- IHm; auto.
 Qed.

 (** Definition of polynomial expressions *)

 #[local] Notation PExpr := (PExpr C).

 (** evaluation of polynomial expressions towards R *)
 Definition mk_X := mkX.

 (** evaluation of polynomial expressions towards R *)

 Fixpoint PEeval (l:list R) (pe:PExpr) {struct pe} : R :=
   match pe with
   | PEO => rO
   | PEI => rI
   | PEc c => phi c
   | PEX _ j => nth 0 j l
   | PEadd pe1 pe2 => (PEeval l pe1) + (PEeval l pe2)
   | PEsub pe1 pe2 => (PEeval l pe1) - (PEeval l pe2)
   | PEmul pe1 pe2 => (PEeval l pe1) * (PEeval l pe2)
   | PEopp pe1 => - (PEeval l pe1)
   | PEpow pe1 n => rpow (PEeval l pe1) (Cp_phi n)
   end.

Strategy expand [PEeval].

 (** Correctness proofs *)

 Lemma mkX_ok p l : nth 0 p l == (mk_X p) @ l.
 Proof.
  destruct p;simpl;intros;Esimpl;trivial.
  - now rewrite <-jump_tl, nth_jump.
  - now rewrite <- nth_jump, nth_pred_double.
 Qed.

 Hint Rewrite Padd_ok Psub_ok : Esimpl.

#[local] Notation Ppow_pos := (Ppow_pos cO cI cadd cmul ceqb).
#[local] Notation Ppow_N := (Ppow_N cO cI cadd cmul ceqb).

Section POWER.
  Variable subst_l : Pol -> Pol.

  Lemma Ppow_pos_ok l :
    (forall P, subst_l P@l == P@l) ->
    forall res P p, (Ppow_pos res P p)@l == res@l * (pow_pos Pmul P p)@l.
  Proof.
   intros subst_l_ok res P p. revert res.
   induction p as [p IHp|p IHp|];simpl;intros;
    rewrite ?subst_l_ok, ?Pmul_ok, ?IHp;
    mul_permut.
  Qed.

  Lemma Ppow_N_ok l :
    (forall P, subst_l P@l == P@l) ->
    forall P n, (Ppow_N P n)@l == (pow_N P1 Pmul P n)@l.
  Proof.
  intros ? P n; destruct n;simpl.
  - reflexivity.
  - rewrite Ppow_pos_ok by trivial. Esimpl.
  Qed.

 End POWER.

 (** Normalization and rewriting *)

 Section NORM_SUBST_REC.
  Variable n : nat.
  Variable lmp:list (C*Mon*Pol).
  Let subst_l P := PNSubstL P lmp n n.
  Let Pmul_subst P1 P2 := subst_l (P1 ** P2).

  #[local] Notation norm_aux := (Pol_of_PExpr cO cI cadd cmul csub copp ceqb).
  #[local] Notation norm_subst := (norm_subst cO cI cadd cmul csub copp ceqb cdiv n lmp).

  (** Internally, [norm_aux] is expanded in a large number of cases.
      To speed-up proofs, we use an alternative definition. *)

  Definition get_PEopp (pe : PExpr) :=
   match pe with
   | PEopp pe' => Some pe'
   | _ => None
   end.

  Lemma norm_aux_PEadd pe1 pe2 :
    norm_aux (PEadd pe1 pe2) =
    match get_PEopp pe1, get_PEopp pe2 with
    | Some pe1', _ => (norm_aux pe2) -- (norm_aux pe1')
    | None, Some pe2' => (norm_aux pe1) -- (norm_aux pe2')
    | None, None => (norm_aux pe1) ++ (norm_aux pe2)
    end.
  Proof.
  simpl (norm_aux (PEadd _ _)).
  destruct pe1; [ | | | | | | | reflexivity | ];
   destruct pe2; simpl get_PEopp; reflexivity.
  Qed.

  Lemma norm_aux_PEopp pe :
    match get_PEopp pe with
    | Some pe' => norm_aux pe = -- (norm_aux pe')
    | None => True
    end.
  Proof.
  now destruct pe.
  Qed.

  Arguments Pol_of_PExpr _ _ _ _ _ _ _ _ !pe : simpl nomatch.

  Lemma norm_aux_spec l pe :
    PEeval l pe == (norm_aux pe)@l.
  Proof.
   intros.
   induction pe as [| |c|p|pe1 IHpe1 pe2 IHpe2|? IHpe1 ? IHpe2|? IHpe1 ? IHpe2
                   |? IHpe|? IHpe n0]; cbn.
   - now rewrite (morph0 CRmorph).
   - now rewrite (morph1 CRmorph).
   - reflexivity.
   - apply mkX_ok.
   - rewrite IHpe1, IHpe2.
     assert (H1 := norm_aux_PEopp pe1).
     assert (H2 := norm_aux_PEopp pe2).
     rewrite norm_aux_PEadd.
     do 2 destruct get_PEopp; rewrite ?H1, ?H2; Esimpl; add_permut.
   - rewrite IHpe1, IHpe2. Esimpl.
   - rewrite IHpe1, IHpe2. now rewrite Pmul_ok.
   - rewrite IHpe. Esimpl.
   - rewrite (Ppow_N_ok id) by reflexivity.
     rewrite (rpow_pow_N pow_th). destruct n0 as [|p]; simpl; Esimpl.
     induction p as [p IHp|p IHp|];simpl;
      now rewrite ?IHp, ?IHpe, ?Pms_ok, ?Pmul_ok.
  Qed.

 Lemma norm_subst_spec :
     forall l pe, MPcond lmp l ->
       PEeval l pe == (norm_subst pe)@l.
 Proof.
  intros;unfold norm_subst.
  unfold subst_l;rewrite <- PNSubstL_ok;trivial. apply norm_aux_spec.
 Qed.

 End NORM_SUBST_REC.
 #[local] Notation norm_subst := (norm_subst cO cI cadd cmul csub copp ceqb cdiv).

 Fixpoint interp_PElist (l:list R) (lpe:list (PExpr*PExpr)) {struct lpe} : Prop :=
   match lpe with
   | nil => True
   | (me,pe)::lpe =>
     match lpe with
     | nil => PEeval l me == PEeval l pe
     | _ => PEeval l me == PEeval l pe /\ interp_PElist l lpe
     end
  end.

 #[local] Notation mon_of_pol := (Mon_of_Pol cO ceqb).
 #[local] Notation mk_monpol_list := (mk_monpol_list cO cI cadd cmul csub copp ceqb cdiv).
 #[local] Notation ring_checker := (ring_checker cO cI cadd cmul csub copp ceqb cdiv).

  Lemma mon_of_pol_ok : forall P m, mon_of_pol P = Some m ->
              forall l, [fst m] * Mphi l (snd m) == P@l.
  Proof.
    intros P; induction P as [c|p P IHP|P2 IHP1 ? P3 ?];simpl;intros m H l;Esimpl.
    - assert (H1 := (morph_eq CRmorph) c cO).
      destruct (c ?=! cO).
      + discriminate.
      + inversion H;trivial;Esimpl.
    - generalize H;clear H;case_eq (mon_of_pol P).
      + intros (c1,P2) H0 H1; inversion H1; Esimpl.
        generalize (IHP (c1, P2) H0 (jump p l)).
        rewrite mkZmon_ok;simpl;auto.
      + intros; discriminate.
    - generalize H;clear H;change match P3 with
                                  | Pc c => c ?=! cO
                                  | Pinj _ _ => false
                                  | PX _ _ _ => false
                                  end with (P3 ?== P0).
      assert (H := Peq_ok P3 P0).
      destruct (P3 ?== P0).
      + case_eq (mon_of_pol P2);try intros (cc, pp); intros H0 H1.
        * inversion H1.
          simpl.
          rewrite mkVmon_ok;simpl.
          rewrite H;trivial;Esimpl.
          generalize (IHP1 _ H0); simpl; intros HH; rewrite HH; rsimpl.
        * discriminate.
      + intros;discriminate.
  Qed.

 Lemma interp_PElist_ok : forall l lpe,
         interp_PElist l lpe -> MPcond (mk_monpol_list lpe) l.
 Proof.
   intros l lpe; induction lpe as [|a lpe IHlpe];simpl.
   - trivial.
   - destruct a as [p p0];simpl;intros H.
     assert (HH:=mon_of_pol_ok (norm_subst 0 nil  p));
       destruct  (mon_of_pol (norm_subst 0 nil p)).
     + split.
       * rewrite <- norm_subst_spec by exact I.
         destruct lpe;try destruct H as [H H0];rewrite <- H;
           rewrite (norm_subst_spec 0 nil); try exact I;apply HH;trivial.
       * apply IHlpe. destruct lpe;simpl;trivial. destruct H as [H H0]. exact H0.
     + apply IHlpe. destruct lpe;simpl;trivial. destruct H as [H H0]. exact H0.
 Qed.

 Lemma norm_subst_ok : forall n l lpe pe,
   interp_PElist l lpe ->
   PEeval l pe == (norm_subst n (mk_monpol_list lpe) pe)@l.
 Proof.
   intros;apply norm_subst_spec. apply interp_PElist_ok;trivial.
  Qed.

 Lemma ring_correct : forall n l lpe pe1 pe2,
   interp_PElist l lpe ->
   ring_checker n lpe pe1 pe2 = true ->
   PEeval l pe1 == PEeval l pe2.
 Proof.
  simpl;intros n l lpe pe1 pe2 **.
  do 2 (rewrite (norm_subst_ok n l lpe);trivial).
  apply Peq_ok;trivial.
 Qed.



  (** Generic evaluation of polynomial towards R avoiding parenthesis *)
 Variable get_sign : C -> option C.
 Variable get_sign_spec : sign_theory copp ceqb get_sign.


 Section EVALUATION.

  (* [mkpow x p] = x^p *)
  Variable mkpow : R -> positive -> R.
  (* [mkpow x p] = -(x^p) *)
  Variable mkopp_pow : R -> positive -> R.
  (* [mkmult_pow r x p] = r * x^p *)
  Variable mkmult_pow : R -> R -> positive -> R.

  Fixpoint mkmult_rec (r:R) (lm:list (R*positive)) {struct lm}: R :=
   match lm with
   | nil => r
   | cons (x,p) t => mkmult_rec (mkmult_pow r x p) t
   end.

  Definition mkmult1 lm :=
   match lm with
   | nil => 1
   | cons (x,p) t => mkmult_rec (mkpow x p) t
   end.

  Definition mkmultm1 lm :=
   match lm with
   | nil => ropp rI
   | cons (x,p) t => mkmult_rec (mkopp_pow x p) t
   end.

  Definition mkmult_c_pos c lm :=
   if c ?=! cI then mkmult1 (rev' lm)
   else mkmult_rec [c] (rev' lm).

  Definition mkmult_c c lm :=
   match get_sign c with
   | None => mkmult_c_pos c lm
   | Some c' =>
     if c' ?=! cI then mkmultm1 (rev' lm)
     else mkmult_rec [c] (rev' lm)
   end.

  Definition mkadd_mult rP c lm :=
   match get_sign c with
   | None => rP + mkmult_c_pos c lm
   | Some c' => rP - mkmult_c_pos c' lm
   end.

  Definition add_pow_list (r:R) n l :=
   match n with
   | N0 => l
   | Npos p => (r,p)::l
   end.

  Fixpoint add_mult_dev
      (rP:R) (P:Pol) (fv:list R) (n:N) (lm:list (R*positive)) {struct P} : R :=
   match P with
   | Pc c =>
     let lm := add_pow_list (hd fv) n lm in
     mkadd_mult rP c lm
   | Pinj j Q =>
     add_mult_dev rP Q (jump j fv) N0 (add_pow_list (hd fv) n lm)
   | PX P i Q =>
     let rP := add_mult_dev rP P fv (N.add (Npos i) n) lm in
     if Q ?== P0 then rP
     else add_mult_dev rP Q (tail fv) N0 (add_pow_list (hd fv) n lm)
   end.

  Fixpoint mult_dev (P:Pol) (fv : list R) (n:N)
                     (lm:list (R*positive)) {struct P} : R :=
  (* P@l * (hd 0 l)^n * lm *)
  match P with
  | Pc c => mkmult_c c (add_pow_list (hd fv) n lm)
  | Pinj j Q => mult_dev Q (jump j fv) N0 (add_pow_list (hd fv) n lm)
  | PX P i Q =>
     let rP := mult_dev P fv (N.add (Npos i) n) lm in
     if Q ?== P0 then rP
     else
       let lmq := add_pow_list (hd fv) n lm in
       add_mult_dev rP Q (tail fv) N0 lmq
  end.

 Definition Pphi_avoid fv P := mult_dev P fv N0 nil.

 Fixpoint r_list_pow (l:list (R*positive)) : R :=
  match l with
  | nil => rI
  | cons (r,p) l => pow_pos rmul r p * r_list_pow l
  end.

  Hypothesis mkpow_spec : forall r p, mkpow r p == pow_pos rmul r p.
  Hypothesis mkopp_pow_spec : forall r p, mkopp_pow r p == - (pow_pos rmul r p).
  Hypothesis mkmult_pow_spec : forall r x p, mkmult_pow r x p == r * pow_pos rmul x p.

 Lemma mkmult_rec_ok : forall lm r, mkmult_rec r lm == r * r_list_pow lm.
 Proof.
   intros lm; induction lm as [|a lm IHlm];intros;simpl;Esimpl.
   destruct a as (x,p);Esimpl.
   rewrite IHlm. rewrite mkmult_pow_spec. Esimpl.
  Qed.

 Lemma mkmult1_ok : forall lm, mkmult1 lm == r_list_pow lm.
 Proof.
   intros lm; destruct lm as [|p lm];simpl;Esimpl.
   destruct p. rewrite mkmult_rec_ok;rewrite mkpow_spec;Esimpl.
 Qed.

 Lemma mkmultm1_ok : forall lm, mkmultm1 lm == - r_list_pow lm.
 Proof.
  intros lm; destruct lm as [|p lm];simpl;Esimpl.
  destruct p;rewrite mkmult_rec_ok. rewrite mkopp_pow_spec;Esimpl.
 Qed.

 Lemma r_list_pow_rev :  forall l, r_list_pow (rev' l) == r_list_pow l.
 Proof.
   assert
    (forall l lr : list (R * positive), r_list_pow (rev_append l lr) == r_list_pow lr * r_list_pow l) as H.
   - intros l; induction l as [|a l IHl];intros;simpl;Esimpl.
     destruct a as [r p];rewrite IHl;Esimpl.
     rewrite (ARmul_comm ARth (pow_pos rmul r p)). reflexivity.
   - intros;unfold rev'. rewrite H;simpl;Esimpl.
 Qed.

 Lemma mkmult_c_pos_ok : forall c lm, mkmult_c_pos c lm == [c]* r_list_pow lm.
 Proof.
  intros c lm;unfold mkmult_c_pos;simpl.
   assert (H := (morph_eq CRmorph) c cI).
   rewrite <- r_list_pow_rev; destruct (c ?=! cI).
  - rewrite H;trivial;Esimpl.
    apply mkmult1_ok.
  - apply mkmult_rec_ok.
 Qed.

 Lemma mkmult_c_ok : forall c lm, mkmult_c c lm == [c] * r_list_pow lm.
 Proof.
  intros c lm;unfold mkmult_c;simpl.
  case_eq (get_sign c);intros c0; try intros H.
  - assert (H1 := (morph_eq CRmorph) c0  cI).
    destruct (c0 ?=! cI).
    + rewrite (morph_eq CRmorph _ _ (sign_spec get_sign_spec _ H)). Esimpl. rewrite H1;trivial.
      rewrite <- r_list_pow_rev;trivial;Esimpl.
      apply mkmultm1_ok.
    + rewrite <- r_list_pow_rev; apply mkmult_rec_ok.
  - apply mkmult_c_pos_ok.
 Qed.

 Lemma mkadd_mult_ok : forall rP c lm, mkadd_mult rP c lm == rP + [c]*r_list_pow lm.
 Proof.
  intros rP c lm;unfold mkadd_mult.
  case_eq (get_sign c);intros c0; try intros H.
  - rewrite (morph_eq CRmorph _ _ (sign_spec get_sign_spec _ H));Esimpl.
    rewrite mkmult_c_pos_ok;Esimpl.
  - rewrite mkmult_c_pos_ok;Esimpl.
 Qed.

 Lemma add_pow_list_ok :
      forall r n l, r_list_pow (add_pow_list r n l) == pow_N rI rmul r n * r_list_pow l.
 Proof.
   intros r n; destruct n;simpl;intros;Esimpl.
 Qed.

 Lemma add_mult_dev_ok : forall P rP fv n lm,
    add_mult_dev rP P fv n lm == rP + P@fv*pow_N rI rmul (hd fv) n * r_list_pow lm.
  Proof.
    intros P; induction P as [|p P IHP|P2 IHP1 p P3 IHP2];simpl;intros rP fv n lm.
    - rewrite mkadd_mult_ok. rewrite add_pow_list_ok; Esimpl.
    - rewrite IHP. simpl. rewrite add_pow_list_ok; Esimpl.
    - change (match P3 with
              | Pc c => c ?=! cO
              | Pinj _ _ => false
              | PX _ _ _ => false
              end) with (Peq P3 P0).
      change match n with
             | N0 => Npos p
             | Npos q => Npos (p + q)
             end with (N.add (Npos p) n);trivial.
      assert (H := Peq_ok P3 P0).
      destruct (P3 ?== P0).
      + rewrite (H eq_refl).
        rewrite IHP1. destruct n;simpl;Esimpl;rewrite pow_pos_add;Esimpl.
        add_permut. mul_permut.
      + rewrite IHP2.
        rewrite IHP1. destruct n;simpl;Esimpl;rewrite pow_pos_add;Esimpl.
        add_permut. mul_permut.
  Qed.

 Lemma mult_dev_ok : forall P fv n lm,
    mult_dev P fv n lm == P@fv * pow_N rI rmul (hd fv) n * r_list_pow lm.
 Proof.
   intros P; induction P as [|p P IHP|P2 IHP1 p P3 IHP2];simpl;intros fv n lm;Esimpl.
   - rewrite mkmult_c_ok;rewrite add_pow_list_ok;Esimpl.
   - rewrite IHP. simpl;rewrite add_pow_list_ok;Esimpl.
   - change (match P3 with
             | Pc c => c ?=! cO
             | Pinj _ _ => false
             | PX _ _ _ => false
             end) with (Peq P3 P0).
     change match n with
            | N0 => Npos p
            | Npos q => Npos (p + q)
            end with (N.add (Npos p) n);trivial.
     assert (H := Peq_ok P3 P0).
     destruct (P3 ?== P0).
     + rewrite (H eq_refl).
       rewrite  IHP1. destruct n;simpl;Esimpl;rewrite pow_pos_add;Esimpl.
       mul_permut.
     + rewrite add_mult_dev_ok. rewrite IHP1; rewrite add_pow_list_ok.
       destruct n;simpl;Esimpl;rewrite pow_pos_add;Esimpl.
       add_permut; mul_permut.
 Qed.

 Lemma Pphi_avoid_ok : forall P fv, Pphi_avoid fv P  == P@fv.
 Proof.
   unfold Pphi_avoid;intros;rewrite mult_dev_ok;simpl;Esimpl.
 Qed.

 End EVALUATION.

  Definition Pphi_pow :=
   let mkpow x p :=
      match p with xH => x | _ => rpow x (Cp_phi (Npos p)) end in
   let mkopp_pow x p := ropp (mkpow x p)  in
   let mkmult_pow r x p := rmul r (mkpow x p) in
    Pphi_avoid mkpow mkopp_pow mkmult_pow.

 Lemma local_mkpow_ok r p :
    match p with
    | xI _ => rpow r (Cp_phi (Npos p))
    | xO _ => rpow r (Cp_phi (Npos p))
    | 1 => r
    end == pow_pos rmul r p.
 Proof. destruct p; now rewrite ?(rpow_pow_N pow_th). Qed.

 Lemma Pphi_pow_ok : forall P fv, Pphi_pow fv P  == P@fv.
 Proof.
  unfold Pphi_pow;intros;apply Pphi_avoid_ok;intros;
   now rewrite ?local_mkpow_ok.
 Qed.

 Lemma ring_rw_pow_correct : forall n lH l,
      interp_PElist l lH ->
      forall lmp, mk_monpol_list lH = lmp ->
      forall pe npe, norm_subst n lmp pe = npe ->
      PEeval l pe == Pphi_pow l npe.
 Proof.
  intros n lH l H1 lmp Heq1 pe npe Heq2.
  rewrite Pphi_pow_ok, <- Heq2, <- Heq1.
  apply norm_subst_ok. trivial.
 Qed.

 Fixpoint mkmult_pow (r x:R) (p: positive) {struct p} : R :=
   match p with
   | xH => r*x
   | xO p => mkmult_pow (mkmult_pow r x p) x p
   | xI p => mkmult_pow (mkmult_pow (r*x) x p) x p
   end.

  Definition mkpow x p :=
    match p with
    | xH => x
    | xO p => mkmult_pow x x (Pos.pred_double p)
    | xI p => mkmult_pow x x (xO p)
    end.

  Definition mkopp_pow x p :=
    match p with
    | xH => -x
    | xO p => mkmult_pow (-x) x (Pos.pred_double p)
    | xI p => mkmult_pow (-x) x (xO p)
    end.

  Definition Pphi_dev := Pphi_avoid mkpow mkopp_pow mkmult_pow.

  Lemma mkmult_pow_ok p r x : mkmult_pow r x p == r * x^p.
  Proof.
    revert r; induction p as [p IHp|p IHp|];intros;simpl;Esimpl;rewrite !IHp;Esimpl.
  Qed.

 Lemma mkpow_ok p x : mkpow x p == x^p.
  Proof.
    destruct p;simpl;intros;Esimpl.
    - rewrite !mkmult_pow_ok;Esimpl.
    - rewrite mkmult_pow_ok;Esimpl.
      change x with (x^1) at 1.
      now rewrite <- pow_pos_add, Pos.add_1_r, Pos.succ_pred_double.
  Qed.

  Lemma mkopp_pow_ok p x : mkopp_pow x p == - x^p.
  Proof.
    destruct p;simpl;intros;Esimpl.
    - rewrite !mkmult_pow_ok;Esimpl.
    - rewrite mkmult_pow_ok;Esimpl.
      change x with (x^1) at 1.
      now rewrite <- pow_pos_add, Pos.add_1_r, Pos.succ_pred_double.
  Qed.

 Lemma Pphi_dev_ok : forall P fv, Pphi_dev fv P == P@fv.
  Proof.
   unfold Pphi_dev;intros;apply Pphi_avoid_ok.
   - intros;apply mkpow_ok.
   - intros;apply mkopp_pow_ok.
   - intros;apply mkmult_pow_ok.
  Qed.

 Lemma ring_rw_correct : forall n lH l,
      interp_PElist l lH ->
      forall lmp, mk_monpol_list lH = lmp ->
      forall pe npe, norm_subst n lmp pe = npe ->
      PEeval l pe == Pphi_dev l npe.
 Proof.
  intros n lH l H1 lmp Heq1 pe npe Heq2.
  rewrite  Pphi_dev_ok. rewrite <- Heq2;rewrite <- Heq1.
  apply norm_subst_ok. trivial.
 Qed.

End MakeRingPol.

Arguments PEO {C}.
Arguments PEI {C}.

Notation norm_aux := Pol_of_PExpr.
