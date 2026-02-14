Attributes deprecated(since="Stdlib 9.1", note="Use RNsatz, QNsatz, or ZNsatz, or NsatzTactic.").
Require Export RNsatz QNsatz ZNsatz NsatzTactic.

From Stdlib Require Import List.
From Stdlib Require Import Setoid.
From Stdlib Require Import BinPos.
From Stdlib Require Import BinList.
From Stdlib Require Export Morphisms Setoid Bool.
From Stdlib Require Export Algebra_syntax.
From Stdlib Require Export Ncring.
From Stdlib Require Export Ncring_initial.
From Stdlib Require Export Ncring_tac.
From Stdlib Require Export Integral_domain.
From Stdlib Require Import DiscrR.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Export Rbase.
From Stdlib Require Export Rfunctions.
From Stdlib Require Import RealField.
From Stdlib Require Import QArith_base.

#[global] Existing Instance Zops.
#[global] Existing Instance Zr.
#[global] Existing Instance Zdi.
#[global] Existing Instance Qops.
#[global] Existing Instance Qri.
#[global] Existing Instance Qdi.

(* Same hint as in RNsatz, but superglobal *)
Ltac Ncring_tac.extra_reify term ::=
  lazymatch term with
  | IZR ?z =>
      lazymatch isZcst z with
      | true => open_constr:(PEc z)
      | false => open_constr:(tt)
      end
  | _ => open_constr:(tt)
  end.

#[deprecated(since="Stdlib 9.1", note="use discriminate")]
Lemma Z_one_zero: 1%Z <> 0%Z.
Proof. discriminate. Qed.

#[deprecated(since="Stdlib 9.1", use=Q_apart_0_1)]
Notation Q_one_zero := Q_apart_0_1 (only parsing).

#[deprecated(since="Stdlib 9.1", use=eq_equivalence)]
Lemma Rsth : Setoid_Theory R (@eq R).
Proof. cbv [Setoid_Theory]. exact _. Qed.

#[deprecated(since="Stdlib 9.1", use=R1_neq_R0)]
Notation R_one_zero := R1_neq_R0 (only parsing).
