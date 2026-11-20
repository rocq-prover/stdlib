From Stdlib Require Import Relations.
From Stdlib Require Import Setoid.
From Stdlib Require Import Ring_theory.
From Stdlib Require Import Ring_base.


Parameter R : Type.
Parameter Rone Rzero : R.
Parameter Rplus Rmult Rminus : R -> R -> R.
Parameter Rneg : R -> R.

Lemma my_ring_theory : @ring_theory R Rzero Rone Rplus Rmult Rminus Rneg (@eq
R).
Admitted.

Parameter Req : R -> R -> Prop.

Axiom Req_refl : reflexive _ Req.
Axiom Req_sym : symmetric _ Req.
Axiom Req_trans : transitive _ Req.

#[global] Instance Req_rel : @Equivalence R Req := {
  Equivalence_Reflexive := Req_refl;
  Equivalence_Symmetric := Req_sym;
  Equivalence_Transitive := Req_trans }.

Add Ring my_ring : my_ring_theory (abstract).
