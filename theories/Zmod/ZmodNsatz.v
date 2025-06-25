Require Export (ltac.notations) NsatzTactic.

Require Import Zdivisibility Lia NsatzTactic.
Require Import ZmodDef ZmodBase ZmodInv.

#[export]
Instance Ring_ops_Zmod m : @Ring_ops (Zmod m) Zmod.zero Zmod.one Zmod.add Zmod.mul Zmod.sub Zmod.opp Logic.eq := {}.

#[export]
Instance Ring_Zmod m : Ring (Ro:=Ring_ops_Zmod m).
Proof.
  split.
  { apply eq_equivalence. }
  1,2,3,4 : Morphisms.solve_proper.
  { apply Zmod.add_0_l. }
  { apply Zmod.add_comm. }
  { apply Zmod.add_assoc. }
  { apply Zmod.mul_1_l. }
  { apply Zmod.mul_1_r. }
  { apply Zmod.mul_assoc. }
  { apply Zmod.mul_add_l. }
  { intros ? ? ?. apply Zmod.mul_add_r. }
  { symmetry; apply Zmod.add_opp_r. }
  { apply Zmod.add_opp_same_r. }
Qed.

#[export]
Instance Cring_ZMod m : Cring (Rr:=Ring_Zmod m).
Proof.
  cbv [Cring].
  apply Zmod.mul_comm.
Qed.

#[export]
Instance Integral_domain_Zmod m : Z.prime m -> Integral_domain (Rr:=Ring_Zmod m).
Proof.
  intros H; split.
  { apply Zmod.mul_0_iff_prime, H. }
  { apply Zmod.one_neq_zero. pose proof Z.prime_ge_2 _ H. lia. }
Qed.

#[local] Ltac extra_reify_of_Z :=
  lazymatch goal with |- Ncring_tac.extra_reify _ (@Zmod.of_Z ?m ?z) =>
  constr_eq true ltac:(isZcst m);
  constr_eq true ltac:(isZcst z);
  exact (PEc z)
  end.

#[local] Ltac extra_reify_pow_pos :=
  lazymatch goal with |- @Ncring_tac.extra_reify ?R ?ring0 ?ring1 ?add ?mul ?sub ?opp ?lvar (Zmod.pow ?t (Z.pos ?p)) =>
  constr_eq true ltac:(isPcst p);
  let et := Ncring_tac.reify_term R ring0 ring1 add mul sub opp lvar t in
  exact (PEpow et (BinNat.N.pos p))
  end.

#[export] Hint Extern 1 (Ncring_tac.extra_reify _ (Zmod.of_Z ?m ?z)) => extra_reify_of_Z : typeclass_instances.
#[export] Hint Extern 1 (Ncring_tac.extra_reify _ (Zmod.pow _ (Z.pos _))) => extra_reify_pow_pos : typeclass_instances.
#[export] Hint Extern 1 (Ncring_tac.extra_reify _ (Zmod.pow _ Z0)) => exact (PEc 0%Z) : typeclass_instances.
(* [Zmod.pow _ (Z.neg) = Zmod.inv (Zmod.pow _ _)] can't be reified directly *)
