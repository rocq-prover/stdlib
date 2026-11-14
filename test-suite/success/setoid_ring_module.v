From Stdlib Require Import Setoid Morphisms Ring Ring_theory.

Module abs_ring.

Parameters (Coef:Set)(c0 c1 : Coef)
(cadd cmul csub: Coef -> Coef -> Coef)
(copp : Coef -> Coef)
(ceq : Coef -> Coef -> Prop)
(ceq_sym : forall x y, ceq x y -> ceq y x)
(ceq_trans : forall x y z, ceq x y -> ceq y z -> ceq x z)
(ceq_refl : forall x, ceq x x).


#[global] Instance ceq_relation : @Equivalence Coef ceq := {
  Equivalence_Reflexive := ceq_refl;
  Equivalence_Symmetric := ceq_sym;
  Equivalence_Transitive := ceq_trans }.

#[global] Instance cadd_Morphism : Proper (ceq ==> ceq ==> ceq) cadd.
Admitted.

#[global] Instance cmul_Morphism : Proper (ceq ==> ceq ==> ceq) cmul.
Admitted.

#[global] Instance copp_Morphism : Proper (ceq ==> ceq) copp.
Admitted.

Definition cRth : ring_theory c0 c1 cadd cmul csub copp ceq.
Admitted.

Add Ring CoefRing : cRth.

End abs_ring.
Import abs_ring.

Theorem check_setoid_ring_modules :
  forall a b, ceq (cadd a b) (cadd b a).
intros.
ring.
Qed.
