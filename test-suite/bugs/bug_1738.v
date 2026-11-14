From Stdlib Require Import FSets.

Module SomeSetoids (Import M:FSetInterface.S).

Lemma Equal_refl : forall s, s[=]s.
Proof. red; split; auto. Qed.

#[global] Instance EqualSetoid : @Equivalence t Equal := {
  Equivalence_Reflexive := Equal_refl;
  Equivalence_Symmetric := eq_sym;
  Equivalence_Transitive := eq_trans }.

#[global] Instance Empty_m : Proper (Equal ==> iff) Empty.
Proof.
unfold Equal, Empty; firstorder.
Qed.

End SomeSetoids.

Module Test (Import M:FSetInterface.S).
 Module A:=SomeSetoids M.
 Module B:=SomeSetoids M. (* lots of warning *)

 Lemma Test : forall s s', s[=]s' -> Empty s -> Empty s'.
 intros.
 rewrite H in H0.
 assumption.
Qed.
End Test.
