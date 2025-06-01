From Stdlib Require Import Integral_domain ZArith ZNsatz.
Set Typeclasses Debug.
Lemma test (x y : Z) : x = y -> y = x.
Proof. nsatz. Qed.
