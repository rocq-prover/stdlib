From Stdlib Require Import ZArith Nsatz.
Set Typeclasses Debug.
Lemma test (x y : Z) : x = y -> y = x.
Proof. nsatz. Qed.
