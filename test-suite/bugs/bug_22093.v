From Stdlib Require Import ZArith Lia.

Section S.
Open Scope Z_scope.
Variable n : Z.
Variable bound_n : 0 <= n < 1.

Goal True.
Proof.
  Timeout 1 lia.
  (* Used to not terminate, now 3ms *)
Qed.

End S.
