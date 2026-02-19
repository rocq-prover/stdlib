
From Stdlib Require Import Btauto.
#[local] Open Scope bool_scope.

Axiom unsigned : bool.
Axiom combine : bool.

Lemma foo
  : (false &&  unsigned) || (false &&  combine) =
      combine .
Proof.
  Fail btauto.
Abort.
