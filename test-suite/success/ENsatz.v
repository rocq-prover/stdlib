From Stdlib Require Import Znumtheory.
From Stdlib Require Import ZArith.
From Stdlib Require Import ENsatzTactic.

Lemma modulo1 a b c: (a mod b = c -> exists k, a - c = k*b)%Z.
Proof.
  intros.
  destruct (Z.eq_dec b 0) as [H1 | H1].
    - subst.
      exists 0%Z.
      rewrite Zmod_0_r.
      rewrite Z.sub_diag.
      rewrite Z.mul_0_l.
      trivial.
    - specialize (Zmod_divides (a -c)%Z b H1).
      rewrite Zminus_mod.
      rewrite H.
      rewrite Zminus_mod_idemp_r.
      rewrite Z.sub_diag.
      rewrite Zmod_0_l.
      intros [H2 _].
      destruct (H2 eq_refl).
      exists x.
      rewrite Z.mul_comm.
      trivial.
Qed.

Lemma modulo2 a b c: ((exists k, a - c = k*b) -> a mod b = c mod b)%Z.
Proof.
  intros. destruct H.
  rewrite Z.sub_move_r in H.
  subst.
  rewrite Z.add_comm.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

Lemma div1 a b : ((a | b)  -> exists k, b = k*a)%Z.
Proof.
  intros.
  destruct (Z.eq_dec a 0) as [H1 | H1].
    - subst.
      exists 0%Z.
      apply Z.divide_0_l in H.
      subst. reflexivity.
    - apply Zdivide_mod in H.
      apply (Zmod_divides _ _ H1 ) in H.
      destruct H.
      rewrite Z.mul_comm in H.
      exists x. trivial.
Qed.

Lemma div2 a b : ((exists k, b = k*a) -> (a | b))%Z.
Proof.
 intros.
 destruct (Z.eq_dec a 0) as [H1 | H1].
    - subst.
      destruct H.
      rewrite Z.mul_0_r in H.
      subst.
      apply Z.divide_0_r.
    - assert (H': exists k:Z, b = a * k).
      destruct H. exists x. rewrite Z.mul_comm. trivial.
      apply (Zmod_divides _ _ H1) in H'.
      apply (Zmod_divide _ _ H1 H').
Qed.

Ltac div_to_equality H x y := try (apply (div1 x y) in H).

Ltac divs_to_equalities :=
  lazymatch goal with
  |  H: (?x | ?y)%Z |- _ => div_to_equality H x y
   end.

Ltac mod_to_equality H x y z:= try (apply (modulo1 x y z) in H).

Ltac mods_to_equalities :=
  lazymatch goal with
  |  H: (?z = ?x mod ?y)%Z |- _ => apply symmetry in H; mods_to_equalities
  |  H: (?x mod ?y = ?z)%Z |- _ => mod_to_equality H x y z
  end.

Ltac exists_to_equalities :=
  lazymatch goal with
  | H: (exists e: ?A, ?b1) |- _ => destruct H
  end.

Ltac get_mods_aux a :=
  match a with
  | context [?a mod ?b] =>
      first [get_mods_aux a | get_mods_aux b |
      let j := fresh "j" in
      let Hj := fresh "Hj" in
      remember (a mod b) as j eqn: Hj]
  end.

Ltac get_mods :=
  match goal with
    |- context [?a mod ?b] =>
      let t := constr:(a mod b) in
      get_mods_aux t
  end.

Ltac preprocess :=
  intros;
  repeat mods_to_equalities;
  repeat divs_to_equalities;
  repeat exists_to_equalities;
  match goal with
  | |- (?x mod ?n)%Z = (?y mod ?n)%Z => apply modulo2
  | |- (?x | ?y)%Z => apply div2
  | |- ?g => idtac
  end;
  repeat (get_mods;  mods_to_equalities;  exists_to_equalities).

(*
     Examples of the Stdlib.
*)

Example mod_mod_divide: forall a b c : Z, (c | b) -> (a mod b) mod c = a mod c.
Proof.
  preprocess.
  Time ensatz.
Qed.

Example mod_mod_divide2: forall a b c : Z, (c | b) -> ((a mod b) mod b) mod c = a mod c.
  preprocess.
  Time ensatz.
Qed.

Example Zmult_mod_idemp_l : forall a b n : Z, (a mod n * b) mod n = (a * b) mod n.
Proof.
  preprocess.
  Time ensatz.
Qed.

Example Zplus_mod_idemp_l: forall a b n : Z, (a mod n + b) mod n = (a + b) mod n.
Proof.
  preprocess.
  Time ensatz.
Qed.

Example Zplus_mod: forall a b n : Z, (a + b) mod n = (a mod n + b mod n) mod n.
Proof.
  preprocess.
  Time ensatz.
Qed.

Example Zmult_mod: forall a b n : Z, (a * b) mod n = (a mod n * (b mod n)) mod n.
Proof.
  preprocess.
  Time ensatz.
Qed.

Example mod_mod_opp_r: forall a b : Z, (a mod - b) mod b = a mod b.
Proof.
  preprocess.
  Time ensatz.
Qed.

Example cong: forall a b m : Z, (a - b) mod m = 0%Z -> a mod m = b mod m.
Proof.
  preprocess.
  Time ensatz.
Qed.

(*
     Example of the paper "Automating elementary number-theoretic proofs
     using Gröbner bases" by John Harrison.
*)
Example cancellation_congruence a n x y:
  (a * x = (a * y) mod n -> (exists e1 e2, a * e1 + n * e2 = 1) -> y mod n = x mod n)%Z.
Proof.
  preprocess.
  Time ensatz.
Qed.

(*
     Examples of the paper "Connecting Gröbner bases programs with Coq to
     do proofs in algebra, geometry and arithmetics" by Loïc Pottier.
*)
Definition divides(a b:Z):= exists c:Z, b=c*a.
Definition modulo(a b p:Z):= exists k:Z, a - b = k*p.
Definition ideal(x a b:Z):= exists u:Z, exists v:Z, x = u*a+v*b.
Definition gcd(g a b:Z):= divides g a /\ divides g b /\ ideal g a b.
Definition coprime(a b:Z):= exists u:Z, exists v:Z, 1 = u*a+v*b.

Goal forall a b c:Z, divides a (b*c) -> coprime a b -> divides a c.
  unfold divides, modulo, coprime, ideal, gcd.
  preprocess.
  Time ensatz.
Qed.

Goal forall m n r:Z, divides m r -> divides n r -> coprime m n -> divides (m*n) r.
  unfold divides, modulo, coprime, ideal, gcd.
  preprocess.
  Time ensatz.
Qed.

Goal forall x y a n:Z, modulo (x*x) a n -> modulo (y*y) a n -> divides n ((x+y)*(x-y)).
  unfold divides, modulo, coprime, ideal, gcd.
  preprocess.
  Time ensatz.
Qed.
