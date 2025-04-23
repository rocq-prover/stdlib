From Stdlib Require Import Znumtheory.
From Stdlib Require Import ZArith.
From Stdlib Require Import ZNsatz.
From Stdlib Require Import ENsatzTactic.
From Stdlib Require Import Cring.
From Stdlib Require Import Lia.

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

(* *)
(*      Example of the paper "Automating elementary number-theoretic proofs *)
(*      using Gröbner bases" by John Harrison. *)
(* *)
Example cancellation_congruence a n x y:
  (a * x = (a * y) mod n -> (exists e1 e2, a * e1 + n * e2 = 1) -> y mod n = x mod n)%Z.
Proof.
  preprocess.
  Time ensatz.
Qed.

(* *)
(*      Examples of the paper "Connecting Gröbner bases programs with Coq to *)
(*      do proofs in algebra, geometry and arithmetics" by Loïc Pottier. *)
(* *)

Definition modulo(a b p:Z):= exists k:Z, a - b = k*p.
Definition ideal(x a b:Z):= exists u:Z, exists v:Z, x = u*a+v*b.
Definition coprime(a b:Z):= exists u:Z, exists v:Z, 1 = u*a+v*b.
Definition gcd(g a b:Z):= (g | a) /\ (g | b) /\ ideal g a b.

Ltac integer_rule :=
  repeat unfold modulo, coprime, ideal;
  unfold Z.pow, Z.pow_pos; simpl;
  preprocess; ensatz.

Goal forall a b c:Z, (a | b*c) -> coprime a b -> (a | c).
  integer_rule.
Qed.

Goal forall m n r:Z, (m | r ) -> (n | r) -> coprime m n -> (m*n | r).
  integer_rule.
Qed.

Goal forall x y a n:Z, modulo (x*x) a n -> modulo (y*y) a n -> (n | (x+y)*(x-y)).
  integer_rule.
Qed.

Goal forall x y:Z, (x+y | x^7+y^7).
  integer_rule.
Qed.

Goal forall a b c:Z, (a | b*c) -> coprime a b -> (a | c).
  integer_rule.
Qed.

Goal forall x y:Z, coprime (x*y) (x^2+y^2) <-> coprime x y.
  split; integer_rule.
Qed.

Goal forall x y a n:Z, modulo (x+a) (y+a) n <-> modulo x y n.
  split; integer_rule.
Qed.

Goal forall x n:Z, modulo x 0 n <-> (n | x).
  split; integer_rule.
Qed.

Goal forall x y n:Z, modulo x y n -> (coprime n x <-> coprime n y).
  intros * H; split; revert H; integer_rule.
Qed.

Goal forall a b x y:Z, gcd x a b -> (y | a) -> (y | b) -> (y | x).
  intros * [H1 [H2 H3]]; revert H1 H2 H3.
  integer_rule.
Qed.

Goal forall a x y n:Z, modulo (a*x) (a*y) n -> coprime a n -> modulo x y n.
  integer_rule.
Qed.

Goal forall d a b:Z, (d | a) -> (d | b) -> (d | (a-b)).
  integer_rule.
Qed.

Goal forall a b c:Z, (a | b) -> (c*a | c*b).
  integer_rule.
Qed.

Goal forall x d a:Z, (x*d | a)  -> (d | a).
  integer_rule.
Qed.

Goal forall a b c d:Z, (a | b) -> (c | d) -> (a*c | b*d).
  integer_rule.
Qed.

Goal forall a b d:Z, coprime d a -> coprime d b -> coprime d (a*b).
  integer_rule.
Qed.

Goal forall a b d:Z, coprime d (a*b) -> coprime d a.
  integer_rule.
Qed.

Goal forall m n r:Z, (m | r)  -> (n | r) -> coprime m n -> (m*n | r).
  integer_rule.
Qed.

Goal forall x x' y y' n:Z, modulo x x' n -> modulo y y' n -> modulo (x*y) (x'*y') n.
  integer_rule.
Qed.

Goal forall x y m n:Z, modulo x y m -> (n | m) -> modulo x y n.
  integer_rule.
Qed.

Goal forall a b x y:Z, coprime a b -> modulo x y a -> modulo x y b -> modulo x y (a*b).
  integer_rule.
Qed.

Goal forall x y:Z, modulo (x^2) (y^2) (x+y).
  integer_rule.
Qed.

Goal forall x y a n:Z, modulo (x^2) a n -> modulo (y^2) a n -> (n | (x+y)*(x-y)).
  integer_rule.
Qed.

(* *)
(*      Examples from HOL: *)
(*      https://github.com/jrh13/hol-light/blob/master/Library/integer.ml *)
(* *)

Goal  forall d : Z, (d | d).
  integer_rule.
Qed.

Goal forall x y z : Z, (x | y) -> (y | z) -> (x | z).
  integer_rule.
Qed.

Goal forall d a b : Z, (d | a) -> (d | b) -> (d | a + b).
  integer_rule.
Qed.

Goal forall d a b : Z, (d | a) -> (d | b) -> (d | a - b).
  integer_rule.
Qed.

Goal forall d : Z, (d | 0).
  integer_rule.
Qed.

Goal forall x : Z, (0 | x) <-> x = 0.
  split; preprocess.
  + subst. cring.
  + ensatz.
Qed.

Goal forall d x : Z, ( -d | x) <->  (d | x).
  split; integer_rule.
Qed.

Goal forall d x : Z, (d | --x) <-> (d | x).
  split; integer_rule.
Qed.

Goal forall d x y : Z, (d | x) -> (d | x * y).
  integer_rule.
Qed.

Goal forall d x y : Z, (d | y) -> (d | x * y).
  integer_rule.
Qed.

Goal forall x : Z, ( 1 | x).
  integer_rule.
Qed.

Goal forall d a b : Z, (d | a) -> (d | a + b) -> (d | b).
  integer_rule.
Qed.

Goal forall d a b : Z, (d | b) -> (d | a + b) -> (d | a).
  integer_rule.
Qed.

Goal forall a b c : Z, (a | b) -> (c * a | c * b).
  integer_rule.
Qed.

Goal forall a b c : Z, (a | b) -> (a * c | b * c).
  integer_rule.
Qed.

Goal forall d a x : Z, (x * d | a) -> (d | a).
  integer_rule.
Qed.

Goal forall d a x : Z, (d * x | a) -> (d | a).
  integer_rule.
Qed.

Goal forall a b c : Z, (c * a | c * b) -> c <> 0 -> (a | b).
  intros * H; preprocess.
  revert H.
  rewrite <- Zmult_assoc_reverse, <- Z.mul_shuffle0, Z.mul_comm.
  intros ?%(Z.mul_cancel_r b _ _ H0).
  ensatz.
Qed.

Goal forall a b c : Z, c <> 0 -> ((c * a | c * b) <-> (a | b)).
  intros * H0; split; intros H; preprocess.
  + revert H.
    rewrite <- Zmult_assoc_reverse, <- Z.mul_shuffle0, Z.mul_comm.
    intros ?%(Z.mul_cancel_r b _ _ H0).
    ensatz.
  + ensatz.
Qed.

Goal forall a b c : Z, c <> 0 -> ((a * c | b * c) <-> (a |b)).
  intros * H0;split; intros H; preprocess.
  + revert H.
    rewrite <- Zmult_assoc_reverse.
    intros ?%(Z.mul_cancel_r b _ _ H0).
    ensatz.
  + ensatz.
Qed.

Goal forall a b c d : Z, (a | b)  -> (c | d) -> (a * c | b * d).
  integer_rule.
Qed.

Goal forall x y n : Z,  (x | y) -> (x ^ n  | y ^ n).
  preprocess.
  destruct (Z.le_ge_cases 0 n) as [? | [? %(Z.pow_neg_r y)| -> ] %Zle_lt_or_eq].
  - generalize dependent n.
    apply natlike_rec2.
    + ensatz.
    + preprocess.
      repeat rewrite Z.pow_succ_r by assumption.
      ensatz.
  - ensatz.
  - ensatz.
Qed.

Goal forall n x y : Z, (0 <> n) /\ (x ^ n | y) -> (x | y).
  intros n * [[ ? | ? %(Z.pow_neg_r x)] %not_Zeq ?]; preprocess; subst.
  - assert (exists k, n = Z.succ k)
      by (exists (Z.pred n); rewrite Z.succ_pred;reflexivity).
    preprocess.
    subst.
    rewrite Z.pow_succ_r by (apply Zlt_succ_le;auto).
    ensatz.
  - ensatz.
Qed.

Require Import Reals RNsatz.

Definition div(a b: R):= exists k: R, b = k*a.

Goal forall x y z : R, div x y -> div y z -> div x z.
  unfold div.
  preprocess.
  ensatz.
Qed.
