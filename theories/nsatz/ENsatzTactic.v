(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*
 Tactic ensatz: proofs of polynomials equalities in an integral domain
 (commutative ring without zero divisor) with existential quantifier.

Examples: see test-suite/success/ENsatz.v

*)

From Stdlib Require Import List.
From Stdlib Require Import Setoid.
From Stdlib Require Import BinPos.
From Stdlib Require Import BinList.
From Stdlib Require Import Znumtheory.
From Stdlib Require Export Morphisms Setoid Bool.
From Stdlib Require Export Algebra_syntax.
From Stdlib Require Export Ncring.
From Stdlib Require Export Ncring_initial.
From Stdlib Require Export Ncring_tac.
From Stdlib Require Export Integral_domain.
From Stdlib Require Import ZArith.

From Stdlib Require Import NsatzTactic.

Declare ML Module "rocq-runtime.plugins.nsatz".

Section ensatz.

Context {R:Type}`{Rid:Integral_domain R}.

Fixpoint Cond0 (A:Type) (Interp:A->R) (l:list A) : Prop :=
  match l with
  | List.nil => True
  | a::l => Interp a == 0 /\ Cond0 A Interp l
  end.

Fixpoint BFType (A : Type) (l : list A) {struct l} : Type :=
  match l with
  | nil => unit
  |  _ :: l0 =>  (R * BFType A l0)%type
  end.

Fixpoint BCond0 (A : Type) (Interp : A -> R) (l : list A) {struct l} : (BFType A l -> R) :=
  match l return (BFType A l -> R) with
| nil => (fun _ => ring0)
| a :: l0 => (fun n => add (mul (fst n) (Interp a))
                             (BCond0 A Interp l0 (snd n)))
end.

Definition mk_BCond0 (A : Type) (Interp : A -> R) (l : list A) (v : R) :=
  exists n, (v == BCond0 A Interp l n).

Fixpoint ring0_tuple (A :Type) (l: list A) : BFType A l :=
  match l return (BFType A l) with
  | nil => tt
  | a :: q => (ring0, ring0_tuple A q)
  end.

(* The type of the existential *)

Fixpoint FType (A : Type) (l : list (bool * A)) {struct l} : Type :=
  match l with
  | nil => unit
  | (true, _) :: l0 =>  (R * FType A l0)%type
  | (false,_)  :: l0 =>  FType A l0
  end.

(* For the conclusion *)

Fixpoint GCond0 (A : Type) (Interp : A -> R) (l : list (bool * A)) {struct l} : (FType A l -> R) :=
  match l return (FType A l -> R) with
| nil => (fun _ => ring0)
| (true, a) :: l0 => (fun n => add (mul (fst n) (Interp a))
                             (GCond0 A Interp l0 (snd n)))
| (false, a) :: l0 => GCond0 A Interp l0
end.

Definition mk_GCond0 (A : Type) (Interp : A -> R) (l : list (bool * A)) (v : R) :=
  exists n, (v == GCond0 A Interp l n).

(* For the assumptions *)

Fixpoint mk_HCond0 (A : Type) (Interp : A -> R) (l : list (bool * A)) {struct l} : Prop :=
  match l with
  | nil => True
  | (true, a) :: l0 => (mk_HCond0 A Interp l0)
  | (false, a) :: l0 => ((Interp a) == 0) /\ (mk_HCond0 A Interp l0)
  end.

Fixpoint add_coef
  (A : Type)
  (Interp : A -> R)
  (l: list A)  (a : list A)
  (c : R) {struct l} : (BFType A l -> BFType A l) :=
  match l, a return  (BFType A l -> BFType A l) with
  | nil, _ => (fun _ => tt)
  | _, nil => (fun x => x)
  | h :: q , hx :: qx =>
      let coef := c * (Interp hx) in
      fun x => (coef + fst x, add_coef A Interp q qx c (snd x))
  end.

Definition PhiR := @PhiR R ring0 ring1 add mul opp.

Lemma factories_compute_list :
  forall lla l lpe lq,
  mk_BCond0 PolZ (PhiR l) lpe
    (PhiR l (mult_l lq (compute_list lla lpe))).
Proof.
  unfold mk_BCond0.
  induction lla.
  - induction lpe.
    + destruct lq;simpl;exists tt; reflexivity.
    + intros;simpl.
      destruct lq.
      * simpl.
        simpl in IHlpe.
        specialize (IHlpe nil) as (x,H).
        exists (ring0,x).
        rewrite <- H.
        cring.
      * simpl.
        simpl in IHlpe.
        specialize (IHlpe lq) as (x, H).
        exists (PhiR l (norm p),x);unfold PhiR.
        rewrite  PolZadd_correct.
        rewrite PolZmul_correct.
        rewrite <- H.
        cring.
   - intros. simpl.
     specialize (IHlla l (mult_l a lpe :: lpe) lq).
     destruct IHlla.
     simpl in H.
     exists (add_coef PolZ (PhiR l) lpe (map norm a) (fst x) (snd x)).
     unfold PhiR. rewrite H. clear H.
     destruct x.
     simpl.
     generalize dependent lpe.
     induction a.
     + intros; destruct lpe; cring.
     + intros.
       destruct lpe;[ cring |].
       simpl. unfold PhiR.
       rewrite PolZadd_correct.
       rewrite PolZmul_correct.
       specialize (IHa lpe (snd b)).
       rewrite <- IHa.
       cring.
Qed.

Fixpoint btype_to_ftype
  (A B : Type)
  (norm :  A -> B)
  (l: list (bool*A)) {struct l} : (BFType B (map norm (map snd l)) -> FType A l) :=
  match l return  (BFType B (map norm (map snd l)) -> FType A l) with
  | nil => fun _ => tt
  | (true,a) :: q =>  fun x => (fst x, btype_to_ftype A B norm  q (snd x))
  | (false,a) :: q =>  fun x => (btype_to_ftype A B norm q (snd x))
  end.

Lemma check_correct_exists :
  forall l lpe qe lci lq ,
    check (map snd lpe) qe (lci,lq) = true ->
    mk_HCond0 PEZ (PEevalR l) lpe ->
    mk_GCond0 PEZ (PEevalR l) lpe (PEevalR l qe).
Proof.
  unfold check;intros l lpe qe lla lq H2 H1.
  apply PolZeq_correct with (l:=l) in H2.
  unfold mk_GCond0.
  specialize (factories_compute_list lla l (map norm (map snd lpe)) lq) as H.
  unfold mk_BCond0 in H. destruct H.
  rewrite H in H2.
  clear H.
  exists (btype_to_ftype PEZ PolZ norm lpe x).
  rewrite norm_correct.
  rewrite H2.
  clear H2.
  induction lpe.
  - cring.
  - destruct a.
    destruct b.
    + simpl in H1.
      destruct x.
      specialize (IHlpe b H1).
      simpl.
      rewrite IHlpe.
      rewrite norm_correct.
      reflexivity.
    + destruct H1.
      destruct x.
      specialize (IHlpe b H0).
      simpl.
      rewrite IHlpe.
      unfold PhiR.
      rewrite <- norm_correct.
      rewrite H.
      cring.
Qed.

End ensatz.

Fixpoint set_false (l: list (PExpr Z)) :=
  match l with
  | nil => nil
  | h :: q => (false, h) :: (set_false q)
  end.

Fixpoint set_true (l: list (PExpr Z)) :=
  match l with
  | nil => nil
  | h :: q => (true, h) :: (set_true q)
  end.

Lemma efactor:
  forall A B P,  (exists x : A * B, P (fst x) (snd x)) -> (exists x : A, exists y: B, P x y).
Proof.
  intros A B P [x H].  eauto.
Qed.

Lemma efactor1:
  forall A B P,  (exists x : A, exists y: B, P (x, y)) -> (exists x : A * B, P x).
Proof.
intros A B P [x [y HP]]; exists (x, y); auto.
Qed.

Ltac hterm R g :=
  match g with
  | (exists _: _, _ ) => constr:((@nil R))
  | ?b1 == ?b2 -> ?g => let l := hterm R g in
                      constr:((b1 :: l))
  end.

Inductive Var {A: Type}: Type :=
| mRef: A -> Var
| fstVar :forall B,  @Var (A*B) -> @Var A
| sndVar : forall B, @Var (B*A) -> @Var A.

Ltac reify_evar_aux term :=
  match term with
  | (fun e => fst (@?P e)) =>
       let term' := reify_evar_aux P in
       constr:(fun x => @fstVar _ _ (term' x))
  | (fun e => snd (@?P e)) =>
      let term' := reify_evar_aux P in
      constr:(fun x => @sndVar _ _ (term' x))
  | (fun e:?T => e) => constr:(fun e :T => mRef e)
  end.

Inductive MPoly {R: Type}: Type:=
| Poly : MPoly -> (PExpr Z) -> @Var R -> MPoly
| Pc : (PExpr Z) -> MPoly.

Ltac reify_evar R term :=
  match term with
  | (fun e => fst _) =>
      let term' := reify_evar_aux term in
      constr:(fun e' => @Poly R (@Pc R (PEc 0%Z)) (PEc 1%Z) (term' e'))
  | (fun e => snd _) =>
      let term' := reify_evar_aux term in
      constr:(fun e' => @Poly R (@Pc R (PEc 0%Z)) (PEc 1%Z) (term' e'))
  | (fun e:?T => e) =>  constr:(fun e':T => @Poly T (@Pc T (PEc 0%Z)) (PEc 1%Z) (mRef e'))
  end.

Fixpoint mult_mpoly {A: Type} (c : PExpr Z) (p : @MPoly A) : @MPoly A :=
  match p with
  | Pc e => Pc (PEmul e c)
  | Poly p e v => Poly (mult_mpoly c p) (PEmul e c) v
  end.

Fixpoint equal {A1 A2: Type} (v1 : @Var A1) (v2 : @Var A2): comparison :=
    match v1, v2 with
    | mRef _, mRef _ => Eq
    | fstVar _ v1, fstVar _ v2 => equal v1 v2
    | sndVar _ v1, sndVar _ v2 => equal v1 v2
    | fstVar _ _, sndVar _ _ => Gt
    | sndVar _ _, fstVar _ _ => Lt
    | _, mRef _ => Gt
    | mRef _, _ => Lt
    end.

Inductive Monom {R: Type}: Type:=
| Mon : (PExpr Z) -> @Var R -> Monom
| Monc : (PExpr Z) -> Monom.

Fixpoint add_monom_poly {A: Type} (p: @MPoly A) (m: @Monom A) :=
  match p with
  | Pc e1 =>
      match m with
      | Monc e2 => Pc (PEadd e1 e2)
      | Mon e2 v => Poly p e2 v
      end
  | Poly p' e1 v1 =>
      match m with
      | Monc e2 => Poly (add_monom_poly p' m) e1 v1
      | Mon e2 v2 =>
          match equal v1 v2 with
          | Eq => Poly p' (PEadd e1 e2) v1
          | Gt => Poly (add_monom_poly p' m) e1 v1
          | Lt => Poly p e2 v2
          end
      end
  end.

Fixpoint add_mpoly {A: Type} (p1 p2 : @MPoly A) : @MPoly A :=
  match p1 with
  | Pc e1 => add_monom_poly p2 (Monc e1)
  | Poly p1' e1 v1 => add_mpoly p1' (add_monom_poly p2 (Mon e1 v1))
  end.

Fixpoint opp_mpoly {A: Type} (p: @MPoly A) : @MPoly A :=
  match p with
  | Pc e => Pc (PEopp e)
  | Poly p e v => Poly (opp_mpoly p) (PEopp e) v
  end.

Ltac reify R Tring lvar term:=
  match open_constr:((Tring, term)) with
  | (Ring (T:=?R) (add:=?add) (mul:=?mul) (sub:=?sub),
      (fun e1 => ?op (@?E1 e1) (@?E2 e1))) =>
      let _ := match goal with _ => convert add op end in
      let E1' := reify R Tring lvar E1 in
      let E2' := reify R Tring lvar E2 in
      constr:(fun x => add_mpoly (E1' x) (E2' x))
  | (Ring (T:=?R) (add:=?add) (mul:=?mul) (sub:=?sub),
      (fun e1 => ?op (@?E1 e1) (@?E2 e1))) =>
      let _ := match goal with _ => convert sub op end in
      let E1' := reify R Tring lvar E1 in
      let E2' := reify R Tring lvar E2 in
      constr:(fun x => add_mpoly (E1' x) (opp_mpoly (E2' x)))
  | (Ring (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
          (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp),
      (fun e1 => ?op ?E (@?E1 e1))) =>
      let _ := match goal with _ => convert mul op end in
      let E1' := reify R Tring lvar E1 in
      let E' := reify_term R ring0 ring1 add mul sub opp lvar E in
      constr:(fun x => mult_mpoly E' (E1' x))
  | (Ring (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
          (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp),
      (fun e1 => ?op (@?E1 e1) ?E)) =>
      let _ := match goal with _ => convert mul op end in
      let E1' := reify R Tring lvar E1 in
      let E' := reify_term R ring0 ring1 add mul sub opp lvar E in
      constr:(fun x => mult_mpoly E' (E1' x))
  | (_, (fun e => @?E e)) => reify_evar R E
  | (Ring (T:=?R) (opp:=?opp), (fun e => ?op (@?E e))) =>
      let _ := match goal with _ => convert opp op end in
      let E' := reify_evar R E in
      constr:(fun x => opp_mpoly (E' x))
  | (Ring (T:=?R) (ring0:=?ring0) (ring1:=?ring1)
          (add:=?add) (mul:=?mul) (sub:=?sub) (opp:=?opp),
       (fun _:?T => ?E)) =>
      let E' := reify_term R ring0 ring1 add mul sub opp lvar E in
      constr:(fun _:T => @Pc R E')
  end.

Fixpoint get_coef {A:Type} (p: @MPoly A) :=
  match p with
  | Pc e => e :: nil
  | Poly p e v => e :: get_coef p
  end.

Definition coef {A R:Type} (p: A -> @MPoly R) :=
  fun x => get_coef (p x).

Definition merge {A R:Type} (p1 p2: A -> @MPoly R) :=
  fun x => add_mpoly (p1 x) (opp_mpoly (p2 x)).

Ltac reify_goal  :=
  match goal with
  | |- @ex _ (fun e1 : _ => @eq ?R (@?P1 e1) (@?P2 e1)) =>
      let lvar := open_constr:(_ :> list R) in
      let R_ring := constr:(_ :> Ring (T:=R)) in
      let Tring := type of R_ring in
      let xl := reify R Tring lvar P1 in
      let xr := reify R Tring lvar P2 in
      let x := eval cbv delta
                 [merge coef
                    get_coef
                    add_mpoly
                    mult_mpoly
                    add_monom_poly
                    equal
                    opp_mpoly]
                 beta iota in (coef (merge xr xl))
        in
        constr:((lvar,x))
  end.

Ltac mk_tuple R l f :=
  match l with
  | (?a :: ?h) =>
      let t := mk_tuple R h f in
      constr:((t, f a))
  | (?a1 :: ?a2 :: @nil R) => constr:((f a2,f a1))
  end.

Ltac destr_tuple R l f :=
      match goal with
      | x : (R * ?A)%type |- _ =>
          let z := fresh "z" in
          destruct x as [z x];
          let l := constr:(z :: l) in
          destr_tuple R l f
      | x : (unit)%type |- _ =>
          let l := eval compute in (l) in
          let t := mk_tuple R l f in
          exists t
      end.

Ltac mk_exists R x f :=
  match goal with
  | x : (R * unit)%type |- _ =>
      let z := fresh "z" in
      destruct x as [z x]; exists (f z)
  | x : (R * ?A)%type |- _ => destr_tuple R constr:(@nil R) f
  end.

Ltac mk_pl lp21 n :=
  let lp21 := eval compute in (List.rev lp21) in
  let hd   := eval compute in (firstn n lp21) in
  let hdt  := eval compute in (set_true hd) in
  let tl   := eval compute in (skipn n lp21) in
  let tlf  := eval compute in (set_false tl) in
  let pl   := eval compute in (hdt ++ tlf) in
  eval compute in (List.rev pl).

Ltac reify_h lv lb :=
  match lb with
  | @nil ?R =>
      let _ := match goal with _ => close_varlist lv end in
      constr:((lv, (@nil (PExpr Z))))
  | @cons ?R _ _ => list_reifyl lv lb
 end.

Ltac ensatz_solve R p2 lp2 n fv info :=
  let p21 := fresh "p21" in
  let lp21 := fresh "lp21" in
  let n21 := fresh "n21" in
  let lv := fresh "lv" in
  set (p21:=p2); set (lp21:=lp2); set (n21:= n); set(lv := fv);
  (*We want r to be 1, so we set radicalmax to 1*)
  NsatzTactic.nsatz_call 1%N info 0%Z p2 lp2
    ltac:(fun c r lq lci =>
            let Hg := fresh "Hg" in
            let c21 := fresh "c" in
            set (c21 := c);
            let p211 := constr: (PEmul c p21) in
            (*If c is not 1/-1, this assert should fail*)
            assert (Hg:check lp21 p211 (lci,lq) = true);
            [vm_compute; reflexivity |];
            let pl := mk_pl lp21 n in
            assert (Hg2: mk_HCond0 PEZ (PEevalR lv) pl);
            [repeat (split;[assumption|idtac]); exact I|];
            generalize (@check_correct_exists
                          _ _ _ _ _ _ _ _ _ _ _
                          lv pl p211 lci lq Hg Hg2);
            unfold mk_GCond0;
            let x := fresh "x" in
            let H1 := fresh "H" in
            intros [x H1]; simpl in x;
            match c with
            | PEc(-1) => mk_exists R x constr:(fun x:R => -x);
                         symmetry in H1
            | PEc(1%Z) =>  mk_exists R x constr:(fun x:R => x)
            end;
            cbv delta [PEevalR GCond0
                         Ring_polynom.PEeval
                         gen_phiZ gen_phiPOS
                         InitialRing.gen_phiZ
                         InitialRing.gen_phiPOS
                         BinList.nth
                         jump nth lv p21 fst snd hd]
              iota beta match in H1;
              apply NsatzTactic.psos_r1b;
              NsatzTactic.equalities_to_goal;
              intros <-; cring ).

Ltac ensatz_default info :=
  intros;
  repeat apply efactor;
  match goal with
  | |- @ex _ (fun e1 : _ => @eq ?R (@?P1 e1) (@?P2 e1)) =>
      match reify_goal with
      | (?lvar, (fun _: _ => ?x)) =>
          let b := eval simpl in (List.last x (PEc 0%Z)) in
            let b := constr: (PEopp b) in
            let l := constr: (List.removelast x) in
            let n := eval compute in (List.length l) in
            repeat NsatzTactic.equalities_to_goal;
            match goal with
              |- ?g =>
                let lb := hterm R g in
                intros;
                match reify_h lvar lb with
                 |(?fv, ?le) =>
                    let l := constr: (List.rev_append le l) in
                    let le := constr: (b :: l) in
                    let lpol := eval compute in le in
                    match lpol with
                    | ?p2::?lp2 => ensatz_solve R p2 lp2 n fv info
                    | ?g => idtac "polynomial not in the ideal"
                 end
              end
          end
    end
end.

Tactic Notation "ensatz" := ensatz_default 1%Z.

Tactic Notation "ensatz" "with"
 "strategy" ":=" constr(info) :=
  ensatz_default info.
