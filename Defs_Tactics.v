(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the tactis and Hint Db for the proofs.
*)
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Finite_sets_facts.

(**
  Custom database for the hints.
*)
Create HintDb Piull.


(**
  Invert a given hypothesis and cleans up all generates equalities.
*)
Ltac inversions H := inversion H; subst.


(**
  This resolves easy structural inductions over a given term (T).
*)
Ltac StructuralInduction T :=
  intros;
  induction T;
  simpl;
  repeat match goal with 
      | IHT  : _ |- _  =>  rewrite IHT
  end;
  auto with Piull.


(**
*)
Ltac DecidSimple x y := 
  destruct (bool_dec (x =? y) true);
  match goal with
    | e : (x =? y ) = true |- _ => 
      (rewrite e; apply beq_nat_true in e; rewrite e; progress auto with Piull) +
      (apply beq_nat_true in e; lia; progress auto with Piull) +
      (try rewrite e)
    | n : (x =? y ) <> true |- _ =>
      (apply not_true_iff_false in n; try rewrite n; progress auto with Piull) +
      (apply not_true_iff_false in n; try apply beq_nat_false in n; try contradiction; progress auto with Piull) +
      (apply not_true_iff_false in n)
  end;
  auto with Piull.


(**
*)
Ltac Piauto := auto with Piull.


(**
  Searching a proof where the goal contains multiple or operators.
  Keep in mind that this tactics is exponential.
*)
Ltac OrSearch :=
  (progress auto with *) +
  (left; OrSearch) + 
  (right; OrSearch).


(**
*)
Ltac OrSearchRew L :=
  (rewrite L; simpl; progress auto with *) +
  (left; OrSearchRew L) +
  (right; OrSearchRew L).


(**
*)
Ltac OrSearchApp L :=
  (apply L; simpl; progress auto with *) +
  (left; OrSearchApp L) +
  (right; OrSearchApp L).


(**
*)
Ltac FVars_Open_Lt H i i0 := 
  DecidSimple i i0;
  match goal with
    | e : (i =? i0 ) = true |- _ => rewrite e in H;
          simpl in H;
          apply Singleton_inv in H;
          rewrite H
    | n : (i =? i0 ) = false |- _ => rewrite n in H;
        simpl in H;
        contradiction
  end; Piauto.


(**
*)
Ltac FVars_Beq_Close_Lt H x x1 := 
  DecidSimple x x1;
  match goal with
    | e : (x =? x1 ) = true |- _ => try rewrite e in H;
          simpl in H;
          contradiction
    | n : (x =? x1 ) = false |- _ => rewrite n in H;
        apply Singleton_inv in H;
        rewrite H;
        simpl
  end; OrSearch.







(**
*)
Ltac InductionProcess P Name_Lemma := 
  induction P;
    intros; simpl;
    repeat rewrite Name_Lemma;
    repeat match goal with 
      | IHP  : _ |- _  =>  rewrite IHP; auto
      | IHP1 : _ |- _ => try rewrite IHP1; auto
    end.


(**
*)
Ltac InductionProcessRev P Name_Lemma := 
  induction P;
    intros; simpl;
    try rewrite Name_Lemma;
    try rewrite Name_Lemma;
    repeat match goal with 
      | IHP  : _ |- _  =>  rewrite <- IHP; auto
      | IHP1 : _ |- _ => try rewrite <- IHP1; auto
    end.


(**
*)
Ltac UnionSearch H := unfold not; intros; apply H; 
  (left; try left; progress auto) + 
  (right; try left; progress auto) + 
  (left; try right; progress auto) + 
  (right; try right; progress auto).







(**
*)
Ltac isBody := constructor; intros; simpl; repeat constructor.

