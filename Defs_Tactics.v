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
*)
Ltac InductionProcess P Name_Lemma := 
  induction P;
    intros; simpl;
    try rewrite Name_Lemma;
    try rewrite Name_Lemma;
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

