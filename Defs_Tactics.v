(*
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
*)
(*
  
  This file contains convenient tactics.
  En este archivo se definiran las tácticas que se encuentren convenientes.
*)
Ltac inversions H := inversion H; subst.
Ltac isBody := constructor; intros; simpl; repeat constructor.





Ltac InductionProcess P Name_Lemma := 
  induction P;
    intros; simpl;
    try rewrite Name_Lemma;
    try rewrite Name_Lemma;
    repeat match goal with 
      | IHP  : _ |- _  =>  rewrite IHP; auto
      | IHP1 : _ |- _ => try rewrite IHP1; auto
    end.

Ltac InductionProcessRev P Name_Lemma := 
  induction P;
    intros; simpl;
    try rewrite Name_Lemma;
    try rewrite Name_Lemma;
    repeat match goal with 
      | IHP  : _ |- _  =>  rewrite <- IHP; auto
      | IHP1 : _ |- _ => try rewrite <- IHP1; auto
    end.


Ltac UnionSearch H := unfold not; intros; apply H; 
  (left; try left; progress auto) + 
  (right; try left; progress auto) + 
  (left; try right; progress auto) + 
  (right; try right; progress auto).


From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.

Ltac EasyDec x y e n:= 
  destruct (bool_dec (x =? y) true);
    try apply not_true_iff_false in n;
    try rewrite e;
    try rewrite n;
    try simpl;
    auto.



