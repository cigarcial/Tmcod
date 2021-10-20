(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021

  This file contains the basic facts concerning names.
*)

Require Import Coq.Program.Equality.

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Sets.Constructive_sets.

From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Defs_Proposition.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Typing.
From Tmcod Require Import Facts_Names.
From Tmcod Require Import Facts_FVars.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Facts_MOpen.
From Tmcod Require Import Props_Process.
From Tmcod Require Import Facts_WSubst.
From Tmcod Require Import Facts_Typing.


(**
*)
Theorem Congruence_Reduction : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P === Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros.
  induction H0;
    apply No_Typing_Parallel in H;
    contradiction.
Qed.
#[global]
Hint Resolve Congruence_Reduction : Piull.


(**
*)
Lemma Reduction_Cut_One :
forall (P Q Q0 : Process)(u x : nat),
lc Q -> 
((ν Close u ((FName u !· Close x P) ↓ Q)) --> Q0) -> (exists ( y : nat), Q = [FName u ←→ FName y]) \/ (exists ( y : nat), Q = [FName y ←→ FName u]).
Proof.
  intros.
  inversions H0.
  + left.
    exists y;
    apply (Close_Same_Inv _ _ u 0);
    apply (IsClosingInj_inv _ _ u) in H6;
    rewrite H6 in *; Piauto.
  + right.
    exists y;
    apply (Close_Same_Inv _ _ u 0);
    apply (IsClosingInj_inv _ _ u) in H6;
    rewrite H6 in *; Piauto.
Qed.
#[global]
Hint Resolve Reduction_Cut_One : Piull.


Lemma Well_Collected_Reduction :
forall ( D : list Assignment )( P Q : Process)( u x : nat ),
Well_Collected D P -> P --> ({u \ x} Q) ->
Well_Collected D ({u \ x} Q).
Proof.
  constructor.
  intros.
  inversions H.
  specialize (H1 x0 A).
  destruct H1.
  constructor; intros; eauto with Piull.
Qed.
#[global]
Hint Resolve Well_Collected_Reduction : Piull.


(**
*)
Lemma No_Typing_Fuse_One :
forall (A : Proposition)(D F G : list Assignment)(u x0 u0: nat),
~ ( (((FName u0 : A) :: nil) ++ D);;; F !- [FName u ←→ FName x0] ::: G ).
Proof.
  unfold not.
  intros.
  inversions H.
  + inversions H7.
    specialize (H2 x A).
    assert ( Hx : List.In (FName x : A) (((FName x : A) :: nil) ++ D)).
    do 2 constructor.
    apply H2 in Hx.
    destruct Hx;
     apply Singleton_inv in H3; contradiction.
  + inversions H7.
    specialize (H2 x A).
    assert ( Hx : List.In (FName x : A) (((FName x : A) :: nil) ++ D)).
    do 2 constructor.
    apply H2 in Hx.
    destruct Hx;
     apply Singleton_inv in H3; contradiction.
  + admit.
  + admit.
Admitted.
#[global]
Hint Resolve No_Typing_Fuse_One : Piull.




Lemma Reduction_Cut_Two :
forall ( P Q Q0 : Process )( x : nat),
lc P -> lc Q ->
(ν Close x (P ↓ Q)) --> Q0 -> 
(exists (y:nat), Q = [FName x ←→ FName y]) \/
(exists (y:nat), Q = [FName y ←→ FName x]) \/
(exists (y:nat), P = [FName y ←→ FName x]) \/
(exists (y:nat), P = [FName x ←→ FName y]) \/
False.
Proof.
  intros.
  inversions H1.
  + left.
    exists y.
    apply (Close_Same_Inv _ _ x 0); Piauto.
    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7 in *.
    Piauto.
  + right. left.
    exists y.
    apply (Close_Same_Inv _ _ x 0); Piauto.
    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7 in *.
    Piauto.
  + do 2 right. left.
    exists y.
    apply (Close_Same_Inv _ _ x 0); Piauto.
    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7 in *.
    Piauto.
  + do 3 right. left.
    exists y.
    apply (Close_Same_Inv _ _ x 0); Piauto.
    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7 in *.
    Piauto.
  + admit.
  + admit.
Admitted.


(**
*)
Theorem Soundness : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P --> Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros P D F G H.
  dependent induction H; intros.
  + apply Fuse_No_Reduces in H6; contradiction.
  + apply Fuse_No_Reduces in H5; contradiction.
  + apply Rep_Input_No_Reduces in H9; contradiction.
  + assert (Hx := H14).
    apply (Subst_Reduction_NBeq ({x \ u} P) Q x u) in H14; Piauto.
    rewrite <- Double_Subst_Expan_NFVar in H14; Piauto.
    rewrite Subst_By_Equal in H14.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u); ePiauto.
    constructor; ePiauto.
  + assert (Hx := H6).
    apply (Subst_Reduction_NBeq ({x \ u} P) Q x u) in H6; Piauto.
    rewrite <- Double_Subst_Expan_NFVar in H6; Piauto.
    rewrite Subst_By_Equal in H6.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u); ePiauto.
  + apply Rep_Input_No_Reduces in H3; contradiction.
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + apply Parallel_Res_No_Reduces in H9; contradiction.
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + apply Parallel_Res_No_Reduces in H9; contradiction.
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + apply Parallel_Res_No_Reduces in H9; contradiction.
  + apply Chan_Close_No_Reduces in H5; contradiction.
  + apply Zero_No_Reduces in H1; contradiction.
  + apply Chan_Close_No_Reduces in H5; contradiction.
  + apply Zero_No_Reduces in H1; contradiction.
  + apply Output_No_Reduces in H5; contradiction.
  + apply Output_No_Reduces in H5; contradiction.
  + specialize (Reduction_Cut_One _ _ _ _ _ H3 H7) as Hx.
    destruct Hx.
    - destruct H8.
      rewrite H8 in H6.
      apply No_Typing_Fuse_One in H6.
      contradiction.
    - destruct H8.
      rewrite H9 in H6.
      apply No_Typing_Fuse_One in H6.
      contradiction.
  + admit.
  + apply Reduction_Cut_Two in H8; Piauto.
    destruct H8.

    destruct H8.
    rewrite H8 in *.
    
    
    
    
  + inversions H8.
Admitted.

