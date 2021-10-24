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


From Coq Require Import Lists.List.
Import ListNotations.


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
lc P -> lc Q -> 
((ν Close u ((FName u !· Close x P) ↓ Q)) --> Q0) -> 

(exists ( y : nat), Q = [FName u ←→ FName y]) \/ 
(exists ( y : nat), Q = [FName y ←→ FName u]) \/ 
(exists ( y : nat)(R : Process), lc R /\ 
  Q = ν Close y ((FName u) « (FName y) »· R) /\ 
  Q0 = ν Close u ((FName u !· Close x P) ↓ (ν Close y (R ↓ (Close x P) ^ y))) 
  /\ IsClosing R y /\ IsClosingInj R y
  ) \/ 
(exists ( y : nat)(R : Process), lc R /\ 
  Q = ν Close y ((FName u) « (FName y) »· R) /\
  Q0 = ν Close u ((FName u !· Close x P) ↓ (ν Close y ((Close x P) ^ y ↓ R))) 
  /\ IsClosing R y /\ IsClosingInj R y
  )
.
Proof.
  intros.
  inversions H1.
  + left.
    exists y;
    apply (Close_Same_Inv _ _ u 0); Piauto.
    apply (IsClosingInj_inv _ _ u) in H7.
    rewrite H7 in *; Piauto.
  + right. left.
    exists y;
    apply (Close_Same_Inv _ _ u 0);
    apply (IsClosingInj_inv _ _ u) in H7;
    rewrite H7 in *; Piauto.
  + do 2 right. left.
    exists y.
    exists Q1.
    constructor; Piauto.
    constructor.
      apply (Close_Same_Inv _ _ u 0); Piauto.
      apply (IsClosingInj_inv _ _ u) in H13; Piauto.
      rewrite H13 in *; Piauto.
      
     constructor; ePiauto.
      apply (IsClosingInj_inv _ _ u) in H13; Piauto.
      rewrite H13 in *; Piauto.
      apply Close_Same_Inv in H3; Piauto.
      rewrite H3 in *; Piauto.
     
  + do 3 right.
    exists y.
    exists Q1.
    constructor; Piauto.
    constructor.
      apply (Close_Same_Inv _ _ u 0); Piauto.
      apply (IsClosingInj_inv _ _ u) in H13; Piauto.
      rewrite H13 in *; Piauto.
    
    constructor; ePiauto.
      apply (IsClosingInj_inv _ _ u) in H13; Piauto.
      rewrite H13 in *; Piauto.
      apply Close_Same_Inv in H3; Piauto.
      rewrite H3 in *; Piauto.
Qed.
#[global]
Hint Resolve Reduction_Cut_One : Piull.


(**
*)
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
Lemma Reduction_Cut_Two :
forall ( P Q Q0 : Process )( x : nat),
lc P -> lc Q ->
(ν Close x (P ↓ Q)) --> Q0 -> 

((exists (y:nat)(P0 : Process), Q = [FName x ←→ FName y] /\ Q0 = {y \ x} P0 ) \/
(exists (y:nat), Q = [FName y ←→ FName x]) \/
(exists (y:nat), P = [FName y ←→ FName x]) \/
(exists (y:nat), P = [FName x ←→ FName y]) \/
False).
Proof.
  intros.
  inversions H1.
  + left.
    exists y.
    exists P0.
    constructor.
    apply (Close_Same_Inv _ _ x 0); Piauto.
    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7 in *.
    Piauto.

    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7.
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
Theorem Type_Subst_L :
forall ( P : Process )( x u : nat )( D F G : list Assignment )( A : Proposition ),
( D ;;; ((FName x : A) :: nil) ++ F !- P ::: G ) -> ( D ;;; ((FName u : A) :: nil) ++ F !- {u \ x}P ::: G ).
Proof.
Admitted.
#[global]
Hint Resolve Type_Subst_L : Piull.


(**
*)
Lemma No_Typing_Fuse_One :
forall (A : Proposition)(D F G : list Assignment)(u x0 u0: nat),
~ ( (((FName u0 : A) :: nil) ++ D);;; F !- [FName u ←→ FName x0] ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H.
  + admit.
  + admit.
  + apply (Equality_Subst_Equality _ _ u1 x1) in x.
    rewrite <- Double_Subst_Expan_NFVar in x; Piauto.
    rewrite Subst_By_Equal in x.
    simpl in x.
    DecidSimple u x1.
    - rewrite e in x.
      DecidSimple x0 x1.
      * rewrite e0 in x.
        apply (IHInference A0 ((cons (FName u0 : A) nil) ++ D) u1 u1 u1); Piauto.
      * rewrite n in x.
        apply (IHInference A0 ((cons (FName u0 : A) nil) ++ D) u1 x0 u1); Piauto.
    - rewrite n in x.
      DecidSimple x0 x1.
      * rewrite e in x.
        apply (IHInference A0 ((cons (FName u0 : A) nil) ++ D) u u1 u1); Piauto.
      * rewrite n0 in x.
        apply (IHInference A0 ((cons (FName u0 : A) nil) ++ D) u x0 u1); Piauto.
  + apply (Equality_Subst_Equality _ _ u1 x1) in x.
    rewrite <- Double_Subst_Expan_NFVar in x; Piauto.
    rewrite Subst_By_Equal in x.
    simpl in x.
    DecidSimple u x1.
    - rewrite e in x.
      DecidSimple x0 x1.
      * rewrite e0 in x.
        apply (IHInference A0 ((cons (FName u0 : A) nil) ++ D) u1 u1 u1); Piauto.
      * rewrite n in x.
        apply (IHInference A0 ((cons (FName u0 : A) nil) ++ D) u1 x0 u1); Piauto.
    - rewrite n in x.
      DecidSimple x0 x1.
      * rewrite e in x.
        apply (IHInference A0 ((cons (FName u0 : A) nil) ++ D) u u1 u1); Piauto.
      * rewrite n0 in x.
        apply (IHInference A0 ((cons (FName u0 : A) nil) ++ D) u x0 u1); Piauto.
Admitted.
#[global]
Hint Resolve No_Typing_Fuse_One : Piull.




Lemma Inv_Typing_Implication :
forall ( D F0 F' G0 G' : list Assignment ) ( u x2  x0 : nat )( A A0 B : Proposition )( P : Process ), 
( cons (FName u : A) nil ++ D);;;  cons ((FName x2) : (A0 −∘ B)) nil ++ F0 ++ F' !- ν Close x0 (FName u « FName x0 »· P) ::: (G0 ++ G') -> x2 = u.
Proof.
  intros.
  DecidSimple x2 u.
Admitted.




(**
*)
Theorem Soundness : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P --> Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros P D F G H.
  dependent induction H; intros.
  + apply Fuse_No_Reduces in H4; contradiction.
  + apply Fuse_No_Reduces in H4; contradiction.
  + apply Rep_Input_No_Reduces in H7; contradiction.
(*   + assert (Hx := H10).
    apply (Subst_Reduction_NBeq ({x \ u} P) Q x u) in H10; Piauto.
    rewrite <- Double_Subst_Expan_NFVar in H10; Piauto.
    rewrite Subst_By_Equal in H10.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u); ePiauto.
    constructor; ePiauto.
  + assert (Hx := H6).
    apply (Subst_Reduction_NBeq ({x \ u} P) Q x u) in H6; Piauto.
    rewrite <- Double_Subst_Expan_NFVar in H6; Piauto.
    rewrite Subst_By_Equal in H6.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u); ePiauto. *)
  + admit.
  + admit.
  + apply Rep_Input_No_Reduces in H3; contradiction.
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + apply Parallel_Res_No_Reduces in H8; contradiction.
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
  + specialize (Reduction_Cut_One _ _ _ _ _ H2 H3 H7) as Hx.
    destruct Hx.
     destruct H8.
      rewrite H8 in H6.
      apply No_Typing_Fuse_One in H6.
      contradiction.

     destruct H8.
      destruct H8.
      rewrite H8 in H6.
      apply No_Typing_Fuse_One in H6.
      contradiction.

     destruct H8.
      do 3 destruct H8.
      destruct H9.
      destruct H10.
      rewrite H9 in *.
      rewrite H10 in *.
      apply (cutrep _ _ _ _ _ A _ _); Piauto.
      inversions H6.
        
        admit.
        admit.
        
        destruct H11.
        apply (IsClosing_inv _ _ u u) in H9.
        destruct H9.
        DecidSimple u x0.
        rewrite n in H12.
        DecidSimple x2 y; try rewrite e in H12; try inversions H12.
        rewrite n0 in H23.
        inversions H23.
        admit. (* *)
        
        assert( Hx : y = x0). admit.
        rewrite Hx in *.
        admit.
        admit.
        admit.

        admit.
        
      
      
      do 3 destruct H8.
      destruct H9.
      destruct H10.
      rewrite H9 in *.
      rewrite H10 in *.
      apply (cutrep _ _ _ _ _ A _ _); Piauto.
      inversions H6.
        
        admit.
        admit.
        
        admit.
        admit.
        admit.
      
        destruct H11.
        assert ( Ht : x2 = x0 ). admit.
        rewrite Ht in *.
        apply (Close_Same_Inv  P0 x1 _ _ ) in H14; Piauto.
        rewrite H14 in *.
        apply (cutr (cons ((FName u):A) nil ++ D) nil nil F G  _ _ A x0); Piauto.

      
  + admit.
  + apply Reduction_Cut_Two in H8; Piauto.
    destruct H8.

    do 3 destruct H8.
    assert ( F' = nil ). admit.
    assert ( G' = (cons (FName x0 : A) nil) ). admit.
    subst.
    admit.
    
    destruct H8.
    admit.
    
    destruct H8.
    admit.
    
    destruct H8.
    admit.
    
    destruct H8.
    admit.
    
    
    
    
    
    
Admitted.



