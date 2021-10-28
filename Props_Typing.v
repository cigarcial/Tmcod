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
forall ( P : Process )( D F G : Context ),
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
Lemma Well_Collected_Reduction :
forall ( D : Context )( P Q : Process)( u x : nat ),
Well_Collected D P -> P --> ({u \ x} Q) ->
Well_Collected D ({u \ x} Q).
Proof.
  constructor.
  intros.
  inversions H.
  specialize (H2 x0 A).
  eauto with Piull.
Qed.
#[global]
Hint Resolve Well_Collected_Reduction : Piull.



(**
*)
Theorem Type_Subst_L :
forall ( P : Process )( x u : nat )( D F G : Context )( A : Proposition ),
( D ;;; F !- P ::: G ) -> ( D ;;; (Sng (FName x:A) ∪ F) !- {u \ x}P ::: G ).
Proof.
Admitted.
#[global]
Hint Resolve Type_Subst_L : Piull.





(**
*)
Theorem Soundness : 
forall (P : Process)(D F G : Context),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P --> Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros P D F G H.
  dependent induction H; intros.
  + apply Fuse_No_Reduces in H3; contradiction.
  + apply Fuse_No_Reduces in H3; contradiction.
  + apply Rep_Input_No_Reduces in H7; contradiction.
(*  + assert (Hx := H10).
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
  + apply Chan_Input_No_Reduces in H4; contradiction.
  + apply Parallel_Res_No_Reduces in H8; contradiction.
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + apply Parallel_Res_No_Reduces in H9; contradiction.
  + apply Chan_Close_No_Reduces in H4; contradiction.
  + apply Zero_No_Reduces in H0; contradiction.
  + apply Chan_Close_No_Reduces in H4; contradiction.
  + apply Zero_No_Reduces in H0; contradiction.
  + apply Output_No_Reduces in H5; contradiction.
  + apply Output_No_Reduces in H5; contradiction.
  + inversions H7.
    - apply (IsClosingInj_inv _ _ u) in H13.
      rewrite <- H13 in *.
      assert ( Hx : [if u =? u then BName 0 else FName u ←→ if y =? u then BName 0 else FName y] = Close_Rec 0 u ([FName u ←→ FName y]) ). Piauto.
      rewrite Hx in H9.
      apply (Close_Same_Inv _ _ u 0) in H9; Piauto.
      rewrite <- H9 in *.
      apply (No_Typing_Fuse_One_Lf A _ _ _ _ ) in H6; try OrSearch.
      
    - apply (IsClosingInj_inv _ _ u) in H13.
      rewrite <- H13 in *.
      assert ( Hx : [if y =? u then BName 0 else FName y ←→ if u =? u then BName 0 else FName u] = Close_Rec 0 u ([FName y ←→ FName u]) ). Piauto.
      rewrite Hx in H9.
      apply (Close_Same_Inv _ _ u 0) in H9; Piauto.
      rewrite <- H9 in *.
      apply (No_Typing_Fuse_One_Rg A _ _ _ _ _) in H6; OrSearch.
    - apply (IsClosingInj_inv _ _ u) in H19.
      rewrite <- H19 in *.
      assert ( Hx : ν (Close_Name 1 u (if u =? y then BName 0 else FName u)
         « Close_Name 1 u (if y =? y then BName 0 else FName y)
         »· Close_Rec 1 u (Close_Rec 0 y Q1)) = Close_Rec 0 u (ν Close_Rec 0 y ( (FName u
         « FName y
         »· Q1) ))). Piauto.
      rewrite Hx in H10.
      apply (Close_Same_Inv _ _ u 0) in H10; Piauto.
      apply (Close_Same_Inv _ _ u 1) in H9; Piauto.
      rewrite H9.
      clear Hx; clear H8; clear IHInference1; clear IHInference2.
      apply (cutrep _ _ _ _ _ A x u); Piauto.
      rewrite <- H10 in H6.
      admit.
    - apply (IsClosingInj_inv _ _ u) in H19.
      rewrite <- H19 in *.
      assert ( Hx : ν (Close_Name 1 u (if u =? y then BName 0 else FName u)
         « Close_Name 1 u (if y =? y then BName 0 else FName y)
         »· Close_Rec 1 u (Close_Rec 0 y Q1)) = Close_Rec 0 u (ν Close_Rec 0 y ( (FName u
         « FName y
         »· Q1) ))). Piauto.
      rewrite Hx in H10.
      apply (Close_Same_Inv _ _ u 0) in H10; Piauto.
      apply (Close_Same_Inv _ _ u 1) in H9; Piauto.
      rewrite H9.
      apply (cutrep _ _ _ _ _ A x u); Piauto.
      rewrite <- H10 in H6.
      inversions H6.
      * admit.
      * admit.

      * admit. (* disjoint contexts *)
      * admit. (* disjoint contexts *)
      * admit. (* disjoint contexts *)

      * apply (IsClosingInj_inv _ _ x0) in H20.
        rewrite  H20 in *.
        apply (Close_Same_Inv _ _ y 0) in H22; Piauto.
        rewrite H22 in *.
        rewrite (App_Nil_Right F).
        rewrite (App_Nil_Right G).
        admit.
      * 
Admitted.










Lemma Inv_Typing_Implication :
forall ( D F0 F' G0 G' : list Assignment ) ( u x2  x0 : nat )( A A0 B : Proposition )( P : Process ), 
( cons (FName u : A) nil ++ D);;;  cons ((FName x2) : (A0 −∘ B)) nil ++ F0 ++ F' !- ν Close x0 (FName u « FName x0 »· P) ::: (G0 ++ G') -> x2 = u.
Proof.
  intros.
  DecidSimple x2 u.
Admitted.





(*


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




*)
