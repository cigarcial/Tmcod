(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the facts for typing structures.
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


(**
*)
Lemma Fuse_No_Reduces :
forall (x y : Name)(Q : Process), 
~([x ←→  y] --> Q ).
Proof.
  unfold not.
  intros.
  inversions H.
Qed.
#[global]
Hint Resolve Fuse_No_Reduces : Piull.


(**
*)
Lemma Rep_Input_No_Reduces :
forall (x: Name)(y : nat)(P Q : Process),
~((x !· Close y P) --> Q).
Proof.
  unfold not.
  intros.
  inversions H.
Qed.
#[global]
Hint Resolve Rep_Input_No_Reduces : Piull.


(**
*)
Lemma Chan_Close_No_Reduces :
forall (x : Name)(P Q : Process),
~((x ()·P) --> Q).
Proof.
  unfold not.
  intros.
  inversions H.
Qed.
#[global]
Hint Resolve Chan_Close_No_Reduces : Piull.


(**
*)
Lemma Zero_No_Reduces :
forall (x : Name)(Q : Process), 
~((x ·θ) --> Q).
Proof.
  unfold not.
  intros.
  inversions H.
Qed.
#[global]
Hint Resolve Zero_No_Reduces : Piull.


(**
*)
Lemma Chan_Input_No_Reduces :
forall (x : Name)(y : nat)(P Q : Process),
~( (x · Close y P) --> Q ).
Proof.
  unfold not.
  intros.
  inversions H.
Qed.
#[global]
Hint Resolve Chan_Input_No_Reduces : Piull.


(**
*)
Lemma Parallel_Res_No_Reduces :
forall (x : Name)(y : nat)(P Q Q0 : Process),
~( (ν Close y (x « FName y »· (P ↓ Q))) --> Q0 ).
Proof.
  unfold not.
  intros.
  inversions H.
Qed.
#[global]
Hint Resolve Parallel_Res_No_Reduces : Piull.


(**
*)
Lemma Output_No_Reduces :
forall (u x: nat)(P Q : Process),
~( (ν Close x (FName u « FName x »· P)) --> Q ).
Proof.
  unfold not.
  intros.
  inversions H.
Qed.
#[global]
Hint Resolve Output_No_Reduces : Piull.


(**
*)
Lemma Extension_On_Names_Red :
forall (P Q P0_2 P0_1 : Process)(x0 u x : nat)(x1 : Name),
lc ((x1 !· P0_1) ↓ P0_2) ->
Close x0 ((x1 !· P0_1) ↓ P0_2) = Close u ((FName u !· Close x P) ↓ Q) -> x1 = FName x0.
Proof.
  intros.
  inversions H0.
  specialize (beq_nat_refl u) as Hx.
  apply eq_sym in Hx.
  rewrite Hx in *.
  inversions H.
  inversions H6.
  inversions H8.
  simpl in H2.
  DecidSimple x2 x0; try rewrite n in H2; try discriminate.
  apply beq_nat_true in e.
  rewrite e; auto.
Qed.
#[global]
Hint Resolve Extension_On_Names_Red : Piull.


(**
*)
Lemma Close_Same_Inv_Names :
forall ( x y : Name)(i x0 : nat),
lca_name i x -> lca_name i y ->
Close_Name i x0 x = Close_Name i x0 y -> x = y. 
Proof.
  intros.
  destruct x.
  + simpl in H1.
    DecidSimple x x0.
    - rewrite e in H1.
      destruct y.
      * simpl in H1.
        DecidSimple x1 x0.
        apply beq_nat_true in e.
        apply beq_nat_true in e0.
        rewrite e.
        rewrite e0.
        auto.
        rewrite n in H1.
        inversions H1.
      * simpl in H1.
        inversions H1.
        inversions H0.
        lia.
    - rewrite n in H1.
      destruct y.
      * simpl in H1.
        DecidSimple x1 x0.
        rewrite e in H1.
        inversions H1.
        rewrite n0 in H1.
        inversions H1; auto.
      * simpl in H1.
        inversions H1.
  + simpl in H1.
    destruct y.
    - simpl in H1.
      DecidSimple x x0.
      * rewrite e in H1.
        inversions H1.
        inversions H.
        lia.
      * rewrite n in H1.
        inversions H1.
    - simpl in H1.
      inversion H1.
      auto.
Qed.
#[global]
Hint Resolve Close_Same_Inv_Names : Piull.


(**
*)
Lemma Close_Same_Inv :
forall ( P Q : Process )( x i : nat ),
lca i P -> lca i Q ->
Close_Rec i x P = Close_Rec i x Q -> P = Q.
Proof.
  induction P; intros; try destruct Q; try discriminate; auto.
  + simpl in H1.
    inversions H1.
    try inversions H; try inversions H0.
    apply Close_Same_Inv_Names in H3; Piauto.
    apply Close_Same_Inv_Names in H4; Piauto.
    subst; auto.
  + simpl in H1.
    inversions H1.
    inversions H0.
    inversions H.
    apply IHP1 in H3; auto.
    apply IHP2 in H4; auto.
    subst; auto.
  + simpl in H1.
    inversions H1.
    inversions H.
    inversions H0.
    apply Close_Same_Inv_Names in H3; auto.
    apply Close_Same_Inv_Names in H4; auto.
    apply IHP in H5; auto.
    subst; auto.
  + simpl in H1.
    inversions H1.
    inversion H.
    inversions H0.
    apply Close_Same_Inv_Names in H3; auto.
    subst; auto.
  + simpl in H1.
    inversions H1.
    inversions H.
    inversions H0.
    apply Close_Same_Inv_Names in H3; auto.
    apply IHP in H4; auto.
    subst; auto.
  + simpl in H1.
    inversions H1.
    inversions H; inversions H0.
    specialize (IHP _ _ (S i) H5 H6 H3).
    subst; auto.
  + simpl in H1.
    inversions H1.
    inversions H.
    inversions H0.
    apply Close_Same_Inv_Names in H3; auto.
    specialize (IHP _ _ (S i) H8 H10 H4).
    subst; auto.
  + simpl in H1.
    inversions H1.
    inversions H.
    inversions H0.
    apply Close_Same_Inv_Names in H3; auto.
    specialize (IHP _ _ (S i) H8 H10 H4).
    subst; auto.
Qed.
#[global]
Hint Resolve Close_Same_Inv : Piull.


(**
*)
Lemma No_Typing_Parallel : 
forall (D F G : Context)(P Q : Process),
~( D ;;; F !- (P↓Q) ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H;
    apply (Equality_Subst_Equality _ _ u x0) in x;
    rewrite <- (Double_Subst_Expan_NFVar _ u u x0) in x;
    try rewrite Subst_By_Equal in x;
    try simpl in x;
    eauto with Piull;
    Piauto.
Qed.
#[global]
Hint Resolve No_Typing_Parallel : Piull.


(** FVars_Close_NotIn
*)
Lemma FVars_Reduction :
forall ( P Q : Process )( x : nat),
x ∈ FVars P -> P --> Q -> x ∈ FVars Q.
Proof.
  intros.
  induction H0.
  + apply In_FVars_Res in H.
    destruct H.
    simpl in H.
    destruct H; Piauto.
    
    destruct H; try apply Singleton_inv in H; try lia.
    rewrite H.
    eauto with Piull.
  + apply In_FVars_Res in H.
    destruct H.
    simpl in H.
    destruct H; Piauto.
    destruct H; try apply Singleton_inv in H; try lia.
    rewrite H.
    eauto with Piull.
  + apply In_FVars_Res in H.
    destruct H.
    simpl in H.
    destruct H; Piauto.
    destruct H; try apply Singleton_inv in H; try lia.
    rewrite H.
    eauto with Piull.
  + admit.
  + apply In_FVars_Res in H.
    destruct H.
    simpl in H.
    repeat destruct H; try apply Singleton_inv in H; try lia.
    Piauto.
  + admit.
  + apply In_FVars_Res in H.
    do 3 destruct H.
    - repeat apply FVars_Close_Beq; Piauto.
      OrSearch.
    - repeat apply FVars_Close_Beq; Piauto.
      OrSearch.
    - repeat destruct H.
      * simpl in H.
        DecidSimple u y.
        rewrite n in H.
        apply Singleton_inv in H.
        lia.
      * simpl in H.
        DecidSimple y y.
        rewrite e in H.
        simpl in H.
        inversions H.
    - apply In_FVars_Res in H.
      destruct H.
      repeat apply FVars_Close_Beq; Piauto.
      right.
      repeat apply FVars_Close_Beq; Piauto.
      OrSearch.
  + admit.
Admitted.
#[global]
Hint Resolve FVars_Reduction : Piull.


(**
*)
Lemma No_Typing_Zero : 
forall (D F G : Context),
~( D ;;; F !- θ ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H;
    apply (Equality_Subst_Equality _ _ u x0) in x;
    rewrite <- (Double_Subst_Expan_NFVar _ u u x0) in x;
    try rewrite Subst_By_Equal in x;
    try simpl in x;
    eauto with Piull;
    Piauto.
Qed.
#[global]
Hint Resolve No_Typing_Zero : Piull.


(**
*)
Lemma No_Typing_Output : 
forall (D F G : Context)(P : Process)(x y : Name),
~( D ;;; F !- x « y »· P ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H;
    apply (Equality_Subst_Equality _ _ u x0) in x;
    rewrite <- (Double_Subst_Expan_NFVar _ u u x0) in x;
    try rewrite Subst_By_Equal in x;
    try simpl in x;
    eauto with Piull;
    Piauto.
Qed.
#[global]
Hint Resolve No_Typing_Output : Piull.


(**
*)
Lemma Append_Assigment_Collect :
forall ( u : nat )( A : Proposition )( L : Context ),
Collect L ->  Collect ( Sng (FName u:A) ∪ L ).
Proof.
  intros.
  constructor.
  intros.
  destruct H1.
  + apply Singleton_inv in H0.
    rewrite <- H0.
    Piauto.
  + inversions H.
    Piauto.
Qed.
#[global]
Hint Resolve Append_Assigment_Collect : Piull.


(**
*)
Lemma Lc_Equal_Process :
forall ( P Q : Process ),
P = Q -> lc P -> lc Q.
Proof.
  intros.
  rewrite <- H.
  Piauto.
Qed.
#[global]
Hint Resolve Lc_Equal_Process : Piull.


(**
*)
Lemma Lca_Equal_Process :
forall ( P Q : Process )( i : nat ),
P = Q -> lca i P -> lca i Q.
Proof.
  intros.
  rewrite <- H.
  Piauto.
Qed.
#[global]
Hint Resolve Lca_Equal_Process : Piull.


(**
*)
Lemma App_Nil_Right :
forall ( L : Context ),
L = (ø ∪ L).
Proof.
  intros.
  apply Extensionality_Ensembles.
  constructor.
  + unfold Included.
    intros.
    OrSearch.
  + unfold Included.
    intros.
    destruct H; auto.
    inversions H.
Qed.
#[global]
Hint Resolve App_Nil_Right : Piull.


(**
*)
Lemma Nil_Is_Collect :
Collect ø.
Proof.
  constructor.
  intros.
  inversions H0.
Qed.
#[global]
Hint Resolve Nil_Is_Collect : Piull.


(**
*)
Lemma Weakening_Well_Collected :
forall ( D : Context )( A : Proposition )( P : Process )( u : nat ),
Well_Collected D P -> Well_Collected (Sng (FName u : A) ∪ D) P.
Proof.
  intros.
  constructor.
  intros.
  inversions H.
  specialize (H1 x A0 H0).
  OrSearch.
Qed.
#[global]
Hint Resolve Weakening_Well_Collected : Piull.


(**
*)
Lemma Weakening_Ordinary :
forall ( D F G : Context )( A : Proposition )( P : Process )( u y: nat ),
( D ;;; F !- P ::: G ) ->
( (Sng (FName u : A) ∪ D) ;;; F !- P ::: G ).
Proof.
  intros.
  induction H.
  + constructor; Piauto.
    constructor.
    inversions H1.
    intros.
    specialize (H3 x0 A1 H4).
    destruct H3; try OrSearch.
    destruct H3; OrSearch.
Admitted.
#[global]
Hint Resolve Weakening_Ordinary : Piull.




(**
*)
Lemma No_Typing_Fuse_One_Lf :
forall ( A : Proposition )( x y : nat  )( D F G : Context ),
((FName x : A) ∈ D ) -> ~( D ;;; F !- ([FName x ←→ FName  y]) ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H0.
  + admit.
  + admit.
  + apply (Equality_Subst_Equality _ _ u x0) in x.
    rewrite <- Double_Subst_Expan_NFVar in x; Piauto.
    rewrite Subst_By_Equal in x.
    simpl in x.
    DecidSimple x1 x0.
    - admit.
    - rewrite n in x.
      DecidSimple y x0.
      * rewrite e in x.
        apply (IHInference x1 u); auto.
        right; Piauto.
      * rewrite n0 in x.
        apply (IHInference x1 y); auto.
        right; Piauto.
Admitted.


(**
*)
Lemma No_Typing_Fuse_One_Rg :
forall ( A : Proposition )( x y : nat  )( D F G : Context ),
((FName x : A) ∈ D ) -> ~( D ;;; F !- ([FName y ←→ FName  x]) ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H0.
  + admit.
  + admit.
  + apply (Equality_Subst_Equality _ _ u x0) in x.
    rewrite <- Double_Subst_Expan_NFVar in x; Piauto.
    rewrite Subst_By_Equal in x.
    simpl in x.
    DecidSimple x1 x0.
    - admit.
    - rewrite n in x.
      DecidSimple y x0.
      * rewrite e in x.
        apply (IHInference x1 u); auto.
        right; Piauto.
      * rewrite n0 in x.
        apply (IHInference x1 y); auto.
        right; Piauto.
Admitted.














