(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the tactis and Hint Db for the proofs.
*)
Require Import Coq.Program.Equality.

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Sets.Constructive_sets.

From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Typing.
From Tmcod Require Import Facts_Names.
From Tmcod Require Import Facts_FVars.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Props_Process.


(**
*)
Lemma Well_Subst_Chan_Output :
forall (P : Process)(x0 y : Name)( u x : nat),
Well_Subst (x0 « y »· P) u x -> Well_Subst (P) u x.
Proof.
  intros.
  constructor.
  inversions H.
  unfold not.
  intros.
  apply H0.
  simpl.
  OrSearch.
  inversions H; auto.
Qed.
#[global]
Hint Resolve Well_Subst_Chan_Output : Piull.


(**
*)
Lemma Well_Subst_Chan_Close :
forall (P : Process)(x0 : Name)( u x : nat),
Well_Subst (x0 ()·P) u x -> Well_Subst P u x.
Proof.
  constructor.
  unfold not.
  intros.
  inversions H.
  apply H1.
  simpl.
  OrSearch.
  inversions H; auto.
Qed.
#[global]
Hint Resolve Well_Subst_Chan_Close : Piull.


(**
*)
Lemma Well_Subst_Chan_Res :
forall ( P : Process )( u x : nat),
Well_Subst (ν P) u x -> Well_Subst P u x.
Proof.
  constructor.
  unfold not.
  intros.
  inversions H.
  apply H1.
  Piauto.
  inversions H; auto.
Qed.
#[global]
Hint Resolve Well_Subst_Chan_Res : Piull.

Ltac Aux_Ltac_1 H H1 :=
  inversions H;
  apply In_FVars_Name_Subst in H1;
  destruct H1;
  (rewrite H1;
  simpl;
  OrSearch) + (contradiction).


(**
*)
Lemma Lc_WSubst_Subst_WSubst :
forall (P : Process)( u x : nat),
lc P -> Well_Subst P u x -> 
Well_Subst ({x \ u} P) x u.
Proof.
  intros.
  constructor; auto.
  unfold not.
  intro.
  induction H.
  + simpl in H1.
    contradiction.
  + inversions H0.
    simpl in H3.
    simpl in H1.
    apply Union_inv in H1.
    apply H3.
    destruct H1.
    - Aux_Ltac_1 H H1.
    - Aux_Ltac_1 H2 H1.
  + inversions H0.
    apply No_FVars_Parallel in H3.
    destruct H3 as [HA HB].
    simpl in H1.
    inversions H1; Piauto.
  + simpl in H1.
    inversions H0.
    apply H4.
    simpl.
    apply Union_inv in H1.
    destruct H1.
    - apply Union_inv in H1.
      destruct H1.
      * Aux_Ltac_1 H H1.
      * Aux_Ltac_1 H2 H1.
    - apply Well_Subst_Chan_Output in H0.
      specialize (IHlc H0 H1).
      contradiction.
  + inversions H0.
    apply H2.
    simpl in *.
    Aux_Ltac_1 H H1.
  + inversions H0.
    apply H3.
    simpl in *.
    apply Union_inv in H1.
    destruct H1.
    - Aux_Ltac_1 H H1.
    - apply Well_Subst_Chan_Close in H0.
      specialize (IHlc H0 H1).
      contradiction.
  + simpl in H1.
    inversions H0.
    apply (After_Subst_No_FVar P u x); auto.
  + inversions H0.
    apply H4.
    simpl in *.
    apply Union_inv in H1.
    destruct H1.
    - Aux_Ltac_1 H H1.
    - apply (After_Subst_No_FVar P u x) in H1; auto.
      contradiction.
  + inversions H0.
    apply H4.
    simpl in *.
    apply Union_inv in H1.
    destruct H1.
    - Aux_Ltac_1 H H1.
    - apply (After_Subst_No_FVar P u x) in H1; auto.
      contradiction.
  + inversions H0.
    auto.
Qed.
#[global]
Hint Resolve Lc_WSubst_Subst_WSubst : Piull.


(** FVars_Subst
*)
Lemma Beq_NFVars_Subst :
forall ( Q : Process )( u x0 x: nat ),
u <> x0 -> ~ x0 ∈ FVars Q -> 
~ x0 ∈ FVars ({u \ x} Q).
Proof.
  intros.
  unfold not.
  intros.
  apply FVars_Subst in H1.
  destruct H1.
  Piauto.
  contradiction.
Qed.
#[global]
Hint Resolve Beq_NFVars_Subst : Piull.


(**
*)
Lemma Beq_FVars_Subst : 
forall ( P : Process )( x0 x u : nat ),
x0 <> x -> x0 ∈ FVars P ->
x0 ∈ FVars ({u \ x} P).
Proof.
  induction P; intros.
  + Piauto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - destruct x; try inversions H0.
      simpl.
      DecidSimple x0 x1.
      rewrite n.
      OrSearch.
    - destruct y; try inversions H0.
      simpl.
      DecidSimple x0 x1.
      rewrite n.
      OrSearch.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0; OrSearch.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0; try OrSearch.
    apply Union_inv in H0.
    destruct H0.
    - destruct x; try inversions H0.
      simpl.
      DecidSimple x0 x1.
      rewrite n.
      OrSearch.
    - destruct y; try inversions H0.
      simpl.
      DecidSimple x0 x1.
      rewrite n.
      OrSearch.
  + simpl in H0.
    destruct x; try inversions H0.
    simpl.
    DecidSimple x0 x1.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0; try OrSearch.
    destruct x; try inversions H0.
    simpl.
    DecidSimple x0 x1.
    rewrite n.
    OrSearch.
  + simpl in *.
    apply IHP; Piauto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0; try OrSearch.
    destruct x; try inversions H0.
    simpl.
    DecidSimple x0 x1.
    rewrite n.
    OrSearch.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0; try OrSearch.
    destruct x; try inversions H0.
    simpl.
    DecidSimple x0 x1.
    rewrite n.
    OrSearch.
Qed.
#[global]
Hint Resolve Beq_FVars_Subst : Piull.


(**
*)
Lemma In_FVars_Subst : 
forall ( P : Process )( x u : nat ),
x ∈ FVars P -> u ∈ FVars ({u \ x} P).
Proof.
  intro.
  induction P; intros.
  + inversions H.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - destruct x; inversions H.
      simpl.
      DecidSimple x0 x0.
      OrSearchCons.
    - destruct y; inversions H.
      simpl.
      DecidSimple x0 x0.
      OrSearchCons.
  + simpl in H.
    destruct H;
    OrSearch.
  + simpl in H.
    destruct H; try OrSearch.
    destruct H.
    - destruct x; inversions H.
      simpl.
      DecidSimple x0 x0.
      OrSearchCons.
    - destruct y; inversions H.
      simpl.
      DecidSimple x0 x0.
      OrSearchCons.
  + simpl in H.
    destruct x; inversions H.
    simpl.
    DecidSimple x0 x0.
    OrSearchCons.
  + simpl in H.
    destruct H; try OrSearch.
    destruct x; inversions H.
    simpl.
    DecidSimple x0 x0.
    OrSearchCons.
  + simpl in *.
    OrSearch.
  + simpl in H.
    destruct H; try OrSearch.
    destruct x; inversions H.
    simpl.
    DecidSimple x0 x0.
    OrSearchCons.
  + simpl in H.
    destruct H; try OrSearch.
    destruct x; inversions H.
    simpl.
    DecidSimple x0 x0.
    OrSearchCons.
Qed.
#[global]
Hint Resolve In_FVars_Subst : Piull.


(** Subst_Close_Dif_Name
*)
Lemma Subst_Reduction_NBeq :
forall ( P Q : Process)(x u : nat),
lc P -> u <> x ->
( P --> Q ) -> ( ({u \ x}P) --> ({u \ x} Q) ).
Proof.
  intros.
  induction H1.
  + specialize (IsClosing_inv P x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} ([FName x0 ←→ FName y])).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    - apply beq_nat_true in e.
      rewrite e.
      rewrite Double_Subst_By_Same_Name.
      constructor; eauto with Piull.
    - rewrite n0.
      apply beq_nat_false in n0.
      rewrite Double_Subst_All_Dif; Piauto.
      constructor; eauto with Piull.
  + specialize (IsClosing_inv P x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} ([FName y ←→ FName x0])).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    - apply beq_nat_true in e.
      rewrite e.
      rewrite Double_Subst_By_Same_Name.
      constructor; eauto with Piull.
    - rewrite n0.
      apply beq_nat_false in n0.
      rewrite Double_Subst_All_Dif; Piauto.
      constructor; eauto with Piull.
  + specialize (IsClosing_inv P x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} ([FName y ←→ FName x0])).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    - apply beq_nat_true in e.
      rewrite e.
      rewrite Double_Subst_By_Same_Name.
      constructor; eauto with Piull.
    - rewrite n0.
      apply beq_nat_false in n0.
      rewrite Double_Subst_All_Dif; Piauto.
      constructor; eauto with Piull.
  + specialize (IsClosing_inv P x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} ([FName x0 ←→ FName y])).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    - apply beq_nat_true in e.
      rewrite e.
      rewrite Double_Subst_By_Same_Name.
      constructor; eauto with Piull.
    - rewrite n0.
      apply beq_nat_false in n0.
      rewrite Double_Subst_All_Dif; Piauto.
      constructor; eauto with Piull.
  + specialize (IsClosing_inv Q x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} (FName x0 ·θ) ).
    simpl ({u \ x} (FName x0 ()·Q) ).
    DecidSimple x0 x.
    rewrite n.
    constructor; eauto with Piull.
  + specialize (IsClosing_inv Q x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} (FName x0 ·θ) ).
    simpl ({u \ x} (FName x0 ()·Q) ).
    DecidSimple x0 x.
    rewrite n.
    constructor; eauto with Piull.
  + specialize (IsClosing_inv P u0 u x H6) as Hx.
    destruct Hx.
    specialize (IsClosing_inv P y u x H7) as Hx.
    destruct Hx.
    do 2 rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 rewrite Subst_Parallel.
    do 2 rewrite Subst_Res.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 simpl ({u \ x} (FName u0 !· P)).
    simpl ({u \ x} (FName u0 « FName y »· Q)).
    DecidSimple u0 x.
    rewrite n.
    DecidSimple y x.
    rewrite n0.
    rewrite Subst_Parallel.
    rewrite <- Subst_Open_NEq_Exchange; Piauto.
    constructor; eauto with Piull.
  + specialize (IsClosing_inv P u0 u x H6) as Hx.
    destruct Hx.
    specialize (IsClosing_inv P y u x H7) as Hx.
    destruct Hx.
    do 2 rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 rewrite Subst_Parallel.
    do 2 rewrite Subst_Res.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 simpl ({u \ x} (FName u0 !· P)).
    simpl ({u \ x} (FName u0 « FName y »· Q)).
    DecidSimple u0 x.
    rewrite n.
    DecidSimple y x.
    rewrite n0.
    rewrite Subst_Parallel.
    rewrite <- Subst_Open_NEq_Exchange; Piauto.
    constructor; eauto with Piull.
  + specialize (IsClosing_inv P x0 u x H8) as Hx.
    destruct Hx.
    specialize (IsClosing_inv P y u x H9) as Hx.
    destruct Hx.
    do 2 rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 rewrite Subst_Parallel.
    do 2 rewrite Subst_Res.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 simpl ({u \ x} (FName x0 · P)).
    simpl ({u \ x} (FName x0 « FName y »· (Q ↓ R))).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    rewrite n0.
    rewrite Subst_Parallel.
    rewrite <- Subst_Open_NEq_Exchange; Piauto.
    constructor; eauto with Piull.
  + specialize (IsClosing_inv P x0 u x H7) as Hx.
    destruct Hx.
    specialize (IsClosing_inv P y u x H8) as Hx.
    destruct Hx.
    do 2 rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 rewrite Subst_Parallel.
    do 2 rewrite Subst_Res.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 simpl ({u \ x} (FName x0 · P)).
    simpl ({u \ x} (FName x0 « FName y »· (Q ↓ R))).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    rewrite n0.
    rewrite Subst_Parallel.
    rewrite <- Subst_Open_NEq_Exchange; Piauto.
    constructor; eauto with Piull.
Qed.
#[global]
Hint Resolve Subst_Reduction_NBeq : Piull.







