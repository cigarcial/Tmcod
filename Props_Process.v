(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the definitions for the processes.
*)
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.


From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Facts_MOpen.
From Tmcod Require Import Facts_Names.


(**
*)
Theorem Process_ProcessAt :
forall ( P : Process ), 
lc P -> lca 0 P.
Proof.
  intros.
  induction H.
  + constructor.
  + constructor.
    - Piauto.
    - Piauto.
  + constructor.
    - Piauto.
    - Piauto.
  + Piauto.
  + Piauto.
  + Piauto.
  + constructor.
    apply Process_Lca_Open_S.
    Piauto.
  + Piauto.
  + Piauto.
Qed.
#[global]
Hint Resolve Process_ProcessAt : Piull.


(**
*)
Theorem ProcessAt_Process :
forall ( P : Process ),
lca 0 P -> lc P.
Proof.
  intros.
  induction P.
  + constructor.
  + inversions H.
    constructor.
    - apply Lca_Zero_Lc_Name.
      auto.
    - apply Lca_Zero_Lc_Name.
      auto.
  + inversions H.
    constructor; Piauto.
  + inversions H.
    constructor; Piauto.
  + inversions H.
    constructor; Piauto.
  + inversions H. 
    constructor; Piauto.
  + try inversions H.
    constructor.
    intros.
    specialize (Lca_Lc_Process_MOpen P 1 [x]) as HB.
    simpl in HB.
    apply HB.
    auto.
    auto.
  + try inversions H;
    try constructor;
    try apply Lca_Zero_Lc_Name;
    try apply IHP1 || apply IHP2;
    try intros;
    try specialize (Lca_Lc_Process_MOpen P 1 [x]) as HB;
    try specialize (Lca_Lc_Process_MOpen P 1 [x0]) as HB;
    Piauto.
  + try inversions H;
    try constructor;
    try apply Lca_Zero_Lc_Name;
    try apply IHP1 || apply IHP2;
    try intros;
    try specialize (Lca_Lc_Process_MOpen P 1 [x]) as HB;
    try specialize (Lca_Lc_Process_MOpen P 1 [x0]) as HB;
    Piauto.
Qed.
#[global]
Hint Resolve ProcessAt_Process : Piull.


(**
*)
Lemma Body_Lc_One :
forall ( P : Process ),
Body P -> lca 1 P.
Proof.
  intros.
  apply Body_Process_Equivalence_Res in H.
  apply Process_ProcessAt in H.
  inversions H.
  auto.
Qed.
#[global]
Hint Resolve Body_Lc_One : Piull.


(**
*)
Lemma Lca_One_Body :
forall ( P : Process ),
lca 1 P -> Body P.
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Lca_One_Body : Piull.


(**
*)
Lemma Lc_Open_Close_Subst :
forall ( P : Process )( x y : nat ), 
lc P -> { 0 ~> y } Close_Rec 0 x P = { y \ x } P.
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Lc_Open_Close_Subst : Piull.


(**
*)
Lemma Open_Lc_Lc :
forall ( P : Process ), lc P -> 
forall ( k x : nat ), lc ( {k ~> x}P ).
Proof.
  intros P H.
  induction H; intros; simpl; 
    try (constructor; intros);
    try rewrite Exchange_Open;
    repeat rewrite Output_LCName_Output;
    Piauto.
Qed.
#[global]
Hint Resolve Open_Lc_Lc : Piull.


(**
*)
Lemma All_Lc_Body :
forall (P : Process),
lc P -> Body P.
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve All_Lc_Body : Piull.


(**
*)
Lemma Close_Lca :
forall ( P : Process )(x k: nat),
lca k P -> lca (S k) (Close_Rec k x P).
Proof.
  intro.
  induction P; intros; simpl; try inversions H; constructor; 
  try apply Lca_Name_Close; auto.
Qed.
#[global]
Hint Resolve Close_Lca : Piull.


(**
*)
Lemma Lc_Close_Body :
forall ( P : Process )(x : nat),
lc P -> Body (Close_Rec 0 x P).
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Lc_Close_Body : Piull.


(**
*)
Lemma Lc_Close_Is_Body :
forall ( P : Process )(x : nat),
lc P -> (forall (y : nat), lc ( (Close_Rec 0 x P) ^ y)).
Proof.
  intros.
  apply (Lc_Close_Body P x) in H.
  inversions H.
  apply H0.
Qed.
#[global]
Hint Resolve Lc_Close_Is_Body : Piull.


(**
*)
Lemma Subst_Body_Body :
forall (P : Process),
Body P -> forall (x y : nat), Body ({y \ x} P).
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Subst_Body_Body : Piull.


(**
*)
Lemma Subst_Lc_Lc :
forall (P : Process)(x y : nat),
lc P -> lc ({y \ x} P).
Proof.
  intros.
  induction H; simpl;
    try specialize ( Subst_Body_Body P) as HP;
    try assert ( HB : Body P ); constructor;
    try specialize ( HP HB x y );
    try inversion HP;
    try constructor; Piauto.
Qed.
#[global]
Hint Resolve Subst_Lc_Lc : Piull.


(**
*)
Lemma Cong_Subst_Cong :
forall (P Q : Process)( x u : nat),
P === Q -> ({u \ x}P) === ({u \ x}Q).
Proof.
  intros.
  induction H; try simpl; Piauto.
Qed.
#[global]
Hint Resolve Cong_Subst_Cong : Piull.


(**
*)
Theorem Congruence_WD :
forall P Q : Process,
(P === Q) -> lc(P)  -> lc(Q).
Proof.
  intros.
  induction H; inversions H0; Piauto.
  + inversions H2; Piauto.
  + constructor. simpl.
    constructor.
    apply Open_Lc_Lc; auto.
    inversions H4.
    apply H2; auto.
Qed.
#[global]
Hint Resolve Congruence_WD : Piull.


Ltac PR_WD :=
  try rewrite Lc_Open_Close_Subst;
    try apply Subst_Lc_Lc;
    try intros;
    try rewrite Lc_Open_Close_Subst;
    try apply Subst_Lc_Lc;
    repeat constructor; Piauto.

(**
*)
Theorem ProcessReduction_WD : 
forall P Q : Process, 
(P --> Q) -> lc(P) -> lc(Q).
Proof.
  intros.
  induction H; try constructor; intros; 
  try PR_WD; eauto with Piull.
Qed.
#[global]
Hint Resolve ProcessReduction_WD : Piull.





