(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the definitions for the processes.
*)
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.

From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Facts_Names.
From Tmcod Require Import Facts_Process.


(**
*)
Lemma List_Sk_char :
forall (k : nat)(L : list nat),
(length L) = S k -> 
(exists (x : nat)(L0 : list nat), L = x :: L0 /\ (length L0) = k).
Proof.
  intros.
  destruct L.
  + simpl in H.
    lia.
  + exists n.
    exists L.
    auto.
Qed.
#[global]
Hint Resolve List_Sk_char : Piull.


(**
*)
Ltac ListEasyInduction k L H HL IHk:=
  induction k; intros;
  try rewrite length_zero_iff_nil in H;
    try rewrite H;
   try specialize (List_Sk_char k L H) as HL;
    try destruct HL as [x0 [ L0 [HL HT]]];
    try rewrite HL;
    try simpl;
    try rewrite IHk; Piauto.


(**
*)
Lemma MOpen_Name_FName :
forall (k x : nat)( L : list nat), 
(length L) = k -> 
MOpen_Name_Rec k L (FName x) = FName x.
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Name_FName : Piull.


(**
*)
Lemma MOpen_Name_BName_Gt :
forall (k i : nat)(L : list nat),
(length L) = k -> k <= i -> 
MOpen_Name_Rec k L (BName i) = (BName i).
Proof.
  intro.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; try lia.
    rewrite Open_Name_BName_Gt; auto.
Qed.
#[global]
Hint Resolve MOpen_Name_BName_Gt : Piull.


(**
*)
Lemma MOpen_Name_Result : 
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> lca_name k x -> 
exists (x0 : nat), ( MOpen_Name_Rec k L x) = FName x0.
Proof.
  induction k; intros.
  + apply Lca_Zero_Lc_Name in H0.
    apply length_zero_iff_nil in H.
    rewrite H.
    simpl.
    inversions H0.
    exists x0.
    auto.
  + inversions H0.
    - rewrite MOpen_Name_FName;
       try exists x0; auto.
    - specialize (List_Sk_char k L H) as HL.
      destruct HL as [x [ L0 [HL HT]]].
      rewrite HL.
      simpl.
      assert (HA : k = i \/ i < k). { lia. }
      destruct HA.
      * assert ( HB: k <= i ). { lia. }
        rewrite MOpen_Name_BName_Gt; auto.
        rewrite Open_Name_BName_Eq; auto.
        exists x; auto.
      * assert (Hk : lca_name k ((BName i)) ).
        constructor; auto.
        specialize (IHk L0 (BName i) HT Hk).
        destruct IHk.
        rewrite H3.
        simpl.
        exists x0.
        auto.
Qed.
#[global]
Hint Resolve MOpen_Name_Result : Piull.


(**
*)
Lemma MOpen_Name_Rec_lc :
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> lca_name k x -> 
lc_name ( MOpen_Name_Rec k L x).
Proof.
  intros.
  specialize (MOpen_Name_Result k L x H H0) as HA.
  destruct HA as [x0 HA].
  rewrite HA.
  constructor.
Qed.
#[global]
Hint Resolve MOpen_Name_Rec_lc : Piull.


(**
*)
Lemma M2Open_MOpen :
forall (k x : nat)(L : list nat)(P : Process),
(length L) = k -> 
({0 ~> x} M2Open_Rec k L P) = MOpen_Rec (S k) (L ++ (x :: nil)) P.
Proof.
  induction k.
  + intros. 
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite <- IHk; auto.
    rewrite Exchange_Open; auto.
Qed.
#[global]
Hint Resolve M2Open_MOpen : Piull.


(**
*)
Lemma MOpen_Pzero : 
forall (k : nat)(L : list nat),
(length L) = k -> MOpen_Rec k L (θ) = θ.
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Pzero : Piull.


(**
*)
Lemma MOpen_Fuse :
forall (k : nat)(L : list nat)(x y : Name),
(length L) = k -> 
MOpen_Rec k L ([x ←→ y]) = [(MOpen_Name_Rec k L x) ←→ (MOpen_Name_Rec k L y)].
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Fuse : Piull.


(**
*)
Lemma MOpen_Parallel : 
forall (k : nat)(L : list nat)( P Q : Process),
(length L) = k ->
MOpen_Rec k L (P ↓ Q) = (MOpen_Rec k L P) ↓ (MOpen_Rec k L Q).
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Parallel : Piull.


(**
*)
Lemma MOpen_Chan_output :
forall (k : nat)(L : list nat)( x y : Name)(P : Process),
(length L) = k -> 
MOpen_Rec k L (x « y »· P) = (MOpen_Name_Rec k L x) « (MOpen_Name_Rec k L y) »· (MOpen_Rec k L P).
Proof.
  ListEasyInduction k L H HL IHk.
Qed. 
#[global]
Hint Resolve MOpen_Chan_output : Piull.


(**
*)
Lemma MOpen_Chan_zero :
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> 
MOpen_Rec k L (x ·θ) = (MOpen_Name_Rec k L x) ·θ.
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Chan_zero : Piull.


(**
*)
Lemma MOpen_Chan_close :
forall (k : nat)(L : list nat)(x : Name)(P : Process),
(length L) = k -> 
MOpen_Rec k L (x ()·P) = (MOpen_Name_Rec k L x) ()·(MOpen_Rec k L P).
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Chan_close : Piull.


(**
*)
Lemma MOpen_Chan_res :
forall (k : nat)(L : list nat)(P : Process), 
(length L) = k -> 
MOpen_Rec k L (ν P) = (ν M2Open_Rec k L P).
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Chan_res : Piull.


(**
*)
Lemma MOpen_Chan_input : 
forall (k : nat)(L : list nat)(x : Name)(P : Process),
(length L) = k -> 
MOpen_Rec k L (x · P) = (MOpen_Name_Rec k L x) · (M2Open_Rec k L P).
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Chan_input : Piull.


(**
*)
Lemma MOpen_Chan_replicate : 
forall (k : nat)(L : list nat)(x : Name)(P : Process),
(length L) = k -> 
MOpen_Rec k L (x !· P) = (MOpen_Name_Rec k L x) !· (M2Open_Rec k L P).
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Chan_replicate : Piull.


(**
*)
Theorem Lca_Lc_Process_MOpen : 
forall (P : Process)(k : nat)(L : list nat),
(length L) = k -> 
lca k P -> lc (MOpen_Rec k L P).
Proof.
  induction P; intros; inversions H0.
  + rewrite MOpen_Pzero; constructor.
  + rewrite MOpen_Fuse; auto.
    constructor; 
    apply MOpen_Name_Rec_lc; auto.
  + rewrite MOpen_Parallel; constructor; auto.
  + rewrite MOpen_Chan_output; auto.
    constructor; 
    try apply MOpen_Name_Rec_lc; auto.
  + rewrite MOpen_Chan_zero; auto.
    constructor; 
    try apply MOpen_Name_Rec_lc; auto.
  + rewrite MOpen_Chan_close; auto.
    constructor;
    try apply MOpen_Name_Rec_lc; auto.
  + rewrite MOpen_Chan_res; auto.
    constructor.
    intros.
    rewrite M2Open_MOpen; auto.
    apply IHP; auto.
    rewrite app_length; simpl; lia.
  + rewrite MOpen_Chan_input; auto.
    inversions H0.
    constructor;
    try apply MOpen_Name_Rec_lc; auto.
    intros.
    rewrite M2Open_MOpen; auto.
    apply IHP; auto.
    rewrite app_length; simpl; lia.
  + rewrite MOpen_Chan_replicate; auto.
    inversions H0.
    constructor;
    try apply MOpen_Name_Rec_lc; auto.
    intros.
    rewrite M2Open_MOpen; auto.
    apply IHP; auto.
    rewrite app_length; simpl; lia.
Qed.
#[global]
Hint Resolve Lca_Lc_Process_MOpen : Piull.


(**
*)
Lemma MOpen_Chan_zero_FName_NoMOpenName :
forall (k x : nat)( L : list nat), 
(length L) = k -> 
MOpen_Rec k L (FName x ·θ) = FName x ·θ.
Proof.
  ListEasyInduction k L H HL IHk.
Qed.
#[global]
Hint Resolve MOpen_Chan_zero_FName_NoMOpenName : Piull.


(*
Lemma MOpen_Chan_zero_BName_Eq_NoMOpenName :
forall (k i : nat)(L : list nat),
(length L) = k -> k <= i -> 
MOpen_Rec k L (BName i ·θ) = (BName i ·θ).
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
    simpl.
    admit.
    lia.
Admitted.


(*
*)
Lemma MOpen_Chan_zero_NoMOpenName :
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> lca k (x·θ) -> 
exists (y : nat), MOpen_Rec k L (x ·θ) = (FName y)·θ.
Proof.
  induction k.
  + intros.
    inversions H0.
    apply Lca_Zero_Lc_Name in H3.
    inversions H3.
    exists x0.
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    inversions H0.
    inversions H3.
    - exists x0.
      rewrite MOpen_Chan_zero_FName_NoMOpenName; auto.
    - specialize (List_Sk_char k L H) as HL.
      destruct HL as [x [ L0 [HL HT]]].
      rewrite HL.
      simpl.
      assert (HA : k = i \/ i < k). { lia. }
      destruct HA.
      * assert ( HB: k <= i ). { lia. }
        specialize (MOpen_Chan_zero_BName_Eq k i L0 HT HB) as HC.
        rewrite HC.
        simpl.
        admit.
      * assert (Hk : lca k ((BName i) ·θ) ).
        constructor; constructor; auto.
        specialize (IHk L0 (BName i) HT Hk).
        destruct IHk.
        rewrite H4; 
        simpl.
        exists x0.
        auto.
Admitted.

 *)