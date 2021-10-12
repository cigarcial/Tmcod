(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021

  This file contains the basic facts concerning names.
*)
From Coq Require Import Ensembles.
From Coq Require Import Finite_sets.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.

From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Facts_Names.


(**
*)
Lemma No_Union_No_Each : 
forall (x : nat)( X Y : FVarsE ),
~(x ∈ (X ∪ Y)) -> ~(x ∈ X) /\ ~(x ∈ Y).
Proof.
Admitted.
#[global]
Hint Resolve No_Union_No_Each : Piull.


(**
*)
Lemma There_Is_A_Name :
forall ( P : Process ),
exists ( x : nat ), ~ ( x ∈ (FVars P) ).
Proof.
Admitted.
#[global]
Hint Resolve There_Is_A_Name : Piull.


(**
*)
Lemma FVar_Process_Is_Or_Not :
forall (P : Process)( x : nat),
(x ∈ FVars P) \/ (~ x ∈ FVars P).
Admitted.
#[global]
Hint Resolve FVar_Process_Is_Or_Not : Piull.


(**
*)
Lemma FVars_Name_Finite :
forall (x : Name),
Finite _ (FVars_Name x).
Proof.
  destruct x.
  + simpl. apply Singleton_is_finite.
  + simpl. constructor.
Qed.
#[global]
Hint Resolve FVars_Name_Finite : Piull.


(**
*)
Lemma FVars_Finite :
forall (P : Process),
Finite _ (FVars P).
Proof.
  induction P;
  repeat apply Union_preserves_Finite;
  repeat apply FVars_Name_Finite; 
  Piauto.
  constructor.
Qed.
#[global]
Hint Resolve FVars_Finite : Piull.


(**
*)
Lemma FVars_Name_No_Close :
forall (z k : nat)(x : Name),
~ (z ∈ FVars_Name x) -> (Close_Name k z x = x).
Proof.
  unfold not.
  intros.
  destruct x; Piauto.
  simpl.
  DecidSimple x z.
  apply beq_nat_true in e.
  rewrite e in H.
  assert ( HB : z ∈ Singleton nat z); try constructor.
  contradiction.
Qed.
#[global]
Hint Resolve FVars_Name_No_Close : Piull.


(**
*)
Lemma FVars_Bex_Name :
forall ( x : Name)(i j : nat),
FVars_Name (Bex_Name i j x) = FVars_Name x.
Proof.
  destruct x; Piauto.
  intros; simpl.
  DecidSimple i i0.
  rewrite n.
  DecidSimple i j.
Qed.
#[global]
Hint Resolve FVars_Bex_Name : Piull.


(**
*)
Lemma FVars_Bex_Process:
forall (P : Process)(i j : nat),
FVars P = FVars ({i <~> j} P).
Proof.
  InductionProcessRev P FVars_Bex_Name.
Qed.
#[global]
Hint Resolve FVars_Bex_Process : Piull.


(**
*)
Lemma Close_NoFVar_Eq :
forall ( P : Process )(z k: nat),
~ ( z ∈ (FVars P) ) -> ( Close_Rec k z P ) = P.
Proof.
  induction P; intros; 
    try simpl in *;
    repeat (apply No_Union_No_Each in H; destruct H as [H ?HA]);
    repeat (rewrite IHP || rewrite IHP1 || rewrite IHP2);
    repeat rewrite FVars_Name_No_Close;
    Piauto.
Qed.
#[global]
Hint Resolve Close_NoFVar_Eq : Piull.


(**
*)
Lemma Cong_FVars :
forall (P Q : Process), 
P === Q -> FVars P = FVars Q.
Proof.
  intros.
  induction H; simpl; Piauto;
  try apply Extensionality_Ensembles;
  try constructor;
  try unfold Included;
  try intros;
  repeat (apply Union_inv in H; destruct H); 
  try inversions H0;
  try rewrite IHCongruence in H1 || rewrite <- IHCongruence in H1;
  try OrSearch.
Admitted.
#[global]
Hint Resolve Cong_FVars : Piull.


(**
*)
Lemma No_FVars_Parallel :
forall (P Q : Process)( u : nat),
( ~(u ∈ FVars (P ↓ Q))) -> (~ u ∈ FVars P) /\ (~ u ∈ FVars Q).
Proof.
  unfold not.
  intros.
  constructor; 
  (intros; assert ( HA : u ∈ FVars (P ↓ Q)); OrSearch).
Qed.
#[global]
Hint Resolve No_FVars_Parallel : Piull.


(**
*)
Lemma In_FVars_Name_Subst :
forall (u x x1 : nat),
u ∈ FVars_Name (Subst_Name u x (FName x1)) -> 
x = x1 \/ u <> u.
Proof.
  intros.
  simpl in H.
  destruct (bool_dec (x1 =? u) true).
  * rewrite e in H.
    simpl in H.
    apply Singleton_inv in H.
    apply beq_nat_true in e.
    rewrite e.
    OrSearch.
  * apply not_true_iff_false in n.
    rewrite n in H.
    simpl in H.
    apply Singleton_inv in H.
    rewrite H in n.
    apply beq_nat_false in n.
    contradiction.
Qed.
#[global]
Hint Resolve In_FVars_Name_Subst : Piull.


Require Import Coq.Program.Equality.


(**
*)
Lemma After_Subst_No_FVar :
forall (P : Process)(u x : nat),
u <> x -> 
~ u ∈ FVars ({x \ u} P).
Proof.
  unfold not.
  intro.
  dependent induction P; 
  intros; try simpl in H0;
  try apply Union_inv in H0.
  + inversions H0.
  + destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (Subst_Name_Gen_Output u x0 y); auto.
  + destruct H0.
    - apply (IHP1 u x); auto.
    - apply (IHP2 u x); auto.
  + destruct H0.
    apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (Subst_Name_Gen_Output u x0 y); auto.
    - apply (IHP u x0); auto.
  + apply (Subst_Name_Gen_Output u x0 x); auto.
  + destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (IHP u x0); auto.
  + apply (IHP u x); auto.
  + destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (IHP u x0); auto.
  + destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (IHP u x0); auto.
Qed.
#[global]
Hint Resolve After_Subst_No_FVar : Piull.


(**
*)
Lemma FVars_Close_Beq_Names :
forall(x : Name)(u x0 i : nat),
u <> x0 -> u ∈ FVars_Name x -> 
Close_Name i x0 x = FName u.
Proof.
  intros.
  destruct x; simpl in H0; try contradiction; auto.
  apply Singleton_inv in H0.
  simpl.
  DecidSimple x x0.
Qed.
#[global]
Hint Resolve FVars_Close_Beq_Names : Piull.


(**
*)
Lemma FVars_Close_Beq :
forall ( P : Process ) (u x i : nat),
u <> x -> u ∈ FVars P -> u ∈ FVars (Close_Rec i x P).
Proof.
  induction P; intros; 
  try simpl in H0; try apply Union_inv in H0; Piauto.
  + destruct H0.
    - OrSearchRew (FVars_Close_Beq_Names x u x0 i).
    - OrSearchRew (FVars_Close_Beq_Names y u x0 i).
  + destruct H0.
    - OrSearchApp (IHP1).
    - OrSearchApp (IHP2).
  + destruct H0.
    - apply Union_inv in H0.
      destruct H0.
      * OrSearchRew (FVars_Close_Beq_Names x u x0 i).
      * OrSearchRew (FVars_Close_Beq_Names y u x0 i).
    - OrSearchApp (IHP).
  + simpl.
    OrSearchRew (FVars_Close_Beq_Names x u x0 i).
  + destruct H0.
    - OrSearchRew (FVars_Close_Beq_Names x u x0 i).
    - OrSearchApp (IHP).
  + simpl; apply IHP; auto.
  + destruct H0.
    - OrSearchRew (FVars_Close_Beq_Names x u x0 i).
    - OrSearchApp (IHP).
  + destruct H0.
    - OrSearchRew (FVars_Close_Beq_Names x u x0 i).
    - OrSearchApp (IHP).
Qed.
#[global]
Hint Resolve FVars_Close_Beq : Piull.


(**
*)
Lemma FVars_Open_Beq_Names :
forall (x : Name)(u x0 i: nat),
u ∈ FVars_Name x -> FVars_Name (Open_Name i x0 x) = Singleton nat u.
Proof.
  intros.
  destruct x; simpl in H; try contradiction.
  apply Singleton_inv in H.
  rewrite H.
  auto.
Qed.
#[global]
Hint Resolve FVars_Open_Beq_Names : Piull.


(**
*)
Lemma FVars_Open_Beq_Names_Inv :
forall (x : Name)(u x0 i: nat),
u <> x0 -> u ∈ FVars_Name (Open_Name i x0 x) ->
FVars_Name x = Singleton nat u.
Proof.
  intros.
  destruct x.
  + simpl in H0.
    apply Singleton_inv in H0.
    simpl.
    auto.
  + simpl in H0.
    destruct (bool_dec (i =? i0) true).
    - rewrite e in H0.
      simpl in H0.
      apply Singleton_inv in H0.
      rewrite H0 in H.
      contradiction.
    - apply not_true_iff_false in n.
      rewrite n in H0.
      simpl in H0.
      contradiction.
Qed.
#[global]
Hint Resolve FVars_Open_Beq_Names_Inv : Piull.


(**
*)
Lemma FVars_Open_Beq :
forall ( P : Process)(u x i: nat),
u <> x -> ( u ∈ FVars P <-> u ∈ FVars ({i ~> x}P)).
Proof.
  intro.
  induction P; intros; simpl; try constructor; try intros; try contradiction.
  + apply Union_inv in H0.
    destruct H0.
    - OrSearchRew (FVars_Open_Beq_Names x u x0 i).
    - OrSearchRew (FVars_Open_Beq_Names y u x0 i).
  + apply Union_inv in H0.
    destruct H0.
    - OrSearchRew (FVars_Open_Beq_Names_Inv x u x0 i).
    - OrSearchRew (FVars_Open_Beq_Names_Inv y u x0 i).
  + apply Union_inv in H0.
    destruct H0.
    - OrSearchApp (IHP1).
    - OrSearchApp (IHP2).
  + apply Union_inv in H0.
    destruct H0.
    - left.
      apply <- (IHP1 u x i); auto.
    - right.
      apply <- (IHP2 u x i); auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply Union_inv in H0.
      destruct H0.
      * OrSearchRew (FVars_Open_Beq_Names x u x0 i).
      * OrSearchRew (FVars_Open_Beq_Names y u x0 i).
    - OrSearchApp (IHP).
  + apply Union_inv in H0.
    destruct H0.
    - apply Union_inv in H0.
      destruct H0.
      * OrSearchRew (FVars_Open_Beq_Names_Inv x u x0 i).
      * OrSearchRew (FVars_Open_Beq_Names_Inv y u x0 i).
    - right.
      apply <- (IHP u x0 i); auto.
  + OrSearchRew (FVars_Open_Beq_Names x u x0 i).
  + OrSearchRew (FVars_Open_Beq_Names_Inv x u x0 i).
  + apply Union_inv in H0.
    destruct H0.
    - OrSearchRew (FVars_Open_Beq_Names x u x0 i).
    - OrSearchApp (IHP).
  + apply Union_inv in H0.
    destruct H0.
    - OrSearchRew (FVars_Open_Beq_Names_Inv x u x0 i).
    - right; apply <- (IHP u x0 i); auto.
  + apply IHP; auto.
  + apply <- (IHP u x (S i)); auto.
  + apply Union_inv in H0.
    destruct H0.
    - OrSearchRew (FVars_Open_Beq_Names x u x0 i).
    - OrSearchApp (IHP).
  + apply Union_inv in H0.
    destruct H0.
    - OrSearchRew (FVars_Open_Beq_Names_Inv x u x0 i).
    - right; apply <- (IHP u x0 (S i)); auto.
  + apply Union_inv in H0.
    destruct H0.
    - OrSearchRew (FVars_Open_Beq_Names x u x0 i).
    - OrSearchApp (IHP).
  + apply Union_inv in H0.
    destruct H0.
    - OrSearchRew (FVars_Open_Beq_Names_Inv x u x0 i).
    - right; apply <- (IHP u x0 (S i)); auto.
Qed.
#[global]
Hint Resolve FVars_Open_Beq : Piull.


(**
*)
Lemma FVars_Open :
forall (Q : Process)( y x i : nat),
x ∈ FVars ( {i ~> y} Q ) ->  x = y \/ x ∈ FVars ( Q ).
Proof.
  induction Q; 
  intros;
  try simpl in *; try apply Union_inv in H; Piauto.
  + destruct H.
    - destruct x; simpl in *.
      * apply Singleton_inv in H.
        OrSearchRew H.
      * FVars_Open_Lt H i i0.
    - destruct y; simpl in *.
      * apply Singleton_inv in H.
        OrSearchRew H.
      * FVars_Open_Lt H i i0.
  + destruct H.
    - apply IHQ1 in H.
      destruct H; auto.
      OrSearch.
    - apply IHQ2 in H.
      destruct H; auto.
      OrSearch.
  + destruct H.
    - apply Union_inv in H.
      destruct H.
      * destruct x; simpl in *.
        ** apply Singleton_inv in H.
          rewrite H.
          OrSearch.
        ** FVars_Open_Lt H i i0.
      * destruct y; simpl in *.
        ** apply Singleton_inv in H.
          rewrite H.
          OrSearch.
        ** FVars_Open_Lt H i i0.
    - apply IHQ in H.
      destruct H; auto.
      OrSearch.
  + destruct x; simpl in *.
    - apply Singleton_inv in H.
      rewrite H.
      OrSearch.
    - FVars_Open_Lt H i i0.
  + destruct H.
    - destruct x; simpl in *.
      * apply Singleton_inv in H.
        rewrite H.
        OrSearch.
      * FVars_Open_Lt H i i0.
    - apply IHQ in H.
      destruct H; auto.
      OrSearch.
  + apply (IHQ _ _ (S i)); auto.
  + destruct H.
    - destruct x; simpl in *.
      * apply Singleton_inv in H.
        rewrite H.
        OrSearch.
      * FVars_Open_Lt H i i0.
    - apply IHQ in H.
      destruct H; auto.
      OrSearch.
  + destruct H.
    - destruct x; simpl in *.
      * apply Singleton_inv in H.
        rewrite H.
        OrSearch.
      * FVars_Open_Lt H i i0.
    - apply IHQ in H.
      destruct H; auto.
      OrSearch.
Qed.
#[global]
Hint Resolve FVars_Open : Piull.


(**
*)
Lemma FVars_Beq_Close :
forall ( Q : Process)(x x0 i : nat),
x <> x0 -> x ∈ FVars (Close_Rec i x0 Q) -> 
x ∈ FVars (Q).
Proof.
  induction Q; 
  intros; simpl in *; 
  try apply Union_inv in H0; Piauto.
  + destruct H0.
    - destruct x; 
       simpl in H0; try contradiction; auto.
      FVars_Beq_Close_Lt H0 x x1.
    - destruct y; 
       simpl in H0; try contradiction; auto.
      FVars_Beq_Close_Lt H0 x2 x1.
  + destruct H0.
    - left.
      apply (IHQ1 _ x0 i); auto.
    - right.
      apply (IHQ2 _ x0 i); auto.
  + destruct H0.
    - simpl in H0.
      apply Union_inv in H0.
      destruct H0.
      * destruct x; 
         simpl in H0; try contradiction; auto.
        FVars_Beq_Close_Lt H0 x x1.
      * destruct y;
         simpl in H0; try contradiction; auto.
        FVars_Beq_Close_Lt H0 x2 x1.
    - right.
      apply (IHQ x0 x1 i); auto.
  + destruct x; 
     simpl in H0; try contradiction; auto.
    FVars_Beq_Close_Lt H0 x x1.
  + destruct H0.
    - destruct x; 
       simpl in H0; try contradiction; auto.
      FVars_Beq_Close_Lt H0 x x1.
    - right.
      apply (IHQ x0 x1 i); auto.
  + apply (IHQ x x0 (S i)); auto.
  + destruct H0.
    - destruct x; 
       simpl in H0; try contradiction; auto.
      FVars_Beq_Close_Lt H0 x x1.
    - right.
      apply (IHQ x0 x1 (S i)); auto.
  + destruct H0.
    - destruct x; 
       simpl in H0; try contradiction; auto.
      FVars_Beq_Close_Lt H0 x x1.
    - right.
      apply (IHQ x0 x1 (S i)); auto.
Qed.
#[global]
Hint Resolve FVars_Beq_Close : Piull.


(**
*)
Lemma FVars_Close_NotIn :
forall ( P : Process )( x x0 i: nat),
x <> x0 -> ~ x ∈ FVars (Close_Rec i x0 P) -> ~ x ∈ FVars (P).
Proof.
  induction P; intros; simpl; unfold not; intro; apply H0; auto.
  + apply Union_inv in H1.
    destruct H1.
    - destruct x; simpl in H1; try contradiction.
      apply Singleton_inv in H1.
      rewrite <- H1 in H.
      apply beq_nat_false_inv in H.
      simpl.
      rewrite H.
      left; simpl.
      rewrite H1.
      constructor.
    - destruct y; simpl in H1; try contradiction.
      apply Singleton_inv in H1.
      rewrite <- H1 in H.
      apply beq_nat_false_inv in H.
      simpl.
      rewrite H.
      right; simpl.
      rewrite H1.
      constructor.
  + simpl in H0.
    apply No_Union_No_Each in H0.
    destruct H0 as [HA HB].
    apply Union_inv in H1.
    destruct H1.
    - apply IHP1 in HA; try contradiction; auto.
    - apply IHP2 in HB; try contradiction; auto.
  + simpl in H0.
    apply No_Union_No_Each in H0.
    destruct H0 as [HA HC].
    apply Union_inv in H1.
    destruct H1.
    - apply No_Union_No_Each in HA.
      destruct HA as [HA HB].
      apply Union_inv in H0.
      destruct H0.
      * destruct x; simpl in H0; try contradiction.
        apply Singleton_inv in H0.
        rewrite <- H0 in H.
        apply beq_nat_false_inv in H.
        simpl.
        rewrite H.
        left; left; simpl.
        rewrite H0.
        constructor.
      * destruct y; simpl in H0; try contradiction.
        apply Singleton_inv in H0.
        rewrite <- H0 in H.
        apply beq_nat_false_inv in H.
        simpl.
        rewrite H.
        left; right; simpl.
        rewrite H0.
        constructor.
    - apply IHP in HC; try contradiction; auto.
  + simpl in H0.
    destruct x; simpl in H1; try contradiction.
        apply Singleton_inv in H1.
        rewrite <- H1 in H.
        apply beq_nat_false_inv in H.
        simpl.
        rewrite H.
        simpl.
        rewrite H1.
        constructor.
  + simpl in H0.
    apply No_Union_No_Each in H0.
    destruct H0 as [HA HB].
    apply Union_inv in H1.
    destruct H1.
    - destruct x; simpl in H0; try contradiction.
      apply Singleton_inv in H0.
      rewrite <- H0 in H.
      apply beq_nat_false_inv in H.
      simpl.
      rewrite H.
      left; simpl.
      rewrite H0.
      constructor.
    - apply IHP in HB; try contradiction; auto.
  + simpl in H0.
    apply IHP in H0; auto.
    contradiction.
  + apply Union_inv in H1.
    destruct H1.
    - destruct x; simpl in H1; try contradiction.
      apply Singleton_inv in H1.
      rewrite <- H1 in H.
      apply beq_nat_false_inv in H.
      simpl.
      rewrite H.
      left; simpl.
      rewrite H1.
      constructor.
    - simpl in H0.
      apply No_Union_No_Each in H0.
      destruct H0 as [HA HB].
      apply IHP in HB; auto.
      contradiction.
  + apply Union_inv in H1.
    destruct H1.
    - destruct x; simpl in H1; try contradiction.
      apply Singleton_inv in H1.
      rewrite <- H1 in H.
      apply beq_nat_false_inv in H.
      simpl.
      rewrite H.
      left; simpl.
      rewrite H1.
      constructor.
    - simpl in H0.
      apply No_Union_No_Each in H0.
      destruct H0 as [HA HB].
      apply IHP in HB; auto.
      contradiction.
Qed.
#[global]
Hint Resolve FVars_Close_NotIn : Piull.


(**
*)
Lemma FVars_Subst :
forall ( P : Process )( x y x0 : nat ), 
x ∈ FVars ({y \ x0} P) -> x = y \/ x ∈ FVars (P).
Proof.
  induction P; intros; simpl; auto.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - destruct x; try contradiction.
      simpl in H.
      DecidSimple x x1.
      rewrite e in H.
      apply Singleton_inv in H; auto.
      rewrite n in H.
      apply Singleton_inv in H; auto.
      rewrite H.
      right; left.
      constructor.
    - destruct y; try contradiction.
      simpl in H.
      DecidSimple x2 x1.
      rewrite e in H.
      apply Singleton_inv in H; auto.
      rewrite n in H.
      apply Singleton_inv in H; auto.
      rewrite H.
      right; right.
      constructor.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - apply IHP1 in H.
      destruct H; auto.
      OrSearch.
    - apply IHP2 in H.
      destruct H; auto.
      OrSearch.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - apply Union_inv in H.
      destruct H.
      * destruct x; try contradiction.
        simpl in H.
        DecidSimple x x1.
        rewrite e in H.
        apply Singleton_inv in H; auto.
        rewrite n in H.
        apply Singleton_inv in H; auto.
        rewrite H.
        right; left; left.
        constructor.
      * destruct y; try contradiction.
        simpl in H.
        DecidSimple x2 x1.
        rewrite e in H.
        apply Singleton_inv in H; auto.
        rewrite n in H.
        apply Singleton_inv in H; auto.
        rewrite H.
        right; left; right.
        constructor.
    - apply IHP in H.
      destruct H; auto.
      right; right; auto.
  + simpl in H.
    destruct x; try contradiction.
    simpl in H.
    DecidSimple x x1.
    rewrite e in H.
    apply Singleton_inv in H; auto.
    rewrite n in H.
    apply Singleton_inv in H; auto.
    rewrite H.
    right.
    constructor.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - destruct x; try contradiction.
      simpl in H.
      DecidSimple x x1.
      rewrite e in H.
      apply Singleton_inv in H; auto.
      rewrite n in H.
      apply Singleton_inv in H; auto.
      rewrite H.
      right; left.
      constructor.
    - apply IHP in H.
      destruct H; auto.
      right; right; auto.
  + simpl in H.
    apply IHP in H; auto.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - destruct x; try contradiction.
      simpl in H.
      DecidSimple x x1.
      rewrite e in H.
      apply Singleton_inv in H; auto.
      rewrite n in H.
      apply Singleton_inv in H; auto.
      rewrite H.
      right; left.
      constructor.
    - apply IHP in H.
      destruct H; auto.
      right; right; auto.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - destruct x; try contradiction.
      simpl in H.
      DecidSimple x x1.
      rewrite e in H.
      apply Singleton_inv in H; auto.
      rewrite n in H.
      apply Singleton_inv in H; auto.
      rewrite H.
      right; left.
      constructor.
    - apply IHP in H.
      destruct H; auto.
      OrSearch.
Qed.
#[global]
Hint Resolve FVars_Subst : Piull.



Lemma FVars_Reduction :
forall (P Q: Process)(x : nat),
(~ x ∈ FVars P) -> P --> Q -> 
(~ x ∈ FVars Q).
Proof.
  intros.
  induction H0.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.

(* Search FVars. *)









