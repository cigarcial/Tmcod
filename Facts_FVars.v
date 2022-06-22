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
Lemma No_Union_No_Each : 
forall (x : nat)( X Y : FVarsE ),
~(x ∈ (X ∪ Y)) -> ~(x ∈ X) /\ ~(x ∈ Y).
Proof.
  unfold not in *.
  intros.
  constructor;
   intros;
   apply H; OrSearch.
Qed.
#[global]
Hint Resolve No_Union_No_Each : Piull.


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
  induction H.
  + simpl.
    apply Extensionality_Ensembles.
    constructor.
    - unfold Included.
      intros.
      apply Union_inv in H.
      destruct H.
      * apply Union_inv in H.
        destruct H.
        ++ OrSearch.
        ++ OrSearch.
      * OrSearch.
    - unfold Included.
      intros.
      apply Union_inv in H.
      destruct H.
      * OrSearch.
      * apply Union_inv in H.
        destruct H.
        ++ OrSearch.
        ++ OrSearch.
  + simpl.
    apply Extensionality_Ensembles.
    constructor.
    - unfold Included.
      intros.
      apply Union_inv in H0.
      destruct H0.
      * OrSearch.
      * OrSearch.
    - unfold Included.
      intros.
      apply Union_inv in H0.
      destruct H0.
      * OrSearch.
      * OrSearch.
Qed.
#[global]
Hint Resolve Cong_FVars : Piull.
(**
Proof.
  intros.
  induction H; simpl; Piauto;
  try apply Extensionality_Ensembles;
  try constructor;
  try unfold Included;
  try intros;
  repeat (apply Union_inv in H; destruct H); 
  try OrSearch.
Qed.
#[global]
Hint Resolve Cong_FVars : Piull.
*)

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
~ (u ∈ FVars ({x \ u} P)).
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


(**
*)
Lemma Close_FVars_Beq:
forall (P : Process) (u x i : nat), 
u <> x -> u ∈ FVars (Close_Rec i x P) -> u ∈ FVars P.
Proof.
  intro.
  induction P; intros; Piauto.
  + simpl in H0.
    destruct H0.
    - destruct x; try contradiction.
      simpl in H0.
      DecidSimple x x0.
      * rewrite e in H0.
        simpl in H0.
        contradiction.
      * rewrite n in H0.
        simpl in H0.
        inversions H0.
        OrSearch.
    - destruct y; try contradiction.
      simpl in H0.
      DecidSimple x2 x0.
      * rewrite e in H0.
        simpl in H0.
        contradiction.
      * rewrite n in H0.
        simpl in H0.
        inversions H0.
        OrSearch.
  + simpl in H0. simpl.
    inversions H0.
    - left.
      apply (IHP1 u x i); Piauto.
    - right.
      apply (IHP2 u x i); Piauto.
  + simpl in H0.
    destruct H0.
    - destruct H0.
      * destruct x; try contradiction.
        simpl in H0.
        DecidSimple x x0.
        ** rewrite e in H0.
           simpl in H0.
           contradiction.
        ** rewrite n in H0.
           simpl in H0.
           inversions H0.
           OrSearch.
      * destruct y; try contradiction.
        simpl in H0.
        DecidSimple x2 x0.
        ** rewrite e in H0.
           simpl in H0.
           contradiction.
        ** rewrite n in H0.
           simpl in H0.
           inversions H0.
           OrSearch.
    - simpl. right.
      apply (IHP x1 x0 i); Piauto.
  + simpl in H0.
    destruct x; try contradiction.
    simpl in H0.
    DecidSimple x x0.
    - rewrite e in H0.
      simpl in H0.
      contradiction.
    - rewrite n in H0.
      simpl in H0.
      inversions H0.
      OrSearch.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - destruct x; try contradiction.
      simpl in H0.
      DecidSimple x x0.
      * rewrite e in H0.
        simpl in H0.
        inversions H0.
      * rewrite n in H0.
        simpl in H0.
        inversions H0.
        OrSearch.
    - specialize (IHP _ _ i H H0).
      OrSearch.
  + simpl in H0.
    simpl.
    apply (IHP u x (S i)); Piauto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - destruct x; try contradiction.
      simpl in H0.
      DecidSimple x x0.
      * rewrite e in H0.
        inversions H0.
      * rewrite n in H0.
        inversions H0.
        OrSearch.
    - simpl in H0.
      specialize (IHP _ _ _ H H0).
      OrSearch.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - destruct x; try contradiction.
      simpl in H0.
      DecidSimple x x0.
      * rewrite e in H0.
        inversions H0.
      * rewrite n in H0.
        inversions H0.
        OrSearch.
    - simpl in H0.
      specialize (IHP _ _ _ H H0).
      OrSearch.
Qed.
#[global]
Hint Resolve Close_FVars_Beq : Piull.


(**
*)
Lemma FVars_Subst_In :
forall ( P : Process )( x y x0 : nat ),
x0 ∈ FVars P -> x ∈ FVars ({y \ x0} P) -> (x = y \/ (x ∈ FVars (P) /\ x <> x0)).
Proof.
  intros.
  DecidSimple x y.
  DecidSimple x x0.
  apply beq_nat_false in n.
  + apply beq_nat_true in e.
    rewrite e in *.
    apply After_Subst_No_FVar in H0; Piauto.
  + apply FVars_Subst in H0.
    destruct H0; Piauto.
    apply beq_nat_false in n0.
    right; constructor; Piauto.
Qed.
#[global]
Hint Resolve FVars_Subst_In : Piull.


(**
*)
Lemma FVars_Res_Neg :
forall ( P : Process )( x : nat ),
~ x ∈ FVars (ν P) <-> ~ x ∈ FVars P.
Proof.
  constructor; Piauto.
Qed.
#[global]
Hint Resolve FVars_Res_Neg : Piull.


(**
*)
Lemma FVars_Res :
forall ( P : Process )( x : nat ),
x ∈ FVars (ν P) <-> x ∈ FVars P.
Proof.
  constructor; Piauto.
Qed.
#[global]
Hint Resolve FVars_Res : Piull.


(**
*)
Lemma NFVar_Close_Names :
forall (z : Name)(x i : nat ),
x ∈ FVars_Name (Close_Name i x z) -> False.
Proof.
  intros.
  destruct z; simpl in H; try contradiction.
  DecidSimple x0 x.
  + rewrite e in H.
    simpl in H.
    contradiction.
  + rewrite n in H.
    simpl in H.
    apply Singleton_inv in H.
    apply beq_nat_false in n.
    contradiction.
Qed.
#[global]
Hint Resolve NFVar_Close_Names : Piull.


(**
*)
Lemma NFVar_Close_Cases :
forall (P : Process )( x u : nat),
~ x ∈ FVars (Close u P) -> x = u \/ ( x <> u /\ ~ x ∈ FVars P).
Proof.
  intros.
  DecidSimple x u.
  apply beq_nat_false in n.
  right.
  constructor; Piauto.
  unfold not.
  intros.
  Piauto.
  specialize (FVars_Close_Beq  P x u 0 n H0) as Hx.
  Piauto.
Qed.
#[global]
Hint Resolve NFVar_Close_Cases : Piull.


(**
*)
Lemma NFVar_Close :
forall ( P : Process )( i x : nat ),
~ x ∈ FVars (Close_Rec i x P).
Proof.
  unfold not.
  induction P; simpl; intros; try inversions H; ePiauto.
  inversions H0; ePiauto.
Qed.
#[global]
Hint Resolve NFVar_Close : Piull.


(** 
*)
Lemma Close_Parallel :
forall ( u : nat)(P Q : Process),
Close u (P ↓ Q) = (Close u P) ↓ (Close u Q).
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Close_Parallel : Piull.


(** FVars_Close_NotIn
*)
Lemma FVars_Reduction_Neg :
forall ( P Q : Process )( x : nat),
~ x ∈ FVars P -> P --> Q -> ~ x ∈ FVars Q.
Proof.
  intros.
  induction H0.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H5; Piauto.

    destruct H5.
    apply No_FVars_Parallel in H6.
    destruct H6 as [HA HB].
    unfold not.
    intros.
    apply FVars_Subst in H6.
    destruct H6; try contradiction.
    rewrite H6 in HB.
    simpl in HB.
    apply No_Union_No_Each in HB.
    destruct HB.
    apply H8.
    constructor.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H5; Piauto.

    destruct H5.
    apply No_FVars_Parallel in H6.
    destruct H6 as [HA HB].
    unfold not.
    intros.
    apply FVars_Subst in H6.
    destruct H6; try contradiction.
    rewrite H6 in HB.
    simpl in HB.
    apply No_Union_No_Each in HB.
    destruct HB.
    apply H7.
    constructor.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H5; Piauto.
    
    destruct H5.
    apply No_FVars_Parallel in H6.
    destruct H6 as [HA HB].
    unfold not.
    intros.
    apply FVars_Subst in H6.
    destruct H6; try contradiction.
    rewrite H6 in HA.
    simpl in HA.
    apply No_Union_No_Each in HA.
    destruct HA.
    apply H7.
    constructor.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H5; Piauto.

    destruct H5.
    apply No_FVars_Parallel in H6.
    destruct H6 as [HA HB].
    unfold not.
    intros.
    apply FVars_Subst in H6.
    destruct H6; try contradiction.
    rewrite H6 in HA.
    simpl in HA.
    apply No_Union_No_Each in HA.
    destruct HA.
    apply H8.
    constructor.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H4; Piauto.

    destruct H4.
    apply No_FVars_Parallel in H5.
    destruct H5 as [HA HB].
    unfold not in *.
    intros.
    apply HB.
    simpl.
    OrSearch.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H4; Piauto.

    destruct H4.
    apply No_FVars_Parallel in H5.
    destruct H5 as [HA HB].
    unfold not in *.
    intros.
    apply HA.
    simpl.
    OrSearch.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x u H) as Ht.
    destruct Ht.
    - rewrite H9 in *.
      apply NFVar_Close.
    - destruct H9.
      apply No_FVars_Parallel in H10.
      destruct H10.
      rewrite Close_Parallel.
      unfold not.
      intros.
      simpl in H12.
      apply Union_inv in H12.
      destruct H12.
      * apply Union_inv in H12.
        destruct H12.
        ++ DecidSimple u u.
           rewrite e in H12.
           inversions H12.
        ++ apply H10.
           apply Close_FVars_Beq in H12; Piauto.
           OrSearch.
      * apply Union_inv in H12.
        destruct H12.
        ++ apply Close_FVars_Beq in H12; Piauto.
           DecidSimple x y.
           -- apply beq_nat_true in e.
              subst.
              apply NFVar_Close in H12; auto.
           -- apply H11.
              OrSearch.
        ++ apply Close_FVars_Beq in H12; Piauto.
           DecidSimple x y.
           -- apply beq_nat_true in e.
              subst.
              apply NFVar_Close in H12; auto.
           -- apply beq_nat_false in n.
              apply FVars_Beq_Close in H12; Piauto.
              apply FVars_Open_Beq in H12; Piauto.
              apply H10.
              OrSearch.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x u H) as Ht.
    destruct Ht.
    - rewrite H9 in *.
      apply NFVar_Close.
    - destruct H9.
      apply No_FVars_Parallel in H10.
      destruct H10.
      rewrite Close_Parallel.
      unfold not.
      intros.
      simpl in H12.
      apply Union_inv in H12.
      destruct H12.
      * apply Union_inv in H12.
        destruct H12.
        ++ DecidSimple u u.
           rewrite e in H12.
           inversions H12.
        ++ apply H10.
           apply Close_FVars_Beq in H12; Piauto.
           OrSearch.
      * apply Union_inv in H12.
        destruct H12.
        ++ apply Close_FVars_Beq in H12; Piauto.
           DecidSimple x y.
           -- apply beq_nat_true in e.
              subst.
              apply NFVar_Close in H12; auto.
           -- apply beq_nat_false in n.
              apply FVars_Beq_Close in H12; Piauto.
              apply FVars_Open_Beq in H12; Piauto.
              apply H10.
              OrSearch.
        ++ apply Close_FVars_Beq in H12; Piauto.
           DecidSimple x y.
           -- apply beq_nat_true in e.
              subst.
              apply NFVar_Close in H12; auto.
           -- apply H11.
              OrSearch.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht.
    - subst.
      unfold not in *.
      intros.
      apply Close_FVars_Beq in H11; Piauto.
      simpl in H11.
      apply Union_inv in H11.
      destruct H11; Piauto.
      apply Union_inv in H11.
      destruct H11.
      apply (NFVar_Close (P ^ y) 0 x0); Piauto.
      apply (NFVar_Close R 0 x0); Piauto.
    - destruct H11.
      apply No_FVars_Parallel in H12.
      destruct H12.
      apply -> FVars_Res_Neg in H13.
      specialize (NFVar_Close_Cases _ x y H13) as Ht.
      apply FVars_Res_Neg.
      destruct Ht.
      * subst.
        apply NFVar_Close.
      * destruct H14.
        unfold not.
        intros.
        apply Close_FVars_Beq in H16; Piauto.
        simpl in H16.
        apply Union_inv in H16.
        destruct H16.
        ++ apply Union_inv in H16.
           destruct H16.
           apply Close_FVars_Beq in H16; Piauto.
           apply FVars_Open_Beq in H16; Piauto.
           apply H12; OrSearch.
           apply Close_FVars_Beq in H16; Piauto.
           apply H15; OrSearch.
        ++ apply H15; OrSearch.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht.
    - rewrite H10 in *.
      apply NFVar_Close.
    - destruct H10.
      apply No_FVars_Parallel in H11.
      destruct H11.
      apply -> FVars_Res_Neg in H11.
      specialize (NFVar_Close_Cases _ x y H11) as Ht.
      apply FVars_Res_Neg.
      unfold not.
      intros.
      apply Close_FVars_Beq in H13; Piauto.
      destruct Ht.
      * subst.
        simpl in H13.
        apply Union_inv in H13.
        destruct H13; Piauto.
        apply Union_inv in H13.
        destruct H13;
        apply NFVar_Close in H13; Piauto.
      * destruct H14.
        destruct H13; Piauto.
        apply H15; OrSearch.
        apply Close_FVars_Beq in H13; Piauto.
        simpl in H13.
        apply Union_inv in H13.
        destruct H13.
        apply H15; OrSearch.
        apply FVars_Open_Beq in H13; Piauto.
        apply H12; OrSearch.
Qed.
#[global]
Hint Resolve FVars_Reduction_Neg : Piull.



(**
*)
Lemma In_FVars_Res : 
forall ( P : Process )( x u  : nat ),
x ∈ FVars (ν Close u P) -> x ∈ FVars P /\ x <> u.
Proof.
  intros.
  DecidSimple x u.
  + apply beq_nat_true in e.
    subst.
    apply NFVar_Close in H.
    contradiction.
  + apply beq_nat_false in n.
    specialize (Close_FVars_Beq P x u 0 n H) as Hx.
    Piauto.
Qed.
#[global]
Hint Resolve In_FVars_Res : Piull.


(**
*)
Lemma Close_Parallel_NFVar :
forall ( P Q : Process )( y : nat ),
~ y ∈ FVars P -> P ↓ Close y Q = Close y (P↓Q).
Proof.
  intros.
  unfold Close.
  simpl.
  rewrite (Close_NoFVar_Eq P y 0); Piauto.
Qed.
#[global]
Hint Resolve Close_Parallel_NFVar : Piull.


(**
*) 
Lemma Rep_Input_NFVar :
forall ( P : Process )( u y : nat), 
y <> u -> ~ y ∈ FVars P -> ~ y ∈ FVars (FName u !· P).
Proof.
  unfold not.
  intros.
  destruct H1; Piauto.
  apply Singleton_inv in H1.
  lia.
Qed.
#[global]
Hint Resolve Rep_Input_NFVar : Piull.



(** FVars_Close_NotIn
*)
Lemma FVars_Reduction_Inv :
forall ( P Q : Process )( x : nat),
x ∈ FVars Q -> P --> Q -> x ∈ FVars P.
Proof.
  intros.
  induction H0.
  + specialize ( FVars_Subst_In _ _ _ _ H4 H) as Hx.
    destruct Hx.
    - DecidSimple y x0.
      simpl.
      rewrite n.
      rewrite H5.
      do 2 right. 
      constructor.
    - destruct H5.
      apply FVars_Res.
      apply FVars_Close_Beq; Piauto.
      OrSearch.
  + specialize ( FVars_Subst_In _ _ _ _ H4 H) as Hx.
    destruct Hx.
    - DecidSimple y x0.
      simpl.
      rewrite n.
      rewrite H5.
      right. left.
      constructor.
    - destruct H5.
      apply FVars_Res.
      apply FVars_Close_Beq; Piauto.
      OrSearch.
  + specialize ( FVars_Subst_In _ _ _ _ H4 H) as Hx.
    destruct Hx.
    - DecidSimple y x0.
      simpl.
      rewrite n.
      subst.
      do 2 left.
      constructor.
    - destruct H5.
      apply FVars_Res.
      apply FVars_Close_Beq; Piauto.
      OrSearch.
  + specialize ( FVars_Subst_In _ _ _ _ H4 H) as Hx.
    destruct Hx.
    - DecidSimple y x0.
      simpl.
      rewrite n.
      subst.
      left.
      right.
      constructor.
    - destruct H5.
      apply FVars_Res.
      apply FVars_Close_Beq; Piauto.
      OrSearch.
  + DecidSimple x x0.
    apply beq_nat_true in e.
    rewrite e in H.
    contradiction.
    apply beq_nat_false in  n.
    apply FVars_Res.
    apply FVars_Close_Beq; Piauto.
    OrSearch.
  + DecidSimple x x0.
    apply beq_nat_true in e.
    rewrite e in H.
    contradiction.
    apply beq_nat_false in  n.
    apply FVars_Res.
    apply FVars_Close_Beq; Piauto.
    OrSearch.
  + apply -> FVars_Res in H.
    DecidSimple x u.
    apply beq_nat_true in e.
    rewrite e in *.
    apply NFVar_Close in H.
    contradiction.

    apply beq_nat_false in n.
    apply FVars_Close_Beq; Piauto.
    apply FVars_Beq_Close in H; Piauto.
    destruct H.
    - destruct H.
      * simpl in H.
        apply Singleton_inv in H.
        lia.
      * OrSearch.
    - apply -> FVars_Res in H.
      DecidSimple x y.
      apply beq_nat_true in e.
      rewrite e in H.
      apply NFVar_Close in H.
      contradiction.
      
      apply beq_nat_false in n0.
      inversions H0.
      rewrite (Cong_FVars
        ((FName u !· P) ↓ (ν Close y (FName u « FName y »· Q)) ) 
        (ν ((FName u !· P) ↓ Close y (FName u « FName y »· Q)) ) ); Piauto.
      rewrite Close_Parallel_NFVar; Piauto.
      apply FVars_Close_Beq; Piauto.
      apply FVars_Beq_Close in H; Piauto.
      destruct H.
      * OrSearch.
      * apply FVars_Open_Beq in H; Piauto.
        OrSearch.
  + apply -> FVars_Res in H.
    DecidSimple x u.
    apply beq_nat_true in e.
    rewrite e in *.
    apply NFVar_Close in H.
    contradiction.

    apply beq_nat_false in n.
    apply FVars_Close_Beq; Piauto.
    apply FVars_Beq_Close in H; Piauto.
    destruct H.
    - destruct H.
      * simpl in H.
        apply Singleton_inv in H.
        lia.
      * OrSearch.
    - apply -> FVars_Res in H.
      DecidSimple x y.
      apply beq_nat_true in e.
      rewrite e in H.
      apply NFVar_Close in H.
      contradiction.
      
      apply beq_nat_false in n0.
      inversions H0.
      rewrite (Cong_FVars
        ((FName u !· P) ↓ (ν Close y (FName u « FName y »· Q)) ) 
        (ν ((FName u !· P) ↓ Close y (FName u « FName y »· Q)) ) ); Piauto.
      rewrite Close_Parallel_NFVar; Piauto.
      apply FVars_Close_Beq; Piauto.
      apply FVars_Beq_Close in H; Piauto.
      destruct H.
      * apply FVars_Open_Beq in H; Piauto.
        OrSearch.
      * OrSearch.
  + apply -> FVars_Res in H.
    DecidSimple x y.
    apply beq_nat_true in e.
    rewrite e in *.
    apply NFVar_Close in H.
    contradiction.

    apply beq_nat_false in n.
    apply FVars_Beq_Close in H; Piauto.
    destruct H.
    - apply -> FVars_Res in H.
      DecidSimple x x0.
      apply beq_nat_true in e.
      rewrite e in H.
      apply NFVar_Close in H.
      contradiction.

      apply beq_nat_false in n0.
      apply FVars_Beq_Close in H; Piauto.
      destruct H.
      * apply FVars_Open_Beq in H; Piauto.
        OrSearch.
      * OrSearch.

    - DecidSimple x x0.
      apply beq_nat_true in e.
      subst.
      contradiction.
      
      apply beq_nat_false in n0.
      right.
      apply FVars_Close_Beq; Piauto.
      OrSearch.
      
      
  + apply -> FVars_Res in H.
    DecidSimple x x0.
    apply beq_nat_true in e.
    rewrite e in *.
    apply NFVar_Close in H.
    contradiction.

    apply beq_nat_false in n.
    apply FVars_Close_Beq; Piauto.
    apply FVars_Beq_Close in H; Piauto.
    destruct H.
    - DecidSimple x y.
      apply beq_nat_true in e.
      subst.
      contradiction.
      
      apply beq_nat_false in n0.
      left.
      apply FVars_Close_Beq; Piauto.
      OrSearch.
    - apply -> FVars_Res in H.
      DecidSimple x y.
      apply beq_nat_true in e.
      rewrite e in H.
      apply NFVar_Close in H.
      contradiction.
      
      apply beq_nat_false in n0.
      inversions H0.
      apply FVars_Beq_Close in H; Piauto.
      destruct H.
      * OrSearch.
      * apply FVars_Open_Beq in H; Piauto.
        OrSearch.
Qed.
#[global]
Hint Resolve FVars_Reduction_Inv : Piull.


(**
*)
Lemma Not_FVar_Subst :
forall ( x w z : nat )( P : Process ),
x <> w -> ~ x ∈ FVars (P) ->
~ x ∈ FVars ({w \ z} P).
Proof.
  unfold not.
  intros.
  apply FVars_Subst in H1.
  destruct H1; Piauto.
Qed.
#[global]
Hint Resolve Not_FVar_Subst : Piull.

  
  
  
  
  
  
  
  
  
  
  
  
  
  
  