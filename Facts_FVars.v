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


(*
*)
Lemma Close_NoFVar_Eq :
forall ( P : Process )(z k: nat),
~ ( z ∈ (FVars P) ) -> ( Close_Rec k z P ) = P.
Proof.
  unfold Close.
  induction P; intros.
  + auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP1; auto.
    rewrite IHP2; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [H HC].
    simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP; auto.
    rewrite FVars_Name_No_Close; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    simpl.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    simpl.
    rewrite IHP; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite IHP; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite IHP; auto.
Qed.



Lemma FVars_Bex_Name :
forall ( x : Name)(i j : nat),
FVars_Name (Bex_Name i j x) = FVars_Name x.
Proof.
  destruct x; intros; simpl; auto.
  EasyDec i i0 e n; try EasyDec i j e n0.
Qed.



Lemma FVars_Bex_Process:
forall (P : Process)(i j : nat),
FVars P = FVars ({i <~> j} P).
Proof.
  InductionProcessRev P FVars_Bex_Name.
Qed.


(*
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
      right. auto.
      left. auto.
    - unfold Included. 
      intros.
      apply Union_inv in H.
      destruct H.
      right. auto.
      left. auto.
  + simpl.
    apply FVars_Bex_Process.  
  + simpl.
    apply Extensionality_Ensembles.
    constructor.
    - unfold Included.
      intros.
      apply Union_inv in H.
      destruct H.
      apply Union_inv in H.
      destruct H.
      left. auto.
      right. left. auto.
      right. right. auto.
    - unfold Included.
      intros.
      apply Union_inv in H.
      destruct H.
      left. left. auto.
      apply Union_inv in H.
      destruct H.
      left. right. auto.
      right. auto.
  + auto.
Qed.


Lemma No_FVars_Parallel :
forall (P Q : Process)( u : nat),
( ~(u ∈ FVars (P ↓ Q))) -> (~ u ∈ FVars P) /\ (~ u ∈ FVars Q).
Proof.
  unfold not.
  intros.
  constructor.
  + intros.
    assert ( HA : u ∈ FVars (P ↓ Q));
      try constructor; auto.
  + intros.
    assert ( HA : u ∈ FVars (P ↓ Q));
      try right; auto.
Qed.

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
    left.
    auto.
  * apply not_true_iff_false in n.
    rewrite n in H.
    simpl in H.
    apply Singleton_inv in H.
    rewrite H in n.
    apply beq_nat_false in n.
    contradiction.
Qed.



Require Import Coq.Program.Equality.

(*
*)
Lemma After_Subst_No_FVar :
forall (P : Process)(u x : nat),
u <> x -> 
u ∈ FVars ({x \ u} P) -> False.
Proof.
  intro.
  dependent induction P; intros; try simpl in H0.
  + inversions H0.
  + apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (Subst_Name_Gen_Output u x0 y); auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply (IHP1 u x); auto.
    - apply (IHP2 u x); auto.
  + apply Union_inv in H0.
    destruct H0.
    apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (Subst_Name_Gen_Output u x0 y); auto.
    - apply (IHP u x0); auto.
  + apply (Subst_Name_Gen_Output u x0 x); auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (IHP u x0); auto.
  + apply (IHP u x); auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (IHP u x0); auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (IHP u x0); auto.
Qed.


Lemma FVars_Close_Beq_Names :
forall(x : Name)(u x0 i : nat),
u <> x0 -> u ∈ FVars_Name x -> 
Close_Name i x0 x = FName u.
Proof.
  intros.
  destruct x; simpl in H0; try contradiction; auto.
  apply Singleton_inv in H0.
  destruct (bool_dec (x =? x0) true); simpl.
  + apply beq_nat_true in e.
    lia.
  + apply not_true_iff_false in n; rewrite n.
    auto.
Qed.


Lemma FVars_Close_Beq :
forall ( P : Process ) (u x i : nat),
u <> x -> u ∈ FVars P -> u ∈ FVars (Close_Rec i x P).
Proof.
  induction P; intros; simpl; auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
    - right.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left; apply IHP1; auto.
    - right; apply IHP2; auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - apply Union_inv in H0.
      destruct H0.
      * left; left.
        rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
        simpl; constructor.
      * left; right.
        rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
        simpl; constructor.
    - right.
      apply IHP; auto.
  + simpl in H0.
    rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
    simpl; constructor.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
    - right.
      apply IHP; auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
    - right.
      apply IHP; auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
    - right.
      apply IHP; auto.
Qed.



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



(*
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


(*
*)
Lemma FVars_Open_Beq :
forall ( P : Process)(u x i: nat),
u <> x -> ( u ∈ FVars P <-> u ∈ FVars ({i ~> x}P)).
Proof.
  intro.
  induction P; intros; simpl; try constructor; try intros; try contradiction.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names x u x0 i); auto.
      constructor.
    - right.
      rewrite (FVars_Open_Beq_Names y u x0 i); auto.
      constructor.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names_Inv _ u x0 i); auto.
      constructor.
    - right.
      rewrite (FVars_Open_Beq_Names_Inv _ u x0 i); auto.
      constructor.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      apply IHP1; auto.
    - right.
      apply IHP2; auto.
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
      * left. left.
        rewrite (FVars_Open_Beq_Names x u x0 i); auto.
        constructor.
      * left. right.
        rewrite (FVars_Open_Beq_Names y u x0 i); auto.
        constructor.
    - right.
      apply IHP; auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply Union_inv in H0.
      destruct H0.
      * left. left.
        rewrite (FVars_Open_Beq_Names_Inv x u x0 i); auto.
        constructor.
      * left. right.
        rewrite (FVars_Open_Beq_Names_Inv y u x0 i); auto.
        constructor.
    - right.
      apply <- (IHP u x0 i); auto.
  + rewrite (FVars_Open_Beq_Names x u x0 i); auto.
    constructor.
  + rewrite (FVars_Open_Beq_Names_Inv x u x0 i); auto.
    constructor.
  + apply Union_inv in H0.
    destruct H0.
    - left. 
      rewrite (FVars_Open_Beq_Names x u x0 i); auto.
      constructor.
    - right; apply IHP; auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names_Inv _ u x0 i); auto.
      constructor.
    - right; apply <- (IHP u x0 i); auto.
  + apply IHP; auto.
  + apply <- (IHP u x (S i)); auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names x u x0 i); auto.
      constructor.
    - right; apply IHP; auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names_Inv _ u x0 i); auto.
      constructor.
    - right; apply <- (IHP u x0 (S i)); auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names x u x0 i); auto.
      constructor.
    - right; apply IHP; auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names_Inv _ u x0 i); auto.
      constructor.
    - right; apply <- (IHP u x0 (S i)); auto.
Qed.





Lemma FVars_Open :
forall (Q : Process)( y x i : nat),
x ∈ FVars ( {i ~> y} Q ) ->  x = y \/ x ∈ FVars ( Q ).
Proof.
  induction Q; intros; simpl; auto.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - destruct x.
      * simpl in *.
        apply Singleton_inv in H.
        right; left. rewrite H; constructor.
      * simpl in *.
        EasyDec i i0 e n.
        rewrite e in H.
        simpl in H.
        apply Singleton_inv in H.
        auto.
        rewrite n in H.
        simpl in H.
        contradiction.
    - destruct y.
      * simpl in *.
        apply Singleton_inv in H.
        right; right; rewrite H; constructor.
      * simpl in *.
        EasyDec i i0 e n.
        rewrite e in H.
        simpl in H.
        apply Singleton_inv in H.
        auto.
        rewrite n in H.
        simpl in H.
        contradiction; auto.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - apply IHQ1 in H.
      destruct H; auto.
      right; left; auto.
    - apply IHQ2 in H.
      destruct H; auto.
      right; right; auto.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - apply Union_inv in H.
      destruct H.
      * destruct x.
        ** simpl in *.
          apply Singleton_inv in H.
          rewrite H.
          right; left; left. constructor.
        ** simpl in *.
          EasyDec i i0 e n.
          rewrite e in H.
          simpl in H.
          apply Singleton_inv in H.
          rewrite H.
          auto.
          rewrite n in H.
          simpl in H.
          contradiction.
      * destruct y.
        ** simpl in *.
          apply Singleton_inv in H.
          rewrite H.
          right; left; right. constructor.
        ** simpl in *.
          EasyDec i i0 e n.
          rewrite e in H.
          simpl in H.
          apply Singleton_inv in H.
          rewrite H.
          auto.
          rewrite n in H.
          simpl in H.
          contradiction.
    - apply IHQ in H.
      destruct H; auto.
      right; right; auto.
  + simpl in H.
    destruct x.
    - simpl in *.
      apply Singleton_inv in H.
      rewrite H.
      right; constructor.
    - simpl in *.
      EasyDec i i0 e n.
      rewrite e in H.
      simpl in H.
      apply Singleton_inv in H.
      rewrite H.
      auto.
      rewrite n in H.
      simpl in H.
      contradiction.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - destruct x.
      * simpl in *.
        apply Singleton_inv in H.
        rewrite H.
        right; left; constructor.
      * simpl in *.
        EasyDec i i0 e n.
        rewrite e in H.
        simpl in H.
        apply Singleton_inv in H.
        rewrite H.
        auto.
        rewrite n in H.
        simpl in H.
        contradiction.
    - apply IHQ in H.
      destruct H; auto.
      right; right; auto.
  + simpl in H.
    apply (IHQ _ _ (S i)); auto.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - destruct x.
      * simpl in *.
        apply Singleton_inv in H.
        rewrite H.
        right; left; constructor.
      * simpl in *.
        EasyDec i i0 e n.
        rewrite e in H.
        simpl in H.
        apply Singleton_inv in H.
        rewrite H.
        auto.
        rewrite n in H.
        simpl in H.
        contradiction.
    - apply IHQ in H.
      destruct H; auto.
      right; right; auto.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - destruct x.
      * simpl in *.
        apply Singleton_inv in H.
        rewrite H.
        right; left; constructor.
      * simpl in *.
        EasyDec i i0 e n.
        rewrite e in H.
        simpl in H.
        apply Singleton_inv in H.
        rewrite H.
        auto.
        rewrite n in H.
        simpl in H.
        contradiction.
    - apply IHQ in H.
      destruct H; auto.
      right; right; auto.
Qed.


Lemma FVars_Beq_Close :
forall ( Q : Process)(x x0 i : nat),
x <> x0 -> x ∈ FVars (Close_Rec i x0 Q) -> 
x ∈ FVars (Q).
Proof.
  induction Q; intros; simpl; auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - destruct x; 
       simpl in H0; try contradiction; auto.
      EasyDec x x1 e n.
      rewrite e in H0.
      simpl in H0.
      contradiction.
      rewrite n in H0.
      apply Singleton_inv in H0.
      rewrite H0.
      left; constructor.
    - destruct y; 
       simpl in H0; try contradiction; auto.
      EasyDec x2 x1 e n.
      rewrite e in H0.
      simpl in H0.
      contradiction.
      rewrite n in H0.
      apply Singleton_inv in H0.
      rewrite H0.
      right; constructor.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left.
      apply (IHQ1 _ x0 i); auto.
    - right.
      apply (IHQ2 _ x0 i); auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - simpl in H0.
      apply Union_inv in H0.
      destruct H0.
      * destruct x; 
         simpl in H0; try contradiction; auto.
        EasyDec x x1 e n.
        rewrite e in H0.
        simpl in H0.
        contradiction.
        rewrite n in H0.
        apply Singleton_inv in H0.
        rewrite H0.
        left; left; constructor.
      * destruct y;
         simpl in H0; try contradiction; auto.
        EasyDec x2 x1 e n.
        rewrite e in H0.
        simpl in H0.
        contradiction.
        rewrite n in H0.
        apply Singleton_inv in H0.
        rewrite H0.
        left; right; constructor.
    - right.
      apply (IHQ x0 x1 i); auto.
  + simpl in H0.
    destruct x; 
     simpl in H0; try contradiction; auto.
    EasyDec x x1 e n.
    rewrite e in H0.
    simpl in H0.
    contradiction.
    rewrite n in H0.
    apply Singleton_inv in H0.
    rewrite H0.
    constructor.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - destruct x; 
       simpl in H0; try contradiction; auto.
      EasyDec x x1 e n.
      rewrite e in H0.
      simpl in H0.
      contradiction.
      rewrite n in H0.
      apply Singleton_inv in H0.
      rewrite H0.
      left; constructor.
    - right.
      apply (IHQ x0 x1 i); auto.
  + simpl in H0.
    apply (IHQ x x0 (S i)); auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - destruct x; 
       simpl in H0; try contradiction; auto.
      EasyDec x x1 e n.
      rewrite e in H0.
      simpl in H0.
      contradiction.
      rewrite n in H0.
      apply Singleton_inv in H0.
      rewrite H0.
      left; constructor.
    - right.
      apply (IHQ x0 x1 (S i)); auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - destruct x; 
       simpl in H0; try contradiction; auto.
      EasyDec x x1 e n.
      rewrite e in H0.
      simpl in H0.
      contradiction.
      rewrite n in H0.
      apply Singleton_inv in H0.
      rewrite H0.
      left; constructor.
    - right.
      apply (IHQ x0 x1 (S i)); auto.
Qed.





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
      EasyDec x x1 e n.
      rewrite e in H.
      apply Singleton_inv in H; auto.
      rewrite n in H.
      apply Singleton_inv in H; auto.
      rewrite H.
      right; left.
      constructor.
    - destruct y; try contradiction.
      simpl in H.
      EasyDec x2 x1 e n.
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
      right; left; auto.
    - apply IHP2 in H.
      destruct H; auto.
      right; right; auto.
  + simpl in H.
    apply Union_inv in H.
    destruct H.
    - apply Union_inv in H.
      destruct H.
      * destruct x; try contradiction.
        simpl in H.
        EasyDec x x1 e n.
        rewrite e in H.
        apply Singleton_inv in H; auto.
        rewrite n in H.
        apply Singleton_inv in H; auto.
        rewrite H.
        right; left; left.
        constructor.
      * destruct y; try contradiction.
        simpl in H.
        EasyDec x2 x1 e n.
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
    EasyDec x x1 e n.
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
      EasyDec x x1 e n.
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
      EasyDec x x1 e n.
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
      EasyDec x x1 e n.
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
Qed.






