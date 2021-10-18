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
Lemma Extl2 :
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
Hint Resolve Extl2 : Piull.


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
forall (D F G : list Assignment)(P Q : Process),
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
Lemma NFVar_Close :
forall ( P : Process )( i x : nat ),
~ x ∈ FVars (Close_Rec i x P).
Proof.
  unfold not.
  induction P; simpl; intros; try inversions H; eauto with Piull.
  inversions H0; eauto with Piull.
Qed.
#[global]
Hint Resolve NFVar_Close : Piull.


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


(** FVars_Close_NotIn
*)
Lemma Close_Res_Rew :
forall (P : Process)(u i: nat),
Close_Rec i u (ν P) = (ν (Close_Rec (S i) u P)).
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Close_Res_Rew : Piull.


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
    destruct Ht; try rewrite H3; Piauto.
    destruct H3.
(*    apply No_FVars_Parallel in H4.
    destruct H4 as [HA HB].
    unfold not.
    intros.
    apply FVars_Subst in H4.
    destruct H4; try contradiction.
    rewrite H4 in HB.
    simpl in HB.
    apply No_Union_No_Each in HB.
    destruct HB.
    apply H6.
    constructor.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H3; Piauto.
    destruct H3.
    apply No_FVars_Parallel in H4.
    destruct H4 as [HA HB].
    unfold not.
    intros.
    apply FVars_Subst in H4.
    destruct H4; try contradiction.
    rewrite H4 in HB.
    simpl in HB.
    apply No_Union_No_Each in HB.
    destruct HB.
    apply H5.
    constructor.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H3; Piauto.
    destruct H3.
    apply No_FVars_Parallel in H4.
    destruct H4 as [HA HB].
    unfold not.
    intros.
    apply FVars_Subst in H4.
    destruct H4; try contradiction.
    rewrite H4 in HA.
    simpl in HA.
    apply No_Union_No_Each in HA.
    destruct HA.
    apply H5.
    constructor.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H3; Piauto.
    destruct H3.
    apply No_FVars_Parallel in H4.
    destruct H4 as [HA HB].
    unfold not.
    intros.
    apply FVars_Subst in H4.
    destruct H4; try contradiction.
    rewrite H4 in HA.
    simpl in HA.
    apply No_Union_No_Each in HA.
    destruct HA.
    apply H6.
    constructor.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H3; Piauto.
    destruct H3.
    apply No_FVars_Parallel in H4.
    destruct H4 as [HA HB].
    unfold not in *.
    intros.
    apply HB.
    simpl.
    OrSearch.
  + apply -> FVars_Res_Neg in H.
    specialize (NFVar_Close_Cases _ x x0 H) as Ht.
    destruct Ht; try rewrite H3; Piauto.
    destruct H3.
    apply No_FVars_Parallel in H4.
    destruct H4 as [HA HB].
    unfold not in *.
    intros.
    apply HA.
    simpl.
    OrSearch.
  + apply -> FVars_Res_Neg in H.
    apply FVars_Res_Neg.
    specialize (NFVar_Close_Cases _ x u H) as Ht.
    destruct Ht.
    - rewrite H7 in *.
      apply NFVar_Close.
    - destruct H7.
      apply -> FVars_Res_Neg in H8.
      specialize (NFVar_Close_Cases _ x y H8) as Ht.
      destruct Ht.
      * rewrite H9.
        unfold Close.
        rewrite Close_Res_Rew.
        apply FVars_Res_Neg.
        rewrite Close_Permutation; Piauto.
      * destruct H9.
        apply No_FVars_Parallel in H10.
        destruct H10 as [HA HB].
        unfold not.
        intros.
        apply Close_FVars_Beq in H10; Piauto.
        apply -> FVars_Res in H10.
        apply Close_FVars_Beq in H10; Piauto.
        simpl in H10.
        destruct H10.
        simpl in HB.
        apply No_Union_No_Each in HB.
        destruct HB.
        ++ destruct H10; try contradiction.
        ++ apply FVars_Open_Beq in H10; Piauto.
           simpl in HA.
           apply No_Union_No_Each in HA.
           destruct HA; contradiction.
  + apply -> FVars_Res_Neg in H.
    apply FVars_Res_Neg.
    specialize (NFVar_Close_Cases _ x u H) as Ht.
    destruct Ht.
    - rewrite H7 in *.
      apply NFVar_Close.
    - destruct H7.
      apply -> FVars_Res_Neg in H8.
      specialize (NFVar_Close_Cases _ x y H8) as Ht.
      destruct Ht.
      * rewrite H9.
        unfold Close.
        rewrite Close_Res_Rew.
        apply FVars_Res_Neg.
        rewrite Close_Permutation; Piauto.
      * destruct H9.
        apply No_FVars_Parallel in H10.
        destruct H10 as [HA HB].
        unfold not.
        intros.
        apply Close_FVars_Beq in H10; Piauto.
        apply -> FVars_Res in H10.
        apply Close_FVars_Beq in H10; Piauto.
        simpl in H10.
        destruct H10.
        ++ destruct H10; try contradiction.
           apply FVars_Open_Beq in H10; Piauto.
           simpl in HA.
           apply No_Union_No_Each in HA.
           destruct HA; contradiction.
        ++ simpl in HB.
           apply No_Union_No_Each in HB.
           destruct HB.
           contradiction.*)
Admitted.
#[global]
Hint Resolve FVars_Reduction_Neg : Piull.


Lemma Reduction_Cut_One :
forall (P Q Q0 : Process)(u x : nat),
lc Q -> 
((ν Close u ((FName u !· Close x P) ↓ Q)) --> Q0) -> (exists ( y : nat), Q = [FName u ←→ FName y]) \/ (exists ( y : nat), Q = [FName y ←→ FName u]).
Proof.
  intros.
  inversions H0.
  + assert ( HA : [if x0 =? x0 then BName 0 else FName x0
     ←→ if y =? x0 then BName 0 else FName y] = Close_Rec 0 x0 ([FName x0 ←→ FName y]) ); Piauto.
    rewrite HA in H2.
    inversions H6.
    specialize (H7 u (Close x0 P0)).
    assert (Hx : u = x0); Piauto.
    rewrite <- Hx in *.
    assert (Ht : lca 0 ([FName x0 ←→ FName y])); Piauto.
    left.
    exists y.
    apply (Close_Same_Inv _ _ u 0); Piauto.
  + assert ( HA : [if y =? x0 then BName 0 else FName y
     ←→ if x0 =? x0 then BName 0 else FName x0] = Close_Rec 0 x0 ([FName y ←→ FName x0]) ); Piauto.
    rewrite HA in H2.
    inversions H6.
    specialize (H7 u (Close x0 P0)).
    assert (Hx : u = x0); Piauto.
    rewrite <- Hx in *.
    assert (Ht : lca 0 ([FName y ←→ FName x0])); Piauto.
    right.
    exists y.
    apply (Close_Same_Inv _ _ u 0); Piauto.
Qed.


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
    rewrite (Double_Subst_Expan_NFVar Q x x u); Piauto.
    constructor; Piauto.
    apply (ProcessReduction_WD P _ ); Piauto.
    
    admit. admit. admit.
    admit. admit. admit.
    apply (FVars_Reduction_Neg ({x \ u} P) _ _ ); Piauto.
  + assert (Hx := H6).
    apply (Subst_Reduction_NBeq ({x \ u} P) Q x u) in H6; Piauto.
    rewrite <- Double_Subst_Expan_NFVar in H6; Piauto.
    rewrite Subst_By_Equal in H6.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u); Piauto.
    constructor; Piauto.
    apply (ProcessReduction_WD P _ ); Piauto.
    apply (FVars_Reduction_Neg ({x \ u} P) _ _ ); Piauto.
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
  + apply Output_No_Reduces in H4; contradiction.
  + apply Output_No_Reduces in H4; contradiction.
  + specialize (Reduction_Cut_One _ _ _ _ _ H3 H8) as Hx.
    destruct Hx.
    - destruct H9.
      rewrite H9 in H6.
      admit.
    - admit.
  + admit.
  + inversions H8.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  + inversions H8.
Admitted.



Lemma No_Typing_Fuse_One :
forall (A : Proposition)(D F G : list Assignment)(u x0 : nat),
forall u0 : nat, (((FName u0 : A) :: nil) ++ D);;; F !- [FName u ←→ FName x0] ::: G
  -> False.
Proof.
  intros.
  inversions H.
  + admit.
  + admit.
  + 
    
Admitted.


(* Lemma Well_Collected_Reduction :
forall ( D : list Assignment )( P Q : Process)( u x : nat ),
Well_Collected D P -> P --> ({u \ x} Q) ->
Well_Collected D ({u \ x} Q).
Proof.
  intros.
  inversions H. *)


Search FVars.

(** FVars_Close_NotIn
*)
Lemma FVars_Reduction :
forall ( P Q : Process )( x : nat),
x ∈ FVars P -> P --> Q -> x ∈ FVars Q.
Proof.
  intros.
  induction H0.
  + DecidSimple x x0.
    - apply beq_nat_true in e.
      subst.
      apply NFVar_Close in H.
      contradiction.
    - apply beq_nat_false in n.
      specialize (Close_FVars_Beq (P ↓ ([FName x0 ←→ FName y])) x x0 0 n H) as Hx.
      simpl in Hx.
      destruct Hx.
      * admit.
      * 
      
      specialize (Close_FVars_Beq 
      
  



