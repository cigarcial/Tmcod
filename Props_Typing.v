(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
Require Import Coq.Program.Equality.

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Sets.Constructive_sets.

From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Proposition.
From Tmcod Require Import Defs_Typing.

From Tmcod Require Import Facts_Names.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Facts_FVars.

From Tmcod Require Import Facts_MOpen.
From Tmcod Require Import Props_Process.
From Tmcod Require Import Facts_WSubst.



Lemma Fuse_No_Reduces :
forall (x y : Name)(Q : Process), 
~([x ←→  y] --> Q ).
Proof.
  unfold not.
  intros.
  inversions H.
  inversions H1.
Qed.


Lemma Rep_Input_No_Reduces :
forall (x: Name)(y : nat)(P Q : Process),
~((x !· Close y P) --> Q).
Proof.
  unfold not.
  intros.
  inversions H.
  inversions H1.
Qed.


Lemma Chan_Close_No_Reduces :
forall (x : Name)(P Q : Process),
~((x ()·P) --> Q).
Proof.
  unfold not.
  intros.
  inversions H.
  inversions H1.
Qed.


Lemma Zero_No_Reduces :
forall (x : Name)(Q : Process), 
~((x ·θ) --> Q).
Proof.
  unfold not.
  intros.
  inversions H.
  inversions H1.
Qed.




Lemma Chan_Input_No_Reduces :
forall (x : Name)(y : nat)(P Q : Process),
~( (x · Close y P) --> Q ).
Proof.
  unfold not.
  intros.
  inversions H.
  inversions H1.
Qed.


Lemma Parallel_Res_No_Reduces :
forall (x : Name)(y : nat)(P Q Q0 : Process),
~( (ν Close y (x « FName y »· (P ↓ Q))) --> Q0 ).
Proof.
  unfold not.
  intros.
  inversions H.
Admitted.


Lemma Output_No_Reduces :
forall (u x: nat)(P Q : Process),
~( (ν Close x (FName u « FName x »· P)) --> Q ).
Proof.
  unfold not.
  intros.
  inversions H.
Admitted.

Lemma Close_Inv :
forall ( P Q : Process )( x y i : nat ),
Close_Rec i x P = Close_Rec i y Q -> P = { x \ y } Q.
Proof.
  induction P; intros; unfold Close in H; simpl; auto.
  + destruct Q; try discriminate.
    simpl; auto.
  + destruct Q; try discriminate.
    simpl in H.
    simpl.
    inversions H.
    (* error hay que pedir condiciones de x en Q *)
    admit.
  + destruct Q; try discriminate.
    simpl.
    simpl in H.
    inversions H.
    rewrite (IHP1 Q1 x y i); auto.
    rewrite (IHP2 Q2 x y i); auto.
  + destruct Q; try discriminate.
    simpl in H.
    inversions H.
    simpl.
    admit.
  + admit.
  + admit.
  + destruct Q; try discriminate.
    simpl in H.
    inversions H.
    simpl.
    rewrite (IHP Q x y (S i)); auto.
Admitted.



Lemma Close_Inv_Names :
forall (x x1 : Name)(i x0 y0 : nat),
Close_Name i x0 x = Close_Name i y0 x1 -> x = Subst_Name y0 x0 x1.
Proof.
  intros.
  destruct x.
  + admit.
  + destruct x1.
    - simpl in H.
      EasyDec x y0 e n.
      * rewrite e in H.
        rewrite e.
    - simpl in H.
      simpl.
      rewrite H; auto.
      
  
  
(*
Teorema 2.1 del artículo.
*)
Theorem Soundness : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P --> Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros P D F G H.
  dependent induction H; intros.
  + apply Fuse_No_Reduces in H2; contradiction.
  + apply Fuse_No_Reduces in H2; contradiction.
  + apply Rep_Input_No_Reduces in H3; contradiction.
  + assert (H6 := H5).
    inversions H3.
    specialize (Lc_WSubst_Subst_WSubst P u x H2 H3) as Hp.
    specialize (Well_Subst_Red_Well_Subst ({x \ u} P) Q x u Hp H6) as Hx.
    inversions Hx; auto.
    apply (Well_Subst_Reduction_Susbt ({x \ u} P) Q x u)  in H5; auto.
    rewrite <- Double_Subst_Expan_NFVar in H5; auto.
    rewrite Subst_By_Equal in H5.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u); auto.
    constructor; auto.
    apply (ProcessReduction_WD P _ ); auto.
    apply Lc_WSubst_Subst_WSubst; auto.
    apply (ProcessReduction_WD ({x \ u} P) _ ); auto.
    apply Subst_Lc_Lc; auto.
    apply Subst_Lc_Lc; auto.
  + assert (H6 := H5).
    inversions H3.
    specialize (Lc_WSubst_Subst_WSubst P u x H2 H3) as Hp.
    specialize (Well_Subst_Red_Well_Subst ({x \ u} P) Q x u Hp H6) as Hx.
    inversions Hx; auto.
    apply (Well_Subst_Reduction_Susbt ({x \ u} P) Q x u)  in H5; auto.
    rewrite <- Double_Subst_Expan_NFVar in H5; auto.
    rewrite Subst_By_Equal in H5.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u); auto.
    constructor; auto.
    apply (ProcessReduction_WD P _ ); auto.
    apply Lc_WSubst_Subst_WSubst; auto.
    apply (ProcessReduction_WD ({x \ u} P) _ ); auto.
    apply Subst_Lc_Lc; auto.
    apply Subst_Lc_Lc; auto.
  + apply Rep_Input_No_Reduces in H3; contradiction.
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + admit.
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + admit.
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + admit.
  + apply Chan_Close_No_Reduces in H5; contradiction.
  + apply Zero_No_Reduces in H1; contradiction.
  + apply Chan_Close_No_Reduces in H5; contradiction.
  + apply Zero_No_Reduces in H1; contradiction.
  + admit.
  + admit.
Admitted.


















