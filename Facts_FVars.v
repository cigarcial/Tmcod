(*
  Ciro Iván García López
  Tesis de Maestría - Master Thesis
  Session Type Systems Verification
  Unam - 2021
*)
From Coq Require Import Ensembles.
From Coq Require Import Finite_sets.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.

From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Tactics.

(*
*)
Lemma No_Union_No_Each : 
forall (x : nat)( X Y : FVarsE ),
~(x ∈ (X ∪ Y)) -> ~(x ∈ X) /\ ~(x ∈ Y).
Proof.
Admitted.


(*
*)
Lemma FVars_Name_Finite :
forall (x : Name),
Finite _ (FVars_Name x).
Proof.
  destruct x.
  + simpl. apply Singleton_is_finite.
  + simpl. constructor.
Qed.


(*
*)
Lemma FVars_Finite :
forall (P : Process),
Finite _ (FVars P).
Proof.
  induction P.
  + simpl.
    constructor.
  + simpl. apply Union_preserves_Finite; apply FVars_Name_Finite.
  + simpl. apply Union_preserves_Finite; auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + simpl. apply FVars_Name_Finite.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
Qed.


(*
*)
Lemma There_Is_A_Name :
forall ( P : Process ),
exists ( x : nat ), ~ ( x ∈ (FVars P) ).
Proof.
Admitted.


(*
*)
Lemma FVars_Name_No_Close :
forall (z k : nat)(x : Name),
~ (z ∈ FVars_Name x) -> (Close_Name k z x = x).
Proof.
  unfold not.
  intros.
  destruct x.
  + destruct (bool_dec (x =? z) true).
    - simpl in H. apply Nat.eqb_eq in e.
      rewrite e in H.
      assert ( HB : z ∈ Singleton nat z).
      { unfold In. constructor. }
      contradiction.
    - simpl. apply not_true_iff_false in n.
      rewrite n. auto.
  + auto.
Qed.


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