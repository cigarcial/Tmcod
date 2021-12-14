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
From Coq Require Import Sets.Powerset_facts.

From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Defs_Proposition.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Context.
From Tmcod Require Import Defs_Typing.
From Tmcod Require Import Facts_Names.
From Tmcod Require Import Facts_FVars.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Facts_MOpen.
From Tmcod Require Import Props_Process.
From Tmcod Require Import Props_Propositions.
From Tmcod Require Import Facts_WSubst.


(**
*)
Lemma Subst_Change_Side :
forall ( x u : nat )( P Q : Process ),
~ x ∈ FVars P -> {x \ u} P = Q -> P = {u \ x} Q.
Proof.
  intros.
  apply (Equality_Subst_Equality _ _ u x) in H0.
  rewrite <- Double_Subst_Expan_NFVar in H0; Piauto.
  rewrite Subst_By_Equal in H0.
  auto.
Qed.
#[global]
Hint Resolve Subst_Change_Side : Piull.


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
    try apply (Equality_Subst_Equality _ _ u x0) in x;
    try rewrite <- (Double_Subst_Expan_NFVar _ u u x0) in x;
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
    try apply (Equality_Subst_Equality _ _ u x0) in x;
    try rewrite <- (Double_Subst_Expan_NFVar _ u u x0) in x;
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
    try apply (Equality_Subst_Equality _ _ u x0) in x;
    try rewrite <- (Double_Subst_Expan_NFVar _ u u x0) in x;
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
Collect L ->  Collect ( (Bld u A) ∪ L ).
Proof.
  intros.
  constructor.
  intros.
  apply Union_inv in H1.
  destruct H1.
  + apply Singleton_inv in H1.
    rewrite <- H1.
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
Admitted.
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

Ltac AndSearch H :=
  (progress auto with *) +
  (destruct H as [? H]; AndSearch H).


(**
*)
Lemma Weakening_Well_Collected :
forall ( D F G : Context )( A : Proposition )( P : Process )( u : nat ),
Good_Contexts D F G P -> Fresh u (D ∪ F ∪ G)  -> Good_Contexts ( (Bld u A) ∪ D) F G P.
Proof.
  intros.
  inversions H.
  constructor.
  
  constructor.
  intros.
  destruct H1.
  specialize (H1 x H2).
  destruct H1.
  exists x0.
  destruct H1; try OrSearch.
  destruct H1; try OrSearch.

  constructor.
  constructor.
  unfold not.
  intros.
  destruct H2.
  apply Union_inv in H2.
  destruct H2.
   inversions H2.
    inversions H0.
    specialize (H4 x B).
    apply H4; Piauto.
    OrSearch.
   destruct H1.
    destruct H4.
    inversions H4.
    specialize (H6 x A0 B).
    auto.
  
  constructor.
  admit.
  
  constructor; AndSearch H1.
Admitted.
#[global]
Hint Resolve Weakening_Well_Collected : Piull.


(**
*)
Lemma Weakening_Ordinary :
forall ( D F G : Context )( A : Proposition )( P : Process )( u y: nat ),
( D ;;; F !- P ::: G ) ->
( ((Bld u A) ∪ D) ;;; F !- P ::: G ).
Proof.
Admitted.
#[global]
Hint Resolve Weakening_Ordinary : Piull.



(**
*)
Lemma No_Typing_Fuse_One_Lf :
forall ( A : Proposition )( x y : nat  )( D F G : Context ),
( (FName x : A) ∈ D ) -> ~( D ;;; F !- ([FName x ←→ FName  y]) ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H0.
  + admit. (* hay contextos no disyuntos *)
  + admit. (* hay contextos no disyuntos *)
  + apply Subst_Change_Side in x; Piauto.
    simpl in x.
    DecidSimple x1 x0.
    - admit. (* hay contextos no disyuntos *)
    - rewrite n in x.
      DecidSimple y x0.
      * rewrite e in x.
        apply (IHInference x1 u); ePiauto.
      * rewrite n0 in x.
        apply (IHInference x1 y); ePiauto.
Admitted.
#[global]
Hint Resolve No_Typing_Fuse_One_Lf : Piull.


(**
*)
Lemma No_Typing_Fuse_One_Rg :
forall ( A : Proposition )( x y : nat  )( D F G : Context ),
( (FName x : A) ∈ D ) -> ~( D ;;; F !- ([FName y ←→ FName  x]) ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H0.
  + admit. (* hay contextos no disyuntos *)
  + admit. (* hay contextos no disyuntos *)
  + apply Subst_Change_Side in x.
    simpl in x.
    DecidSimple x1 x0.
    - admit. (* hay contextos no disyuntos *)
    - rewrite n in x.
      DecidSimple y x0.
      * rewrite e in x.
        apply (IHInference x1 u); ePiauto.
      * rewrite n0 in x.
        apply (IHInference x1 y); ePiauto.
Admitted.
#[global]
Hint Resolve No_Typing_Fuse_One_Rg : Piull.


(**
*)
Lemma No_Typing_Zero_Ord :
forall ( A : Proposition )( x y : nat  )( D F G : Context ),
( (FName x : A) ∈ D ) -> ~( D ;;; F !- ( FName x ·θ ) ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H0.
  + apply Subst_Change_Side in x; Piauto.
    simpl in x.
    DecidSimple x1 x0.
    - admit. (* hay contextos no disyuntos *)
    - rewrite n in x.
      apply (IHInference x1); ePiauto.
  + apply Subst_Change_Side in x; Piauto.
    simpl in x.
    DecidSimple x1 x0.
    - admit. (* hay contextos no disyuntos *)
    - rewrite n in x.
      apply (IHInference x1); ePiauto.
(*   + inversions H1.
    destruct H3.
    inversions H3.
    apply (H5 x A ⊥); Piauto.
    constructor; Piauto.
    simpl.
    OrSearch.
  + admit. (* hay contextos no disyuntos *) *)
Admitted.
#[global]
Hint Resolve No_Typing_Zero_Ord : Piull.














(**
*)
Lemma GContext_Three_Linear :
forall (D F G : Context)(P : Process),
Good_Contexts D F G P -> Linear G.
Proof.
  intros.
  inversions H.
  destruct H0.
  AndSearch H1.
Qed.
#[global]
Hint Resolve GContext_Three_Linear : Piull.


(**
*)
Lemma In_Union_Linear :
forall (G : Context)(x y : nat)(A B : Proposition),
Linear G -> Fresh x G ->
(FName y : B) ∈ (Bld x A ∪ G) -> 
( (FName y : B) = (FName x : A) /\ ~ ( (FName y : B) ∈ G ) \/
  (y <> x /\ ( (FName y : B) ∈ G ) )).
Proof.
  intros.
  apply Union_inv in H1.
  destruct H1.
  + left.
    inversions H1.
    constructor; Piauto.
    unfold not.
    intros.
    inversions H0.
    specialize (H3 y B H2); Piauto.
  + right.
    constructor; Piauto.
    unfold not.
    intros.
    inversions H2.
    inversions H0.
    specialize (H2 x B H1); Piauto.
Qed.
#[global]
Hint Resolve In_Union_Linear : Piull.


(**
*)
Lemma SMA_Nin_Context :
forall (G : Context)(x : nat)(A : Proposition),
~((FName x : A) ∈ G) -> SMA G x A = G.
Proof.
Admitted.
#[global]
Hint Resolve SMA_Nin_Context : Piull.


Lemma SMA_Union :
forall (D F : Context)(x : nat)(A : Proposition),
(SMA (D ∪ F) x A) = ((SMA D x A) ∪ (SMA F x A)).
Proof.
  intros.
  apply Extensionality_Ensembles.
  constructor.
  + unfold Included.
    intros.
    inversions H.
    apply Union_inv in H0.
    destruct H0.
    - left.
      constructor; Piauto.
    - right.
      constructor; Piauto.
  + unfold Included.
    intros.
    apply Union_inv in H.
    destruct H.
    - inversions H.
      constructor; try OrSearch; Piauto.
    - inversions H.
      constructor; try OrSearch; Piauto.
Qed.
#[global]
Hint Resolve SMA_Union : Piull.



(**
*)
Lemma Neq_Nbld :
forall (x y : nat)(A B : Proposition),
x <> y -> ~ (FName x : A) ∈ Bld y B.
Proof.
  unfold not.
  intros.
  inversions H0.
  contradiction.
Qed.
#[global]
Hint Resolve Neq_Nbld : Piull.



(*
Lemma Typing_Change_Side_RgLf :
forall ( P : Process)(D F G : Context),
D;;; F !- P ::: G -> 
forall (x : nat)(A : Proposition), ( (FName x : A) ∈ G ) ->
D;;; (F ∪ Bld x (A ^⊥)) !- P ::: (SMA G x A).
Proof.
  intros.
  dependent induction H.
  + inversions H2.
    rewrite SMA_Elimination.
    constructor; Piauto.
    admit.
  + inversions H2.
  + inversions H6.
    rewrite SMA_Elimination.
    rewrite <- App_Nil_Right in *.
    simpl.
    constructor; Piauto.
    admit.
    admit.
    rewrite <- (SMA_Elimination y A).
    rewrite (App_Nil_Right (Bld y (A ^⊥))) in *.
    apply IHInference; ePiauto.
    constructor.
  + rewrite Union_associative.
    constructor; Piauto.
    rewrite Union_commutative; Piauto.
    admit.
    admit.
    admit.
  + apply In_Union_Linear in H12; ePiauto.
    destruct H12.
    - destruct H12.
      inversions H12.
      rewrite SMA_Union_In.
      simpl.
      rewrite Doble_Duality_ULLT.
      rewrite Union_commutative.
      constructor; Piauto.
      admit.
      admit.
      rewrite SMA_Nin_Context; Piauto.
      rewrite SMA_Nin_Context; Piauto.
    - destruct H12.
      rewrite SMA_Union.
      rewrite (SMA_Nin_Context _ x0 A0).
      constructor; Piauto.
      admit.
      admit.
      admit.
      admit.
      apply Neq_Nbld; Piauto.
  + inversions H6.
  + apply In_Union_Linear in H7; ePiauto.
    destruct H7.
    - destruct H7.
      inversions H7.
      rewrite SMA_Union_In.
      simpl.
      rewrite Doble_Duality_ULLT.
      rewrite Union_commutative.
      admit.
    - destruct H7.
      rewrite SMA_Union.
      rewrite (SMA_Nin_Context _ x0 A0).
      constructor; Piauto.
      admit.
      admit.
      admit.
      admit.
      apply Neq_Nbld; Piauto.
    - admit.
    - admit.
  + apply Union_inv in H11.
    destruct H11.
    - inversions H7.
      rewrite SMA_Union_In.
      simpl.
      rewrite Doble_Duality_ULLT.
      rewrite Union_commutative.
      admit.
    - destruct H7.
      rewrite SMA_Union.
      rewrite (SMA_Nin_Context _ x0 A0).
      constructor; Piauto.
      admit.
      admit.
      admit.
      admit.
      apply Neq_Nbld; Piauto.
    - admit.
    - admit.
    
Admitted.
#[global]
Hint Resolve Typing_Change_Side_RgLf : Piull.
*)














