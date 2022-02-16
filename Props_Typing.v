(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021

  This file contains the basic facts concerning names.
*)

Require Import Coq.Program.Equality.
From Coq Require Import Lists.List.
Import ListNotations.


From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Sets.Constructive_sets.
From Coq Require Import Sets.Powerset_facts.

From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Defs_Proposition.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Typing.
From Tmcod Require Import Defs_Context.
From Tmcod Require Import Facts_Names.
From Tmcod Require Import Facts_FVars.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Facts_MOpen.
From Tmcod Require Import Props_Process.
From Tmcod Require Import Facts_WSubst.
From Tmcod Require Import Facts_Typing.
From Tmcod Require Import Props_Propositions.


(**
*)
Theorem Congruence_Reduction : 
forall ( P : Process )( D F G : Context ),
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
Lemma Well_Collected_Reduction :
forall ( D G F : Context )( P Q : Process)( u x : nat ),
Good_Contexts D G F P -> P --> ({u \ x} Q) ->
Good_Contexts D G F ({u \ x} Q).
Proof.
  constructor.
  inversions H.
  destruct H1.
  constructor.
    intros.
    specialize (H1 x0).
    apply H1; ePiauto.
  auto.
Qed.
#[global]
Hint Resolve Well_Collected_Reduction : Piull.


(**
*)
Lemma Setminus_Nin :
forall (D : Context)(u : nat)(A : Proposition),
~ ( (FName u:A) ∈ D ) ->
(Setminus Assignment D (Bld u A)) = D.
Proof.
  intros.
  apply Extensionality_Ensembles.
  constructor; try unfold Included.
  + intros.
    inversions H0.
    auto.
  + intros.
    constructor; auto.
    unfold not.
    intros.
    inversions H1.
    Piauto.
Qed.
#[global]
Hint Resolve Setminus_Nin : Piull.


(**
*)
Lemma Replace_Bld_Beq :
forall (u x y : nat)(A B: Proposition),
u <> y ->
Replace (Bld y B) u x A = (Bld y B ∪ Bld x A).
Proof.
  intros.
  unfold Replace.
  rewrite Setminus_Nin; Piauto.
Qed.
#[global]
Hint Resolve Replace_Bld_Beq : Piull.


(**
*)
Lemma No_Disjoint_Context_Left :
forall ( x : nat )( A B : Proposition )( D F G : Context )( P : Process), 
Good_Contexts (Bld x A ∪ D) (Bld x B ∪ F) G P -> False.
Proof.
  intros.
  inversions H.
  destruct H0.
  destruct H1.
  inversions H1.
  apply (H3 x A B).
  constructor;
  left; constructor.
Qed.
#[global]
Hint Resolve No_Disjoint_Context_Left : Piull.


(**
*)
Lemma No_Disjoint_Context_Right :
forall ( x : nat )( A B : Proposition )( D F G : Context )( P : Process), 
Good_Contexts (Bld x A ∪ D) F (Bld x B ∪ G) P -> False.
Proof.
  intros.
  inversions H.
  destruct H0.
  destruct H1.
  destruct H2.
  inversions H2.
  apply (H4 x A B).
  constructor;
  left; constructor.
Qed.
#[global]
Hint Resolve No_Disjoint_Context_Right : Piull.


(**
*)
Lemma Equality_Substitution_Beq_Left :
forall ( u1 u0 x y : nat),
u0 <> y -> 
(if u1 =? x then BName 0 else FName u1) = (if u0 =? y then BName 0 else FName u0) -> u1 = u0.
Proof.
  intros.
  DecidSimple u0 y.
  rewrite n in H0.
  DecidSimple u1 x.
  + rewrite e in H0;
    inversions H0.
  + rewrite n0 in H0;
    inversions H0.
    Piauto.
Qed.
#[global]
Hint Resolve Equality_Substitution_Beq_Left : Piull.


(**
*)
Lemma Injective_Bld :
forall ( x : nat )( A : Proposition ),
Injective (Bld x A ∪ ø).
Proof.
  constructor.
  unfold not.
  intros.
  destruct H as [Ha [Hb Hc]].
  rewrite <- App_Nil_Left in Hb.
  rewrite <- App_Nil_Left in Hc.
  apply Ha.
  inversions Hb.
  inversions Hc.
  Piauto.
Qed.
#[global]
Hint Resolve Injective_Bld : Piull.


(**
*)
Lemma No_Disjoint_Context_Left_Right :
forall ( x : nat )( A B : Proposition )( D F G : Context )( P : Process), 
Good_Contexts D (Bld x A ∪ F) (Bld x B ∪ G) P -> False.
Proof.
  intros.
  inversions H.
  destruct H0 as [Ha [Hb [Hc [Hd He]]]].
  inversions Hd.
  apply (H0 x A B).
  constructor; OrSearchCons.
Qed.
#[global]
Hint Resolve No_Disjoint_Context_Left_Right : Piull.


(**
*)
Lemma Equality_Context :
forall ( x : nat )( A B : Proposition)( D F : Context),
Injective (Bld x A ∪ D) -> 
(Bld x A ∪ D) = (Bld x B ∪ F) -> (A = B /\ D = F).
Proof.
  intros.
  constructor.
  + apply Extension in H0.
    inversions H0.
    assert (HA : (FName x:A) ∈ (Bld x A ∪ D)).
      left.
      constructor.
    assert (HB : (FName x:B) ∈ (Bld x A ∪ D)).
      assert (HC : (FName x:B) ∈ (Bld x B ∪ F)).
        left.
        constructor.
      unfold Included in *.
      apply H2; Piauto.
    inversions H.
    specialize (Decid_Propositions A B) as Ha.
    destruct Ha; Piauto.
    exfalso.
    apply (H3 x A B).
    constructor; Piauto.
  + (* set minus and the Injective of the sets complete the proof *)
Admitted.
#[global]
Hint Resolve Equality_Context : Piull.


Proposition Type_Subst_Lf :
forall ( P : Process )( D F G : Context ),
( D ;;; F !- P ::: G ) ->
forall ( w z : nat )( A : Proposition ), (FName z : A) ∈ F -> 
( D ;;; (Replace F z w A) !- {w \ z}P ::: G ).
Proof.
Admitted.


(**
*)
Proposition Type_Subst_Rg :
forall ( P : Process )( D F G : Context ),
( D ;;; F !- P ::: G ) ->
forall ( w z : nat )( A : Proposition ), (FName z : A) ∈ G -> 
( D ;;; F !- {w \ z}P ::: (Replace G z w A) ).
Proof.
Admitted.


(**
*)
Lemma Transference_Rg_Lf :
forall ( P : Process)(D F G : Context),
D;;; F !- P ::: G -> 
forall (x : nat)(A : Proposition), ( (FName x : A) ∈ G ) ->
D;;; (F ∪ Bld x (A ^⊥)) !- P ::: (SMA G x A).
Proof.
Admitted.


(**
*)
Lemma Transference_Lf_Rg :
forall ( P : Process)(D F G : Context),
D;;; F !- P ::: G -> 
forall (x : nat)(A : Proposition), ( (FName x : A) ∈ F ) ->
D;;; (SMA F x A) !- P ::: (G ∪ Bld x (A ^⊥)).
Proof.
Admitted.


(**
*)
Lemma Replace_Union_Bld :
forall ( F : Context )( x y : nat )( A : Proposition),
Replace (Bld x A ∪ F) x y A = (Bld y A ∪ F).
Proof.
Admitted.
#[global]
Hint Resolve Replace_Union_Bld : Piull.


(**
*)
Lemma SMA_Union_Bld :
forall ( G : Context )( x : nat )( A : Proposition),
SMA (Bld x A ∪ G) x A = G .
Proof.
Admitted.
#[global]
Hint Resolve SMA_Union_Bld : Piull.




(**
*)
Theorem Soundness : 
forall (P : Process)(D F G : Context),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P --> Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros P D F G H.
  dependent induction H; intros.
  + apply Fuse_No_Reduces in H2; contradiction.
  + apply Fuse_No_Reduces in H2; contradiction.
  + apply Rep_Input_No_Reduces in H6; contradiction.
  (* + assert (Hx := H12).
    apply (Subst_Reduction_NBeq ({x \ u} P) Q x u) in H12; Piauto.
    rewrite <- Double_Subst_Expan_NFVar in H12; Piauto.
    rewrite Subst_By_Equal in H12.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u); ePiauto.
    constructor; ePiauto.
  + assert (Hx := H12).
    apply (Subst_Reduction_NBeq ({x \ u} P) Q x u) in H12; Piauto.
    rewrite <- Double_Subst_Expan_NFVar in H12; Piauto.
    rewrite Subst_By_Equal in H12.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u); ePiauto.
    constructor; ePiauto.
  + apply Rep_Input_No_Reduces in H6; contradiction.
  + apply Chan_Input_No_Reduces in H7; contradiction.
  + apply Parallel_Res_No_Reduces in H11; contradiction.
  + apply Chan_Input_No_Reduces in H6; contradiction.
  + apply Parallel_Res_No_Reduces in H11; contradiction.
  + apply Chan_Input_No_Reduces in H7; contradiction.
  + apply Parallel_Res_No_Reduces in H12; contradiction.
  + apply Chan_Close_No_Reduces in H6; contradiction.
  + apply Zero_No_Reduces in H1; contradiction.
  + apply Chan_Close_No_Reduces in H6; contradiction.
  + apply Zero_No_Reduces in H1; contradiction.
  + apply Output_No_Reduces in H7; contradiction.
  + apply Output_No_Reduces in H7; contradiction. *)
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + inversions H9.
    - apply (IsClosingInj_inv _ _ u) in H15.
      rewrite <- H15 in *.
      assert ( Hx : [if u =? u then BName 0 else FName u ←→ if y =? u then BName 0 else FName y] = Close_Rec 0 u ([FName u ←→ FName y]) ). Piauto.
      rewrite Hx in H11.
      apply (Close_Same_Inv _ _ u 0) in H11; Piauto.
      rewrite <- H11 in *.
      apply (No_Typing_Fuse_One_Lf A _ _ _ _ ) in H8; try OrSearch.
      unfold Bld; OrSearch.

    - apply (IsClosingInj_inv _ _ u) in H15.
      rewrite <- H15 in *.
      assert ( Hx : [if y =? u then BName 0 else FName y ←→ if u =? u then BName 0 else FName u] = Close_Rec 0 u ([FName y ←→ FName u]) ). Piauto.
      rewrite Hx in H11.
      apply (Close_Same_Inv _ _ u 0) in H11; Piauto.
      rewrite <- H11 in *.
      apply (No_Typing_Fuse_One_Rg A _ _ _ _ _) in H8; try OrSearch.
      unfold Bld. OrSearch.

    - apply (IsClosingInj_inv _ _ u) in H21.
      rewrite <- H21 in *.
      assert ( Hx : ν (Close_Name 1 u (if u =? y then BName 0 else FName u)
         « Close_Name 1 u (if y =? y then BName 0 else FName y)
         »· Close_Rec 1 u (Close_Rec 0 y Q1)) = Close_Rec 0 u (ν Close_Rec 0 y ( (FName u
         « FName y
         »· Q1) ))). Piauto.
      rewrite Hx in H12.
      apply (Close_Same_Inv _ _ u 0) in H12; Piauto.
      apply (Close_Same_Inv _ _ u 1) in H11; Piauto.
      rewrite H11.
      clear Hx; clear H10; clear IHInference1.
      subst.
      apply (cutrep _ _ _ _ _ A x u0); Piauto.
      admit.

      inversions H8.
      * admit. (* cyclic argument *)
      * admit. (* cyclic argument *)
      
      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H29.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H29.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply No_Disjoint_Context_Right in H30.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H22.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H12; Piauto.
        subst.
        rewrite (App_Nil_Left F).
        rewrite (App_Nil_Left G).
        apply (cutl (Bld u0 A0 ∪ D0) F G ø ø _ _  A0 y); Piauto.
        admit.
        
        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x (A0 ^⊥)) x y (A0 ^⊥) = (Bld y (A0 ^⊥) ∪ ø) ).
          rewrite Replace_Bld.
          ePiauto.

        rewrite <- Ht.
        apply Type_Subst_Lf; try constructor.
        assert( Hx : SMA (Bld x A0) x A0 = ø );
          ePiauto.
        apply Equality_Context in H20; ePiauto.
        destruct H20.
        subst.
        rewrite <- Hx.
        rewrite (App_Nil_Right (Bld x (A ^⊥))).
        apply Transference_Rg_Lf; ePiauto.
        constructor.

      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H22.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H12; Piauto.
        subst.
        rewrite (App_Nil_Left F).
        rewrite (App_Nil_Left G).
        apply (cutl (Bld u0 A0 ∪ D0) F G ø ø _ _  A0 y); Piauto.
        admit.
        admit.

        rewrite <- (Doble_Duality_ULLT A0) at 2.
        assert ( Ha : G = SMA (Bld y (A0 ^⊥) ∪ G) y (A0 ^⊥)).
          apply eq_sym.
          Piauto.
        rewrite Ha.
        rewrite (Union_commutative _ ( Bld y ((A0 ^⊥) ^⊥) ) F).
        apply Transference_Rg_Lf; try OrSearchCons; Piauto.

        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x (A0 ^⊥)) x y (A0 ^⊥) = (Bld y (A0 ^⊥) ∪ ø) ).
          rewrite Replace_Bld.
          ePiauto.

        rewrite <- Ht.
        apply Type_Subst_Lf; try constructor.
        assert( Hx : SMA (Bld x A0) x A0 = ø );
          ePiauto.
        apply Equality_Context in H20; ePiauto.
        destruct H20.
        subst.
        rewrite <- Hx.
        rewrite (App_Nil_Right (Bld x (A ^⊥))).
        apply Transference_Rg_Lf; try OrSearchCons; ePiauto.

    - apply (IsClosingInj_inv _ _ u) in H21.
      rewrite <- H21 in *.
      assert ( Hx : ν (Close_Name 1 u (if u =? y then BName 0 else FName u)
         « Close_Name 1 u (if y =? y then BName 0 else FName y)
         »· Close_Rec 1 u (Close_Rec 0 y Q1)) = Close_Rec 0 u (ν Close_Rec 0 y ( (FName u
         « FName y
         »· Q1) ))). Piauto.
      rewrite Hx in H12.
      apply (Close_Same_Inv _ _ u 0) in H12; Piauto.
      apply (Close_Same_Inv _ _ u 1) in H11; Piauto.
      rewrite H11.
      apply (cutrep _ _ _ _ _ A x u); Piauto.
      admit.

      rewrite <- H12 in H8.
      inversions H8.
      * admit. (* cyclic argument *)
      * admit. (* cyclic argument *)

      * apply Equality_Substitution_Beq_Left in H20; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H33.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H20; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H33.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H20; Piauto.
        subst.
        apply No_Disjoint_Context_Right in H34.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H20; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H22.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H24; Piauto.
        subst.
        rewrite (App_Nil_Right F).
        rewrite (App_Nil_Right G).
        apply (cutr (Bld u0 A0 ∪ D0) ø ø F G _ _  A0 y); Piauto.
        admit.
        
        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x A0) x y A0 = (Bld y A0 ∪ ø) ). 
          rewrite Replace_Bld.
          ePiauto.
        rewrite <- Ht.
        apply Type_Subst_Rg; try OrSearchCons; Piauto.
        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        Piauto.

      * apply Equality_Substitution_Beq_Left in H20; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H22.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H24; Piauto.
        subst.
        rewrite (App_Nil_Right F).
        rewrite (App_Nil_Right G).
        apply (cutr (Bld u0 A0 ∪ D0) ø ø F G _ _  A0 y); Piauto.
        admit.
        admit.

        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x A0) x y A0 = (Bld y A0 ∪ ø) ). 
          rewrite Replace_Bld.
          ePiauto.
        rewrite <- Ht.
        apply Type_Subst_Rg; try OrSearchCons; Piauto.
        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        Piauto.

        assert( Ha : SMA (Bld y (A0 ^⊥) ∪ G) y (A0 ^⊥) = G ); Piauto.
        rewrite <- Ha.
        rewrite (Union_commutative _ _ F).
        rewrite <- Doble_Duality_ULLT at 2.
        apply Transference_Rg_Lf; try OrSearchCons; ePiauto.

  + inversions H10.
    - apply (IsClosingInj_inv _ _ u) in H16.
      rewrite <- H16 in *.
      assert ( Hx : [if u =? u then BName 0 else FName u ←→ if y =? u then BName 0 else FName y] = Close_Rec 0 u ([FName u ←→ FName y]) ). Piauto.
      rewrite Hx in H12.
      apply (Close_Same_Inv _ _ u 0) in H12; Piauto.
      rewrite <- H12 in *.
      apply (No_Typing_Fuse_One_Lf A _ _ _ _ ) in H9; try OrSearch.
      unfold Bld; OrSearch.

    - apply (IsClosingInj_inv _ _ u) in H16.
      rewrite <- H16 in *.
      assert ( Hx : [if y =? u then BName 0 else FName y ←→ if u =? u then BName 0 else FName u] = Close_Rec 0 u ([FName y ←→ FName u]) ). Piauto.
      rewrite Hx in H12.
      apply (Close_Same_Inv _ _ u 0) in H12; Piauto.
      rewrite <- H12 in *.
      apply (No_Typing_Fuse_One_Rg A _ _ _ _ _) in H9; try OrSearch.
      unfold Bld. OrSearch.

    - apply (IsClosingInj_inv _ _ u) in H22.
      rewrite <- H22 in *.
      assert ( Hx : ν (Close_Name 1 u (if u =? y then BName 0 else FName u)
         « Close_Name 1 u (if y =? y then BName 0 else FName y)
         »· Close_Rec 1 u (Close_Rec 0 y Q1)) = Close_Rec 0 u (ν Close_Rec 0 y ( (FName u
         « FName y
         »· Q1) ))). Piauto.
      rewrite Hx in H13.
      apply (Close_Same_Inv _ _ u 0) in H13; Piauto.
      apply (Close_Same_Inv _ _ u 1) in H12; Piauto.
      rewrite H12.
      clear Hx; clear H11; clear IHInference1.
      apply (cutwnot _ _ _ _ _ A x u); Piauto.
      admit.
      admit.

      rewrite <- H13 in H9.
      inversions H9.
      * admit. (* cyclic argument *)
      * admit. (* cyclic argument *)
      
      * apply Equality_Substitution_Beq_Left in H11; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H33.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H11; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H33.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H11; Piauto.
        subst.
        apply No_Disjoint_Context_Right in H34.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H11; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H23.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H24; Piauto.
        subst.
        rewrite (App_Nil_Left F).
        rewrite (App_Nil_Left G).
        apply (cutl (Bld u0 A0 ∪ D0) F G ø ø _ _  A0 y); Piauto.
        admit.

        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x (A0 ^⊥)) x y (A0 ^⊥) = (Bld y (A0 ^⊥) ∪ ø) ).
          rewrite Replace_Bld.
          ePiauto.
        rewrite <- Ht.
        apply Type_Subst_Lf; try constructor.
        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        Piauto.

      * apply Equality_Substitution_Beq_Left in H11; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H23.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H24; Piauto.
        subst.
        rewrite (App_Nil_Left F).
        rewrite (App_Nil_Left G).
        apply (cutl (Bld u0 A0 ∪ D0) F G ø ø _ _  A0 y); Piauto.
        admit.
        admit.
        
        rewrite <- (Doble_Duality_ULLT A0) at 2.
        assert ( Ha : G = SMA (Bld y (A0 ^⊥) ∪ G) y (A0 ^⊥)).
          apply eq_sym.
          Piauto.
        rewrite Ha.
        rewrite (Union_commutative _ ( Bld y ((A0 ^⊥) ^⊥) ) F).
        apply Transference_Rg_Lf; try OrSearchCons; Piauto.
        
        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x (A0 ^⊥)) x y (A0 ^⊥) = (Bld y (A0 ^⊥) ∪ ø) ).
          rewrite Replace_Bld.
          ePiauto.
        rewrite <- Ht.
        apply Type_Subst_Lf; try constructor.

        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        Piauto.

    - apply (IsClosingInj_inv _ _ u) in H22.
      rewrite <- H22 in *.
      assert ( Hx : ν (Close_Name 1 u (if u =? y then BName 0 else FName u)
         « Close_Name 1 u (if y =? y then BName 0 else FName y)
         »· Close_Rec 1 u (Close_Rec 0 y Q1)) = Close_Rec 0 u (ν Close_Rec 0 y ( (FName u
         « FName y
         »· Q1) ))). Piauto.
      rewrite Hx in H13.
      apply (Close_Same_Inv _ _ u 0) in H13; Piauto.
      apply (Close_Same_Inv _ _ u 1) in H12; Piauto.
      rewrite H12.
      apply (cutwnot _ _ _ _ _ A x u); Piauto.
      admit.
      admit.

      rewrite <- H13 in H9.
      inversions H9.
      * admit. (* cyclic argument *)
      * admit. (* cyclic argument *)

      * apply Equality_Substitution_Beq_Left in H21; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H34.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H21; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H34.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H21; Piauto.
        subst.
        apply No_Disjoint_Context_Right in H35.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H21; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H23.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H25; Piauto.
        subst.
        rewrite (App_Nil_Right F).
        rewrite (App_Nil_Right G).
        apply (cutr (Bld u0 A0 ∪ D0) ø ø F G _ _  A0 y); Piauto.
        admit.
        
        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x A0) x y A0 = (Bld y A0 ∪ ø) ). 
          rewrite Replace_Bld.
          ePiauto.
        rewrite <- Ht.
        apply Type_Subst_Rg; Piauto.
        apply Equality_Context in H26; ePiauto.
        destruct H26.
        subst.

        assert( Ha : SMA (Bld x (A ^⊥)) x (A ^⊥) = ø );
          ePiauto.
        rewrite <- Ha.
        rewrite App_Nil_Right.
        rewrite <- (Doble_Duality_ULLT A) at 3.

        apply Transference_Lf_Rg; ePiauto.
        constructor.
        constructor.

      * apply Equality_Substitution_Beq_Left in H21; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H23.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H25; Piauto.
        subst.
        rewrite (App_Nil_Right F).
        rewrite (App_Nil_Right G).
        apply (cutr (Bld u0 A0 ∪ D0) ø ø F G _ _  A0 y); Piauto.
        admit.
        admit.
        
        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x A0) x y A0 = (Bld y A0 ∪ ø) ). 
          rewrite Replace_Bld.
          ePiauto.
        rewrite <- Ht.
        apply Type_Subst_Rg; try OrSearchCons; Piauto.
        apply Equality_Context in H26; ePiauto.
        destruct H26.
        subst.

        assert( Ha : SMA (Bld x (A ^⊥)) x (A ^⊥) = ø );
          ePiauto.
        rewrite <- Ha.
        rewrite App_Nil_Right.
        rewrite <- (Doble_Duality_ULLT A) at 3.
        apply Transference_Lf_Rg; try OrSearchCons; ePiauto.

        rewrite (Union_commutative _ (Bld y A0) F).
        assert( Ha : SMA (Bld y (A0 ^⊥) ∪ G) y (A0 ^⊥) = G ); Piauto.
        rewrite <- Ha.
        rewrite <- (Doble_Duality_ULLT A0) at 2.
        apply Transference_Rg_Lf; try OrSearchCons; ePiauto.

  + inversions H10.
    - assert ( Hx : [if x0 =? x0 then BName 0 else FName x0 ←→ if y =? x0 then BName 0 else FName y] =  Close_Rec 0 x0 ([FName x0 ←→ FName y]) ). Piauto.
      rewrite Hx in H12.
      apply (IsClosingInj_inv _ _ x) in H16.
      rewrite <- H16 in *.
      apply (Close_Same_Inv _ _ x 0) in H12; Piauto.
      rewrite <- H12 in *.
      inversions H9.
      * rewrite App_Nil_Left in H20 at 1.
        apply Equality_Context in H20; ePiauto.
        destruct H20.
        apply (Close_Same_Inv _ _ x0 0) in H11; Piauto.
        subst.
        rewrite <- App_Nil_Left.
        rewrite (Union_commutative _ G (Bld y A)).
        assert( Ht : Replace (Bld x0 A ∪ G) x0 y A = (Bld y A ∪ G) ); Piauto.
        rewrite <- Ht.
        apply Type_Subst_Rg; try OrSearchCons; Piauto.

      * apply Equality_Context in H20; ePiauto.
        destruct H20.
        apply (Close_Same_Inv _ _ x0 0) in H11; Piauto.
        subst.
        rewrite <- App_Nil_Left.
        assert( Ht : Replace (F ∪ Bld x0 (A^⊥)) x0 y (A^⊥) = (F ∪ Bld y (A ^⊥)) ).
          rewrite Union_commutative.
          rewrite (Union_commutative _ F _).
          Piauto.
        rewrite <- Ht.
        apply Type_Subst_Lf; try OrSearchCons; Piauto.
        assert( Ha : SMA (Bld x0 A ∪ G) x0 A = G ); Piauto.
        rewrite <- Ha.
        apply Transference_Rg_Lf; try OrSearchCons; ePiauto.

      * apply (Equality_Subst_Equality _ _ u x1) in H17.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H17; Piauto.
        rewrite Subst_By_Equal in H17.
        subst.
        apply (No_Typing_Fuse_One_Subst_Lf A0 _ _ _  _ _ _) in H33; Piauto.
        contradiction.

      * apply (Equality_Subst_Equality _ _ u x1) in H17.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H17; Piauto.
        rewrite Subst_By_Equal in H17.
        subst.
        apply (No_Typing_Fuse_One_Subst_Lf A0 _ _ _  _ _ _) in H31; Piauto.
        contradiction.

    - assert ( Hx : [if y =? x0 then BName 0 else FName y ←→ if x0 =? x0 then BName 0 else FName x0] =  Close_Rec 0 x0 ([FName y ←→ FName x0]) ). Piauto.
      rewrite Hx in H12.
      apply (IsClosingInj_inv _ _ x) in H16.
      rewrite <- H16 in *.
      apply (Close_Same_Inv _ _ x 0) in H12; Piauto.
      rewrite <- H12 in *.
      inversions H9.
      * apply Extension in H20.
        inversions H20.
        unfold Included in H16.
        assert( Ha : (FName x0 : A) ∈ (Bld x0 A ∪ F') ); try OrSearchCons.
        specialize (H16 (FName x0 : A) Ha).
        inversions H16.
        lia.

      * rewrite (Union_commutative _ (Bld y A0) (Bld x0 (A0 ^⊥))) in H20.
        apply Equality_Context in H20; ePiauto.
        destruct H20.
        apply (Close_Same_Inv _ _ x0 0) in H11; Piauto.
        subst.
        rewrite <- App_Nil_Left.
        assert( Ht : Replace (F ∪ Bld x0 A0) x0 y (A0) = (F ∪ Bld y A0) ).
          rewrite Union_commutative.
          rewrite (Union_commutative _ F).
          Piauto.
        rewrite <- Ht.
        apply Type_Subst_Lf; try OrSearchCons; Piauto.
        assert( Ha : SMA (Bld x0 (A0 ^⊥) ∪ G) x0 (A0 ^⊥) = G ); Piauto.
        rewrite <- Ha.
        rewrite <- (Doble_Duality_ULLT A0) at 1.
        apply Transference_Rg_Lf; try OrSearchCons; ePiauto.

        apply GContext_Second_Injective in H25.
        rewrite Union_commutative.
        Piauto.

      * apply (Equality_Subst_Equality _ _ u x1) in H17.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H17; Piauto.
        rewrite Subst_By_Equal in H17.
        subst.
        apply (No_Typing_Fuse_One_Subst_Lf A0 _ _ _  _ _ _) in H33; Piauto.
        contradiction.

      * apply (Equality_Subst_Equality _ _ u x1) in H17.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H17; Piauto.
        rewrite Subst_By_Equal in H17.
        subst.
        apply (No_Typing_Fuse_One_Subst_Lf A0 _ _ _  _ _ _) in H31; Piauto.
        contradiction.

    - assert ( Hx : [if y =? x0 then BName 0 else FName y ←→ if x0 =? x0 then BName 0 else FName x0] =  Close_Rec 0 x0 ([FName y ←→ FName x0]) ). Piauto.
      rewrite Hx in H11.
      apply (IsClosingInj_inv _ _ x) in H16.
      rewrite <- H16 in *.
      apply (Close_Same_Inv _ _ x 0) in H11; Piauto.
      rewrite <- H11 in *.
      inversions H8.
      * rewrite (App_Nil_Left (Bld x0 A0)) in H20.
        apply Equality_Context in H20; ePiauto.
        destruct H20.
        apply (Close_Same_Inv _ _ x0 0) in H12; Piauto.
        subst.
        rewrite <- App_Nil_Right.
        assert( Ht : Replace (Bld x0 A ∪ F') x0 y (A) = (Bld y A ∪ F') ); Piauto.
        rewrite <- Ht.
        apply Type_Subst_Lf; Piauto.
        OrSearchCons.

      * apply Extension in H20.
        inversions H20.
        unfold Included in H16.
        assert( Ha : (FName x0 : A) ∈ (Bld x0 A ∪ G) ); try OrSearchCons.
        specialize (H16 (FName x0 : A) Ha).
        inversions H16.

      * apply (Equality_Subst_Equality _ _ u x1) in H17.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H17; Piauto.
        rewrite Subst_By_Equal in H17.
        subst.
        apply (No_Typing_Fuse_One_Subst_Lf A0 _ _ _  _ _ _) in H31; Piauto.
        contradiction.

      * apply (Equality_Subst_Equality _ _ u x1) in H17.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H17; Piauto.
        rewrite Subst_By_Equal in H17.
        subst.
        apply (No_Typing_Fuse_One_Subst_Lf A0 _ _ _  _ _ _) in H34; Piauto.
        contradiction.

    - assert ( Hx : [if x0 =? x0 then BName 0 else FName x0 ←→ if y =? x0 then BName 0 else FName y] =  Close_Rec 0 x0 ([FName x0 ←→ FName y]) ). Piauto.
      rewrite Hx in H11.
      apply (IsClosingInj_inv _ _ x) in H16.
      rewrite <- H16 in *.
      apply (Close_Same_Inv _ _ x 0) in H11; Piauto.
      rewrite <- H11 in *.
      inversions H8.
      * apply Extension in H20.
        inversions H20.
        unfold Included in H16.
        assert( Ha : (FName x0 : A) ∈ (Bld x0 A ∪ G) ); try OrSearchCons.
        specialize (H16 (FName x0 : A) Ha).
        inversions H16.
        lia.

      * apply Extension in H20.
        inversions H20.
        unfold Included in H16.
        assert( Ha : (FName x0 : A) ∈ (Bld x0 A ∪ G) ); try OrSearchCons.
        specialize (H16 (FName x0 : A) Ha).
        inversions H16.

      * apply (Equality_Subst_Equality _ _ u x1) in H17.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H17; Piauto.
        rewrite Subst_By_Equal in H17.
        subst.
        apply (No_Typing_Fuse_One_Subst_Lf A0 _ _ _  _ _ _) in H31; Piauto.
        contradiction.

      * apply (Equality_Subst_Equality _ _ u x1) in H17.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H17; Piauto.
        rewrite Subst_By_Equal in H17.
        subst.
        apply (No_Typing_Fuse_One_Subst_Lf A0 _ _ _  _ _ _) in H34; Piauto.
        contradiction.

    - assert ( Hx : (if x0 =? x0 then BName 0 else FName x0) ·θ = Close_Rec 0 x0 (FName x0 ·θ) ); Piauto.
      rewrite Hx in H11.
      apply (IsClosingInj_inv _ _ x) in H17.
      rewrite <- H17 in *.
      apply (Close_Same_Inv _ _ x 0) in H11; Piauto.
      rewrite <- H11 in *.
      inversion H8.
      * apply (Equality_Subst_Equality _ _ u x1) in H16.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H16; Piauto.
        rewrite Subst_By_Equal in H16.
        subst.
        apply (No_Typing_Zero_Ord_Subst A0 _ _ _  _ _ _) in H30; Piauto.
        contradiction.

      * apply (Equality_Subst_Equality _ _ u x1) in H16.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H16; Piauto.
        rewrite Subst_By_Equal in H16.
        subst.
        apply (No_Typing_Zero_Ord_Subst A0 _ _ _  _ _ _) in H33; Piauto.
        contradiction.

      * apply Extension in H18.
        inversions H18.
        unfold Included in H24.
        assert( Ha : (FName x0 : A) ∈ (Bld x0 A ∪ G) ); try OrSearchCons.
        specialize (H24 (FName x0 : A) Ha).
        inversions H24.

      * assert ( Ha : ((if x =? x then BName 0 else FName x) ()·Close_Rec 0 x Q0) = Close_Rec 0 x ( (FName x) ()· Q0)).
          Piauto.
        rewrite Ha in H12.
        apply (Close_Same_Inv _ _ x 0) in H12; Piauto.
        subst.
        inversions H9.

        ** admit. (* cyclic argument *)
        ** admit. (* cyclic argument *)

        ** rewrite (App_Nil_Left (Bld x0 ¶)) in H18.
           apply Equality_Context in H18; ePiauto.
           destruct H18.
           subst.
           do 2 rewrite <- App_Nil_Right.
           rewrite (Union_commutative _ (Bld x0 ⊥) G0).
           assert ( Ht : SMA (Bld x0 ¶ ∪ F') x0 ¶ = F' ); Piauto.
           rewrite <- Ht.
           apply Transference_Lf_Rg; try OrSearchCons; ePiauto.

        ** rewrite (App_Nil_Left (Bld x0 ¶)) in H18.
           apply Equality_Context in H18; ePiauto.
           destruct H18.
           apply Equality_Context in H16; ePiauto.
           destruct H16.
           subst.
           do 2 rewrite <- App_Nil_Right.
           Piauto.

    - assert ( Hx : (if x0 =? x0 then BName 0 else FName x0) ·θ = Close_Rec 0 x0 (FName x0 ·θ) ). Piauto.
      rewrite Hx in H12.
      apply (IsClosingInj_inv _ _ x) in H17.
      rewrite <- H17 in *.
      apply (Close_Same_Inv _ _ x 0) in H12; Piauto.
      rewrite <- H12 in *.
      inversion H9.
      * apply (Equality_Subst_Equality _ _ u x1) in H16.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H16; Piauto.
        rewrite Subst_By_Equal in H16.
        subst.
        apply (No_Typing_Zero_Ord_Subst A0 _ _ _  _ _ _) in H32; Piauto.
        contradiction.

      * apply (Equality_Subst_Equality _ _ u x1) in H16.
        rewrite <- (Double_Subst_Expan_NFVar _ u u x1) in H16; Piauto.
        rewrite Subst_By_Equal in H16.
        subst.
        apply (No_Typing_Zero_Ord_Subst A0 _ _ _  _ _ _) in H30; Piauto.
        contradiction.

      * assert ( Ha : ((if x =? x then BName 0 else FName x) ()·Close_Rec 0 x Q0) = Close_Rec 0 x ( (FName x) ()· Q0)).
          Piauto.
        rewrite Ha in H11.
        apply (Close_Same_Inv _ _ x 0) in H11; Piauto.
        subst.
        inversions H8.

        ** admit. (* cyclic argument *)
        ** admit. (* cyclic argument *)

        ** rewrite (App_Nil_Left (Bld x0 ⊥)) in H18.
           apply Equality_Context in H18; ePiauto.
           destruct H18.
           apply Equality_Context in H16; ePiauto.
           destruct H16.
           subst.
           do 2 rewrite <- App_Nil_Left.
           Piauto.

        ** apply No_Disjoint_Context_Left_Right in H24.
           contradiction.

      * apply Extension in H18.
        inversions H18.
        unfold Included in H24.
        assert( Ha : (FName x0 : A) ∈ (Bld x0 A ∪ F') ); try OrSearchCons.
        specialize (H24 (FName x0 : A) Ha).
        inversions H24.

    - admit. (* Prueba repetida Cut! *)
    - admit. (* Prueba repetida Cut? *)
    
    - assert ( Hx : ν (Close_Name 1 x0 (if x0 =? y then BName 0 else FName x0)
         « Close_Name 1 x0 (if y =? y then BName 0 else FName y)
         »· (Close_Rec 1 x0 (Close_Rec 0 y Q1)
             ↓ Close_Rec 1 x0 (Close_Rec 0 y R))) = Close_Rec 0 x0 ( ν Close_Rec 0 y (FName x0 « FName y »· ( Q1 ↓ R)))) .
             Piauto.
      rewrite Hx in H12.
      apply (IsClosingInj_inv _ _ x) in H21.
      subst.
      apply (Close_Same_Inv _ _ x0 _) in H12; Piauto.
      subst.
      inversions H9.

      * admit. (* cyclic argument *)
      * admit. (* cyclic argument *)

      * assert (Ha : (if x0 =? x0 then BName 0 else FName x0) · Close_Rec 1 x0 P0 = Close_Rec 0 x0 (FName x0 · P0));
          Piauto.
        rewrite Ha in H11.
        apply (Close_Same_Inv _ _ x0 _) in H11; Piauto.
        apply Equality_Substitution_Beq_Left in H12; Piauto.
        apply (IsClosingInj_inv _ _ y0) in H23.
        subst.
        apply (Close_Same_Inv _ _ y _) in H24; Piauto.
        apply (Close_Same_Inv _ _ y _) in H22; Piauto.
        subst.
        rewrite Union_associative in H25.
        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        inversions H8.

        ** admit. (* cyclic argument *)
        ** admit. (* cyclic argument *)

        ** apply Equality_Context in H22; ePiauto.
           destruct H22.
           inversions H11.
           do 2 rewrite <- Union_associative.
           apply (cutr D (F ∪ F0) (G ∪ G0) F'0 G'0 _ _  B x0); Piauto.
           admit.
           
           rewrite Union_commutative.
           rewrite <- Union_associative.
           rewrite <- (Union_commutative _ G0).
           apply (cutr D F0 G0 F (Bld x0 B ∪ G) _ _ A0 y); Piauto.
           admit.
           
           rewrite Lc_Open_Close_Subst; Piauto.
           assert( Ht : Replace (Bld y0 A0 ∪ F) y0 y A0 = (Bld y A0 ∪ F) ); Piauto.
           rewrite <- Ht.
           apply Dual_inv in H41.
           subst.
           apply Type_Subst_Lf; try OrSearchCons; Piauto.

        ** apply Equality_Context in H22; ePiauto.
           destruct H22.
           inversions H11.
           do 2 rewrite <- Union_associative.
           apply (cutr D (F ∪ F0) (G ∪ G0) F'0 G'0 _ _  B x0); Piauto.
           admit.

           rewrite Union_commutative.
           rewrite <- Union_associative.
           rewrite <- (Union_commutative _ G0).
           apply (cutr D F0 G0 F (Bld x0 B ∪ G) _ _ A0 y); Piauto.
           admit.

           rewrite Lc_Open_Close_Subst; Piauto.
           assert( Ht : Replace (Bld y0 A0 ∪ F) y0 y A0 = (Bld y A0 ∪ F) ); Piauto.
           rewrite <- Ht.
           apply Type_Subst_Lf;try OrSearchCons; Piauto.
           rewrite Union_commutative.
           assert( Hb : (Bld x0 B ∪ G) = SMA ((Bld x0 B ∪ Bld y0 (A0 ^⊥)) ∪ G) y0 (A0 ^⊥) ).
            apply eq_sym.
            rewrite (Union_commutative _ (Bld x0 B) ).
            rewrite Union_associative.
            Piauto.
           rewrite Hb.
           rewrite <- Doble_Duality_ULLT at 1.
           apply Transference_Rg_Lf ; try OrSearchCons; Piauto.

        ** apply No_Disjoint_Context_Left_Right in H40.
           contradiction.

        ** apply GContext_Second_Injective in H37.
           rewrite <- Union_associative.
           Piauto.

      * assert (Ha : (if x0 =? x0 then BName 0 else FName x0) · Close_Rec 1 x0 P0 = Close_Rec 0 x0 (FName x0 · P0));
          Piauto.
        rewrite Ha in H11.
        apply (Close_Same_Inv _ _ x0 _) in H11; Piauto.
        apply Equality_Substitution_Beq_Left in H12; Piauto.
        apply (IsClosingInj_inv _ _ y0) in H23.
        subst.
        apply (Close_Same_Inv _ _ y _) in H24; Piauto.
        apply (Close_Same_Inv _ _ y _) in H22; Piauto.
        subst.
        rewrite Union_associative in H25.
        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        inversions H8.

        ** admit. (* cyclic argument *)
        ** admit. (* cyclic argument *)

        ** apply Equality_Context in H22; ePiauto.
           destruct H22.
           inversions H11.
           do 2 rewrite <- Union_associative.
           apply (cutr D (F ∪ F0) (G ∪ G0) F'0 G'0 _ _  B x0); Piauto.
           admit.
           
           rewrite Union_commutative.
           rewrite <- Union_associative.
           rewrite <- (Union_commutative _ G0).
           apply (cutr D F0 G0 F (Bld x0 B ∪ G) _ _ A y); Piauto.
           admit.
           admit.

           assert( Ht : SMA (Bld y (A ^⊥) ∪ F0) y (A ^⊥) = F0); Piauto.
           rewrite <- Ht.
           rewrite <- (Doble_Duality_ULLT A) at 3.
           rewrite <- (Union_commutative _ G0).
           apply Transference_Lf_Rg; try OrSearchCons; Piauto.

           rewrite Lc_Open_Close_Subst; Piauto.
           assert( Ht : Replace (Bld y0 A ∪ F) y0 y A = (Bld y A ∪ F) ); Piauto.
           rewrite <- Ht.
           apply Type_Subst_Lf; try OrSearchCons; Piauto.

        ** apply Equality_Context in H22; ePiauto.
           destruct H22.
           inversions H11.
           do 2 rewrite <- Union_associative.
           apply (cutr D (F ∪ F0) (G ∪ G0) F'0 G'0 _ _  B x0); Piauto.
           admit.
           
           rewrite Union_commutative.
           rewrite <- Union_associative.
           rewrite <- (Union_commutative _ G0).
           apply (cutl D F0 G0 F (Bld x0 B ∪ G) _ _ A0 y); Piauto.
           admit.
           
           rewrite Lc_Open_Close_Subst; Piauto.
           assert( Ht : Replace (Bld y0 (A0 ^⊥) ∪ F) y0 y (A0 ^⊥) = (Bld y (A0 ^⊥) ∪ F) ); Piauto.
           rewrite <- Ht.
           apply Type_Subst_Lf; try OrSearchCons; Piauto.

           assert( Hb : SMA (((Bld x0 B ∪ Bld y0 A0) ∪ G)) y0 (A0) = (Bld x0 B ∪ G)).
            rewrite (Union_commutative _ (Bld x0 B) ).
            rewrite Union_associative.
            Piauto.
           rewrite <- Hb.
           rewrite <- (Union_commutative _ F).
           apply Transference_Rg_Lf; try OrSearchCons; Piauto.

        ** apply No_Disjoint_Context_Left_Right in H40.
           contradiction.

        ** apply GContext_Second_Injective in H37.
           rewrite <- Union_associative.
           Piauto.

      * apply Equality_Substitution_Beq_Left in H12; Piauto.
        apply (IsClosingInj_inv _ _ y0) in H23.
        subst.
        rewrite H25 in H38.
        rewrite Union_associative in H38.
        apply No_Disjoint_Context_Left_Right in H38.
        contradiction.

      * apply (IsClosingInj_inv _ _ x) in H23.
        subst.
        assert (Ht : Close_Rec 0 y Q1 ↓ Close_Rec 0 y R = Close_Rec 0 y (Q1 ↓ R));
          Piauto.
        rewrite Ht in H22.
        apply (Close_Same_Inv _ _ y _) in H22; Piauto.
        subst.
        apply No_Typing_Parallel in H34.
        contradiction.

      * apply (IsClosingInj_inv _ _ x) in H23.
        subst.
        assert (Ht : Close_Rec 0 y Q1 ↓ Close_Rec 0 y R = Close_Rec 0 y (Q1 ↓ R));
          Piauto.
        rewrite Ht in H22.
        apply (Close_Same_Inv _ _ y _) in H22; Piauto.
        subst.
        apply No_Typing_Parallel in H34.
        contradiction.

      * apply Process_ProcessAt.
        apply Body_Process_Equivalence_Res.
        constructor.
        apply Lc_Close_Is_Body.
        constructor; Piauto.

    - assert ( Hx : ν (Close_Name 1 x0 (if x0 =? y then BName 0 else FName x0)
         « Close_Name 1 x0 (if y =? y then BName 0 else FName y)
         »· (Close_Rec 1 x0 (Close_Rec 0 y Q1)
             ↓ Close_Rec 1 x0 (Close_Rec 0 y R))) = Close_Rec 0 x0 ( ν Close_Rec 0 y (FName x0 « FName y »· ( Q1 ↓ R)))) .
             Piauto.
      rewrite Hx in H11.
      apply (IsClosingInj_inv _ _ x) in H21.
      subst.
      apply (Close_Same_Inv _ _ x0 _) in H11; Piauto.
      subst.
      inversions H8.

      * admit. (* cyclic argument *)
      * admit. (* cyclic argument *)

      * apply Equality_Substitution_Beq_Left in H11; Piauto.
        subst.
        rewrite H25 in H37.
        rewrite Union_associative in H37.
        apply No_Disjoint_Context_Left_Right in H37.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H11; Piauto.
        subst.
        rewrite H25 in H37.
        rewrite Union_associative in H37.
        apply No_Disjoint_Context_Left_Right in H37.
        contradiction.

      * assert (Ha : (if x0 =? x0 then BName 0 else FName x0) · Close_Rec 1 x0 P0 = Close_Rec 0 x0 (FName x0 · P0));
          Piauto.
        rewrite Ha in H12.
        apply (Close_Same_Inv _ _ x0 _) in H12; Piauto.
        apply Equality_Substitution_Beq_Left in H11; Piauto.
        apply (IsClosingInj_inv _ _ y0) in H23.
        subst.
        apply (Close_Same_Inv _ _ y _) in H24; Piauto.
        apply (Close_Same_Inv _ _ y _) in H22; Piauto.
        subst.
        rewrite Union_associative in H25.
        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        inversions H9.

        ** admit. (* cyclic argument *)
        ** admit. (* cyclic argument *)

        ** apply No_Disjoint_Context_Left_Right in H41.
           contradiction.

        ** apply No_Disjoint_Context_Left_Right in H36.
           contradiction.

        ** apply Equality_Context in H22; ePiauto.
           destruct H22.
           inversions H11.
           rewrite (Union_commutative _ F0).
           rewrite (Union_commutative _ G0).
           do 2 rewrite Union_associative.
           apply (cutr D F'0 G'0 (F0 ∪ F') (G0 ∪ G')  _ _  B x0); Piauto.
           admit.

           rewrite <- Union_associative.
           rewrite <- (Union_commutative _ F0).
           rewrite Union_associative.
           apply (cutr D F0 G0 (Bld x0 B ∪ F') G' _ _ A0 y); Piauto.
           admit.
           
           rewrite Lc_Open_Close_Subst; Piauto.
           assert( Ht : Replace ((Bld x0 B ∪ Bld y1 A0) ∪ F') y1 y A0 = (Bld y A0 ∪ (Bld x0 B ∪ F')) ).
            rewrite (Union_commutative _ (Bld x0 B)).
            rewrite Union_associative.
            Piauto.
           rewrite <- Ht.
           apply Type_Subst_Lf; try OrSearchCons; Piauto.

        ** apply GContext_Three_Injective in H38.
           rewrite <- Union_associative.
           Piauto.

      * apply (IsClosingInj_inv _ _ x) in H23.
        subst.
        assert (Ht : Close_Rec 0 y Q1 ↓ Close_Rec 0 y R = Close_Rec 0 y (Q1 ↓ R));
          Piauto.
        rewrite Ht in H22.
        apply (Close_Same_Inv _ _ y _) in H22; Piauto.
        subst.
        apply No_Typing_Parallel in H34.
        contradiction.

      * apply (IsClosingInj_inv _ _ x) in H23.
        subst.
        assert (Ht : Close_Rec 0 y Q1 ↓ Close_Rec 0 y R = Close_Rec 0 y (Q1 ↓ R));
          Piauto.
        rewrite Ht in H22.
        apply (Close_Same_Inv _ _ y _) in H22; Piauto.
        subst.
        apply No_Typing_Parallel in H34.
        contradiction.

      * apply Process_ProcessAt.
        apply Body_Process_Equivalence_Res.
        constructor.
        apply Lc_Close_Is_Body.
        constructor; Piauto.

  + admit.
Admitted.
