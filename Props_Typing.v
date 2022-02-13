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




(*
(**
*)
Proposition Type_Subst_Lf :
forall ( P : Process )( D F G : Context ),
( D ;;; F !- P ::: G ) ->
forall ( w z : nat )( A : Proposition ), (FName z : A) ∈ F -> Fresh w (D ∪ F ∪ G) -> 
~(w ∈ (FVars P)) -> ( D ;;; (Replace F z w A) !- {w \ z}P ::: G ).
Proof.
  intros.
  dependent induction H.
  + inversions H2.
    simpl.
    DecidSimple z z.
    DecidSimple y z.
    rewrite n.
    rewrite Replace_Bld.
    constructor; Piauto.
    admit.
    admit.
  + apply Union_inv in H2.
    destruct H2.
    - inversions H2.
      rewrite Replace_Union.
      rewrite Replace_Bld.
      rewrite Replace_Bld_Beq; Piauto.
      
      rewrite Union_commutative.
      rewrite Union_associative.
      rewrite Union_idempotent.
      rewrite Union_commutative.

      simpl.
      DecidSimple z z.
      DecidSimple y z.
      rewrite n.
      constructor; Piauto.
      
      admit.
      admit.

    - inversions H2.
      rewrite Replace_Union.
      rewrite Replace_Bld.
      rewrite Replace_Bld_Beq; Piauto.
      
      rewrite Union_associative.
      rewrite Union_idempotent.

      simpl.
      DecidSimple z z.
      DecidSimple x z.
      rewrite n.
      constructor; Piauto.
      admit.
      admit.
  + inversions H6.
  + admit.
  + assert (Hu : u <> z). admit.
    assert (Hx : x <> z). admit.
    assert (Hux : w <> u). admit.
    subst.

    rewrite Double_Subst_All_Dif; Piauto.
    constructor; ePiauto.
    admit.
    admit.
    admit.
    admit.
    admit.
    apply IHInference; Piauto.
    constructor.
    unfold not.
    intros.
    subst.
    admit.
Admitted.
#[global]
Hint Resolve Type_Subst_Lf : Piull.



(**
*)
Proposition Type_Subst_Rg :
forall ( P : Process )( D F G : Context ),
( D ;;; F !- P ::: G ) ->
forall ( w z : nat )( A : Proposition ), (FName z : A) ∈ G -> Fresh w (D ∪ F ∪ G) -> 
~(w ∈ (FVars P)) -> ( D ;;; F !- {w \ z}P ::: (Replace G z w A) ).
Proof.
Admitted.
#[global]
Hint Resolve Type_Subst_Rg : Piull.

*)


Proposition Type_Subst_Lf :
forall ( P : Process )( D F G : Context ),
( D ;;; F !- P ::: G ) ->
forall ( w z : nat )( A : Proposition ), (FName z : A) ∈ F -> 
( D ;;; (Replace F z w A) !- {w \ z}P ::: G ).
Proof.
Admitted.



Proposition Type_Subst_Rg :
forall ( P : Process )( D F G : Context ),
( D ;;; F !- P ::: G ) ->
forall ( w z : nat )( A : Proposition ), (FName z : A) ∈ G -> 
( D ;;; F !- {w \ z}P ::: (Replace G z w A) ).
Proof.
Admitted.


Lemma Transference_Rg_Lf :
forall ( P : Process)(D F G : Context),
D;;; F !- P ::: G -> 
forall (x : nat)(A : Proposition), ( (FName x : A) ∈ G ) ->
D;;; (F ∪ Bld x (A ^⊥)) !- P ::: (SMA G x A).
Proof.
Admitted.


Lemma Transference_Lf_Rg :
forall ( P : Process)(D F G : Context),
D;;; F !- P ::: G -> 
forall (x : nat)(A : Proposition), ( (FName x : A) ∈ F ) ->
D;;; (SMA F x A) !- P ::: (G ∪ Bld x (A ^⊥)).
Proof.
Admitted.





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
    exfalso.
    apply (H3 x A B).
    constructor; Piauto.
  + 
Admitted.
#[global]
Hint Resolve Equality_Context : Piull.



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
  + admit.
  (*+ inversions H9.
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
      apply (cutrep _ _ _ _ _ A x u); Piauto.
      subst.
      admit.

      rewrite <- H12 in H8.
      inversions H8.
      * admit. (* cyclic argument *)
      * admit. (* cyclic argument *)
      
      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H32.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply No_Disjoint_Context_Left in H32.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply No_Disjoint_Context_Right in H33.
        contradiction.

      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H22.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H23; Piauto.
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
        apply Equality_Context in H24; ePiauto.
        destruct H24.
        subst.
        rewrite <- Hx.
        rewrite (App_Nil_Right (Bld x (A ^⊥))).
        apply Transference_Rg_Lf; ePiauto.
        constructor.

      * apply Equality_Substitution_Beq_Left in H10; Piauto.
        subst.
        apply (IsClosingInj_inv _ _ x0) in H22.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H23; Piauto.
        subst.
        rewrite (App_Nil_Left F).
        rewrite (App_Nil_Left G).
        apply (cutl (Bld u0 A0 ∪ D0) F G ø ø _ _  A0 y); Piauto.
        admit.
        admit.
        
        rewrite <- (Doble_Duality_ULLT A0) at 2.
        assert ( Ha : G = SMA (Bld y (A0 ^⊥) ∪ G) y (A0 ^⊥)).
          admit.
        rewrite Ha.
        rewrite (Union_commutative _ ( Bld y ((A0 ^⊥) ^⊥) ) F).
        apply Transference_Rg_Lf; Piauto.
        left; constructor.
        
        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x (A0 ^⊥)) x y (A0 ^⊥) = (Bld y (A0 ^⊥) ∪ ø) ).
          rewrite Replace_Bld.
          ePiauto.

        rewrite <- Ht.
        apply Type_Subst_Lf; try constructor.
        assert( Hx : SMA (Bld x A0) x A0 = ø );
          ePiauto.
        apply Equality_Context in H24; ePiauto.
        destruct H24.
        subst.
        rewrite <- Hx.
        rewrite (App_Nil_Right (Bld x (A ^⊥))).
        apply Transference_Rg_Lf; ePiauto.
        constructor.

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
        apply Type_Subst_Rg; Piauto.
        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        try OrSearch.
        constructor.

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
        apply Type_Subst_Rg; Piauto.
        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        try OrSearch.
        constructor.
    *)
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
          admit.
        rewrite Ha.
        rewrite (Union_commutative _ ( Bld y ((A0 ^⊥) ^⊥) ) F).
        apply Transference_Rg_Lf; Piauto.
        left; constructor.
        
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
        apply Type_Subst_Rg; Piauto.
        apply Equality_Context in H25; ePiauto.
        destruct H25.
        subst.
        try OrSearch.
        constructor.
  
  
    
    
    
    
    
    
    
    
    
    
    
    
    
    

  + inversions H10.
    - assert ( Hx : [if x0 =? x0 then BName 0 else FName x0 ←→ if y =? x0 then BName 0 else FName y] =  Close_Rec 0 x0 ([FName x0 ←→ FName y]) ). Piauto.
      rewrite Hx in H12.
      apply (IsClosingInj_inv _ _ x) in H16.
      rewrite <- H16 in *.
      apply (Close_Same_Inv _ _ x 0) in H12; Piauto.
      rewrite <- H12 in *.
      inversions H9.
      * admit. (* derivable *)
      * assert ( Ht : (SMA (Bld x0 A ∪ G) x0 A ) = G ).
        admit.
        rewrite <- Ht.
        admit. (* derivable *)
      * admit. (* revienta *)
      * admit. (* revienta *)
    - assert ( Hx : [if y =? x0 then BName 0 else FName y ←→ if x0 =? x0 then BName 0 else FName x0] =  Close_Rec 0 x0 ([FName y ←→ FName x0]) ). Piauto.
      rewrite Hx in H12.
      apply (IsClosingInj_inv _ _ x) in H16.
      rewrite <- H16 in *.
      apply (Close_Same_Inv _ _ x 0) in H12; Piauto.
      rewrite <- H12 in *.
      inversions H9.
      * admit. (* revienta *)
      * admit. (* derivable *)
      * admit. (* revienta *)
      * admit. (* revienta *)
    - assert ( Hx : [if y =? x0 then BName 0 else FName y ←→ if x0 =? x0 then BName 0 else FName x0] =  Close_Rec 0 x0 ([FName y ←→ FName x0]) ). Piauto.
      rewrite Hx in H11.
      apply (IsClosingInj_inv _ _ x) in H16.
      rewrite <- H16 in *.
      apply (Close_Same_Inv _ _ x 0) in H11; Piauto.
      rewrite <- H11 in *.
      inversions H8.
      * admit. (* deducible *)
      * admit. (* revienta *)
      * admit. (* revienta *) 
      * admit. (* revienta *) 
    - assert ( Hx : [if x0 =? x0 then BName 0 else FName x0 ←→ if y =? x0 then BName 0 else FName y] =  Close_Rec 0 x0 ([FName x0 ←→ FName y]) ). Piauto.
      rewrite Hx in H11.
      apply (IsClosingInj_inv _ _ x) in H16.
      rewrite <- H16 in *.
      apply (Close_Same_Inv _ _ x 0) in H11; Piauto.
      rewrite <- H11 in *.
      inversions H8.
      * admit. (* revienta *)
      * admit. (* revienta *)
      * admit. (* revienta *)
      * admit. (* revienta *)

    - assert ( Hx : (if x0 =? x0 then BName 0 else FName x0) ·θ = Close_Rec 0 x0 (FName x0 ·θ) ); Piauto.
      rewrite Hx in H11.
      apply (IsClosingInj_inv _ _ x) in H17.
      rewrite <- H17 in *.
      apply (Close_Same_Inv _ _ x 0) in H11; Piauto.
      rewrite <- H11 in *.
      inversion H8.
      * subst.
        admit. (* revienta *)
      * subst.
        admit. (* revienta *)
      * admit. (* revienta *)
      * assert ( Q = (FName x0) ()· Q0 ). admit.
        subst.
        inversions H9.
        ** admit. (* cicla *)
        ** admit. (* cicla *)
        ** admit. (* derivable *)
        ** admit. (* derivable *)
    - assert ( Hx : (if x0 =? x0 then BName 0 else FName x0) ·θ = Close_Rec 0 x0 (FName x0 ·θ) ). Piauto.
      rewrite Hx in H12.
      apply (IsClosingInj_inv _ _ x) in H17.
      rewrite <- H17 in *.
      apply (Close_Same_Inv _ _ x 0) in H12; Piauto.
      rewrite <- H12 in *.
      inversion H9.
      * admit. (* revienta *)
      * admit. (* revienta *)
      * assert ( P = (FName x0) ()· Q0 ). admit.
        subst.
        inversions H8.
        ** admit. (* cicla *)
        ** admit. (* cicla *)
        ** admit. (* derivable *)
        ** admit. (* revienta - contextos disjuntos *)
      * admit. (* revienta *)
      (* * subst.
        apply Subst_Change_Side in H16; Piauto.
        simpl in H16.
        admit. (* revienta - analizar casos x0 x1*)
      * subst.
        apply Subst_Change_Side in H16; Piauto.
        simpl in H16.
        DecidSimple x0 x1.
        ** rewrite e in H16.
           rewrite H16 in *.
           apply (No_Typing_Zero_Ord A0 u) in H30; try OrSearch; Piauto.
        ** rewrite n in H16.
           admit. (* revienta *)
      * subst.
        admit. (* no se *)
      * admit. (* revienta *)  *)
    - admit. (* Prueba repetida *)
    - admit. (* Prueba repetida *)
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
      * admit.
      * admit.
      
      * admit.
      * admit.
      * admit.
      
      * admit. (* revienta, no se puede tipar ↓ *)
      * admit. (* revienta, no se puede tipar ↓ *)
      
      * admit.
    - admit.
  + admit.
Admitted.


