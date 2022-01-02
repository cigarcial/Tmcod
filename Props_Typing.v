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

Search Open_Rec.

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


Lemma Typing_Change_Side_RgLf :
forall ( P : Process)(D F G : Context),
D;;; F !- P ::: G -> 
forall (x : nat)(A : Proposition), ( (FName x : A) ∈ G ) ->
D;;; (F ∪ Bld x (A ^⊥)) !- P ::: (SMA G x A).
Proof.
Admitted.
















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
  (*+ assert (Hx := H12).
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
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + apply Parallel_Res_No_Reduces in H8; contradiction.
  + apply Chan_Input_No_Reduces in H4; contradiction.
  + apply Parallel_Res_No_Reduces in H8; contradiction.
  + apply Chan_Input_No_Reduces in H5; contradiction.
  + apply Parallel_Res_No_Reduces in H9; contradiction.
  + apply Chan_Close_No_Reduces in H4; contradiction.
  + apply Zero_No_Reduces in H0; contradiction.
  + apply Chan_Close_No_Reduces in H4; contradiction.
  + apply Zero_No_Reduces in H0; contradiction.
  + apply Output_No_Reduces in H5; contradiction.
  + apply Output_No_Reduces in H5; contradiction. *)
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
      unfold Bld. OrSearch.

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
      admit.
      
      
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
      * admit. (* cicla *)
      * admit. (* cicla *)

      * admit. (* disjoint contexts *)
      * admit. (* disjoint contexts *)
      * admit. (* disjoint contexts *)

      * apply (IsClosingInj_inv _ _ x0) in H22.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H24; Piauto.
        subst.
        rewrite (App_Nil_Right F).
        rewrite (App_Nil_Right G).
        apply (cutr (Bld u1 A0 ∪ D0) ø ø F G _ _  A0 y); Piauto.
        admit.
        admit.
        
        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x A0) x y A0 = (Bld y A0 ∪ ø) ). admit.
        rewrite <- Ht.
        apply Type_Subst_Rg; Piauto.
        try OrSearch.
        admit.
        admit.
      * apply (IsClosingInj_inv _ _ x0) in H22.
        subst.
        apply (Close_Same_Inv _ _ y 0) in H24; Piauto.
        subst.
        rewrite (App_Nil_Right F).
        rewrite (App_Nil_Right G).
        apply (cutr (Bld u1 A0 ∪ D0) ø ø F G _ _  A0 y); Piauto.
        admit.
        admit.
        
        apply Weakening_Ordinary; Piauto.
        rewrite Lc_Open_Close_Subst; Piauto.
        assert( Ht : Replace (Bld x A0) x y A0 = (Bld y A0 ∪ ø) ). admit.
        rewrite <- Ht.
        apply Type_Subst_Rg; Piauto.
        try OrSearch.
        admit.
        admit.
        
        admit.
        
      
      
      
      
      
      
      
  + inversions H8.
    - assert ( Hx : [if x0 =? x0 then BName 0 else FName x0 ←→ if y =? x0 then BName 0 else FName y] =  Close_Rec 0 x0 ([FName x0 ←→ FName y]) ). Piauto.
      rewrite Hx in H10.
      apply (IsClosingInj_inv _ _ x) in H14.
      rewrite <- H14 in *.
      apply (Close_Same_Inv _ _ x 0) in H10; Piauto.
      rewrite <- H10 in *.
      inversions H7.
      * admit. (* derivable *)
      * assert ( Ht : (Remove x0 A (Bld x0 A ++ G)) = G ++ nil).
        simpl. rewrite app_nil_r.
        Piauto.
        rewrite <- Ht.
        apply (Typing_Change_Side_RgLf _ D F (Bld y A ++ G) y A); try constructor; Piauto.
        admit. (* derivable *)
      * admit. (* revienta *)
      * admit. (* revienta *)
    - assert ( Hx : [if y =? x0 then BName 0 else FName y ←→ if x0 =? x0 then BName 0 else FName x0] =  Close_Rec 0 x0 ([FName y ←→ FName x0]) ). Piauto.
      rewrite Hx in H10.
      apply (IsClosingInj_inv _ _ x) in H14.
      rewrite <- H14 in *.
      apply (Close_Same_Inv _ _ x 0) in H10; Piauto.
      rewrite <- H10 in *.
      inversions H7.
      * contradiction.
      * contradiction. 
      * admit. (* revienta *)
      * admit. (* revienta *)
    - assert ( Hx : [if y =? x0 then BName 0 else FName y ←→ if x0 =? x0 then BName 0 else FName x0] =  Close_Rec 0 x0 ([FName y ←→ FName x0]) ). Piauto.
      rewrite Hx in H9.
      apply (IsClosingInj_inv _ _ x) in H14.
      rewrite <- H14 in *.
      apply (Close_Same_Inv _ _ x 0) in H9; Piauto.
      rewrite <- H9 in *.
      inversions H6.
      * admit. (* deducible *)
      * admit. (* revienta *)
      * admit. (* revienta *) 
    - assert ( Hx : [if x0 =? x0 then BName 0 else FName x0 ←→ if y =? x0 then BName 0 else FName y] =  Close_Rec 0 x0 ([FName x0 ←→ FName y]) ). Piauto.
      rewrite Hx in H9.
      apply (IsClosingInj_inv _ _ x) in H14.
      rewrite <- H14 in *.
      apply (Close_Same_Inv _ _ x 0) in H9; Piauto.
      rewrite <- H9 in *.
      inversions H6.
      * contradiction.
      * admit. (* revienta *)
      * admit. (* revienta *)
    - assert ( Hx : (if x0 =? x0 then BName 0 else FName x0) ·θ = Close_Rec 0 x0 (FName x0 ·θ) ). Piauto.
      rewrite Hx in H9.
      apply (IsClosingInj_inv _ _ x) in H15.
      rewrite <- H15 in *.
      apply (Close_Same_Inv _ _ x 0) in H9; Piauto.
      rewrite <- H9 in *.
      inversion H6.
      * subst.
        admit. (* revienta *)
      * subst.
        admit. (* revienta *)
      * assert ( Hy : (if x0 =? x0 then BName 0 else FName x0) ()·Close_Rec 0 x0 Q0 = Close_Rec 0 x0 ( FName x0 ()· Q0) ). Piauto.
        subst.
        rewrite Hy in H10.
        apply (Close_Same_Inv _ _ x0 0) in H10; Piauto.
        rewrite <- H10 in *.
        inversions H7.
        ** admit. (* cicla *)
        ** admit. (* derivable *)
        ** Piauto.
    - assert ( Hx : (if x0 =? x0 then BName 0 else FName x0) ·θ = Close_Rec 0 x0 (FName x0 ·θ) ). Piauto.
      rewrite Hx in H10.
      apply (IsClosingInj_inv _ _ x) in H15.
      rewrite <- H15 in *.
      apply (Close_Same_Inv _ _ x 0) in H10; Piauto.
      rewrite <- H10 in *.
      inversion H7.
      * subst.
        apply Subst_Change_Side in H14; Piauto.
        simpl in H14.
        DecidSimple x0 x0.
        rewrite e in H14.
        rewrite H14 in *.
        apply (No_Typing_Zero_Ord A0 u) in H32; try OrSearch; Piauto.
      * subst.
        apply Subst_Change_Side in H14; Piauto.
        simpl in H14.
        DecidSimple x0 x1.
        ** rewrite e in H14.
           rewrite H14 in *.
           apply (No_Typing_Zero_Ord A0 u) in H27; try OrSearch; Piauto.
        ** rewrite n in H14.
           admit.
      * assert ( Hy : (if x =? x then BName 0 else FName x) ()·Close_Rec 0 x Q0 = Close_Rec 0 x ( FName x ()· Q0) ). Piauto.
        subst.
        rewrite Hy in H9.
        apply (Close_Same_Inv _ _ x0 0) in H9; Piauto.
        rewrite <- H9 in *.
        inversions H6.
        ** admit. (* cicla *)
        ** do 2 rewrite app_nil_r.
           Piauto.
        ** admit. (* derivable *)
    - 
    - admit.
    - admit.
Admitted.



(*


(**
*)
Lemma Reduction_Cut_Two :
forall ( P Q Q0 : Process )( x : nat),
lc P -> lc Q ->
(ν Close x (P ↓ Q)) --> Q0 -> 

((exists (y:nat)(P0 : Process), Q = [FName x ←→ FName y] /\ Q0 = {y \ x} P0 ) \/
(exists (y:nat), Q = [FName y ←→ FName x]) \/
(exists (y:nat), P = [FName y ←→ FName x]) \/
(exists (y:nat), P = [FName x ←→ FName y]) \/
False).
Proof.
  intros.
  inversions H1.
  + left.
    exists y.
    exists P0.
    constructor.
    apply (Close_Same_Inv _ _ x 0); Piauto.
    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7 in *.
    Piauto.

    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7.
    Piauto.
  + right. left.
    exists y.
    apply (Close_Same_Inv _ _ x 0); Piauto.
    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7 in *.
    Piauto.
  + do 2 right. left.
    exists y.
    apply (Close_Same_Inv _ _ x 0); Piauto.
    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7 in *.
    Piauto.
  + do 3 right. left.
    exists y.
    apply (Close_Same_Inv _ _ x 0); Piauto.
    apply (IsClosingInj_inv _ _ x) in H7.
    rewrite H7 in *.
    Piauto.
  + admit.
  + admit.
Admitted.





(**
*)
Lemma Reduction_Cut_One :
forall (P Q Q0 : Process)(u x : nat),
lc P -> lc Q -> 
((ν Close u ((FName u !· Close x P) ↓ Q)) --> Q0) -> 

(exists ( y : nat), Q = [FName u ←→ FName y]) \/ 
(exists ( y : nat), Q = [FName y ←→ FName u]) \/ 
(exists ( y : nat)(R : Process), lc R /\ 
  Q = ν Close y ((FName u) « (FName y) »· R) /\ 
  Q0 = ν Close u ((FName u !· Close x P) ↓ (ν Close y (R ↓ (Close x P) ^ y))) 
  /\ IsClosing R y /\ IsClosingInj R y
  ) \/ 
(exists ( y : nat)(R : Process), lc R /\ 
  Q = ν Close y ((FName u) « (FName y) »· R) /\
  Q0 = ν Close u ((FName u !· Close x P) ↓ (ν Close y ((Close x P) ^ y ↓ R))) 
  /\ IsClosing R y /\ IsClosingInj R y
  )
.
Proof.
  intros.
  inversions H1.
  + left.
    exists y;
    apply (Close_Same_Inv _ _ u 0); Piauto.
    apply (IsClosingInj_inv _ _ u) in H7.
    rewrite H7 in *; Piauto.
  + right. left.
    exists y;
    apply (Close_Same_Inv _ _ u 0);
    apply (IsClosingInj_inv _ _ u) in H7;
    rewrite H7 in *; Piauto.
  + do 2 right. left.
    exists y.
    exists Q1.
    constructor; Piauto.
    constructor.
      apply (Close_Same_Inv _ _ u 0); Piauto.
      apply (IsClosingInj_inv _ _ u) in H13; Piauto.
      rewrite H13 in *; Piauto.
      
     constructor; ePiauto.
      apply (IsClosingInj_inv _ _ u) in H13; Piauto.
      rewrite H13 in *; Piauto.
      apply Close_Same_Inv in H3; Piauto.
      rewrite H3 in *; Piauto.
     
  + do 3 right.
    exists y.
    exists Q1.
    constructor; Piauto.
    constructor.
      apply (Close_Same_Inv _ _ u 0); Piauto.
      apply (IsClosingInj_inv _ _ u) in H13; Piauto.
      rewrite H13 in *; Piauto.
    
    constructor; ePiauto.
      apply (IsClosingInj_inv _ _ u) in H13; Piauto.
      rewrite H13 in *; Piauto.
      apply Close_Same_Inv in H3; Piauto.
      rewrite H3 in *; Piauto.
Qed.
#[global]
Hint Resolve Reduction_Cut_One : Piull.




*)
