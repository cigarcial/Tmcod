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
  destruct P0; try discriminate.
  inversions H2.
  inversions H4.
  inversions H1.
Qed.


Lemma Output_No_Reduces :
forall (u x: nat)(P Q : Process),
~( (ν Close x (FName u « FName x »· P)) --> Q ).
Proof.
  unfold not.
  intros.
  inversions H.
  destruct P0; try discriminate.
  inversions H2.
  inversions H4.
  inversions H1.
Qed.


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
  EasyDec x2 x0 e n; try rewrite n in H2; try discriminate.
  apply beq_nat_true in e.
  rewrite e; auto.
Qed.


Lemma Close_Same_Inv_Names :
forall ( x y : Name)(i x0 : nat),
lca_name i x -> lca_name i y ->
Close_Name i x0 x = Close_Name i x0 y -> x = y. 
Proof.
  intros.
  destruct x.
  + simpl in H1.
    EasyDec x x0 e n.
    - rewrite e in H1.
      destruct y.
      * simpl in H1.
        EasyDec x1 x0 e0 n.
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
        EasyDec x1 x0 e n0.
        rewrite e in H1.
        inversions H1.
        rewrite n0 in H1.
        inversions H1; auto.
      * simpl in H1.
        inversions H1.
  + simpl in H1.
    destruct y.
    - simpl in H1.
      EasyDec x x0 e n.
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


Lemma Close_Same_Inv :
forall ( P Q : Process )( x i : nat ),
lca i P -> lca i Q ->
Close_Rec i x P = Close_Rec i x Q -> P = Q.
Proof.
  induction P; intros; try destruct Q; try discriminate; auto.
  + simpl in H1.
    inversions H1.
    try inversions H; try inversions H0.
    apply Close_Same_Inv_Names in H3; auto.
    apply Close_Same_Inv_Names in H4; auto.
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


Hypothesis Close_Susbst_Beh : forall(P P0: Process)(x y z: nat), P = Close x P0 -> x <> y.


(*
Teorema 2.1 del artículo.
*)
Theorem SoundnessX : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P === Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros P D F G H Q HA.
  dependent induction H; try inversions HA.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.
  

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
  + inversions H8.
    - destruct P0; try discriminate.
      destruct P0_1; try discriminate.
      specialize (Extl2 _ _ _ _ _ _ _ x1 H10 H9) as Ht.
      assert ( Hx : x0 = u ). admit.
      subst.
      apply Close_Same_Inv in H9.
      rewrite H9 in H11.
      inversion H11.
      * admit.
      * admit.
      * dependent induction H13.
        ** inversion H15.
           admit.
           inversions H21; inversions H23.
           
        ** 
      * admit. (* facil *)
      * admit. (* facil *)
    - inversions H10.
      specialize (beq_nat_refl u) as Hx.
      apply eq_sym in Hx.
      rewrite Hx in *.
      inversions H15.
      inversions H16.
Admitted.


Lemma Close_Inv_Names :
forall (x x1 : Name)(i x0 y0 : nat),
lca_name i x -> lca_name i x1 ->
Close_Name i x0 x = Close_Name i y0 x1 -> x = x1 \/ x = Subst_Name y0 x0 x1.
Proof.
  intros.
  destruct x.
  + simpl in H1.
    EasyDec x x0 e n.
    - rewrite e in H1.
      destruct x1.
      * simpl in H1.
        EasyDec x1 y0 e n.
        ++ rewrite e0.
            apply beq_nat_true in e.
            rewrite e.
            auto.
        ++ rewrite n in H1.
           inversions H1.
      * simpl in H1.
        inversion H1.
        inversions H0.
        lia.
    - rewrite n in H1.
      destruct x1.
      * simpl in H1.
        EasyDec x1 y0 e0 n0.
        ++ rewrite e in H1.
           inversions H1.
        ++ rewrite n0 in H1.
           inversions H1.
           auto.
      * simpl in H1.
        inversion H1.
  + simpl in H1.
    destruct x1.
    - simpl in H1.
      EasyDec x y0 e n.
      * rewrite e in H1.
        inversions H.
        inversion H1.
        lia.
      * rewrite n in H1; inversions H1.
    - simpl in H1.
      inversions H1.
      auto.
Qed.



Lemma Exl :
forall ( P Q Q0 : Process )( u x : nat),
(ν Close u ((FName u !· Close x P) ↓ Q)) --> Q0
-> Q0 = P.
Proof.
  intros.
  inversions H.
  + destruct P0; try discriminate.
    destruct P0_1; try discriminate.
    specialize (Extl2 _ _ _ _ _ _ _ x1 H1 H0) as Ht.
    rewrite Ht in H0.
    inversions H2.
    - admit.
    - admit.
    - inversion H4.
      * destruct Q0; try discriminate.
        inversions H9.
        inversions H6.
        ** admit.
        ** inversions H13.
           inversions H8.
(* 
    admit.
  + inversions H1.
    specialize (beq_nat_refl u) as Hx.
    apply eq_sym in Hx.
    rewrite Hx in *.
    inversions H6.
    inversions H7. *)
Admitted.

