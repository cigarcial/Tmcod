(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the tactis and Hint Db for the proofs.
*)
Require Import Coq.Program.Equality.

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Sets.Constructive_sets.

From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Typing.
From Tmcod Require Import Facts_Names.
From Tmcod Require Import Facts_FVars.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Props_Process.


(**
*)
Lemma Well_Subst_Chan_Output :
forall (P : Process)(x0 y : Name)( u x : nat),
Well_Subst (x0 « y »· P) u x -> Well_Subst (P) u x.
Proof.
  intros.
  constructor.
  inversions H.
  unfold not.
  intros.
  apply H0.
  simpl.
  OrSearch.
  inversions H; auto.
Qed.
#[global]
Hint Resolve Well_Subst_Chan_Output : Piull.


(**
*)
Lemma Well_Subst_Chan_Close :
forall (P : Process)(x0 : Name)( u x : nat),
Well_Subst (x0 ()·P) u x -> Well_Subst P u x.
Proof.
  constructor.
  unfold not.
  intros.
  inversions H.
  apply H1.
  simpl.
  OrSearch.
  inversions H; auto.
Qed.
#[global]
Hint Resolve Well_Subst_Chan_Close : Piull.


(**
*)
Lemma Well_Subst_Chan_Res :
forall ( P : Process )( u x : nat),
Well_Subst (ν P) u x -> Well_Subst P u x.
Proof.
  constructor.
  unfold not.
  intros.
  inversions H.
  apply H1.
  Piauto.
  inversions H; auto.
Qed.
#[global]
Hint Resolve Well_Subst_Chan_Res : Piull.

Ltac Aux_Ltac_1 H H1 :=
  inversions H;
  apply In_FVars_Name_Subst in H1;
  destruct H1;
  (rewrite H1;
  simpl;
  OrSearch) + (contradiction).


(**
*)
Lemma Lc_WSubst_Subst_WSubst :
forall (P : Process)( u x : nat),
lc P -> Well_Subst P u x -> 
Well_Subst ({x \ u} P) x u.
Proof.
  intros.
  constructor; auto.
  unfold not.
  intro.
  induction H.
  + simpl in H1.
    contradiction.
  + inversions H0.
    simpl in H3.
    simpl in H1.
    apply Union_inv in H1.
    apply H3.
    destruct H1.
    - Aux_Ltac_1 H H1.
    - Aux_Ltac_1 H2 H1.
  + inversions H0.
    apply No_FVars_Parallel in H3.
    destruct H3 as [HA HB].
    simpl in H1.
    inversions H1; Piauto.
  + simpl in H1.
    inversions H0.
    apply H4.
    simpl.
    apply Union_inv in H1.
    destruct H1.
    - apply Union_inv in H1.
      destruct H1.
      * Aux_Ltac_1 H H1.
      * Aux_Ltac_1 H2 H1.
    - apply Well_Subst_Chan_Output in H0.
      specialize (IHlc H0 H1).
      contradiction.
  + inversions H0.
    apply H2.
    simpl in *.
    Aux_Ltac_1 H H1.
  + inversions H0.
    apply H3.
    simpl in *.
    apply Union_inv in H1.
    destruct H1.
    - Aux_Ltac_1 H H1.
    - apply Well_Subst_Chan_Close in H0.
      specialize (IHlc H0 H1).
      contradiction.
  + simpl in H1.
    inversions H0.
    apply (After_Subst_No_FVar P u x); auto.
  + inversions H0.
    apply H4.
    simpl in *.
    apply Union_inv in H1.
    destruct H1.
    - Aux_Ltac_1 H H1.
    - apply (After_Subst_No_FVar P u x) in H1; auto.
      contradiction.
  + inversions H0.
    apply H4.
    simpl in *.
    apply Union_inv in H1.
    destruct H1.
    - Aux_Ltac_1 H H1.
    - apply (After_Subst_No_FVar P u x) in H1; auto.
      contradiction.
  + inversions H0.
    auto.
Qed.
#[global]
Hint Resolve Lc_WSubst_Subst_WSubst : Piull.


(** FVars_Subst
*)
Lemma Beq_NFVars_Subst :
forall ( Q : Process )( u x0 x: nat ),
u <> x0 -> ~ x0 ∈ FVars Q -> 
~ x0 ∈ FVars ({u \ x} Q).
Proof.
  intros.
  unfold not.
  intros.
  apply FVars_Subst in H1.
  destruct H1.
  Piauto.
  contradiction.
Qed.
#[global]
Hint Resolve Beq_NFVars_Subst : Piull.


(**
*)
Lemma Beq_FVars_Subst : 
forall ( P : Process )( x0 x u : nat ),
x0 <> x -> x0 ∈ FVars P ->
x0 ∈ FVars ({u \ x} P).
Proof.
Admitted.
#[global]
Hint Resolve Beq_FVars_Subst : Piull.


(**
*)
Lemma In_FVars_Subst : 
forall ( P : Process )( x0 x u : nat ),
x0 ∈ FVars P -> u ∈ FVars ({u \ x} P).
Proof.
Admitted.
#[global]
Hint Resolve In_FVars_Subst : Piull.


(** Subst_Close_Dif_Name
*)
Lemma Subst_Reduction_NBeq :
forall ( P Q : Process)(x u : nat),
lc P -> u <> x ->
( P --> Q ) -> ( ({u \ x}P) --> ({u \ x} Q) ).
Proof.
  intros.
  induction H1.
  + specialize (IsClosing_inv P x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} ([FName x0 ←→ FName y])).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    - apply beq_nat_true in e.
      rewrite e.
      rewrite Double_Subst_By_Same_Name.
      constructor; eauto with Piull.
    - rewrite n0.
      apply beq_nat_false in n0.
      rewrite Double_Subst_All_Dif; Piauto.
      constructor; eauto with Piull.
  + specialize (IsClosing_inv P x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} ([FName y ←→ FName x0])).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    - apply beq_nat_true in e.
      rewrite e.
      rewrite Double_Subst_By_Same_Name.
      constructor; eauto with Piull.
    - rewrite n0.
      apply beq_nat_false in n0.
      rewrite Double_Subst_All_Dif; Piauto.
      constructor; eauto with Piull.
  + specialize (IsClosing_inv P x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} ([FName y ←→ FName x0])).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    - apply beq_nat_true in e.
      rewrite e.
      rewrite Double_Subst_By_Same_Name.
      constructor; eauto with Piull.
    - rewrite n0.
      apply beq_nat_false in n0.
      rewrite Double_Subst_All_Dif; Piauto.
      constructor; eauto with Piull.
  + specialize (IsClosing_inv P x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} ([FName x0 ←→ FName y])).
    DecidSimple x0 x.
    rewrite n.
    DecidSimple y x.
    - apply beq_nat_true in e.
      rewrite e.
      rewrite Double_Subst_By_Same_Name.
      constructor; eauto with Piull.
    - rewrite n0.
      apply beq_nat_false in n0.
      rewrite Double_Subst_All_Dif; Piauto.
      constructor; eauto with Piull.
  + specialize (IsClosing_inv Q x0 u x H3) as Hx.
    destruct Hx.
    rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Parallel.
    simpl ({u \ x} (FName x0 ·θ) ).
    simpl ({u \ x} (FName x0 ()·Q) ).
    DecidSimple x0 x.
    rewrite n.
    constructor; eauto with Piull.
  + admit.
  + specialize (IsClosing_inv P u0 u x H6) as Hx.
    destruct Hx.
    specialize (IsClosing_inv P y u x H7) as Hx.
    destruct Hx.
    do 2 rewrite Subst_Res.
    unfold Close.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 rewrite Subst_Parallel.
    do 2 rewrite Subst_Res.
    rewrite Subst_Close_Dif_Name; Piauto.
    rewrite Subst_Close_Dif_Name; Piauto.
    do 2 simpl ({u \ x} (FName u0 !· P)).
    simpl ({u \ x} (FName u0 « FName y »· Q)).
    DecidSimple u0 x.
    rewrite n.
    DecidSimple y x.
    rewrite n0.
    rewrite Subst_Parallel.
    rewrite <- Subst_Open_NEq_Exchange; Piauto.
    constructor; eauto with Piull.
  + admit.
Admitted.
#[global]
Hint Resolve Subst_Reduction_NBeq : Piull.









 (* 
  assert (HA := H1).
  
  
  
  dependent induction H1; simpl; Piauto.
  + DecidSimple x0 x0; Piauto.
    DecidSimple y x0; Piauto.
    - simpl.
  
    - DecidSimple y x; Piauto.
      * rewrite e.
        
        rewrite <- (Subst_By_Equal ({u \ x} ({y \ x0} P)) u).
        apply beq_nat_true in e0.
        rewrite e0.
        apply beq_nat_true in e.
        rewrite e.
        rewrite (Subst_By_Equal P x).
        Piauto.
      * rewrite n.
        apply beq_nat_true in e.
        apply beq_nat_false in n.
        rewrite e.
        rewrite Double_Subst_AlreadySubst_Eq; auto.
        apply No_FVars_Parallel in H0.
        destruct H0.
        rewrite (Double_Subst_Expan_NFVar P x y u); auto.
        constructor; Piauto.
    - DecidSimple y x; Piauto.
      * rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        rewrite Double_Subst_By_Same_Name.
        Piauto.
      * rewrite n.
        rewrite n0.
        apply beq_nat_false in n.
        apply beq_nat_false in n0.
        rewrite Double_Subst_All_Dif; auto.
        constructor; Piauto.
        (* se puede derivar *)
        admit.  
  
  
  + DecidSimple x0 x; Piauto.
    - DecidSimple y x; Piauto.
      * apply beq_nat_true in e0.
        rewrite e0.
        rewrite Subst_Open_Eq_Exchange.
        Piauto.
      * rewrite n.
        rewrite <- Subst_Open_NEq_Exchange.
        Piauto.
        apply beq_nat_false in n.
        auto.
    - DecidSimple y x; Piauto.
      * rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        rewrite Subst_Open_Eq_Exchange.
        Piauto.
      * rewrite n. rewrite n0.
        rewrite <- Subst_Open_NEq_Exchange.
        Piauto.
        apply beq_nat_false in n0.
        auto.
  + destruct (bool_dec (x0 =? x) true).
    - destruct (bool_dec (y =? x) true).
      * rewrite e. rewrite e0.
        apply beq_nat_true in e.
        apply beq_nat_true in e0.
        rewrite e0.
        rewrite Subst_Open_Eq_Exchange.
        Piauto.
      * rewrite e.
        apply not_true_iff_false in n. rewrite n.
        rewrite <- Subst_Open_NEq_Exchange.
        Piauto.
        apply beq_nat_false in n; auto.
    - destruct (bool_dec (y =? x) true).
      * rewrite e.
        apply not_true_iff_false in n. rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        rewrite Subst_Open_Eq_Exchange.
        constructor; Piauto.
      * apply not_true_iff_false in n. rewrite n.
        apply not_true_iff_false in n0. rewrite n0.
        rewrite <- Subst_Open_NEq_Exchange.
        Piauto.
        apply beq_nat_false in n0.
        auto.
  + 
  + destruct (bool_dec (x0 =? x) true).
    - destruct (bool_dec (y =? x) true).
      * rewrite e. rewrite e0.
        apply beq_nat_true in e.
        apply beq_nat_true in e0.
        rewrite e. rewrite e0.
        rewrite <- (Subst_By_Equal ({u \ x} ({x \ x} P)) u).
        rewrite (Subst_By_Equal P _ ).
        Piauto.
      * rewrite e.
        apply not_true_iff_false in n; rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        apply beq_nat_false in n.
        rewrite Double_Subst_AlreadySubst_Eq; auto.
        inversions H.
        rewrite (Double_Subst_Expan_NFVar P x y u); auto.
        constructor; Piauto.
        inversions H0.
        unfold not in *.
        intros.
        apply H2.
        constructor; auto.
    - destruct (bool_dec (y =? x) true).
      * rewrite e.
        apply not_true_iff_false in n; rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        rewrite Double_Subst_By_Same_Name.
        Piauto.
      * apply not_true_iff_false in n. rewrite n.
        apply not_true_iff_false in n0. rewrite n0.
        inversions H.
        apply beq_nat_false in n.
        apply beq_nat_false in n0.
        rewrite Double_Subst_All_Dif; auto.
        constructor; Piauto.
        unfold not.
        intros.
        apply H2.
        rewrite H4.
        simpl.
        OrSearch.
  + constructor; Piauto.
    apply IHReduction; Piauto.
    inversions H.
    constructor; auto.
    unfold not in *.
    intros.
    apply H4.
    OrSearch.
    inversions H0; auto.
  + destruct (bool_dec (x =? x0) true).
    - apply beq_nat_true in e.
      rewrite e.
      unfold Close.
      do 2 rewrite Subst_Close_By_Equal_Name.
      Piauto.
    - destruct (bool_dec (u =? x0) true).
      * (* Impossible by construction - pi calculus *)
        inversions H.
        simpl in H3.
        specialize (Close_Subst_Beh P x0 x u) as Hx.
        exfalso.
        apply beq_nat_true in e.
        apply Hx; Piauto.
      * apply not_true_iff_false in n.
        apply not_true_iff_false in n0.
        apply beq_nat_false in n.
        apply beq_nat_false in n0.
        unfold Close.
        rewrite Subst_Close_Dif_Name; Piauto.
        rewrite Subst_Close_Dif_Name; Piauto.
        constructor; Piauto.
        apply IHReduction; auto.
        inversions H.
        constructor; Piauto.
        unfold not.
        intros.
        apply H3.
        simpl.
        apply FVars_Close_Beq; auto.
  + assert (HX : Well_Subst P' x u).
    inversions H.
    constructor; Piauto.
    specialize (Cong_FVars P' P H2) as HT.
    rewrite HT; eauto with *.
    apply (Cong_Subst_Cong _ _ x u) in H2.
    apply (Cong_Subst_Cong _ _ x u) in H3.
    apply (Red_reduction_struct _ _ ({u \ x} P') ({u \ x} Q')); Piauto.
Qed.
#[global]
Hint Resolve Well_Subst_Reduction_Susbt : Piull.


(**
*)
Lemma Double_WSubst_Equality_Names :
forall (x : Name)(x0 u : nat),
~ x0 ∈ FVars_Name x -> 
Subst_Name x0 u (Subst_Name u x0 x) = x.
Proof.
  destruct x; intros; simpl; Piauto.
  simpl in H.
  assert( HA : x <> x0).
    unfold not in *.
    intros.
    apply H.
    rewrite H0; constructor.
  simpl.
  DecidSimple x u.
  + simpl.
    DecidSimple x0 x0.
    apply beq_nat_true in e.
    Piauto.
  + rewrite n.
    simpl.
    apply beq_nat_false_inv in HA.
    rewrite HA.
    auto.
Qed.
#[global]
Hint Resolve Double_WSubst_Equality_Names : Piull.


(**
*)
Lemma Double_WSubst_Equality :
forall (P : Process)( x u : nat),
Well_Subst P u x -> ({u \ x} ({x \ u} P)) = P.
Proof.
  intro.
  dependent induction P; intros; simpl; inversions H;
    try simpl in H0;
    try apply No_Union_No_Each in H0;
    try destruct H0 as [HA HC];
    repeat rewrite Double_WSubst_Equality_Names;
    try rewrite IHP1; try constructor;
    try rewrite IHP2; try constructor;
    try rewrite IHP;
    try constructor;
    auto.
  + apply No_Union_No_Each in HA;
    destruct HA as [HA HB]; auto.
  + apply No_Union_No_Each in HA;
    destruct HA as [HA HB]; auto.
Qed.
#[global]
Hint Resolve Double_WSubst_Equality : Piull.

(* 
(**
*)
Lemma Well_Subst_Red_Well_Subst :
forall (P Q : Process)(u x : nat),
Well_Subst P u x -> P --> Q -> 
Well_Subst Q u x.
Proof.
  intros.
  dependent induction H0; try inversions H; try constructor; Piauto.
  + unfold not.
    intros.
    simpl in H4.
    apply Union_inv in H4.
    simpl in H2.
    apply No_Union_No_Each in H2.
    destruct H2 as [HA HD].
    apply No_Union_No_Each in HA.
    destruct HA as [HA HC].
    destruct H4.
    - contradiction.
    - apply FVars_Open in H2.
      destruct H2.
      * apply No_Union_No_Each in HA.
        destruct HA as [HA HB].
        rewrite H2 in HB.
        assert ( Hx : y <> y ).
          unfold not.
          intros.
          apply HB.
          constructor.
        contradiction.
      * apply No_Union_No_Each in HD.
        destruct HD as [HD HE].
        auto.
  + unfold not.
    intro.
    simpl in H2.
    apply No_Union_No_Each in H2.
    destruct H2 as [HA HD].
    apply No_Union_No_Each in HA.
    destruct HA as [HA HC].
    apply No_Union_No_Each in HA.
    destruct HA as [HA HB].
    apply No_Union_No_Each in HD.
    destruct HD as [HD HE]; auto.
    simpl in H4.
    apply Union_inv in H4.
    destruct H4.
    - apply Union_inv in H2.
      destruct H2; auto.
      apply FVars_Open in H2.
      destruct H2; auto.
      rewrite H2 in HB.
      assert ( Hx : y <> y ).
        unfold not.
        intros.
        apply HB.
        constructor.
      contradiction.
    - apply Union_inv in H2.
      destruct H2; auto.
  + unfold not.
    intros.
    simpl in H1.
    apply No_Union_No_Each in H1.
    destruct H1 as [HA HC].
    apply No_Union_No_Each in HC.
    destruct HC as [HB HC].
    contradiction.
  + unfold not.
    intros.
    simpl in H1.
    apply No_Union_No_Each in H1.
    destruct H1 as [HA HC].
    apply No_Union_No_Each in HC.
    destruct HC as [HB HC].
    apply FVars_Subst in H3.
    destruct H3.
    - rewrite H1 in HC. 
      apply HC.
      constructor.
    - apply HA; auto.
  + unfold not.
    intros.
    simpl in H5.
    apply Union_inv in H5.
    simpl in H3.
    apply No_Union_No_Each in H3.
    destruct H3 as [HA HB].
    destruct H5.
    - contradiction.
    - assert (Hx : Well_Subst Q u x); try constructor; auto.
      apply IHReduction in Hx.
      inversions Hx.
      contradiction.
  + unfold not.
    intros.
    simpl in H3.
    simpl in H4.
    DecidSimple x x0.
    - (* Impossible by construction - pi calculus *)
      inversions H.
      simpl in H5.
      specialize (Close_Subst_Beh P x0 u x) as Hx.
      exfalso.
      apply beq_nat_true in e.
      apply Hx; Piauto.
    - apply beq_nat_false in n.
      specialize (FVars_Beq_Close Q x x0 _ n H4) as Hx.
      specialize (FVars_Close_NotIn P x x0 0 n H2) as Ht.
      assert ( Hz : Well_Subst P u x ); try constructor; auto.
      apply IHReduction in Hz.
      inversions Hz; auto.
  + unfold not.
    intros.
    specialize ( Cong_FVars P' P H1) as Hc1.
    specialize ( Cong_FVars Q' Q H2) as Hc2.
    rewrite <- Hc1 in H4.
    rewrite <- Hc2 in H6.
    assert (Hx : Well_Subst P' u x); try constructor; auto.
    apply IHReduction in Hx.
    inversions Hx.
    contradiction.
Qed.
#[global]
Hint Resolve Well_Subst_Red_Well_Subst : Piull.
 *) *)
