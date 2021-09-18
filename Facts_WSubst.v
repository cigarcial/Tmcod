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
From Tmcod Require Import Defs_Typing.


From Tmcod Require Import Facts_Names.
From Tmcod Require Import Facts_FVars.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Props_Process.

(*
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
  right.
  auto.
  inversions H; auto.
Qed.


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
  right.
  auto.
  inversions H; auto.
Qed.

Lemma Well_Subst_Chan_Res :
forall ( P : Process )( u x : nat),
Well_Subst (ν P) u x -> Well_Subst P u x.
Proof.
  constructor.
  unfold not.
  intros.
  inversions H.
  apply H1.
  simpl.
  auto.
  inversions H; auto.
Qed.



(*
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
    - inversions H.
      left.
      apply In_FVars_Name_Subst in H1.
      destruct H1.
      rewrite H1.
      simpl.
      constructor.
      contradiction.
    - inversions H2.
      apply In_FVars_Name_Subst in H1.
      destruct H1.
      rewrite H1.
      right.
      simpl.
      constructor.
      contradiction.
  + inversions H0.
    apply No_FVars_Parallel in H3.
    destruct H3 as [HA HB].
    simpl in H1.
    inversions H1.
    apply IHlc1; try constructor; auto.
    apply IHlc2; try constructor; auto.
  + simpl in H1.
    inversions H0.
    apply H4.
    simpl.
    apply Union_inv in H1.
    destruct H1.
    - apply Union_inv in H1.
      destruct H1.
      * inversions H.
        apply In_FVars_Name_Subst in H1.
        destruct H1.
        rewrite H1.
        left. left.
        simpl.
        constructor.
        contradiction.
      * inversions H2.
        apply In_FVars_Name_Subst in H1.
        destruct H1.
        rewrite H1.
        left. right.
        simpl.
        constructor.
        contradiction.
    - apply Well_Subst_Chan_Output in H0.
      specialize (IHlc H0 H1).
      contradiction.
  + inversions H0.
    apply H2.
    simpl.
    simpl in H1.
    inversions H.
    apply In_FVars_Name_Subst in H1.
    destruct H1.
    rewrite H1.
    simpl.
    constructor.
    contradiction.
  + inversions H0.
    apply H3.
    simpl.
    simpl in H1.
    apply Union_inv in H1.
    destruct H1.
    - inversions H.
      apply In_FVars_Name_Subst in H1.
      destruct H1.
      rewrite H1.
      simpl.
      left.
      constructor.
      contradiction.
    - apply Well_Subst_Chan_Close in H0.
      specialize (IHlc H0 H1).
      contradiction.
  + simpl in H1.
    inversions H0.
    apply (After_Subst_No_FVar P u x); auto.
  + inversions H0.
    apply H4.
    simpl.
    simpl in H1.
    apply Union_inv in H1.
    destruct H1.
    - inversions H.
      apply In_FVars_Name_Subst in H1.
      destruct H1.
      rewrite H1.
      simpl.
      left.
      constructor.
      contradiction.
    - apply (After_Subst_No_FVar P u x) in H1; auto.
      contradiction.
  + inversions H0.
    apply H4.
    simpl.
    simpl in H1.
    apply Union_inv in H1.
    destruct H1.
    - inversions H.
      apply In_FVars_Name_Subst in H1.
      destruct H1.
      rewrite H1.
      simpl.
      left.
      constructor.
      contradiction.
    - apply (After_Subst_No_FVar P u x) in H1; auto.
      contradiction.
  + inversions H0.
    auto.
Qed.



Lemma Well_Subst_Reduction_Susbt :
forall ( P Q : Process)(x u : nat),
Well_Subst P x u -> lc P ->
( P --> Q ) ->  ( ({u \ x}P) --> ({u \ x} Q)).
Proof.
  intros.
  assert (HA := H1).
  dependent induction H1.
  + simpl.
    destruct (bool_dec (x0 =? x) true).
    - destruct (bool_dec (y =? x) true).
      * rewrite e. rewrite e0.
        apply beq_nat_true in e.
        apply beq_nat_true in e0.
        rewrite e0.
        rewrite Subst_Open_Eq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
      * rewrite e. 
        apply not_true_iff_false in n. rewrite n.
        rewrite <- Subst_Open_NEq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        apply beq_nat_false in n.
        auto.
    - destruct (bool_dec (y =? x) true).
      * rewrite e.
        apply not_true_iff_false in n. rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        rewrite Subst_Open_Eq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
      * apply not_true_iff_false in n. rewrite n.
        apply not_true_iff_false in n0. rewrite n0.
        rewrite <- Subst_Open_NEq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        apply beq_nat_false in n0.
        auto.
  + simpl.
    destruct (bool_dec (x0 =? x) true).
    - destruct (bool_dec (y =? x) true).
      * rewrite e. rewrite e0.
        apply beq_nat_true in e.
        apply beq_nat_true in e0.
        rewrite e0.
        rewrite Subst_Open_Eq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
      * rewrite e. 
        apply not_true_iff_false in n. rewrite n.
        rewrite <- Subst_Open_NEq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        apply beq_nat_false in n.
        auto.
    - destruct (bool_dec (y =? x) true).
      * rewrite e.
        apply not_true_iff_false in n. rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        rewrite Subst_Open_Eq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
      * apply not_true_iff_false in n. rewrite n.
        apply not_true_iff_false in n0. rewrite n0.
        rewrite <- Subst_Open_NEq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        apply beq_nat_false in n0.
        auto.
  + simpl.
    destruct (bool_dec (x0 =? x) true).
    - rewrite e.
      constructor.
      apply Subst_Lc_Lc; auto.
    - apply not_true_iff_false in n; rewrite n.
      constructor.
      apply Subst_Lc_Lc; auto.
  + simpl.
    destruct (bool_dec (x0 =? x) true).
    - destruct (bool_dec (y =? x) true).
      * rewrite e. rewrite e0.
        apply beq_nat_true in e.
        apply beq_nat_true in e0.
        rewrite e. rewrite e0.
        rewrite <- (Subst_By_Equal ({u \ x} ({x \ x} P)) u).
        rewrite (Subst_By_Equal P _ ).
        constructor.
        apply Subst_Lc_Lc; auto.
      * rewrite e. 
        apply not_true_iff_false in n; rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        apply beq_nat_false in n.
        rewrite Double_Subst_AlreadySubst_Eq; auto.
        inversions H.
        rewrite (Double_Subst_Expan_NFVar P x y u); auto.
        constructor.
        apply Subst_Lc_Lc; auto.
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
        constructor; auto.
        apply Subst_Lc_Lc; auto.
      * apply not_true_iff_false in n. rewrite n.
        apply not_true_iff_false in n0. rewrite n0.
        inversions H.
        apply beq_nat_false in n.
        apply beq_nat_false in n0.
        rewrite Double_Subst_All_Dif; auto.
        constructor.
        apply Subst_Lc_Lc; auto.
        unfold not.
        intros.
        apply H2.
        right.
        rewrite H4.
        simpl.
        left; constructor.
  + simpl.
    constructor.
    apply Subst_Lc_Lc; auto.
    apply Subst_Lc_Lc; auto.
    apply IHReduction; auto.
    inversions H.
    constructor; auto.
    unfold not in *.
    intros.
    apply H4.
    right.
    auto.
    inversions H0; auto.
  + simpl.
    destruct (bool_dec (x =? x0) true).
    - apply beq_nat_true in e.
      rewrite e.
      unfold Close.
      do 2 rewrite Subst_Close_By_Equal_Name.
      constructor; auto.
    - destruct (bool_dec (u =? x0) true).
      * admit. (* imposible by construction - pi calculus *)
      * apply not_true_iff_false in n.
        apply not_true_iff_false in n0.
        apply beq_nat_false in n.
        apply beq_nat_false in n0.
        unfold Close.
        rewrite Subst_Close_Dif_Name; auto.
        rewrite Subst_Close_Dif_Name; auto.
        constructor; auto.
        apply Subst_Lc_Lc; auto.
        apply IHReduction; auto.
        inversions H.
        constructor; auto.
        unfold not.
        intros.
        apply H3.
        simpl.
        apply FVars_Close_Beq; auto.
  + assert (HX : Well_Subst P' x u).
    inversions H.
    constructor; auto.
    specialize (Cong_FVars P' P H2) as HT.
    rewrite HT; auto.
    apply (Cong_Subst_Cong _ _ x u) in H2.
    apply (Cong_Subst_Cong _ _ x u) in H3.
    apply (Red_reduction_struct _ _ ({u \ x} P') ({u \ x} Q')); auto.
    apply Subst_Lc_Lc; auto.
Admitted.



(*
*)
Lemma Double_WSubst_Equality_Names :
forall (x : Name)(x0 u : nat),
~ x0 ∈ FVars_Name x -> 
Subst_Name x0 u (Subst_Name u x0 x) = x.
Proof.
  destruct x; intros; simpl; auto.
  simpl in H.
  assert( HA : x <> x0).
    unfold not in *.
    intros.
    apply H.
    rewrite H0; constructor.
  EasyDec x u e n.
  + specialize (beq_nat_refl x0) as Hx.
    apply eq_sym in Hx.
    rewrite Hx.
    apply beq_nat_true in e.
    rewrite e; auto.
  + apply beq_nat_false_inv in HA.
    rewrite HA.
    auto.
Qed.




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


Lemma Well_Subst_Red_Well_Subst :
forall (P Q : Process)(u x : nat),
Well_Subst P u x -> P --> Q -> 
Well_Subst Q u x.
Proof.
  intros.
  dependent induction H0; try inversions H; try constructor; auto.
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
    EasyDec x x0 e n.
    - admit. (* Impossible by construction - pi calculus *)
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
Admitted.
