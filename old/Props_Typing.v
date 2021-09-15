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

From old Require Import Defs_Typing.
From old Require Import Defs_Process.
From old Require Import Defs_Proposition.
From old Require Import Props_Process.
From old Require Import Facts_MOpen.
From old Require Import Defs_Tactics.


Lemma FVar_Process_Is_Or_Not :
forall (P : Process)( x : nat),
(x ∈ FVars P) \/ (~ x ∈ FVars P).
Admitted.

Lemma FVars_Bex_Name :
forall ( x : Name)(i j : nat),
FVars_Name (Bex_Name i j x) = FVars_Name x.
Proof.
  destruct x; intros; simpl; auto.
  destruct (bool_dec (i =? i0) true).
  + rewrite e.
    auto.
  + apply not_true_iff_false in n.
    rewrite n.
    destruct (bool_dec (i =? j) true).
    * rewrite e.
      auto.
    * apply not_true_iff_false in n0.
      rewrite n0.
      auto.
Qed.




Lemma FVars_Bex_Process:
forall (P : Process)(i j : nat),
FVars P = FVars ({i <~> j} P).
Proof.
    induction P; 
      intros;
      try simpl;
      try rewrite FVars_Bex_Name;
      try rewrite FVars_Bex_Name;
      try rewrite <- IHP1;
      try rewrite <- IHP2;
      try rewrite <- IHP;
      auto.
Qed.


(*
*)
Lemma Cong_FVars :
forall (P Q : Process), 
P === Q -> FVars P = FVars Q.
Proof.
  intros.
  induction H.
  + simpl.
    apply Extensionality_Ensembles.
    constructor.
    - unfold Included. 
      intros.
      apply Union_inv in H.
      destruct H.
      right. auto.
      left. auto.
    - unfold Included. 
      intros.
      apply Union_inv in H.
      destruct H.
      right. auto.
      left. auto.
  + simpl.
    apply FVars_Bex_Process.  
  + simpl.
    apply Extensionality_Ensembles.
    constructor.
    - unfold Included.
      intros.
      apply Union_inv in H.
      destruct H.
      apply Union_inv in H.
      destruct H.
      left. auto.
      right. left. auto.
      right. right. auto.
    - unfold Included.
      intros.
      apply Union_inv in H.
      destruct H.
      left. left. auto.
      apply Union_inv in H.
      destruct H.
      left. right. auto.
      right. auto.
  + auto.
Qed.


Lemma No_FVars_Parallel :
forall (P Q : Process)( u : nat),
( ~(u ∈ FVars (P ↓ Q))) -> (~ u ∈ FVars P) /\ (~ u ∈ FVars Q).
Proof.
  unfold not.
  intros.
  constructor.
  + intros.
    assert ( HA : u ∈ FVars (P ↓ Q));
      try constructor; auto.
  + intros.
    assert ( HA : u ∈ FVars (P ↓ Q));
      try right; auto.
Qed.

Lemma In_FVars_Name_Subst :
forall (u x x1 : nat),
u ∈ FVars_Name (Subst_Name u x (FName x1)) -> 
x = x1 \/ u <> u.
Proof.
  intros.
  simpl in H.
  destruct (bool_dec (x1 =? u) true).
  * rewrite e in H.
    simpl in H.
    apply Singleton_inv in H.
    apply beq_nat_true in e.
    rewrite e.
    left.
    auto.
  * apply not_true_iff_false in n.
    rewrite n in H.
    simpl in H.
    apply Singleton_inv in H.
    rewrite H in n.
    apply beq_nat_false in n.
    contradiction.
Qed.


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
Lemma Subst_Name_Gen_Output :
forall (u x0 : nat)(x : Name),
u <> x0 -> 
u ∈ FVars_Name (Subst_Name u x0 x) -> False.
Proof.
  intros.
  destruct x.
  + simpl in H0.
    destruct (bool_dec (x =? u) true).
    - rewrite e in H0. simpl in H0.
      apply Singleton_inv in H0.
      auto.
    - apply not_true_iff_false in n.
      rewrite n in H0.
      simpl in H0.
      apply Singleton_inv in H0.
      apply beq_nat_false in n.
      auto.
  + simpl in H0.
    inversions H0.
Qed.


(*
*)
Lemma After_Subst_No_FVar :
forall (P : Process)(u x : nat),
u <> x -> 
u ∈ FVars ({x \ u} P) -> False.
Proof.
  intro.
  dependent induction P; intros; try simpl in H0.
  + inversions H0.
  + apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (Subst_Name_Gen_Output u x0 y); auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply (IHP1 u x); auto.
    - apply (IHP2 u x); auto.
  + apply Union_inv in H0.
    destruct H0.
    apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (Subst_Name_Gen_Output u x0 y); auto.
    - apply (IHP u x0); auto.
  + apply (Subst_Name_Gen_Output u x0 x); auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (IHP u x0); auto.
  + apply (IHP u x); auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (IHP u x0); auto.
  + apply Union_inv in H0.
    destruct H0.
    - apply (Subst_Name_Gen_Output u x0 x); auto.
    - apply (IHP u x0); auto.
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


(*
*)
Lemma Subst_Bex_Exchange_Name :
forall (N : Name)(x u i j : nat),
i <> j -> Subst_Name x u (Bex_Name i j N) =  Bex_Name i j (Subst_Name x u N) .
Proof.
  intros.
  destruct N.
  + simpl.
    destruct (bool_dec (x0 =? x) true).
    - rewrite e.
      simpl.
      auto.
    - apply not_true_iff_false in n.
      rewrite n.
      simpl.
      auto.
  + simpl.
    destruct (bool_dec (i0 =? i) true).
    - rewrite e.
      simpl.
      auto.
    - apply not_true_iff_false in n.
      rewrite n.
      destruct (bool_dec (i0 =? j) true).
      * rewrite e.
        simpl.
        auto.
      * apply not_true_iff_false in n0.
        rewrite n0.
        auto.
Qed.


(*
*)
Lemma Subst_Bex_Exchange :
forall ( P : Process)(u x i j : nat),
i <> j -> {u \ x} ({i <~> j} P) =  {i <~> j} ( {u \ x} P).
Proof.
  intro.
  induction P; intros.
  + auto.
  + simpl.
    rewrite Subst_Bex_Exchange_Name; auto.
    rewrite Subst_Bex_Exchange_Name; auto.
  + simpl.
    rewrite IHP1; auto.
    rewrite IHP2; auto.
  + simpl.
    rewrite Subst_Bex_Exchange_Name; auto.
    rewrite Subst_Bex_Exchange_Name; auto.
    rewrite IHP; auto.
  + simpl.
    rewrite Subst_Bex_Exchange_Name; auto.
  + simpl.
    rewrite Subst_Bex_Exchange_Name; auto.
    rewrite IHP; auto.
  + simpl.
    rewrite IHP; auto.
  + simpl.
    rewrite Subst_Bex_Exchange_Name; auto.
    rewrite IHP; auto.
  + simpl.
    rewrite Subst_Bex_Exchange_Name; auto.
    rewrite IHP; auto.
Qed.



(*
*)
Lemma Cong_Subst_Cong :
forall (P Q : Process)( x u : nat),
P === Q -> ({u \ x}P) === ({u \ x}Q).
Proof.
  intros.
  induction H; try simpl; auto.
  + simpl.
    rewrite Subst_Bex_Exchange; auto.
  + constructor.
    apply Subst_Lc_Lc.
    auto.
Qed.


(*
*)
Lemma Subst_Open_NEq_Exchange :
forall (Q : Process)(x y u : nat),
x <> y -> 
({u \ x} Q) ^ y = {u \ x} (Q ^ y).
Proof.
  intros.
  simpl.
  rewrite (Subst_Open_Exchange Q x u y y 0); auto.
  simpl.
  destruct (bool_dec (y =? x) true).
  - apply beq_nat_true in e. lia.
  - apply not_true_iff_false in n.
    rewrite n. auto.
Qed.


(*
*)
Lemma Subst_Open_Eq_Exchange_Name :
forall (N : Name)(x u i : nat),
Subst_Name x u (Open_Name i x N) = Open_Name i u (Subst_Name x u N).
Proof.
  intros.
  destruct N.
  + simpl.
    destruct (bool_dec (x0 =? x) true).
    - rewrite e. auto.
    - apply not_true_iff_false in n.
      rewrite n. auto.
  + simpl.
    destruct (bool_dec (i =? i0) true).
    - rewrite e. simpl.
      destruct (bool_dec (x =? x) true).
      rewrite e0. auto.
      apply not_true_iff_false in n.
      apply beq_nat_false in n.
      contradiction.
    - apply not_true_iff_false in n.
      rewrite n. auto.
Qed.


(*
*)
Lemma Subst_Open_Eq_Exchange :
forall ( Q : Process)(u x i: nat),
({u \ x} ({i ~> x} Q )) = {i ~> u}({u \ x} Q).
Proof.
  intro.
  induction Q; intros.
  + auto.
  + simpl.
    do 2 rewrite Subst_Open_Eq_Exchange_Name.
    auto.
  + simpl.
    rewrite IHQ1.
    rewrite IHQ2.
    auto.
  + simpl.
    do 2 rewrite Subst_Open_Eq_Exchange_Name.
    rewrite IHQ.
    auto.
  + simpl.
    rewrite Subst_Open_Eq_Exchange_Name.
    auto.
  + simpl.
    rewrite Subst_Open_Eq_Exchange_Name.
    rewrite IHQ.
    auto.
  + simpl.
    rewrite IHQ.
    auto.
  + simpl.
    rewrite Subst_Open_Eq_Exchange_Name.
    rewrite IHQ.
    auto.
  + simpl.
    rewrite Subst_Open_Eq_Exchange_Name.
    rewrite IHQ.
    auto.
Qed.


(*
*)
Lemma Equality_Subst_Equality :
forall (P Q : Process)(x u : nat),
P = Q -> {x \ u} P = {x \ u} Q.
Proof.
  intros.
  rewrite H.
  auto.
Qed.






Lemma Aux1 :
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
        admit.
      * rewrite e. 
        apply not_true_iff_false in n. rewrite n.
        rewrite <- Subst_Open_NEq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        admit.
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
        admit.
      * apply not_true_iff_false in n. rewrite n.
        apply not_true_iff_false in n0. rewrite n0.
        rewrite <- Subst_Open_NEq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        admit.
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
        admit.
      * rewrite e. 
        apply not_true_iff_false in n. rewrite n.
        rewrite <- Subst_Open_NEq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        admit.
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
        admit.
      * apply not_true_iff_false in n. rewrite n.
        apply not_true_iff_false in n0. rewrite n0.
        rewrite <- Subst_Open_NEq_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        admit.
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
        admit.
      * rewrite e. 
        apply not_true_iff_false in n; rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        admit.
    - destruct (bool_dec (y =? x) true).
      * rewrite e.
        apply not_true_iff_false in n; rewrite n.
        apply beq_nat_true in e.
        rewrite e.
        admit.
      * apply not_true_iff_false in n. rewrite n.
        apply not_true_iff_false in n0. rewrite n0.
        admit.
  + simpl.
    constructor.
    apply Subst_Lc_Lc; auto.
    apply Subst_Lc_Lc; auto.
    apply IHReduction; auto.
    admit. (* facil *)
    inversions H0; auto.
  + simpl.
    
  + admit.














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



(*
Teorema 2.1 del artículo.
*)
Theorem Soundness : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P --> Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros P D F G H.
  dependent induction H; intros.
  + apply Fuse_No_Reduces in H2.
    contradiction.
  + apply Fuse_No_Reduces in H2.
    contradiction.
  + apply Rep_Input_No_Reduces in H3.
    contradiction.
  + admit.
  + admit.
  + apply Rep_Input_No_Reduces in H3.
    contradiction.
  + apply Chan_Close_No_Reduces in H5. contradiction.
  + apply Zero_No_Reduces in H1. contradiction.
  + apply Chan_Close_No_Reduces in H5. contradiction.
  + apply Zero_No_Reduces in H1. contradiction.
  + 
Admitted.



    
    
    
    
    
    
    
    
Lemma Double_WSubst_Equality :
forall (P : Process)( x u : nat),
Well_Subst P u x -> ({u \ x} ({x \ u} P)) = P.
Proof.
  intros.
  dependent induction P.
  + simpl. auto.
Admitted.

Lemma Well_Subst_Red_Well_Subst :
forall (P Q : Process)(u x : nat),
Well_Subst P u x -> ({x \ u} P) --> Q -> 
Well_Subst Q x u.
Proof.
Admitted.


Lemma Lc_Subst_WSubst_WSubst :
forall (P : Process)( u x : nat),
lc ({x \ u} P) -> Well_Subst ({x \ u} P) x u -> Well_Subst P u x.
Proof.
Admitted.
    
    
    
    