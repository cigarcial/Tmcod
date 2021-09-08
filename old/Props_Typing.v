(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
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
(x ∈ FVars P) \/  (~ x ∈ FVars P).
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
Qed.


Lemma Well_Subst_Subst :
forall (P : Process)( u x : nat),
lc P -> Well_Subst P u x -> 
Well_Subst ({x \ u} P) x u.
Proof.
  intros.
  constructor.
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
    admit.
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
    - admit.
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
    - admit.
Admitted.


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
Lemma Well_Subst_Open_Exchange :
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
Lemma Subst_Open_Name_Eq :
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
Lemma Subst_Open_Eq :
forall ( Q : Process)(u x i: nat),
({u \ x} ({i ~> x} Q )) = {i ~> u}({u \ x} Q).
Proof.
  intro.
  induction Q; intros.
  + auto.
  + simpl.
    do 2 rewrite Subst_Open_Name_Eq.
    auto.
  + simpl.
    rewrite IHQ1.
    rewrite IHQ2.
    auto.
  + simpl.
    do 2 rewrite Subst_Open_Name_Eq.
    rewrite IHQ.
    auto.
  + simpl.
    rewrite Subst_Open_Name_Eq.
    auto.
  + simpl.
    rewrite Subst_Open_Name_Eq.
    rewrite IHQ.
    auto.
  + simpl.
    rewrite IHQ.
    auto.
  + simpl.
    rewrite Subst_Open_Name_Eq.
    rewrite IHQ.
    auto.
  + simpl.
    rewrite Subst_Open_Name_Eq.
    rewrite IHQ.
    auto.
Qed.


(*
*)
Lemma Red_Subst_Red :
forall (P Q : Process)(x u : nat),
Well_Subst P x u -> 
(P --> Q ) -> ( ({u \ x} P) --> ({u \ x}Q)).
Proof.
  intros.
  induction H0.
  + destruct (bool_dec (x0 =? x) true).
    - destruct (bool_dec (y =? x) true).
      * admit. (* caso que no esta contemplado por construcción *)
      * simpl.
        rewrite e.
        apply not_true_iff_false in n; rewrite n.
        rewrite <- Well_Subst_Open_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        admit.
        apply beq_nat_false in n.
        auto.
    - destruct (bool_dec (y =? x) true).
      * simpl.
        apply not_true_is_false in n; rewrite n.
        rewrite e.
        apply beq_nat_true in e.
        rewrite <- e.
        rewrite Subst_Open_Eq.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        admit.
      * simpl.
        apply not_true_is_false in n; rewrite n.
        apply not_true_is_false in n0; rewrite n0.
        rewrite <- Well_Subst_Open_Exchange.
        constructor.
        apply Subst_Lc_Lc; auto.
        apply Subst_Body_Body; auto.
        admit.
        apply beq_nat_false in n0.
        auto.
  + admit.
  + destruct (bool_dec (x0 =? x) true).
    - simpl.
      rewrite e.
      constructor.
      apply Subst_Lc_Lc; auto.
    - apply not_true_iff_false in n.
      simpl.
      rewrite n.
      constructor.
      apply Subst_Lc_Lc; auto.
  + admit.
  + simpl.
    constructor.
    apply Subst_Lc_Lc; auto.
    apply Subst_Lc_Lc; auto.
    apply IHReduction.
    constructor.
    inversions H.
    apply No_FVars_Parallel in H3.
    destruct H3 as [HA HB]; auto.
  + simpl.
    inversions H.
    simpl in H2.
    
    admit.
  + inversions H.
    specialize (Cong_FVars P' P H1) as HFV.
    apply (Cong_Subst_Cong _ _ x u) in H1.
    apply (Cong_Subst_Cong _ _ x u) in H2.
    apply (Subst_Lc_Lc _ x u) in H0.
    apply (Red_reduction_struct ({u \ x} P) ({u \ x} Q) ({u \ x} P') ({u \ x} Q')); auto.
    apply IHReduction.
    constructor.
    rewrite HFV.
    auto.
Admitted.




Lemma Subst_Subst_Equal_Names :
forall (P : Process)( x u : nat),
Well_Subst P u x -> ({u \ x} ({x \ u} P)) = P.
Admitted.


Lemma Well_Subst_Red_Well_Subst :
forall (P Q : Process)(u x : nat),
Well_Subst P u x -> ({x \ u} P) --> Q -> 
Well_Subst Q x u.
Admitted.



(*
Teorema 2.1 del artículo.
*)
Theorem Soundness : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P --> Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros P D F G H.
  induction H; intros.
  + apply Fuse_No_Reduces in H2.
    contradiction.
  + apply Fuse_No_Reduces in H2.
    contradiction.
  + apply Rep_Input_No_Reduces in H3.
    contradiction.
  + specialize (Red_Subst_Red ({x \ u} P) Q x u) as HB.
    rewrite Subst_Subst_Equal_Names in HB; auto.
    specialize (Well_Subst_Red_Well_Subst P Q u x H3 H5) as HT.
    rewrite <- (Subst_Subst_Equal_Names Q u x); auto.
    specialize (Well_Subst_Subst P u x H2 H3) as HA.
    constructor; auto.
    apply Subst_Lc_Lc.
    apply (ProcessReduction_WD ({x \ u} P) Q); auto.
    apply Subst_Lc_Lc; auto.
    apply Well_Subst_Subst; auto.
    apply (ProcessReduction_WD  ({x \ u} P) _ ); auto.
    apply Subst_Lc_Lc; auto.
  + specialize (Red_Subst_Red ({x \ u} P) Q x u) as HB.
    rewrite Subst_Subst_Equal_Names in HB; auto.
    specialize (Well_Subst_Red_Well_Subst P Q u x H3 H5) as HT.
    rewrite <- (Subst_Subst_Equal_Names Q u x); auto.
    specialize (Well_Subst_Subst P u x H2 H3) as HA.
    constructor; auto.
    apply Subst_Lc_Lc.
    apply (ProcessReduction_WD ({x \ u} P) Q); auto.
    apply Subst_Lc_Lc; auto.
    apply Well_Subst_Subst; auto.
    apply (ProcessReduction_WD  ({x \ u} P) _ ); auto.
    apply Subst_Lc_Lc; auto.
  + apply Rep_Input_No_Reduces in H3.
    contradiction.
  + apply Chan_Close_No_Reduces in H5. contradiction.
  + admit.
  + admit.
  + admit.
Admitted.












































(*
*)
Lemma Replicant_No_Reduces : 
forall (P Q : Process)( x : Name )( y : nat ),
~ ((x !· Close_Rec 0 y P) --> Q).
Proof.
  intro.
  unfold not.
  induction P.
  + intros.
    simpl in H.
    inversions H.
    inversions H.
    simpl.

  unfold not.
  intros.
  inversions H.
  inversions H1.
  + inversions H3.
    admit.
    
  + 
Qed.

(*
Los siguientes lemas apoyan la prueba del teorema 2.1, determinan que algunos de los casos no se reducen a algo.
*)
Lemma Fuse_No_Reduces : 
forall (x y : Name)(Q : Process), 
~([x ←→  y] --> Q ).
Proof. 
  intros.

Qed.


























(*
*)
Lemma No_Red_AX4 : 
forall (x : Name)(P Q: Prepro),
~( (x · P) --> Q ).
Proof.
  unfold not.
  intros.
  inversion H.
Qed. 

Check No_Red_AX4.


(*
*)
Lemma No_Red_AX51 :
forall (x y : Name)(P Q R: Prepro), 
~( (x « y »· (P ↓ Q)) --> R ).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


(*
*)
Lemma No_Red_AX5 : 
forall (x : Name)(y : nat)(P Q R: Prepro), 
Process_Name x -> Process P -> Process Q ->
~( (ν Close_Rec 0 y (x « (FName y) »· (P ↓ Q))) --> R ).
Proof.
  unfold not.
  intros.
  inversions H2.
  inversions H.
  apply (Equal_Prepro_Equal_Open x0 _ _ ) in H3.
  simpl in H3.
  fold (Close_Name 0 y (FName y)) in H3.
  rewrite Open_Close_FName in H3.
  do 3 rewrite Process_Open_Close_Subst in H3; auto.
  rewrite Subst_By_Equal in H3.
  rewrite H3 in H6.
  destruct (bool_dec (x1 =? y) true).
  + rewrite e in H6.
    simpl in H6.
    apply No_Red_AX51 in H6.
    contradiction.
  + apply not_true_iff_false in n.
    rewrite n in H6.
    simpl in H6.
    apply No_Red_AX51 in H6.
    contradiction.
Qed.


(*
*)
Lemma No_Red_AX6 : 
forall (x : Name)(P Q : Prepro), 
~( ( x ()· P ) --> Q).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


(*
*)
Lemma No_Red_AX71 :
forall ( x u : Name)( P Q : Prepro),
~((u « x »· P) --> Q).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


(*
Caso 7 no reduce a nada
*)
Lemma No_Red_AX7 :
forall ( u : Name )( x : nat )( P Q : Prepro),
Process_Name u -> Process P ->
~(ν (Close_Rec 0 x (u « (FName x) »· P)) --> Q).
Proof.
  unfold not.
  intros.
  inversions H1.
  inversions H.
  apply (Equal_Prepro_Equal_Open x0 _ _ ) in H2.
  simpl in H2.
  fold (Close_Name 0 x (FName x)) in H2.
  rewrite Open_Close_FName in H2.
  do 2 rewrite Process_Open_Close_Subst in H2; auto.
  rewrite Subst_By_Equal in H2.
  rewrite H2 in H5.
  destruct (bool_dec (x1 =? x) true).
  + rewrite e in H5.
    simpl in H5.
    apply No_Red_AX71 in H5.
    contradiction.
  + apply not_true_iff_false in n.
    rewrite n in H5.
    simpl in H5.
    apply No_Red_AX71 in H5.
    contradiction.
Qed.


(*
El caso 8 no reduce a nada
*)
Lemma No_Red_AX8 : 
forall (x : Name)( Q : Prepro),
~ ((x «»·°) --> Q).
Proof.
  unfold not.
  intros.
  induction Q; try inversion H.
Qed.


(*
Construcción de un tipo de Proceso.
*)
Lemma Proc_Valid_V1 :
forall (P Q : Prepro)( u : Name )( x : nat  ),
Process_Name u -> Process P -> Process Q -> 
Process ((u !· Close x P) ↓ Q).
Proof.
  intros.
  constructor; auto.
  specialize ( Close_Is_Body P x) as HB.
  specialize ( HB H0 ).
  inversion HB.
  constructor; auto.
Qed.


(*
Teorema 2.1 del artículo.
*)
Theorem Soundness : 
forall (P : Prepro)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> (forall (Q: Prepro), (P --> Q)
  -> ( D ;;; F !- Q ::: G )).
Proof.
  intros P D F G H.
  induction H; intros.
  + apply No_Red_AX1 in H2. contradiction.
  + apply No_Red_AX1 in H2. contradiction.
  + apply No_Red_AX2 in H3. contradiction.
  + admit.
  + admit.
  (* + rewrite Ax_Alpha in H6.
    rewrite <- (Ax_Alpha u x Q). 
    constructor; auto.
    apply (ProcessReduction_WD P Q); auto.
  + rewrite Ax_Alpha in H6.
    rewrite <- (Ax_Alpha u x Q). 
    constructor; auto.
    apply (ProcessReduction_WD P Q); auto. *)
  + apply No_Red_AX2 in H3. contradiction.
  + apply No_Red_AX4 in H5. contradiction.
  + apply No_Red_AX5 in H9; try contradiction; auto.
  + apply No_Red_AX4 in H5. contradiction.
  + apply No_Red_AX5 in H9; try contradiction; auto.
  + apply No_Red_AX4 in H5. contradiction.
  + apply No_Red_AX5 in H9; try contradiction; auto.
  + apply No_Red_AX6 in H5. contradiction.
  + apply No_Red_AX8 in H1. contradiction.
  + apply No_Red_AX6 in H5. contradiction.
  + apply No_Red_AX8 in H1. contradiction.
  + apply No_Red_AX7 in H4; try contradiction; auto. constructor.
  + apply No_Red_AX7 in H4; try contradiction; auto. constructor.
  + 
  + admit.
Admitted.
(*   + specialize (Char_Red_Chanres2  ((u !· Close x P) ↓ Q) Q0 u) as HU.
    specialize (Proc_Valid_V1 P Q u x) as HV.
    specialize (HV H3 H2 H4 H5).
    specialize (HU HV H8).
    destruct HU as [Q1 H9].
    destruct H9.
    rewrite H9.
    specialize (Char_Red_Arr u x P Q Q1) as HT.
    specialize (HT H10).
    destruct HT as [Q2 H11].
    destruct H11.
    rewrite H11.
    apply (cutrep D F G x u P Q2 A); auto.
    apply (ProcessReduction_WD Q Q2); auto.
  + specialize (Char_Red_Chanres2  ((u !· Close x P) ↓ Q) Q0 u) as HU.
    specialize (Proc_Valid_V1 P Q u x) as HV.
    specialize (HV H3 H2 H4 H5).
    specialize (HU HV H8).
    destruct HU as [Q1 H9].
    destruct H9.
    rewrite H9.
    specialize (Char_Red_Arr u x P Q Q1) as HT.
    specialize (HT H10).
    destruct HT as [Q2 H11].
    destruct H11.
    rewrite H11.
    apply (cutcon D F G x u P Q2 A); auto.
    apply (ProcessReduction_WD Q Q2); auto. *)




(*
Caracteriza la reducción de un proceso como el de la hipótesis.
*)
Lemma Char_Red_Chanres2 :
forall (P Q : Prepro)(x : nat),
Process P -> (ν (Close x P) --> Q ) -> 
exists (Q0 : Prepro), ( Q = (ν (Close x Q0)) /\ P --> Q0).
Proof.
  intros.
  inversions H0.
  
  
  inversion H0; subst.
  exists ({x\x0}Q0).
  split.
  + 
    
  + specialize (Close_Rec_Eq_Subst P0 P x0 x 0) as HT.
    specialize (HT H2 H H1).
    rewrite Ax_Alpha in HT.
    rewrite Ax_Alpha.
    rewrite <- HT.
    auto.
Qed.















Lemma Close_Subst_Name :
forall (P : Prepro)(x y i: nat),
x <> y -> Close_Rec i x P = Close_Rec i y ( { y \ x } P ).
Proof.
  intro.
  unfold Close.
  induction P; intros.
  + auto.
  + simpl.
    admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + simpl.
    rewrite (IHP _ y _); auto.
Admitted.

Lemma Close_Name_Subst_Name :
forall ( x : Name )( i x0 y0 : nat ),
Close_Name i x0 x = Close_Name i y0 (Subst_Name x0 y0 x).
Proof.
  intro.
  destruct x; intros.
  + simpl.
    destruct (bool_dec (x =? x0) true).
    - rewrite e.
      simpl.
      destruct (bool_dec (y0 =? y0) true).
      * rewrite e0. auto.
      * apply not_true_iff_false in n.
        apply beq_nat_false in n.
        admit.
    - apply not_true_iff_false in n.
      rewrite n.
      simpl.
      destruct (bool_dec (x =? y0) true).
      * admit.
      * apply not_true_iff_false in n0.
        rewrite n0.
        auto.
  + auto.
Admitted.







(*
Lo siguientes lemas son intuitivamente ciertos, sin embargo su prueba 
es difícil teniendo en cuenta que necesitan la idea que x aparece en P para que la operación  Close_Rec i x P tenga sentido. 
*)
Lemma Close_Rec_Eq_Subst : 
forall (P Q : Prepro)(x y : nat)( i: nat),
Process P -> Process Q -> 
Close_Rec i x P = Close_Rec i y Q ->
P = { x \ y } Q.
Proof.
Admitted.



(*
*)
Lemma Char_Red_Arr :
forall ( u : Name )( x : nat )( P Q0 Q1 : Prepro ),
( ((u !· Close x P) ↓ Q0) --> Q1 ) -> 
(exists (Q2 : Prepro), ( Q1 = ((u !· Close x P) ↓ Q2) /\ Q0 --> Q2 )).
Proof.
  intros.
  inversion H; subst.
  + admit.
  + exists R.
    split; auto.
Admitted.
