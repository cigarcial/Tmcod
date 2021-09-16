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

From old Require Import Defs_Tactics.
From old Require Import Defs_Typing.
From old Require Import Defs_Process.
From old Require Import Defs_Proposition.
From old Require Import Facts_MOpen.
From old Require Import Props_Process.



Ltac InductionProcess P Name_Lemma := 
  induction P;
    intros; simpl;
    try rewrite Name_Lemma;
    try rewrite Name_Lemma;
    repeat match goal with 
      | IHP  : _ |- _  =>  rewrite IHP; auto
      | IHP1 : _ |- _ => try rewrite IHP1; auto
    end.

Ltac InductionProcessRev P Name_Lemma := 
  induction P;
    intros; simpl;
    try rewrite Name_Lemma;
    try rewrite Name_Lemma;
    repeat match goal with 
      | IHP  : _ |- _  =>  rewrite <- IHP; auto
      | IHP1 : _ |- _ => try rewrite <- IHP1; auto
    end.


Ltac UnionSearch H := unfold not; intros; apply H; 
  (left; try left; progress auto) + 
  (right; try left; progress auto) + 
  (left; try right; progress auto) + 
  (right; try right; progress auto).


Ltac EasyDec x y e n:= 
  destruct (bool_dec (x =? y) true);
    try apply not_true_iff_false in n;
    try rewrite e;
    try rewrite n;
    try simpl;
    auto.

















Lemma beq_nat_false_inv :
forall ( x y : nat),
x <> y -> 
(x =? y) = false.
Proof.
  intros.
  apply not_true_iff_false.
  unfold not.
  intros.
  apply beq_nat_true in H0.
  contradiction.
Qed.


Lemma beq_nat_true_inv :
forall ( x y : nat),
x = y -> 
(x =? y) = true.
Proof.
  intros.
  rewrite H.
  apply eq_sym.
  apply beq_nat_refl.
Qed.



Lemma FVar_Process_Is_Or_Not :
forall (P : Process)( x : nat),
(x ∈ FVars P) \/ (~ x ∈ FVars P).
Admitted.

Lemma FVars_Bex_Name :
forall ( x : Name)(i j : nat),
FVars_Name (Bex_Name i j x) = FVars_Name x.
Proof.
  destruct x; intros; simpl; auto.
  EasyDec i i0 e n; try EasyDec i j e n0.
Qed.



Lemma FVars_Bex_Process:
forall (P : Process)(i j : nat),
FVars P = FVars ({i <~> j} P).
Proof.
  InductionProcessRev P FVars_Bex_Name.
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
  destruct x; simpl in H0; try inversions H0.
  unfold not in *.
  apply H.
  destruct (bool_dec (x =? u) true).
  + rewrite e in H0.
    apply Singleton_inv in H0.
    auto.
  + apply not_true_iff_false in n.
    rewrite n in H0.
    simpl in H0.
    apply Singleton_inv in H0.
    apply beq_nat_false in n.
    contradiction.
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
Lemma Subst_Bex_Exchange_Names :
forall (N : Name)(x u i j : nat),
i <> j -> Subst_Name x u (Bex_Name i j N) =  Bex_Name i j (Subst_Name x u N) .
Proof.
  intros.
  destruct N.
  + simpl.
    EasyDec x0 x e n.
  + simpl.
    EasyDec i0 i e n; try EasyDec i0 j e n0.
Qed.


(*
*)
Lemma Subst_Bex_Exchange :
forall ( P : Process)(u x i j : nat),
i <> j -> {u \ x} ({i <~> j} P) =  {i <~> j} ( {u \ x} P).
Proof.
  InductionProcess P Subst_Bex_Exchange_Names.
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
  EasyDec y x e n.
  apply beq_nat_true in e; lia.
Qed.


(*
*)
Lemma Subst_Open_Eq_Exchange_Names :
forall (N : Name)(x u i : nat),
Subst_Name x u (Open_Name i x N) = Open_Name i u (Subst_Name x u N).
Proof.
  intros.
  destruct N.
  + simpl.
    EasyDec x0 x e n.
  + simpl.
    EasyDec i i0 e n.
    specialize (beq_nat_refl x) as HT.
    apply eq_sym in HT.
    rewrite HT.
    auto.
Qed.


(*
*)
Lemma Subst_Open_Eq_Exchange :
forall ( Q : Process)(u x i: nat),
({u \ x} ({i ~> x} Q )) = {i ~> u}({u \ x} Q).
Proof.
  InductionProcess Q Subst_Open_Eq_Exchange_Names.
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


Lemma Subst_Close_By_Equal_Name_Names :
forall (u y i : nat)(x : Name),
Subst_Name y u (Close_Name i y x) = Close_Name i y x.
Proof.
  destruct x; auto.
   simpl.
   EasyDec x y e n.
   rewrite n.
   auto.
Qed.


(*
*)
Lemma Subst_Close_By_Equal_Name :
forall (P : Process)(u x i: nat),
{u \ x} Close_Rec i x P = Close_Rec i x P.
Proof.
  InductionProcess P Subst_Close_By_Equal_Name_Names.
Qed.



Lemma Subst_Close_Dif_Name_Names :
forall (x0 u i z : nat)(x : Name),
x0 <> z -> u <> z -> 
Subst_Name x0 u (Close_Name i z x ) = Close_Name i z (Subst_Name x0 u x).
Proof.
  intros.
  destruct x; auto.
  simpl.
  destruct (bool_dec (x =? z) true).
  + destruct (bool_dec (x =? x0) true).
    - apply beq_nat_true in e0.
      apply beq_nat_true in e.
      rewrite <- e0 in H.
      contradiction.
    - apply not_true_iff_false in n.
      rewrite e.
      rewrite n.
      simpl.
      rewrite e.
      auto.
  + destruct (bool_dec (x =? x0) true).
    - apply not_true_iff_false in n.
      rewrite n. rewrite e.
      simpl. rewrite e.
      destruct (bool_dec (u =? z) true).
      apply beq_nat_true in e0; contradiction.
      apply not_true_iff_false in n0.
      rewrite n0; auto.
    - apply not_true_iff_false in n.
      apply not_true_iff_false in n0.
      rewrite n. rewrite n0.
      simpl.
      rewrite n. rewrite n0.
      auto.
Qed.


Lemma Subst_Close_Dif_Name :
forall (P : Process)(u x i z: nat),
x <> z -> u <> z -> 
{u \ x} Close_Rec i z P = Close_Rec i z ({u \ x}P).
Proof.
  InductionProcess P Subst_Close_Dif_Name_Names.
Qed.


Lemma Double_Subst_AlreadySubst_Eq_Names :
forall (x0 u y0 : nat)(x : Name),
x0 <> y0 ->
Subst_Name x0 u (Subst_Name x0 y0 x) = Subst_Name x0 y0 x.
Proof.
  intros.
  destruct x; auto.
  simpl.
  destruct (bool_dec (x =? x0) true).
  + rewrite e.
    simpl.
    specialize (beq_nat_false_inv y0 x0) as HX.
    rewrite HX; auto.
  + apply not_true_iff_false in n; rewrite n.
    simpl. rewrite n.
    auto.
Qed.

(*
*)
Lemma Double_Subst_AlreadySubst_Eq :
forall (P : Process)( u x y : nat),
x <> y -> 
({u \ x} ({y \ x} P)) = {y \ x} P.
Proof.
  InductionProcess P Double_Subst_AlreadySubst_Eq_Names.
Qed.



Lemma Double_Subst_Expan_NFVar_Names :
forall (x : Name)(x0 y0 u : nat),
~ u ∈ FVars_Name x -> 
Subst_Name x0 y0 x = Subst_Name u y0 (Subst_Name x0 u x).
Proof.
  destruct x; intros; auto.
  simpl.
  assert (HX : x <> u). 
  simpl in H.
  unfold not.
  intros.
  apply H.
  rewrite H0.
  constructor.
  destruct (bool_dec (x =? x0) true).
  + rewrite e.
    simpl.
    specialize (beq_nat_refl u) as HT.
    apply eq_sym in HT.
    rewrite HT.
    auto.
  + apply not_true_iff_false in n.
    rewrite n.
    simpl.
    specialize (beq_nat_false_inv x u HX) as Ht.
    rewrite Ht.
    auto.
Qed.


Lemma Double_Subst_Expan_NFVar :
forall (P : Process)(x y u : nat),
~ u ∈ FVars P -> 
({y \ x} P) = ({y \ u} ({u \ x} P)).
Proof.
  induction P; 
    intros; simpl; 
    simpl in H;
    try rewrite (Double_Subst_Expan_NFVar_Names x _ _ u);
    try rewrite (Double_Subst_Expan_NFVar_Names y _ _ u);
    try rewrite (IHP1 _ _ u);
    try rewrite (IHP2 _ _ u);
    try rewrite (IHP _ _ u);
    try UnionSearch H;
    auto.
Qed.




Lemma Double_Subst_By_Same_Name_Names :
forall (x : Name)(x0 u x1 : nat),
Subst_Name x0 u (Subst_Name x1 x0 x) = Subst_Name x1 u (Subst_Name x0 u x).
Proof.
  destruct x; auto.
  intros.
  simpl.
  destruct (bool_dec (x =? x1) true).
  + rewrite e.
    destruct (bool_dec (x =? x0) true).
    - rewrite e0.
      simpl.
      specialize (beq_nat_refl x0) as HX.
      apply eq_sym in HX.
      rewrite HX.
      EasyDec u x1 e1 n.
    - apply not_true_iff_false in n.
      rewrite n.
      simpl.
      specialize (beq_nat_refl x0) as HX.
      apply eq_sym in HX.
      rewrite HX.
      rewrite e; auto.
  + apply not_true_iff_false in n.
    rewrite n.
    destruct (bool_dec (x =? x0) true).
    - rewrite e.
      simpl.
      rewrite e.
      EasyDec u x1 e0 n0.
    - apply not_true_iff_false in n0.
      rewrite n0.
      simpl.
      rewrite n.
      rewrite n0.
      auto.
Qed.



Lemma Double_Subst_By_Same_Name :
forall (P : Process)(u x x0 : nat),
({u \ x} ({x \ x0} P)) = ({u \ x0} ({u \ x} P)).
Proof.
  InductionProcess P Double_Subst_By_Same_Name_Names.
Qed.


(*
*)
Lemma Double_Subst_All_Dif_Names :
forall (x : Name)(x0 u x1 y0 : nat),
x1 <> x0 -> y0 <> x0 -> u <> x1 ->
Subst_Name x0 u (Subst_Name x1 y0 x) = Subst_Name x1 y0 (Subst_Name x0 u x).
Proof.
  intros.
  destruct x; auto.
  simpl.
  destruct (bool_dec (x =? x1) true).
  + destruct (bool_dec (x =? x0) true).
    - apply beq_nat_true in e.
      apply beq_nat_true in e0.
      rewrite e in e0.
      contradiction.
    - apply not_true_iff_false in n.
      rewrite n.
      rewrite e.
      simpl.
      rewrite e.
      specialize (beq_nat_false_inv y0 x0 H0) as Hx.
      rewrite Hx.
      auto.
  + destruct (bool_dec (x =? x0) true).
    - apply not_true_iff_false in n.
      rewrite e; rewrite n.
      simpl.
      rewrite e.
      specialize (beq_nat_false_inv u x1 H1) as Hx.
      rewrite Hx.
      auto.
    - apply not_true_iff_false in n.
      apply not_true_iff_false in n0.
      rewrite n; rewrite n0.
      simpl.
      rewrite n; rewrite n0.
      auto.
Qed.


Lemma Double_Subst_All_Dif :
forall (P : Process)(u x y x0 : nat),
x0 <> x -> y <> x -> u <> x0 ->
({u \ x} ({y \ x0} P)) = ({y \ x0} ({u \ x} P)).
Proof.
  induction P; intros; simpl; auto.
  + rewrite (Double_Subst_All_Dif_Names x _ _ _ _); auto.
    rewrite (Double_Subst_All_Dif_Names y _ _ _ _); auto.
  + rewrite IHP1; auto.
    rewrite IHP2; auto.
  + rewrite (Double_Subst_All_Dif_Names x _ _ _ _); auto.
    rewrite (Double_Subst_All_Dif_Names y _ _ _ _); auto.
    rewrite IHP; auto.
  + rewrite (Double_Subst_All_Dif_Names x _ _ _ _); auto.
  + rewrite (Double_Subst_All_Dif_Names x _ _ _ _); auto.
    rewrite IHP; auto.
  + rewrite IHP; auto.
  + rewrite (Double_Subst_All_Dif_Names x _ _ _ _); auto.
    rewrite IHP; auto.
  + rewrite (Double_Subst_All_Dif_Names x _ _ _ _); auto.
    rewrite IHP; auto.
Qed.


Lemma FVars_Close_Beq_Names :
forall(x : Name)(u x0 i : nat),
u <> x0 -> u ∈ FVars_Name x -> 
Close_Name i x0 x = FName u.
Proof.
  intros.
  destruct x; simpl in H0; try contradiction; auto.
  apply Singleton_inv in H0.
  destruct (bool_dec (x =? x0) true); simpl.
  + apply beq_nat_true in e.
    lia.
  + apply not_true_iff_false in n; rewrite n.
    auto.
Qed.


Lemma FVars_Close_Beq :
forall ( P : Process ) (u x i : nat),
u <> x -> u ∈ FVars P -> u ∈ FVars (Close_Rec i x P).
Proof.
  induction P; intros; simpl; auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
    - right.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left; apply IHP1; auto.
    - right; apply IHP2; auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - apply Union_inv in H0.
      destruct H0.
      * left; left.
        rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
        simpl; constructor.
      * left; right.
        rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
        simpl; constructor.
    - right.
      apply IHP; auto.
  + simpl in H0.
    rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
    simpl; constructor.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
    - right.
      apply IHP; auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
    - right.
      apply IHP; auto.
  + simpl in H0.
    apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Close_Beq_Names _ u _ _ ); auto.
      simpl; constructor.
    - right.
      apply IHP; auto.
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
        apply Subst_Lc_Lc; auto.
        apply IHReduction; auto.
        inversions H.
        constructor; auto.
        unfold not.
        intros.
        apply H4.
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




Lemma FVars_Open_Beq_Names :
forall (x : Name)(u x0 i: nat),
u ∈ FVars_Name x -> FVars_Name (Open_Name i x0 x) = Singleton nat u.
Proof.
  intros.
  destruct x; simpl in H; try contradiction.
  apply Singleton_inv in H.
  rewrite H.
  auto.
Qed.



(*
*)
Lemma FVars_Open_Beq_Names_Inv :
forall (x : Name)(u x0 i: nat),
u <> x0 -> u ∈ FVars_Name (Open_Name i x0 x) ->
FVars_Name x = Singleton nat u.
Proof.
  intros.
  destruct x.
  + simpl in H0.
    apply Singleton_inv in H0.
    simpl.
    auto.
  + simpl in H0.
    destruct (bool_dec (i =? i0) true).
    - rewrite e in H0.
      simpl in H0.
      apply Singleton_inv in H0.
      rewrite H0 in H.
      contradiction.
    - apply not_true_iff_false in n.
      rewrite n in H0.
      simpl in H0.
      contradiction.
Qed.


(*
*)
Lemma FVars_Open_Beq :
forall ( P : Process)(u x i: nat),
u <> x -> ( u ∈ FVars P <-> u ∈ FVars ({i ~> x}P)).
Proof.
  intro.
  induction P; intros; simpl; try constructor; try intros; try contradiction.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names x u x0 i); auto.
      constructor.
    - right.
      rewrite (FVars_Open_Beq_Names y u x0 i); auto.
      constructor.
  + admit.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      apply IHP1; auto.
    - right.
      apply IHP2; auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      apply <- (IHP1 u x i); auto.
    - right.
      apply <- (IHP2 u x i); auto.
  + admit.
  + admit.
  + admit.
  + admit.
  + apply Union_inv in H0.
    destruct H0.
    - left. 
      rewrite (FVars_Open_Beq_Names x u x0 i); auto.
      constructor.
    - right; apply IHP; auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names_Inv _ u x0 i); auto.
      constructor.
    - right; apply <- (IHP u x0 i); auto.
  + apply IHP; auto.
  + apply <- (IHP u x (S i)); auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names x u x0 i); auto.
      constructor.
    - right; apply IHP; auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names_Inv _ u x0 i); auto.
      constructor.
    - right; apply <- (IHP u x0 (S i)); auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names x u x0 i); auto.
      constructor.
    - right; apply IHP; auto.
  + apply Union_inv in H0.
    destruct H0.
    - left.
      rewrite (FVars_Open_Beq_Names_Inv _ u x0 i); auto.
      constructor.
    - right; apply <- (IHP u x0 (S i)); auto.
Admitted.























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
  + assert (H6 := H5).
    inversions H3.
    apply (Well_Subst_Reduction_Susbt ({x \ u} P) Q x u)  in H5; auto.
    rewrite <- Double_Subst_Expan_NFVar in H5; auto.
    rewrite Subst_By_Equal in H5.
    rewrite <- (Subst_By_Equal Q x).
    rewrite (Double_Subst_Expan_NFVar Q x x u).
    constructor; auto.
    apply (ProcessReduction_WD P _ ); auto.
    apply Lc_WSubst_Subst_WSubst; auto.
    apply (ProcessReduction_WD ({x \ u} P) _ ); auto.
    apply Subst_Lc_Lc; auto.
    constructor; auto.
    admit.
    admit.
    apply Lc_WSubst_Subst_WSubst; auto.
    apply Subst_Lc_Lc; auto.
  + admit.
  + apply Rep_Input_No_Reduces in H3.
    contradiction.
  + apply Chan_Close_No_Reduces in H5. contradiction.
  + apply Zero_No_Reduces in H1. contradiction.
  + apply Chan_Close_No_Reduces in H5. contradiction.
  + apply Zero_No_Reduces in H1. contradiction.
  + 
Admitted.


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




Lemma Subst_WSubst_WSubst :
forall (P : Process)( u x : nat),
Well_Subst ({x \ u} P) x u -> Well_Subst P u x.
Proof.
  induction P; intros; try inversions H; try constructor; simpl; auto.
  + unfold not.
    intros.
    contradiction. 
  + simpl in H0.
    apply No_Union_No_Each in H0.
    destruct H0 as [HA HB].
    admit.
  + simpl in H0.
    apply No_Union_No_Each in H0.
    destruct H0 as [HA HB].
    unfold not.
    intros.
    admit.
  + admit.
  + admit.
  + admit.
  + unfold not.
    intros.
    simpl in H0.
    assert (Ht : Well_Subst P u x). 
      try apply IHP; try constructor; auto.
    inversions Ht.
    contradiction.
Admitted.












Lemma Well_Subst_Red_Well_Subst :
forall (P Q : Process)(u x : nat),
Well_Subst P u x -> P --> Q -> 
Well_Subst Q u x.
Proof.
  intros.
  inversions H.
  constructor; auto.
  unfold not in H1.
  unfold not.
  intros.
  apply H1.
  dependent induction H0.
  + simpl in H4.
    apply Union_inv in H4.
    destruct H4.
    - left; right; auto.
    - admit.
  + simpl in H4.
    apply Union_inv in H4.
    destruct H4.
    - apply Union_inv in H4.
      destruct H4.
      * left; right; auto.
      * admit.
    - apply Union_inv in H4.
      destruct H4.
      * right; left; auto.
      * right; right; auto.
  + right; right; auto.
  + admit.
  + simpl in H5.
    apply Union_inv in H5.
    destruct H5.
    - left; auto.
    - right; auto.
      inversions H.
      simpl in H6.
      apply No_Union_No_Each in H6.
      destruct H6 as [HA HB].
      apply IHReduction; try constructor; auto.
  + simpl.
  
  
  
Admitted.



























    
    
    
    