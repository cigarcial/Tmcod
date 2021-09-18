(*
  Ciro Iván García López
  Tesis de Maestría - Master Thesis
  Session Type Systems Verification
  Unam - 2021
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Sets.Constructive_sets.

From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Facts_Names.




(*
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
Resultados generales sobre procesos
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
*)


(*
*)
Lemma Body_Parallel_Body_Each :
forall ( P Q : Process),
Body (P ↓ Q) -> (Body P /\ Body Q).
Proof.
  constructor;
    try constructor;
    intros;
    inversions H;
    specialize (H0 x);
    simpl in H0;
    inversions H0; auto.
Qed.


(*
*)
Lemma Body_Process_Equivalence_Res :
forall (P : Process),
Body P <-> lc (ν P).
Proof.
  split.
  + intros.
    constructor. inversion H. auto.
  + intros.
    inversion H. constructor. auto.
Qed.


(*
*)
Lemma Exchange_Open :
forall ( P : Process)(x y k i : nat),
i <> k -> 
{i ~> y} ( {k ~> x} P ) = {k ~> x} ( {i ~> y} P ).
Proof.
  induction P; intros.
  + auto.
  + simpl.
    destruct x.
    - destruct y.
      * auto.
      * rewrite (Eq_Open_Name i y0 k x0 i0); auto.
    - destruct y.
      * rewrite (Eq_Open_Name i y0 k x0 i0); auto.
      * rewrite (Eq_Open_Name i y0 k x0 i0); auto.
        rewrite (Eq_Open_Name i y0 k x0 i1); auto.
  + simpl. 
    rewrite IHP1; auto.
    rewrite IHP2; auto.
  + simpl.
    rewrite IHP; auto.
     destruct x.
      - destruct y.
        * auto.
        * rewrite (Eq_Open_Name i y0 k x0 i0); auto.
      - destruct y.
        * rewrite (Eq_Open_Name i y0 k x0 i0); auto.
        * rewrite (Eq_Open_Name i y0 k x0 i0); auto.
          rewrite (Eq_Open_Name i y0 k x0 i1); auto.
  + simpl.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name i y k x0 i0); auto.
  + simpl.
    rewrite IHP; auto.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name i y k x0 i0); auto.
  + simpl.
    apply f_equal.
    rewrite IHP; auto.
  + simpl.
    rewrite IHP; auto.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name i y k x0 i0); auto.
  + simpl.
    rewrite IHP; auto.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name i y k x0 i0); auto.
Qed.


(*
*)
Lemma Subst_Open_Exchange :
forall ( P : Process )( x y z w k: nat ),
FName w = (Subst_Name x y (FName z)) -> 
{y \ x} ({k ~> z} P) = {k ~> w} ({y \ x} P).
Proof.
  intro.
  induction P; intros.
  + auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _  w _ ); auto.
    rewrite (Subst_Name_Open_Name_Ex y x0 y0 z w k ); auto.
  + simpl.
    rewrite (IHP1 _ _ _ w _); auto.
    rewrite (IHP2 _ _ _ w _); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _ w _ ); auto.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _ w _ ); auto.
    rewrite (IHP _ _ _ w _); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _ w _ ); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _ w _ ); auto.
    rewrite (IHP _ _ _ w _); auto.
  + simpl.
    rewrite (IHP x y z w (S k)); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex x x0 y z w k ); auto.
    rewrite (IHP x0 y z w (S k)); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex x x0 y z w k ); auto.
    rewrite (IHP x0 y z w (S k)); auto.
Qed.


(*
*)
Lemma Subst_By_Equal :
forall ( P : Process )( x : nat ),
{ x \ x } P = P.
Proof.
  induction P; intros; simpl; repeat rewrite Subst_Name_By_Equal; try apply f_equal; auto.
  + rewrite IHP1.
    rewrite IHP2.
    auto.
Qed.


(*
*)
Lemma Equal_Process_Equal_Open : 
forall ( x : nat )( P Q: Process ),
(P = Q ) -> (Open_Rec 0 x P = Open_Rec 0 x Q).
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.


(*
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
Resultados generales relacionadas con las operaciones sobre procesos a nivel k
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
*)


(*
*)
Lemma Process_Lca_Open_S :
forall ( P : Process )(i: nat),
(forall (x : nat), lca i ({i ~> x} P)) -> lca (S i) P.
Proof.
  intro.
  induction P.
  + intros.
    constructor.
  + intros.
    constructor;
      apply (Lca_Name_Open _ _);
      intros;
      specialize (H x0);
      inversions H; auto.
  + intros.
    constructor;
      apply (IHP1 _) || apply (IHP2 _);
      intros;
      specialize (H x);
      inversions H;
      auto.
  + intros.
    constructor;
      try apply (Lca_Name_Open _ _);
      try intros;
      try specialize (H x0);
      try inversions H; auto.
    - apply (IHP _). 
      intros. 
      specialize (H x0).
      inversions H.
      auto.
  + intros.
    constructor.
      try apply (Lca_Name_Open _ _);
      try intros;
      try specialize (H x0);
      try inversions H; auto.
  + intros.
    constructor.
      try apply (Lca_Name_Open _ _);
      try intros;
      try specialize (H x0);
      try inversions H; auto.
    - apply (IHP _). 
      intros.
      specialize (H x0).
      inversions H.
      auto.
  + constructor.
    simpl in H.
    apply IHP.
    intros.
    specialize (H x).
    inversions H.
    auto.
  + constructor.
      try apply (Lca_Name_Open _ _);
      try intros;
      try specialize (H x0);
      try inversions H; auto.
    simpl in H.
    apply IHP.
    intros.
    specialize (H x0).
    inversions H.
    auto.
  + constructor.
      try apply (Lca_Name_Open _ _);
      try intros;
      try specialize (H x0);
      try inversions H; auto.
    simpl in H.
    apply IHP.
    intros.
    specialize (H x0).
    inversions H.
    auto.
Qed.



(*
*)
Lemma Lca_Process_Rd :
forall ( P : Process )( k x: nat ),
lca (S k) P -> lca k ({k ~> x} P).
Proof.
  intro.
  induction P; intros; simpl; try inversions H.
  + constructor.
  + constructor; apply Lca_Name_Rd; auto.
  + constructor.
    apply IHP1; auto.
    apply IHP2; auto.
  + constructor; try apply Lca_Name_Rd; auto.
  + constructor; try apply Lca_Name_Rd; auto.
  + constructor; try apply Lca_Name_Rd; auto.
  + simpl.
    constructor.
    inversions H.
    apply IHP; auto.
  + simpl.
    inversions H.
    constructor.
    - apply Lca_Name_Rd; auto.
    - apply IHP; auto.
  + simpl.
    inversions H.
    constructor.
    - apply Lca_Name_Rd; auto.
    - apply IHP; auto.
Qed.


(*
*)
Lemma Subst_Lca_Process :
forall ( P : Process )( k : nat ),
lca k P -> forall (x y : nat ), lca k ({y \ x} P).
Proof.
  induction P; intros;
    try constructor;
    try inversions H;
    try constructor;
    try apply Subst_Lca_Name;
    auto.
Qed.


(*
*)
Lemma Lca_Name_Open_Close_Subst :
forall ( x : Name )( x0 y k : nat),
lca_name k x -> 
Open_Name k y (Close_Name k x0 x) = Subst_Name x0 y x.
Proof.
  intros.
  inversions H.
  + simpl.
    destruct (bool_dec (x1 =? x0) true).
    - rewrite e.
      simpl.
      destruct (bool_dec (k =? k) true).
      * rewrite e0; auto.
      * apply not_true_iff_false in n.
        apply beq_nat_false in n.
        lia.
    - apply not_true_iff_false in n.
      rewrite n.
      auto.
  + simpl.
    destruct (bool_dec (k =? i) true).
    - apply beq_nat_true in e.
      lia.
    - apply not_true_iff_false in n.
      rewrite n; auto.
Qed.


(*
*)
Lemma Lca_Open_Close_Subst :
forall ( P : Process )( x y k : nat ), 
lca k P -> { k ~> y } Close_Rec k x P = { y \ x } P.
Proof.
  intros P.
  induction P; intros; simpl; inversions H; try auto.
  + repeat rewrite Lca_Name_Open_Close_Subst; auto.
  + rewrite IHP1; auto.
    rewrite IHP2; auto.
  + repeat rewrite Lca_Name_Open_Close_Subst; auto.
    rewrite IHP; auto.
  + repeat rewrite Lca_Name_Open_Close_Subst; auto.
  + repeat rewrite Lca_Name_Open_Close_Subst; auto.
    rewrite IHP; auto.
  + inversions H.
    rewrite IHP; auto.
  + repeat rewrite Lca_Name_Open_Close_Subst; auto.
    rewrite IHP; auto.
  + repeat rewrite Lca_Name_Open_Close_Subst; auto.
    rewrite IHP; auto.
Qed.





Lemma Lca_Bex :
forall (P : Process)(i j k : nat),
i < j -> j < k -> 
lca k (P) -> lca k ({i <~> j} P).
Proof.
  intro.
  induction P; 
    try intros;
    try simpl; 
    try inversions H1; 
    try constructor; 
    try apply Lca_Name_Bex; 
    try apply IHP; try lia; auto.
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











