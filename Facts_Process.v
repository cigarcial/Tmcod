(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the definitions for the processes.
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Sets.Constructive_sets.

From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Facts_Names.


(**
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
#[global]
Hint Resolve Body_Parallel_Body_Each : Piull.


(**
*)
Lemma Body_Process_Equivalence_Res :
forall (P : Process),
Body P <-> lc (ν P).
Proof.
  split;
  intros; try inversions H; Piauto.
Qed.
#[global]
Hint Resolve Body_Process_Equivalence_Res : Piull.


(**
*)
Lemma Exchange_Open :
forall ( P : Process)(x y k i : nat),
i <> k -> 
{i ~> y} ( {k ~> x} P ) = {k ~> x} ( {i ~> y} P ).
Proof.
  induction P; intros; simpl; Piauto.
  + destruct x;
     destruct y;
        try rewrite (Eq_Open_Name i y0 k x0 _); 
        try rewrite (Eq_Open_Name i y0 k x0 i1);
        Piauto.
  + rewrite IHP1; Piauto.
    rewrite IHP2; Piauto.
  + rewrite IHP; auto.
    destruct x;
     destruct y;
        try rewrite (Eq_Open_Name i y0 k x0 _); 
        try rewrite (Eq_Open_Name i y0 k x0 i1); Piauto.
  + destruct x;
      try rewrite (Eq_Open_Name i y k x0 i0); Piauto.
  + rewrite IHP; auto.
    destruct x;
      try rewrite (Eq_Open_Name i y k x0 i0); Piauto.
  + rewrite IHP; auto.
  + rewrite IHP; auto.
    destruct x;
      try rewrite (Eq_Open_Name i y k x0 i0); Piauto.
  + rewrite IHP; auto.
    destruct x;
      try rewrite (Eq_Open_Name i y k x0 i0); Piauto.
Qed.
#[global]
Hint Resolve Exchange_Open : Piull.


(**
*)
Lemma Subst_Open_Exchange :
forall ( P : Process )( x y z w k: nat ),
FName w = (Subst_Name x y (FName z)) -> 
{y \ x} ({k ~> z} P) = {k ~> w} ({y \ x} P).
Proof.
  induction P; intros; simpl;
    repeat rewrite (Subst_Name_Open_Name_Ex _ _ _ _  w _ );
    try rewrite (IHP _ _ _ w _);
    try rewrite (IHP1 _ _ _ w _);
    try rewrite (IHP2 _ _ _ w _);
    Piauto.
Qed.
#[global]
Hint Resolve Subst_Open_Exchange : Piull.


(**
*)
Lemma Subst_By_Equal :
forall ( P : Process )( x : nat ),
{ x \ x } P = P.
Proof.
  InductionProcess P Subst_Name_By_Equal.
Qed.
#[global]
Hint Resolve Subst_By_Equal : Piull.


(**
*)
Lemma Equal_Process_Equal_Open : 
forall ( x : nat )( P Q: Process ),
(P = Q ) -> (Open_Rec 0 x P = Open_Rec 0 x Q).
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.
#[global]
Hint Resolve Equal_Process_Equal_Open : Piull.


(**
*)
Lemma Process_Lca_Open_S :
forall ( P : Process )(i: nat),
(forall (x : nat), lca i ({i ~> x} P)) -> lca (S i) P.
Proof.
  intro.
  induction P; intros; Piauto.
  + constructor;
      apply (Lca_Name_Open _ _);
      intros;
      specialize (H x0);
      inversions H; auto.
  + constructor;
      apply (IHP1 _) || apply (IHP2 _);
      intros;
      specialize (H x);
      inversions H;
      auto.
  + constructor;
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
      try apply (Lca_Name_Open _ _);
      try intros;
      try specialize (H x0);
      try inversions H; auto.
  + constructor.
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
#[global]
Hint Resolve Process_Lca_Open_S : Piull.


(**
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
#[global]
Hint Resolve Lca_Process_Rd : Piull.


(**
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
#[global]
Hint Resolve Subst_Lca_Process : Piull.


(**
*)
Lemma Lca_Name_Open_Close_Subst :
forall ( x : Name )( x0 y k : nat),
lca_name k x -> 
Open_Name k y (Close_Name k x0 x) = Subst_Name x0 y x.
Proof.
  intros.
  inversions H; simpl.
  + DecidSimple x1 x0.
  + DecidSimple k i.
Qed.
#[global]
Hint Resolve Lca_Name_Open_Close_Subst : Piull.


(**
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
#[global]
Hint Resolve Lca_Open_Close_Subst : Piull.


(**
*)
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
#[global]
Hint Resolve Lca_Bex : Piull.


(**
*)
Lemma Subst_Bex_Exchange_Names :
forall (N : Name)(x u i j : nat),
i <> j -> Subst_Name x u (Bex_Name i j N) =  Bex_Name i j (Subst_Name x u N) .
Proof.
  intros.
  destruct N; simpl.
  + DecidSimple x0 x.
  + DecidSimple i0 i.
    rewrite n.
    DecidSimple i0 j.
Qed.
#[global]
Hint Resolve Subst_Bex_Exchange_Names : Piull.


(**
*)
Lemma Subst_Bex_Exchange :
forall ( P : Process)(u x i j : nat),
i <> j -> {u \ x} ({i <~> j} P) =  {i <~> j} ( {u \ x} P).
Proof.
  InductionProcess P Subst_Bex_Exchange_Names.
Qed.
#[global]
Hint Resolve Subst_Bex_Exchange : Piull.


(**
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
  DecidSimple y x.
Qed.
#[global]
Hint Resolve Subst_Open_NEq_Exchange : Piull.


(**
*)
Lemma Subst_Open_Eq_Exchange_Names :
forall (N : Name)(x u i : nat),
Subst_Name x u (Open_Name i x N) = Open_Name i u (Subst_Name x u N).
Proof.
  intros.
  destruct N; simpl.
  + DecidSimple x0 x.
  + DecidSimple i i0.
    simpl.
    DecidSimple x x.
Qed.
#[global]
Hint Resolve Subst_Open_Eq_Exchange_Names : Piull.


(**
*)
Lemma Subst_Open_Eq_Exchange :
forall ( Q : Process)(u x i: nat),
({u \ x} ({i ~> x} Q )) = {i ~> u}({u \ x} Q).
Proof.
  InductionProcess Q Subst_Open_Eq_Exchange_Names.
Qed.
#[global]
Hint Resolve Subst_Open_Eq_Exchange : Piull.


(**
*)
Lemma Equality_Subst_Equality :
forall (P Q : Process)(x u : nat),
P = Q -> {x \ u} P = {x \ u} Q.
Proof.
  intros.
  rewrite H.
  auto.
Qed.
#[global]
Hint Resolve Equality_Subst_Equality : Piull.


(**
*)
Lemma Subst_Close_By_Equal_Name_Names :
forall (u y i : nat)(x : Name),
Subst_Name y u (Close_Name i y x) = Close_Name i y x.
Proof.
  destruct x; auto.
   simpl.
   DecidSimple x y.
   rewrite n.
   simpl.
   DecidSimple x y.
   apply beq_nat_true in e.
   apply beq_nat_false in n.
   lia.
Qed.
#[global]
Hint Resolve Subst_Close_By_Equal_Name_Names : Piull.


(**
*)
Lemma Subst_Close_By_Equal_Name :
forall (P : Process)(u x i: nat),
{u \ x} Close_Rec i x P = Close_Rec i x P.
Proof.
  InductionProcess P Subst_Close_By_Equal_Name_Names.
Qed.
#[global]
Hint Resolve Subst_Close_By_Equal_Name : Piull.


(**
*)
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
      DecidSimple u z.
    - apply not_true_iff_false in n.
      apply not_true_iff_false in n0.
      rewrite n. rewrite n0.
      simpl.
      rewrite n. rewrite n0.
      auto.
Qed.
#[global]
Hint Resolve Subst_Close_Dif_Name_Names : Piull.


(**
*)
Lemma Subst_Close_Dif_Name :
forall (P : Process)(u x i z: nat),
x <> z -> u <> z -> 
{u \ x} Close_Rec i z P = Close_Rec i z ({u \ x}P).
Proof.
  InductionProcess P Subst_Close_Dif_Name_Names.
Qed.
#[global]
Hint Resolve Subst_Close_Dif_Name : Piull.


(**
*)
Lemma Double_Subst_AlreadySubst_Eq_Names :
forall (x0 u y0 : nat)(x : Name),
x0 <> y0 ->
Subst_Name x0 u (Subst_Name x0 y0 x) = Subst_Name x0 y0 x.
Proof.
  intros.
  destruct x; auto.
  simpl.
  DecidSimple x x0; simpl.
  + DecidSimple y0 x0.
  + repeat (rewrite n; simpl).
    auto.
Qed.
#[global]
Hint Resolve Double_Subst_AlreadySubst_Eq_Names : Piull.


(**
*)
Lemma Double_Subst_AlreadySubst_Eq :
forall (P : Process)( u x y : nat),
x <> y -> 
({u \ x} ({y \ x} P)) = {y \ x} P.
Proof.
  InductionProcess P Double_Subst_AlreadySubst_Eq_Names.
Qed.
#[global]
Hint Resolve Double_Subst_AlreadySubst_Eq : Piull.


(**
*)
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
  DecidSimple x x0; simpl.
  + DecidSimple u u.
  + rewrite n; simpl.
    DecidSimple x u.
Qed.
#[global]
Hint Resolve Double_Subst_Expan_NFVar_Names : Piull.


(**
*)
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
#[global]
Hint Resolve Double_Subst_Expan_NFVar : Piull.


(**
*)
Lemma Double_Subst_By_Same_Name_Names :
forall (x : Name)(x0 u x1 : nat),
Subst_Name x0 u (Subst_Name x1 x0 x) = Subst_Name x1 u (Subst_Name x0 u x).
Proof.
  destruct x; auto.
  intros.
  simpl.
  DecidSimple x x1; simpl.
  + DecidSimple x x0; simpl.
    - DecidSimple x0 x0; simpl.
      DecidSimple u x1; simpl.
    - DecidSimple x0 x0; simpl.
      rewrite n; simpl.
      DecidSimple x x1; simpl.
  + DecidSimple x x0; simpl.
    - DecidSimple x0 x0; simpl.
      rewrite n; simpl.
      rewrite e; simpl.
      DecidSimple u x1; simpl.
    - DecidSimple x0 x0; simpl.
      rewrite n0; simpl.
      rewrite n; simpl.
      rewrite n0; simpl.
      auto.
Qed.
#[global]
Hint Resolve Double_Subst_By_Same_Name_Names : Piull.


(**
*)
Lemma Double_Subst_By_Same_Name :
forall (P : Process)(u x x0 : nat),
({u \ x} ({x \ x0} P)) = ({u \ x0} ({u \ x} P)).
Proof.
  InductionProcess P Double_Subst_By_Same_Name_Names.
Qed.
#[global]
Hint Resolve Double_Subst_By_Same_Name : Piull.


(**
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
      DecidSimple u x1.
    - apply not_true_iff_false in n.
      apply not_true_iff_false in n0.
      repeat (rewrite n; rewrite n0; simpl).
      auto.
Qed.
#[global]
Hint Resolve Double_Subst_All_Dif_Names : Piull.


(**
*)
Lemma Double_Subst_All_Dif :
forall (P : Process)(u x y x0 : nat),
x0 <> x -> y <> x -> u <> x0 ->
({u \ x} ({y \ x0} P)) = ({y \ x0} ({u \ x} P)).
Proof.
  induction P; intros; simpl;
    try rewrite (Double_Subst_All_Dif_Names x _ _ _ _);
    try rewrite (Double_Subst_All_Dif_Names y _ _ _ _);
    try rewrite IHP1;
    try rewrite IHP2;
    try rewrite IHP; Piauto.
Qed.
#[global]
Hint Resolve Double_Subst_All_Dif : Piull.


(**
*)
Lemma Close_Permutation_Names :
forall (x : Name)(i j u v : nat),
u <> v ->
Close_Name i u (Close_Name j v x) = Close_Name j v (Close_Name i u x).
Proof.
  intros.
  destruct x; simpl; Piauto.
  DecidSimple x v.
  + DecidSimple x u.
    - apply beq_nat_true in e.
      apply beq_nat_true in e0.
      lia.
    - rewrite n.
      simpl.
      rewrite e.
      Piauto.
  + DecidSimple x u.
    - rewrite n.
      simpl.
      rewrite e.
      Piauto.
    - rewrite n; rewrite n0.
      simpl.
      rewrite n; rewrite n0.
      Piauto.
Qed.
#[global]
Hint Resolve Close_Permutation_Names : Piull.


(**
*)
Lemma Close_Permutation :
forall (P : Process)(i j u v : nat),
u <> v ->
Close_Rec i u (Close_Rec j v P) = Close_Rec j v (Close_Rec i u P).
Proof.
  intro.
  induction P; intros; simpl;
    try rewrite Close_Permutation_Names;
    try rewrite (Close_Permutation_Names y _ _ _ _);
    try rewrite IHP1;
    try rewrite IHP2;
    try rewrite IHP; 
    Piauto.
Qed.
#[global]
Hint Resolve Close_Permutation : Piull.


(**
*)
Lemma IsClosingInj_inv :
forall (P : Process)(x y : nat),
IsClosingInj P x -> y = x.
Proof.
  intros.
  inversions H.
  ePiauto.
Qed.
#[global]
Hint Resolve IsClosingInj_inv : Piull.


(**
*)
Lemma Subst_Res :
forall ( P : Process )( u v : nat),
{u \ v} ( ν P ) = ν ( {u \ v}  P ).
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Subst_Res : Piull.


(**
*)
Lemma Subst_Parallel :
forall ( P Q : Process )( u x : nat),
{u \ x} (P ↓ Q ) = ({u \ x} P ) ↓ ({u \ x}Q ).
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Subst_Parallel : Piull.


(**
*)
Lemma IsClosing_Process :
forall ( P Q : Process )( x0 : nat ),
IsClosing P x0 -> IsClosing Q x0.
Proof.
  constructor.
  intros.
  inversions H.
  specialize (H1 u v ({u \ v} Close x0 P)).
  Piauto.
Qed.
#[global]
Hint Resolve IsClosing_Process : Piull.


(**
*)
Lemma IsClosingInj_Process :
forall ( P Q : Process )( x0 : nat ),
IsClosingInj P x0 -> IsClosingInj Q x0.
Proof.
  constructor.
  intros.
  inversions H.
  specialize (H1 u (Close x0 P)).
  Piauto.
Qed.
#[global]
Hint Resolve IsClosingInj_Process : Piull.


(**
*)
Lemma IsClosing_inv :
forall ( P : Process )( x0 u v : nat ),
(IsClosing P x0) -> u <> x0 /\ x0 <> v.
Proof.
  intros.
  inversions H.
  eauto with Piull.
Qed.
#[global]
Hint Resolve IsClosing_inv : Piull.


(** FVars_Close_NotIn
*)
Lemma Close_Res_Rew :
forall (P : Process)(u i: nat),
Close_Rec i u (ν P) = (ν (Close_Rec (S i) u P)).
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Close_Res_Rew : Piull.


