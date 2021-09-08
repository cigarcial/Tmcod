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

From old Require Import Defs_Process.
From old Require Import Defs_Tactics.

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



































From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.



Lemma List_Sk_char :
forall (k : nat)(L : list nat),
(length L) = S k -> 
(exists (x : nat)(L0 : list nat), L = x :: L0 /\ (length L0) = k).
Proof.
  intros.
  destruct L.
  + simpl in H.
    lia.
  + exists n. 
    exists L.
    auto.
Qed.



Lemma MOpen_Name_FName :
forall (k x : nat)( L : list nat), 
(length L) = k -> 
MOpen_Name_Rec k L (FName x) = FName x.
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
Qed.


(*
*)
Lemma MOpen_Name_BName_Gt :
forall (k i : nat)(L : list nat),
(length L) = k -> k <= i -> 
MOpen_Name_Rec k L (BName i) = (BName i).
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; try lia.
    rewrite Open_Name_BName_Gt; auto.
Qed.



(*
*)
Lemma MOpen_Name_Result : 
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> lca_name k x -> 
exists (x0 : nat), ( MOpen_Name_Rec k L x) = FName x0.
Proof.
  induction k; intros.
  + apply Lca_Zero_Lc_Name in H0.
    apply length_zero_iff_nil in H.
    rewrite H.
    simpl.
    inversions H0.
    exists x0.
    auto.
  + inversions H0.
    - rewrite MOpen_Name_FName;
       try exists x0; auto.
    - specialize (List_Sk_char k L H) as HL.
      destruct HL as [x [ L0 [HL HT]]].
      rewrite HL.
      simpl.
      assert (HA : k = i \/ i < k). { lia. }
      destruct HA.
      * assert ( HB: k <= i ). { lia. }
        rewrite MOpen_Name_BName_Gt; auto.
        rewrite Open_Name_BName_Eq; auto.
        exists x; auto.
      * assert (Hk : lca_name k ((BName i)) ).
        constructor; auto.
        specialize (IHk L0 (BName i) HT Hk).
        destruct IHk.
        rewrite H3.
        simpl.
        exists x0.
        auto.
Qed.


(*
*)
Lemma MOpen_Name_Rec_lc :
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> lca_name k x -> 
lc_name ( MOpen_Name_Rec k L x).
Proof.
  intros.
  specialize (MOpen_Name_Result k L x H H0) as HA.
  destruct HA as [x0 HA].
  rewrite HA.
  constructor.
Qed.


(*
*)
Lemma M2Open_MOpen :
forall (k x : nat)(L : list nat)(P : Process),
(length L) = k -> 
({0 ~> x} M2Open_Rec k L P) = MOpen_Rec (S k) (L ++ (x :: nil)) P.
Proof.
  induction k.
  + intros. 
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl. 
    rewrite <- IHk; auto.
    rewrite Exchange_Open; auto.
Qed.


(*
*)
Lemma MOpen_Pzero : 
forall (k : nat)(L : list nat),
(length L) = k -> MOpen_Rec k L (θ) = θ.
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
Qed.


(*
*)
Lemma MOpen_Fuse :
forall (k : nat)(L : list nat)(x y : Name),
(length L) = k -> 
MOpen_Rec k L ([x ←→ y]) = [(MOpen_Name_Rec k L x) ←→ (MOpen_Name_Rec k L y)].
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    simpl.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
Qed.



(*
*)
Lemma MOpen_Parallel : 
forall (k : nat)(L : list nat)( P Q : Process),
(length L) = k ->
MOpen_Rec k L (P ↓ Q) = (MOpen_Rec k L P) ↓ (MOpen_Rec k L Q).
Proof.
  induction k.
  + intros.
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    specialize (List_Sk_char k L H) as HL.
    destruct HL as [x [ L0 [HL HT]]].
    rewrite HL.
    simpl. 
    rewrite IHk; auto.
Qed.


(*
*)
Lemma MOpen_Chan_output :
forall (k : nat)(L : list nat)( x y : Name)(P : Process),
(length L) = k -> 
MOpen_Rec k L (x « y »· P) = (MOpen_Name_Rec k L x) « (MOpen_Name_Rec k L y) »· (MOpen_Rec k L P).
Proof.
   induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl. 
    rewrite IHk; auto.
Qed. 


(*
*)
Lemma MOpen_Chan_zero :
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> 
MOpen_Rec k L (x ·θ) = (MOpen_Name_Rec k L x) ·θ.
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
Qed.



(*
*)
Lemma MOpen_Chan_close :
forall (k : nat)(L : list nat)(x : Name)(P : Process),
(length L) = k -> 
MOpen_Rec k L (x ()·P) = (MOpen_Name_Rec k L x) ()·(MOpen_Rec k L P).
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
Qed.


(*
*)
Lemma MOpen_Chan_res :
forall (k : nat)(L : list nat)(P : Process), 
(length L) = k -> 
MOpen_Rec k L (ν P) = (ν M2Open_Rec k L P).
Proof.
  induction k.
  + intros.
    simpl.
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    specialize (List_Sk_char k L H) as HL.
    destruct HL as [x [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
Qed.

(*
*)
Lemma MOpen_Chan_input : 
forall (k : nat)(L : list nat)(x : Name)(P : Process),
(length L) = k -> 
MOpen_Rec k L (x · P) = (MOpen_Name_Rec k L x) · (M2Open_Rec k L P).
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
Qed.


(*
*)
Lemma MOpen_Chan_replicate : 
forall (k : nat)(L : list nat)(x : Name)(P : Process),
(length L) = k -> 
MOpen_Rec k L (x !· P) = (MOpen_Name_Rec k L x) !· (M2Open_Rec k L P).
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
Qed.



(*
*)
Theorem Lca_Lc_Process_MOpen : 
forall (P : Process)(k : nat)(L : list nat),
(length L) = k -> 
lca k P -> lc (MOpen_Rec k L P).
Proof.
  induction P; intros; inversions H0.
  + rewrite MOpen_Pzero; constructor.
  + rewrite MOpen_Fuse; auto.
    constructor; 
    apply MOpen_Name_Rec_lc; auto.
  + rewrite MOpen_Parallel; constructor; auto.
  + rewrite MOpen_Chan_output; auto.
    constructor; 
    try apply MOpen_Name_Rec_lc; auto.
  + rewrite MOpen_Chan_zero; auto.
    constructor; 
    try apply MOpen_Name_Rec_lc; auto.
  + rewrite MOpen_Chan_close; auto.
    constructor;
    try apply MOpen_Name_Rec_lc; auto.
  + rewrite MOpen_Chan_res; auto.
    constructor.
    intros.
    rewrite M2Open_MOpen; auto.
    apply IHP; auto.
    rewrite app_length; simpl; lia.
  + rewrite MOpen_Chan_input; auto.
    inversions H0.
    constructor;
    try apply MOpen_Name_Rec_lc; auto.
    intros.
    rewrite M2Open_MOpen; auto.
    apply IHP; auto.
    rewrite app_length; simpl; lia.
  + rewrite MOpen_Chan_replicate; auto.
    inversions H0.
    constructor;
    try apply MOpen_Name_Rec_lc; auto.
    intros.
    rewrite M2Open_MOpen; auto.
    apply IHP; auto.
    rewrite app_length; simpl; lia.
Qed.






(*
*)

(*
*)
Lemma MOpen_Chan_zero_FName_NoMOpenName :
forall (k x : nat)( L : list nat), 
(length L) = k -> 
MOpen_Rec k L (FName x ·θ) = FName x ·θ.
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
Qed.


(* (*
*)
Lemma MOpen_Chan_zero_BName_Eq_NoMOpenName :
forall (k i : nat)(L : list nat),
(length L) = k -> k <= i -> 
MOpen_Rec k L (BName i ·θ) = (BName i ·θ).
Proof.
  induction k; intros.
  + rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + specialize (List_Sk_char k L H) as HL.
    destruct HL as [x0 [ L0 [HL HT]]].
    rewrite HL.
    simpl.
    rewrite IHk; auto.
    simpl.
    admit.
    lia.
Admitted.


(*
*)
Lemma MOpen_Chan_zero_NoMOpenName :
forall (k : nat)(L : list nat)(x : Name),
(length L) = k -> lca k (x·θ) -> 
exists (y : nat), MOpen_Rec k L (x ·θ) = (FName y)·θ.
Proof.
  induction k.
  + intros.
    inversions H0.
    apply Lca_Zero_Lc_Name in H3.
    inversions H3.
    exists x0.
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    inversions H0.
    inversions H3.
    - exists x0.
      rewrite MOpen_Chan_zero_FName_NoMOpenName; auto.
    - specialize (List_Sk_char k L H) as HL.
      destruct HL as [x [ L0 [HL HT]]].
      rewrite HL.
      simpl.
      assert (HA : k = i \/ i < k). { lia. }
      destruct HA.
      * assert ( HB: k <= i ). { lia. }
        specialize (MOpen_Chan_zero_BName_Eq k i L0 HT HB) as HC.
        rewrite HC.
        simpl.
        admit.
      * assert (Hk : lca k ((BName i) ·θ) ).
        constructor; constructor; auto.
        specialize (IHk L0 (BName i) HT Hk).
        destruct IHk.
        rewrite H4; 
        simpl.
        exists x0.
        auto.
Admitted.

 *)