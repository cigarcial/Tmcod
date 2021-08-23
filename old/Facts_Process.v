(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López 
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Ensembles.
From Coq Require Import Finite_sets.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Lia.

From Tmcod Require Import Defs_Process.


Lemma ProcessAt_One_Body :
forall ( P : Prepro ),
Process_At 1 P -> Body P.
Proof.
Admitted.


(*
*)
Lemma No_Union_No_Each : 
forall (x : nat)( X Y : FVarsE ),
~(x ∈ (X ∪ Y)) -> ~(x ∈ X) /\ ~(x ∈ Y).
Proof.
Admitted.


(*
*)
Lemma FVars_Name_Finite :
forall (x : Name),
Finite _ (FVars_Name x).
Proof.
  destruct x.
  + simpl. apply Singleton_is_finite.
  + simpl. constructor.
Qed.


(*
*)
Lemma FVars_Finite :
forall (P : Prepro),
Finite _ (FVars P).
Proof.
  induction P.
  + simpl.
    constructor.
  + simpl. apply Union_preserves_Finite; apply FVars_Name_Finite.
  + simpl. apply Union_preserves_Finite; auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + simpl. apply FVars_Name_Finite.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
Qed.


(*
*)
Lemma There_Is_A_Name :
forall ( P : Prepro ),
exists ( x : nat ), ~ ( x ∈ (FVars P) ).
Proof.
Admitted.


(*
*)
Lemma FVars_Name_No_Close :
forall (z k : nat)(x : Name),
~ (z ∈ FVars_Name x) -> (Close_Name k z x = x).
Proof.
  unfold not.
  intros.
  destruct x.
  + destruct (bool_dec (x =? z) true).
    - simpl in H. apply Nat.eqb_eq in e.
      rewrite e in H.
      assert ( HB : z ∈ Singleton nat z).
      { unfold In. constructor. }
      contradiction.
    - simpl. apply not_true_iff_false in n.
      rewrite n. auto.
  + auto.
Qed.


(*
*)
Lemma Close_NoFVar_Eq :
forall ( P : Prepro )(z k: nat),
~ ( z ∈ (FVars P) ) -> ( Close_Rec k z P ) = P.
Proof.
  unfold Close.
  induction P; intros.
  + auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP1; auto.
    rewrite IHP2; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [H HC].
    simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP; auto.
    rewrite FVars_Name_No_Close; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    simpl.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    simpl.
    rewrite IHP; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite IHP; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite IHP; auto.
Qed.


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
forall ( P Q : Prepro),
Body (P ↓ Q) -> (Body P /\ Body Q).
Proof.
  constructor; 
    try constructor;
    intros;
    inversions H;
    specialize (H2 L H0 x H1);
    simpl in H2;
    inversions H2; auto.
Qed.


(*
*)
Lemma Body_Process_Equivalence_Res :
forall (P : Prepro),
Body P <-> Process (ν P).
Proof.
  split.
  + intros.
    constructor. inversion H. auto.
  + intros.
    inversion H. constructor. auto.
Qed.


(*
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
Resultados generales relacionadas con las operaciones sobre nombres
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
*)


(*
Siempre que se hace una sustitución sobre nombres solo se pueden obtener dos resultados, se remplaza o queda igual.
*)
Lemma Subst_Name_Output :
forall ( x y : nat )( z : Name ),
Process_Name z -> ((Subst_Name x y z = (FName y)) \/ (Subst_Name x y z = z)).
Proof.
  intros.
  inversions H.
  simpl. 
  destruct (bool_dec (x0 =? x) true).
  + rewrite e. auto.
  + apply not_true_iff_false in n.
    rewrite n. auto.
Qed.


(*
Análogamente, al cerrar un nombre solo hay dos opciones, se remplazar o queda igual.
*)
Lemma Close_Name_Output : 
forall ( i x : nat) ( y : Name), 
Process_Name y -> ( (Close_Name i x y = y) \/ (Close_Name i x y = BName i) ).
Proof.
  intros.
  inversion H.
  simpl.
  destruct (bool_dec (x0 =? x) true).
  + rewrite e. auto.
  + apply not_true_iff_false in n.
    rewrite n. auto.
Qed.


(*
*)
Lemma Open_BName_Output :
forall ( k x p : nat),
Open_Name k x (BName p) = BName p \/ Open_Name k x (BName p) = FName x.
Proof.
  intros.
  simpl.
  destruct (bool_dec (k =? p) true).
  - rewrite e; auto.
  - apply not_true_iff_false in n.
    rewrite n; auto.
Qed.


(*
*)
Lemma Output_PName_Output :
forall ( p : Name )( k x : nat ),
Process_Name p -> Open_Name k x p = p.
Proof.
  intros.
  inversions H.
  auto.
Qed.


(*
*)
Lemma Open_BName_IsFName_Eq :
forall ( k x p : nat),
Open_Name k x (BName p) = FName x -> k = p.
Proof.
  intros.
  destruct (bool_dec (k =? p) true).
  + apply beq_nat_true; auto.
  + apply not_true_iff_false in n.
    simpl in H.
    rewrite n in H.
    discriminate.
Qed.


(*
*)
Lemma Open_BName_IsBName_Eq :
forall ( k x p : nat),
Open_Name k x (BName p) = BName p -> k <> p.
Proof.
  intros.
  destruct (bool_dec (k =? p) true).
  + simpl in H.
    rewrite e in H.
    discriminate.
  + apply not_true_iff_false in n.
    apply beq_nat_false; auto.
Qed.


(*
*)
Lemma Eq_Open_Name_Sk_i :
forall ( i y k x p : nat),
i <> (S k) -> 
Open_Name i y (Open_Name (S k) x (BName p)) = Open_Name (S k) x (Open_Name i y (BName p)).
Proof.
  intros.
  specialize ( Open_BName_Output (S k) x p) as HA.
  specialize ( Open_BName_Output i y p) as HB.
  destruct HA.
  + destruct HB.
    - congruence.
    - rewrite ?H0; rewrite ?H1.
      auto.
 + destruct HB.
  - rewrite H1; rewrite H0.
    auto.
  - apply Open_BName_IsFName_Eq in H0.
    apply Open_BName_IsFName_Eq in H1.
    lia.
Qed.


(*
*)
Lemma Subst_BName_Output :
forall ( x y i : nat ),
Subst_Name x y (BName i) = BName i.
Proof.
  intros.
  simpl.
  auto.
Qed.


(*
*)
Lemma Subst_Name_Open_Name_Ex : 
forall ( x : Name )( x0 y0 z w k: nat ),
FName w = Subst_Name x0 y0 (FName z) -> 
Subst_Name x0 y0 (Open_Name k z x) = Open_Name k w (Subst_Name x0 y0 x).
Proof.
  intros.
  destruct x.
  + simpl.
    destruct (bool_dec (x =? x0) true).
    - rewrite e. auto.
    - apply not_true_iff_false in n.
      rewrite n. auto.
  + specialize ( Open_BName_Output k z i ) as HA.
    destruct HA.
    - rewrite Subst_BName_Output.
      rewrite H0.
      specialize ( Open_BName_Output k w i ) as HB.
      destruct HB.
      * rewrite H1; auto.
      * apply Open_BName_IsFName_Eq in H1.
        apply Open_BName_IsBName_Eq in H0.
        contradiction.
    - rewrite Subst_BName_Output.
      rewrite H0.
      specialize ( Open_BName_Output k w i ) as HB.
      destruct HB.
      * apply Open_BName_IsFName_Eq in H0.
        apply Open_BName_IsBName_Eq in H1.
        contradiction.
      * rewrite H1.
        rewrite H.
        auto.
Qed.


(*
*)
Lemma Open_Close_FName : 
forall ( x y : nat ),
(Open_Name 0 x (Close_Name 0 y (FName y))) = (FName x).
Proof.
  intros.
  destruct (bool_dec (y =? y) true).
  + simpl. rewrite e; auto.
  + apply not_true_iff_false in n.
    apply beq_nat_false in n.
    contradiction.
Qed.


(*
*)
Lemma Subst_Name_By_Equal :
forall ( x0 : nat )( x : Name ),
Subst_Name x0 x0 x = x.
Proof.
  intros.
  destruct x.
  + simpl.
    destruct (bool_dec (x =? x0) true).
    - rewrite e.
      apply beq_nat_true in e.
      auto.
    - apply not_true_iff_false in n.
      rewrite n.
      auto.
  + auto.
Qed.


(*
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
Resultados generales relacionadas con las operaciones en preprocesos
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
*)


(*
*)
Lemma Exchange_Open_Sk_i :
forall ( P : Prepro)(x y k i : nat),
i <> S k -> 
{i ~> y} ( {S k ~> x} P ) = {S k ~> x} ( {i ~> y} P ).
Proof.
  induction P; intros.
  + auto.
  + simpl.
    destruct x.
    - destruct y.
      * auto.
      * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
    - destruct y.
      * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
      * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
        rewrite (Eq_Open_Name_Sk_i i y0 k x0 i1); auto.
  + simpl. 
    rewrite IHP1; auto.
    rewrite IHP2; auto.
  + simpl.
    rewrite IHP; auto.
     destruct x.
      - destruct y.
        * auto.
        * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
      - destruct y.
        * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
        * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
          rewrite (Eq_Open_Name_Sk_i i y0 k x0 i1); auto.
  + simpl.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name_Sk_i i y k x0 i0); auto.
  + simpl.
    rewrite IHP; auto.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name_Sk_i i y k x0 i0); auto.
  + simpl.
    apply f_equal.
    rewrite IHP; auto.
  + simpl.
    rewrite IHP; auto.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name_Sk_i i y k x0 i0); auto.
  + simpl.
    rewrite IHP; auto.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name_Sk_i i y k x0 i0); auto.
Qed.


(*
*)
Lemma Subst_Open_Exchange :
forall ( P : Prepro )( x y z w k: nat ),
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
forall ( P : Prepro )( x : nat ),
{ x \ x } P = P.
Proof.
  induction P; intros; simpl; repeat rewrite Subst_Name_By_Equal; try apply f_equal; auto.
  + rewrite IHP1.
    rewrite IHP2.
    auto.
Qed.


(*
*)
Lemma Equal_Prepro_Equal_Open : 
forall ( x : nat )( P Q: Prepro ),
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
Resultados generales relacionadas con las operaciones sobre nombres a nivel k
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
*)


(*
*)
Lemma Process_Name_Process_NameAt :
forall ( x : Name ),
Process_Name x -> Process_Name_At 0 x.
Proof.
  intros.
  inversions H.
  constructor.
Qed.


(*
*)
Lemma Process_NameAt_Zero :
forall ( x : Name ),
Process_Name_At 0 x -> Process_Name x.
Proof.
  intros.
  destruct x.
  + constructor.
  + inversions H.
    lia.
Qed.


(*
*)
Lemma Process_NameAt_Open :
forall (x : Name)(i x0 : nat),
Process_Name_At i (Open_Name i x0 x) -> Process_Name_At (S i) x.
Proof.
  intros.
  destruct x.
  - constructor.
  - simpl in H.
    destruct (bool_dec (i =? i0) true).
    rewrite e in H.
    * constructor.
      apply beq_nat_true in e.
      lia.
    * apply not_true_iff_false in n.
      rewrite n in H.
      inversions H.
      constructor.
      auto.
Qed.


(*
*)
Lemma Process_NameAt_Rd :
forall ( x : Name )( k y : nat ),
Process_Name_At (S k) x -> Process_Name_At k (Open_Name k y x).
Proof.
  intros.
  inversions H.
  - simpl. constructor.
  - assert ( HI : i = k \/ i < k ). { lia. }
    destruct HI.
    * simpl. 
      assert ( HI : k =? i = true ).
        { destruct (bool_dec (k =? i) true).
          + auto.
          + apply not_true_iff_false in n.
            apply beq_nat_false in n; auto.
        } 
      rewrite HI.
      constructor.
    * assert ( HI : k =? i = false ).
      { destruct (bool_dec (k =? i) true).
          + apply beq_nat_true in e. lia.
          + apply not_true_iff_false in n.
            auto.
        }
      simpl.
      rewrite HI. 
      constructor; auto.
Qed.


(*
*)
Lemma Process_NameAt_Close_Name :
forall ( x : Name )( k y : nat ),
Process_Name_At k x -> Process_Name_At (S k) (Close_Name k y x).
Proof.
  intros.
  inversions H.
  + destruct (bool_dec (x0 =? y) true).
    - simpl. rewrite e.
      constructor. auto.
    - apply not_true_iff_false in n.
      simpl. rewrite n.
      constructor.
  + simpl. constructor; auto.
Qed.


(*
*)
Lemma Subst_Process_NameAt :
forall ( x : Name )( k x0 y0 : nat),
Process_Name_At k x -> Process_Name_At k (Subst_Name x0 y0 x).
Proof.
  intros.
  inversions H.
  + specialize ( Subst_Name_Output x0 y0 (FName x1)) as HS.
    destruct HS; try rewrite H0; constructor.
  + constructor; auto.
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
Lemma Process_At_Open_S :
forall ( P : Prepro )( x i: nat),
Process_At i ({i ~> x} P) -> Process_At (S i) P.
Proof.
  intro.
  induction P.
  + intros.
    constructor.
  + intros.
    inversions H.
    constructor.
    - apply (Process_NameAt_Open _ _ x0); auto.
    - apply (Process_NameAt_Open _ _ x0); auto.
  + intros.
    inversions H.
    constructor.
    apply (IHP1 x _); auto.
    apply (IHP2 x _); auto.
  + intros.
    inversions H.
    constructor.
    - apply (Process_NameAt_Open _ _ x0); auto.
    - apply (Process_NameAt_Open _ _ x0); auto.
    - apply (IHP x0 _); auto.
  + intros.
    inversions H.
    constructor.
    apply (Process_NameAt_Open _ _ x0); auto.
  + intros.
    inversions H.
    constructor.
    - apply (Process_NameAt_Open _ _ x0); auto.
    - apply (IHP x0 _); auto.
  + intros.
    constructor.
    simpl in H.
    inversions H.
    specialize (IHP x (S i) H2).
    auto.
  + intros.
    inversions H.
    specialize (IHP x0 (S i) H4).
    constructor.
    - apply (Process_NameAt_Open _ _ x0); auto.
    - auto.
  + intros.
    inversions H.
    specialize (IHP x0 (S i) H4).
    constructor.
    - apply (Process_NameAt_Open _ _ x0); auto.
    - auto.
Qed.


(*
*)
Theorem Process_ProcessAt :
forall ( P : Prepro ), 
Process P -> Process_At 0 P.
Proof.
  intros.
  induction H;  
    constructor; 
    try apply Process_Name_Process_NameAt; 
    try specialize (FVars_Finite P) as FV;
    try specialize (There_Is_A_Name P) as HX;
    try destruct HX;
    try specialize (H0 (FVars P) FV x H1) || specialize (H1 (FVars P) FV x0 H2);
    try apply (Process_At_Open_S _ x _ ) || apply (Process_At_Open_S _ x0 _ );
    auto.
Qed.


(*
*)
Lemma Body_ProcessAt_One :
forall ( P : Prepro ),
Body P -> Process_At 1 P.
Proof.
  intros.
  apply Body_Process_Equivalence_Res in H.
  apply Process_ProcessAt in H.
  inversions H.
  auto.
Qed.


(*
*)
Lemma ProcessAt_Rd :
forall ( P : Prepro )( k x: nat ),
Process_At (S k) P -> Process_At k ({k ~> x} P).
Proof.
  intro.
  induction P; intros; simpl; try inversions H.
  + constructor.
  + constructor; apply Process_NameAt_Rd; auto.
  + constructor.
    apply IHP1; auto.
    apply IHP2; auto.
  + constructor; try apply Process_NameAt_Rd; auto.
  + constructor; try apply Process_NameAt_Rd; auto.
  + constructor; try apply Process_NameAt_Rd; auto.
  + simpl.
    constructor.
    inversions H.
    apply IHP; auto.
  + simpl.
    inversions H.
    constructor.
    - apply Process_NameAt_Rd; auto.
    - apply IHP; auto.
  + simpl.
    inversions H.
    constructor.
    - apply Process_NameAt_Rd; auto.
    - apply IHP; auto.
Qed.


(*
*)
Theorem ProcessAt_Process :
forall ( P : Prepro ),
Process_At 0 P -> Process P.
Proof.
  intro.
  induction P; intros; try inversions H.
  + auto.
  + constructor; apply Process_NameAt_Zero; auto.
  + constructor; auto.
  + constructor; try apply Process_NameAt_Zero; auto.
  + constructor; apply Process_NameAt_Zero; auto.
  + constructor; try apply Process_NameAt_Zero; auto.
  + apply ProcessAt_One_Body in H2.
    inversions H2.
    constructor; auto.
  + constructor.
    - try apply Process_NameAt_Zero; auto.
    - apply ProcessAt_One_Body in H4.
      inversions H4; auto.
  + constructor.
    - try apply Process_NameAt_Zero; auto.
    - apply ProcessAt_One_Body in H4.
      inversions H4; auto.
Qed.


(*
*)
Lemma Subst_Process_At :
forall ( P : Prepro )( k : nat ),
Process_At k P -> forall (x y : nat ), Process_At k ({y \ x} P).
Proof.
  intro.
  induction P; intros; simpl; try inversions H; try constructor; try apply Subst_Process_NameAt; auto.
Qed.


(*
*)
Lemma Process_NameAt_Open_Close_Subst :
forall ( x : Name )( x0 y k : nat),
Process_Name_At k x -> 
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
Lemma ProcessAt_Open_Close_Subst :
forall ( P : Prepro )( x y k : nat ), 
Process_At k P -> { k ~> y } Close_Rec k x P = { y \ x } P.
Proof.
  intros P.
  induction P; intros; simpl; inversions H; try auto.
  + repeat rewrite Process_NameAt_Open_Close_Subst; auto.
  + rewrite IHP1; auto.
    rewrite IHP2; auto.
  + repeat rewrite Process_NameAt_Open_Close_Subst; auto.
    rewrite IHP; auto.
  + repeat rewrite Process_NameAt_Open_Close_Subst; auto.
  + repeat rewrite Process_NameAt_Open_Close_Subst; auto.
    rewrite IHP; auto.
  + inversions H.
    rewrite IHP; auto.
  + repeat rewrite Process_NameAt_Open_Close_Subst; auto.
    rewrite IHP; auto.
  + repeat rewrite Process_NameAt_Open_Close_Subst; auto.
    rewrite IHP; auto.
Qed.









Lemma Process_Open_Close_Subst :
forall ( P : Prepro )( x y k : nat ), 
Process P -> { 0 ~> y } Close_Rec 0 x P = { y \ x } P.
Proof.
  intros.
  apply ProcessAt_Open_Close_Subst.
  apply Process_ProcessAt; auto.
Qed.









