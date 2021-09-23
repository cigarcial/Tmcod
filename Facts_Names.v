(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the basic facts concerning names.
*)
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Bool.Bool.
From Coq Require Import Lia.
From Coq Require Import Sets.Constructive_sets.

From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Tactics.


(**
  Inverse for the beq_nat_false lemma.
*)
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
#[global]
Hint Resolve beq_nat_false_inv : Piull.


(**
  Inverse for the beq_nat_true lemma.
*)
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
#[global]
Hint Resolve beq_nat_true_inv : Piull.


(**
*)
Ltac DecidEq :=
  match goal with
    | Gt : ?num0 = ?num1 |- _ =>  apply beq_nat_true_inv in Gt; rewrite Gt
  end;
  auto with Piull.


(**
*)
Lemma Open_Name_BName_Eq : 
forall (k i x : nat),
k = i -> 
Open_Name k x (BName i) = FName x.
Proof.
  intros.
  simpl.
  DecidEq.
Qed.
#[global]
Hint Resolve Open_Name_BName_Eq : Piull.


(**
*)
Lemma Open_Name_BName_Gt : 
forall (k i x : nat),
k < i -> 
Open_Name k x (BName i) = BName i.
Proof.
  intros.
  simpl.
  DecidSimple k i.
Qed.
#[global]
Hint Resolve Open_Name_BName_Gt : Piull.


(**
Siempre que se hace una sustitución sobre nombres solo se pueden obtener dos resultados, se remplaza o queda igual.
*)
Lemma Subst_Name_Output :
forall ( x y : nat )( z : Name ),
lc_name z -> ((Subst_Name x y z = (FName y)) \/ (Subst_Name x y z = z)).
Proof.
  intros.
  inversions H.
  simpl.
  DecidSimple x0 x.
Qed.
#[global]
Hint Resolve Subst_Name_Output : Piull.


(**
Análogamente, al cerrar un nombre solo hay dos opciones, se remplazar o queda igual.
*)
Lemma Close_Name_Output : 
forall ( i x : nat) ( y : Name), 
lc_name y -> ( (Close_Name i x y = y) \/ (Close_Name i x y = BName i) ).
Proof.
  intros.
  inversion H.
  simpl.
  DecidSimple x0 x.
Qed.
#[global]
Hint Resolve Close_Name_Output : Piull.


(**
*)
Lemma Open_BName_Output :
forall ( k x p : nat),
Open_Name k x (BName p) = BName p \/ Open_Name k x (BName p) = FName x.
Proof.
  intros.
  simpl.
  DecidSimple k p.
Qed.
#[global]
Hint Resolve Open_BName_Output : Piull.


(**
*)
Lemma Output_LCName_Output :
forall ( p : Name )( k x : nat ),
lc_name p -> Open_Name k x p = p.
Proof.
  intros.
  inversions H.
  auto.
Qed.
#[global]
Hint Resolve Output_LCName_Output : Piull.


(**
*)
Lemma Open_BName_IsFName_Eq :
forall ( k x p : nat),
Open_Name k x (BName p) = FName x -> k = p.
Proof.
  intros.
  simpl.
  DecidSimple k p.
  simpl in H.
  rewrite n in H.
  discriminate.
Qed.
#[global]
Hint Resolve Open_BName_IsFName_Eq : Piull.


(**
*)
Lemma Open_BName_IsBName_Eq :
forall ( k x p : nat),
Open_Name k x (BName p) = BName p -> k <> p.
Proof.
  intros.
  DecidSimple k p.
  simpl in H.
  rewrite e in H.
  discriminate.
Qed.
#[global]
Hint Resolve Open_BName_IsBName_Eq : Piull.


(**
*)
Lemma Eq_Open_Name :
forall ( i y k x p : nat),
i <> k -> 
Open_Name i y (Open_Name k x (BName p)) = Open_Name k x (Open_Name i y (BName p)).
Proof.
  intros.
  specialize ( Open_BName_Output k x p) as HA.
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
#[global]
Hint Resolve Eq_Open_Name : Piull.


(**
*)
Lemma Subst_BName_Output :
forall ( x y i : nat ),
Subst_Name x y (BName i) = BName i.
Proof.
  auto.
Qed.
#[global]
Hint Resolve Subst_BName_Output : Piull.


(**
*)
Lemma Subst_Name_Open_Name_Ex : 
forall ( x : Name )( x0 y0 z w k: nat ),
FName w = Subst_Name x0 y0 (FName z) -> 
Subst_Name x0 y0 (Open_Name k z x) = Open_Name k w (Subst_Name x0 y0 x).
Proof.
  intros.
  destruct x.
  + simpl.
    DecidSimple x x0.
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
#[global]
Hint Resolve Subst_Name_Open_Name_Ex : Piull.


(**
*)
Lemma Open_Close_FName : 
forall ( x y : nat ),
(Open_Name 0 x (Close_Name 0 y (FName y))) = (FName x).
Proof.
  intros.
  simpl.
  DecidSimple y y.
Qed.
#[global]
Hint Resolve Open_Close_FName : Piull.


(**
*)
Lemma Subst_Name_By_Equal :
forall ( x0 : nat )( x : Name ),
Subst_Name x0 x0 x = x.
Proof.
  intros.
  destruct x; auto.
  simpl.
  DecidSimple x x0.
Qed.
#[global]
Hint Resolve Subst_Name_By_Equal : Piull.



(**
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
lca names results
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
*)


(**
*)
Lemma Lc_Lca_Zero_Name :
forall ( x : Name ),
lc_name x -> lca_name 0 x.
Proof.
  intros.
  inversions H.
  Piauto.
Qed.
#[global]
Hint Resolve Lc_Lca_Zero_Name : Piull.


(**
*)
Lemma Lca_Zero_Lc_Name :
forall ( x : Name ),
lca_name 0 x -> lc_name x.
Proof.
  intros.
  destruct x; Piauto.
  inversions H.
  lia.
Qed.
#[global]
Hint Resolve Lca_Zero_Lc_Name : Piull.


(**
*)
Lemma Lca_Name_Open :
forall (x : Name)(i : nat),
(forall (x0 : nat), lca_name i (Open_Name i x0 x)) -> lca_name (S i) x.
Proof.
  intros.
  destruct x; Piauto.
  simpl in H.
  destruct (bool_dec (i =? i0) true).
  rewrite e in H.
  * constructor.
    apply beq_nat_true in e.
    lia.
  * apply not_true_iff_false in n.
    rewrite n in H.
    specialize (H i).
    inversions H.
    constructor.
    auto.
Qed.
#[global]
Hint Resolve Lca_Name_Open : Piull.


(**
*)
Lemma Lca_Name_Rd :
forall ( x : Name )( k y : nat ),
lca_name (S k) x -> lca_name k (Open_Name k y x).
Proof.
  intros.
  inversions H.
  - simpl. constructor.
  - assert ( HI : k = i \/ i < k ). { lia. }
    destruct HI; simpl; 
    DecidSimple k i.
Qed.
#[global]
Hint Resolve Lca_Name_Rd : Piull.


(**
*)
Lemma Lca_Name_Close :
forall ( x : Name )( k y : nat ),
lca_name k x -> lca_name (S k) (Close_Name k y x).
Proof.
  intros.
  inversions H; simpl; Piauto.
  DecidSimple x0 y.
Qed.
#[global]
Hint Resolve Lca_Name_Close : Piull.


(**
*)
Lemma Subst_Lca_Name :
forall ( x : Name )( k x0 y0 : nat),
lca_name k x -> lca_name k (Subst_Name x0 y0 x).
Proof.
  intros.
  inversions H; Piauto.
  specialize ( Subst_Name_Output x0 y0 (FName x1)) as HS.
  destruct HS; try rewrite H0; constructor.
Qed.
#[global]
Hint Resolve Subst_Lca_Name : Piull.


(**
*)
Lemma Lca_Name_Bex : 
forall (N : Name)( i j k : nat),
i < j -> j < k -> lca_name k N ->
lca_name k (Bex_Name i j N).
Proof.
  intros.
  destruct N; Piauto.
  inversions H1.
  simpl.
  DecidSimple i0 i.
  DecidSimple i0 j.
  + rewrite n.
    constructor; try lia; Piauto.
  + rewrite n.
    rewrite n0.
    Piauto.
Qed.
#[global]
Hint Resolve Lca_Name_Bex : Piull.


(**
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
#[global]
Hint Resolve Subst_Name_Gen_Output : Piull.











