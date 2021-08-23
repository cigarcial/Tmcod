(*
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
*)

(*
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
Resultados generales relacionadas con las operaciones sobre nombres
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
*)


From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Bool.Bool.
From Coq Require Import Lia.

From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Tactics.

(*
*)
Lemma Open_Name_BName_Eq : 
forall (k i x : nat),
k = i -> 
Open_Name k x (BName i) = FName x.
Proof.
  intros.
  inversion H.
  simpl.
  destruct (bool_dec (i =? i) true).
  + rewrite e. auto.
  + apply not_true_iff_false in n.
    apply beq_nat_false in n; contradiction.
Qed.


(*
*)
Lemma Open_Name_BName_Gt : 
forall (k i x : nat),
k < i -> 
Open_Name k x (BName i) = BName i.
Proof.
  intros.
  destruct (bool_dec (k =? i) true); simpl.
  + apply beq_nat_true in e. lia.
  + apply not_true_iff_false in n.
    rewrite n.
    auto.
Qed.



(*
Siempre que se hace una sustitución sobre nombres solo se pueden obtener dos resultados, se remplaza o queda igual.
*)
Lemma Subst_Name_Output :
forall ( x y : nat )( z : Name ),
lc_name z -> ((Subst_Name x y z = (FName y)) \/ (Subst_Name x y z = z)).
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
lc_name y -> ( (Close_Name i x y = y) \/ (Close_Name i x y = BName i) ).
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
Lemma Output_LCName_Output :
forall ( p : Name )( k x : nat ),
lc_name p -> Open_Name k x p = p.
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
Resultados generales relacionadas con las operaciones sobre nombres a nivel k
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
*)


(*
*)
Lemma Lc_Lca_Zero_Name :
forall ( x : Name ),
lc_name x -> lca_name 0 x.
Proof.
  intros.
  inversions H.
  constructor.
Qed.


(*
*)
Lemma Lca_Zero_Lc_Name :
forall ( x : Name ),
lca_name 0 x -> lc_name x.
Proof.
  intros.
  destruct x.
  + constructor.
  + inversions H.
    lia.
Qed.


(*
*)
Lemma Lca_Name_Open :
forall (x : Name)(i : nat),
(forall (x0 : nat), lca_name i (Open_Name i x0 x)) -> lca_name (S i) x.
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
      specialize (H i).
      inversions H.
      constructor.
      auto.
Qed.


(*
*)
Lemma Lca_Name_Rd :
forall ( x : Name )( k y : nat ),
lca_name (S k) x -> lca_name k (Open_Name k y x).
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
Lemma Lca_Name_Close :
forall ( x : Name )( k y : nat ),
lca_name k x -> lca_name (S k) (Close_Name k y x).
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
Lemma Subst_Lca_Name :
forall ( x : Name )( k x0 y0 : nat),
lca_name k x -> lca_name k (Subst_Name x0 y0 x).
Proof.
  intros.
  inversions H.
  + specialize ( Subst_Name_Output x0 y0 (FName x1)) as HS.
    destruct HS; try rewrite H0; constructor.
  + constructor; auto.
Qed.






