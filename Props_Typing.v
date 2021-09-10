(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.

From Tmcod Require Import Defs_Typing.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Proposition.
From Tmcod Require Import Props_Process.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Defs_Tactics.
Require Import Coq.Program.Equality.

Theorem One : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P === Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros.
  inversions H0.
  + admit.
  + admit.
  + 


Admitted.



Lemma Fuse_No_Reduces :
forall (x y : Name)(Q : Process), 
~([x ←→  y] --> Q ).
Proof.
Admitted.


(*
Teorema 2.1 del artículo.
*)
Theorem Soundness : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P --> Q) -> ( D ;;; F !- Q ::: G ).
Proof.
  intros P D F G H.
  dependent induction H.
  + intros.
    induction H2.








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
