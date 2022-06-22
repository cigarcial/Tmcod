(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021 set-reglas
  
  This file contains the tactis and Hint Db for the proofs.
*)
From Coq Require Import Ensembles.
From Coq Require Import Finite_sets.
From Coq Require Import Finite_sets_facts.

From Tmcod Require Import  Defs_Proposition.
From Tmcod Require Import  Defs_Process.
From Tmcod Require Import  Defs_Tactics.


(**
*)
Inductive Assignment : Type := assig ( x : Name )( A : Proposition ) : Assignment.
Notation " x : A " := (assig x A )(at level 60).
#[global]
Hint Constructors Assignment : Piull.


(**
*)
Inductive Assig : Assignment -> Prop :=
  is_assig :  forall (x : Name)(A:Proposition), lc_name x -> Assig ( x : A).
#[global]
Hint Constructors Assig : Piull.


(**
  The following definitions are required to work with Ensembles or the representation for sets given by Coq.
*)
Definition Context := Ensemble Assignment.


(**
*)
Inductive Collect : Context -> Prop := is_collect :
  forall L : Context,
  (forall H : Assignment, (H ∈ L) -> Assig H ) -> Collect L.
#[global] 
Hint Constructors Collect : Piull.


(**
*)
Inductive Injective : Context -> Prop := 
  is_linear : forall L : Context,
  (forall (x : nat)(A B : Proposition), ~ ( A <> B /\ ((FName x:A) ∈ L) /\ ((FName x:B) ∈ L)) ) 
  -> Injective L.
#[global] 
Hint Constructors Injective : Piull.


(**
*)
Inductive Fresh : nat -> Context -> Prop := 
  is_fresh : forall (x : nat)(L : Context),
  (forall (y : nat)(A : Proposition), ((FName y:A) ∈ L) -> x <> y ) 
  -> Fresh x L.
#[global] 
Hint Constructors Fresh : Piull.



(**
*)
Definition Bld ( x : nat )( A : Proposition ) : Context := Singleton _ (FName x:A).
#[global] 
Hint Resolve Bld : Piull.


(**
*)
Definition BldA ( X : Assignment ) : Context := Singleton _ X.
#[global]
Hint Resolve BldA : Piull.


(**
*)
Definition SMA (X : Context)(x : nat)(A : Proposition): Context := Setminus _ X (Bld x A).
#[global]
Hint Resolve SMA : Piull.


(**
*)
Definition Replace (X : Context)(u x: nat)(A : Proposition): Context := (Setminus _ X (Bld u A)) ∪ (Bld x A).
#[global]
Hint Resolve Replace : Piull.



(* (**
*)
Fixpoint Replace (u x : nat)(A : Proposition)(D : Context) : Context := 
match D with
  | nil  => nil
  | (FName u : A) :: L0 =>  (Bld x A) ++ (Replace u x A L0)
  | X :: L0 =>  (BldA X) ++ (Replace u x A L0)
end.
#[global]
Hint Resolve Replace : Piull.


(**
*)
Fixpoint Remove (x : nat)(A : Proposition)(D : Context) : Context := 
match D with
  | nil  => nil
  | (FName x : A) :: L0 =>  L0
  | X :: L0 =>  (BldA X) ++ (Remove x A L0)
end.
#[global]
Hint Resolve Remove : Piull. *)


(**
*)
Lemma In_SMA_In_Org :
forall (x u : nat)(A A0 : Proposition)(D : Context),
(FName x : A) ∈ SMA D u A0 -> (FName x : A) ∈ D.
Proof.
  intros.
  inversions H.
  auto.
Qed.
#[global]
Hint Resolve In_SMA_In_Org : Piull.


(**
*)
Lemma Setminus_Equality :
forall ( A : Context ),
Setminus _ A A = ø.
Proof.
  intros.
  apply Extensionality_Ensembles.
  constructor.
  + unfold Setminus.
    unfold Included.
    intros.
    inversions H.
    contradiction.
  + constructor;
    inversions H.
Qed.
#[global]
Hint Resolve Setminus_Equality : Piull.


(**
*)
Lemma SMA_Elimination :
forall (x : nat)(A : Proposition),
SMA (Bld x A) x A = ø.
Proof.
  intros.
  unfold SMA.
  Piauto.
Qed.
#[global]
Hint Resolve SMA_Elimination : Piull.


(**
*)
Lemma SMA_nil :
forall (x : nat)(A : Proposition),
SMA ø x A = ø.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set.
  constructor; unfold Included; intros; inversions H.
  inversions H0.
Qed.
#[global]
Hint Resolve SMA_nil : Piull.


(**
*)
Lemma SMA_Collect :
forall (G : Context)(x : nat)(A : Proposition),
Collect G -> Collect (SMA G x A).
Proof.
  intros.
  constructor.
  intros.
  inversions H1.
  inversions H.
  specialize (H4 H0 H2).
  Piauto.
Qed.
#[global]
Hint Resolve SMA_Collect : Piull.


(**
*)
Lemma Replace_Union :
forall (x u : nat)(A : Proposition)(D F : Context),
Replace (D ∪ F) u x A = ((Replace D u x A) ∪ (Replace F u x A)).
Proof.
  intros.
  apply Extensionality_Ensembles.
  constructor.
  + unfold Included.
    intros.
    unfold Replace in H.
    apply Union_inv in H.
    inversions H.
    - inversions H0.
      apply Union_inv in H1.
      destruct H1; OrSearch.
    - inversions H0; OrSearch.
  + unfold Included.
    intros.
    apply Union_inv in H.
    destruct H.
    - inversions H.
      * inversions H0; OrSearch.
      * OrSearch.
    - inversions H.
      * inversions H0; OrSearch.
      * OrSearch.
Qed.
#[global]
Hint Resolve Replace_Union : Piull.


(**
*)
Lemma SMA_Union_In :
forall (G : Context)(x : nat)(A : Proposition),
SMA ((Bld x A) ∪ G) x A = SMA G x A.
Proof.
  intros.
  apply Extensionality_Ensembles.
  constructor; unfold Included; intros.
  + constructor.
    - inversions H.
      apply Union_inv in H0.
      destruct H0; auto.
      contradiction.
    - inversions H; auto.
  + constructor;
     inversions H;
     OrSearch.
Qed.
#[global]
Hint Resolve SMA_Union_In : Piull.


(**
*)
Lemma Fresh_Union :
forall (D F : Context)(x : nat),
Fresh x (D ∪ F) -> Fresh x F.
Proof.
  intros.
  constructor.
  intros.
  inversions H.
  apply (H1 y A).
  OrSearch.
Qed.
#[global]
Hint Resolve Fresh_Union : Piull.



(**
*)
Lemma Replace_Bld :
forall (u x : nat)(A : Proposition),
Replace (Bld u A) u x A = Bld x A.
Proof.
  intros.
  unfold Replace.
  rewrite Setminus_Equality.
  rewrite Union_commutative.
  rewrite Empty_set_zero_right.
  auto.
Qed.
#[global]
Hint Resolve Replace_Bld : Piull.


Lemma Union_Collect_Collect :
forall ( A B : Context ),
Collect A -> Collect B -> Collect (A ∪ B).
Proof.
  intros.
  constructor.
  intros.
  apply Union_inv in H2.
  destruct H2.
  + inversions H.
    specialize (H3 H1 H2).
    Piauto.
  + inversions H0.
    specialize (H3 H1 H2).
    Piauto.
Qed.
#[global]
Hint Resolve Union_Collect_Collect : Piull.


(**
*)
Lemma Collect_After_Replace :
forall ( x y : nat )( A : Proposition )( D : Context),
Collect D -> Collect (Replace D x y A).
Proof.
  intros.
  constructor.
  intros.
  inversions H1.
  + inversions H2.
    inversions H.
    apply H5; Piauto.
  + inversions H2.
    repeat constructor.
Qed.
#[global]
Hint Resolve Collect_After_Replace : Piull.


(**
*)
Lemma Fresh_Replace :
forall ( x w z : nat )( A : Proposition )( D F G : Context ),
x <> w -> Fresh x ((D ∪ F) ∪ G) ->
Fresh x ((D ∪ Replace F z w A) ∪ G).
Proof.
  constructor.
  intros.
  unfold not.
  intros.
  subst.
  apply Union_inv in H1.
  destruct H1.
  + apply Union_inv in H1.
    destruct H1.
    - inversions H0.
      apply (H2 y A0); try OrSearchCons.
    - inversions H1.
      * inversions H2.
        inversions H0.
        apply (H5 y A0); try OrSearchCons.
      * inversions H2.
        contradiction.
  + inversions H0.
    apply (H2 y A0); try OrSearchCons.
Qed.
#[global]
Hint Resolve Fresh_Replace : Piull.


(**
*)
Lemma Context_Element_Partition :
forall ( x : nat )( A : Proposition ) ( F : Context ),
(FName x : A) ∈ F -> 
exists ( B : Context ), F = ((Bld x A) ∪ B).
Proof.
  intros.
  exists (SMA F x A).
  apply Extensionality_Ensembles.
  constructor; unfold Included; intros.
  + admit.
  + apply Union_inv in H0.
    destruct H0;
    inversions H0; Piauto.
Admitted.



(**
x, A  // x no está en A 
x -> y 
y, A 
*)
Lemma Replace_Union_Bld :
forall ( F : Context )( x y : nat )( A : Proposition),
Replace (Bld x A ∪ F) x y A = (Bld y A ∪ F).
Proof.
  intros.
  apply Extensionality_Ensembles.
  constructor; unfold Included; intros.
  + inversions H; try OrSearch.
    inversions H0.
    apply Union_inv in H1.
    destruct H1; try contradiction.
    OrSearch.
  + unfold Replace.
    inversions H; try OrSearch.
    left.
    constructor; try OrSearch.
    admit.
Admitted.
#[global]
Hint Resolve Replace_Union_Bld : Piull.


(**
(x, A) / x = A 
*)
Lemma SMA_Union_Bld :
forall ( G : Context )( x : nat )( A : Proposition),
SMA (Bld x A ∪ G) x A = G .
Proof.
  intros.
  apply Extensionality_Ensembles.
  constructor; unfold Included; intros.
  + inversions H.
    apply Union_inv in H0.
    destruct H0; try contradiction; Piauto.
  + constructor; try OrSearch.
    admit.
Admitted.
#[global]
Hint Resolve SMA_Union_Bld : Piull.


(**
*)
Lemma Replace_Context_Element_Partition :
forall ( x w : nat )( A : Proposition ) ( F : Context ),
(FName x : A) ∈ F -> 
exists ( B : Context ), F = ((Bld x A) ∪ B) /\ (Replace F x w A) = ((Bld w A) ∪ B).
Proof.
  intros.
  apply Context_Element_Partition in H.
  destruct H as [B Hb].
  exists B.
  rewrite Hb.
  rewrite Replace_Union_Bld.
  constructor; Piauto.
Qed.









