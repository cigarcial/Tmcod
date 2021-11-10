(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021 set-reglas
  
  This file contains the tactis and Hint Db for the proofs.
*)
From Tmcod Require Import Defs_Proposition.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Tactics.

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


Inductive Snoc : Type :=
  | nil : Snoc
  | cons : Snoc -> Assignment -> Snoc.


(**
  The following definitions are required to work with Ensembles or the representation for sets given by Coq.
*)
Definition Context := Snoc.


(**
*)
Fixpoint In (A : Assignment)(C : Snoc) : Prop :=
match C with 
  | nil => False 
  | cons D a => A = a \/ In A D
end.


(**
*)
Fixpoint app (C D : Snoc) : Snoc :=
match D with 
  | nil => C
  | cons E a => cons (app C E) a
end.


Notation "L ++ M " := (app L M).


(**
*)
Definition Bld ( x : nat )( A : Proposition ) : Context := cons nil (FName x:A).
#[global] 
Hint Resolve Bld : Piull.


(**
*)
Definition BldA ( X : Assignment ) : Context := cons nil X.
#[global]
Hint Resolve BldA : Piull.


(**
*)
Lemma Snoc_appr :
forall ( L : Context ),
L = (nil ++ L).
Proof.
  intros.
  induction L; Piauto.
  simpl.
  rewrite <- IHL.
  Piauto.
Qed.
#[global]
Hint Resolve Snoc_appr : Piull.


Lemma Snoc_appl :
forall ( L : Context ),
L = (L ++ nil).
Proof.
  Piauto.
Qed.
#[global]
Hint Resolve Snoc_appl : Piull.
  
  
Lemma Snoc_app_inv :
forall (L M : Snoc)(A : Assignment),
In A (L ++ M) -> (In A L \/ In A M).
Proof.
  intros.
  induction M.
  + rewrite <- Snoc_appl in H.
    OrSearch.
  + simpl.
    simpl in H.
    destruct H; try OrSearch.
    specialize (IHM H).
    destruct IHM; OrSearch.
Qed.
#[global]
Hint Resolve Snoc_app_inv : Piull.














