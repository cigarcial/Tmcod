(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.

From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Defs_Proposition.
From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Typing.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Props_Process.


Require Import Coq.Program.Equality.

Lemma Inv_Subst_Zero :
forall (P : Process)(x0 u : nat),
{x0 \ u} P = θ -> P = θ.
Proof.
  intros.
  induction P; try discriminate; auto.
Qed.


Lemma No_Typing_Zero : 
forall (D F G : list Assignment),
~( D ;;; F !- θ ::: G ).
Proof.
  unfold not.
  intros.
  dependent induction H.
  + apply Inv_Subst_Zero in x. auto.
  + apply Inv_Subst_Zero in x; auto.
Qed.



(*
Teorema 2.1 del artículo.
*)
Theorem Soundness : 
forall (P : Process)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> forall (Q : Process), (P --> Q) -> ( D ;;; F !- Q ::: G ).
Proof.
Admitted.


Axiom Refl_Cong :
forall (P : Process),
P === P.


Axiom Sym_Cong :
forall (P Q : Process),
P === Q -> Q === P.



Axiom Trans_Cong :
forall (P Q R : Process),
P === Q -> Q === R -> P === R.


Lemma Red_1 :
forall (x y : Name),
lc_name x -> lc_name y-> 
[x ←→ y ] --> θ.
Proof.
  intros.
  assert ( H1 : [x ←→ y ] === [x ←→ y]↓θ).
  apply Sym_Cong.
  apply Con_parallel_zero.
  assert ( H2 : ([x ←→ y]↓θ) === (θ↓[x ←→ y]) ).
  apply Con_conmt_parallel.
  assert ( H3 : [x ←→ y ] === θ↓[x ←→ y] ).
  apply (Trans_Cong _ ([x ←→ y]↓θ) _ ); auto.
  assert (H4 : θ === θ). apply Refl_Cong.
  assert (H5 : (θ↓[x ←→ y]) --> θ).
  inversions H. inversions H0.
  apply Red_parallel_fuse.
  auto.
  constructor.
  unfold not.
  intro.
  inversions H5.
  apply (Red_reduction_struct _ _ (θ↓[x ←→ y]) (θ) ); auto.
  apply Sym_Cong; auto.
Qed.


Theorem Contradiction :
forall (D : list Assignment)(x y : Name)( A : Proposition), 
Collect D -> lc_name x -> lc_name y -> False.
Proof.
  intros.
  assert (HA : D ;;; ( cons (x:A) nil ) !- ([x←→y]) ::: ( cons (y:A) nil ) ).
  constructor; auto.
  apply (No_Typing_Zero D ( cons (x:A) nil ) ( cons (y:A) nil ) ) .
  apply (Soundness ([x ←→ y]) ); auto.
  apply Red_1; auto.
Qed.


Lemma ABC :
forall ( D : list Assignment)( x y : Name )( A : Proposition),
Collect D -> lc_name x -> lc_name y -> 
D;;; (x : A) :: nil !- θ ::: ((y : A) :: nil).
Proof.
  intros.
  assert (HA : D ;;; ( cons (x:A) nil ) !- ([x←→y]) ::: ( cons (y:A) nil ) ).
  constructor; auto.
  apply (Soundness ([x ←→ y]) ); auto.
  apply Red_1; auto.
Qed.


Lemma False_True :
forall (x y : Name)( A : Proposition), 
lc_name x -> lc_name y -> False.
Proof.
  intros.
  apply (No_Typing_Zero nil ( cons (x:A) nil ) ( cons (y:A) nil ) ) .
  apply ABC; auto.
  
  constructor; intros.
  inversions H2.
Qed.















