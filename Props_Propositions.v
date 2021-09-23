(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
*)
From Tmcod Require Import Defs_Proposition.
From Tmcod Require Import Defs_Tactics.


(**
  The dual operation is idempotent.
*)
Proposition Doble_Duality_ULLT  : 
forall A : Proposition , 
(A^⊥)^⊥ = A. 
Proof.
  StructuralInduction A.
Qed.
#[global]
Hint Resolve Doble_Duality_ULLT : Piull.


(**
  The definition of the linear implication is well defined.
*)
Proposition Dual_Implication_Tensor : 
forall A B : Proposition , 
((A −∘ B)^⊥) = (A ⊗ (B^⊥)).
Proof.
  intros.
  unfold ULLT_IMP.
  simpl.
  rewrite -> (Doble_Duality_ULLT A).
  reflexivity.
Qed.
#[global]
Hint Resolve Dual_Implication_Tensor : Piull.


(**
  Relation between duals, tensor and linear implication.
  The proof follows fron the definitions.
*)
Proposition Dual_Tensor_Implication :  
forall A B : Proposition, 
((A ⊗ B )^⊥) = (A −∘ (B^⊥)).
Proof.
  auto with Piull.
Qed.
#[global]
Hint Resolve Dual_Implication_Tensor : Piull.


(**
  The linar implication respect the idempotent property of the tensor.
  The proof follows from the definitions.
*)
Proposition Doble_Dual_Implication : 
forall A B : Proposition, 
(((A −∘ B)^⊥)^⊥) = (A −∘ B).
Proof.
  auto with Piull.
Qed.
#[global]
Hint Resolve Dual_Implication_Tensor : Piull.