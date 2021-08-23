(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From PROYI Require Import  Defs_Proposition.


(*
Observación presente en la definición 2.2 (primer parrafo).
*)
Proposition Doble_Duality_ULLT  : 
forall A : Proposition , 
(A^⊥)^⊥ = A. 
Proof.
  intros.
  induction A; auto. 
  - simpl. rewrite -> IHA1. rewrite -> IHA2. reflexivity.
  - simpl. rewrite -> IHA1. rewrite -> IHA2. reflexivity.
  - simpl. rewrite -> IHA. reflexivity. 
  - simpl. rewrite -> IHA. reflexivity. 
Qed.


(*
Prueba de las propiedades descritas en la definición 2.2.
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


Proposition Dual_Tensor_Implication :  
forall A B : Proposition, 
((A ⊗ B )^⊥) = (A −∘ (B^⊥)).
Proof.
  intros.
  simpl.
  unfold ULLT_IMP.
  reflexivity.
Qed.


Proposition Doble_Dual_Implication : 
forall A B : Proposition, 
(((A −∘ B)^⊥)^⊥) = (A −∘ B).
Proof.
  intros.
  unfold ULLT_IMP.
  rewrite -> (Doble_Duality_ULLT).
  reflexivity.
Qed.