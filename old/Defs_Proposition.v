(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López 
  Proyecto 1. Session Type Systems Verification
*)


(*
Definición 2.1, ULL Propositions
*)
Inductive Proposition : Type := 
  | ONE : Proposition
  | ABS : Proposition
  | TEN (A : Proposition) (B : Proposition) : Proposition
  | PAR (A : Proposition) (B : Proposition) : Proposition
(*   | ULLT_IMP (A : ULLType) (B : ULLType) : ULLType  *)
  | EXP (A : Proposition) : Proposition
  | MOD (A : Proposition) : Proposition.
Hint Constructors Proposition : core.


(*
Notación análoga a la propuesta por el artículo.
Los niveles de asociatividad se dan siguiendo las ideas de Honda.
*)
Notation "¶" := ONE.
Notation "⊥" := ABS.
Notation "A ⊗ B" := (TEN A B)(at level 70, right associativity).
Notation "A ⅋ B" := (PAR A B)(at level 70, right associativity).
(* Notation "A −∘ B" := (ULLT_IMP A B)(at level 50, left associativity). *)
Notation "! A" := (EXP A)(at level 60, right associativity).
Notation "? A" := (MOD A)(at level 60, right associativity).


(*
Definicion 2.2, Dualidad
*)
Fixpoint Dual_Prop ( T : Proposition ) : Proposition := 
match T with 
  | ¶ => ⊥
  | ⊥ => ¶
  | A ⊗ B => (Dual_Prop A) ⅋ (Dual_Prop B)
  | A ⅋ B => (Dual_Prop A) ⊗ (Dual_Prop B)
  | ! A => ? (Dual_Prop A)
  | ? A => ! (Dual_Prop A)
end.
Hint Unfold Dual_Prop : core.
Notation "A '^⊥'" := (Dual_Prop A)(at level 60, right associativity).


(*
Definición del operador −∘ de acuerdo a los descrito en el primer parrafo de la Definición 2.2.
*)
Definition ULLT_IMP (A : Proposition) (B : Proposition) : Proposition := (A^⊥) ⅋ B.
Notation "A −∘ B" := (ULLT_IMP A B)(at level 70, right associativity).

(*
⊥
⊗
⅋
−∘
^⊥
*)


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
