(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
*)
From Tmcod Require Import Defs_Tactics.


(**
Definition 2.1 - ULL propositions
*)
Inductive Proposition : Type := 
  | ONE : Proposition
  | ABS : Proposition
  | TEN (A : Proposition) (B : Proposition) : Proposition
  | PAR (A : Proposition) (B : Proposition) : Proposition
(*   | ULLT_IMP (A : Proposition) (B : Proposition) : Proposition *)
  | EXP (A : Proposition) : Proposition
  | MOD (A : Proposition) : Proposition.
#[global]
Hint Constructors Proposition : Piull.


(**
Similar notation to the given in the article. 
The associativity and levels follows the ideas from Honda.
*)
Notation "¶" := ONE.
Notation "⊥" := ABS.
Notation "A ⊗ B" := (TEN A B)(at level 70, right associativity).
Notation "A ⅋ B" := (PAR A B)(at level 70, right associativity).
(* Notation "A −∘ B" := (ULLT_IMP A B)(at level 50, left associativity). *)
Notation "! A" := (EXP A)(at level 60, right associativity).
Notation "? A" := (MOD A)(at level 60, right associativity).


(**
Definition 2.2 - Duals
*)
Fixpoint Dual_Prop ( T : Proposition ) : Proposition := 
match T with 
  | ¶ => ⊥
  | ⊥ => ¶
  | A ⊗ B => (Dual_Prop A) ⅋ (Dual_Prop B)
  | A ⅋ B => (Dual_Prop A) ⊗ (Dual_Prop B)
(*   | A −∘ B => A ⊗ (Dual_Prop B) *)
  | ! A => ? (Dual_Prop A)
  | ? A => ! (Dual_Prop A)
end.
#[global]
Hint Resolve Dual_Prop : Piull.


Notation "A '^⊥'" := (Dual_Prop A)(at level 60, right associativity).


(**
Alternative definition for the operator (−∘), it is given in the first paragraph in the definition 2.2.
*)
Definition ULLT_IMP (A : Proposition) (B : Proposition) : Proposition := (A^⊥) ⅋ B.
#[global]
Hint Resolve ULLT_IMP : Piull.


Notation "A −∘ B" := (ULLT_IMP A B)(at level 70, right associativity).


(*
⊥
⊗
⅋
−∘
^⊥
*)