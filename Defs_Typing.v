(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021 set-reglas
  
  This file contains the tactis and Hint Db for the proofs.
*)
From Coq Require Import Lists.List.
Import ListNotations.

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
Definition Context := list Assignment.


(**
*)
Inductive Collect : Context -> Prop := is_collect :
  forall L : Context,
  (forall H : Assignment, (In H L) -> Assig H ) -> Collect L.
#[global]
Hint Constructors Collect : Piull.


(**
*)
Inductive Well_Collected : Context -> Process -> Prop := is_well_collected : 
forall (L : Context)(P : Process),
  (forall (x : nat)(A : Proposition), ( (x ∈ FVars P) -> ( In (FName x:A) L ) )) -> (Well_Collected L P).
#[global]
Hint Constructors Well_Collected : Piull.


(**
*)
Inductive Disjoint_Sets : Context -> Context -> Prop := are_disjoint_lists :
forall (D F : Context),
  (forall (x : nat)(A B: Proposition), ~ ( ( In (FName x:A) D )  /\ ( In (FName x:B) F) ) ) -> (Disjoint_Sets D F).
#[global]
Hint Constructors Disjoint_Sets : Piull.


(**
*)
Inductive Disjoint_Contexts : Context -> Context -> Context -> Prop := are_disjoint_contexts :
forall (D F G : Context),
  ( (Disjoint_Sets D F) /\ (Disjoint_Sets D G) /\ (Disjoint_Sets  F G) ) -> (Disjoint_Contexts D F G).
#[global]
Hint Constructors Disjoint_Contexts : Piull.


Definition Bld ( x : nat )( A : Proposition ) : Context := cons (FName x:A) nil.
#[global] 
Hint Resolve Bld : Piull.

Definition BldA ( X : Assignment ) : Context := cons X nil.
#[global]
Hint Resolve Bld : Piull.


(**
*)
Reserved Notation "D ';;;'  F '!-' P ':::' G" (at level 60).
Inductive Inference : Process -> Context -> Context -> Context -> Prop := 
  | idr : forall ( D : Context )( x y : nat )( A : Proposition ),
    Collect D -> x <> y ->
    Well_Collected ( (Bld x A) ++ (Bld y A) ++ D ) ([FName x ←→ FName y]) ->
    Disjoint_Contexts D (Bld x A) (Bld y A) ->
    ( D ;;; (Bld x A) !- ([FName x ←→ FName y]) ::: (Bld y A) )


  | idl : forall ( D : Context )( x y : nat )( A : Proposition ),
    Collect D -> x <> y ->
    Well_Collected ( (Bld x A) ++ (Bld y (A^⊥)) ++ D) ([FName x ←→ FName y]) ->
    Disjoint_Contexts D ( (Bld x A) ++ (Bld y (A^⊥)) ) nil ->
    ( D ;;; ( (Bld x A) ++ (Bld y (A^⊥)) ) !-  ([FName x ←→ FName y]) ::: nil  )


  | repr : forall ( D : Context )( x y : nat )( A : Proposition )( P : Process ),
    Collect D -> lc P -> x <> y ->
    Well_Collected ( (Bld y A) ++ D ) P ->
    Well_Collected ( (Bld x (!A)) ++ D ) (FName x !· (Close y P)) ->
    Disjoint_Contexts D nil (Bld y A) ->
    Disjoint_Contexts D nil (Bld x (!A)) ->
    ( D ;;; nil !- P ::: (Bld y A) ) ->
    ( D ;;; nil !- (FName x !· (Close y P)) ::: (Bld x (!A)) )


  | repl : forall ( D F G : Context )( u x : nat )( A : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> u <> x -> 
    ~( x ∈ (FVars P) ) -> ( u ∈ (FVars P) ) ->
    Well_Collected ( (Bld u A) ++ D ++ F ++ G ) P ->
    Well_Collected ( (Bld x (!A)) ++ D ++ F ++ G ) ({x \ u }P) ->
    Disjoint_Contexts ( (Bld u A) ++ D ) F G ->
    Disjoint_Contexts D ( (Bld x (!A)) ++ F ) G ->
    ( ( (Bld u A) ++ D ) ;;; F !- P ::: G ) ->
    ( D ;;; ( (Bld x (!A)) ++ F ) !- ({x \ u }P) ::: G )


  | wnotr : forall ( D F G : Context )( u x : nat )( A : Proposition )( P : Process ),
    Collect D -> Collect G -> Collect F -> lc P -> u <> x -> 
    ~( x ∈ (FVars P) ) -> ( u ∈ (FVars P) ) ->
    Well_Collected ( (Bld u A) ++ D ++ F ++ G ) P ->
    Well_Collected ( D ++ F ++ (Bld x (?(A ^⊥))) ++ G ) ({x \ u }P) ->
    Disjoint_Contexts ( (Bld u A) ++ D ) F G ->
    Disjoint_Contexts D F ( (Bld x (?(A ^⊥))) ++ G ) ->
    ( ( (Bld u A) ++ D ) ;;; F !- P ::: G ) -> 
    ( D ;;; F !- ({x \ u }P) ::: ( (Bld x (?(A ^⊥))) ++ G ) )


  | wnotl : forall ( D : Context )( x y : nat )( A : Proposition )( P : Process ),
    Collect D -> lc P -> x <> y -> 
    Well_Collected ( D ++ (Bld y A) ) P ->
    Well_Collected ( D ++ (Bld x (? A)) ) ( FName x !· (Close y P))  ->
    Disjoint_Contexts D (Bld y A) nil ->
    Disjoint_Contexts D (Bld x (? A)) nil ->
    ( D ;;; (Bld y A) !- P ::: nil ) -> 
    ( D ;;; (Bld x (? A)) !- ( FName x !· (Close y P)) ::: nil )


  | limpr : forall ( D F G: Context )( x y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> x <> y -> 
    lc P -> 
    ( D ;;; ( (Bld y A) ++ F ) !- P ::: ( (Bld x B) ++ G ) ) -> 
    ( D ;;; F !- (FName x · (Close y P)) ::: ( (Bld x (A−∘B)) ++ G ) )


  | limpl : forall ( D F G F' G': Context )( x y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> 
    lc P  -> lc Q -> 
    ( D ;;; F !- P ::: ( (Bld y A) ++ G ) ) ->
    ( D ;;; ( (Bld x B) ++ F' ) !- Q ::: G' ) ->
    ( D ;;; ( (Bld x (A−∘B)) ++ F ++ F' ) !- (ν Close y (FName x « FName y »· (P↓Q))) ::: ( G ++ G') )


  | rampr : forall ( D F G: Context )( x y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> 
    ( D ;;; F !- P ::: ( (Bld x B) ++ (Bld y A) ++ G ) ) -> 
    ( D ;;; F !- (FName x · (Close y P)) ::: ( (Bld x (A⅋B)) ++ G ) )


  | rampl  : forall ( D F G F' G': Context )( x y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> lc P  -> lc Q -> 
    ( D ;;; ( (Bld y A) ++ F ) !- P ::: G ) ->
    ( D ;;; ( (Bld x B) ++ F' ) !- Q ::: G') ->
    ( D ;;; ( (Bld x (A⅋B)) ++ F ++ F' ) !- (ν Close y (FName x « FName y »· (P↓Q)) ) ::: ( G ++ G') )



  | otiml : forall ( D F G: Context )( x y : nat )( y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> x <> y -> 
    ( D ;;; ( (Bld x B) ++ (Bld y A) ++ F ) !- P ::: G ) -> 
    ( D ;;; ( (Bld x (A⊗B)) ++ F ) !- (FName x · Close y P) ::: G )


  | otimr  : forall ( D F G F' G': Context )( x y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> lc P  -> lc Q -> x <> y ->
    ( D ;;; F !- P ::: ( (Bld y A) ++ G ) ) ->
    ( D ;;; F' !- Q ::: ( (Bld x B) ++ G' ) ) ->
    ( D ;;; (F ++ F') !- ν Close y ( FName x « FName y »· (P↓Q)) ::: ( (Bld x (A⊗B)) ++ G ++ G' ) )


  | perpr : forall ( D F G: Context )( x : nat )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P ->
    Well_Collected ( D ++ F ++ G ) P ->
    Well_Collected ( D ++ F ++ (Bld x ⊥) ++ G ) (FName x ()· P) ->
    Disjoint_Contexts D F G ->
    Disjoint_Contexts D F ( (Bld x ⊥) ++ G ) ->
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; F !- (FName x ()· P) ::: ( (Bld x ⊥) ++ G ) )


  | perpl : forall ( D : Context )( x : nat ),
    Collect D ->
    Well_Collected ( D ++ (Bld x ⊥) ) (FName x ·θ ) ->
    Disjoint_Contexts D (Bld x ⊥) nil ->
    ( D ;;; (Bld x ⊥) !- (FName x ·θ ) ::: nil )


  | onel : forall ( D F G : Context )( x : nat )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> 
    Well_Collected ( D ++ F ++ G ) P ->
    Well_Collected ( D ++ (Bld x ¶) ++ F ++ G ) (FName x ()· P) ->
    Disjoint_Contexts D F G ->
    Disjoint_Contexts D ( (Bld x ¶) ++ F ) G ->
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; ( (Bld x ¶) ++ F ) !- (FName x ()· P ) ::: G )


  | oner : forall ( D : Context)( x : nat ),
    Collect D -> 
    Well_Collected ( D ++ (Bld x ¶) ) (FName x ·θ ) ->
    Disjoint_Contexts D nil (Bld x ¶) ->
    ( D ;;; nil !- (FName x ·θ ) ::: (Bld x ¶) )


  | copyl : forall ( D F G : Context )( x u : nat )( P : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> lc P -> x <> u ->
    ( ( (Bld u A) ++ D ) ;;; ( (Bld x A) ++ F ) !- P ::: G ) -> 
    ( ( (Bld u A) ++ D ) ;;; F !- ν Close x ( FName u « FName x »· P ) ::: G )


  | copyr : forall ( D F G : Context )( x u : nat )( P : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> lc P -> x <> u ->
    ( ( (Bld u A) ++ D ) ;;; F !- P ::: ( (Bld x (A^⊥)) ++ G ) ) -> 
    ( ( (Bld u A) ++ D ) ;;; F !- ν Close x ( FName u « FName x »· P ) ::: G )


  | cutrep : forall ( D F G : Context )( P Q : Process )( A : Proposition )( x u : nat ),
    Collect D -> Collect F -> Collect G ->
    lc P -> lc Q -> x <> u ->
    ( D ;;; nil !- P ::: (Bld x A) ) -> 
    ( ( (Bld u A) ++ D ) ;;; F !- Q ::: G )  -> 
    ( D ;;; F !- ν Close u ((FName u !· Close x P) ↓ Q) ::: G )


  | cutr : forall ( D F G F' G' : Context )( P Q : Process )( A : Proposition )( x : nat ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> 
    lc P -> lc Q ->
    ( D ;;; F !- P ::: ( (Bld x A) ++ G ) ) ->
    ( D ;;; ( (Bld x A) ++ F' ) !- Q ::: G' ) ->
    ( D ;;; ( F ++ F' ) !- ( ν Close x (P↓Q) ) ::: ( G ++ G' ) )



(*
  | cutwnot : forall ( D F G : Context )( x u : nat )( P Q : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> 
    lc P -> lc Q ->  x <> u ->
    ( D ;;; ( cons ((FName x):(A^⊥)) nil ) !- P ::: nil ) -> 
    ( ((cons ((FName u):A) nil) ++ D) ;;; F !- Q ::: G ) -> 
    ( D ;;; F !- (ν Close u ( ((FName u) !· Close x P) ↓ Q)) ::: G )  



  | cutl : forall ( D F G F' G' : Context )( P Q : Process )( A : Proposition )( x : nat ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> 
    lc P -> lc Q ->
    ( D ;;; (cons ((FName x):A) nil ++ F) !- P ::: G ) ->
    ( D ;;; (cons ((FName x):(A^⊥)) nil ++ F') !- Q ::: G' ) ->
    ( D ;;; (F ++ F') !- ( ν Close x (P↓Q) ) ::: (G ++ G') )

*)
where "D ';;;'  F '!-' P ':::' G" := (Inference P D F G).
#[global]
Hint Constructors Inference : Piull.


(**
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
Hint Resolve Remove : Piull.

