(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the tactis and Hint Db for the proofs.
*)
From Coq Require Import Lists.List.
Import ListNotations.

From Tmcod Require Import  Defs_Proposition.
From Tmcod Require Import  Defs_Process.


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
*)
Inductive Collect : list Assignment -> Prop := is_collect :forall L : list Assignment,
  (forall H : Assignment, (In H L) -> Assig H ) -> Collect L.
#[global]
Hint Constructors Collect : Piull.


(**
*)
Inductive Well_Collected : list Assignment -> Process -> Prop := is_well_collected : 
forall (L : list Assignment)(P : Process),
  (forall (x : nat)(A : Proposition), ( (In ((FName x):A) L) <-> (x ∈ FVars P))) -> (Well_Collected L P).
#[global]
Hint Constructors Well_Collected : Piull.


(**
*)
Inductive Disjoint_Lists : list Assignment -> list Assignment -> Prop := are_disjoint_lists :
forall (D F : list Assignment),
  (forall (x : nat)(A : Proposition), ~ ( (In ((FName x):A) D)  /\ (In ((FName x):A) F) ) ) -> (Disjoint_Lists D F).
#[global]
Hint Constructors Disjoint_Lists : Piull.


(**
*)
Inductive Disjoint_Contexts : list Assignment -> list Assignment -> list Assignment -> Prop := are_disjoint_contexts :
forall (D F G : list Assignment),
  (forall (x : nat)(A : Proposition), ( (Disjoint_Lists D F) /\ (Disjoint_Lists D G) /\ (Disjoint_Lists  F G) )) -> (Disjoint_Contexts D F G).
#[global]
Hint Constructors Disjoint_Contexts : Piull.


(**
*)
Reserved Notation "D ';;;'  F '!-' P ':::' G" (at level 60).
Inductive Inference : Process -> list Assignment -> list Assignment -> list Assignment -> Prop := 
  | idr : forall (D : list Assignment) (x y : Name) ( A : Proposition),
    Collect D -> lc_name x -> lc_name y ->
    Well_Collected D ([x←→y]) -> Well_Collected (cons (x:A) nil) ([x←→y]) ->
    Well_Collected (cons (y:A) nil) ([x←→y]) -> 
    Disjoint_Contexts D (cons (x:A) nil) (cons (y:A) nil) ->
    ( D ;;; (cons (x:A) nil) !- ([x←→y]) ::: (cons (y:A) nil)  )


  | idl : forall (D : list Assignment)(x y : Name)(A : Proposition),
    Collect D -> lc_name x -> lc_name y ->
    Well_Collected D ([x←→y]) -> Well_Collected ((cons (x:A) nil) ++ (cons (y:(A^⊥)) nil)) ([x←→y]) ->
    Disjoint_Contexts D ((cons (x:A) nil) ++ (cons (y:(A^⊥)) nil)) nil ->
    ( D ;;; ((cons (x:A) nil) ++ (cons (y:(A^⊥)) nil)) !-  ([x←→y]) ::: nil  )


  | repr : forall ( D : list Assignment ) ( x : Name)( y : nat )( A : Proposition )( P : Process ), 
    Collect D -> lc_name x -> lc P ->
    Well_Collected D P -> Well_Collected (cons ((FName y):A) nil) P ->
    Well_Collected D (x !· (Close y P)) -> Well_Collected (cons (x:!A) nil) (x !· (Close y P)) ->
    Disjoint_Contexts D nil (cons ((FName y):A) nil) ->
    Disjoint_Contexts D nil (cons (x:!A) nil) ->
    ( D ;;; nil !- P ::: [ ((FName y):A) ] ) ->
    ( D ;;; nil !- (x !· (Close y P)) ::: [(x:!A)] )


  | repl : forall ( D F G : list Assignment ) ( u x : nat)( A : Proposition)(P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> u <> x -> ~( x ∈ (FVars P) ) ->
    Well_Collected ((cons ((FName u):A) nil) ++ D) P ->
    Well_Collected F P -> Well_Collected G P ->
    Well_Collected ((cons ((FName x):!A) nil) ++ F) ({x \ u }P) ->
    Well_Collected D ({x \ u }P) -> Well_Collected G ({x \ u }P) ->
    Disjoint_Contexts ((cons ((FName u):A) nil) ++ D) F G ->
    Disjoint_Contexts D ((cons ((FName x):!A) nil) ++ F) G ->
    ( ((cons ((FName u):A) nil) ++ D) ;;; F !- P ::: G ) ->
    ( D ;;; ((cons ((FName x):!A) nil) ++ F) !- ({x \ u }P) ::: G)


  | wnotr : forall ( D F G : list Assignment ) ( u x : nat)( A : Proposition)(P : Process ),
    Collect D -> Collect G -> Collect F -> lc P -> u <> x -> ~( x ∈ (FVars P) ) -> 
    ( ((cons ((FName u):A) nil) ++ D) ;;; F !- P ::: G ) -> 
    ( D ;;; F !- ({x \ u }P) ::: ( ( cons ((FName x): (? (A ^⊥) )) nil ) ++ G) )


  | wnotl : forall ( D : list Assignment )( x : Name)( y : nat )( A : Proposition)(P : Process ),
    Collect D -> lc_name x -> lc P -> 
    ( D ;;; (cons ((FName y):A) nil) !- P ::: nil ) -> 
    ( D ;;; (cons (x:? A) nil) !- ( x !· (Close y P)) ::: nil)


  | limpr : forall ( D F G: list Assignment )( x : Name )( y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc_name x -> lc P -> 
    ( D ;;; ( (cons ((FName y):A) nil) ++ F) !- P ::: ( (cons (x:B) nil) ++ G ) ) -> 
    ( D ;;; F !- (x · (Close y P)) ::: ((cons (x:(A−∘B) ) nil) ++ G ) )


  | limpl : forall ( D F G F' G': list Assignment )( x : Name )( y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> lc_name x -> lc P  -> lc Q -> 
    ( D ;;; F !- P ::: ( (cons ((FName y):A) nil) ++ G ) ) ->
    ( D ;;; ((cons (x:B) nil) ++ F') !- Q ::: G' ) ->
    ( D ;;; ((cons (x:(A−∘B) ) nil) ++ (F ++ F')) !- (ν (Close y (x « (FName y) »· (P↓Q)))) ::: ( G ++ G') )


  | rampr : forall ( D F G: list Assignment )( x : Name)( y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc_name x -> lc P -> 
    ( D ;;; F !- P ::: ( (cons (x:B) (cons ((FName y):A) nil) ) ++ G ) ) -> 
    ( D ;;; F !- (x · (Close y P)) ::: ((cons (x:(A⅋B) ) nil) ++ G ) )


  | rampl  : forall ( D F G F' G': list Assignment )( x : Name )( y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> lc_name x -> lc P  -> lc Q -> 
    ( D ;;; ( (cons ((FName y):A) nil) ++ F ) !- P ::: G ) ->
    ( D ;;; ((cons (x:B) nil) ++ F') !- Q ::: G' ) ->
    ( D ;;; ((cons (x:(A⅋B) ) nil) ++ (F ++ F')) !- (ν ( Close y (x « (FName y) »· (P↓Q)) )) ::: ( G ++ G') )


  | otiml : forall ( D F G: list Assignment )( y x : Name )( y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc_name x -> lc P -> 
    ( D ;;; ( (cons (x:B) (cons ((FName y):A) nil) ) ++ F) !- P ::: G ) -> 
    ( D ;;; ( (cons (x:(A⊗B) ) nil) ++ F) !- (x · (Close y P)) ::: G )


  | otimr  : forall ( D F G F' G': list Assignment )( x : Name )( y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> lc_name x -> lc P  -> lc Q -> 
    ( D ;;; F !- P ::: ( (cons ((FName y):A) nil) ++ G) ) ->
    ( D ;;; F' !- Q ::: ( (cons (x:B) nil) ++ G') ) ->
    ( D ;;; (F ++ F') !- (ν (Close y (x « (FName y) »· (P↓Q)) )) ::: ( (cons (x:(A⊗B)) nil) ++ G ++ G') )


  | perpr : forall ( D F G: list Assignment )( x : Name) (P : Process ),
    Collect D -> Collect F -> Collect G -> lc_name x -> lc P -> 
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; F !- (x ()· P) ::: ( (cons (x:⊥) nil) ++ G) )


  | perpl : forall ( D : list Assignment)( x : Name),
    Collect D -> lc_name x -> 
    ( D ;;; (cons (x:⊥) nil ) !- (x ·θ ) ::: nil )


  | onel : forall ( D F G : list Assignment)( x : Name)( P : Process),
    Collect D -> Collect F -> Collect G ->  lc_name x -> lc P -> 
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; (cons (x:¶) nil ++ F) !- (x ()· P ) ::: G )


  | oner : forall ( D : list Assignment)( x : Name),
    Collect D -> lc_name x -> 
    ( D ;;; nil !- (x ·θ ) ::: (cons (x:¶) nil ) )


  | copyl : forall ( D F G : list Assignment )( x u : nat )( P : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> lc P ->
    ( ( cons ((FName u):A) nil ++ D ) ;;; ( cons ((FName x):A) nil ++ F ) !- P ::: G ) -> 
    ( ( cons ((FName u):A) nil ++ D ) ;;; F !- (ν (Close x ( (FName u) « (FName x) »· P ))) ::: G )


  | copyr : forall ( D F G : list Assignment )( x u : nat )( P : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> lc P ->
    ( ( cons ((FName u):A) nil ++ D ) ;;; F !- P ::: ( cons ((FName x):(A^⊥)) nil ++ G) ) -> 
    ( ( cons ((FName u):A) nil ++ D ) ;;; F !- (ν (Close x ( (FName u) « (FName x) »· P ))) ::: G )


  | cutrep : forall ( D F G : list Assignment )( P Q : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> 
    lc P -> lc Q ->
    (forall ( x : nat ), ( D ;;; nil !- P ::: ( cons ((FName x):A) nil ) ) )-> 
    (forall ( u : nat ), ( (cons ((FName u):A) nil ++ D) ;;; F !- Q ::: G ) )-> 
    forall ( x u : nat ), ( D ;;; F !- (ν Close u ( ((FName u) !· Close x P) ↓ Q)) ::: G )


  | cutwnot : forall ( D F G : list Assignment )( x u : nat )( P Q : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> lc P -> lc Q ->
    ( D ;;; ( cons ((FName x):(A^⊥)) nil ) !- P ::: nil ) -> 
    ( ((cons ((FName u):A) nil) ++ D) ;;; F !- Q ::: G ) -> 
    ( D ;;; F !- (ν Close u ( ((FName u) !· Close x P) ↓ Q)) ::: G )  


  | cutr : forall ( D F G F' G' : list Assignment )( P Q : Process )( A : Proposition )( x : nat ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> 
    lc P -> lc Q ->
    ( D ;;; F !- P ::: ( cons ((FName x):A) nil ++ G ) ) ->
    ( D ;;; (cons ((FName x):A) nil ++ F') !- Q ::: G' ) ->
    ( D ;;; (F ++ F') !- ( ν Close x (P↓Q) ) ::: (G ++ G') )


  | cutl : forall ( D F G F' G' : list Assignment )( P Q : Process )( A : Proposition )( x : nat ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> 
    lc P -> lc Q ->
    ( D ;;; ( cons ((FName x):A) nil ++ F) !- P ::: G ) ->
    ( D ;;; (cons ((FName x):(A^⊥)) nil ++ F') !- Q ::: G' ) ->
    ( D ;;; (F ++ F') !- ( ν Close x (P↓Q) ) ::: (G ++ G') )


where "D ';;;'  F '!-' P ':::' G" := (Inference P D F G).
#[global]
Hint Constructors Inference : Piull.




