(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021 set-reglas
  
  This file contains the tactis and Hint Db for the proofs.
*)

From Tmcod Require Import  Defs_Proposition.
From Tmcod Require Import  Defs_Process.
From Tmcod Require Import  Defs_Tactics.
From Tmcod Require Import  Defs_Context.


(**
*)
Inductive Disjoint_Sets : Context -> Context -> Prop := are_disjoint_lists :
forall (D F : Context),
  (forall (x : nat)(A B: Proposition), ~ ( ( (FName x:A) ∈ D )  /\ ( (FName x:B) ∈ F) ) ) -> (Disjoint_Sets D F).
#[global]
Hint Constructors Disjoint_Sets : Piull.



(**
*)
Inductive Good_Contexts : Context -> Context -> Context -> Process -> Prop := is_well_collected : 
forall (D F G : Context)(P : Process),
  ( forall (x : nat), ( (x ∈ FVars P) -> ( exists (A : Proposition), (FName x:A) ∈ (D ∪ F ∪ G) ) )) /\
  ( (Disjoint_Sets D F) /\ (Disjoint_Sets D G) /\ (Disjoint_Sets F G) /\ (Injective D) /\ (Injective F) /\ (Injective G))
   -> (Good_Contexts D F G P).
#[global]
Hint Constructors Good_Contexts : Piull.


(**
*)
Reserved Notation "D ';;;'  F '!-' P ':::' G" (at level 60).
Inductive Inference : Process -> Context -> Context -> Context -> Prop := 

  | idr : forall ( D : Context )( x y : nat )( A : Proposition ),
    Collect D -> x <> y ->
    Good_Contexts D (Bld x A) (Bld y A) ([FName x ←→ FName y]) ->
    ( D ;;; (Bld x A) !- ([FName x ←→ FName y]) ::: (Bld y A) )


  | idl : forall ( D : Context )( x y : nat )( A : Proposition ),
    Collect D -> x <> y ->
    Good_Contexts D ( (Bld x A) ∪ (Bld y (A^⊥)) ) ø ([FName x ←→ FName y]) ->
    ( D ;;; ( (Bld x A) ∪ (Bld y (A^⊥)) ) !-  ([FName x ←→ FName y]) ::: ø  )


  | repr : forall ( D : Context )( x y : nat )( A : Proposition )( P : Process ),
    Collect D -> lc P -> x <> y ->
    Good_Contexts D ø (Bld y A) P ->
    Good_Contexts D ø (Bld x (!A)) (FName x !· (Close y P)) ->
    Fresh x D -> 
    ( D ;;; ø !- P ::: (Bld y A) ) ->
    ( D ;;; ø !- (FName x !· (Close y P)) ::: (Bld x (!A)) )


  | repl : forall ( D F G : Context )( u x : nat )( A : Proposition )( P : Process ),
    IsClosing P u -> 
    Collect D -> Collect F -> Collect G -> lc P -> u <> x -> 
    ~( x ∈ (FVars P) ) -> ( u ∈ (FVars P) ) -> ( ( (FName u):A ) ∈ D ) -> 
    Good_Contexts D F G P ->
    Good_Contexts (SMA D u A) ( (Bld x (!A)) ∪ F ) G ({x \ u }P) ->
    Fresh x (D ∪ F ∪ G) ->
    ( D ;;; F !- P ::: G ) ->
    ( (SMA D u A) ;;; ( (Bld x (!A)) ∪ F ) !- ({x \ u }P) ::: G )


  | wnotr : forall ( D F G : Context )( u x : nat )( A : Proposition )( P : Process ),
    IsClosing P u -> 
    Collect D -> Collect G -> Collect F -> lc P -> u <> x -> 
    ~( x ∈ (FVars P) ) -> ( u ∈ (FVars P) ) -> ( ( (FName u):A ) ∈ D ) -> 
    Good_Contexts D F G P ->
    Good_Contexts (SMA D u A) F ( (Bld x (?(A ^⊥))) ∪ G ) ({x \ u }P) ->
    Fresh x (D ∪ F ∪ G) ->
    ( D ;;; F !- P ::: G ) -> 
    ( (SMA D u A) ;;; F !- ({x \ u }P) ::: ( (Bld x (?(A ^⊥))) ∪ G ) )


  | wnotl : forall ( D : Context )( x y : nat )( A : Proposition )( P : Process ),
    Collect D -> lc P -> x <> y -> 
    Good_Contexts D (Bld y A) ø P ->
    Good_Contexts D (Bld x (? A)) ø ( FName x !· (Close y P))  ->
    Fresh x D ->
    ( D ;;; (Bld y A) !- P ::: ø ) -> 
    ( D ;;; (Bld x (? A)) !- ( FName x !· (Close y P)) ::: ø )


(*   | limpr : forall ( D F G: Context )( x y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> x <> y -> 
    lc P -> 
    Good_Contexts D ( (Bld y A) ∪ F ) ( (Bld x B) ∪ G )  P ->
    Good_Contexts D F ( (Bld x (A−∘B)) ∪ G ) (FName x · (Close y P)) ->
    ( D ;;; ( (Bld y A) ∪ F ) !- P ::: ( (Bld x B) ∪ G ) ) -> 
    ( D ;;; F !- (FName x · (Close y P)) ::: ( (Bld x (A−∘B)) ∪ G ) )


  | limpl : forall ( D F G F' G': Context )( x y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> 
    lc P  -> lc Q -> 
    Good_Contexts D F ( (Bld y A) ∪ G )  P -> 
    Good_Contexts D ( (Bld x B) ∪ F' ) G' Q -> 
    Good_Contexts D ( (Bld x (A−∘B)) ∪ F ∪ F' ) ( G ∪ G') (ν Close y (FName x « FName y »· (P↓Q))) ->
    ( D ;;; F !- P ::: ( (Bld y A) ∪ G ) ) ->
    ( D ;;; ( (Bld x B) ∪ F' ) !- Q ::: G' ) ->
    ( D ;;; ( (Bld x (A−∘B)) ∪ F ∪ F' ) !- (ν Close y (FName x « FName y »· (P↓Q))) ::: ( G ∪ G') ) *)

  | rampr : forall ( D F G: Context )( x y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> 
    Good_Contexts D F ( (Bld x B) ∪ (Bld y A) ∪ G )  P -> 
    Good_Contexts D F ( (Bld x (A⅋B)) ∪ G )  (FName x · (Close y P)) -> 
    ( D ;;; F !- P ::: ( (Bld x B) ∪ (Bld y A) ∪ G ) ) -> 
    ( D ;;; F !- (FName x · (Close y P)) ::: ( (Bld x (A⅋B)) ∪ G ) )


  | rampl  : forall ( D F G F' G': Context )( x y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> 
    Collect G' -> lc P  -> lc Q -> 
    Good_Contexts D ( (Bld y A) ∪ F ) G  P -> 
    Good_Contexts D ( (Bld x B) ∪ F') G' Q -> 
    Good_Contexts D ( (Bld x (A⅋B)) ∪ F ∪ F' ) ( G ∪ G')  (ν Close y (FName x « FName y »· (P↓Q)) ) -> 
    ( D ;;; ( (Bld y A) ∪ F ) !- P ::: G ) ->
    ( D ;;; ( (Bld x B) ∪ F' ) !- Q ::: G') ->
    ( D ;;; ( (Bld x (A⅋B)) ∪ F ∪ F' ) !-  (ν Close y (FName x « FName y »· (P↓Q)) ) ::: ( G ∪ G') )



  | otiml : forall ( D F G: Context )( x y : nat )( y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> x <> y -> 
    Good_Contexts D ( (Bld x B) ∪ (Bld y A) ∪ F ) G  P -> 
    Good_Contexts D ( (Bld x (A⊗B)) ∪ F ) G  (FName x · Close y P) -> 
    ( D ;;; ( (Bld x B) ∪ (Bld y A) ∪ F ) !- P ::: G ) -> 
    ( D ;;; ( (Bld x (A⊗B)) ∪ F ) !- (FName x · Close y P) ::: G )


  | otimr  : forall ( D F G F' G': Context )( x y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> 
    Collect G' -> lc P  -> lc Q -> x <> y ->
    Good_Contexts D F ( (Bld y A) ∪ G ) P -> 
    Good_Contexts D F' ((Bld x B) ∪ G')  Q -> 
    Good_Contexts D (F ∪ F') ( (Bld x (A⊗B)) ∪ G ∪ G' )  (ν Close y ( FName x « FName y »· (P↓Q))) -> 
    ( D ;;; F !- P ::: ( (Bld y A) ∪ G ) ) ->
    ( D ;;; F' !- Q ::: ( (Bld x B) ∪ G' ) ) ->
    ( D ;;; (F ∪ F') !- ν Close y ( FName x « FName y »· (P↓Q)) ::: ( (Bld x (A⊗B)) ∪ G ∪ G' ) )


  | perpr : forall ( D F G: Context )( x : nat )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P ->
    Good_Contexts D F G P -> 
    Good_Contexts D F ( (Bld x ⊥) ∪ G ) (FName x ()· P) -> 
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; F !- (FName x ()· P) ::: ( (Bld x ⊥) ∪ G ) )


  | perpl : forall ( D : Context )( x : nat ),
    Collect D ->
    Good_Contexts D (Bld x ⊥) ø (FName x ·θ ) -> 
    ( D ;;; (Bld x ⊥) !- (FName x ·θ ) ::: ø )


  | onel : forall ( D F G : Context )( x : nat )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> 
    Good_Contexts D F G P ->
    Good_Contexts D ( (Bld x ¶) ∪ F ) G (FName x ()· P ) ->
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; ( (Bld x ¶) ∪ F ) !- (FName x ()· P ) ::: G )


  | oner : forall ( D : Context)( x : nat ),
    Collect D -> 
    Good_Contexts D ø (Bld x ¶)  (FName x ·θ ) -> 
    ( D ;;; ø !- (FName x ·θ ) ::: (Bld x ¶) )


  | copyl : forall ( D F G : Context )( x u : nat )( P : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> lc P -> x <> u ->
    Good_Contexts ( (Bld u A) ∪ D ) ( (Bld x A) ∪ F ) G P ->
    Good_Contexts ( (Bld u A) ∪ D ) F G (ν Close x ( FName u « FName x »· P )) ->
    ( ( (Bld u A) ∪ D ) ;;; ( (Bld x A) ∪ F ) !- P ::: G ) -> 
    ( ( (Bld u A) ∪ D ) ;;; F !- ν Close x ( FName u « FName x »· P ) ::: G )


  | copyr : forall ( D F G : Context )( x u : nat )( P : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> lc P -> x <> u ->
    Good_Contexts ( (Bld u A) ∪ D ) F ( (Bld x (A^⊥)) ∪ G ) P ->
    Good_Contexts ( (Bld u A) ∪ D ) F G (ν Close x ( FName u « FName x »· P )) ->
    ( ( (Bld u A) ∪ D ) ;;; F !- P ::: ( (Bld x (A^⊥)) ∪ G ) ) -> 
    ( ( (Bld u A) ∪ D ) ;;; F !- ν Close x ( FName u « FName x »· P ) ::: G )


  | cutrep : forall ( D F G : Context )( P Q : Process )( A : Proposition )( x u : nat ),
    Collect D -> Collect F -> Collect G ->
    lc P -> lc Q -> x <> u ->
    Good_Contexts D ø (Bld x A) P ->
    Good_Contexts ( (Bld u A) ∪ D ) F G Q ->
    ( D ;;; ø !- P ::: (Bld x A) ) -> 
    ( ( (Bld u A) ∪ D ) ;;; F !- Q ::: G )  -> 
    ( D ;;; F !- ν Close u ((FName u !· Close x P) ↓ Q) ::: G )


  | cutwnot : forall ( D F G : Context )( P Q : Process )( A : Proposition )( x u : nat ),
    Collect D -> Collect F -> Collect G -> 
    lc P -> lc Q ->  x <> u ->
    Good_Contexts D (Bld x (A^⊥)) ø P ->
    Good_Contexts ((Bld u A) ∪ D) F G Q ->
    Good_Contexts D F G (ν Close u ( ((FName u) !· Close x P) ↓ Q)) ->
    ( D ;;; (Bld x (A^⊥)) !- P ::: ø ) -> 
    ( ((Bld u A) ∪ D) ;;; F !- Q ::: G ) -> 
    ( D ;;; F !- (ν Close u ( ((FName u) !· Close x P) ↓ Q)) ::: G )


  | cutr : forall ( D F G F' G' : Context )( P Q : Process )( A : Proposition )( x : nat ),
    Collect D -> Collect F -> Collect G -> 
    Collect F' -> Collect G' -> 
    Good_Contexts D F ( (Bld x A) ∪ G ) P ->
    Good_Contexts D ( (Bld x A) ∪ F' ) G' Q ->
    lc P -> lc Q ->
    ( D ;;; F !- P ::: ( (Bld x A) ∪ G ) ) ->
    ( D ;;; ( (Bld x A) ∪ F' ) !- Q ::: G' ) ->
    ( D ;;; ( F ∪ F' ) !- ( ν Close x (P↓Q) ) ::: ( G ∪ G' ) )


  | cutl : forall ( D F G F' G' : Context )( P Q : Process )( A : Proposition )( x : nat ),
    Collect D -> Collect F -> Collect G -> 
    Collect F' -> Collect G' -> 
    Good_Contexts D ((Bld x A) ∪ F) G P ->
    Good_Contexts D ((Bld x (A^⊥)) ∪ F') G' Q ->
    lc P -> lc Q ->
    ( D ;;; ((Bld x A) ∪ F) !- P ::: G ) ->
    ( D ;;; ((Bld x (A^⊥)) ∪ F') !- Q ::: G' ) ->
    ( D ;;; (F ∪ F') !- ( ν Close x (P↓Q) ) ::: (G ∪ G') )


where "D ';;;'  F '!-' P ':::' G" := (Inference P D F G).
#[global]
Hint Constructors Inference : Piull.


