(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Lists.List.
Import ListNotations.

From Tmcod Require Import  Defs_Proposition.
From Tmcod Require Import  Defs_Process.


(*
Las siguientes definiciones son necesarias para poder hablar de inferencia, se encuentran sueltas a lo largo del parrafo 'Typing inference'. 

Definición de Asignación.
*)
Inductive Assignment : Type := assig ( x : Name )( A : Proposition ) : Assignment.
Notation " x : A " := (assig x A )(at level 60).


(*
Nuevamente, por la LNR no todo es necesario distinguir aquellas asignaciones que si tienen sentido.
*)
Inductive Assig : Assignment -> Prop :=
  is_assig :  forall (x : Name)(A:Proposition), lc_name x -> Assig ( x : A).


(*
Definición de una colección de asignaciones.
*)
Inductive Collect : list Assignment -> Prop := is_collect :forall L : list Assignment,
  (forall H : Assignment, (In H L) -> Assig H ) -> Collect L.


(*
Figura 1, reglas de inferencia.
*)
Reserved Notation "D ';;;'  F '!-' P ':::' G" (at level 60).
Inductive Inference : Process -> list Assignment -> list Assignment -> list Assignment -> Prop := 
  | idr : forall (D : list Assignment) (x y : Name) ( A : Proposition),
    Collect D -> lc_name x -> lc_name y -> 
    ( D ;;; ( cons (x:A) nil ) !- ([x←→y]) ::: [ (y:A) ]  )


  | idl : forall (D : list Assignment)(x y : Name)(A : Proposition),
    Collect D -> lc_name x -> lc_name y -> 
    ( D ;;; ( (cons (x:A) nil) ++ (cons (y:(A^⊥)) nil) )  !-  ([x←→y]) ::: []  )


  | repr : forall ( D : list Assignment ) ( x : Name)( y : nat )( A : Proposition )( P : Process ), 
    Collect D -> lc_name x -> lc P ->
    ( D ;;; nil !- P ::: [ ((FName y):A) ] ) -> 
    ( D ;;; nil !- (x !· (Close y P) ) ::: [ (x:!A)  ] )


  | repl : forall ( D F G : list Assignment ) ( u x : nat)( A : Proposition)(P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> Well_Subst P u x -> 
    ( D ;;; ( (cons ((FName u):A) nil) ++ F) !- P ::: G ) -> 
    ( D ;;; ( (cons ((FName x):!A) nil) ++ F) !- ({x \ u }P) ::: G)


  | conr : forall ( D F G : list Assignment ) ( u x : nat)( A : Proposition)(P : Process ),
    Collect D -> Collect G -> Collect F -> lc P -> Well_Subst P u x ->
    ( D ;;; ( (cons ((FName u):A) nil) ++ F) !- P ::: G ) -> 
    ( D ;;; F !- ({x \ u }P) ::: ( ( cons ((FName x): (? (A ^⊥) )) nil ) ++ G) )


  | conl : forall ( D : list Assignment )( x : Name)( y : nat )( A : Proposition)(P : Process ),
    Collect D -> lc_name x -> lc P -> 
    ( D ;;; (cons ((FName y):A) nil) !- P ::: nil ) -> 
    ( D ;;; (cons (x:? A) nil) !- ( x !· (Close y P)) ::: nil)

(*
  | recr : forall ( D F G: list Assignment )( x : Name )( y : nat )( A B : Proposition )( P : Prepro ),
    Collect D -> Collect F -> Collect G -> Process_Name x -> Process P -> 
    ( D ;;; ( (cons ((FName y):A) nil) ++ F) !- P ::: ( (cons (x:B) nil) ++ G ) ) -> 
    ( D ;;; F !- (x · (Close y P)) ::: ((cons (x:(A−∘B) ) nil) ++ G ) )


  | recl : forall ( D F G F' G': list Assignment )( x : Name )( y : nat )( A B : Proposition )( P Q: Prepro ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> Process_Name x -> Process P  -> Process Q -> 
    ( D ;;; F !- P ::: ( (cons ((FName y):A) nil) ++ G ) ) ->
    ( D ;;; ((cons (x:B) nil) ++ F') !- Q ::: G' ) ->
    ( D ;;; ((cons (x:(A−∘B) ) nil) ++ (F ++ F')) !- (ν (Close y (x « (FName y) »· (P↓Q)))) ::: ( G ++ G') )


  | reccr : forall ( D F G: list Assignment )( x : Name)( y : nat )( A B : Proposition )( P : Prepro ),
    Collect D -> Collect F -> Collect G -> Process_Name x -> Process P -> 
    ( D ;;; F !- P ::: ( (cons (x:B) (cons ((FName y):A) nil) ) ++ G ) ) -> 
    ( D ;;; F !- (x · (Close y P)) ::: ((cons (x:(A⅋B) ) nil) ++ G ) )


  | reccl  : forall ( D F G F' G': list Assignment )( x : Name )( y : nat )( A B : Proposition )( P Q: Prepro ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> Process_Name x -> Process P  -> Process Q -> 
    ( D ;;; ( (cons ((FName y):A) nil) ++ F ) !- P ::: G ) ->
    ( D ;;; ((cons (x:B) nil) ++ F') !- Q ::: G' ) ->
    ( D ;;; ((cons (x:(A⅋B) ) nil) ++ (F ++ F')) !- (ν (Close y (x « (FName y) »· (P↓Q)))) ::: ( G ++ G') )


  | senl : forall ( D F G: list Assignment )( y x : Name )( y : nat )( A B : Proposition )( P : Prepro ),
    Collect D -> Collect F -> Collect G -> Process_Name x -> Process P -> 
    ( D ;;; ( (cons (x:B) (cons ((FName y):A) nil) ) ++ F) !- P ::: G ) -> 
    ( D ;;; ( (cons (x:(A⊗B) ) nil) ++ F) !- (x · (Close y P)) ::: G )


  | senr  : forall ( D F G F' G': list Assignment )( x : Name )( y : nat )( A B : Proposition )( P Q: Prepro ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> Process_Name x -> Process P  -> Process Q -> 
    ( D ;;; F !- P ::: ( (cons ((FName y):A) nil) ++ G) ) ->
    ( D ;;; F' !- Q ::: ( (cons (x:B) nil) ++ G') ) ->
    ( D ;;; (F ++ F') !- (ν (Close y (x « (FName y) »· (P↓Q)))) ::: ( (cons (x:(A⊗B)) nil) ++ G ++ G') )


  | absr : forall ( D F G: list Assignment )( x : Name) (P : Prepro ),
    Collect D -> Collect F -> Collect G -> Process_Name x -> Process P -> 
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; F !- (x ()· P) ::: ( (cons (x:⊥) nil) ++ G) )


  | absl : forall ( D : list Assignment)( x : Name),
    Collect D -> Process_Name x -> 
    ( D ;;; (cons (x:⊥) nil ) !- (x «»·° ) ::: nil )


  | onel : forall ( D F G : list Assignment)( x : Name)( P : Prepro),
    Collect D -> Collect F -> Collect G ->  Process_Name x -> Process P -> 
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; (cons (x:¶) nil ++ F) !- (x ()· P ) ::: G )


  | oner : forall ( D : list Assignment)( x : Name),
    Collect D -> Process_Name x -> 
    ( D ;;; nil !- (x «»·° ) ::: (cons (x:¶) nil ) )


  | copyl : forall ( D F G : list Assignment )( x u : nat )( P : Prepro )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> Process P ->
    ( ( cons ((FName u):A) nil ++ D ) ;;; ( cons ((FName x):A) nil ++ F ) !- P ::: G ) -> 
    ( ( cons ((FName u):A) nil ++ D ) ;;; F !- (ν (Close x ( (FName u) « (FName x) »· P ))) ::: G )


  | copyr : forall ( D F G : list Assignment )( x u : nat )( P : Prepro )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> Process P ->
    ( ( cons ((FName u):A) nil ++ D ) ;;; F !- P ::: ( cons ((FName x):(A^⊥)) nil ++ G) ) -> 
    ( ( cons ((FName u):A) nil ++ D ) ;;; F !- (ν (Close x ( (FName u) « (FName x) »· P ))) ::: G )


  | cutrep : forall ( D F G : list Assignment )( P Q : Prepro )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> 
    Process P -> Process Q ->
    (forall ( x : nat ), ( D ;;; nil !- P ::: ( cons ((FName x):A) nil ) ) )-> 
    (forall ( u : nat ), ( D ;;; (cons ((FName u):A) nil ++ F) !- Q ::: G ) )-> 
    forall ( x u : nat ), ( D ;;; F !- (ν Close u ( ((FName u) !· Close x P) ↓ Q)) ::: G )


  | cutcon : forall ( D F G : list Assignment )( x u : nat )( P Q : Prepro )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> Process P -> Process Q ->
    ( D ;;; ( cons ((FName x):(A^⊥)) nil ) !- P ::: nil ) -> 
    ( D ;;; (cons ((FName u):A) nil ++ F) !- Q ::: G ) -> 
    ( D ;;; F !- (ν Close u ( ((FName u) !· Close x P) ↓ Q)) ::: G )  

*)

where "D ';;;'  F '!-' P ':::' G" := (Inference P D F G).
Hint Constructors Inference : core.


