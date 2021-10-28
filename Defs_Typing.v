(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the tactis and Hint Db for the proofs.
*)
From Coq Require Import Ensembles.


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
Definition Context := Ensemble Assignment.


(**
*)
Inductive Collect : Context -> Prop := is_collect :
  forall L : Context,
  (forall H : Assignment, (H ∈ L) -> Assig H ) -> Collect L.
#[global]
Hint Constructors Collect : Piull.


(**
*)
Inductive Well_Collected : Context -> Process -> Prop := is_well_collected : 
forall (L : Context)(P : Process),
  (forall (x : nat)(A : Proposition), ( (x ∈ FVars P) -> ( (FName x:A) ∈ L ) )) -> (Well_Collected L P).
#[global]
Hint Constructors Well_Collected : Piull.


(**
*)
Inductive Disjoint_Sets : Context -> Context -> Prop := are_disjoint_lists :
forall (D F : Context),
  (forall (x : nat)(A B: Proposition), ~ ( ( (FName x:A) ∈ D )  /\ ( (FName x:A) ∈ F) ) ) -> (Disjoint_Sets D F).
#[global]
Hint Constructors Disjoint_Sets : Piull.


(**
*)
Inductive Disjoint_Contexts : Context -> Context -> Context -> Prop := are_disjoint_contexts :
forall (D F G : Context),
  ( (Disjoint_Sets D F) /\ (Disjoint_Sets D G) /\ (Disjoint_Sets  F G) ) -> (Disjoint_Contexts D F G).
#[global]
Hint Constructors Disjoint_Contexts : Piull.

Definition Sng ( H : Assignment ) : Context := Singleton _ H.
#[global]
Hint Resolve Sng : Piull.




(**
*)
Reserved Notation "D ';;;'  F '!-' P ':::' G" (at level 60).
Inductive Inference : Process -> Context -> Context -> Context -> Prop := 
  | idr : forall ( D : Context )( x y : nat )( A : Proposition ),
    Collect D -> x <> y ->
    Well_Collected (D ∪ Sng (FName y:A) ∪ Sng (FName x:A) ) ([FName x ←→ FName y]) ->
    Disjoint_Contexts D (Sng (FName y:A)) (Sng (FName x:A)) ->
    ( D ;;; (Sng (FName x:A)) !- ([FName x←→ FName y]) ::: (Sng (FName y:A))  )


  | idl : forall ( D : Context )( x y : nat )( A : Proposition ),
    Collect D -> x <> y -> 
    Well_Collected (D ∪ Sng (FName x:A) ∪ Sng (FName y:(A^⊥))) ([FName x ←→ FName y]) ->
    Disjoint_Contexts D (Sng (FName x:A) ∪ Sng (FName y:(A^⊥)) ) ø ->
    ( D ;;; (Sng (FName x:A) ∪ Sng (FName y:(A^⊥)) ) !-  ([FName x ←→ FName y]) ::: ø  )


  | repr : forall ( D : Context )( x y : nat )( A : Proposition )( P : Process ),
    Collect D -> lc P -> x <> y ->
    Well_Collected (D ∪ Sng (FName y:A)) P ->
    Well_Collected (D ∪ Sng (FName x:!A)) (FName x !· (Close y P)) ->
    Disjoint_Contexts D ø (Sng (FName y:A)) ->
    Disjoint_Contexts D ø (Sng (FName x:!A)) ->
    ( D ;;; ø !- P ::: (Sng (FName y:A)) ) ->
    ( D ;;; ø !- (FName x !· (Close y P)) ::: (Sng (FName x:!A)) )


  | repl : forall ( D F G : Context )( u x : nat )( A : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> u <> x -> 
    ~( x ∈ (FVars P) ) -> 
    Well_Collected ( Sng (FName u:A) ∪ D ∪ F ∪ G ) P ->
    Well_Collected ( Sng (FName x:!A) ∪ D ∪ F ∪ G ) ({x \ u }P) ->
    Disjoint_Contexts (Sng (FName u:A) ∪ D) F G ->
    Disjoint_Contexts D (Sng (FName x:!A) ∪ F) G ->
    ( (Sng (FName u:A) ∪ D) ;;; F !- P ::: G ) ->
    ( D ;;; (Sng (FName x:!A) ∪ F) !- ({x \ u }P) ::: G)


  | wnotr : forall ( D F G : Context )( u x : nat )( A : Proposition )( P : Process ),
    Collect D -> Collect G -> Collect F -> lc P -> u <> x -> 
    ~( x ∈ (FVars P) ) ->
    ( ( Sng (FName u:A) ∪ D ) ;;; F !- P ::: G ) -> 
    ( D ;;; F !- ({x \ u }P) ::: ( Sng (FName x: (? (A ^⊥))) ∪ G) )


  | wnotl : forall ( D : Context )( x y : nat )( A : Proposition )( P : Process ),
    Collect D -> lc P -> x <> y -> 
    ( D ;;; (Sng (FName y:A)) !- P ::: ø ) -> 
    ( D ;;; (Sng (FName x:? A)) !- ( FName x !· (Close y P)) ::: ø)


  | limpr : forall ( D F G: Context )( x y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> x <> y -> 
    lc P -> 
    ( D ;;; ( Sng (FName y:A) ∪ F) !- P ::: ( Sng (FName x:B) ∪ G ) ) -> 
    ( D ;;; F !- (FName x · (Close y P)) ::: (Sng (FName x:(A−∘B)) ∪ G ) )


  | limpl : forall ( D F G F' G': Context )( x y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> 
    lc P  -> lc Q -> 
    ( D ;;; F !- P ::: ( Sng (FName y:A) ∪ G ) ) ->
    ( D ;;; (Sng (FName x:B) ∪ F') !- Q ::: G' ) ->
    ( D ;;; (Sng (FName x:(A−∘B)) ∪ F ∪ F') !- (ν Close y (FName x « FName y »· (P↓Q))) ::: ( G ∪ G') )


  | rampr : forall ( D F G: Context )( x y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> 
    ( D ;;; F !- P ::: ( Sng (FName x:B) ∪ Sng (FName y:A) ∪ G ) ) -> 
    ( D ;;; F !- (FName x · (Close y P)) ::: ( Sng (FName x:(A⅋B)) ∪ G ) )


  | rampl  : forall ( D F G F' G': Context )( x y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> lc P  -> lc Q -> 
    ( D ;;; ( Sng (FName y:A) ∪ F ) !- P ::: G ) ->
    ( D ;;; ( Sng (FName x:B) ∪ F') !- Q ::: G') ->
    ( D ;;; ( Sng (FName x:(A⅋B)) ∪ F ∪F') !- (ν Close y (FName x « FName y »· (P↓Q)) ) ::: ( G ∪ G') )



  | otiml : forall ( D F G: Context )( x y : nat )( y : nat )( A B : Proposition )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> x <> y -> 
    ( D ;;; ( Sng (FName x:B) ∪ Sng (FName y:A) ∪ F ) !- P ::: G ) -> 
    ( D ;;; ( Sng (FName x:(A⊗B)) ∪ F) !- (FName x · Close y P) ::: G )


  | otimr  : forall ( D F G F' G': Context )( x y : nat )( A B : Proposition )( P Q: Process ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> lc P  -> lc Q -> x <> y ->
    ( D ;;; F !- P ::: ( Sng (FName y:A) ∪ G) ) ->
    ( D ;;; F' !- Q ::: ( Sng (FName x:B) ∪ G') ) ->
    ( D ;;; (F ∪ F') !- ν Close y ( FName x « FName y »· (P↓Q)) ::: ( Sng (FName x:(A⊗B)) ∪ G ∪ G') )


  | perpr : forall ( D F G: Context )( x : nat )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> 
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; F !- (FName x ()· P) ::: ( Sng (FName x:⊥) ∪ G ) )


  | perpl : forall ( D : Context )( x : nat ),
    Collect D ->
    ( D ;;; (Sng (FName x:⊥)) !- (FName x ·θ ) ::: ø )


  | onel : forall ( D F G : Context )( x : nat )( P : Process ),
    Collect D -> Collect F -> Collect G -> lc P -> 
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; (Sng (FName x:¶) ∪ F) !- (FName x ()· P ) ::: G )


  | oner : forall ( D : Context)( x : nat ),
    Collect D -> 
    ( D ;;; ø !- (FName x ·θ ) ::: ( Sng (FName x:¶) ) )


  | copyl : forall ( D F G : Context )( x u : nat )( P : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> lc P -> x <> u ->
    ( ( Sng (FName u:A) ∪ D ) ;;; ( Sng (FName x:A) ∪ F ) !- P ::: G ) -> 
    ( ( Sng (FName u:A) ∪ D ) ;;; F !- ν Close x ( FName u « FName x »· P ) ::: G )


  | copyr : forall ( D F G : Context )( x u : nat )( P : Process )( A : Proposition ),
    Collect D -> Collect F -> Collect G -> lc P -> x <> u ->
    ( ( Sng (FName u:A) ∪ D ) ;;; F !- P ::: ( Sng (FName x:(A^⊥)) ∪ G) ) -> 
    ( ( Sng (FName u:A) ∪ D ) ;;; F !- ν Close x ( FName u « FName x »· P ) ::: G )


  | cutrep : forall ( D F G : Context )( P Q : Process )( A : Proposition )( x u : nat ),
    Collect D -> Collect F -> Collect G ->
    lc P -> lc Q -> x <> u ->
    ( D ;;; ø !- P ::: ( Sng (FName x:A) ) ) -> 
    ( (Sng (FName u:A) ∪ D) ;;; F !- Q ::: G )  -> 
    ( D ;;; F !- ν Close u ((FName u !· Close x P) ↓ Q) ::: G )


  | cutr : forall ( D F G F' G' : Context )( P Q : Process )( A : Proposition )( x : nat ),
    Collect D -> Collect F -> Collect G -> Collect F' -> Collect G' -> 
    lc P -> lc Q ->
    ( D ;;; F !- P ::: ( Sng (FName x:A) ∪ G ) ) ->
    ( D ;;; (Sng (FName x:A) ∪ F') !- Q ::: G' ) ->
    ( D ;;; (F ∪ F') !- ( ν Close x (P↓Q) ) ::: (G ∪ G') )

    

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









