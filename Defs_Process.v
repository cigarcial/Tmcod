(**
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
  
  This file contains the definitions for the processes.
*)
From Coq Require Import Nat.
From Coq Require Import Arith.Peano_dec.
From Coq Require Import Ensembles.

From Tmcod Require Import Defs_Tactics.


(**
  The following definitions are required to work with Ensembles or the representation for sets given by Coq.
*)
Definition FVarsE := Ensemble nat.


(**
  Definition for the names, two types bound or free.
  The definition use natural numbers to represent free names, this can be changed for any datatype that implements equality comparision at syntactic level and boolean level.
*)
Inductive Name : Type := 
  | FName ( x : nat) : Name
  | BName ( i : nat) : Name.
#[global]
Hint Constructors Name : Piull.

Inductive Process : Type  := 
  | Pzero : Process 
  | Fuse (x y : Name) : Process
  | Parallel (P Q : Process ) : Process
  | Chan_output ( x y : Name ) (P : Process) : Process
  | Chan_zero (x : Name ) : Process
  | Chan_close ( x : Name ) ( P : Process ) : Process
  (* Processes with bounded names *)
  | Chan_res (P : Process ) : Process
  | Chan_input ( x : Name ) (P : Process) : Process
  | Chan_replicate ( x : Name)(P : Process ) : Process.
#[global]
Hint Constructors Process : Piull.


(**
  Notation for the processes.
  In most cases the notation is the same, but in others the notation is changed due to conflicts with Coq syntax, e.g. | for ↓.
*)
Notation "'θ'" := Pzero (at level 60).
Notation "[ x ←→ y ]" := (Fuse x y ) ( at level 60).
Notation "P ↓ Q" :=  (Parallel P Q ) ( at level 60).
Notation "x « y »· P " := (Chan_output x y P ) (at level 60).
Notation "x ·θ " :=  (Chan_zero x ) (at level 60).
Notation "x ()· P" := (Chan_close x P)(at level 60).
Notation " 'ν' P " := (Chan_res P ) ( at level 60).
Notation "x · P " := (Chan_input x P)(at level 60).
Notation " x !· P " :=  (Chan_replicate x P)(at level 60).


(**
  Free names for a given term.
*)
Definition FVars_Name ( N : Name ) : FVarsE :=
match N with
  | FName x => Singleton nat x
  | BName i => Empty_set nat
end.
#[global]
Hint Resolve FVars_Name : Piull.

Fixpoint FVars ( T : Process ) {struct T} : FVarsE := 
match T with
  | Pzero => Empty_set nat
  | Fuse x y => (FVars_Name x) ∪ (FVars_Name y)
  | Parallel P Q => (FVars P) ∪ (FVars Q)
  | Chan_output x y P => (FVars_Name x) ∪ (FVars_Name y) ∪ (FVars P)
  | Chan_zero x => FVars_Name x
  | Chan_close x P => (FVars_Name x) ∪ (FVars P)
  | Chan_res P => FVars P
  | Chan_input x P => (FVars_Name x) ∪ (FVars P)
  | Chan_replicate x P => (FVars_Name x) ∪ (FVars P)
end.
#[global]
Hint Resolve FVars : Piull.


(**
  Open functions for names and processes.
  The notation follows the paper from Charguéraud.
*) 
Definition Open_Name ( k z : nat )( N : Name ) : Name := 
match N with 
  | FName x => FName x
  | BName i => if ( k =? i ) then (FName z) else (BName i)
end.
#[global]
Hint Resolve Open_Name : Piull.

Fixpoint Open_Rec (k z : nat)( T : Process ) {struct T} : Process := 
match T with
  | Pzero => Pzero
  | Fuse x y => Fuse (Open_Name k z x ) (Open_Name k z y )
  | Parallel P Q => Parallel (Open_Rec k z P) (Open_Rec k z Q)
  | Chan_output x y P => Chan_output (Open_Name k z x) (Open_Name k z y) (Open_Rec k z P)
  | Chan_zero x => Chan_zero (Open_Name k z x)
  | Chan_close x P => Chan_close (Open_Name k z x) (Open_Rec k z P)
  | Chan_res P => Chan_res (Open_Rec (S k) z P)
  | Chan_input x P => Chan_input (Open_Name k z x) (Open_Rec (S k) z P)
  | Chan_replicate x P => Chan_replicate (Open_Name k z x) (Open_Rec (S k) z P)
end.
#[global]
Hint Resolve Open_Rec : Piull.

Notation "{ k ~> z } P " := (Open_Rec k z P)(at level 60).
Definition Open ( z : nat )( T : Process ): Process := Open_Rec 0 z T.
#[global]
Hint Resolve Open : Piull.
Notation "P ^ z" := (Open_Rec 0 z P).


(**
  In his article, Chargeroud warn that the variable which is used to open a name should now be free in the term.
*)
Inductive Well_Open : Process -> nat -> Prop := 
  | Is_Well_Open : forall ( P : Process)(z : nat),
    ~( z ∈ (FVars P) ) -> (Well_Open P z).
#[global]
Hint Constructors Well_Open : Piull.


(**
  Definition for the closed functions.
*)
Definition Close_Name ( k z: nat )( N : Name ) : Name := 
match N with
  | FName n0 => if ( n0 =? z ) then (BName k) else N
  | BName i => N
end.
#[global]
Hint Resolve Close_Name : Piull.

Fixpoint Close_Rec (k z : nat)( T : Process ) {struct T} : Process := 
match T with
  | Pzero => Pzero
  | Fuse x y => Fuse (Close_Name k z x ) (Close_Name k z y )
  | Parallel P Q => Parallel (Close_Rec k z P) (Close_Rec k z Q)
  | Chan_output x y P => Chan_output (Close_Name k z x) (Close_Name k z y) (Close_Rec k z P) 
  | Chan_zero x => Chan_zero (Close_Name k z x)
  | Chan_close x P => Chan_close (Close_Name k z x) (Close_Rec k z P)
  | Chan_res P => Chan_res (Close_Rec (S k) z P)
  | Chan_input x P => Chan_input (Close_Name k z x) (Close_Rec (S k) z P)
  | Chan_replicate x P => Chan_replicate (Close_Name k z x) (Close_Rec (S k) z P)
end.
#[global]
Hint Resolve Close_Rec : Piull.

Definition Close ( z : nat )( T : Process ): Process := Close_Rec 0 z T.
#[global]
Hint Resolve Close : Piull.

(**
  Locally closed predicate.
*)
Inductive lc_name : Name -> Prop := 
  | lc_fname : forall (x : nat), lc_name (FName x).
#[global]
Hint Constructors lc_name : Piull.

Inductive lc : Process -> Prop :=
  | lc_pzero : lc(θ)
  
  | lc_fuse : forall x y : Name, 
    lc_name x -> lc_name y -> lc ( [ x ←→ y] )
    
  | lc_parallel : forall P Q : Process, 
    lc P -> lc Q -> lc (P ↓ Q)
    
  | lc_chan_output : forall (x y : Name ) (P : Process),
    lc_name x -> lc_name y -> lc P -> lc ( x «y»· P)
  
  | lc_chan_zero : forall x : Name, 
    lc_name x -> lc ( x ·θ )
    
  | lc_chan_close : forall (x : Name)(P : Process),
    lc_name x -> lc P -> lc ( x ()· P )
   
  | lc_chan_res : forall (P : Process), 
    ( forall (x : nat), lc ({ 0 ~> x }P) ) -> lc (ν P)
  
  | lc_chan_input : forall (x : Name ) (P: Process),
    lc_name x -> 
    ( forall (x : nat), lc ({ 0 ~> x }P) ) -> lc ( x · P)
   
  | lc_chan_replicate : forall (x : Name) (P : Process),
    lc_name x -> 
    ( forall (x : nat), lc ({ 0 ~> x }P) ) -> lc ( x !· P ).
#[global]
Hint Constructors lc : Piull.


(**
  Definition of a body.
*)
Inductive Body : Process -> Prop := 
  | is_body : forall (P : Process), 
    ( forall (x : nat), lc ({ 0 ~> x}P) ) -> Body(P).
#[global]
Hint Constructors Body : Piull.


(**
  Locally closed at predicate.
*)
Inductive lca_name : nat -> Name -> Prop := 
  | lca_Fname : forall ( k x : nat), lca_name k (FName x)
  | lca_Bname : forall ( k i : nat), ( i < k ) -> lca_name k (BName i).
#[global]
Hint Constructors lca_name : Piull.

Inductive lca : nat -> Process -> Prop :=
  | lca_pzero : forall k : nat, lca k (θ)
  
  | lca_fuse : forall ( k : nat )( x y : Name ),
    lca_name k x -> lca_name k y -> lca k ( [ x ←→ y] )
    
  | lca_parallel : forall ( k : nat )( P Q : Process ),
    lca k P -> lca k Q -> lca k (P ↓ Q)
    
  | lca_chan_output : forall ( k : nat )( x y : Name )( P : Process ),
    lca_name k x -> lca_name k y -> lca k P -> lca k ( x «y»· P)
  
  | lca_chan_zero : forall ( k : nat )( x : Name ),
    lca_name k x -> lca k ( x ·θ )
    
  | lca_chan_close : forall ( k : nat )( x : Name )( P : Process ),
    lca_name k x -> lca k P -> lca k ( x ()· P )
  
  | lca_chan_res : forall ( k : nat )( P : Process ),
     lca (S k) P -> lca k (ν P)
  
  | lca_chan_input : forall ( k : nat )( x : Name )( P: Process ),
    lca_name k x -> lca (S k) P -> lca k ( x · P)
   
  | lca_chan_replicate : forall ( k : nat )( x : Name )( P : Process ),
    lca_name k x -> lca (S k) P -> lca k ( x !· P ).
#[global]
Hint Constructors lca : Piull.


(**
  Definnition for substitution of free names.
*)
Definition Subst_Name ( x y : nat )( N : Name ) : Name :=
match N with 
  | FName n0 => if ( n0 =? x ) then (FName y) else N
  | BName i => N
end.
#[global]
Hint Resolve Subst_Name : Piull.

Fixpoint Subst ( x y : nat )( T : Process ) {struct T} : Process := 
match T with
  | Pzero => Pzero
  | Fuse u v => Fuse (Subst_Name x y u ) (Subst_Name x y v)
  | Parallel P Q => Parallel (Subst x y P) (Subst x y Q)
  | Chan_output u v P => Chan_output (Subst_Name x y u) (Subst_Name x y v) (Subst x y P)
  | Chan_zero u => Chan_zero (Subst_Name x y u )
  | Chan_close u P => Chan_close (Subst_Name x y u) (Subst x y P)
  (* preprocesos con variables ligadas *)
  | Chan_res P => Chan_res (Subst x y P)
  | Chan_input u P  => Chan_input (Subst_Name x y u) (Subst x y P)
  | Chan_replicate u P => Chan_replicate (Subst_Name x y u) (Subst x y P)
end.
#[global]
Hint Resolve Subst : Piull.

Notation " { y \ x } P " := (Subst x y P) (at level 60).


(**
*)
Inductive Well_Subst : Process -> nat -> nat -> Prop := 
  | Is_Well_Subst : forall ( P : Process)(x y : nat),
    ~( y ∈ (FVars P) ) -> x <> y -> (Well_Subst P x y).
#[global]
Hint Constructors Well_Subst : Piull.


(**
  Definition for the bound names exchange function.
*) 
Definition Bex_Name ( i j : nat )( N : Name ) : Name := 
match N with 
  | FName x => FName x
  | BName k => if ( k =? i ) then (BName j) else (if ( k =? j ) then (BName i) else (BName k) ) 
end.
#[global]
Hint Resolve Bex_Name : Piull.

Fixpoint Bex_Rec (i j : nat)( T : Process ) {struct T} : Process := 
match T with
  | Pzero => Pzero
  | Fuse x y => Fuse (Bex_Name i j x ) (Bex_Name i j y )
  | Parallel P Q => Parallel (Bex_Rec i j P) (Bex_Rec i j Q)
  | Chan_output x y P => Chan_output (Bex_Name i j x) (Bex_Name i j y) (Bex_Rec i j P)
  | Chan_zero x => Chan_zero (Bex_Name i j x)
  | Chan_close x P => Chan_close (Bex_Name i j x) (Bex_Rec i j P)
  | Chan_res P => Chan_res (Bex_Rec (S i) (S j) P)
  | Chan_input x P => Chan_input (Bex_Name i j x) (Bex_Rec (S i) (S j) P)
  | Chan_replicate x P => Chan_replicate (Bex_Name i j x) (Bex_Rec (S i) (S j) P)
end.
#[global]
Hint Resolve Bex_Rec : Piull.

Notation "{ i <~> j } P " := (Bex_Rec i j P)(at level 60).


(**
  Require for the MOpen definitions.
*)
From Coq Require Import Lists.List.
Import ListNotations.


(**
  Definition for multiple open function in names
*)
Fixpoint MOpen_Name_Rec (k : nat)(L : list nat)( N : Name ) : Name := 
match L , k with
  | nil , _  => N
  | x :: L0, 0 =>  Open_Name 0 x (MOpen_Name_Rec 0 L0 N)
  | x :: L0, S t =>  Open_Name t x (MOpen_Name_Rec t L0 N)
end.
#[global]
Hint Resolve MOpen_Name_Rec : Piull.

Fixpoint MOpen_Rec (k : nat)(L : list nat)( T : Process ) : Process := 
match L , k with
  | nil , _  => T
  | x :: L0, 0 =>  { 0 ~> x } (MOpen_Rec 0 L0 T)
  | x :: L0, S t =>  { t ~> x } (MOpen_Rec t L0 T)
end.
#[global]
Hint Resolve MOpen_Rec : Piull.


(**
  Multiple open at second level.
*)
Fixpoint M2Open_Rec (k : nat)(L : list nat)( T : Process ) : Process := 
match L , k with
  | nil , _  => T
  | x :: L0, 0 =>  { 0 ~> x } (M2Open_Rec 0 L0 T)
  | x :: L0, S t =>  { S t ~> x } (M2Open_Rec t L0 T)
end.
#[global]
Hint Resolve M2Open_Rec : Piull.


(**
*)
Inductive IsClosing : Process -> nat -> Prop :=
  | IsClosing_Base : forall ( P : Process)(x: nat),
    (forall (u v : nat)(Q : Process), Q = ({u \ v} Close x P) -> u <> x /\ x <> v ) -> (IsClosing P x).
#[global]
Hint Constructors IsClosing : Piull.


(**
*)
Inductive IsClosingInj : Process -> nat -> Prop :=
  | IsClosingInj_Base : forall ( P : Process)(x: nat),
    (forall (u : nat)(Q : Process), Q = (Close x P) -> u = x ) -> (IsClosingInj P x).
#[global]
Hint Constructors IsClosingInj : Piull.


(**
  Definition 2.4 - Structural congruence
*)
Reserved Notation "R '===' S" (at level 60).
Inductive Congruence : Process -> Process -> Prop :=
(*    | Con_parallel_zero : forall (P : Process),
        (P↓θ) === P
      
    | Con_res_zero : 
        ( ν θ)  === (θ) 
        
    | Con_conmt_fuses : forall (n m : Name),
        [n ←→ m] === ([m ←→ n])
        
    | Con_res_ex : forall (P : Process),
        (ν (ν P)) === (ν (ν ( { 0 <~> 1 }P ) ))
        
    | Con_conmt_parallel : forall (P Q : Process),
        (P↓Q) === (Q↓P)
        ν (P↓Q) === ν (Q↓P)
*)
      
    | Con_asoc_parallel : forall (P Q R : Process),
        ((P↓Q)↓R) === (P↓(Q↓R))
      
    | Con_abs_restriction : forall (P Q : Process),
        lc P -> (P↓(ν Q)) === ν (P↓Q)
      
where "R '===' S" := (Congruence R S).
#[global]
Hint Constructors Congruence : Piull.


(**
  Definition 2.5 - Processes Reductions.
*)
Reserved Notation "R '-->' S" (at level 60).
Inductive Reduction : Process -> Process -> Prop :=

  | Red_parallel_fuse_dr1 : forall ( x y : nat) ( P : Process),
    lc P -> x <> y -> IsClosing P x -> IsClosingInj P x -> x ∈ FVars P -> 
    ( ν Close x (P ↓ ([(FName x) ←→ (FName y)])) -->
    (Subst x y P) )


  | Red_parallel_fuse_dr2 : forall ( x y : nat) ( P : Process),
    lc P -> x <> y -> IsClosing P x -> IsClosingInj P x -> x ∈ FVars P -> 
    ( ν Close x (P ↓ ([(FName y) ←→ (FName x)])) -->
    (Subst x y P) )


  | Red_parallel_fuse_iz1 : forall ( x y : nat) ( P : Process),
    lc P -> x <> y -> IsClosing P x -> IsClosingInj P x -> x ∈ FVars P -> 
    ( ν Close x (([(FName y) ←→ (FName x)]) ↓ P ) -->
    (Subst x y P) )


  | Red_parallel_fuse_iz2 : forall ( x y : nat) ( P : Process),
    lc P -> x <> y -> IsClosing P x -> IsClosingInj P x -> x ∈ FVars P -> 
    ( ν Close x (([(FName x) ←→ (FName y)]) ↓ P ) -->
    (Subst x y P) )


  | Red_chzero_chclose_lt : forall ( Q : Process) (x : nat),
     lc Q -> ~ x ∈ FVars Q -> IsClosing Q x -> IsClosingInj Q x ->
     ( ν Close x ( ( (FName x) ·θ ) ↓ ( (FName x) ()· Q ) ) -->  Q )


  | Red_chzero_chclose_dr : forall ( Q : Process) (x : nat),
     lc Q -> ~ x ∈ FVars Q -> IsClosing Q x -> IsClosingInj Q x ->
     ( ν Close x ( ( (FName x) ()· Q ) ↓ ( (FName x) ·θ ) ) -->  Q )


  | Red_parallel_replicate_rg : forall (y u : nat) (P Q : Process),
    Body P -> lc Q -> ~ u ∈ FVars P -> ~ y ∈ FVars P -> u <> y -> IsClosing P u ->  
    IsClosing P y -> IsClosingInj P u -> IsClosingInj P y ->
      ( ν Close u ( ((FName u) !· P) ↓  ν Close y  ( ((FName u) « (FName y) »· Q)) )
      --> ν Close u ( ((FName u) !· P) ↓  ν Close y  ( Q ↓ ({0 ~> y} P) )) )


  | Red_parallel_replicate_lf : forall (y u : nat) (P Q : Process),
    Body P -> lc Q -> ~ u ∈ FVars P -> ~ y ∈ FVars P -> u <> y -> IsClosing P u -> 
    IsClosing P y -> IsClosingInj P u -> IsClosingInj P y ->
      ( ν Close u ( ((FName u) !· P) ↓  ν Close y  ( ((FName u) « (FName y) »· Q)) )
      --> ν Close u ( ((FName u) !· P) ↓  ν Close y  ( ({0 ~> y} P) ↓ Q )) )


  | Red_output_input_rg : forall ( x y : nat) (P Q R : Process),
    Body P -> lc Q -> lc R -> x <> y ->
    ~ y ∈ FVars P -> ~ y ∈ FVars R -> ~ x ∈ FVars Q ->
    IsClosing P x -> IsClosing P y -> 
    IsClosingInj P x -> IsClosingInj P y ->
      ( ν Close x (  ((FName x) · P) ↓ ν Close y ( (FName x) « (FName y) »· (Q↓R)) )
      --> ν Close y ( ν Close x ( ({0 ~> y} P) ↓ R ) ↓ Q ) )


  | Red_output_input_lf : forall ( x y : nat) (P Q R : Process),
    Body P -> lc Q -> lc R -> x <> y -> 
    ~ y ∈ FVars P -> ~ y ∈ FVars R ->
    IsClosing P x -> IsClosing P y -> 
    IsClosingInj P x -> IsClosingInj P y ->
      ( ν Close x ( ν Close y ( (FName x) « (FName y) »· (Q↓R)) ↓ ((FName x) · P) )
      --> ν Close x ( R ↓ ν Close y ( Q ↓ ({0 ~> y} P)) ) )

(*

  | Red_output_input : forall ( x y : nat ) ( P Q : Process ),
    lc P -> Body Q ->
    ( ( ( (FName x) « (FName y) »· P)  ↓ ( (FName x) · Q) ) --> (P ↓ ( {0 ~> y} Q )) )



   | Red_reduction_struct : forall ( P Q P' Q' : Process ),
    lc P' -> ( P' === P ) -> ( Q' === Q ) ->
    (P' --> Q') -> (P --> Q) 


*)
where "R '-->' S" := (Reduction R S).
#[global]
Hint Constructors Reduction: Piull.





Fixpoint M4Open_Rec (k : nat)(L : list nat)( T : Process ) : Process := 
match L , k with
  | nil , _  => T
  | x :: L0, 0 =>  { 0 ~> x } (M4Open_Rec 0 L0 T)
  | x :: L0, (S 0) =>  { (S 0) ~> x } (M4Open_Rec 0 L0 T)
  | x :: L0, (S (S 0)) =>  { (S (S 0)) ~> x } (M4Open_Rec 0 L0 T)
  | x :: L0, S t =>  { S t ~> x } (M4Open_Rec t L0 T)
end.
#[global]
Hint Resolve M4Open_Rec : Piull.





