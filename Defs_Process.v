(*
  Ciro Iván García López
  Tesis de Maestría - Master Thesis
  Session Type Systems Verification
  Unam - 2021
*)
From Coq Require Import Nat.
From Coq Require Import Arith.Peano_dec.
From Coq Require Import Ensembles.
From Coq Require Import Finite_sets.
From Coq Require Import Finite_sets_facts.



From Tmcod Require Import Defs_Tactics.

(*
*)
Definition FVarsE := Ensemble nat.

Notation ø := (Empty_set _).
Notation " x ∈ A " := ( In _ A x ) (at level 50,no associativity).
Notation " A ⊆ B " := ( Included _ A B ) (at level 100, no associativity).
Notation " A ∪ B " := ( Union _ A B ) (at level 80, no associativity).
Notation " A ∩ B " := ( Intersection _ A B ) (at level 80, no associativity).

(*
*)
Inductive Name : Type := 
  | FName ( x : nat) : Name
  | BName ( i : nat) : Name.

Inductive Process : Type  := 
  (*  *)
  | Pzero : Process 
  | Fuse (x y : Name) : Process
  | Parallel (P Q : Process ) : Process
  | Chan_output ( x y : Name ) (P : Process) : Process
  | Chan_zero (x : Name ) : Process
  | Chan_close ( x : Name ) ( P : Process ) : Process
  (* procesos con variables ligadas *)
  | Chan_res (P : Process ) : Process
  | Chan_input ( x : Name ) (P : Process) : Process
  | Chan_replicate ( x : Name)(P : Process ) : Process.


(*

*)
Notation "'θ'" := Pzero (at level 60).
Notation "[ x ←→ y ]" := (Fuse x y ) ( at level 60).
(*
Cambio la notación respecto al artículo, no uso el | porque genera problemas en las definiciones Inductive
*)
Notation "P ↓ Q" :=  (Parallel P Q ) ( at level 60).
Notation "x « y »· P " := (Chan_output x y P ) (at level 60).
Notation "x ·θ " :=  (Chan_zero x ) (at level 60).
Notation "x ()· P" := (Chan_close x P)(at level 60).
(*
Procesos con variables ligadas
*)
Notation " 'ν' P " := (Chan_res P ) ( at level 60).
Notation "x · P " := (Chan_input x P)(at level 60).
Notation " x !· P " :=  (Chan_replicate x P)(at level 60).


(*
Se computan las variables libres de un término.
*)
Definition FVars_Name ( N : Name ) : FVarsE :=
match N with
  | FName x => Singleton nat x
  | BName i => Empty_set nat
end.

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


(*
Se necesitan las nociones de apertura y clausura de preprocesos, por lo que se procede a definirlas apropiadamente.

Se usa la misma notación del artículo de Charguéraud

Se necesita ahora distinguir dos aperturas uno para preprocesos y otra para los nombres.
*) 
Definition Open_Name ( k z : nat )( N : Name ) : Name := 
match N with 
  | FName x => FName x
  | BName i => if ( k =? i ) then (FName z) else (BName i)
end.


(*
Apertura para los preprocesos
*)
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
Notation "{ k ~> z } P " := (Open_Rec k z P)(at level 60).
Definition Open ( z : nat )( T : Process ): Process := Open_Rec 0 z T.
Notation "P ^ z" := (Open_Rec 0 z P).


(*
Chargeroud Menciona que siempre se debe pensar que la variable con la que se abre debe ser un nombre que no aparece en P
*)
Inductive Well_Open : Process -> nat -> Prop := 
  | Is_Well_Open : forall ( P : Process)(z : nat),
    ~( z ∈ (FVars P) ) -> (Well_Open P z).


(*
De manera análoga se necesitan dos cerraduras; una para nombres y otra para preprocesos.
*)
Definition Close_Name ( k z: nat )( N : Name ) : Name := 
match N with
  | FName n0 => if ( n0 =? z ) then (BName k) else N
  | BName i => N
end.


(*
Cerradura de preprocesos bajo la nueva gramática
*)
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


(* *)
Definition Close ( z : nat )( T : Process ): Process := Close_Rec 0 z T.


(*

*)
Inductive lc_name : Name -> Prop := 
  | lc_fname : forall (x : nat), lc_name (FName x).

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
Hint Constructors lc : core.


(*

*)
Inductive Body : Process -> Prop := 
  | is_body : forall (P : Process), 
    ( forall (x : nat), lc ({ 0 ~> x
     }P) ) -> Body(P).


(*

*)
Inductive lca_name : nat -> Name -> Prop := 
  | lca_Fname : forall ( k x : nat), lca_name k (FName x)
  | lca_Bname : forall ( k i : nat), ( i < k ) -> lca_name k (BName i).

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
Hint Constructors Process : core.


(*

*)
Definition Subst_Name ( x y : nat )( N : Name ) : Name :=
match N with 
  | FName n0 => if ( n0 =? x ) then (FName y) else N
  | BName i => N
end.


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
Notation " { y \ x } P " := (Subst x y P) (at level 60). 


Inductive Well_Subst : Process -> nat -> nat -> Prop := 
  | Is_Well_Subst : forall ( P : Process)(x y : nat),
    ~( y ∈ (FVars P) ) -> x <> y -> (Well_Subst P x y).


(*

*) 
Definition Bex_Name ( i j : nat )( N : Name ) : Name := 
match N with 
  | FName x => FName x
  | BName k => if ( k =? i ) then (BName j) else (if ( k =? j ) then (BName i) else (BName k) ) 
end.


(*
Apertura para los preprocesos
*)
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
Notation "{ i <~> j } P " := (Bex_Rec i j P)(at level 60).









From Coq Require Import Lists.List.
Import ListNotations.


(*
*)
Fixpoint MOpen_Name_Rec (k : nat)(L : list nat)( N : Name ) : Name := 
match L , k with
  | nil , _  => N
  | x :: L0, 0 =>  Open_Name 0 x (MOpen_Name_Rec 0 L0 N)
  | x :: L0, S t =>  Open_Name t x (MOpen_Name_Rec t L0 N)
end.


(*
*)
Fixpoint MOpen_Rec (k : nat)(L : list nat)( T : Process ) : Process := 
match L , k with
  | nil , _  => T
  | x :: L0, 0 =>  { 0 ~> x } (MOpen_Rec 0 L0 T)
  | x :: L0, S t =>  { t ~> x } (MOpen_Rec t L0 T)
end.


(*
*)
Fixpoint M2Open_Rec (k : nat)(L : list nat)( T : Process ) : Process := 
match L , k with
  | nil , _  => T
  | x :: L0, 0 =>  { 0 ~> x } (M2Open_Rec 0 L0 T)
  | x :: L0, S t =>  { S t ~> x } (M2Open_Rec t L0 T)
end.



(*
Definición 2.4, equivalencias entre términos, observe que usando NLR no es necesario hablar de alpha-equivalencia pero si es necesario introducir las equivalencias entre procesos.
*)
Reserved Notation "R '===' S" (at level 60).
Inductive Congruence : Process -> Process -> Prop :=
(*    | Con_parallel_zero : forall (P : Process),
        (P↓θ) === P
    
    | Con_res_zero : 
        ( ν θ)  === (θ) 
        
    | Con_conmt_fuses : forall (n m : Name),
        [n ←→ m] === ([m ←→ n])   
*)
      
    | Con_conmt_parallel : forall (P Q : Process),
        (P↓Q) === (Q↓P)
      
    | Con_res_ex : forall (P : Process),
        (ν (ν P)) === (ν (ν ( { 0 <~> 1 }P ) ))
      
    | Con_asoc_parallel : forall (P Q R : Process),
        ((P↓Q)↓R) === (P↓(Q↓R))
      
    | Con_abs_restriction : forall (P Q : Process),
        lc P -> (P↓(ν Q)) === ν (P↓Q)
(*
    | Con_con_res : forall (P Q : Process)(x : nat), 
      lc P -> P === Q -> (ν Close x P) === (ν Close x Q)
      
    | Con_con_output : forall (P Q : Process)(n m : Name), 
      P === Q -> ( n « m »· P) === ( n « m »· Q)
      
    | Con_con_repli : forall (P Q : Process)(n : Name)(x : nat), 
      lc P -> P === Q -> ( n !· Close x P) === (n !· Close x Q)
      
    | Con_con_parallel : forall (P Q R : Process), 
      P === Q -> (R↓P) === (R↓Q)
      
    | Con_con_input : forall (P Q : Process)(n : Name)(x : nat), 
      lc P -> P === Q -> ( n · Close x P) === ( n · Close x Q)  
      
    | Con_con_chan_close : forall (P Q : Process)(n : Name), 
      P === Q -> ( n ()· P) === ( n ()· Q)  
*)
where "R '===' S" := (Congruence R S).
Hint Constructors Congruence : core.


(*
Definición 2.5, reducciones. Observe que la última reducción queda congelada, esto debido a que no ha sido posible reconciliar Coq (genera argumentos circulares) con la prueba en papel.
*)
Reserved Notation "R '-->' S" (at level 60).
Inductive Reduction : Process -> Process -> Prop :=

  | Red_output_input : forall ( x y : nat ) ( P Q : Process ),
    lc P -> Body Q ->
    ( ( ( (FName x) « (FName y) »· P)  ↓ ( (FName x) · Q) ) --> (P ↓ ( {0 ~> y} Q )) )

  | Red_parallel_replicate : forall (x y : nat) (P Q : Process),
    lc P -> Body Q ->
      (( ( (FName x) « (FName y) »· P) ↓ ( (FName x) !· Q )  ) --> ( P ↓ ({0 ~> y} Q) ↓ ( (FName x) !· Q) ))

  | Red_chzero_chclose : forall ( Q : Process) (x : nat),
     lc Q -> 
     ( ( ( (FName x) ·θ ) ↓ ( (FName x) ()· Q ) ) -->  Q )

  | Red_parallel_fuse : forall ( x y : nat) ( P : Process),
    lc P -> 
    ( P ↓ ([(FName x) ←→ (FName y)]) --> (Subst x y P) )

  | Red_reduction_parallel : forall ( P Q R : Process), 
    lc P -> lc R ->
    ((Q --> R) -> ((P ↓ Q ) --> (P ↓ R)))

  | Red_reduction_chanres : forall (P Q : Process)( x : nat),
    lc P -> 
    ( P --> Q ) -> ( ν (Close x P) --> ν (Close x Q) )

   | Red_reduction_struct : forall ( P Q P' Q' : Process ),
    lc P' -> ( P' === P ) -> ( Q' === Q ) ->
    (P' --> Q') -> (P --> Q) 
where "R '-->' S" := (Reduction R S).

