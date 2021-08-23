(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Nat.
From Coq Require Import Arith.Peano_dec.
From Coq Require Import Ensembles.
From Coq Require Import Finite_sets.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Lia.



From Coq Require Import Lists.List.

Import ListNotations.






Ltac inversions H := inversion H; subst.
Ltac isBody := constructor; intros; simpl; repeat constructor.


(*
Se llaman algunas definiciones de conjuntos finitos para el manejo del conjunto de variables libres (FVar).
FVarsE representa un conjunto de naturales.
*)
Definition FVarsE := Ensemble nat.

Notation ø := (Empty_set _).
Notation " x ∈ A " := ( In _ A x ) (at level 90,no associativity).
Notation " A ⊆ B " := ( Included _ A B ) (at level 100, no associativity).
Notation " A ∪ B " := ( Union _ A B ) (at level 80, no associativity).
Notation " A ∩ B " := ( Intersection _ A B ) (at level 80, no associativity).

(*
Cuarta aproximación a la mecanización de los procesos usando las nocinoes de 'locally named representation'.

FVAR y BVAR representan la idea de variable libre y ligada, respectivamente. 

Para esta parte se usa como base las ideas expuestas en el artículo de Castro Engineering The Meta-Theory of Session Types

Definición 2.3, por un lado se representan las variables y por el otro los procesos. 

Se cambia la representación de un nombre libre de str a nat.
*)
Inductive Name : Type := 
  | FName ( x : nat) : Name
  | BName ( i : nat) : Name.

Inductive Prepro : Type  := 
  (* Ahora vienen los procesos bajo las nuevas ideas *)
  | Preparallel (P Q : Prepro ) : Prepro
  | Preoutput ( x y : Name ) (P : Prepro) : Prepro
  (* preprocesos con variables ligadas *)
  | Prechan_res (P : Prepro ) : Prepro.


(*
Las nuevas ideas son más simples ya que reducen los términos no deseados.

La notación cambia bastante, no se fija el tipo de nombre por defecto

Asociatividad y prioridades de acuerdo a lo expuesto en Sangiorgi - The Pi Calculus. 
*)

(*
Cambio la notación respecto al artículo, no uso el | porque genera problemas en las definiciones Inductive
*)
Notation "P ↓ Q" :=  (Preparallel P Q ) ( at level 60).
Notation "x  « y »· P " := (Preoutput x y P ) (at level 60).
(*
Procesos con variables ligadas
*)
Notation " 'ν' P " := (Prechan_res P ) ( at level 60).


(*
Se computan las variables libres de un término.
*)
Definition FVars_Name ( N : Name ) : FVarsE :=
match N with
  | FName x => Singleton nat x
  | BName i => Empty_set nat
end.

Fixpoint FVars ( T : Prepro ) {struct T} : FVarsE := 
match T with
  | Preparallel P Q => (FVars P) ∪ (FVars Q)
  | Preoutput x y P => (FVars_Name x) ∪ (FVars_Name y) ∪ (FVars P)
  | Prechan_res P => FVars P
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
Fixpoint Open_Rec (k z : nat)( T : Prepro ) {struct T} : Prepro := 
match T with
  | Preparallel P Q => Preparallel (Open_Rec k z P) (Open_Rec k z Q)
  | Preoutput x y P => Preoutput (Open_Name k z x) (Open_Name k z y) (Open_Rec k z P)
  | Prechan_res P => Prechan_res (Open_Rec (S k) z P)
end.
Notation "{ k ~> z } P " := (Open_Rec k z P)(at level 60).


(*
Chargeroud Menciona que siempre se debe pensar que la variable con la que se abre debe ser un nombre que no aparece en P
*)
(* Inductive Well_Open : Prepro -> nat -> Prop := 
  | Is_Well_Open : forall ( P : Prepro)(z : nat),
    ~( In _ (FVars P) z) -> (Well_Open P z). *)


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
Fixpoint Close_Rec (k z : nat)( T : Prepro ) {struct T} : Prepro := 
match T with
  | Preparallel P Q => Preparallel (Close_Rec k z P) (Close_Rec k z Q)
  | Preoutput x y P => Preoutput (Close_Name k z x) (Close_Name k z y) (Close_Rec k z P) 
  | Prechan_res P => Prechan_res (Close_Rec (S k) z P)
end.


(* *)
Definition Close ( z : nat )( T : Prepro ): Prepro := Close_Rec 0 z T.


(*
Tal como indica Charguéraud, no todo preproceso resulta ser un proceso bien formado, por lo que se necesita distinguir de aquellos que corresponden con procesos (en el sentido de la definición 2.3) de aquellos que no tienen 'sentido'.
Nuevamente, se parte de la definición para nombres y posteriormente para preprocesos.
*)
Inductive Process_Name : Name -> Prop := 
  | Process_FName : forall (x : nat), Process_Name (FName x).

Inductive Process : Prepro -> Prop :=
  | Parallel : forall P Q : Prepro, 
    Process P -> Process Q -> Process (P ↓ Q)
    
  | Output : forall (x y : Name ) (P : Prepro),
    Process_Name x -> Process_Name y -> Process P -> Process ( x «y»· P)
  
   
  | Chan_res : forall (P : Prepro),
    (forall (x : nat), Process ({ 0 ~> x }P)) -> Process (ν P).
Hint Constructors Process : core.
Check Process_ind.



(*
Concepto de Body, presente en el artículo de Charguéraud. Es el concepto clave para determinar los procesos bien formados bajo la presencia de una variable ligada.
Intuitivamente una expresión es un body si al tomar una variable libre y remplazar la ocurrencia de la primera ligada, es un término bien formado. Es decir, solo aparece un nombre ligado que no tiene ligadura. 
*)
(* Inductive Body : Prepro -> Prop := 
  | is_body : forall (P : Prepro), 
    ( forall L : FVarsE, Finite _ L -> forall (x : nat), ~( x ∈ L ) -> Process ({ 0 ~> x }P) ) -> Body(P).
Check Body_ind. *)


Inductive Process_Name_At : Name -> nat -> Prop := 
  | Process_FName_At : forall ( k x : nat), Process_Name_At (FName x) k
  | Process_BName_At : forall ( k i : nat), ( i < k ) -> Process_Name_At (BName i) k.

Inductive Process_At (k : nat) : Prepro -> Prop :=
    
  | Parallel_At : forall ( P Q : Prepro ),
    Process_At k P -> Process_At k Q -> Process_At k (P ↓ Q)
    
  | Output_At : forall ( x y : Name )( P : Prepro ),
    Process_Name_At x k -> Process_Name_At y k -> Process_At k P -> Process_At k ( x «y»· P)

  | Chan_res_At : forall ( P : Prepro ),
     Process_At (S k) P -> Process_At k (ν P).

Check Process_At_ind.

Lemma Exchange_Open : 
forall (P : Prepro)(i j x y : nat),
i <> j -> ({i ~> x}({j ~> y} P) = {j ~> y}({i ~> x}P)).
Proof. 
  induction P.
  + intros.
    simpl.
    admit.
  + intros.
    simpl.
    admit.
  + intros.
    simpl.
    rewrite (IHP (S i) (S j) x y). 
    auto.
    lia.
Admitted.

Fixpoint MOpen_Rec (k : nat)(L : list nat)( T : Prepro ) : Prepro := 
match L , k with
  | nil , _  => T
  | x :: L0, 0 =>  { 0 ~> x } (MOpen_Rec 0 L0 T)
  | x :: L0, S t =>  { t ~> x } (MOpen_Rec t L0 T)
end.

Fixpoint M2Open_Rec (k : nat)(L : list nat)( T : Prepro ) : Prepro := 
match L , k with
  | nil , _  => T
  | x :: L0, 0 =>  { 0 ~> x } (M2Open_Rec 0 L0 T)
  | x :: L0, S t =>  { S t ~> x } (M2Open_Rec t L0 T)
end.

Lemma MOpen_M2Open_Rest :
forall (k : nat)(L : list nat)(P : Prepro), 
(length L) = k -> 
MOpen_Rec k L (ν P) = (ν M2Open_Rec k L P).
Proof.
  induction k.
  + intros.
    simpl.
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    simpl.
    assert (HA : (exists (x : nat)(L0 : list nat), L = x :: L0)).
    - admit.
    - destruct HA as [x [L0 HA]].
      rewrite HA.
      simpl.
      rewrite IHk.
      auto.
      admit.
Admitted.


Lemma MOpen_Parallel : 
forall (k : nat)(L : list nat)( P Q : Prepro),
(length L) = k ->
MOpen_Rec k L (P ↓ Q) = (MOpen_Rec k L P) ↓ (MOpen_Rec k L Q).
Proof.
  induction k.
  + intros.
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    assert (HA : (exists (x : nat)(L0 : list nat), L = x :: L0)).
    - admit.
    - destruct HA as [x [L0 HA]].
      rewrite HA.
      simpl.
      rewrite IHk.
      auto.
      admit.
Admitted.

Lemma M2Open_MOpen :
forall (k x : nat)(L : list nat)(P : Prepro),
(length L) = k -> 
({0 ~> x} M2Open_Rec k L P) = MOpen_Rec (S k) (L ++ (x :: nil)) P.
Proof.
  induction k.
  + intros. 
    rewrite length_zero_iff_nil in H.
    rewrite H.
    auto.
  + intros.
    assert (HA : (exists (x : nat)(L0 : list nat), L = x :: L0)).
    - admit.
    - destruct HA as [y [L0 HA]].
      rewrite HA.
      simpl.
      rewrite <- IHk.
      rewrite Exchange_Open; auto.
      admit.
Admitted.


Theorem ProcessAt_Process_MOpen : 
forall (P : Prepro)(k : nat)(L : list nat),
(length L) = k -> 
Process_At k P -> Process (MOpen_Rec k L P).
Proof.
  induction P.
  + intros.
    rewrite MOpen_Parallel; auto.
    inversions H0.
    constructor; apply IHP1 || apply IHP2; auto.
  + intros. admit.
  + intros.
    rewrite MOpen_M2Open_Rest; auto.
    constructor.
    inversions H0.
    intros.
    rewrite M2Open_MOpen; auto.
    apply IHP; auto.
    admit.
Admitted.





Theorem ProcessAt_Process :
forall ( P : Prepro ),
Process_At 0 P -> Process P.
Proof.
  intros.
  induction P.
  + admit.
  + admit.
  + inversion H; subst.
    constructor.
    intros.
    
Admitted.




























Lemma MOpen_Rest_Aux : 
forall (k x : nat)( P : Prepro),
Open_Recx k x (ν P) = ν (DMOpen_Rec (S k) x P).
Proof.
  induction k.
  + auto.
  + intros. simpl. 

Admitted.


Lemma MOpen_Rest_Aux2 : 
forall (k x : nat)(P : Prepro), 
({0 ~> x} DMOpen_Rec (S (S k)) x P) = (Open_Recx (S (S k)) x P).
Proof.
Admitted.


Lemma MOpen_Rest : 
forall (k x : nat)(P : Prepro), 
Process (Open_Recx (S k) x P ) -> Process (Open_Recx k x (ν P)).
Proof.
  induction k.
  + intros.
    simpl in H.
    simpl.
    constructor.
    intros.
    admit.
  + intros.
    rewrite MOpen_Rest_Aux.
    constructor.
    intros.
    apply (Chan_res (DMOpen_Rec (S (S k)) x P) x).
    rewrite MOpen_Rest_Aux2.
    auto.
Qed.

Lemma Process_Change_Open_Var : 
forall (P : Prepro)(x y : nat), 
Process ( {0 ~> x}P ) ->  Process( {0 ~> y} P).
Proof.
  induction P; intros.
  + intros. 
    simpl in H; inversion H; subst.
    simpl. constructor; admit.
  + admit.
  + inversion H; subst.
    simpl.
    constructor.
    intros.
  
Admitted.




















