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



From old Require Import Defs_Tactics.

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


Inductive Well_Subst_Close : Process -> nat -> nat -> nat -> Prop :=
 | Is_Well_Subst_Close : forall ( P : Process)(x y z: nat),
    ~( y ∈ (FVars P) ) -> x <> y -> y <> z-> 
    (Well_Subst_Close P x y z).

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

  (*  | Con_con_res : forall (P Q : Process)(x : nat), 
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
    (Q --> R) -> ((P ↓ Q ) --> (P ↓ R))

  | Red_reduction_chanres : forall (P Q : Process)( x : nat),
    lc P -> lc Q ->
    ( P --> Q ) -> ( ν Close x P --> ν Close x Q )

   | Red_reduction_struct : forall ( P Q P' Q' : Process ),
    lc P' -> ( P' === P ) -> ( Q' === Q ) ->
    (P' --> Q') -> (P --> Q) 
where "R '-->' S" := (Reduction R S).
Check Reduction_ind.




From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Bool.Bool.
From Coq Require Import Lia.


(*
*)
Lemma Open_Name_BName_Eq : 
forall (k i x : nat),
k = i -> 
Open_Name k x (BName i) = FName x.
Proof.
  intros.
  inversion H.
  simpl.
  destruct (bool_dec (i =? i) true).
  + rewrite e. auto.
  + apply not_true_iff_false in n.
    apply beq_nat_false in n; contradiction.
Qed.


(*
*)
Lemma Open_Name_BName_Gt : 
forall (k i x : nat),
k < i -> 
Open_Name k x (BName i) = BName i.
Proof.
  intros.
  destruct (bool_dec (k =? i) true); simpl.
  + apply beq_nat_true in e. lia.
  + apply not_true_iff_false in n.
    rewrite n.
    auto.
Qed.



(*
Siempre que se hace una sustitución sobre nombres solo se pueden obtener dos resultados, se remplaza o queda igual.
*)
Lemma Subst_Name_Output :
forall ( x y : nat )( z : Name ),
lc_name z -> ((Subst_Name x y z = (FName y)) \/ (Subst_Name x y z = z)).
Proof.
  intros.
  inversions H.
  simpl. 
  destruct (bool_dec (x0 =? x) true).
  + rewrite e. auto.
  + apply not_true_iff_false in n.
    rewrite n. auto.
Qed.


(*
Análogamente, al cerrar un nombre solo hay dos opciones, se remplazar o queda igual.
*)
Lemma Close_Name_Output : 
forall ( i x : nat) ( y : Name), 
lc_name y -> ( (Close_Name i x y = y) \/ (Close_Name i x y = BName i) ).
Proof.
  intros.
  inversion H.
  simpl.
  destruct (bool_dec (x0 =? x) true).
  + rewrite e. auto.
  + apply not_true_iff_false in n.
    rewrite n. auto.
Qed.


(*
*)
Lemma Open_BName_Output :
forall ( k x p : nat),
Open_Name k x (BName p) = BName p \/ Open_Name k x (BName p) = FName x.
Proof.
  intros.
  simpl.
  destruct (bool_dec (k =? p) true).
  - rewrite e; auto.
  - apply not_true_iff_false in n.
    rewrite n; auto.
Qed.


(*
*)
Lemma Output_LCName_Output :
forall ( p : Name )( k x : nat ),
lc_name p -> Open_Name k x p = p.
Proof.
  intros.
  inversions H.
  auto.
Qed.


(*
*)
Lemma Open_BName_IsFName_Eq :
forall ( k x p : nat),
Open_Name k x (BName p) = FName x -> k = p.
Proof.
  intros.
  destruct (bool_dec (k =? p) true).
  + apply beq_nat_true; auto.
  + apply not_true_iff_false in n.
    simpl in H.
    rewrite n in H.
    discriminate.
Qed.


(*
*)
Lemma Open_BName_IsBName_Eq :
forall ( k x p : nat),
Open_Name k x (BName p) = BName p -> k <> p.
Proof.
  intros.
  destruct (bool_dec (k =? p) true).
  + simpl in H.
    rewrite e in H.
    discriminate.
  + apply not_true_iff_false in n.
    apply beq_nat_false; auto.
Qed.


(*
*)
Lemma Eq_Open_Name :
forall ( i y k x p : nat),
i <> k -> 
Open_Name i y (Open_Name k x (BName p)) = Open_Name k x (Open_Name i y (BName p)).
Proof.
  intros.
  specialize ( Open_BName_Output k x p) as HA.
  specialize ( Open_BName_Output i y p) as HB.
  destruct HA.
  + destruct HB.
    - congruence.
    - rewrite ?H0; rewrite ?H1.
      auto.
 + destruct HB.
  - rewrite H1; rewrite H0.
    auto.
  - apply Open_BName_IsFName_Eq in H0.
    apply Open_BName_IsFName_Eq in H1.
    lia.
Qed.


(*
*)
Lemma Subst_BName_Output :
forall ( x y i : nat ),
Subst_Name x y (BName i) = BName i.
Proof.
  intros.
  simpl.
  auto.
Qed.


(*
*)
Lemma Subst_Name_Open_Name_Ex : 
forall ( x : Name )( x0 y0 z w k: nat ),
FName w = Subst_Name x0 y0 (FName z) -> 
Subst_Name x0 y0 (Open_Name k z x) = Open_Name k w (Subst_Name x0 y0 x).
Proof.
  intros.
  destruct x.
  + simpl.
    destruct (bool_dec (x =? x0) true).
    - rewrite e. auto.
    - apply not_true_iff_false in n.
      rewrite n. auto.
  + specialize ( Open_BName_Output k z i ) as HA.
    destruct HA.
    - rewrite Subst_BName_Output.
      rewrite H0.
      specialize ( Open_BName_Output k w i ) as HB.
      destruct HB.
      * rewrite H1; auto.
      * apply Open_BName_IsFName_Eq in H1.
        apply Open_BName_IsBName_Eq in H0.
        contradiction.
    - rewrite Subst_BName_Output.
      rewrite H0.
      specialize ( Open_BName_Output k w i ) as HB.
      destruct HB.
      * apply Open_BName_IsFName_Eq in H0.
        apply Open_BName_IsBName_Eq in H1.
        contradiction.
      * rewrite H1.
        rewrite H.
        auto.
Qed.


(*
*)
Lemma Open_Close_FName : 
forall ( x y : nat ),
(Open_Name 0 x (Close_Name 0 y (FName y))) = (FName x).
Proof.
  intros.
  destruct (bool_dec (y =? y) true).
  + simpl. rewrite e; auto.
  + apply not_true_iff_false in n.
    apply beq_nat_false in n.
    contradiction.
Qed.


(*
*)
Lemma Subst_Name_By_Equal :
forall ( x0 : nat )( x : Name ),
Subst_Name x0 x0 x = x.
Proof.
  intros.
  destruct x.
  + simpl.
    destruct (bool_dec (x =? x0) true).
    - rewrite e.
      apply beq_nat_true in e.
      auto.
    - apply not_true_iff_false in n.
      rewrite n.
      auto.
  + auto.
Qed.

(*
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
Resultados generales relacionadas con las operaciones sobre nombres a nivel k
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
*)


(*
*)
Lemma Lc_Lca_Zero_Name :
forall ( x : Name ),
lc_name x -> lca_name 0 x.
Proof.
  intros.
  inversions H.
  constructor.
Qed.


(*
*)
Lemma Lca_Zero_Lc_Name :
forall ( x : Name ),
lca_name 0 x -> lc_name x.
Proof.
  intros.
  destruct x.
  + constructor.
  + inversions H.
    lia.
Qed.


(*
*)
Lemma Lca_Name_Open :
forall (x : Name)(i : nat),
(forall (x0 : nat), lca_name i (Open_Name i x0 x)) -> lca_name (S i) x.
Proof.
  intros.
  destruct x.
  - constructor.
  - simpl in H.
    destruct (bool_dec (i =? i0) true).
    rewrite e in H.
    * constructor.
      apply beq_nat_true in e.
      lia.
    * apply not_true_iff_false in n.
      rewrite n in H.
      specialize (H i).
      inversions H.
      constructor.
      auto.
Qed.


(*
*)
Lemma Lca_Name_Rd :
forall ( x : Name )( k y : nat ),
lca_name (S k) x -> lca_name k (Open_Name k y x).
Proof.
  intros.
  inversions H.
  - simpl. constructor.
  - assert ( HI : i = k \/ i < k ). { lia. }
    destruct HI.
    * simpl. 
      assert ( HI : k =? i = true ).
        { destruct (bool_dec (k =? i) true).
          + auto.
          + apply not_true_iff_false in n.
            apply beq_nat_false in n; auto.
        } 
      rewrite HI.
      constructor.
    * assert ( HI : k =? i = false ).
      { destruct (bool_dec (k =? i) true).
          + apply beq_nat_true in e. lia.
          + apply not_true_iff_false in n.
            auto.
        }
      simpl.
      rewrite HI. 
      constructor; auto.
Qed.


(*
*)
Lemma Lca_Name_Close :
forall ( x : Name )( k y : nat ),
lca_name k x -> lca_name (S k) (Close_Name k y x).
Proof.
  intros.
  inversions H.
  + destruct (bool_dec (x0 =? y) true).
    - simpl. rewrite e.
      constructor. auto.
    - apply not_true_iff_false in n.
      simpl. rewrite n.
      constructor.
  + simpl. constructor; auto.
Qed.


(*
*)
Lemma Subst_Lca_Name :
forall ( x : Name )( k x0 y0 : nat),
lca_name k x -> lca_name k (Subst_Name x0 y0 x).
Proof.
  intros.
  inversions H.
  + specialize ( Subst_Name_Output x0 y0 (FName x1)) as HS.
    destruct HS; try rewrite H0; constructor.
  + constructor; auto.
Qed.



Lemma Lca_Name_Bex : 
forall (N : Name)( i j k : nat),
i < j -> j < k -> lca_name k N ->
lca_name k (Bex_Name i j N).
Proof.
  intros.
  destruct N.
  + constructor.
  + inversions H1.
    destruct (bool_dec (i0 =? i) true).
    - simpl. rewrite e.
      constructor. auto.
    - apply not_true_iff_false in n.
      simpl. rewrite n.
      destruct (bool_dec (i0 =? j) true).
      * simpl. rewrite e.
        constructor. lia.
      * apply not_true_iff_false in n0.
        simpl. rewrite n0.
        constructor. auto.
Qed.



From Coq Require Import Ensembles.
From Coq Require Import Finite_sets.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.

(*
*)
Lemma No_Union_No_Each : 
forall (x : nat)( X Y : FVarsE ),
~(x ∈ (X ∪ Y)) -> ~(x ∈ X) /\ ~(x ∈ Y).
Proof.
Admitted.


(*
*)
Lemma FVars_Name_Finite :
forall (x : Name),
Finite _ (FVars_Name x).
Proof.
  destruct x.
  + simpl. apply Singleton_is_finite.
  + simpl. constructor.
Qed.


(*
*)
Lemma FVars_Finite :
forall (P : Process),
Finite _ (FVars P).
Proof.
  induction P.
  + simpl.
    constructor.
  + simpl. apply Union_preserves_Finite; apply FVars_Name_Finite.
  + simpl. apply Union_preserves_Finite; auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + simpl. apply FVars_Name_Finite.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
Qed.


(*
*)
Lemma There_Is_A_Name :
forall ( P : Process ),
exists ( x : nat ), ~ ( x ∈ (FVars P) ).
Proof.
Admitted.


(*
*)
Lemma FVars_Name_No_Close :
forall (z k : nat)(x : Name),
~ (z ∈ FVars_Name x) -> (Close_Name k z x = x).
Proof.
  unfold not.
  intros.
  destruct x.
  + destruct (bool_dec (x =? z) true).
    - simpl in H. apply Nat.eqb_eq in e.
      rewrite e in H.
      assert ( HB : z ∈ Singleton nat z).
      { unfold In. constructor. }
      contradiction.
    - simpl. apply not_true_iff_false in n.
      rewrite n. auto.
  + auto.
Qed.


(*
*)
Lemma Close_NoFVar_Eq :
forall ( P : Process )(z k: nat),
~ ( z ∈ (FVars P) ) -> ( Close_Rec k z P ) = P.
Proof.
  unfold Close.
  induction P; intros.
  + auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP1; auto.
    rewrite IHP2; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [H HC].
    simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP; auto.
    rewrite FVars_Name_No_Close; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    simpl.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    simpl.
    rewrite IHP; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite IHP; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite IHP; auto.
Qed.















