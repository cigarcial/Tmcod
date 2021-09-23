(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López 
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.


From Tmcod Require Import Defs_Process.
From Tmcod Require Import Defs_Tactics.
From Tmcod Require Import Facts_Process.
From Tmcod Require Import Facts_MOpen.
From Tmcod Require Import Facts_Names.


(*
*)
Theorem Process_ProcessAt :
forall ( P : Process ), 
lc P -> lca 0 P.
Proof.
  intros.
  induction H;
   constructor;
    try apply Lc_Lca_Zero_Name;
    try apply (Process_Lca_Open_S _  _ ); auto.
Qed.


(*
*)
Theorem ProcessAt_Process :
forall ( P : Process ),
lca 0 P -> lc P.
Proof.
  intros.
  induction P; try inversions H;
    try constructor;
    try apply Lca_Zero_Lc_Name;
    try apply IHP1 || apply IHP2;
    try intros;
    try specialize (Lca_Lc_Process_MOpen P 1 [x]) as HB;
    try specialize (Lca_Lc_Process_MOpen P 1 [x0]) as HB;
    try simpl in HB;
    try apply HB; auto.
Qed.


(*
*)
Lemma Body_Lc_One :
forall ( P : Process ),
Body P -> lca 1 P.
Proof.
  intros.
  apply Body_Process_Equivalence_Res in H.
  apply Process_ProcessAt in H.
  inversions H.
  auto.
Qed.


(*
*)
Lemma Lca_One_Body :
forall ( P : Process ),
lca 1 P -> Body P.
Proof.
  intros.
  apply Body_Process_Equivalence_Res.
  apply ProcessAt_Process.
  constructor.
  auto.
Qed.


(*
*)
Lemma Lc_Open_Close_Subst :
forall ( P : Process )( x y k : nat ), 
lc P -> { 0 ~> y } Close_Rec 0 x P = { y \ x } P.
Proof.
  intros.
  apply Lca_Open_Close_Subst.
  apply Process_ProcessAt; auto.
Qed.



(*
*)
Lemma Open_Lc_Lc :
forall ( P : Process ), lc P -> 
forall ( k x : nat ), lc ( {k ~> x}P ).
Proof.
  intros P H.
  induction H; intros; simpl.
  + Piauto.
  + rewrite Output_LCName_Output; Piauto.
    rewrite Output_LCName_Output; Piauto.
  + constructor.
    apply IHlc1.
    apply IHlc2.
  + rewrite Output_LCName_Output; auto.
    rewrite Output_LCName_Output; Piauto.
  + rewrite Output_LCName_Output; Piauto.
  + rewrite Output_LCName_Output; Piauto.
  + constructor.
    intros.
    rewrite Exchange_Open; auto.
  + constructor.
    rewrite Output_LCName_Output; auto.
    intros.
    rewrite Exchange_Open; auto.
  + constructor.
    rewrite Output_LCName_Output; auto.
    intros.
    rewrite Exchange_Open; auto.
Qed.


(*
*)
Lemma All_Lc_Body :
forall (P : Process),
lc P -> Body P.
Proof.
  intros.
  constructor.
  intros.
  apply Open_Lc_Lc; auto.
Qed.


(*
*)
Lemma Close_Lca :
forall ( P : Process )(x k: nat),
lca k P -> lca (S k) (Close_Rec k x P).
Proof.
  intro.
  induction P; intros; simpl; try inversions H; constructor; 
  try apply Lca_Name_Close; auto.
Qed.


(*
*)
Lemma Lc_Close_Body :
forall ( P : Process )(x : nat),
lc P -> Body (Close_Rec 0 x P).
Proof.
  intros.
  apply Process_ProcessAt in H.
  apply (Close_Lca _ x _)  in H.
  apply Lca_One_Body in H.
  auto.
Qed.

(*
*)
Lemma Lc_Close_Is_Body :
forall ( P : Process )(x : nat),
lc P -> ( forall (y : nat), lc ( (Close_Rec 0 x P) ^ y)).
Proof.
  intros.
  apply (Lc_Close_Body P x) in H.
  inversions H.
  apply H0.
Qed.


(*
*)
Lemma Subst_Body_Body :
forall (P : Process),
Body P -> forall (x y : nat), Body ({y \ x} P).
Proof.
  intros.
  apply Body_Lc_One in H.
  apply Lca_One_Body.
  apply Subst_Lca_Process.
  auto.
Qed.


(*
*)
Lemma Subst_Lc_Lc :
forall (P : Process)(x y : nat),
lc P -> lc ({y \ x} P).
Proof.
  intros.
  induction H.
  + Piauto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    specialize (Subst_Name_Output x y y0) as HB.
    destruct HA;
      destruct HB;
        try rewrite H1;
        try rewrite H2;
        try constructor; try constructor; auto.
  + simpl.
    constructor; auto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    specialize (Subst_Name_Output x y y0) as HB.
    destruct HA;
      destruct HB;
        try rewrite H2;
        try rewrite H3;
        try constructor; try constructor; auto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    destruct HA; 
      try rewrite H0;
      try constructor; try constructor; auto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    destruct HA; 
      try rewrite H1;
      try constructor; try constructor; auto.
  + specialize ( Subst_Body_Body P) as HP.
    simpl.
    assert ( HB : Body P ). constructor; auto.
    specialize ( HP HB x y ).
    inversion HP.
    constructor; auto.
  + specialize ( Subst_Body_Body P) as HP.
    simpl.
    assert ( HB : Body P ). constructor; auto.
    specialize ( HP HB x y ).
    inversion HP.
    constructor.
    - specialize (Subst_Name_Output x y x0) as HA.
        destruct HA;
          try rewrite H4;
          try constructor; try constructor; auto.
    - auto.
  + specialize ( Subst_Body_Body P) as HP.
    simpl.
    assert ( HB : Body P ). constructor; auto.
    specialize ( HP HB x y ).
    inversion HP.
    constructor.
    - specialize (Subst_Name_Output x y x0) as HA.
        destruct HA;
          try rewrite H4;
          try constructor; try constructor; auto.
    - auto.
Qed.




(*
*)
Lemma Cong_Subst_Cong :
forall (P Q : Process)( x u : nat),
P === Q -> ({u \ x}P) === ({u \ x}Q).
Proof.
  intros.
  induction H; try simpl; Piauto.
  + simpl.
    rewrite Subst_Bex_Exchange; Piauto.
  + constructor.
    apply Subst_Lc_Lc.
    auto.
Qed.





(*
Primer teorema fuerte, la representación local libre de nombres preserva sentido bajo congruencias.
*)
Theorem Congruence_WD :
forall P Q : Process, 
(P === Q) -> lc(P)  -> lc(Q).
Proof.
  intros.
  induction H; inversions H0; Piauto.
  + apply ProcessAt_Process.
    do 2 constructor.
    apply Process_ProcessAt in H0.
    inversions H0.
    inversions H3.
    apply Lca_Bex; auto.
  + inversions H2; Piauto.
  + constructor. simpl.
    constructor.
    apply Open_Lc_Lc; auto.
    inversions H4.
    apply H2; auto.
Qed.

(*
Resultado fundamental para la representación LNR, al hacer una redución de un proceso se obtiene un proceso.
*)
Theorem ProcessReduction_WD : 
forall P Q : Process, 
(P --> Q) -> lc(P)  -> lc(Q).
Proof.
  intros.
  induction H; try inversions H0; try constructor; auto.
  + inversions H1.
    specialize (H2 y); auto.
  + constructor; auto.
    inversions H1.
    specialize (H2 y); auto.
  + apply Subst_Lc_Lc; auto.
  + apply IHReduction in H.
    apply Lc_Close_Is_Body; auto.
  (* los casos que faltan son aplicaciones del lema anterior *)
Admitted.



