(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López 
  Proyecto 1. Session Type Systems Verification
*)
From PROYI Require Import Defs_Process.
From PROYI Require Import Facts_Process.
From Coq Require Import Bool.Bool.








(*
*)
Lemma Open_Process_Process :
forall ( P : Prepro ), Process P -> 
forall ( k x : nat ), Process ( {k ~> x}P ).
Proof.
  intros P H.
  induction H; intros; simpl.
  + auto.
  + rewrite Output_PName_Output; auto.
    rewrite Output_PName_Output; auto.
  + constructor.
    apply IHProcess1.
    apply IHProcess2.
  + rewrite Output_PName_Output; auto.
    rewrite Output_PName_Output; auto.
  + rewrite Output_PName_Output; auto.
  + rewrite Output_PName_Output; auto.
  + simpl.
    isBody.
    specialize (H0 L H1 x0 H2 (S k) x).
    rewrite Exchange_Open_Sk_i; auto.
  + simpl.
    isBody.
    - rewrite Output_PName_Output; auto.
    - specialize (H1 L H2 x1 H3 (S k) x0).
      rewrite Exchange_Open_Sk_i; auto.
  + simpl.
    isBody.
    - rewrite Output_PName_Output; auto.
    - specialize (H1 L H2 x1 H3 (S k) x0).
      rewrite Exchange_Open_Sk_i; auto.
Qed.


(*
*)
Lemma All_Process_Body :
forall (P : Prepro),
Process P -> Body P.
Proof.
  intros.
  constructor.
  intros.
  apply Open_Process_Process; auto.
Qed.


(*
*)
Lemma Close_Process_At :
forall ( P : Prepro )(x k: nat),
Process_At k P -> Process_At (S k) (Close_Rec k x P).
Proof.
  intro.
  induction P; intros; simpl; try inversions H; constructor; try apply Process_NameAt_Close_Name; auto.
Qed.


(*
*)
Lemma Close_Is_Body :
forall ( P : Prepro )(x : nat),
Process P -> Body (Close_Rec 0 x P).
Proof.
  intros.
  apply Process_ProcessAt in H.
  apply (Close_Process_At _ x _)  in H.
  apply ProcessAt_One_Body in H.
  auto.
Qed.


(*
*)
Lemma Subst_Body_Body :
forall (P : Prepro),
Body P -> forall (x y : nat), Body ({y \ x} P).
Proof.
  intros.
  apply Body_ProcessAt_One in H.
  apply ProcessAt_One_Body.
  apply Subst_Process_At.
  auto.
Qed.


(*
*)
Lemma Subst_Process_Process :
forall (P : Prepro)(x y : nat),
Process P -> Process ({y \ x} P).
Proof.
  intros.
  induction H.
  + auto.
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

(*
Primer teorema fuerte, la representación local libre de nombres preserva sentido bajo congruencias.
*)
Theorem Congruence_WD :
forall P Q : Prepro, 
(P === Q) -> Process(P)  -> Process(Q).
Proof.
  intros.
  inversions H; inversions H0; auto.
  constructor.
  intros.
  simpl.
  constructor.
  + apply (Open_Process_Process); auto.
  + inversion H6.
    apply (H8 L); auto.
Qed.


(*
Resultado fundamental para la representación LNR, al hacer una redución de un proceso se obtiene un proceso.
*)
Theorem ProcessReduction_WD : 
forall P Q : Prepro, 
(P --> Q) -> Process(P)  -> Process(Q).
Proof.
  intros.
  induction H.
  + constructor; auto.
    inversions H1.
    inversions H2.
    specialize (FVars_Finite Q) as HF.
    apply (H3 (FVars Q)); auto.
  + inversions H0.
    inversions H5.
    inversions H6.
    inversions H2.
    specialize (FVars_Finite Q) as HF.
    constructor; auto.
    constructor; auto.
    apply (H11 (FVars Q)); auto.
  + inversions H1; auto.
  + apply Subst_Process_Process; auto.
  + inversions H0.
    constructor; auto.
  + unfold Close in *.
    apply (Close_Is_Body _ x) in H1.
    inversions H1.
    constructor; auto.
(*   + apply IHReduction in H.
    specialize (Congruence_WD Q' Q) as HQ.
    specialize (HQ H2 H).
    auto. *)
Qed.




