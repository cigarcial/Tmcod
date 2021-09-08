(*
  Ciro Iván García López
  Tesis de Maestría
  Session Type Systems Verification
  Unam - 2021
*)
(*
  
  This file contains convenient tactics.
  En este archivo se definiran las tácticas que se encuentren convenientes.
*)
Ltac inversions H := inversion H; subst.
Ltac isBody := constructor; intros; simpl; repeat constructor.
