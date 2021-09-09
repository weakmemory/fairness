(******************************************************************************)
(** * Definition of labels *)
(******************************************************************************)

Require Import FinFun ListDec.
Require Import List.
From hahn Require Import Hahn.
Require Import AuxRel.

Set Implicit Arguments.

Definition Loc := nat.
Definition Val := nat.

(******************************************************************************)
(** ** Labels  *)
(******************************************************************************)

Inductive Lab := 
(*   | Askip  *)
  | Aload  (x:Loc) (v:Val)
  | Astore (x:Loc) (v:Val)
  | Armw   (x:Loc) (vr vw:Val).

Definition loc_l l :=
  match l with
  | Aload  x _
  | Astore x _
  | Armw   x _ _ => x
  end.

Definition valr_l l :=
  match l with
  | Aload  _ v
  | Armw   _ v _ => v
  | _ => 0 
  end.

Definition valw_l l :=
  match l with
  | Astore _ v
  | Armw   _ _ v => v
  | _ => 0 
  end.

Definition is_r_l l := 
  match l with
  | Aload  _ _ => true
  | Armw   _ _ _ => true
  | _ => false
  end.

Definition is_w_l l := 
  match l with
  | Astore  _ _  => true
   | Armw   _ _ _ => true
  | _ => false
  end.

Definition is_rmw_l l := 
  match l with
  | Armw   _ _ _ => true
  | _ => false
  end.
