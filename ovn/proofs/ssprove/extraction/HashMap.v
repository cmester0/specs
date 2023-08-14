(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Sumbool.

From mathcomp Require Import fintype.

From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset fmap.

From mathcomp Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith List.
Import ListNotations.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.

Declare Scope hacspec_scope.

Open Scope list_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.

(* Require Import Hacspec_Lib_Comparable. *)

Import choice.Choice.Exports.

Require Import Core.
Export Core.

Require Import Hacspec_lib.
Export Hacspec_lib.

Inductive random_state :=
  t_RandomState.
Definition t_HashMap A B (_ : random_state) := chMap A B.

Equations insert : forall {L1 L2 L3 I1 I2 I3} {A B : choice_type}, both L1 I1 (t_HashMap A B t_RandomState) -> both L2 I2 A -> both L3 I3 B -> both (L1 :|: L2 :|: L3) (I1 :|: I2 :|: I3) (t_Option B × t_HashMap A B t_RandomState) :=
  insert m i v :=
    bind_both m (fun m' =>
    bind_both i (fun i' =>
    bind_both v (fun v' =>
    solve_lift ret_both (
      (Some v', setm m' (chElement_ordType_ce_to_ce A i') v')
                 : chOption B × t_HashMap A B _)))).

Equations get {L1 L2 I1 I2} {A B} (m : both L1 I1 (t_HashMap A B t_RandomState)) (i : both L2 I2 A) : both (L1 :|: L2) (I1 :|: I2) (t_Option B) :=
  get m i :=
    bind_both m (fun m' =>
    bind_both i (fun i' =>
    solve_lift ret_both (getm m' (chElement_ordType_ce_to_ce A i') : chOption B))).

Equations new {L I A B} : both L I (t_HashMap A B t_RandomState) :=
  new := (solve_lift ret_both emptym). (* (fmap (s:=[]) _ : chMap _ _) *)
