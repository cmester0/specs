(* File automatically generated by Hacspec *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
From Coq Require Import Strings.String.
   Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.

(*Not implemented yet? todo(item)*)

Require Import Hacspec_lib.

(*Not implemented yet? todo(item)*)

Require Import Schnorr.

Notation t_Secret := (t_Q).

Program Definition sample_uniform : both (fset []) ([interface ]) (t_Q) :=
  Build_t_Q i32(1).
Fail Next Obligation.

Notation t_public := (t_G).

Notation t_public_key := ((t_G × (t_G × t_G × t_Q × t_Q))).

Program Definition p_i_init {L1 : {fset Location}} {I1 : Interface} (_ : both L1 I1 ('unit)) : both (L1 :|: fset [commit_loc]) (I1) ((t_G × (t_G × t_G × t_Q × t_Q))) :=
  letb x := (sample_uniform) : both _ _ (t_Q) in
  letb y := (Build_t_G i32(1)) : both _ _ (t_G) in
  letb zkp := (fiat_shamir_run (prod_b (y,x))) : both _ _ ((t_G × t_G × t_Q × t_Q)) in
  prod_b (y,zkp).
Fail Next Obligation.

Notation t_pid := (t_N).

Require Import Std. (* as HashMap *)

Notation t_public_keys := (t_HashMap (t_N) ((t_G × (t_G × t_G × t_Q × t_Q))) (t_RandomState)).

Program Definition p_i_construct {L1 : {fset Location}} {I1 : Interface} (m : both L1 I1 (t_HashMap (t_N) ((t_G × (t_G × t_G × t_Q × t_Q))) (t_RandomState))) : both (L1) (I1) ('unit) :=
  ret_both (tt : 'unit).
Fail Next Obligation.

Program Definition p_i_vote {L1 : {fset Location}} {I1 : Interface} (v : both L1 I1 ('bool)) : both (L1) (I1) (t_G) :=
  Build_t_G i32(1).
Fail Next Obligation.

Program Definition exec {L1 : {fset Location}} {I1 : Interface} (v : both L1 I1 ('bool)) : both (L1 :|: fset [commit_loc]) (I1) (t_G) :=
  letb x := (sample_uniform) : both _ _ (t_Q) in
  letb y := (Build_t_G i32(1)) : both _ _ (t_G) in
  letb zkp := (fiat_shamir_run (prod_b (y,x))) : both _ _ ((t_G × t_G × t_Q × t_Q)) in
  p_i_vote v.
Fail Next Obligation.
