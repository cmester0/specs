(* File automatically generated by Hacspec *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import word_ssrZ word.
(* From Jasmin Require Import word. *)

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

Class t_Field (v_Self : choice_type) := {
  f_q_loc : {fset Location} ;
  f_q : (both 'unit -> both v_Self) ;
  f_random_field_elem_loc : {fset Location} ;
  f_random_field_elem : (both int32 -> both v_Self) ;
  f_field_zero_loc : {fset Location} ;
  f_field_zero : (both 'unit -> both v_Self) ;
  f_field_one_loc : {fset Location} ;
  f_field_one : (both 'unit -> both v_Self) ;
  f_add_loc : {fset Location} ;
  f_add : (both v_Self -> both v_Self -> both v_Self) ;
  f_sub_loc : {fset Location} ;
  f_sub : (both v_Self -> both v_Self -> both v_Self) ;
  f_mul_loc : {fset Location} ;
  f_mul : (both v_Self -> both v_Self -> both v_Self) ;
}.
Hint Unfold f_q_loc.
Hint Unfold f_random_field_elem_loc.
Hint Unfold f_field_zero_loc.
Hint Unfold f_field_one_loc.
Hint Unfold f_add_loc.
Hint Unfold f_sub_loc.
Hint Unfold f_mul_loc.

Class t_Group (v_Self : choice_type) := {
  f_Z : choice_type ;
  f_Z_t_Field :> (t_Field f_Z) ;
  f_Z_t_Serialize :> (t_Serialize f_Z) ;
  f_Z_t_Deserial :> (t_Deserial f_Z) ;
  f_Z_t_Serial :> (t_Serial f_Z) ;
  f_Z_t_Clone :> (t_Clone f_Z) ;
  f_Z_t_Eq :> (t_Eq f_Z) ;
  f_Z_t_PartialEq :> (t_PartialEq f_Z) ;
  f_Z_t_Copy :> (t_Copy f_Z) ;
  f_Z_t_Sized :> (t_Sized f_Z) ;
  f_g_loc : {fset Location} ;
  f_g : (both 'unit -> both v_Self) ;
  f_g_pow_loc : {fset Location} ;
  f_g_pow : (both f_Z -> both v_Self) ;
  f_pow_loc : {fset Location} ;
  f_pow : (both v_Self -> both f_Z -> both v_Self) ;
  f_group_one_loc : {fset Location} ;
  f_group_one : (both 'unit -> both v_Self) ;
  f_prod_loc : {fset Location} ;
  f_prod : (both v_Self -> both v_Self -> both v_Self) ;
  f_inv_loc : {fset Location} ;
  f_inv : (both v_Self -> both v_Self) ;
  f_div_loc : {fset Location} ;
  f_div : (both v_Self -> both v_Self -> both v_Self) ;
  f_hash_loc : {fset Location} ;
  f_hash : (both (t_Vec v_Self t_Global) -> both f_Z) ;
}.
Hint Unfold f_g_loc.
Hint Unfold f_g_pow_loc.
Hint Unfold f_pow_loc.
Hint Unfold f_group_one_loc.
Hint Unfold f_prod_loc.
Hint Unfold f_inv_loc.
Hint Unfold f_div_loc.
Hint Unfold f_hash_loc.
