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

Require Import Crate.
Export Crate.

Class t_HasParameter (Self : choice_type) := {
  size_loc : {fset Location} ;
  size : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: size_loc) I1 (int32) ;
}.

Class t_HasChainMetadata (Self : choice_type) := {
  slot_time_loc : {fset Location} ;
  slot_time : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: slot_time_loc) I1 (t_Timestamp) ;
}.

Class t_HasPolicy (Self : choice_type) := {
  identity_provider_loc : {fset Location} ;
  identity_provider : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: identity_provider_loc) I1 (int32) ;
  created_at_loc : {fset Location} ;
  created_at : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: created_at_loc) I1 (t_Timestamp) ;
  valid_to_loc : {fset Location} ;
  valid_to : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: valid_to_loc) I1 (t_Timestamp) ;
  next_item_loc : {fset Location} ;
  next_item : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (nseq int8 31) -> both (L1 :|: L2 :|: next_item_loc) (I1 :|: I2) ((t_Option ((t_AttributeTag × int8)) × nseq int8 31 × Self)) ;
}.

Class t_HasCommonData (Self : choice_type) := {
  t_PolicyType : choice_type ;
  t_PolicyType_t_HasPolicy :> t_HasPolicy (t_PolicyType) ;
  t_PolicyType_t_Sized :> t_Sized (t_PolicyType) ;
  t_MetadataType : choice_type ;
  t_MetadataType_t_HasChainMetadata :> t_HasChainMetadata (t_MetadataType) ;
  t_MetadataType_t_Sized :> t_Sized (t_MetadataType) ;
  t_ParamType : choice_type ;
  t_ParamType_t_Read :> t_Read (t_ParamType) ;
  t_ParamType_t_HasParameter :> t_HasParameter (t_ParamType) ;
  t_ParamType_t_Sized :> t_Sized (t_ParamType) ;
  t_PolicyIteratorType : choice_type ;
  t_PolicyIteratorType_t_ExactSizeIterator :> t_ExactSizeIterator (t_PolicyIteratorType) ;
  t_PolicyIteratorType_t_Iterator :> t_Iterator (t_PolicyIteratorType) ;
  t_PolicyIteratorType_t_Sized :> t_Sized (t_PolicyIteratorType) ;
  policies_loc : {fset Location} ;
  policies : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: policies_loc) I1 (t_PolicyIteratorType) ;
  metadata_loc : {fset Location} ;
  metadata : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: metadata_loc) I1 (t_MetadataType) ;
  parameter_cursor_loc : {fset Location} ;
  parameter_cursor : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: parameter_cursor_loc) I1 (t_ParamType) ;
}.

Class t_HasInitContext (Self : choice_type) := {
  t_InitData : choice_type ;
  t_InitData_t_Sized :> t_Sized (t_InitData) ;
  open_loc : {fset Location} ;
  open : forall {L1 I1}, both L1 I1 (t_InitData) -> both (L1 :|: open_loc) I1 (Self) ;
  init_origin_loc : {fset Location} ;
  init_origin : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: init_origin_loc) I1 (t_AccountAddress) ;
}.

Class t_HasReceiveContext (Self : choice_type) := {
  t_ReceiveData : choice_type ;
  t_ReceiveData_t_Sized :> t_Sized (t_ReceiveData) ;
  open_loc : {fset Location} ;
  open : forall {L1 I1}, both L1 I1 (t_ReceiveData) -> both (L1 :|: open_loc) I1 (Self) ;
  invoker_loc : {fset Location} ;
  invoker : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: invoker_loc) I1 (t_AccountAddress) ;
  self_address_loc : {fset Location} ;
  self_address : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: self_address_loc) I1 (t_ContractAddress) ;
  self_balance_loc : {fset Location} ;
  self_balance : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: self_balance_loc) I1 (t_Amount) ;
  sender_loc : {fset Location} ;
  sender : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: sender_loc) I1 (t_Address) ;
  owner_loc : {fset Location} ;
  owner : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: owner_loc) I1 (t_AccountAddress) ;
}.

Class t_HasContractState (Self : choice_type) := {
  t_ContractStateData : choice_type ;
  t_ContractStateData_t_Sized :> t_Sized (t_ContractStateData) ;
  open_loc : {fset Location} ;
  open : forall {L1 I1}, both L1 I1 (t_ContractStateData) -> both (L1 :|: open_loc) I1 (Self) ;
  size_loc : {fset Location} ;
  size : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: size_loc) I1 (int32) ;
  truncate_loc : {fset Location} ;
  truncate : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (int32) -> both (L1 :|: L2 :|: truncate_loc) (I1 :|: I2) (Self) ;
  reserve_loc : {fset Location} ;
  reserve : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (int32) -> both (L1 :|: L2 :|: reserve_loc) (I1 :|: I2) (('bool × Self)) ;
}.

Class t_HasLogger (Self : choice_type) := {
  init_loc : {fset Location} ;
  init : forall {L1 I1}, both (L1 :|: init_loc) I1 (Self) ;
  log_raw_loc : {fset Location} ;
  log_raw : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (seq int8) -> both (L1 :|: L2 :|: log_raw_loc) (I1 :|: I2) ((t_Result ('unit) (t_LogError) × Self)) ;
  log_loc : {fset Location} ;
  log : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (S) -> both (L1 :|: L2 :|: log_loc) (I1 :|: I2) ((t_Result ('unit) (t_LogError) × Self)) ;
}.

Class t_HasActions (Self : choice_type) := {
  accept_loc : {fset Location} ;
  accept : forall {L1 I1}, both (L1 :|: accept_loc) I1 (Self) ;
  simple_transfer_loc : {fset Location} ;
  simple_transfer : forall {L1 L2 I1 I2}, both L1 I1 (t_AccountAddress) -> both L2 I2 (t_Amount) -> both (L1 :|: L2 :|: simple_transfer_loc) (I1 :|: I2) (Self) ;
  send_raw_loc : {fset Location} ;
  send_raw : forall {L1 L2 L3 L4 I1 I2 I3 I4}, both L1 I1 (t_ContractAddress) -> both L2 I2 (t_ReceiveName) -> both L3 I3 (t_Amount) -> both L4 I4 (seq int8) -> both (L1 :|: L2 :|: L3 :|: L4 :|: send_raw_loc) (I1 :|: I2 :|: I3 :|: I4) (Self) ;
  and_then_loc : {fset Location} ;
  and_then : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (Self) -> both (L1 :|: L2 :|: and_then_loc) (I1 :|: I2) (Self) ;
  or_else_loc : {fset Location} ;
  or_else : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (Self) -> both (L1 :|: L2 :|: or_else_loc) (I1 :|: I2) (Self) ;
}.

Class t_UnwrapAbort (Self : choice_type) := {
  t_Unwrap : choice_type ;
  t_Unwrap_t_Sized :> t_Sized (t_Unwrap) ;
  unwrap_abort_loc : {fset Location} ;
  unwrap_abort : forall {L1 I1}, both L1 I1 (Self) -> both (L1 :|: unwrap_abort_loc) I1 (t_Unwrap) ;
}.

Class t_ExpectReport (Self : choice_type) := {
  t_Unwrap : choice_type ;
  t_Unwrap_t_Sized :> t_Sized (t_Unwrap) ;
  expect_report_loc : {fset Location} ;
  expect_report : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (chString) -> both (L1 :|: L2 :|: expect_report_loc) (I1 :|: I2) (t_Unwrap) ;
}.

Class t_ExpectErrReport (Self : choice_type) := {
  t_Unwrap : choice_type ;
  t_Unwrap_t_Sized :> t_Sized (t_Unwrap) ;
  expect_err_report_loc : {fset Location} ;
  expect_err_report : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (chString) -> both (L1 :|: L2 :|: expect_err_report_loc) (I1 :|: I2) (t_Unwrap) ;
}.

Class t_ExpectNoneReport (Self : choice_type) := {
  expect_none_report_loc : {fset Location} ;
  expect_none_report : forall {L1 L2 I1 I2}, both L1 I1 (Self) -> both L2 I2 (chString) -> both (L1 :|: L2 :|: expect_none_report_loc) (I1 :|: I2) ('unit) ;
}.

Class t_SerialCtx (Self : choice_type) := {
  serial_ctx_loc : {fset Location} ;
  serial_ctx : forall {L1 L2 L3 I1 I2 I3}, both L1 I1 (Self) -> both L2 I2 (t_SizeLength) -> both L3 I3 (W) -> both (L1 :|: L2 :|: L3 :|: serial_ctx_loc) (I1 :|: I2 :|: I3) ((t_Result ('unit) (t_Err) × W)) ;
}.

Class t_DeserialCtx (Self : choice_type) := {
  deserial_ctx_loc : {fset Location} ;
  deserial_ctx : forall {L1 L2 L3 I1 I2 I3}, both L1 I1 (t_SizeLength) -> both L2 I2 ('bool) -> both L3 I3 (R) -> both (L1 :|: L2 :|: L3 :|: deserial_ctx_loc) (I1 :|: I2 :|: I3) ((t_Result (Self) (t_ParseError) × R)) ;
}.