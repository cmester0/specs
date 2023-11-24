(* File automatically generated by Hacspec *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import word_ssrZ word.
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

(*Not implemented yet? todo(item)*)

Class t_Group (Self : choice_type) := {
  f_group_type : choice_type ;
  f_group_type_t_Serialize :> t_Serialize (f_group_type) ;
  f_group_type_t_Deserial :> t_Deserial (f_group_type) ;
  f_group_type_t_Serial :> t_Serial (f_group_type) ;
  f_group_type_t_Copy :> t_Copy (f_group_type) ;
  f_group_type_t_Clone :> t_Clone (f_group_type) ;
  f_group_type_t_Eq :> t_Eq (f_group_type) ;
  f_group_type_t_PartialEq :> t_PartialEq (f_group_type) ;
  f_group_type_t_Sized :> t_Sized (f_group_type) ;
  q : both (fset[]) (fset[]) (int32) ;
  g : both (fset[]) (fset[]) (f_group_type) ;
  f_g_pow_loc : {fset Location} ;
  f_g_pow : forall {L1 I1}, both L1 I1 (int32) -> both (L1 :|: f_g_pow_loc) I1 (f_group_type) ;
  f_pow_loc : {fset Location} ;
  f_pow : forall {L1 L2 I1 I2}, both L1 I1 (f_group_type) -> both L2 I2 (int32) -> both (L1 :|: L2 :|: f_pow_loc) (I1 :|: I2) (f_group_type) ;
  f_one_loc : {fset Location} ;
  f_one : forall {L1 I1}, both (L1 :|: f_one_loc) I1 (f_group_type) ;
  f_prod_loc : {fset Location} ;
  f_prod : forall {L1 L2 I1 I2}, both L1 I1 (f_group_type) -> both L2 I2 (f_group_type) -> both (L1 :|: L2 :|: f_prod_loc) (I1 :|: I2) (f_group_type) ;
  f_inv_loc : {fset Location} ;
  f_inv : forall {L1 I1}, both L1 I1 (f_group_type) -> both (L1 :|: f_inv_loc) I1 (f_group_type) ;
  f_div_loc : {fset Location} ;
  f_div : forall {L1 L2 I1 I2}, both L1 I1 (f_group_type) -> both L2 I2 (f_group_type) -> both (L1 :|: L2 :|: f_div_loc) (I1 :|: I2) (f_group_type) ;
}.
Hint Unfold f_g_pow_loc.
Hint Unfold f_pow_loc.
Hint Unfold f_one_loc.
Hint Unfold f_prod_loc.
Hint Unfold f_inv_loc.
Hint Unfold f_div_loc.

Definition t_z_17_ : choice_type :=
  'unit.
Equations Build_t_z_17_ : both (fset []) (fset []) (t_z_17_) :=
  Build_t_z_17_  :=
    solve_lift (ret_both ((_) : (t_z_17_))) : both (fset []) (fset []) (t_z_17_).
Fail Next Obligation.

Definition res_loc : Location :=
  (int32 ; 0%nat).

Notation f_into_iter := into_iter.

#[global] Program Instance t_z_17__t_Group : t_Group t_z_17_ :=
  let f_group_type := int32 : choice_type in
  let q := ret_both (17 : int32) : both (fset []) (fset []) (int32) in
  let g := ret_both (3 : int32) : both (fset []) (fset []) (int32) in
  let f_g_pow := fun  {L1 : {fset Location}} {I1 : Interface} (x : both L1 I1 (int32)) => solve_lift ((g .^ x) .% q) : both (L1 :|: fset []) I1 (int32) in
  let f_pow := fun  {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (g : both L1 I1 (int32)) (x : both L2 I2 (int32)) => solve_lift ((g .^ x) .% q) : both (L1 :|: L2 :|: fset []) (I1 :|: I2) (int32) in
  let f_one := fun  {L : {fset Location}} {I : Interface} => solve_lift (ret_both (1 : int32)) : both (L :|: fset []) I (int32) in
  let f_prod := fun  {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (x : both L1 I1 (int32)) (y : both L2 I2 (int32)) => solve_lift ((x .* y) .% q) : both (L1 :|: L2 :|: fset []) (I1 :|: I2) (int32) in
  let f_inv := fun  {L1 : {fset Location}} {I1 : Interface} (x : both L1 I1 (int32)) => letb res loc(res_loc) := ret_both (0 : int32) in
  letb res := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (1 : int32)) (f_end := q))) (fun i =>
    ssp (fun res =>
      letb ii_computation := i in
      solve_lift (ifb (f_g_pow i) =.? x
      then letb res := ii_computation in
        res
      else res) : both (*2*)(L1:|:fset [res_loc;res_loc]) (I1) (int32))) res in
  solve_lift res : both (L1 :|: fset [res_loc]) I1 (int32) in
  let f_div := fun  {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (x : both L1 I1 (int32)) (y : both L2 I2 (int32)) => solve_lift (f_prod x (f_inv y)) : both (L1 :|: L2 :|: fset [res_loc]) (I1 :|: I2) (int32) in
  {| f_group_type := (@f_group_type);
  q := (@q);
  g := (@g);
  f_g_pow_loc := (fset [] : {fset Location});
  f_g_pow := (@f_g_pow);
  f_pow_loc := (fset [] : {fset Location});
  f_pow := (@f_pow);
  f_one_loc := (fset [] : {fset Location});
  f_one := (@f_one);
  f_prod_loc := (fset [] : {fset Location});
  f_prod := (@f_prod);
  f_inv_loc := (fset [res_loc] : {fset Location});
  f_inv := (@f_inv);
  f_div_loc := (fset [res_loc] : {fset Location});
  f_div := (@f_div)|}.
Solve All Obligations with exact int_eqdec.
Fail Next Obligation.
Hint Unfold t_z_17__t_Group.

Notation "'t_G'" := (t_z_17_).

Equations n {L : {fset Location}} {I : Interface} : both L I (uint_size) :=
  n  :=
    solve_lift (ret_both (20 : uint_size)) : both L I (uint_size).
Fail Next Obligation.

Definition t_OvnContractState : choice_type :=
  (nseq f_group_type 20 × nseq int32 20 × nseq int32 20 × nseq f_group_type 20 × nseq int32 20 × int32).
Equations f_g_pow_xis {L : {fset Location}} {I : Interface} (s : both L I (t_OvnContractState)) : both L I (nseq f_group_type 20) :=
  f_g_pow_xis s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (fst (fst (fst (fst (fst x)))) : nseq f_group_type 20))) : both L I (nseq f_group_type 20).
Fail Next Obligation.
Equations f_zkp_xis {L : {fset Location}} {I : Interface} (s : both L I (t_OvnContractState)) : both L I (nseq int32 20) :=
  f_zkp_xis s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd (fst (fst (fst (fst x)))) : nseq int32 20))) : both L I (nseq int32 20).
Fail Next Obligation.
Equations f_commit_vis {L : {fset Location}} {I : Interface} (s : both L I (t_OvnContractState)) : both L I (nseq int32 20) :=
  f_commit_vis s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd (fst (fst (fst x))) : nseq int32 20))) : both L I (nseq int32 20).
Fail Next Obligation.
Equations f_g_pow_xi_yi_vis {L : {fset Location}} {I : Interface} (s : both L I (t_OvnContractState)) : both L I (nseq f_group_type 20) :=
  f_g_pow_xi_yi_vis s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd (fst (fst x)) : nseq f_group_type 20))) : both L I (nseq f_group_type 20).
Fail Next Obligation.
Equations f_zkp_vis {L : {fset Location}} {I : Interface} (s : both L I (t_OvnContractState)) : both L I (nseq int32 20) :=
  f_zkp_vis s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd (fst x) : nseq int32 20))) : both L I (nseq int32 20).
Fail Next Obligation.
Equations f_tally {L : {fset Location}} {I : Interface} (s : both L I (t_OvnContractState)) : both L I (int32) :=
  f_tally s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd x : int32))) : both L I (int32).
Fail Next Obligation.
Equations Build_t_OvnContractState {L0 : {fset Location}} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {L4 : {fset Location}} {L5 : {fset Location}} {I0 : Interface} {I1 : Interface} {I2 : Interface} {I3 : Interface} {I4 : Interface} {I5 : Interface} {f_g_pow_xis : both L0 I0 (nseq f_group_type 20)} {f_zkp_xis : both L1 I1 (nseq int32 20)} {f_commit_vis : both L2 I2 (nseq int32 20)} {f_g_pow_xi_yi_vis : both L3 I3 (nseq f_group_type 20)} {f_zkp_vis : both L4 I4 (nseq int32 20)} {f_tally : both L5 I5 (int32)} : both (L0:|:L1:|:L2:|:L3:|:L4:|:L5) (I0:|:I1:|:I2:|:I3:|:I4:|:I5) (t_OvnContractState) :=
  Build_t_OvnContractState  :=
    bind_both f_tally (fun f_tally =>
      bind_both f_zkp_vis (fun f_zkp_vis =>
        bind_both f_g_pow_xi_yi_vis (fun f_g_pow_xi_yi_vis =>
          bind_both f_commit_vis (fun f_commit_vis =>
            bind_both f_zkp_xis (fun f_zkp_xis =>
              bind_both f_g_pow_xis (fun f_g_pow_xis =>
                solve_lift (ret_both ((f_g_pow_xis,f_zkp_xis,f_commit_vis,f_g_pow_xi_yi_vis,f_zkp_vis,f_tally) : (t_OvnContractState))))))))) : both (L0:|:L1:|:L2:|:L3:|:L4:|:L5) (I0:|:I1:|:I2:|:I3:|:I4:|:I5) (t_OvnContractState).
Fail Next Obligation.
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_g_pow_xis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := y) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := f_zkp_vis x) (f_tally := f_tally x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_zkp_xis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := y) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := f_zkp_vis x) (f_tally := f_tally x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_commit_vis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := y) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := f_zkp_vis x) (f_tally := f_tally x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_g_pow_xi_yi_vis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := y) (f_zkp_vis := f_zkp_vis x) (f_tally := f_tally x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_zkp_vis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := y) (f_tally := f_tally x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_tally' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := f_zkp_vis x) (f_tally := y)).

Equations init_ovn_contract {L1 : {fset Location}} {I1 : Interface} {impl_108907986_ : _} `{ t_Sized (impl_108907986_)} `{ t_HasInitContext (impl_108907986_) ('unit)} (_ : both L1 I1 (impl_108907986_)) : both L1 I1 (t_Result (t_OvnContractState) (t_Reject)) :=
  init_ovn_contract _  :=
    Result_Ok (solve_lift (Build_t_OvnContractState (f_g_pow_xis := repeat f_one (ret_both (20 : uint_size))) (f_zkp_xis := repeat (ret_both (0 : int32)) (ret_both (20 : uint_size))) (f_commit_vis := repeat (ret_both (0 : int32)) (ret_both (20 : uint_size))) (f_g_pow_xi_yi_vis := repeat f_one (ret_both (20 : uint_size))) (f_zkp_vis := repeat (ret_both (0 : int32)) (ret_both (20 : uint_size))) (f_tally := ret_both (0 : int32)))) : both L1 I1 (t_Result (t_OvnContractState) (t_Reject)).
Fail Next Obligation.

Equations select_private_voting_key {L1 : {fset Location}} {I1 : Interface} (random : both L1 I1 (int32)) : both L1 I1 (int32) :=
  select_private_voting_key random  :=
    solve_lift (random .% q) : both L1 I1 (int32).
Fail Next Obligation.

Equations v_ZKP {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (g_pow_xi : both L1 I1 (int32)) (xi : both L2 I2 (int32)) : both (L1 :|: L2) (I1 :|: I2) (int32) :=
  v_ZKP g_pow_xi xi  :=
    solve_lift (ret_both (0 : int32)) : both (L1 :|: L2) (I1 :|: I2) (int32).
Fail Next Obligation.

Definition t_RegisterParam : choice_type :=
  (int32 × int32).
Equations f_rp_i {L : {fset Location}} {I : Interface} (s : both L I (t_RegisterParam)) : both L I (int32) :=
  f_rp_i s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (fst x : int32))) : both L I (int32).
Fail Next Obligation.
Equations f_rp_xi {L : {fset Location}} {I : Interface} (s : both L I (t_RegisterParam)) : both L I (int32) :=
  f_rp_xi s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd x : int32))) : both L I (int32).
Fail Next Obligation.
Equations Build_t_RegisterParam {L0 : {fset Location}} {L1 : {fset Location}} {I0 : Interface} {I1 : Interface} {f_rp_i : both L0 I0 (int32)} {f_rp_xi : both L1 I1 (int32)} : both (L0:|:L1) (I0:|:I1) (t_RegisterParam) :=
  Build_t_RegisterParam  :=
    bind_both f_rp_xi (fun f_rp_xi =>
      bind_both f_rp_i (fun f_rp_i =>
        solve_lift (ret_both ((f_rp_i,f_rp_xi) : (t_RegisterParam))))) : both (L0:|:L1) (I0:|:I1) (t_RegisterParam).
Fail Next Obligation.
Notation "'Build_t_RegisterParam' '[' x ']' '(' 'f_rp_i' ':=' y ')'" := (Build_t_RegisterParam (f_rp_i := y) (f_rp_xi := f_rp_xi x)).
Notation "'Build_t_RegisterParam' '[' x ']' '(' 'f_rp_xi' ':=' y ')'" := (Build_t_RegisterParam (f_rp_i := f_rp_i x) (f_rp_xi := y)).

Definition register_vote_state_ret_loc {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} : Location :=
  (t_OvnContractState ; 1%nat).

(* Notation f_branch := branch. *)
Notation f_get := get.
Notation f_parameter_cursor := parameter_cursor.
Notation f_from_residual := from_residual.
Notation f_clone := clone.
Notation f_accept := accept.

Equations register_vote {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} (ctx : both L1 I1 (impl_574521470_)) (state : both L2 I2 (t_OvnContractState)) : both (L1 :|: L2 :|: fset [register_vote_state_ret_loc]) (I1 :|: I2) (t_Result ((v_A × t_OvnContractState)) (t_ParseError)) :=
  register_vote ctx state  :=
    solve_lift (run (letb '(_,out) := f_get (f_parameter_cursor ctx) in
    letm[choice_typeMonad.result_bind_code (t_Result ((v_A × t_OvnContractState)) (t_ParseError))] (params:t_RegisterParam) := matchb branch out with
    | ControlFlow_Break residual =>
      letm[choice_typeMonad.result_bind_code (t_Result ((v_A × t_OvnContractState)) (t_ParseError))] hoist1 := v_Break (f_from_residual residual) in
      ControlFlow_Continue (never_to_any hoist1)
    | ControlFlow_Continue val =>
      ControlFlow_Continue val
    end in
    ControlFlow_Continue (letb g_pow_xi := f_g_pow (f_rp_xi params) in
    letb zkp_xi := v_ZKP g_pow_xi (f_rp_xi params) in
    letb register_vote_state_ret loc(register_vote_state_ret_loc) := f_clone state in
    letb register_vote_state_ret := Build_t_OvnContractState[register_vote_state_ret] (f_g_pow_xis := update_at (f_g_pow_xis register_vote_state_ret) (cast_int (WS2 := _) (f_rp_i params)) g_pow_xi) in
    letb register_vote_state_ret := Build_t_OvnContractState[register_vote_state_ret] (f_zkp_xis := update_at (f_zkp_xis register_vote_state_ret) (cast_int (WS2 := _) (f_rp_i params)) zkp_xi) in
    Result_Ok (prod_b (f_accept,register_vote_state_ret))))) : both (L1 :|: L2 :|: fset [register_vote_state_ret_loc]) (I1 :|: I2) (t_Result ((v_A × t_OvnContractState)) (t_ParseError)).
Fail Next Obligation.

Definition t_CastVoteParam : choice_type :=
  (int32 × int32 × 'bool).
Equations f_cvp_i {L : {fset Location}} {I : Interface} (s : both L I (t_CastVoteParam)) : both L I (int32) :=
  f_cvp_i s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (fst (fst x) : int32))) : both L I (int32).
Fail Next Obligation.
Equations f_cvp_xi {L : {fset Location}} {I : Interface} (s : both L I (t_CastVoteParam)) : both L I (int32) :=
  f_cvp_xi s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd (fst x) : int32))) : both L I (int32).
Fail Next Obligation.
Equations f_cvp_vote {L : {fset Location}} {I : Interface} (s : both L I (t_CastVoteParam)) : both L I ('bool) :=
  f_cvp_vote s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd x : 'bool))) : both L I ('bool).
Fail Next Obligation.
Equations Build_t_CastVoteParam {L0 : {fset Location}} {L1 : {fset Location}} {L2 : {fset Location}} {I0 : Interface} {I1 : Interface} {I2 : Interface} {f_cvp_i : both L0 I0 (int32)} {f_cvp_xi : both L1 I1 (int32)} {f_cvp_vote : both L2 I2 ('bool)} : both (L0:|:L1:|:L2) (I0:|:I1:|:I2) (t_CastVoteParam) :=
  Build_t_CastVoteParam  :=
    bind_both f_cvp_vote (fun f_cvp_vote =>
      bind_both f_cvp_xi (fun f_cvp_xi =>
        bind_both f_cvp_i (fun f_cvp_i =>
          solve_lift (ret_both ((f_cvp_i,f_cvp_xi,f_cvp_vote) : (t_CastVoteParam)))))) : both (L0:|:L1:|:L2) (I0:|:I1:|:I2) (t_CastVoteParam).
Fail Next Obligation.
Notation "'Build_t_CastVoteParam' '[' x ']' '(' 'f_cvp_i' ':=' y ')'" := (Build_t_CastVoteParam (f_cvp_i := y) (f_cvp_xi := f_cvp_xi x) (f_cvp_vote := f_cvp_vote x)).
Notation "'Build_t_CastVoteParam' '[' x ']' '(' 'f_cvp_xi' ':=' y ')'" := (Build_t_CastVoteParam (f_cvp_i := f_cvp_i x) (f_cvp_xi := y) (f_cvp_vote := f_cvp_vote x)).
Notation "'Build_t_CastVoteParam' '[' x ']' '(' 'f_cvp_vote' ':=' y ')'" := (Build_t_CastVoteParam (f_cvp_i := f_cvp_i x) (f_cvp_xi := f_cvp_xi x) (f_cvp_vote := y)).

Equations check_valid {L1 : {fset Location}} {I1 : Interface} (zkp : both L1 I1 (int32)) : both L1 I1 ('bool) :=
  check_valid zkp  :=
    solve_lift (ret_both (true : 'bool)) : both L1 I1 ('bool).
Fail Next Obligation.

Definition prod1_loc : Location :=
  (int32 ; 2%nat).
Definition prod2_loc : Location :=
  (int32 ; 3%nat).
Equations compute_group_element_for_vote {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {L4 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} {I4 : Interface} (i : both L1 I1 (int32)) (xi : both L2 I2 (int32)) (vote : both L3 I3 ('bool)) (xis : both L4 I4 (nseq int32 20)) : both (L1 :|: L2 :|: L3 :|: L4 :|: fset [res_loc;prod1_loc;prod2_loc]) (I1 :|: I2 :|: I3 :|: I4) (int32) :=
  compute_group_element_for_vote i xi vote xis  :=
    letb prod1 loc(prod1_loc) := f_one in
    letb prod1 := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (0 : uint_size)) (f_end := cast_int (WS2 := _) (i .- (ret_both (1 : int32)))))) (fun j =>
      ssp (fun prod1 =>
        solve_lift (f_prod prod1 (xis.a[j])) : both (*2*)(L1:|:L4:|:L1:|:fset [prod1_loc;prod1_loc]) (I1:|:I4:|:I1) (f_group_type))) prod1 in
    letb prod2 loc(prod2_loc) := f_one in
    letb prod2 := foldi_both_list (f_into_iter (Build_t_Range (f_start := cast_int (WS2 := _) (i .+ (ret_both (1 : int32)))) (f_end := n))) (fun j =>
      ssp (fun prod2 =>
        solve_lift (f_prod prod2 (xis.a[j])) : both (*2*)(L1:|:L4:|:L1:|:fset [prod2_loc;prod2_loc]) (I1:|:I4:|:I1) (f_group_type))) prod2 in
    letb v_Yi := f_div prod1 prod2 in
    solve_lift (f_prod (f_pow v_Yi xi) (f_g_pow (ifb vote
    then ret_both (1 : int32)
    else ret_both (0 : int32)))) : both (L1 :|: L2 :|: L3 :|: L4 :|: fset [res_loc;prod1_loc;prod2_loc]) (I1 :|: I2 :|: I3 :|: I4) (int32).
Fail Next Obligation.

Equations commit_to {L1 : {fset Location}} {I1 : Interface} (x : both L1 I1 (int32)) : both L1 I1 (int32) :=
  commit_to x  :=
    solve_lift (ret_both (0 : int32)) : both L1 I1 (int32).
Fail Next Obligation.

Definition commit_to_vote_state_ret_loc {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} : Location :=
  (t_OvnContractState ; 4%nat).
Equations commit_to_vote {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} (ctx : both L1 I1 (impl_574521470_)) (state : both L2 I2 (t_OvnContractState)) : both (L1 :|: L2 :|: fset [res_loc;commit_to_vote_state_ret_loc;prod1_loc;prod2_loc]) (I1 :|: I2) (t_Result ((v_A × t_OvnContractState)) (t_ParseError)) :=
  commit_to_vote ctx state  :=
    solve_lift (run (letb '(_,out) := f_get (f_parameter_cursor ctx) in
    letm[choice_typeMonad.result_bind_code (t_Result ((v_A × t_OvnContractState)) (t_ParseError))] (params:t_CastVoteParam) := matchb branch out with
    | ControlFlow_Break residual =>
      letm[choice_typeMonad.result_bind_code (t_Result ((v_A × t_OvnContractState)) (t_ParseError))] hoist2 := v_Break (f_from_residual residual) in
      ControlFlow_Continue (never_to_any hoist2)
    | ControlFlow_Continue val =>
      ControlFlow_Continue val
    end in
    ControlFlow_Continue (letb _ := foldi_both_list (f_into_iter (f_zkp_xis state)) (fun zkp =>
      ssp (fun _ =>
        letb _ := check_valid zkp in
        solve_lift (ret_both (tt : 'unit)) : both (*0*)(L2:|:fset []) (I2) ('unit))) (ret_both (tt : 'unit)) in
    letb g_pow_xi_yi_vi := compute_group_element_for_vote (f_cvp_i params) (f_cvp_xi params) (f_cvp_vote params) (f_g_pow_xis state) in
    letb commit_vi := commit_to g_pow_xi_yi_vi in
    letb commit_to_vote_state_ret loc(commit_to_vote_state_ret_loc) := f_clone state in
    letb commit_to_vote_state_ret := Build_t_OvnContractState[commit_to_vote_state_ret] (f_commit_vis := update_at (f_commit_vis commit_to_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i params)) commit_vi) in
    Result_Ok (prod_b (f_accept,commit_to_vote_state_ret))))) : both (L1 :|: L2 :|: fset [res_loc;commit_to_vote_state_ret_loc;prod1_loc;prod2_loc]) (I1 :|: I2) (t_Result ((v_A × t_OvnContractState)) (t_ParseError)).
Fail Next Obligation.

Equations v_ZKP_one_out_of_two {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (g_pow_vi : both L1 I1 (int32)) (vi : both L2 I2 ('bool)) : both (L1 :|: L2) (I1 :|: I2) (int32) :=
  v_ZKP_one_out_of_two g_pow_vi vi  :=
    solve_lift (ret_both (32 : int32)) : both (L1 :|: L2) (I1 :|: I2) (int32).
Fail Next Obligation.

Definition cast_vote_state_ret_loc {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} : Location :=
  (t_OvnContractState ; 5%nat).
Equations cast_vote {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} (ctx : both L1 I1 (impl_574521470_)) (state : both L2 I2 (t_OvnContractState)) : both (L1 :|: L2 :|: fset [res_loc;cast_vote_state_ret_loc;prod1_loc;prod2_loc]) (I1 :|: I2) (t_Result ((v_A × t_OvnContractState)) (t_ParseError)) :=
  cast_vote ctx state  :=
    solve_lift (run (letb '(_,out) := f_get (f_parameter_cursor ctx) in
    letm[choice_typeMonad.result_bind_code (t_Result ((v_A × t_OvnContractState)) (t_ParseError))] (params:t_CastVoteParam) := matchb branch out with
    | ControlFlow_Break residual =>
      letm[choice_typeMonad.result_bind_code (t_Result ((v_A × t_OvnContractState)) (t_ParseError))] hoist3 := v_Break (f_from_residual residual) in
      ControlFlow_Continue (never_to_any hoist3)
    | ControlFlow_Continue val =>
      ControlFlow_Continue val
    end in
    ControlFlow_Continue (letb g_pow_xi_yi_vi := compute_group_element_for_vote (f_cvp_i params) (f_cvp_xi params) (f_cvp_vote params) (f_g_pow_xis state) in
    letb zkp_vi := v_ZKP_one_out_of_two g_pow_xi_yi_vi (f_cvp_vote params) in
    letb cast_vote_state_ret loc(cast_vote_state_ret_loc) := f_clone state in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_g_pow_xi_yi_vis := update_at (f_g_pow_xi_yi_vis cast_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i params)) g_pow_xi_yi_vi) in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_zkp_vis := update_at (f_zkp_vis cast_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i params)) zkp_vi) in
    Result_Ok (prod_b (f_accept,cast_vote_state_ret))))) : both (L1 :|: L2 :|: fset [res_loc;cast_vote_state_ret_loc;prod1_loc;prod2_loc]) (I1 :|: I2) (t_Result ((v_A × t_OvnContractState)) (t_ParseError)).
Fail Next Obligation.

Equations check_valid2 {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (g_pow_xi_yi_vi : both L1 I1 (int32)) (zkp : both L2 I2 (int32)) : both (L1 :|: L2) (I1 :|: I2) ('bool) :=
  check_valid2 g_pow_xi_yi_vi zkp  :=
    solve_lift (ret_both (true : 'bool)) : both (L1 :|: L2) (I1 :|: I2) ('bool).
Fail Next Obligation.

Equations check_commitment {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (g_pow_xi_yi_vi : both L1 I1 (int32)) (zkp : both L2 I2 (int32)) : both (L1 :|: L2) (I1 :|: I2) ('bool) :=
  check_commitment g_pow_xi_yi_vi zkp  :=
    solve_lift (ret_both (true : 'bool)) : both (L1 :|: L2) (I1 :|: I2) ('bool).
Fail Next Obligation.

Definition t_TallyParameter : choice_type :=
  'unit.
Equations Build_t_TallyParameter : both (fset []) (fset []) (t_TallyParameter) :=
  Build_t_TallyParameter  :=
    solve_lift (ret_both ((_) : (t_TallyParameter))) : both (fset []) (fset []) (t_TallyParameter).
Fail Next Obligation.

Definition tally_loc {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} : Location :=
  (int32 ; 6%nat).
Definition tally_votes_state_ret_loc {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} : Location :=
  (t_OvnContractState ; 7%nat).
Definition vote_result_loc {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} : Location :=
  (f_group_type ; 8%nat).
Equations tally_votes {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} (_ : both L1 I1 (impl_574521470_)) (state : both L2 I2 (t_OvnContractState)) : both (L1 :|: L2 :|: fset [tally_loc;tally_votes_state_ret_loc;vote_result_loc]) (I1 :|: I2) (t_Result ((v_A × t_OvnContractState)) (t_ParseError)) :=
  tally_votes _ state  :=
    letb _ := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (0 : uint_size)) (f_end := n))) (fun i =>
      ssp (fun _ =>
        letb _ := check_valid2 ((f_g_pow_xi_yi_vis state).a[i]) ((f_zkp_vis state).a[i]) in
        letb _ := check_commitment ((f_g_pow_xi_yi_vis state).a[i]) ((f_commit_vis state).a[i]) in
        solve_lift (ret_both (tt : 'unit)) : both (*0*)(L2:|:fset []) (I2) ('unit))) (ret_both (tt : 'unit)) in
    letb vote_result loc(vote_result_loc) := f_one in
    letb vote_result := foldi_both_list (f_into_iter (f_g_pow_xi_yi_vis state)) (fun g_pow_vote =>
      ssp (fun vote_result =>
        solve_lift (f_prod vote_result g_pow_vote) : both (*2*)(L2:|:L2:|:fset [vote_result_loc;vote_result_loc]) (I2:|:I2) (f_group_type))) vote_result in
    letb tally loc(tally_loc) := ret_both (0 : int32) in
    letb tally := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (0 : int32)) (f_end := cast_int (WS2 := _) n))) (fun i =>
      ssp (fun tally =>
        solve_lift (ifb (f_g_pow i) =.? vote_result
        then letb tally := i in
          tally
        else tally) : both (*3*)(L2 :|: fset [tally_loc;vote_result_loc;tally_loc]) (I2 :|: (fset [])) (int32))) tally in
    letb tally_votes_state_ret loc(tally_votes_state_ret_loc) := f_clone state in
    letb tally_votes_state_ret := Build_t_OvnContractState[tally_votes_state_ret] (f_tally := tally) in
      Result_Ok (solve_lift (prod_b (f_accept,tally_votes_state_ret))) : both (L1 :|: L2 :|: fset [tally_loc;tally_votes_state_ret_loc;vote_result_loc]) (I1 :|: I2) (t_Result ((v_A × t_OvnContractState)) (t_ParseError)).
Fail Next Obligation.

(** Concert lib part **)
From ConCert.Utils Require Import Extras.
Export Extras.
From ConCert.Utils Require Import Automation.
Export Automation.
From ConCert.Execution Require Import Serializable.
Export Serializable.
From ConCert.Execution Require Import Blockchain.
Export Blockchain.
From ConCert.Execution Require Import ContractCommon.
Export ContractCommon.
From ConCert.Execution Require Import Serializable.
Export Serializable.
Require Import ConCertLib.
Export ConCertLib.

Definition state_OVN : choice_type :=
  t_OvnContractState.

Definition init_OVN (chain : Chain) (ctx : ContractCallContext) (st : state_OVN) : ResultMonad.result (state_OVN) (t_ParseError) :=
  ResultMonad.Ok st.

#[global] Program Instance t_RegisterParam_t_HasReceiveContext : t_HasReceiveContext t_RegisterParam 'unit :=
  { get := (fun  (x : _) {L : {fset Location}} {I : Interface} => (solve_lift (@ret_both (t_ParamType × t_Result x t_ParseError)) (tt, inr tt)) : _)}.
Fail Next Obligation.
#[global] Program Instance t_RegisterParam_t_Sized : t_Sized t_RegisterParam := { Sized := (fun x => x) }.
Fail Next Obligation.
Definition receive_OVN_register {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} {L0 : {fset Location}} {L1 : {fset Location}} {I0 : Interface} {I1 : Interface} (ctx : both L0 I0 (t_RegisterParam)) (st : both L1 I1 (state_OVN)) : both _ _ (t_Result ((v_A × state_OVN)) (t_ParseError)) :=
  register_vote ctx st.

#[global] Program Instance t_CastVoteParam_t_HasReceiveContext : t_HasReceiveContext t_CastVoteParam 'unit :=
  {| get := (fun  (x : _) {L : {fset Location}} {I : Interface} => (solve_lift (@ret_both (t_ParamType × t_Result x t_ParseError)) (tt, inr tt)) : _)|}.
Fail Next Obligation.
#[global] Program Instance t_CastVoteParam_t_Sized : t_Sized t_CastVoteParam :=
  { Sized := (fun  (x : _) => x : _)}.
Fail Next Obligation.
Definition receive_OVN_commit_to_vote {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} {L0 : {fset Location}} {L1 : {fset Location}} {I0 : Interface} {I1 : Interface} (ctx : both L0 I0 (t_CastVoteParam)) (st : both L1 I1 (state_OVN)) : both _ _ (t_Result ((v_A × state_OVN)) (t_ParseError)) :=
  commit_to_vote ctx st.

(* #[global] Program Instance t_CastVoteParam_t_HasReceiveContext : t_HasReceiveContext t_CastVoteParam 'unit := *)
(*   {| get := (fun  (x : _) {L : {fset Location}} {I : Interface} => (solve_lift (@ret_both (t_ParamType × t_Result x t_ParseError)) (tt, inr tt)) : _)|}. *)
(* Fail Next Obligation. *)
(* #[global] Program Instance t_CastVoteParam_t_Sized : t_Sized t_CastVoteParam := *)
(*   { Sized := (fun  (x : _) => x : _)}. *)
(* Fail Next Obligation. *)
Definition receive_OVN_cast_vote {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} {L0 : {fset Location}} {L1 : {fset Location}} {I0 : Interface} {I1 : Interface} (ctx : both L0 I0 (t_CastVoteParam)) (st : both L1 I1 (state_OVN)) : both _ _ (t_Result ((v_A × state_OVN)) (t_ParseError)) :=
  cast_vote ctx st.

#[global] Program Instance t_TallyParameter_t_HasReceiveContext : t_HasReceiveContext t_TallyParameter 'unit :=
  {| get := (fun  (x : _) {L : {fset Location}} {I : Interface} => (solve_lift (@ret_both (t_ParamType × t_Result x t_ParseError)) (tt, inr tt)) : _)|}.
Fail Next Obligation.
#[global] Program Instance t_TallyParameter_t_Sized : t_Sized t_TallyParameter :=
  { Sized := (fun  (x : _) => x : _)}.
Fail Next Obligation.
Definition receive_OVN_tally {v_A : _} {impl_574521470_ : _} `{ t_Sized (v_A)} `{ t_Sized (impl_574521470_)} `{ t_HasActions (v_A)} `{ t_HasReceiveContext (impl_574521470_) ('unit)} {L0 : {fset Location}} {L1 : {fset Location}} {I0 : Interface} {I1 : Interface} (ctx : both L0 I0 (t_TallyParameter)) (st : both L1 I1 (state_OVN)) : both _ _ (t_Result ((v_A × state_OVN)) (t_ParseError)) :=
  tally_votes ctx st.

Inductive Msg_OVN: Type :=
| msg_OVN_register : t_RegisterParam -> Msg_OVN
| msg_OVN_commit_to_vote : t_CastVoteParam -> Msg_OVN
| msg_OVN_cast_vote : t_CastVoteParam -> Msg_OVN
| msg_OVN_tally : t_TallyParameter -> Msg_OVN.
#[global] Program Instance state_OVN_t_HasReceiveContext : t_HasReceiveContext state_OVN 'unit :=
  {| get := (fun  (x : _) {L : {fset Location}} {I : Interface} => (solve_lift (@ret_both (t_ParamType × t_Result x t_ParseError)) (tt, inr tt)) : _)|}.
Fail Next Obligation.
#[global] Program Instance state_OVN_t_Sized : t_Sized state_OVN :=
  { Sized := (fun  (x : _) => x : _)}.
Fail Next Obligation.
#[global] Program Instance state_OVN_t_HasActions : t_HasActions state_OVN :=
  _.
Next Obligation.
  constructor.
  intros.
  refine (solve_lift (Build_t_OvnContractState (f_g_pow_xis := repeat f_one (ret_both (20 : uint_size))) (f_zkp_xis := repeat (ret_both (0 : int32)) (ret_both (20 : uint_size))) (f_commit_vis := repeat (ret_both (0 : int32)) (ret_both (20 : uint_size))) (f_g_pow_xi_yi_vis := repeat f_one (ret_both (20 : uint_size))) (f_zkp_vis := repeat (ret_both (0 : int32)) (ret_both (20 : uint_size))) (f_tally := ret_both (0 : int32))) : both L I state_OVN).
  Unshelve.
  3: apply I.
  3: apply L.
  3: apply I.
  3: apply L.
  all: solve_ssprove_obligations.
Defined.

Fail Next Obligation.
Equations receive_OVN (chain : Chain) (ctx : ContractCallContext) (st : state_OVN) (msg : Datatypes.option Msg_OVN) : ResultMonad.result (state_OVN * list ActionBody) t_ParseError :=
  receive_OVN chain ctx st msg  :=
    match msg with
    | Some (msg_OVN_register val) =>
      match (is_pure (both_prog (receive_OVN_register (ret_both val) (ret_both st)))) with
         | inl x => ResultMonad.Ok ((fst x), [])
         | inr x => ResultMonad.Err x
         end
    | Some (msg_OVN_commit_to_vote val) =>
      match (is_pure (both_prog (receive_OVN_commit_to_vote (ret_both val) (ret_both st)))) with
         | inl x => ResultMonad.Ok ((fst x), [])
         | inr x => ResultMonad.Err x
         end
    | Some (msg_OVN_cast_vote val) =>
      match (is_pure (both_prog (receive_OVN_cast_vote (ret_both val) (ret_both st)))) with
         | inl x => ResultMonad.Ok ((fst x), [])
         | inr x => ResultMonad.Err x
         end
    | Some (msg_OVN_tally val) =>
      match (is_pure (both_prog (receive_OVN_tally (ret_both val) (ret_both st)))) with
         | inl x => ResultMonad.Ok ((fst x), [])
         | inr x => ResultMonad.Err x
         end
    | _ =>
      ResultMonad.Err tt
    end : ResultMonad.result (state_OVN * list ActionBody) t_ParseError.
Fail Next Obligation.
#[global] Program Instance state_OVN_Serializable : Serializable state_OVN :=
  _.
Fail Next Obligation.
#[global] Program Instance Msg_OVN_Serializable : Serializable Msg_OVN :=
  Derive Serializable Msg_OVN_rect< msg_OVN_register, msg_OVN_commit_to_vote, msg_OVN_cast_vote, msg_OVN_tally >.
Fail Next Obligation.
Definition contract_OVN : Contract (state_OVN) (Msg_OVN) (state_OVN) (t_ParseError) :=
  build_contract init_OVN receive_OVN.
