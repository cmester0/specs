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

Require Import (* Hacspec_ovn_ *)Core.
Export (* Hacspec_ovn_ *)Core.

Require Import (* Hacspec_ovn_ *)Hacspec_lib.
Export (* Hacspec_ovn_ *)Hacspec_lib.

Class t_Group (Self : choice_type) := {
  t_group_type : choice_type ;
  t_group_type_t_Copy :> t_Copy (t_group_type) ;
  t_group_type_t_Clone :> t_Clone (t_group_type) ;
  t_group_type_t_PartialEq :> t_PartialEq (t_group_type) ;
  t_group_type_t_Sized :> t_Sized (t_group_type) ;
  q : forall {L I}, both L I uint_size ;
  g : forall {L I}, both L I t_group_type ;
  g_pow : forall {L I}, both L I uint_size -> both L I t_group_type ;
  one : forall {L I}, both L I t_group_type ;
  prod_tt : forall {L1 L2 I1 I2}, both L1 I1 t_group_type -> both L2 I2 t_group_type -> both (L1 :|: L2) (I1 :|: I2) t_group_type ;
  div : forall {L1 L2 I1 I2}, both L1 I1 t_group_type -> both L2 I2 t_group_type -> both (L1 :|: L2) (I1 :|: I2) t_group_type ;
  random_element : forall {L I}, both L I t_group_type ;
}.

Definition t_eligible_votes : choice_type :=
  (uint_size).
Equations Build_t_eligible_votes {L : {fset Location}} {I : Interface} (f_v_id : both L I (uint_size)) : both L I (t_eligible_votes) :=
  Build_t_eligible_votes f_v_id  :=
    bind_both f_v_id (fun f_v_id =>
      solve_lift (ret_both ((f_v_id) : (t_eligible_votes)))) : both L I (t_eligible_votes).
Fail Next Obligation.

Equations n : both (fset []) ([interface ]) (uint_size) :=
  n  :=
    solve_lift (ret_both (3 : uint_size)) : both (fset []) ([interface ]) (uint_size).
Fail Next Obligation.

Equations v_P : both (fset []) ([interface ]) (nseq t_eligible_votes 3) :=
  v_P  :=
    array_from_list [solve_lift (Build_t_eligible_votes (* Build_t_C_eligible_votes *) (ret_both (0 : uint_size)));
      solve_lift (Build_t_eligible_votes (* Build_t_C_eligible_votes *) (ret_both (1 : uint_size)));
      solve_lift (Build_t_eligible_votes (* Build_t_C_eligible_votes *) (ret_both (2 : uint_size)))] : both (fset []) ([interface ]) (nseq t_eligible_votes 3).
Fail Next Obligation.

Equations select_private_voting_key (G : _) `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {I1 : Interface} (random : both L1 I1 (uint_size)) : both (L1) (I1) (uint_size) :=
  select_private_voting_key G random  :=
    solve_lift (random .% q) : both (L1) (I1) (uint_size).
Fail Next Obligation.

Equations v_ZKP (G : _) `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {I1 : Interface} (xi : both L1 I1 (uint_size)) : both (L1) (I1) (uint_size) :=
  v_ZKP G xi  :=
    solve_lift (ret_both (0 : uint_size)) : both (L1) (I1) (uint_size).
Fail Next Obligation.

Equations get_broadcast1 : both (fset []) ([interface ]) ((t_Vec (uint_size) (t_Global) × t_Vec (uint_size) (t_Global))) :=
  get_broadcast1  :=
    solve_lift (prod_b (new(* _under_impl *) : both fset0 fset0 _,new(* _under_impl *) : both fset0 fset0 _)) : both (fset []) ([interface ]) ((t_Vec (uint_size) (t_Global) × t_Vec (uint_size) (t_Global))).
Fail Next Obligation.

Equations check_valid {L1 : {fset Location}} {I1 : Interface} (zkp : both L1 I1 (uint_size)) : both (L1) (I1) ('bool) :=
  check_valid zkp  :=
    solve_lift (ret_both (true : 'bool)) : both (L1) (I1) ('bool).
Fail Next Obligation.

Equations broadcast1 (G : _) `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (xi : both L1 I1 (t_group_type)) (zkp : both L2 I2 (uint_size)) (i : both L3 I3 (uint_size)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit) :=
  broadcast1 G xi zkp i  :=
    solve_lift (ret_both (tt : 'unit)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit).
Fail Next Obligation.

Definition prod1_loc {G : _} `{ t_Sized (G)} `{ t_Group (G)} : Location :=
  (t_group_type ; 0%nat).
Equations register_vote (G : _) `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (i : both L1 I1 (uint_size)) (random : both L2 I2 (uint_size)) : both (L1:|:L2 :|: fset [prod1_loc]) (I1:|:I2) ('unit) :=
  register_vote G i random  :=
    letb xi := (select_private_voting_key G random) : both _ _ (uint_size) in
    letb _ := (broadcast1 G (g_pow xi) (v_ZKP G xi) i) : both _ _ ('unit) in
    letb _ := (ret_both (tt : 'unit)) : both _ _ ('unit) in
    letb '(gs,zkps) := (get_broadcast1) : both _ _ ((t_Vec (uint_size) (t_Global) × t_Vec (uint_size) (t_Global))) in
    (* letb _ := (other loop todo(term)) : both _ _ ('unit) in *)
    letbm prod1 loc(prod1_loc) := (one) : both _ _ (t_group_type) in
    letb prod1 := (foldi_both (into_iter (Build_t_Range (ret_both (1 : uint_size))(i .- (ret_both (1 : uint_size))))) (fun {L I _ _} =>fun j =>
        (ssp (fun prod1 =>
          solve_lift (prod_tt prod1 (g_pow (gs.a[j])))) )) prod1) : both _ _ (t_group_type) in
    letb prod2 := (one) : both _ _ (t_group_type) in
    letb prod1 := (foldi_both (into_iter (Build_t_Range (i .+ (ret_both (1 : uint_size)))n)) (fun {L I _ _} =>fun j =>
        (ssp (fun prod1 =>
          solve_lift (prod_tt prod1 (g_pow (gs.a[j])))) )) prod1) : both _ _ (t_group_type) in
    letb Yi := (div prod1 prod2) : both _ _ (t_group_type) in
    solve_lift (ret_both (tt : 'unit)) : both (L1:|:L2 :|: fset [prod1_loc]) (I1:|:I2) ('unit).
Fail Next Obligation.

Equations v_ZKP_one_out_of_two {L1 : {fset Location}} {I1 : Interface} (vi : both L1 I1 ('bool)) : both (L1) (I1) (uint_size) :=
  v_ZKP_one_out_of_two vi  :=
    solve_lift (ret_both (32 : uint_size)) : both (L1) (I1) (uint_size).
Fail Next Obligation.

Equations broadcast2 (G : _) `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (g_pow_xiyi : both L1 I1 (t_group_type)) (g_pow_vi : both L2 I2 (t_group_type)) (g_pow_vi_zkp : both L3 I3 (uint_size)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit) :=
  broadcast2 G g_pow_xiyi g_pow_vi g_pow_vi_zkp  :=
    solve_lift (ret_both (tt : 'unit)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit).
Fail Next Obligation.

Equations get_broadcast2 (G : _) `{ t_Sized (G)} `{ t_Group (G)} : both (fset []) ([interface ]) ((t_Vec (t_group_type) (t_Global) × t_Vec (t_group_type) (t_Global) × t_Vec (uint_size) (t_Global))) :=
  get_broadcast2 G  :=
    solve_lift (prod_b (new(* _under_impl *) : both fset0 fset0 _,new(* _under_impl *): both fset0 fset0 _,new(* _under_impl *): both fset0 fset0 _)) : both (fset []) ([interface ]) ((t_Vec (t_group_type) (t_Global) × t_Vec (t_group_type) (t_Global) × t_Vec (uint_size) (t_Global))).
Fail Next Obligation.

Equations cast_vote (G : _) `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (xi : both L1 I1 (uint_size)) (yi : both L2 I2 (uint_size)) (vi : both L3 I3 ('bool)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit) :=
  cast_vote G xi yi vi  :=
    letb _ := (broadcast2 G (g_pow (xi .* yi)) (g_pow (ifb vi
      then ret_both (1 : uint_size)
      else ret_both (0 : uint_size))) (v_ZKP_one_out_of_two vi)) : both _ _ ('unit) in
    letb _ := (ret_both (tt : 'unit)) : both _ _ ('unit) in
    solve_lift (ret_both (tt : 'unit)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit).
Fail Next Obligation.

Definition vote_result_loc {G : _} `{ t_Sized (G)} `{ t_Group (G)} : Location :=
  (t_group_type ; 2%nat).
Definition tally_loc {G : _} `{ t_Sized (G)} `{ t_Group (G)} : Location :=
  (uint_size ; 1%nat).

Definition len {A L I} := lift1_both (L := L) (I := I) (fun (x : chList A) => repr _ (@List.length A x) : uint32).

Equations tally_votes (G : _) `{ t_Sized (G)} `{ t_Group (G)} : both (fset [tally_loc; vote_result_loc]) ([interface ]) (uint_size) :=
  tally_votes G  :=
    letb '(g_pow_xi_yi,g_pow_vi,zkps) := (get_broadcast2 G) : both _ _ ((t_Vec (t_group_type) (t_Global) × t_Vec (t_group_type) (t_Global) × t_Vec (uint_size) (t_Global))) in
    (* letb _ := (other loop todo(term)) : both _ _ ('unit) in *)
    (* letbm vote_result loc(vote_result_loc) := (one) : both _ _ (t_group_type) in *)
    (* letb vote_result := (foldi_both (into_iter (Build_t_Range (ret_both (0 : uint_size))(len(* _under_impl_1 *) g_pow_vi))) (fun {L I _ _} =>fun i => *)
    (*     (ssp (fun vote_result => *)
    (*       solve_lift (prod_tt vote_result (prod_tt (clone (g_pow_xi_yi.a[i])) (clone (g_pow_vi.a[i]))))) )) vote_result) : both _ _ (t_group_type) in *)
    letbm tally loc(tally_loc) := (ret_both (0 : uint_size)) : both _ _ (uint_size) in
    (* letb tally := (foldi_both (into_iter (Build_t_Range (ret_both (1 : uint_size))n)) (fun {L I _ _} =>fun i => *)
    (*     (ssp (fun tally => *)
    (*       (* ifb solve_lift ((g_pow tally) <> vote_result) *) *)
    (*       (* then ControlFlow_Continue (letb _ := (tally .+ (ret_both (1 : uint_size))) : both _ _ ('unit) in *) *)
    (*         solve_lift (ret_both (tt : 'unit)) (* ) *) *)
    (*       (* else letb hoist1 := (v_Break tally) : both _ _ (t_Never) in *) *)
    (*       (*   ControlFlow_Continue (letb _ := (never_to_any hoist1) : both _ _ ('unit) in *) *)
    (*       (*   tally) *)) )) tally) : both _ _ ('unit) in *)
      solve_lift tally : both (fset [tally_loc; vote_result_loc]) ([interface ]) (uint_size).
Fail Next Obligation.