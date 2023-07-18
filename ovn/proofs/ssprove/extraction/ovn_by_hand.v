(* File automatically generated by Hacspec *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
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

Require Import Core. (* as TryFrom *)

Require Import Core. (* as mem *)

Require Import Hacspec_lib.

Class t_Hasher (Self : choice_type) := {
  t_Hash : choice_type ;
  t_Hash_t_TryFrom :> t_TryFrom (t_Hash) ;
  t_Hash_t_Into :> t_Into (t_Hash) ;
  t_Hash_t_PartialEq :> t_PartialEq (t_Hash) ;
  t_Hash_t_Copy :> t_Copy (t_Hash) ;
  t_Hash_t_Clone :> t_Clone (t_Hash) ;
  t_Hash_t_Sized :> t_Sized (t_Hash) ;
  hash : seq int8 -> t_Hash ;
  concat_and_hash : t_Hash -> t_Option (t_Hash) -> t_Hash ;
  hash_size : uint_size ;
}.

Definition t_PartialTreeLayer (H : _) : choice_type :=
  t_Vec ((uint_size × H)) (t_Global).

Definition t_PartialTree (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} : choice_type := t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global).
Definition Build_PartialTree {L I} {T : _} `{ t_Sized (T)} `{ t_Hasher (T)} {f_layers : both L I (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global))} : both L I (t_PartialTree _) := f_layers.

Program Definition is_left_index {L1 : {fset Location}} {I1 : Interface} (index : both L1 I1 (uint_size)) : both (L1) (I1) ('bool) :=
  (index .% i32(2)) =.? i32(0).
Fail Next Obligation.

Program Definition get_sibling_index {L1 : {fset Location}} {I1 : Interface} (index : both L1 I1 (uint_size)) : both (L1) (I1) (uint_size) :=
  ifb is_left_index index
  then index .+ i32(1)
  else index .- i32(1).
Fail Next Obligation.

Definition height_loc : Location :=
  (int32 ; 0%nat).
Program Definition tree_depth {L1 : {fset Location}} {I1 : Interface} (leaves_count : both L1 I1 (uint_size)) : both (L1 :|: fset [height_loc]) (I1) (uint_size) :=
  letbm height loc(height_loc) := (i32(0)) : both _ _ (int32) in
  letbm height loc(height_loc) := (ifb leaves_count =.? i32(1)
    then letb height := (i32(1)) : both _ _ (int32) in
      height
    else letb height := (ilog2 leaves_count) : both _ _ (int32) in
      height) : both _ _ (int32) in
  (cast_int height).
Fail Next Obligation.

Program Definition parent_index {L1 : {fset Location}} {I1 : Interface} (index : both L1 I1 (uint_size)) : both (L1) (I1) (uint_size) :=
  ifb is_left_index index
  then index ./ i32(2)
  else (get_sibling_index index) ./ i32(2).
Fail Next Obligation.

Definition parents_loc : Location :=
  (t_Vec (uint_size) (t_Global) ; 1%nat).
Program Definition parent_indices {L1 : {fset Location}} {I1 : Interface} (indices : both L1 I1 (seq uint_size)) : both (L1 :|: fset [parents_loc]) (I1) (t_Vec (uint_size) (t_Global)) :=
  letbm parents loc(parents_loc) := (collect (map (cloned (iter indices)) parent_index)) : both _ _ (t_Vec (uint_size) (t_Global)) in
  letb parents := (dedup parents) : both _ _ (t_Vec (uint_size) (t_Global)) in
  parents.
Fail Next Obligation.

Definition t_ErrorKind : choice_type := chFin (mkpos 5).
Definition ErrorKind_SerializedProofSizeIsIncorrect {L I} : both L I t_ErrorKind := ret_both (fintype.Ordinal (n:=5) (m:=0) eq_refl : t_ErrorKind).
Definition ErrorKind_NotEnoughHelperNodes {L I} : both L I t_ErrorKind := ret_both (fintype.Ordinal (n:=5) (m:=1) eq_refl : t_ErrorKind).
Definition ErrorKind_HashConversionError {L I} : both L I t_ErrorKind := ret_both (fintype.Ordinal (n:=5) (m:=2) eq_refl : t_ErrorKind).
Definition ErrorKind_NotEnoughHashesToCalculateRoot {L I} : both L I t_ErrorKind := ret_both (fintype.Ordinal (n:=5) (m:=3) eq_refl : t_ErrorKind).
Definition ErrorKind_LeavesIndicesCountMismatch {L I} : both L I t_ErrorKind := ret_both (fintype.Ordinal (n:=5) (m:=4) eq_refl : t_ErrorKind).

Definition t_Error : choice_type := t_ErrorKind.
Definition Build_Error {L I} : both L I t_ErrorKind -> both L I t_Error :=
  fun x => x.

Program Definition new_under_impl {L1 : {fset Location}} {I1 : Interface} (kind : both L1 I1 (t_ErrorKind)) : both (L1) (I1) (t_Error) :=
  Build_Error kind.
Fail Next Obligation.

Program Definition not_enough_helper_nodes_under_impl : both (fset []) ([interface ]) (t_Error) :=
  new_under_impl ErrorKind_NotEnoughHelperNodes.
Fail Next Obligation.

Program Definition new_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} : both (fset []) ([interface ]) (t_PartialTree (T)) :=
  Build_PartialTree new_under_impl.
Fail Next Obligation.

Program Definition from_leaves_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} {L1 : {fset Location}} {I1 : Interface} (leaves : both L1 I1 (seq t_Hash)) : both (L1 :|: fset [current_layer_loc;nodes_loc;partial_tree_loc;reversed_layers_loc;parents_loc;height_loc]) (I1) (t_Result (t_PartialTree (T)) (t_Error)) :=
  letb leaf_tuples := (collect (enumerate (cloned (iter_under_impl leaves)))) : both _ _ (t_Vec ((uint_size × t_Hash)) (t_Global)) in
  build_under_impl_1 (into_vec_under_impl (unsize box_new)) (tree_depth (len_under_impl leaves)).
Fail Next Obligation.

Program Definition build_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (partial_layers : both L1 I1 (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global))) (depth : both L2 I2 (uint_size)) : both (L1:|:L2 :|: fset [current_layer_loc;nodes_loc;partial_tree_loc;reversed_layers_loc;parents_loc]) (I1:|:I2) (t_Result (t_PartialTree (T)) (t_Error)) :=
  run (letb layers := (match branch (build_tree_under_impl_1 partial_layers depth) with
    | ControlFlow_Break residual => letb hoist1 := (v_Break (from_residual residual)) : both _ _ (t_Never) in
      ControlFlow_Continue (never_to_any hoist1)
    | ControlFlow_Continue val => ControlFlow_Continue val
    end) : both _ _ (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global)) in
  ControlFlow_Continue (Result_Ok (Build_PartialTree layers))).
Fail Next Obligation.

Definition reversed_layers_loc : Location :=
  (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global) ; 5%nat).
Definition partial_tree_loc : Location :=
  (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global) ; 4%nat).
Definition nodes_loc : Location :=
  (t_Vec ((uint_size × t_Hash)) (t_Global) ; 3%nat).
Definition current_layer_loc : Location :=
  (t_Vec ((uint_size × t_Hash)) (t_Global) ; 2%nat).
Program Definition build_tree_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (partial_layers : both L1 I1 (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global))) (full_tree_depth : both L2 I2 (uint_size)) : both (L1:|:L2 :|: fset [current_layer_loc;nodes_loc;partial_tree_loc;reversed_layers_loc;parents_loc]) (I1:|:I2) (t_Result (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global)) (t_Error)) :=
  letbm partial_tree loc(partial_tree_loc) := (new_under_impl) : both _ _ (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global)) in
  letbm current_layer loc(current_layer_loc) := (new_under_impl) : both _ _ (t_Vec ((uint_size × t_Hash)) (t_Global)) in
  letb '(todo_fresh_var,partial_layers_temp) := (drain_under_impl_1 partial_layers RangeFull) : both _ _ ((t_Drain (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global) × t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global))) in
  letb partial_layers := (partial_layers_temp) : both _ _ (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global)) in
  letb hoist2 := (todo_fresh_var) : both _ _ (t_Drain (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global)) in
  letb hoist3 := (rev hoist2) : both _ _ (t_Rev (t_Drain (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global))) in
  letbm reversed_layers loc(reversed_layers_loc) := (collect hoist3) : both _ _ (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global)) in
  letb '(current_layer,partial_tree,reversed_layers) := (foldi_both (into_iter (Build_Range i32(0)full_tree_depth)) (fun {L I _ _} =>fun _ =>
      (ssp (fun '(current_layer,partial_tree,reversed_layers) =>
        letb '(todo_fresh_var,reversed_layers_temp) := (pop_under_impl_1 reversed_layers) : both _ _ ((t_Option (t_Vec ((uint_size × t_Hash)) (t_Global)) × t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global))) in
        letb reversed_layers := (reversed_layers_temp) : both _ _ (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global)) in
        letb hoist4 := (todo_fresh_var) : both _ _ (t_Option (t_Vec ((uint_size × t_Hash)) (t_Global))) in
        letb current_layer := (match hoist4 with
          | Option_Some nodes => letb '(current_layer_temp,nodes_temp) := (append_under_impl_1 current_layer nodes) : both _ _ ((t_Vec ((uint_size × t_Hash)) (t_Global) × t_Vec ((uint_size × t_Hash)) (t_Global))) in
            letb current_layer := (current_layer_temp) : both _ _ (t_Vec ((uint_size × t_Hash)) (t_Global)) in
            letb nodes := (nodes_temp) : both _ _ (t_Vec ((uint_size × t_Hash)) (t_Global)) in
            letb _ := (tt) : both _ _ (unit) in
            current_layer
          | _ => current_layer
          end) : both _ _ (t_Vec ((uint_size × t_Hash)) (t_Global)) in
        letb partial_tree := (push_under_impl_1 partial_tree (clone current_layer)) : both _ _ (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global)) in
        letb '(todo_fresh_var,current_layer_temp) := (drain_under_impl_1 current_layer RangeFull) : both _ _ ((t_Drain ((uint_size × t_Hash)) (t_Global) × t_Vec ((uint_size × t_Hash)) (t_Global))) in
        letb current_layer := (current_layer_temp) : both _ _ (t_Vec ((uint_size × t_Hash)) (t_Global)) in
        letb hoist5 := (todo_fresh_var) : both _ _ (t_Drain ((uint_size × t_Hash)) (t_Global)) in
        letb '(indices,nodes) := (unzip hoist5) : both _ _ ((t_Vec (uint_size) (t_Global) × t_Vec (t_Hash) (t_Global))) in
        letb parent_layer_indices := (parent_indices (deref indices)) : both _ _ (t_Vec (uint_size) (t_Global)) in
        letb current_layer := (foldi_both (into_iter (enumerate (iter_under_impl (deref parent_layer_indices)))) (fun {L I _ _} =>fun '(i,parent_node_index) =>
            (ssp (fun current_layer =>
              match get_under_impl (deref nodes) (i .* i32(2)) with
              | Option_Some left_node => ControlFlow_Continue (push_under_impl_1 current_layer prod_b(parent_node_index,concat_and_hash left_node (get_under_impl (deref nodes) ((i .* i32(2)) .+ i32(1)))))
              | Option_None  => letb hoist6 := (v_Break (Result_Err not_enough_helper_nodes_under_impl)) : both _ _ (t_Never) in
                ControlFlow_Continue (letb 'tt := (never_to_any hoist6) : both _ _ (unit) in
                current_layer)
              end) )) current_layer) : both _ _ (t_Vec ((uint_size × t_Hash)) (t_Global)) in
        prod_b(current_layer,partial_tree,reversed_layers)) )) prod_b(current_layer,partial_tree,reversed_layers)) : both _ _ ((t_Vec ((uint_size × t_Hash)) (t_Global) × t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global) × t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global))) in
  letb partial_tree := (push_under_impl_1 partial_tree (clone current_layer)) : both _ _ (t_Vec (t_Vec ((uint_size × t_Hash)) (t_Global)) (t_Global)) in
  Result_Ok partial_tree.
Fail Next Obligation.

Program Definition depth_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} {L1 : {fset Location}} {I1 : Interface} (self : both L1 I1 (t_PartialTree (T))) : both (L1) (I1) (uint_size) :=
  (len_under_impl_1 (f_layers self)) .- i32(1).
Fail Next Obligation.

Definition temp_loc : Location :=
  (t_IntoIter ((uint_size × t_Hash)) (t_Global) ; 6%nat).
Program Definition contains_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (self : both L1 I1 (t_PartialTree (T))) (layer_index : both L2 I2 (uint_size)) (node_index : both L3 I3 (uint_size)) : both (L1:|:L2:|:L3 :|: fset [temp_loc]) (I1:|:I2:|:I3) ('bool) :=
  match get_under_impl (layers_under_impl_1 self) layer_index with
  | Option_Some layer => letbm temp loc(temp_loc) := (into_iter (clone layer)) : both _ _ (t_IntoIter) in
    letb '(todo_fresh_var,temp_temp) := (any temp (fun '(index,_) =>
        index =.? node_index)) : both _ _ (('bool × t_IntoIter ((uint_size × t_Hash)) (t_Global))) in
    letb temp := (temp_temp) : both _ _ (t_IntoIter ((uint_size × t_Hash)) (t_Global)) in
    todo_fresh_var
  | Option_None  => false
  end.
Fail Next Obligation.

Program Definition upsert_layer_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (self : both L1 I1 (t_PartialTree (T))) (layer_index : both L2 I2 (uint_size)) (new_layer : both L3 I3 (t_Vec ((uint_size × t_Hash)) (t_Global))) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) (unit) :=
  match get_under_impl (deref (f_layers self)) layer_index with
  | Option_Some layer => tt
  | Option_None  => tt
  end.
Fail Next Obligation.

Program Definition layer_nodes_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} {L1 : {fset Location}} {I1 : Interface} (self : both L1 I1 (t_PartialTree (T))) : both (L1) (I1) (t_Vec (t_Vec (t_Hash) (t_Global)) (t_Global)) :=
  letb hashes := (collect (map (iter_under_impl (layers_under_impl_1 self)) (fun layer =>
      collect (map (cloned (iter_under_impl (deref layer))) (fun '(_,hash) =>
        hash))))) : both _ _ (t_Vec (t_Vec (t_Hash) (t_Global)) (t_Global)) in
  hashes.
Fail Next Obligation.

Program Definition layers_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} {L1 : {fset Location}} {I1 : Interface} (self : both L1 I1 (t_PartialTree (T))) : both (L1) (I1) (seq t_Vec ((uint_size × t_Hash)) (t_Global)) :=
  deref (f_layers self).
Fail Next Obligation.

Program Definition clear_under_impl_1 (T : _) `{ t_Sized (T)} `{ t_Hasher (T)} {L1 : {fset Location}} {I1 : Interface} (self : both L1 I1 (t_PartialTree (T))) : both (L1) (I1) (unit) :=
  tt.
Fail Next Obligation.
