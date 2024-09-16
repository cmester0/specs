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

Require Import Crate_Ovn_traits.
Export Crate_Ovn_traits.

Equations sub {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (x : both v_Z) (y : both v_Z) : both v_Z :=
  sub x y  :=
    x .+ (f_neg y) : both v_Z.
Fail Next Obligation.

Equations compute_group_element_for_vote {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (xi : both f_Z) (vote : both 'bool) (g_pow_yi : both v_G) : both v_G :=
  compute_group_element_for_vote xi vote g_pow_yi  :=
    (f_pow g_pow_yi xi) .* (f_g_pow (ifb vote
    then f_field_one
    else f_field_zero)) : both v_G.
Fail Next Obligation.

Equations div {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (x : both v_G) (y : both v_G) : both v_G :=
  div x y  :=
    x .* (f_group_inv y) : both v_G.
Fail Next Obligation.

Equations compute_g_pow_yi {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} (i : both uint_size) (xis : both (nseq v_G (is_pure (n)))) : both v_G :=
  compute_g_pow_yi i xis  :=
    letb prod1 := f_product (f_map (impl__iter (xis.a[(Build_t_Range (f_start := ret_both (0 : uint_size)) (f_end := i))])) (fun x =>
      f_clone x)) in
    letb prod2 := f_product (f_map (impl__iter (xis.a[(Build_t_Range (f_start := i .+ (ret_both (1 : uint_size))) (f_end := n))])) (fun x =>
      f_clone x)) in
    div prod1 prod2 : both v_G.
Fail Next Obligation.

Equations check_commitment {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (g_pow_xi_yi_vi : both v_G) (commitment : both f_Z) : both 'bool :=
  check_commitment g_pow_xi_yi_vi commitment  :=
    (f_hash (impl__into_vec (unsize (box_new (array_from_list [g_pow_xi_yi_vi]))))) =.? commitment : both 'bool.
Fail Next Obligation.

Equations commit_to {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (g_pow_xi_yi_vi : both v_G) : both f_Z :=
  commit_to g_pow_xi_yi_vi  :=
    f_hash (impl__into_vec (unsize (box_new (array_from_list [g_pow_xi_yi_vi])))) : both f_Z.
Fail Next Obligation.

Definition t_CastVoteParam {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} : choice_type :=
  (int32 × v_Z × v_Z × v_Z × v_Z × 'bool).
Equations f_cvp_i {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (s : both t_CastVoteParam) : both int32 :=
  f_cvp_i s  :=
    bind_both s (fun x =>
      ret_both (fst (fst (fst (fst (fst x)))) : int32)) : both int32.
Fail Next Obligation.
Equations f_cvp_xi {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (s : both t_CastVoteParam) : both v_Z :=
  f_cvp_xi s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst (fst x)))) : v_Z)) : both v_Z.
Fail Next Obligation.
Equations f_cvp_zkp_random_w {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (s : both t_CastVoteParam) : both v_Z :=
  f_cvp_zkp_random_w s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst x))) : v_Z)) : both v_Z.
Fail Next Obligation.
Equations f_cvp_zkp_random_r {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (s : both t_CastVoteParam) : both v_Z :=
  f_cvp_zkp_random_r s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst x)) : v_Z)) : both v_Z.
Fail Next Obligation.
Equations f_cvp_zkp_random_d {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (s : both t_CastVoteParam) : both v_Z :=
  f_cvp_zkp_random_d s  :=
    bind_both s (fun x =>
      ret_both (snd (fst x) : v_Z)) : both v_Z.
Fail Next Obligation.
Equations f_cvp_vote {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (s : both t_CastVoteParam) : both 'bool :=
  f_cvp_vote s  :=
    bind_both s (fun x =>
      ret_both (snd x : 'bool)) : both 'bool.
Fail Next Obligation.
Equations Build_t_CastVoteParam {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} {f_cvp_i : both int32} {f_cvp_xi : both v_Z} {f_cvp_zkp_random_w : both v_Z} {f_cvp_zkp_random_r : both v_Z} {f_cvp_zkp_random_d : both v_Z} {f_cvp_vote : both 'bool} : both (t_CastVoteParam) :=
  Build_t_CastVoteParam  :=
    bind_both f_cvp_vote (fun f_cvp_vote =>
      bind_both f_cvp_zkp_random_d (fun f_cvp_zkp_random_d =>
        bind_both f_cvp_zkp_random_r (fun f_cvp_zkp_random_r =>
          bind_both f_cvp_zkp_random_w (fun f_cvp_zkp_random_w =>
            bind_both f_cvp_xi (fun f_cvp_xi =>
              bind_both f_cvp_i (fun f_cvp_i =>
                ret_both ((f_cvp_i,f_cvp_xi,f_cvp_zkp_random_w,f_cvp_zkp_random_r,f_cvp_zkp_random_d,f_cvp_vote) : (t_CastVoteParam)))))))) : both (t_CastVoteParam).
Fail Next Obligation.
Notation "'Build_t_CastVoteParam' '[' x ']' '(' 'f_cvp_i' ':=' y ')'" := (Build_t_CastVoteParam (f_cvp_i := y) (f_cvp_xi := f_cvp_xi x) (f_cvp_zkp_random_w := f_cvp_zkp_random_w x) (f_cvp_zkp_random_r := f_cvp_zkp_random_r x) (f_cvp_zkp_random_d := f_cvp_zkp_random_d x) (f_cvp_vote := f_cvp_vote x)).
Notation "'Build_t_CastVoteParam' '[' x ']' '(' 'f_cvp_xi' ':=' y ')'" := (Build_t_CastVoteParam (f_cvp_i := f_cvp_i x) (f_cvp_xi := y) (f_cvp_zkp_random_w := f_cvp_zkp_random_w x) (f_cvp_zkp_random_r := f_cvp_zkp_random_r x) (f_cvp_zkp_random_d := f_cvp_zkp_random_d x) (f_cvp_vote := f_cvp_vote x)).
Notation "'Build_t_CastVoteParam' '[' x ']' '(' 'f_cvp_zkp_random_w' ':=' y ')'" := (Build_t_CastVoteParam (f_cvp_i := f_cvp_i x) (f_cvp_xi := f_cvp_xi x) (f_cvp_zkp_random_w := y) (f_cvp_zkp_random_r := f_cvp_zkp_random_r x) (f_cvp_zkp_random_d := f_cvp_zkp_random_d x) (f_cvp_vote := f_cvp_vote x)).
Notation "'Build_t_CastVoteParam' '[' x ']' '(' 'f_cvp_zkp_random_r' ':=' y ')'" := (Build_t_CastVoteParam (f_cvp_i := f_cvp_i x) (f_cvp_xi := f_cvp_xi x) (f_cvp_zkp_random_w := f_cvp_zkp_random_w x) (f_cvp_zkp_random_r := y) (f_cvp_zkp_random_d := f_cvp_zkp_random_d x) (f_cvp_vote := f_cvp_vote x)).
Notation "'Build_t_CastVoteParam' '[' x ']' '(' 'f_cvp_zkp_random_d' ':=' y ')'" := (Build_t_CastVoteParam (f_cvp_i := f_cvp_i x) (f_cvp_xi := f_cvp_xi x) (f_cvp_zkp_random_w := f_cvp_zkp_random_w x) (f_cvp_zkp_random_r := f_cvp_zkp_random_r x) (f_cvp_zkp_random_d := y) (f_cvp_vote := f_cvp_vote x)).
Notation "'Build_t_CastVoteParam' '[' x ']' '(' 'f_cvp_vote' ':=' y ')'" := (Build_t_CastVoteParam (f_cvp_i := f_cvp_i x) (f_cvp_xi := f_cvp_xi x) (f_cvp_zkp_random_w := f_cvp_zkp_random_w x) (f_cvp_zkp_random_r := f_cvp_zkp_random_r x) (f_cvp_zkp_random_d := f_cvp_zkp_random_d x) (f_cvp_vote := y)).

Definition t_OrZKPCommit {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} : choice_type :=
  (v_G × v_G × v_G × v_G × v_G × v_G × f_Z × f_Z × f_Z × f_Z × f_Z).
Equations f_or_zkp_x {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both v_G :=
  f_or_zkp_x s  :=
    bind_both s (fun x =>
      ret_both (fst (fst (fst (fst (fst (fst (fst (fst (fst (fst x))))))))) : v_G)) : both v_G.
Fail Next Obligation.
Equations f_or_zkp_y {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both v_G :=
  f_or_zkp_y s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst (fst (fst (fst (fst (fst (fst x))))))))) : v_G)) : both v_G.
Fail Next Obligation.
Equations f_or_zkp_a1 {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both v_G :=
  f_or_zkp_a1 s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst (fst (fst (fst (fst (fst x)))))))) : v_G)) : both v_G.
Fail Next Obligation.
Equations f_or_zkp_b1 {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both v_G :=
  f_or_zkp_b1 s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst (fst (fst (fst (fst x))))))) : v_G)) : both v_G.
Fail Next Obligation.
Equations f_or_zkp_a2 {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both v_G :=
  f_or_zkp_a2 s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst (fst (fst (fst x)))))) : v_G)) : both v_G.
Fail Next Obligation.
Equations f_or_zkp_b2 {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both v_G :=
  f_or_zkp_b2 s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst (fst (fst x))))) : v_G)) : both v_G.
Fail Next Obligation.
Equations f_or_zkp_c {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both f_Z :=
  f_or_zkp_c s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst (fst x)))) : f_Z)) : both f_Z.
Fail Next Obligation.
Equations f_or_zkp_d1 {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both f_Z :=
  f_or_zkp_d1 s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst x))) : f_Z)) : both f_Z.
Fail Next Obligation.
Equations f_or_zkp_d2 {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both f_Z :=
  f_or_zkp_d2 s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst x)) : f_Z)) : both f_Z.
Fail Next Obligation.
Equations f_or_zkp_r1 {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both f_Z :=
  f_or_zkp_r1 s  :=
    bind_both s (fun x =>
      ret_both (snd (fst x) : f_Z)) : both f_Z.
Fail Next Obligation.
Equations f_or_zkp_r2 {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OrZKPCommit) : both f_Z :=
  f_or_zkp_r2 s  :=
    bind_both s (fun x =>
      ret_both (snd x : f_Z)) : both f_Z.
Fail Next Obligation.
Equations Build_t_OrZKPCommit {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} {f_or_zkp_x : both v_G} {f_or_zkp_y : both v_G} {f_or_zkp_a1 : both v_G} {f_or_zkp_b1 : both v_G} {f_or_zkp_a2 : both v_G} {f_or_zkp_b2 : both v_G} {f_or_zkp_c : both f_Z} {f_or_zkp_d1 : both f_Z} {f_or_zkp_d2 : both f_Z} {f_or_zkp_r1 : both f_Z} {f_or_zkp_r2 : both f_Z} : both (t_OrZKPCommit) :=
  Build_t_OrZKPCommit  :=
    bind_both f_or_zkp_r2 (fun f_or_zkp_r2 =>
      bind_both f_or_zkp_r1 (fun f_or_zkp_r1 =>
        bind_both f_or_zkp_d2 (fun f_or_zkp_d2 =>
          bind_both f_or_zkp_d1 (fun f_or_zkp_d1 =>
            bind_both f_or_zkp_c (fun f_or_zkp_c =>
              bind_both f_or_zkp_b2 (fun f_or_zkp_b2 =>
                bind_both f_or_zkp_a2 (fun f_or_zkp_a2 =>
                  bind_both f_or_zkp_b1 (fun f_or_zkp_b1 =>
                    bind_both f_or_zkp_a1 (fun f_or_zkp_a1 =>
                      bind_both f_or_zkp_y (fun f_or_zkp_y =>
                        bind_both f_or_zkp_x (fun f_or_zkp_x =>
                          ret_both ((f_or_zkp_x,f_or_zkp_y,f_or_zkp_a1,f_or_zkp_b1,f_or_zkp_a2,f_or_zkp_b2,f_or_zkp_c,f_or_zkp_d1,f_or_zkp_d2,f_or_zkp_r1,f_or_zkp_r2) : (t_OrZKPCommit))))))))))))) : both (t_OrZKPCommit).
Fail Next Obligation.
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_x' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := y) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_y' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := y) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_a1' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := y) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_b1' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := y) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_a2' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := y) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_b2' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := y) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_c' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := y) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_d1' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := y) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_d2' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := y) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_r1' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := y) (f_or_zkp_r2 := f_or_zkp_r2 x)).
Notation "'Build_t_OrZKPCommit' '[' x ']' '(' 'f_or_zkp_r2' ':=' y ')'" := (Build_t_OrZKPCommit (f_or_zkp_x := f_or_zkp_x x) (f_or_zkp_y := f_or_zkp_y x) (f_or_zkp_a1 := f_or_zkp_a1 x) (f_or_zkp_b1 := f_or_zkp_b1 x) (f_or_zkp_a2 := f_or_zkp_a2 x) (f_or_zkp_b2 := f_or_zkp_b2 x) (f_or_zkp_c := f_or_zkp_c x) (f_or_zkp_d1 := f_or_zkp_d1 x) (f_or_zkp_d2 := f_or_zkp_d2 x) (f_or_zkp_r1 := f_or_zkp_r1 x) (f_or_zkp_r2 := y)).

Definition t_RegisterParam {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} : choice_type :=
  (int32 × v_Z × v_Z).
Equations f_rp_i {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (s : both t_RegisterParam) : both int32 :=
  f_rp_i s  :=
    bind_both s (fun x =>
      ret_both (fst (fst x) : int32)) : both int32.
Fail Next Obligation.
Equations f_rp_xi {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (s : both t_RegisterParam) : both v_Z :=
  f_rp_xi s  :=
    bind_both s (fun x =>
      ret_both (snd (fst x) : v_Z)) : both v_Z.
Fail Next Obligation.
Equations f_rp_zkp_random {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} (s : both t_RegisterParam) : both v_Z :=
  f_rp_zkp_random s  :=
    bind_both s (fun x =>
      ret_both (snd x : v_Z)) : both v_Z.
Fail Next Obligation.
Equations Build_t_RegisterParam {v_Z : _} `{ t_Sized v_Z} `{ t_Field v_Z} {f_rp_i : both int32} {f_rp_xi : both v_Z} {f_rp_zkp_random : both v_Z} : both (t_RegisterParam) :=
  Build_t_RegisterParam  :=
    bind_both f_rp_zkp_random (fun f_rp_zkp_random =>
      bind_both f_rp_xi (fun f_rp_xi =>
        bind_both f_rp_i (fun f_rp_i =>
          ret_both ((f_rp_i,f_rp_xi,f_rp_zkp_random) : (t_RegisterParam))))) : both (t_RegisterParam).
Fail Next Obligation.
Notation "'Build_t_RegisterParam' '[' x ']' '(' 'f_rp_i' ':=' y ')'" := (Build_t_RegisterParam (f_rp_i := y) (f_rp_xi := f_rp_xi x) (f_rp_zkp_random := f_rp_zkp_random x)).
Notation "'Build_t_RegisterParam' '[' x ']' '(' 'f_rp_xi' ':=' y ')'" := (Build_t_RegisterParam (f_rp_i := f_rp_i x) (f_rp_xi := y) (f_rp_zkp_random := f_rp_zkp_random x)).
Notation "'Build_t_RegisterParam' '[' x ']' '(' 'f_rp_zkp_random' ':=' y ')'" := (Build_t_RegisterParam (f_rp_i := f_rp_i x) (f_rp_xi := f_rp_xi x) (f_rp_zkp_random := y)).

Definition t_SchnorrZKPCommit {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} : choice_type :=
  (v_G × f_Z × f_Z).
Equations f_schnorr_zkp_u {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_SchnorrZKPCommit) : both v_G :=
  f_schnorr_zkp_u s  :=
    bind_both s (fun x =>
      ret_both (fst (fst x) : v_G)) : both v_G.
Fail Next Obligation.
Equations f_schnorr_zkp_c {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_SchnorrZKPCommit) : both f_Z :=
  f_schnorr_zkp_c s  :=
    bind_both s (fun x =>
      ret_both (snd (fst x) : f_Z)) : both f_Z.
Fail Next Obligation.
Equations f_schnorr_zkp_z {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_SchnorrZKPCommit) : both f_Z :=
  f_schnorr_zkp_z s  :=
    bind_both s (fun x =>
      ret_both (snd x : f_Z)) : both f_Z.
Fail Next Obligation.
Equations Build_t_SchnorrZKPCommit {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} {f_schnorr_zkp_u : both v_G} {f_schnorr_zkp_c : both f_Z} {f_schnorr_zkp_z : both f_Z} : both (t_SchnorrZKPCommit) :=
  Build_t_SchnorrZKPCommit  :=
    bind_both f_schnorr_zkp_z (fun f_schnorr_zkp_z =>
      bind_both f_schnorr_zkp_c (fun f_schnorr_zkp_c =>
        bind_both f_schnorr_zkp_u (fun f_schnorr_zkp_u =>
          ret_both ((f_schnorr_zkp_u,f_schnorr_zkp_c,f_schnorr_zkp_z) : (t_SchnorrZKPCommit))))) : both (t_SchnorrZKPCommit).
Fail Next Obligation.
Notation "'Build_t_SchnorrZKPCommit' '[' x ']' '(' 'f_schnorr_zkp_u' ':=' y ')'" := (Build_t_SchnorrZKPCommit (f_schnorr_zkp_u := y) (f_schnorr_zkp_c := f_schnorr_zkp_c x) (f_schnorr_zkp_z := f_schnorr_zkp_z x)).
Notation "'Build_t_SchnorrZKPCommit' '[' x ']' '(' 'f_schnorr_zkp_c' ':=' y ')'" := (Build_t_SchnorrZKPCommit (f_schnorr_zkp_u := f_schnorr_zkp_u x) (f_schnorr_zkp_c := y) (f_schnorr_zkp_z := f_schnorr_zkp_z x)).
Notation "'Build_t_SchnorrZKPCommit' '[' x ']' '(' 'f_schnorr_zkp_z' ':=' y ')'" := (Build_t_SchnorrZKPCommit (f_schnorr_zkp_u := f_schnorr_zkp_u x) (f_schnorr_zkp_c := f_schnorr_zkp_c x) (f_schnorr_zkp_z := y)).

Definition t_TallyParameter : choice_type :=
  'unit.
Equations Build_t_TallyParameter : both (t_TallyParameter) :=
  Build_t_TallyParameter  :=
    ret_both (tt (* Empty tuple *) : (t_TallyParameter)) : both (t_TallyParameter).
Fail Next Obligation.

Equations schnorr_zkp {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (random : both f_Z) (h : both v_G) (x : both f_Z) : both (t_SchnorrZKPCommit v_G) :=
  schnorr_zkp random h x  :=
    run (letb r := random in
    letb u := f_g_pow r in
    letb c := f_hash (impl__into_vec (unsize (box_new (array_from_list [f_g;
      h;
      u])))) in
    letb z := r .+ (c .* x) in
    letm[choice_typeMonad.result_bind_code (t_SchnorrZKPCommit v_G)] hoist1 := ControlFlow_Break (Build_t_SchnorrZKPCommit (f_schnorr_zkp_u := u) (f_schnorr_zkp_c := c) (f_schnorr_zkp_z := z)) in
    ControlFlow_Continue (never_to_any hoist1)) : both (t_SchnorrZKPCommit v_G).
Fail Next Obligation.

Equations schnorr_zkp_validate {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (h : both v_G) (pi : both (t_SchnorrZKPCommit v_G)) : both 'bool :=
  schnorr_zkp_validate h pi  :=
    andb ((f_schnorr_zkp_c pi) =.? (f_hash (impl__into_vec (unsize (box_new (array_from_list [f_g;
      h;
      f_schnorr_zkp_u pi])))))) ((f_g_pow (f_schnorr_zkp_z pi)) =.? ((f_schnorr_zkp_u pi) .* (f_pow h (f_schnorr_zkp_c pi)))) : both 'bool.
Fail Next Obligation.

Equations zkp_one_out_of_two {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (random_w : both f_Z) (random_r : both f_Z) (random_d : both f_Z) (h : both v_G) (xi : both f_Z) (vi : both 'bool) : both (t_OrZKPCommit v_G) :=
  zkp_one_out_of_two random_w random_r random_d h xi vi  :=
    letb w := random_w in
    ifb vi
    then letb r1 := random_r in
    letb d1 := random_d in
    letb x := f_g_pow xi in
    letb y := (f_pow h xi) .* f_g in
    letb a1 := (f_g_pow r1) .* (f_pow x d1) in
    letb b1 := (f_pow h r1) .* (f_pow y d1) in
    letb a2 := f_g_pow w in
    letb b2 := f_pow h w in
    letb c := f_hash (impl__into_vec (unsize (box_new (array_from_list [x;
      y;
      a1;
      b1;
      a2;
      b2])))) in
    letb d2 := sub c d1 in
    letb r2 := sub w (xi .* d2) in
    Build_t_OrZKPCommit (f_or_zkp_x := x) (f_or_zkp_y := y) (f_or_zkp_a1 := a1) (f_or_zkp_b1 := b1) (f_or_zkp_a2 := a2) (f_or_zkp_b2 := b2) (f_or_zkp_c := c) (f_or_zkp_d1 := d1) (f_or_zkp_d2 := d2) (f_or_zkp_r1 := r1) (f_or_zkp_r2 := r2)
    else letb r2 := random_r in
    letb d2 := random_d in
    letb x := f_g_pow xi in
    letb y := f_pow h xi in
    letb a1 := f_g_pow w in
    letb b1 := f_pow h w in
    letb a2 := (f_g_pow r2) .* (f_pow x d2) in
    letb b2 := (f_pow h r2) .* (f_pow (div y f_g) d2) in
    letb c := f_hash (impl__into_vec (unsize (box_new (array_from_list [x;
      y;
      a1;
      b1;
      a2;
      b2])))) in
    letb d1 := sub c d2 in
    letb r1 := sub w (xi .* d1) in
    Build_t_OrZKPCommit (f_or_zkp_x := x) (f_or_zkp_y := y) (f_or_zkp_a1 := a1) (f_or_zkp_b1 := b1) (f_or_zkp_a2 := a2) (f_or_zkp_b2 := b2) (f_or_zkp_c := c) (f_or_zkp_d1 := d1) (f_or_zkp_d2 := d2) (f_or_zkp_r1 := r1) (f_or_zkp_r2 := r2) : both (t_OrZKPCommit v_G).
Fail Next Obligation.

Equations zkp_one_out_of_two_validate {v_G : _} `{ t_Sized v_G} `{ t_Group v_G} (h : both v_G) (zkp : both (t_OrZKPCommit v_G)) : both 'bool :=
  zkp_one_out_of_two_validate h zkp  :=
    letb c := f_hash (impl__into_vec (unsize (box_new (array_from_list [f_or_zkp_x zkp;
      f_or_zkp_y zkp;
      f_or_zkp_a1 zkp;
      f_or_zkp_b1 zkp;
      f_or_zkp_a2 zkp;
      f_or_zkp_b2 zkp])))) in
    andb (andb (andb (andb (c =.? ((f_or_zkp_d1 zkp) .+ (f_or_zkp_d2 zkp))) ((f_or_zkp_a1 zkp) =.? ((f_g_pow (f_or_zkp_r1 zkp)) .* (f_pow (f_or_zkp_x zkp) (f_or_zkp_d1 zkp))))) ((f_or_zkp_b1 zkp) =.? ((f_pow h (f_or_zkp_r1 zkp)) .* (f_pow (f_or_zkp_y zkp) (f_or_zkp_d1 zkp))))) ((f_or_zkp_a2 zkp) =.? ((f_g_pow (f_or_zkp_r2 zkp)) .* (f_pow (f_or_zkp_x zkp) (f_or_zkp_d2 zkp))))) ((f_or_zkp_b2 zkp) =.? ((f_pow h (f_or_zkp_r2 zkp)) .* (f_pow (div (f_or_zkp_y zkp) f_g) (f_or_zkp_d2 zkp)))) : both 'bool.
Fail Next Obligation.

Definition t_OvnContractState {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} : choice_type :=
  (nseq v_G (is_pure (n)) × nseq (t_SchnorrZKPCommit v_G) (is_pure (n)) × nseq f_Z (is_pure (n)) × nseq v_G (is_pure (n)) × nseq (t_OrZKPCommit v_G) (is_pure (n)) × int32 × nseq 'bool (is_pure (n))).
Equations f_g_pow_xis {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OvnContractState) : both (nseq v_G (is_pure (n))) :=
  f_g_pow_xis s  :=
    bind_both s (fun x =>
      ret_both (fst (fst (fst (fst (fst (fst x))))) : (nseq v_G (is_pure (n))))) : both (nseq v_G (is_pure (n))).
Fail Next Obligation.
Equations f_zkp_xis {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OvnContractState) : both (nseq (t_SchnorrZKPCommit v_G) (is_pure (n))) :=
  f_zkp_xis s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst (fst (fst x))))) : (nseq (t_SchnorrZKPCommit v_G) (is_pure (n))))) : both (nseq (t_SchnorrZKPCommit v_G) (is_pure (n))).
Fail Next Obligation.
Equations f_commit_vis {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OvnContractState) : both (nseq f_Z (is_pure (n))) :=
  f_commit_vis s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst (fst x)))) : (nseq f_Z (is_pure (n))))) : both (nseq f_Z (is_pure (n))).
Fail Next Obligation.
Equations f_g_pow_xi_yi_vis {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OvnContractState) : both (nseq v_G (is_pure (n))) :=
  f_g_pow_xi_yi_vis s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst (fst x))) : (nseq v_G (is_pure (n))))) : both (nseq v_G (is_pure (n))).
Fail Next Obligation.
Equations f_zkp_vis {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OvnContractState) : both (nseq (t_OrZKPCommit v_G) (is_pure (n))) :=
  f_zkp_vis s  :=
    bind_both s (fun x =>
      ret_both (snd (fst (fst x)) : (nseq (t_OrZKPCommit v_G) (is_pure (n))))) : both (nseq (t_OrZKPCommit v_G) (is_pure (n))).
Fail Next Obligation.
Equations f_tally {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OvnContractState) : both int32 :=
  f_tally s  :=
    bind_both s (fun x =>
      ret_both (snd (fst x) : int32)) : both int32.
Fail Next Obligation.
Equations f_round1 {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} (s : both t_OvnContractState) : both (nseq 'bool (is_pure (n))) :=
  f_round1 s  :=
    bind_both s (fun x =>
      ret_both (snd x : (nseq 'bool (is_pure (n))))) : both (nseq 'bool (is_pure (n))).
Fail Next Obligation.
Equations Build_t_OvnContractState {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} {f_g_pow_xis : both (nseq v_G (is_pure (n)))} {f_zkp_xis : both (nseq (t_SchnorrZKPCommit v_G) (is_pure (n)))} {f_commit_vis : both (nseq f_Z (is_pure (n)))} {f_g_pow_xi_yi_vis : both (nseq v_G (is_pure (n)))} {f_zkp_vis : both (nseq (t_OrZKPCommit v_G) (is_pure (n)))} {f_tally : both int32} {f_round1 : both (nseq 'bool (is_pure (n)))} : both (t_OvnContractState) :=
  Build_t_OvnContractState  :=
    bind_both f_round1 (fun f_round1 =>
      bind_both f_tally (fun f_tally =>
        bind_both f_zkp_vis (fun f_zkp_vis =>
          bind_both f_g_pow_xi_yi_vis (fun f_g_pow_xi_yi_vis =>
            bind_both f_commit_vis (fun f_commit_vis =>
              bind_both f_zkp_xis (fun f_zkp_xis =>
                bind_both f_g_pow_xis (fun f_g_pow_xis =>
                  ret_both ((f_g_pow_xis,f_zkp_xis,f_commit_vis,f_g_pow_xi_yi_vis,f_zkp_vis,f_tally,f_round1) : (t_OvnContractState))))))))) : both (t_OvnContractState).
Fail Next Obligation.
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_g_pow_xis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := y) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := f_zkp_vis x) (f_tally := f_tally x) (f_round1 := f_round1 x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_zkp_xis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := y) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := f_zkp_vis x) (f_tally := f_tally x) (f_round1 := f_round1 x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_commit_vis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := y) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := f_zkp_vis x) (f_tally := f_tally x) (f_round1 := f_round1 x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_g_pow_xi_yi_vis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := y) (f_zkp_vis := f_zkp_vis x) (f_tally := f_tally x) (f_round1 := f_round1 x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_zkp_vis' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := y) (f_tally := f_tally x) (f_round1 := f_round1 x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_tally' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := f_zkp_vis x) (f_tally := y) (f_round1 := f_round1 x)).
Notation "'Build_t_OvnContractState' '[' x ']' '(' 'f_round1' ':=' y ')'" := (Build_t_OvnContractState (f_g_pow_xis := f_g_pow_xis x) (f_zkp_xis := f_zkp_xis x) (f_commit_vis := f_commit_vis x) (f_g_pow_xi_yi_vis := f_g_pow_xi_yi_vis x) (f_zkp_vis := f_zkp_vis x) (f_tally := f_tally x) (f_round1 := y)).

Equations cast_vote {v_G : _} {n : both uint_size} {v_A : _} {impl_574521470_ : _} `{ t_Sized v_G} `{ t_Sized v_A} `{ t_Sized impl_574521470_} `{ t_Group v_G} `{ t_HasActions v_A} `{ t_HasReceiveContext impl_574521470_ 'unit} (ctx : both impl_574521470_) (state : both (t_OvnContractState v_G (both uint_size))) : both (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError) :=
  cast_vote ctx state  :=
    run (letb '(_,out) := f_get (f_parameter_cursor ctx) in
    letm[choice_typeMonad.result_bind_code t_ParseError] (params : t_CastVoteParam f_Z) := out in
    Result_Ok (letb g_pow_yi := compute_g_pow_yi (cast_int (WS2 := _) (f_cvp_i params)) (f_g_pow_xis state) in
    letb g_pow_xi_yi_vi := compute_group_element_for_vote (f_cvp_xi params) (f_cvp_vote params) g_pow_yi in
    letb zkp_vi := zkp_one_out_of_two (f_cvp_zkp_random_w params) (f_cvp_zkp_random_r params) (f_cvp_zkp_random_d params) g_pow_yi (f_cvp_xi params) (f_cvp_vote params) in
    letb cast_vote_state_ret := f_clone state in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_g_pow_xi_yi_vis := update_at_usize (f_g_pow_xi_yi_vis cast_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i params)) g_pow_xi_yi_vi) in
    letb cast_vote_state_ret := Build_t_OvnContractState[cast_vote_state_ret] (f_zkp_vis := update_at_usize (f_zkp_vis cast_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i params)) zkp_vi) in
    Result_Ok (prod_b (f_accept,cast_vote_state_ret)))) : both (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError).
Fail Next Obligation.

Equations commit_to_vote {v_G : _} {n : both uint_size} {v_A : _} {impl_574521470_ : _} `{ t_Sized v_G} `{ t_Sized v_A} `{ t_Sized impl_574521470_} `{ t_Group v_G} `{ t_HasActions v_A} `{ t_HasReceiveContext impl_574521470_ 'unit} (ctx : both impl_574521470_) (state : both (t_OvnContractState v_G (both uint_size))) : both (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError) :=
  commit_to_vote ctx state  :=
    run (letb '(_,out) := f_get (f_parameter_cursor ctx) in
    letm[choice_typeMonad.result_bind_code t_ParseError] (params : t_CastVoteParam f_Z) := out in
    Result_Ok (letb _ := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (0 : uint_size)) (f_end := n))) (fun i =>
      ssp (fun _ =>
        ifb orb (not (schnorr_zkp_validate ((f_g_pow_xis state).a[i]) ((f_zkp_xis state).a[i]))) (not ((f_round1 state).a[i]))
        then letm[choice_typeMonad.result_bind_code (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError)] hoist26 := ControlFlow_Break (Result_Err ParseError) in
        ControlFlow_Continue (never_to_any hoist26)
        else ControlFlow_Continue (ret_both (tt : 'unit)) : (both (t_ControlFlow (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError) 'unit)))) (ret_both (tt : 'unit)) in
    letb g_pow_yi := compute_g_pow_yi (cast_int (WS2 := _) (f_cvp_i params)) (f_g_pow_xis state) in
    letb g_pow_xi_yi_vi := compute_group_element_for_vote (f_cvp_xi params) (f_cvp_vote params) g_pow_yi in
    letb commit_vi := commit_to g_pow_xi_yi_vi in
    letb commit_to_vote_state_ret := f_clone state in
    letb commit_to_vote_state_ret := Build_t_OvnContractState[commit_to_vote_state_ret] (f_commit_vis := update_at_usize (f_commit_vis commit_to_vote_state_ret) (cast_int (WS2 := _) (f_cvp_i params)) commit_vi) in
    Result_Ok (prod_b (f_accept,commit_to_vote_state_ret)))) : both (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError).
Fail Next Obligation.

Equations init_ovn_contract {v_G : _} {n : both uint_size} `{ t_Sized v_G} `{ t_Group v_G} (_ : both 'unit) : both (t_Result (t_OvnContractState v_G (both uint_size)) t_Reject) :=
  init_ovn_contract _  :=
    Result_Ok (Build_t_OvnContractState (f_g_pow_xis := repeat f_group_one n) (f_zkp_xis := repeat (Build_t_SchnorrZKPCommit (f_schnorr_zkp_u := f_group_one) (f_schnorr_zkp_z := f_field_zero) (f_schnorr_zkp_c := f_field_zero)) n) (f_commit_vis := repeat f_field_zero n) (f_g_pow_xi_yi_vis := repeat f_group_one n) (f_zkp_vis := repeat (Build_t_OrZKPCommit (f_or_zkp_x := f_group_one) (f_or_zkp_y := f_group_one) (f_or_zkp_a1 := f_group_one) (f_or_zkp_b1 := f_group_one) (f_or_zkp_a2 := f_group_one) (f_or_zkp_b2 := f_group_one) (f_or_zkp_c := f_field_zero) (f_or_zkp_d1 := f_field_zero) (f_or_zkp_d2 := f_field_zero) (f_or_zkp_r1 := f_field_zero) (f_or_zkp_r2 := f_field_zero)) n) (f_tally := ret_both (0 : int32)) (f_round1 := repeat (ret_both (false : 'bool)) n)) : both (t_Result (t_OvnContractState v_G (both uint_size)) t_Reject).
Fail Next Obligation.

Equations register_vote {v_G : _} {n : both uint_size} {v_A : _} {impl_574521470_ : _} `{ t_Sized v_G} `{ t_Sized v_A} `{ t_Sized impl_574521470_} `{ t_Group v_G} `{ t_HasActions v_A} `{ t_HasReceiveContext impl_574521470_ 'unit} (ctx : both impl_574521470_) (state : both (t_OvnContractState v_G (both uint_size))) : both (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError) :=
  register_vote ctx state  :=
    run (letb '(_,out) := f_get (f_parameter_cursor ctx) in
    letm[choice_typeMonad.result_bind_code t_ParseError] (params : t_RegisterParam f_Z) := out in
    Result_Ok (letb g_pow_xi := f_g_pow (f_rp_xi params) in
    letb zkp_xi := schnorr_zkp (f_rp_zkp_random params) g_pow_xi (f_rp_xi params) in
    letb register_vote_state_ret := f_clone state in
    letb register_vote_state_ret := Build_t_OvnContractState[register_vote_state_ret] (f_g_pow_xis := update_at_usize (f_g_pow_xis register_vote_state_ret) (cast_int (WS2 := _) (f_rp_i params)) g_pow_xi) in
    letb register_vote_state_ret := Build_t_OvnContractState[register_vote_state_ret] (f_zkp_xis := update_at_usize (f_zkp_xis register_vote_state_ret) (cast_int (WS2 := _) (f_rp_i params)) zkp_xi) in
    letb register_vote_state_ret := Build_t_OvnContractState[register_vote_state_ret] (f_round1 := update_at_usize (f_round1 register_vote_state_ret) (cast_int (WS2 := _) (f_rp_i params)) (ret_both (true : 'bool))) in
    Result_Ok (prod_b (f_accept,register_vote_state_ret)))) : both (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError).
Fail Next Obligation.

Equations tally_votes {v_G : _} {n : both uint_size} {v_A : _} {impl_574521470_ : _} `{ t_Sized v_G} `{ t_Sized v_A} `{ t_Sized impl_574521470_} `{ t_Group v_G} `{ t_HasActions v_A} `{ t_HasReceiveContext impl_574521470_ 'unit} (_ : both impl_574521470_) (state : both (t_OvnContractState v_G (both uint_size))) : both (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError) :=
  tally_votes _ state  :=
    letb _ := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (0 : uint_size)) (f_end := n))) (fun i =>
      ssp (fun _ =>
        letb g_pow_yi := compute_g_pow_yi i (f_g_pow_xis state) in
        letm[choice_typeMonad.result_bind_code (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError)] _ := ControlFlow_Continue (ifb not (zkp_one_out_of_two_validate g_pow_yi ((f_zkp_vis state).a[i]))
        then letm[choice_typeMonad.result_bind_code (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError)] hoist27 := ControlFlow_Break (Result_Err ParseError) in
        ControlFlow_Continue (never_to_any hoist27)
        else ControlFlow_Continue (ret_both (tt : 'unit))) in
        ifb not (check_commitment ((f_g_pow_xi_yi_vis state).a[i]) ((f_commit_vis state).a[i]))
        then letm[choice_typeMonad.result_bind_code (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError)] hoist28 := ControlFlow_Break (Result_Err ParseError) in
        ControlFlow_Continue (never_to_any hoist28)
        else ControlFlow_Continue (ret_both (tt : 'unit)) : (both (t_ControlFlow (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError) 'unit)))) (ret_both (tt : 'unit)) in
    letb vote_result := f_group_one in
    letb vote_result := foldi_both_list (f_into_iter (f_g_pow_xi_yi_vis state)) (fun g_pow_vote =>
      ssp (fun vote_result =>
        vote_result .* g_pow_vote : (both v_G))) vote_result in
    letb tally := ret_both (0 : int32) in
    letb curr := f_field_zero in
    letb '(curr,tally) := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (0 : int32)) (f_end := cast_int (WS2 := _) n))) (fun i =>
      ssp (fun '(curr,tally) =>
        letb tally := ifb (f_g_pow curr) =.? vote_result
        then letb tally := i in
        tally
        else tally in
        letb curr := curr .+ f_field_one in
        prod_b (curr,tally) : (both (f_Z × int32)))) (prod_b (curr,tally)) in
    letb tally_votes_state_ret := f_clone state in
    letb tally_votes_state_ret := Build_t_OvnContractState[tally_votes_state_ret] (f_tally := tally) in
    Result_Ok (prod_b (f_accept,tally_votes_state_ret)) : both (t_Result (v_A × t_OvnContractState v_G (both uint_size)) t_ParseError).
Fail Next Obligation.
