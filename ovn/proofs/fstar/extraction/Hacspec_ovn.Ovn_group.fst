module Hacspec_ovn.Ovn_group
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Concordium_contracts_common.Traits in
  let open Hacspec_concordium.Concordium_traits in
  let open Hacspec_ovn.Ovn_traits in
  ()

type t_TallyParameter = | TallyParameter : t_TallyParameter

let sub
      (#v_Z: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Field v_Z)
      (x y: v_Z)
    : v_Z =
  Hacspec_ovn.Ovn_traits.f_add #v_Z
    #FStar.Tactics.Typeclasses.solve
    x
    (Hacspec_ovn.Ovn_traits.f_opp #v_Z #FStar.Tactics.Typeclasses.solve y <: v_Z)

let check_commitment
      (#v_G: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (g_pow_xi_yi_vi: v_G)
      (commitment: i1.f_Z)
    : bool =
  (Hacspec_ovn.Ovn_traits.f_hash #v_G
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #v_G
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list = [g_pow_xi_yi_vi] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                <:
                Alloc.Boxed.t_Box (t_Array v_G (sz 1)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice v_G) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec v_G Alloc.Alloc.t_Global)
    <:
    i1.f_Z) =.
  commitment

let commit_to
      (#v_G: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (g_pow_xi_yi_vi: v_G)
    : i1.f_Z =
  Hacspec_ovn.Ovn_traits.f_hash #v_G
    #FStar.Tactics.Typeclasses.solve
    (Alloc.Slice.impl__into_vec #v_G
        #Alloc.Alloc.t_Global
        (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list = [g_pow_xi_yi_vi] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              Alloc.Boxed.t_Box (t_Array v_G (sz 1)) Alloc.Alloc.t_Global)
          <:
          Alloc.Boxed.t_Box (t_Slice v_G) Alloc.Alloc.t_Global)
      <:
      Alloc.Vec.t_Vec v_G Alloc.Alloc.t_Global)

let compute_group_element_for_vote
      (#v_G: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (xi: i1.f_Z)
      (vote: bool)
      (g_pow_yi: v_G)
    : v_G =
  Hacspec_ovn.Ovn_traits.f_prod #v_G
    #FStar.Tactics.Typeclasses.solve
    (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve g_pow_yi xi <: v_G)
    (Hacspec_ovn.Ovn_traits.f_g_pow #v_G
        #FStar.Tactics.Typeclasses.solve
        (if vote
          then
            Hacspec_ovn.Ovn_traits.f_field_one #i1.f_Z #FStar.Tactics.Typeclasses.solve () <: i1.f_Z
          else
            Hacspec_ovn.Ovn_traits.f_field_zero #i1.f_Z #FStar.Tactics.Typeclasses.solve ()
            <:
            i1.f_Z)
      <:
      v_G)

let div
      (#v_G: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (x y: v_G)
    : v_G =
  Hacspec_ovn.Ovn_traits.f_prod #v_G
    #FStar.Tactics.Typeclasses.solve
    x
    (Hacspec_ovn.Ovn_traits.f_group_inv #v_G #FStar.Tactics.Typeclasses.solve y <: v_G)

let compute_g_pow_yi
      (#v_G: Type0)
      (n: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (i: usize)
      (xis: t_Array v_G n)
    : v_G =
  let prod1:v_G = Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve () in
  let prod1:v_G =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      i
      (fun prod1 temp_1_ ->
          let prod1:v_G = prod1 in
          let _:usize = temp_1_ in
          true)
      prod1
      (fun prod1 j ->
          let prod1:v_G = prod1 in
          let j:usize = j in
          Hacspec_ovn.Ovn_traits.f_prod #v_G
            #FStar.Tactics.Typeclasses.solve
            prod1
            (xis.[ j ] <: v_G)
          <:
          v_G)
  in
  let prod2:v_G = Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve () in
  let prod2:v_G =
    Rust_primitives.Hax.Folds.fold_range (i +! sz 1 <: usize)
      n
      (fun prod2 temp_1_ ->
          let prod2:v_G = prod2 in
          let _:usize = temp_1_ in
          true)
      prod2
      (fun prod2 j ->
          let prod2:v_G = prod2 in
          let j:usize = j in
          Hacspec_ovn.Ovn_traits.f_prod #v_G
            #FStar.Tactics.Typeclasses.solve
            prod2
            (xis.[ j ] <: v_G)
          <:
          v_G)
  in
  div #v_G prod1 prod2

type t_CastVoteParam (v_Z: Type0) {| i1: Hacspec_ovn.Ovn_traits.t_Field v_Z |} = {
  f_cvp_i:u32;
  f_cvp_xi:v_Z;
  f_cvp_zkp_random_w:v_Z;
  f_cvp_zkp_random_r:v_Z;
  f_cvp_zkp_random_d:v_Z;
  f_cvp_vote:bool
}

type t_OrZKPCommit (v_G: Type0) {| i1: Hacspec_ovn.Ovn_traits.t_Group v_G |} = {
  f_or_zkp_x:v_G;
  f_or_zkp_y:v_G;
  f_or_zkp_a1:v_G;
  f_or_zkp_b1:v_G;
  f_or_zkp_a2:v_G;
  f_or_zkp_b2:v_G;
  f_or_zkp_c:i1.f_Z;
  f_or_zkp_d1:i1.f_Z;
  f_or_zkp_d2:i1.f_Z;
  f_or_zkp_r1:i1.f_Z;
  f_or_zkp_r2:i1.f_Z
}

type t_RegisterParam (v_Z: Type0) {| i1: Hacspec_ovn.Ovn_traits.t_Field v_Z |} = {
  f_rp_i:u32;
  f_rp_xi:v_Z;
  f_rp_zkp_random:v_Z
}

type t_SchnorrZKPCommit (v_G: Type0) {| i1: Hacspec_ovn.Ovn_traits.t_Group v_G |} = {
  f_schnorr_zkp_u:v_G;
  f_schnorr_zkp_c:i1.f_Z;
  f_schnorr_zkp_z:i1.f_Z
}

(** Non-interactive Schnorr proof using Fiat-Shamir heuristics (RFC 8235) *)
let schnorr_zkp
      (#v_G: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (random: i1.f_Z)
      (h: v_G)
      (x: i1.f_Z)
    : t_SchnorrZKPCommit v_G =
  Rust_primitives.Hax.Control_flow_monad.Mexception.run (let r = random in
      let u:v_G = Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve r in
      let c =
        Hacspec_ovn.Ovn_traits.f_hash #v_G
          #FStar.Tactics.Typeclasses.solve
          (Alloc.Slice.impl__into_vec #v_G
              #Alloc.Alloc.t_Global
              (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                          [
                            Hacspec_ovn.Ovn_traits.f_g #v_G #FStar.Tactics.Typeclasses.solve ()
                            <:
                            v_G;
                            h;
                            u
                          ]
                        in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
                        Rust_primitives.Hax.array_of_list 3 list)
                    <:
                    Alloc.Boxed.t_Box (t_Array v_G (sz 3)) Alloc.Alloc.t_Global)
                <:
                Alloc.Boxed.t_Box (t_Slice v_G) Alloc.Alloc.t_Global)
            <:
            Alloc.Vec.t_Vec v_G Alloc.Alloc.t_Global)
      in
      let z =
        Hacspec_ovn.Ovn_traits.f_add #i1.f_Z
          #FStar.Tactics.Typeclasses.solve
          r
          (Hacspec_ovn.Ovn_traits.f_mul #i1.f_Z #FStar.Tactics.Typeclasses.solve c x <: i1.f_Z)
      in
      let! hoist9:Rust_primitives.Hax.t_Never =
        Core.Ops.Control_flow.ControlFlow_Break
        ({ f_schnorr_zkp_u = u; f_schnorr_zkp_c = c; f_schnorr_zkp_z = z } <: t_SchnorrZKPCommit v_G
        )
        <:
        Core.Ops.Control_flow.t_ControlFlow (t_SchnorrZKPCommit v_G) Rust_primitives.Hax.t_Never
      in
      Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist9)
      <:
      Core.Ops.Control_flow.t_ControlFlow (t_SchnorrZKPCommit v_G) (t_SchnorrZKPCommit v_G))

let schnorr_zkp_validate
      (#v_G: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (h: v_G)
      (pi: t_SchnorrZKPCommit v_G)
    : bool =
  pi.f_schnorr_zkp_c =.
  (Hacspec_ovn.Ovn_traits.f_hash #v_G
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #v_G
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        Hacspec_ovn.Ovn_traits.f_g #v_G #FStar.Tactics.Typeclasses.solve () <: v_G;
                        h;
                        pi.f_schnorr_zkp_u
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
                    Rust_primitives.Hax.array_of_list 3 list)
                <:
                Alloc.Boxed.t_Box (t_Array v_G (sz 3)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice v_G) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec v_G Alloc.Alloc.t_Global)
    <:
    i1.f_Z) &&
  (Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve pi.f_schnorr_zkp_z <: v_G) =.
  (Hacspec_ovn.Ovn_traits.f_prod #v_G
      #FStar.Tactics.Typeclasses.solve
      pi.f_schnorr_zkp_u
      (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve h pi.f_schnorr_zkp_c
        <:
        v_G)
    <:
    v_G)

(** Cramer, Damgård and Schoenmakers (CDS) technique *)
let zkp_one_out_of_two
      (#v_G: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (random_w random_r random_d: i1.f_Z)
      (h: v_G)
      (xi: i1.f_Z)
      (vi: bool)
    : t_OrZKPCommit v_G =
  let w = random_w in
  if vi
  then
    let r1 = random_r in
    let d1 = random_d in
    let x:v_G = Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve xi in
    let y:v_G =
      Hacspec_ovn.Ovn_traits.f_prod #v_G
        #FStar.Tactics.Typeclasses.solve
        (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve h xi <: v_G)
        (Hacspec_ovn.Ovn_traits.f_g #v_G #FStar.Tactics.Typeclasses.solve () <: v_G)
    in
    let a1:v_G =
      Hacspec_ovn.Ovn_traits.f_prod #v_G
        #FStar.Tactics.Typeclasses.solve
        (Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve r1 <: v_G)
        (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve x d1 <: v_G)
    in
    let b1:v_G =
      Hacspec_ovn.Ovn_traits.f_prod #v_G
        #FStar.Tactics.Typeclasses.solve
        (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve h r1 <: v_G)
        (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve y d1 <: v_G)
    in
    let a2:v_G = Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve w in
    let b2:v_G = Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve h w in
    let c =
      Hacspec_ovn.Ovn_traits.f_hash #v_G
        #FStar.Tactics.Typeclasses.solve
        (Alloc.Slice.impl__into_vec #v_G
            #Alloc.Alloc.t_Global
            (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                        [x; y; a1; b1; a2; b2]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 6);
                      Rust_primitives.Hax.array_of_list 6 list)
                  <:
                  Alloc.Boxed.t_Box (t_Array v_G (sz 6)) Alloc.Alloc.t_Global)
              <:
              Alloc.Boxed.t_Box (t_Slice v_G) Alloc.Alloc.t_Global)
          <:
          Alloc.Vec.t_Vec v_G Alloc.Alloc.t_Global)
    in
    let d2 = sub #i1.f_Z c d1 in
    let r2 =
      sub #i1.f_Z
        w
        (Hacspec_ovn.Ovn_traits.f_mul #i1.f_Z #FStar.Tactics.Typeclasses.solve xi d2 <: i1.f_Z)
    in
    {
      f_or_zkp_x = x;
      f_or_zkp_y = y;
      f_or_zkp_a1 = a1;
      f_or_zkp_b1 = b1;
      f_or_zkp_a2 = a2;
      f_or_zkp_b2 = b2;
      f_or_zkp_c = c;
      f_or_zkp_d1 = d1;
      f_or_zkp_d2 = d2;
      f_or_zkp_r1 = r1;
      f_or_zkp_r2 = r2
    }
    <:
    t_OrZKPCommit v_G
  else
    let r2 = random_r in
    let d2 = random_d in
    let x:v_G = Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve xi in
    let y:v_G = Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve h xi in
    let a1:v_G = Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve w in
    let b1:v_G = Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve h w in
    let a2:v_G =
      Hacspec_ovn.Ovn_traits.f_prod #v_G
        #FStar.Tactics.Typeclasses.solve
        (Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve r2 <: v_G)
        (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve x d2 <: v_G)
    in
    let b2:v_G =
      Hacspec_ovn.Ovn_traits.f_prod #v_G
        #FStar.Tactics.Typeclasses.solve
        (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve h r2 <: v_G)
        (Hacspec_ovn.Ovn_traits.f_pow #v_G
            #FStar.Tactics.Typeclasses.solve
            (div #v_G y (Hacspec_ovn.Ovn_traits.f_g #v_G #FStar.Tactics.Typeclasses.solve () <: v_G)
              <:
              v_G)
            d2
          <:
          v_G)
    in
    let c =
      Hacspec_ovn.Ovn_traits.f_hash #v_G
        #FStar.Tactics.Typeclasses.solve
        (Alloc.Slice.impl__into_vec #v_G
            #Alloc.Alloc.t_Global
            (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                        [x; y; a1; b1; a2; b2]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 6);
                      Rust_primitives.Hax.array_of_list 6 list)
                  <:
                  Alloc.Boxed.t_Box (t_Array v_G (sz 6)) Alloc.Alloc.t_Global)
              <:
              Alloc.Boxed.t_Box (t_Slice v_G) Alloc.Alloc.t_Global)
          <:
          Alloc.Vec.t_Vec v_G Alloc.Alloc.t_Global)
    in
    let d1 = sub #i1.f_Z c d2 in
    let r1 =
      sub #i1.f_Z
        w
        (Hacspec_ovn.Ovn_traits.f_mul #i1.f_Z #FStar.Tactics.Typeclasses.solve xi d1 <: i1.f_Z)
    in
    {
      f_or_zkp_x = x;
      f_or_zkp_y = y;
      f_or_zkp_a1 = a1;
      f_or_zkp_b1 = b1;
      f_or_zkp_a2 = a2;
      f_or_zkp_b2 = b2;
      f_or_zkp_c = c;
      f_or_zkp_d1 = d1;
      f_or_zkp_d2 = d2;
      f_or_zkp_r1 = r1;
      f_or_zkp_r2 = r2
    }
    <:
    t_OrZKPCommit v_G

let zkp_one_out_of_two_validate
      (#v_G: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (h: v_G)
      (zkp: t_OrZKPCommit v_G)
    : bool =
  let c =
    Hacspec_ovn.Ovn_traits.f_hash #v_G
      #FStar.Tactics.Typeclasses.solve
      (Alloc.Slice.impl__into_vec #v_G
          #Alloc.Alloc.t_Global
          (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                      [
                        zkp.f_or_zkp_x;
                        zkp.f_or_zkp_y;
                        zkp.f_or_zkp_a1;
                        zkp.f_or_zkp_b1;
                        zkp.f_or_zkp_a2;
                        zkp.f_or_zkp_b2
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 6);
                    Rust_primitives.Hax.array_of_list 6 list)
                <:
                Alloc.Boxed.t_Box (t_Array v_G (sz 6)) Alloc.Alloc.t_Global)
            <:
            Alloc.Boxed.t_Box (t_Slice v_G) Alloc.Alloc.t_Global)
        <:
        Alloc.Vec.t_Vec v_G Alloc.Alloc.t_Global)
  in
  c =.
  (Hacspec_ovn.Ovn_traits.f_add #i1.f_Z
      #FStar.Tactics.Typeclasses.solve
      zkp.f_or_zkp_d1
      zkp.f_or_zkp_d2
    <:
    i1.f_Z) &&
  zkp.f_or_zkp_a1 =.
  (Hacspec_ovn.Ovn_traits.f_prod #v_G
      #FStar.Tactics.Typeclasses.solve
      (Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve zkp.f_or_zkp_r1 <: v_G)
      (Hacspec_ovn.Ovn_traits.f_pow #v_G
          #FStar.Tactics.Typeclasses.solve
          zkp.f_or_zkp_x
          zkp.f_or_zkp_d1
        <:
        v_G)
    <:
    v_G) &&
  zkp.f_or_zkp_b1 =.
  (Hacspec_ovn.Ovn_traits.f_prod #v_G
      #FStar.Tactics.Typeclasses.solve
      (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve h zkp.f_or_zkp_r1 <: v_G)
      (Hacspec_ovn.Ovn_traits.f_pow #v_G
          #FStar.Tactics.Typeclasses.solve
          zkp.f_or_zkp_y
          zkp.f_or_zkp_d1
        <:
        v_G)
    <:
    v_G) &&
  zkp.f_or_zkp_a2 =.
  (Hacspec_ovn.Ovn_traits.f_prod #v_G
      #FStar.Tactics.Typeclasses.solve
      (Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve zkp.f_or_zkp_r2 <: v_G)
      (Hacspec_ovn.Ovn_traits.f_pow #v_G
          #FStar.Tactics.Typeclasses.solve
          zkp.f_or_zkp_x
          zkp.f_or_zkp_d2
        <:
        v_G)
    <:
    v_G) &&
  zkp.f_or_zkp_b2 =.
  (Hacspec_ovn.Ovn_traits.f_prod #v_G
      #FStar.Tactics.Typeclasses.solve
      (Hacspec_ovn.Ovn_traits.f_pow #v_G #FStar.Tactics.Typeclasses.solve h zkp.f_or_zkp_r2 <: v_G)
      (Hacspec_ovn.Ovn_traits.f_pow #v_G
          #FStar.Tactics.Typeclasses.solve
          (div #v_G
              zkp.f_or_zkp_y
              (Hacspec_ovn.Ovn_traits.f_g #v_G #FStar.Tactics.Typeclasses.solve () <: v_G)
            <:
            v_G)
          zkp.f_or_zkp_d2
        <:
        v_G)
    <:
    v_G)

type t_OvnContractState (v_G: Type0) (n: usize) {| i1: Hacspec_ovn.Ovn_traits.t_Group v_G |} = {
  f_g_pow_xis:t_Array v_G n;
  f_zkp_xis:t_Array (t_SchnorrZKPCommit v_G) n;
  f_commit_vis:t_Array i1.f_Z n;
  f_g_pow_xi_yi_vis:t_Array v_G n;
  f_zkp_vis:t_Array (t_OrZKPCommit v_G) n;
  f_tally:u32;
  f_round1:t_Array bool n
}

(** Primary function in round 2, also opens commitment *)
let cast_vote
      (#v_G: Type0)
      (n: usize)
      (#v_A #impl_574521470_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Hacspec_concordium.Concordium_traits.t_HasActions v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Hacspec_concordium.Concordium_traits.t_HasReceiveContext impl_574521470_ Prims.unit)
      (ctx: impl_574521470_)
      (state: t_OvnContractState v_G n)
    : Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError =
  let _, out:(_ &
    Core.Result.t_Result (t_CastVoteParam i3.f_Z) Concordium_contracts_common.Types.t_ParseError) =
    Concordium_contracts_common.Traits.f_get #_
      #(t_CastVoteParam i3.f_Z)
      #FStar.Tactics.Typeclasses.solve
      (Hacspec_concordium.Concordium_traits.f_parameter_cursor #impl_574521470_
          #FStar.Tactics.Typeclasses.solve
          ctx
        <:
        _)
  in
  match out with
  | Core.Result.Result_Ok (params: t_CastVoteParam i3.f_Z) ->
    let g_pow_yi:v_G =
      compute_g_pow_yi #v_G n (cast (params.f_cvp_i <: u32) <: usize) state.f_g_pow_xis
    in
    let g_pow_xi_yi_vi:v_G =
      compute_group_element_for_vote #v_G params.f_cvp_xi params.f_cvp_vote g_pow_yi
    in
    let zkp_vi:t_OrZKPCommit v_G =
      zkp_one_out_of_two #v_G
        params.f_cvp_zkp_random_w
        params.f_cvp_zkp_random_r
        params.f_cvp_zkp_random_d
        g_pow_yi
        params.f_cvp_xi
        params.f_cvp_vote
    in
    let cast_vote_state_ret:t_OvnContractState v_G n =
      Core.Clone.f_clone #(t_OvnContractState v_G n) #FStar.Tactics.Typeclasses.solve state
    in
    let cast_vote_state_ret:t_OvnContractState v_G n =
      {
        cast_vote_state_ret with
        f_g_pow_xi_yi_vis
        =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize cast_vote_state_ret
            .f_g_pow_xi_yi_vis
          (cast (params.f_cvp_i <: u32) <: usize)
          g_pow_xi_yi_vi
      }
      <:
      t_OvnContractState v_G n
    in
    let cast_vote_state_ret:t_OvnContractState v_G n =
      {
        cast_vote_state_ret with
        f_zkp_vis
        =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize cast_vote_state_ret.f_zkp_vis
          (cast (params.f_cvp_i <: u32) <: usize)
          zkp_vi
      }
      <:
      t_OvnContractState v_G n
    in
    Core.Result.Result_Ok
    (Hacspec_concordium.Concordium_traits.f_accept #v_A #FStar.Tactics.Typeclasses.solve (),
      cast_vote_state_ret
      <:
      (v_A & t_OvnContractState v_G n))
    <:
    Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError

(** Commitment before round 2 *)
let commit_to_vote
      (#v_G: Type0)
      (n: usize)
      (#v_A #impl_574521470_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Hacspec_concordium.Concordium_traits.t_HasActions v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Hacspec_concordium.Concordium_traits.t_HasReceiveContext impl_574521470_ Prims.unit)
      (ctx: impl_574521470_)
      (state: t_OvnContractState v_G n)
    : Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError =
  let _, out:(_ &
    Core.Result.t_Result (t_CastVoteParam i3.f_Z) Concordium_contracts_common.Types.t_ParseError) =
    Concordium_contracts_common.Traits.f_get #_
      #(t_CastVoteParam i3.f_Z)
      #FStar.Tactics.Typeclasses.solve
      (Hacspec_concordium.Concordium_traits.f_parameter_cursor #impl_574521470_
          #FStar.Tactics.Typeclasses.solve
          ctx
        <:
        _)
  in
  match out with
  | Core.Result.Result_Ok (params: t_CastVoteParam i3.f_Z) ->
    let _:Prims.unit =
      Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nLoop without mutation?"
        "{\n        for i in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n            f_start: 0,\n            f_end: n,\n        })) {\n            (if BinOp::Ast\n                .Or(\n                    core::ops::bit::Not::not(\n                        hacspec_ovn::ovn_group::schnorr_zkp_validate::<\n                            G,\n                        >(\n                            core::ops::index::Index::index(\n                                proj_hacspec_ovn::ovn_group::f_g_pow_xis(state),\n                                i,\n                            ),\n                            core::ops::index::Index::index(\n                                proj_hacspec_ovn::ovn_group::f_zkp_xis(state),\n                                i,\n                            ),\n                        ),\n                    ),\n                    core::ops::bit::Not::not(\n                        core::ops::index::Index::index(\n                            proj_hacspec_ovn::ovn_group::f_round1(state),\n                            i,\n                        ),\n                    ),\n                )\n            {\n                {\n                    #[note(\n                        \"rhs.typ=core::ops::control_flow::t_ControlFlow<core::result::t_Result<tuple2<A, hacspec_ovn::ovn_group::t_OvnContractState<G, generic_value!(todo)>>, concordium_contracts_common::types::t_ParseError>, rust_primitives::hax::t_Never>\"\n                    )]\n                    #[monadic_let(\n                        MException<core::result::t_Result<tuple2<A,\n                        hacspec_ovn::ovn_group::t_OvnContractState<G,\n                        generic_value!(todo)>>,\n                        concordium_contracts_common::types::t_ParseError>>\n                    )]\n                    let hoist12: rust_primitives::hax::t_Never = {\n                        core::ops::control_flow::ControlFlow_Break(\n                            core::result::Result_Err(\n                                concordium_contracts_common::types::ParseError(),\n                            ),\n                        )\n                    };\n                    core::ops::control_flow::ControlFlow_Continue(\n                        rust_primitives::hax::never_to_any(hoist12),\n                    )\n                }\n            } else {\n                core::ops::control_flow::ControlFlow_Continue(Tuple0)\n            })\n        }\n    }"

    in
    let g_pow_yi:v_G =
      compute_g_pow_yi #v_G n (cast (params.f_cvp_i <: u32) <: usize) state.f_g_pow_xis
    in
    let g_pow_xi_yi_vi:v_G =
      compute_group_element_for_vote #v_G params.f_cvp_xi params.f_cvp_vote g_pow_yi
    in
    let commit_vi = commit_to #v_G g_pow_xi_yi_vi in
    let commit_to_vote_state_ret:t_OvnContractState v_G n =
      Core.Clone.f_clone #(t_OvnContractState v_G n) #FStar.Tactics.Typeclasses.solve state
    in
    let commit_to_vote_state_ret:t_OvnContractState v_G n =
      {
        commit_to_vote_state_ret with
        f_commit_vis
        =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize commit_to_vote_state_ret
            .f_commit_vis
          (cast (params.f_cvp_i <: u32) <: usize)
          commit_vi
      }
      <:
      t_OvnContractState v_G n
    in
    Core.Result.Result_Ok
    (Hacspec_concordium.Concordium_traits.f_accept #v_A #FStar.Tactics.Typeclasses.solve (),
      commit_to_vote_state_ret
      <:
      (v_A & t_OvnContractState v_G n))
    <:
    Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError

let init_ovn_contract
      (#v_G: Type0)
      (n: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (_: Prims.unit)
    : Core.Result.t_Result (t_OvnContractState v_G n) Hacspec_concordium.Concordium_types.t_Reject =
  Core.Result.Result_Ok
  ({
      f_g_pow_xis
      =
      Rust_primitives.Hax.repeat (Hacspec_ovn.Ovn_traits.f_group_one #v_G
            #FStar.Tactics.Typeclasses.solve
            ()
          <:
          v_G)
        n;
      f_zkp_xis
      =
      Rust_primitives.Hax.repeat ({
            f_schnorr_zkp_u
            =
            Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve () <: v_G;
            f_schnorr_zkp_z
            =
            Hacspec_ovn.Ovn_traits.f_field_zero #i1.f_Z #FStar.Tactics.Typeclasses.solve ()
            <:
            i1.f_Z;
            f_schnorr_zkp_c
            =
            Hacspec_ovn.Ovn_traits.f_field_zero #i1.f_Z #FStar.Tactics.Typeclasses.solve ()
            <:
            i1.f_Z
          }
          <:
          t_SchnorrZKPCommit v_G)
        n;
      f_commit_vis
      =
      Rust_primitives.Hax.repeat (Hacspec_ovn.Ovn_traits.f_field_zero #i1.f_Z
            #FStar.Tactics.Typeclasses.solve
            ()
          <:
          i1.f_Z)
        n;
      f_g_pow_xi_yi_vis
      =
      Rust_primitives.Hax.repeat (Hacspec_ovn.Ovn_traits.f_group_one #v_G
            #FStar.Tactics.Typeclasses.solve
            ()
          <:
          v_G)
        n;
      f_zkp_vis
      =
      Rust_primitives.Hax.repeat ({
            f_or_zkp_x
            =
            Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve () <: v_G;
            f_or_zkp_y
            =
            Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve () <: v_G;
            f_or_zkp_a1
            =
            Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve () <: v_G;
            f_or_zkp_b1
            =
            Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve () <: v_G;
            f_or_zkp_a2
            =
            Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve () <: v_G;
            f_or_zkp_b2
            =
            Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve () <: v_G;
            f_or_zkp_c
            =
            Hacspec_ovn.Ovn_traits.f_field_zero #i1.f_Z #FStar.Tactics.Typeclasses.solve ()
            <:
            i1.f_Z;
            f_or_zkp_d1
            =
            Hacspec_ovn.Ovn_traits.f_field_zero #i1.f_Z #FStar.Tactics.Typeclasses.solve ()
            <:
            i1.f_Z;
            f_or_zkp_d2
            =
            Hacspec_ovn.Ovn_traits.f_field_zero #i1.f_Z #FStar.Tactics.Typeclasses.solve ()
            <:
            i1.f_Z;
            f_or_zkp_r1
            =
            Hacspec_ovn.Ovn_traits.f_field_zero #i1.f_Z #FStar.Tactics.Typeclasses.solve ()
            <:
            i1.f_Z;
            f_or_zkp_r2
            =
            Hacspec_ovn.Ovn_traits.f_field_zero #i1.f_Z #FStar.Tactics.Typeclasses.solve ()
            <:
            i1.f_Z
          }
          <:
          t_OrZKPCommit v_G)
        n;
      f_tally = 0ul;
      f_round1 = Rust_primitives.Hax.repeat false n
    }
    <:
    t_OvnContractState v_G n)
  <:
  Core.Result.t_Result (t_OvnContractState v_G n) Hacspec_concordium.Concordium_types.t_Reject

(** Primary function in round 1 *)
let register_vote
      (#v_G: Type0)
      (n: usize)
      (#v_A #impl_574521470_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Hacspec_concordium.Concordium_traits.t_HasActions v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Hacspec_concordium.Concordium_traits.t_HasReceiveContext impl_574521470_ Prims.unit)
      (ctx: impl_574521470_)
      (state: t_OvnContractState v_G n)
    : Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError =
  let _, out:(_ &
    Core.Result.t_Result (t_RegisterParam i3.f_Z) Concordium_contracts_common.Types.t_ParseError) =
    Concordium_contracts_common.Traits.f_get #_
      #(t_RegisterParam i3.f_Z)
      #FStar.Tactics.Typeclasses.solve
      (Hacspec_concordium.Concordium_traits.f_parameter_cursor #impl_574521470_
          #FStar.Tactics.Typeclasses.solve
          ctx
        <:
        _)
  in
  match out with
  | Core.Result.Result_Ok (params: t_RegisterParam i3.f_Z) ->
    let g_pow_xi:v_G =
      Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve params.f_rp_xi
    in
    let zkp_xi:t_SchnorrZKPCommit v_G =
      schnorr_zkp #v_G params.f_rp_zkp_random g_pow_xi params.f_rp_xi
    in
    let register_vote_state_ret:t_OvnContractState v_G n =
      Core.Clone.f_clone #(t_OvnContractState v_G n) #FStar.Tactics.Typeclasses.solve state
    in
    let register_vote_state_ret:t_OvnContractState v_G n =
      {
        register_vote_state_ret with
        f_g_pow_xis
        =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize register_vote_state_ret
            .f_g_pow_xis
          (cast (params.f_rp_i <: u32) <: usize)
          g_pow_xi
      }
      <:
      t_OvnContractState v_G n
    in
    let register_vote_state_ret:t_OvnContractState v_G n =
      {
        register_vote_state_ret with
        f_zkp_xis
        =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize register_vote_state_ret
            .f_zkp_xis
          (cast (params.f_rp_i <: u32) <: usize)
          zkp_xi
      }
      <:
      t_OvnContractState v_G n
    in
    let register_vote_state_ret:t_OvnContractState v_G n =
      {
        register_vote_state_ret with
        f_round1
        =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize register_vote_state_ret.f_round1
          (cast (params.f_rp_i <: u32) <: usize)
          true
      }
      <:
      t_OvnContractState v_G n
    in
    Core.Result.Result_Ok
    (Hacspec_concordium.Concordium_traits.f_accept #v_A #FStar.Tactics.Typeclasses.solve (),
      register_vote_state_ret
      <:
      (v_A & t_OvnContractState v_G n))
    <:
    Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError

(** Anyone can tally the votes *)
let tally_votes
      (#v_G: Type0)
      (n: usize)
      (#v_A: Type0)
      (#impl_574521470_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Hacspec_ovn.Ovn_traits.t_Group v_G)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i4:
          Hacspec_concordium.Concordium_traits.t_HasActions v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i5:
          Hacspec_concordium.Concordium_traits.t_HasReceiveContext impl_574521470_ Prims.unit)
      (_: impl_574521470_)
      (state: t_OvnContractState v_G n)
    : Core.Result.t_Result (v_A & t_OvnContractState v_G n)
      Concordium_contracts_common.Types.t_ParseError =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nLoop without mutation?"
      "{\n        for i in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n            f_start: 0,\n            f_end: n,\n        })) {\n            {\n                let g_pow_yi: G = {\n                    hacspec_ovn::ovn_group::compute_g_pow_yi::<\n                        G,\n                        generic_value!(todo),\n                    >(i, proj_hacspec_ovn::ovn_group::f_g_pow_xis(state))\n                };\n                {\n                    #[note(\n                        \"rhs.typ=core::ops::control_flow::t_ControlFlow<core::result::t_Result<tuple2<A, hacspec_ovn::ovn_group::t_OvnContractState<G, generic_value!(todo)>>, concordium_contracts_common::types::t_ParseError>, core::ops::control_flow::t_ControlFlow<core::result::t_Result<tuple2<A, hacspec_ovn::ovn_group::t_OvnContractState<G, generic_value!(todo)>>, concordium_contracts_common::types::t_ParseError>, tuple0>>\"\n                    )]\n                    #[monadic_let(\n                        MException<core::result::t_Result<tuple2<A,\n                        hacspec_ovn::ovn_group::t_OvnContractState<G,\n                        generic_value!(todo)>>,\n                        concordium_contracts_common::types::t_ParseError>>\n                    )]\n                    let _: tuple0 = {\n                        core::ops::control_flow::ControlFlow_Continue(\n                            (if core::ops::bit::Not::not(\n                                hacspec_ovn::ovn_group::zkp_one_out_of_two_validate::<\n                                    G,\n                                >(\n                                    g_pow_yi,\n                                    core::ops::index::Index::index(\n                                        proj_hacspec_ovn::ovn_group::f_zkp_vis(state),\n                                        i,\n                                    ),\n                                ),\n                            ) {\n                                {\n                                    #[note(\n                                        \"rhs.typ=core::ops::control_flow::t_ControlFlow<core::result::t_Result<tuple2<A, hacspec_ovn::ovn_group::t_OvnContractState<G, generic_value!(todo)>>, concordium_contracts_common::types::t_ParseError>, rust_primitives::hax::t_Never>\"\n                                    )]\n                                    #[monadic_let(\n                                        MException<core::result::t_Result<tuple2<A,\n                                        hacspec_ovn::ovn_group::t_OvnContractState<G,\n                                        generic_value!(todo)>>,\n                                        concordium_contracts_common::types::t_ParseError>>\n                                    )]\n                                    let hoist13: rust_primitives::hax::t_Never = {\n                                        core::ops::control_flow::ControlFlow_Break(\n                                            core::result::Result_Err(\n                                                concordium_contracts_common::types::ParseError(),\n                                            ),\n                                        )\n                                    };\n                                    core::ops::control_flow::ControlFlow_Continue(\n                                        rust_primitives::hax::never_to_any(hoist13),\n                                    )\n                                }\n                            } else {\n                                core::ops::control_flow::ControlFlow_Continue(Tuple0)\n                            }),\n                        )\n                    };\n                    (if core::ops::bit::Not::not(\n                        hacspec_ovn::ovn_group::check_commitment::<\n                            G,\n                        >(\n                            core::ops::index::Index::index(\n                                proj_hacspec_ovn::ovn_group::f_g_pow_xi_yi_vis(state),\n                                i,\n                            ),\n                            core::ops::index::Index::index(\n                                proj_hacspec_ovn::ovn_group::f_commit_vis(state),\n                                i,\n                            ),\n                        ),\n                    ) {\n                        {\n                            #[note(\n                                \"rhs.typ=core::ops::control_flow::t_ControlFlow<core::result::t_Result<tuple2<A, hacspec_ovn::ovn_group::t_OvnContractState<G, generic_value!(todo)>>, concordium_contracts_common::types::t_ParseError>, rust_primitives::hax::t_Never>\"\n                            )]\n                            #[monadic_let(\n                                MException<core::result::t_Result<tuple2<A,\n                                hacspec_ovn::ovn_group::t_OvnContractState<G,\n                                generic_value!(todo)>>,\n                                concordium_contracts_common::types::t_ParseError>>\n                            )]\n                            let hoist14: rust_primitives::hax::t_Never = {\n                                core::ops::control_flow::ControlFlow_Break(\n                                    core::result::Result_Err(\n                                        concordium_contracts_common::types::ParseError(),\n                                    ),\n                                )\n                            };\n                            core::ops::control_flow::ControlFlow_Continue(\n                                rust_primitives::hax::never_to_any(hoist14),\n                            )\n                        }\n                    } else {\n                        core::ops::control_flow::ControlFlow_Continue(Tuple0)\n                    })\n                }\n            }\n        }\n    }"

  in
  let vote_result:v_G =
    Hacspec_ovn.Ovn_traits.f_group_one #v_G #FStar.Tactics.Typeclasses.solve ()
  in
  let vote_result:v_G =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Array v_G n)
          #FStar.Tactics.Typeclasses.solve
          state.f_g_pow_xi_yi_vis
        <:
        Core.Array.Iter.t_IntoIter v_G n)
      vote_result
      (fun vote_result g_pow_vote ->
          let vote_result:v_G = vote_result in
          let g_pow_vote:v_G = g_pow_vote in
          Hacspec_ovn.Ovn_traits.f_prod #v_G #FStar.Tactics.Typeclasses.solve vote_result g_pow_vote
          <:
          v_G)
  in
  let tally:u32 = 0ul in
  let curr = Hacspec_ovn.Ovn_traits.f_field_zero #i3.f_Z #FStar.Tactics.Typeclasses.solve () in
  let curr, tally:(i3.f_Z & u32) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (cast (n <: usize) <: u32)
      (fun temp_0_ temp_1_ ->
          let curr, tally:(i3.f_Z & u32) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (curr, tally <: (i3.f_Z & u32))
      (fun temp_0_ i ->
          let curr, tally:(i3.f_Z & u32) = temp_0_ in
          let i:u32 = i in
          let tally:u32 =
            if
              (Hacspec_ovn.Ovn_traits.f_g_pow #v_G #FStar.Tactics.Typeclasses.solve curr <: v_G) =.
              vote_result
            then
              let tally:u32 = i in
              tally
            else tally
          in
          let curr =
            Hacspec_ovn.Ovn_traits.f_add #i3.f_Z
              #FStar.Tactics.Typeclasses.solve
              curr
              (Hacspec_ovn.Ovn_traits.f_field_one #i3.f_Z #FStar.Tactics.Typeclasses.solve ()
                <:
                i3.f_Z)
          in
          curr, tally <: (i3.f_Z & u32))
  in
  let tally_votes_state_ret:t_OvnContractState v_G n =
    Core.Clone.f_clone #(t_OvnContractState v_G n) #FStar.Tactics.Typeclasses.solve state
  in
  let tally_votes_state_ret:t_OvnContractState v_G n =
    { tally_votes_state_ret with f_tally = tally } <: t_OvnContractState v_G n
  in
  Core.Result.Result_Ok
  (Hacspec_concordium.Concordium_traits.f_accept #v_A #FStar.Tactics.Typeclasses.solve (),
    tally_votes_state_ret
    <:
    (v_A & t_OvnContractState v_G n))
  <:
  Core.Result.t_Result (v_A & t_OvnContractState v_G n)
    Concordium_contracts_common.Types.t_ParseError
