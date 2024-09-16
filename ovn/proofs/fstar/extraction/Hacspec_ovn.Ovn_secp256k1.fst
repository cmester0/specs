module Hacspec_ovn.Ovn_secp256k1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Concordium_contracts_common.Impls in
  let open Concordium_contracts_common.Traits in
  let open Hacspec_bip_340 in
  let open Hacspec_lib.Seq in
  let open Hacspec_ovn.Ovn_traits in
  ()

type t_Group_curve = { f_g_val:Hacspec_bip_340.t_Point }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Concordium_contracts_common.Traits.t_Deserial t_Group_curve =
  {
    f_deserial_pre
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Concordium_contracts_common.Traits.t_Read v_R)
        (source: v_R)
        ->
        true);
    f_deserial_post
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Concordium_contracts_common.Traits.t_Read v_R)
        (source: v_R)
        (out1:
          (v_R & Core.Result.t_Result t_Group_curve Concordium_contracts_common.Types.t_ParseError))
        ->
        true);
    f_deserial
    =
    fun
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Concordium_contracts_common.Traits.t_Read v_R)
      (source: v_R)
      ->
      let tmp0, out:(v_R & Core.Result.t_Result bool Concordium_contracts_common.Types.t_ParseError)
      =
        Concordium_contracts_common.Traits.f_get #v_R #bool #FStar.Tactics.Typeclasses.solve source
      in
      let source:v_R = tmp0 in
      match out with
      | Core.Result.Result_Ok (b: bool) ->
        let source, hax_temp_output:(v_R &
          Core.Result.t_Result t_Group_curve Concordium_contracts_common.Types.t_ParseError) =
          if b
          then
            let tmp0, out:(v_R &
              Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                Concordium_contracts_common.Types.t_ParseError) =
              Concordium_contracts_common.Traits.f_get #v_R
                #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                source
            in
            let source:v_R = tmp0 in
            match out with
            | Core.Result.Result_Ok (vx: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
              let tmp0, out:(v_R &
                Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  Concordium_contracts_common.Types.t_ParseError) =
                Concordium_contracts_common.Traits.f_get #v_R
                  #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  source
              in
              let source:v_R = tmp0 in
              (match out with
                | Core.Result.Result_Ok (vy: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
                  source,
                  (Core.Result.Result_Ok
                    ({
                        f_g_val
                        =
                        Hacspec_bip_340.Point_Affine
                        (Hacspec_bip_340.impl__FieldElement__from_public_byte_seq_be #(Hacspec_lib.Seq.t_Seq
                              u8)
                            (Hacspec_lib.Seq.impl_52__from_vec #u8 vx <: Hacspec_lib.Seq.t_Seq u8),
                          Hacspec_bip_340.impl__FieldElement__from_public_byte_seq_be #(Hacspec_lib.Seq.t_Seq
                              u8)
                            (Hacspec_lib.Seq.impl_52__from_vec #u8 vy <: Hacspec_lib.Seq.t_Seq u8)
                          <:
                          (Hacspec_bip_340.t_FieldElement & Hacspec_bip_340.t_FieldElement))
                        <:
                        Hacspec_bip_340.t_Point
                      }
                      <:
                      t_Group_curve)
                    <:
                    Core.Result.t_Result t_Group_curve
                      Concordium_contracts_common.Types.t_ParseError)
                  <:
                  (v_R &
                    Core.Result.t_Result t_Group_curve
                      Concordium_contracts_common.Types.t_ParseError)
                | Core.Result.Result_Err err ->
                  source,
                  (Core.Ops.Control_flow.ControlFlow_Break
                    (source,
                      (Core.Result.Result_Err err
                        <:
                        Core.Result.t_Result t_Group_curve
                          Concordium_contracts_common.Types.t_ParseError)
                      <:
                      (v_R &
                        Core.Result.t_Result t_Group_curve
                          Concordium_contracts_common.Types.t_ParseError))
                    <:
                    Core.Ops.Control_flow.t_ControlFlow
                      (v_R &
                        Core.Result.t_Result t_Group_curve
                          Concordium_contracts_common.Types.t_ParseError)
                      (Core.Result.t_Result t_Group_curve
                          Concordium_contracts_common.Types.t_ParseError))
                  <:
                  (v_R &
                    Core.Result.t_Result t_Group_curve
                      Concordium_contracts_common.Types.t_ParseError))
            | Core.Result.Result_Err err ->
              source,
              (Core.Ops.Control_flow.ControlFlow_Break
                (source,
                  (Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result t_Group_curve
                      Concordium_contracts_common.Types.t_ParseError)
                  <:
                  (v_R &
                    Core.Result.t_Result t_Group_curve
                      Concordium_contracts_common.Types.t_ParseError))
                <:
                Core.Ops.Control_flow.t_ControlFlow
                  (v_R &
                    Core.Result.t_Result t_Group_curve
                      Concordium_contracts_common.Types.t_ParseError)
                  (Core.Result.t_Result t_Group_curve Concordium_contracts_common.Types.t_ParseError
                  ))
              <:
              (v_R &
                Core.Result.t_Result t_Group_curve Concordium_contracts_common.Types.t_ParseError)
          else
            source,
            (Core.Result.Result_Ok
              ({ f_g_val = Hacspec_bip_340.Point_AtInfinity <: Hacspec_bip_340.t_Point }
                <:
                t_Group_curve)
              <:
              Core.Result.t_Result t_Group_curve Concordium_contracts_common.Types.t_ParseError)
            <:
            (v_R & Core.Result.t_Result t_Group_curve Concordium_contracts_common.Types.t_ParseError
            )
        in
        source, hax_temp_output
        <:
        (v_R & Core.Result.t_Result t_Group_curve Concordium_contracts_common.Types.t_ParseError)
      | Core.Result.Result_Err err ->
        source,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result t_Group_curve Concordium_contracts_common.Types.t_ParseError)
        <:
        (v_R & Core.Result.t_Result t_Group_curve Concordium_contracts_common.Types.t_ParseError)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Concordium_contracts_common.Traits.t_Serial t_Group_curve =
  {
    f_serial_pre
    =
    (fun
        (#v_W: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Concordium_contracts_common.Traits.t_Write v_W)
        (self: t_Group_curve)
        (out: v_W)
        ->
        true);
    f_serial_post
    =
    (fun
        (#v_W: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Concordium_contracts_common.Traits.t_Write v_W)
        (self: t_Group_curve)
        (out: v_W)
        (out2: (v_W & Core.Result.t_Result Prims.unit i1.f_Err))
        ->
        true);
    f_serial
    =
    fun
      (#v_W: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Concordium_contracts_common.Traits.t_Write v_W)
      (self: t_Group_curve)
      (out: v_W)
      ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let! out:v_W =
            match self.f_g_val with
            | Hacspec_bip_340.Point_Affine p ->
              let tmp0, out1:(v_W & Core.Result.t_Result Prims.unit i1.f_Err) =
                Concordium_contracts_common.Traits.f_serial #bool
                  #FStar.Tactics.Typeclasses.solve
                  #v_W
                  true
                  out
              in
              let out:v_W = tmp0 in
              (match out1 with
                | Core.Result.Result_Ok _ ->
                  let (vx: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u8
                    Alloc.Alloc.t_Global =
                    Alloc.Vec.impl__new #u8 ()
                  in
                  let vx:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
                    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Slice
                            u8)
                          #FStar.Tactics.Typeclasses.solve
                          (Hacspec_lib.Seq.impl_41__native_slice #u8
                              (Hacspec_bip_340.impl__FieldElement__to_public_byte_seq_be (Hacspec_bip_340.x
                                      p
                                    <:
                                    Hacspec_bip_340.t_FieldElement)
                                <:
                                Hacspec_lib.Seq.t_Seq u8)
                            <:
                            t_Slice u8)
                        <:
                        Core.Slice.Iter.t_Iter u8)
                      vx
                      (fun vx x ->
                          let vx:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = vx in
                          let x:u8 = x in
                          Alloc.Vec.impl_1__push #u8
                            #Alloc.Alloc.t_Global
                            vx
                            (Core.Clone.f_clone #u8 #FStar.Tactics.Typeclasses.solve x <: u8)
                          <:
                          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  in
                  let tmp0, out1:(v_W & Core.Result.t_Result Prims.unit i1.f_Err) =
                    Concordium_contracts_common.Traits.f_serial #(Alloc.Vec.t_Vec u8
                          Alloc.Alloc.t_Global)
                      #FStar.Tactics.Typeclasses.solve
                      #v_W
                      vx
                      out
                  in
                  let out:v_W = tmp0 in
                  (match out1 with
                    | Core.Result.Result_Ok _ ->
                      let (vy: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u8
                        Alloc.Alloc.t_Global =
                        Alloc.Vec.impl__new #u8 ()
                      in
                      let vy:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
                        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Slice
                                u8)
                              #FStar.Tactics.Typeclasses.solve
                              (Hacspec_lib.Seq.impl_41__native_slice #u8
                                  (Hacspec_bip_340.impl__FieldElement__to_public_byte_seq_be (Hacspec_bip_340.y
                                          p
                                        <:
                                        Hacspec_bip_340.t_FieldElement)
                                    <:
                                    Hacspec_lib.Seq.t_Seq u8)
                                <:
                                t_Slice u8)
                            <:
                            Core.Slice.Iter.t_Iter u8)
                          vy
                          (fun vy y ->
                              let vy:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = vy in
                              let y:u8 = y in
                              Alloc.Vec.impl_1__push #u8
                                #Alloc.Alloc.t_Global
                                vy
                                (Core.Clone.f_clone #u8 #FStar.Tactics.Typeclasses.solve y <: u8)
                              <:
                              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                      in
                      let tmp0, out1:(v_W & Core.Result.t_Result Prims.unit i1.f_Err) =
                        Concordium_contracts_common.Traits.f_serial #(Alloc.Vec.t_Vec u8
                              Alloc.Alloc.t_Global)
                          #FStar.Tactics.Typeclasses.solve
                          #v_W
                          vy
                          out
                      in
                      let out:v_W = tmp0 in
                      (match out1 with
                        | Core.Result.Result_Ok _ ->
                          Core.Ops.Control_flow.ControlFlow_Continue out
                          <:
                          Core.Ops.Control_flow.t_ControlFlow
                            (v_W & Core.Result.t_Result Prims.unit i1.f_Err) v_W
                        | Core.Result.Result_Err err ->
                          let! _:Prims.unit =
                            Core.Ops.Control_flow.ControlFlow_Break
                            (out,
                              (Core.Result.Result_Err err
                                <:
                                Core.Result.t_Result Prims.unit i1.f_Err)
                              <:
                              (v_W & Core.Result.t_Result Prims.unit i1.f_Err))
                            <:
                            Core.Ops.Control_flow.t_ControlFlow
                              (v_W & Core.Result.t_Result Prims.unit i1.f_Err) Prims.unit
                          in
                          Core.Ops.Control_flow.ControlFlow_Continue out
                          <:
                          Core.Ops.Control_flow.t_ControlFlow
                            (v_W & Core.Result.t_Result Prims.unit i1.f_Err) v_W)
                    | Core.Result.Result_Err err ->
                      let! _:Prims.unit =
                        Core.Ops.Control_flow.ControlFlow_Break
                        (out,
                          (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit i1.f_Err)
                          <:
                          (v_W & Core.Result.t_Result Prims.unit i1.f_Err))
                        <:
                        Core.Ops.Control_flow.t_ControlFlow
                          (v_W & Core.Result.t_Result Prims.unit i1.f_Err) Prims.unit
                      in
                      Core.Ops.Control_flow.ControlFlow_Continue out
                      <:
                      Core.Ops.Control_flow.t_ControlFlow
                        (v_W & Core.Result.t_Result Prims.unit i1.f_Err) v_W)
                | Core.Result.Result_Err err ->
                  let! _:Prims.unit =
                    Core.Ops.Control_flow.ControlFlow_Break
                    (out, (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit i1.f_Err)
                      <:
                      (v_W & Core.Result.t_Result Prims.unit i1.f_Err))
                    <:
                    Core.Ops.Control_flow.t_ControlFlow
                      (v_W & Core.Result.t_Result Prims.unit i1.f_Err) Prims.unit
                  in
                  Core.Ops.Control_flow.ControlFlow_Continue out
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (v_W & Core.Result.t_Result Prims.unit i1.f_Err) v_W)
            | Hacspec_bip_340.Point_AtInfinity  ->
              let tmp0, out1:(v_W & Core.Result.t_Result Prims.unit i1.f_Err) =
                Concordium_contracts_common.Traits.f_serial #bool
                  #FStar.Tactics.Typeclasses.solve
                  #v_W
                  false
                  out
              in
              let out:v_W = tmp0 in
              match out1 with
              | Core.Result.Result_Ok _ ->
                Core.Ops.Control_flow.ControlFlow_Continue out
                <:
                Core.Ops.Control_flow.t_ControlFlow (v_W & Core.Result.t_Result Prims.unit i1.f_Err)
                  v_W
              | Core.Result.Result_Err err ->
                let! _:Prims.unit =
                  Core.Ops.Control_flow.ControlFlow_Break
                  (out, (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit i1.f_Err)
                    <:
                    (v_W & Core.Result.t_Result Prims.unit i1.f_Err))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (v_W & Core.Result.t_Result Prims.unit i1.f_Err) Prims.unit
                in
                Core.Ops.Control_flow.ControlFlow_Continue out
                <:
                Core.Ops.Control_flow.t_ControlFlow (v_W & Core.Result.t_Result Prims.unit i1.f_Err)
                  v_W
          in
          Core.Ops.Control_flow.ControlFlow_Continue
          (let hax_temp_output:Core.Result.t_Result Prims.unit i1.f_Err =
              Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit i1.f_Err
            in
            out, hax_temp_output <: (v_W & Core.Result.t_Result Prims.unit i1.f_Err))
          <:
          Core.Ops.Control_flow.t_ControlFlow (v_W & Core.Result.t_Result Prims.unit i1.f_Err)
            (v_W & Core.Result.t_Result Prims.unit i1.f_Err))
  }

type t_Z_curve = { f_z_val:Hacspec_bip_340.t_Scalar }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Concordium_contracts_common.Traits.t_Deserial t_Z_curve =
  {
    f_deserial_pre
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Concordium_contracts_common.Traits.t_Read v_R)
        (source: v_R)
        ->
        true);
    f_deserial_post
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Concordium_contracts_common.Traits.t_Read v_R)
        (source: v_R)
        (out1:
          (v_R & Core.Result.t_Result t_Z_curve Concordium_contracts_common.Types.t_ParseError))
        ->
        true);
    f_deserial
    =
    fun
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Concordium_contracts_common.Traits.t_Read v_R)
      (source: v_R)
      ->
      let tmp0, out:(v_R &
        Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          Concordium_contracts_common.Types.t_ParseError) =
        Concordium_contracts_common.Traits.f_get #v_R
          #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          source
      in
      let source:v_R = tmp0 in
      match out with
      | Core.Result.Result_Ok (temp: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) ->
        let hax_temp_output:Core.Result.t_Result t_Z_curve
          Concordium_contracts_common.Types.t_ParseError =
          Core.Result.Result_Ok
          ({
              f_z_val
              =
              Hacspec_bip_340.impl__Scalar__from_public_byte_seq_be #(Hacspec_lib.Seq.t_Seq u8)
                (Hacspec_lib.Seq.impl_52__from_vec #u8 temp <: Hacspec_lib.Seq.t_Seq u8)
            }
            <:
            t_Z_curve)
          <:
          Core.Result.t_Result t_Z_curve Concordium_contracts_common.Types.t_ParseError
        in
        source, hax_temp_output
        <:
        (v_R & Core.Result.t_Result t_Z_curve Concordium_contracts_common.Types.t_ParseError)
      | Core.Result.Result_Err err ->
        source,
        (Core.Result.Result_Err err
          <:
          Core.Result.t_Result t_Z_curve Concordium_contracts_common.Types.t_ParseError)
        <:
        (v_R & Core.Result.t_Result t_Z_curve Concordium_contracts_common.Types.t_ParseError)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Concordium_contracts_common.Traits.t_Serial t_Z_curve =
  {
    f_serial_pre
    =
    (fun
        (#v_W: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Concordium_contracts_common.Traits.t_Write v_W)
        (self: t_Z_curve)
        (out: v_W)
        ->
        true);
    f_serial_post
    =
    (fun
        (#v_W: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Concordium_contracts_common.Traits.t_Write v_W)
        (self: t_Z_curve)
        (out: v_W)
        (out2: (v_W & Core.Result.t_Result Prims.unit i1.f_Err))
        ->
        true);
    f_serial
    =
    fun
      (#v_W: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Concordium_contracts_common.Traits.t_Write v_W)
      (self: t_Z_curve)
      (out: v_W)
      ->
      let (v: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Alloc.Vec.impl__new #u8 ()
      in
      let v:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Slice u8)
              #FStar.Tactics.Typeclasses.solve
              (Hacspec_lib.Seq.impl_41__native_slice #u8
                  (Hacspec_bip_340.impl__Scalar__to_public_byte_seq_be self.f_z_val
                    <:
                    Hacspec_lib.Seq.t_Seq u8)
                <:
                t_Slice u8)
            <:
            Core.Slice.Iter.t_Iter u8)
          v
          (fun v x ->
              let v:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = v in
              let x:u8 = x in
              Alloc.Vec.impl_1__push #u8
                #Alloc.Alloc.t_Global
                v
                (Core.Clone.f_clone #u8 #FStar.Tactics.Typeclasses.solve x <: u8)
              <:
              Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      in
      let tmp0, out1:(v_W & Core.Result.t_Result Prims.unit i1.f_Err) =
        Concordium_contracts_common.Traits.f_serial #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          #v_W
          v
          out
      in
      let out:v_W = tmp0 in
      let hax_temp_output:Core.Result.t_Result Prims.unit i1.f_Err = out1 in
      out, hax_temp_output <: (v_W & Core.Result.t_Result Prims.unit i1.f_Err)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Hacspec_ovn.Ovn_traits.t_Field t_Z_curve =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_12632649257025169145 = FStar.Tactics.Typeclasses.solve;
    _super_8099741844003281729 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_17605656595743636193 = FStar.Tactics.Typeclasses.solve;
    f_q_pre = (fun (_: Prims.unit) -> true);
    f_q_post = (fun (_: Prims.unit) (out: t_Z_curve) -> true);
    f_q
    =
    (fun (_: Prims.unit) ->
        {
          f_z_val
          =
          Hacspec_bip_340.impl__Scalar__from_hex "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"

        }
        <:
        t_Z_curve);
    f_random_field_elem_pre = (fun (random: u32) -> true);
    f_random_field_elem_post = (fun (random: u32) (out: t_Z_curve) -> true);
    f_random_field_elem
    =
    (fun (random: u32) ->
        { f_z_val = Hacspec_bip_340.impl__Scalar__from_literal (cast (random <: u32) <: u128) }
        <:
        t_Z_curve);
    f_field_zero_pre = (fun (_: Prims.unit) -> true);
    f_field_zero_post = (fun (_: Prims.unit) (out: t_Z_curve) -> true);
    f_field_zero
    =
    (fun (_: Prims.unit) ->
        { f_z_val = Hacspec_bip_340.impl__Scalar__from_literal (pub_u128 0) } <: t_Z_curve);
    f_field_one_pre = (fun (_: Prims.unit) -> true);
    f_field_one_post = (fun (_: Prims.unit) (out: t_Z_curve) -> true);
    f_field_one
    =
    (fun (_: Prims.unit) ->
        { f_z_val = Hacspec_bip_340.impl__Scalar__from_literal (pub_u128 1) } <: t_Z_curve);
    f_add_pre = (fun (x: t_Z_curve) (y: t_Z_curve) -> true);
    f_add_post = (fun (x: t_Z_curve) (y: t_Z_curve) (out: t_Z_curve) -> true);
    f_add = (fun (x: t_Z_curve) (y: t_Z_curve) -> { f_z_val = x.f_z_val +! y.f_z_val } <: t_Z_curve);
    f_opp_pre = (fun (x: t_Z_curve) -> true);
    f_opp_post = (fun (x: t_Z_curve) (out: t_Z_curve) -> true);
    f_opp
    =
    (fun (x: t_Z_curve) ->
        {
          f_z_val
          =
          (Hacspec_ovn.Ovn_traits.f_field_zero #t_Z_curve #FStar.Tactics.Typeclasses.solve ()
            <:
            t_Z_curve)
            .f_z_val -!
          x.f_z_val
        }
        <:
        t_Z_curve);
    f_mul_pre = (fun (x: t_Z_curve) (y: t_Z_curve) -> true);
    f_mul_post = (fun (x: t_Z_curve) (y: t_Z_curve) (out: t_Z_curve) -> true);
    f_mul = (fun (x: t_Z_curve) (y: t_Z_curve) -> { f_z_val = x.f_z_val *! y.f_z_val } <: t_Z_curve);
    f_inv_pre = (fun (x: t_Z_curve) -> true);
    f_inv_post = (fun (x: t_Z_curve) (out: t_Z_curve) -> true);
    f_inv
    =
    fun (x: t_Z_curve) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _:Prims.unit =
            Hax_lib.v_assert false
          in
          let! hoist10:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow_Break x
            <:
            Core.Ops.Control_flow.t_ControlFlow t_Z_curve Rust_primitives.Hax.t_Never
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist10)
          <:
          Core.Ops.Control_flow.t_ControlFlow t_Z_curve t_Z_curve)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Hacspec_ovn.Ovn_traits.t_Group t_Group_curve =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_12632649257025169145 = FStar.Tactics.Typeclasses.solve;
    _super_8099741844003281729 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_17605656595743636193 = FStar.Tactics.Typeclasses.solve;
    f_Z = t_Z_curve;
    f_Z_5568683927164688039 = FStar.Tactics.Typeclasses.solve;
    f_g_pre = (fun (_: Prims.unit) -> true);
    f_g_post = (fun (_: Prims.unit) (out: t_Group_curve) -> true);
    f_g
    =
    (fun (_: Prims.unit) ->
        let gx:Hacspec_bip_340.t_PBytes32 =
          Hacspec_bip_340.PBytes32
          (let list =
              [
                121uy; 190uy; 102uy; 126uy; 249uy; 220uy; 187uy; 172uy; 85uy; 160uy; 98uy; 149uy;
                206uy; 135uy; 11uy; 7uy; 2uy; 155uy; 252uy; 219uy; 45uy; 206uy; 40uy; 217uy; 89uy;
                242uy; 129uy; 91uy; 22uy; 248uy; 23uy; 152uy
              ]
            in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
            Rust_primitives.Hax.array_of_list 32 list)
          <:
          Hacspec_bip_340.t_PBytes32
        in
        let gy:Hacspec_bip_340.t_PBytes32 =
          Hacspec_bip_340.PBytes32
          (let list =
              [
                72uy; 58uy; 218uy; 119uy; 38uy; 163uy; 196uy; 101uy; 93uy; 164uy; 251uy; 252uy; 14uy;
                17uy; 8uy; 168uy; 253uy; 23uy; 180uy; 72uy; 166uy; 133uy; 84uy; 25uy; 156uy; 71uy;
                208uy; 143uy; 251uy; 16uy; 212uy; 184uy
              ]
            in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 32);
            Rust_primitives.Hax.array_of_list 32 list)
          <:
          Hacspec_bip_340.t_PBytes32
        in
        {
          f_g_val
          =
          Hacspec_bip_340.Point_Affine
          (Hacspec_bip_340.impl__FieldElement__from_public_byte_seq_be #Hacspec_bip_340.t_PBytes32
              gx,
            Hacspec_bip_340.impl__FieldElement__from_public_byte_seq_be #Hacspec_bip_340.t_PBytes32
              gy
            <:
            (Hacspec_bip_340.t_FieldElement & Hacspec_bip_340.t_FieldElement))
          <:
          Hacspec_bip_340.t_Point
        }
        <:
        t_Group_curve);
    f_pow_pre = (fun (g: t_Group_curve) (x: t_Z_curve) -> true);
    f_pow_post = (fun (g: t_Group_curve) (x: t_Z_curve) (out: t_Group_curve) -> true);
    f_pow
    =
    (fun (g: t_Group_curve) (x: t_Z_curve) ->
        { f_g_val = Hacspec_bip_340.point_mul x.f_z_val g.f_g_val } <: t_Group_curve);
    f_g_pow_pre = (fun (x: t_Z_curve) -> true);
    f_g_pow_post = (fun (x: t_Z_curve) (out: t_Group_curve) -> true);
    f_g_pow
    =
    (fun (x: t_Z_curve) -> { f_g_val = Hacspec_bip_340.point_mul_base x.f_z_val } <: t_Group_curve);
    f_group_one_pre = (fun (_: Prims.unit) -> true);
    f_group_one_post = (fun (_: Prims.unit) (out: t_Group_curve) -> true);
    f_group_one
    =
    (fun (_: Prims.unit) ->
        Hacspec_ovn.Ovn_traits.f_g_pow #t_Group_curve
          #FStar.Tactics.Typeclasses.solve
          (Hacspec_ovn.Ovn_traits.f_field_zero #t_Z_curve #FStar.Tactics.Typeclasses.solve ()
            <:
            t_Z_curve));
    f_prod_pre = (fun (x: t_Group_curve) (y: t_Group_curve) -> true);
    f_prod_post = (fun (x: t_Group_curve) (y: t_Group_curve) (out: t_Group_curve) -> true);
    f_prod
    =
    (fun (x: t_Group_curve) (y: t_Group_curve) ->
        { f_g_val = Hacspec_bip_340.point_add x.f_g_val y.f_g_val } <: t_Group_curve);
    f_group_inv_pre = (fun (x: t_Group_curve) -> true);
    f_group_inv_post = (fun (x: t_Group_curve) (out: t_Group_curve) -> true);
    f_group_inv
    =
    (fun (x: t_Group_curve) ->
        {
          f_g_val
          =
          match x.f_g_val with
          | Hacspec_bip_340.Point_Affine (a, b) ->
            Hacspec_bip_340.Point_Affine
            (a,
              (Hacspec_bip_340.impl__FieldElement__from_literal (pub_u128 0)
                <:
                Hacspec_bip_340.t_FieldElement) -!
              b
              <:
              (Hacspec_bip_340.t_FieldElement & Hacspec_bip_340.t_FieldElement))
            <:
            Hacspec_bip_340.t_Point
          | Hacspec_bip_340.Point_AtInfinity  ->
            Hacspec_bip_340.Point_AtInfinity <: Hacspec_bip_340.t_Point
        }
        <:
        t_Group_curve);
    f_hash_pre = (fun (x: Alloc.Vec.t_Vec t_Group_curve Alloc.Alloc.t_Global) -> true);
    f_hash_post
    =
    (fun (x: Alloc.Vec.t_Vec t_Group_curve Alloc.Alloc.t_Global) (out: t_Z_curve) -> true);
    f_hash
    =
    fun (x: Alloc.Vec.t_Vec t_Group_curve Alloc.Alloc.t_Global) ->
      Hacspec_ovn.Ovn_traits.f_field_one #t_Z_curve #FStar.Tactics.Typeclasses.solve ()
  }
