module Hacspec_ovn.Ovn_z_89_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Concordium_contracts_common.Traits in
  let open Hacspec_ovn.Ovn_traits in
  ()

type t_g_z_89_ = { f_g_val:u8 }

type t_z_89_ = { f_z_val:u8 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Hacspec_ovn.Ovn_traits.t_Field t_z_89_ =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_12632649257025169145 = FStar.Tactics.Typeclasses.solve;
    _super_8099741844003281729 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_17605656595743636193 = FStar.Tactics.Typeclasses.solve;
    f_q_pre = (fun (_: Prims.unit) -> true);
    f_q_post = (fun (_: Prims.unit) (out: t_z_89_) -> true);
    f_q = (fun (_: Prims.unit) -> { f_z_val = 89uy } <: t_z_89_);
    f_random_field_elem_pre = (fun (random: u32) -> true);
    f_random_field_elem_post = (fun (random: u32) (out: t_z_89_) -> true);
    f_random_field_elem
    =
    (fun (random: u32) ->
        {
          f_z_val
          =
          (cast (random <: u32) <: u8) %!
          ((Hacspec_ovn.Ovn_traits.f_q #t_z_89_ #FStar.Tactics.Typeclasses.solve () <: t_z_89_)
              .f_z_val -!
            1uy
            <:
            u8)
        }
        <:
        t_z_89_);
    f_field_zero_pre = (fun (_: Prims.unit) -> true);
    f_field_zero_post = (fun (_: Prims.unit) (out: t_z_89_) -> true);
    f_field_zero = (fun (_: Prims.unit) -> { f_z_val = 0uy } <: t_z_89_);
    f_field_one_pre = (fun (_: Prims.unit) -> true);
    f_field_one_post = (fun (_: Prims.unit) (out: t_z_89_) -> true);
    f_field_one = (fun (_: Prims.unit) -> { f_z_val = 1uy } <: t_z_89_);
    f_add_pre = (fun (x: t_z_89_) (y: t_z_89_) -> true);
    f_add_post = (fun (x: t_z_89_) (y: t_z_89_) (out: t_z_89_) -> true);
    f_add
    =
    (fun (x: t_z_89_) (y: t_z_89_) ->
        let q___:u8 =
          (Hacspec_ovn.Ovn_traits.f_q #t_z_89_ #FStar.Tactics.Typeclasses.solve () <: t_z_89_)
            .f_z_val -!
          1uy
        in
        let x___:u8 = x.f_z_val %! q___ in
        let y___:u8 = y.f_z_val %! q___ in
        { f_z_val = (x___ +! y___ <: u8) %! q___ } <: t_z_89_);
    f_opp_pre = (fun (x: t_z_89_) -> true);
    f_opp_post = (fun (x: t_z_89_) (out: t_z_89_) -> true);
    f_opp
    =
    (fun (x: t_z_89_) ->
        let q___:u8 =
          (Hacspec_ovn.Ovn_traits.f_q #t_z_89_ #FStar.Tactics.Typeclasses.solve () <: t_z_89_)
            .f_z_val -!
          1uy
        in
        let x___:u8 = x.f_z_val %! q___ in
        { f_z_val = q___ -! x___ } <: t_z_89_);
    f_mul_pre = (fun (x: t_z_89_) (y: t_z_89_) -> true);
    f_mul_post = (fun (x: t_z_89_) (y: t_z_89_) (out: t_z_89_) -> true);
    f_mul
    =
    (fun (x: t_z_89_) (y: t_z_89_) ->
        let q___:u8 =
          (Hacspec_ovn.Ovn_traits.f_q #t_z_89_ #FStar.Tactics.Typeclasses.solve () <: t_z_89_)
            .f_z_val -!
          1uy
        in
        let (x___: u16):u16 = cast (x.f_z_val %! q___ <: u8) <: u16 in
        let (y___: u16):u16 = cast (y.f_z_val %! q___ <: u8) <: u16 in
        { f_z_val = cast ((x___ *! y___ <: u16) %! (cast (q___ <: u8) <: u16) <: u16) <: u8 }
        <:
        t_z_89_);
    f_inv_pre = (fun (x: t_z_89_) -> true);
    f_inv_post = (fun (x: t_z_89_) (out: t_z_89_) -> true);
    f_inv
    =
    fun (x: t_z_89_) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _:Prims.unit =
            Hax_lib.v_assert false
          in
          let! hoist11:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow_Break x
            <:
            Core.Ops.Control_flow.t_ControlFlow t_z_89_ Rust_primitives.Hax.t_Never
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist11)
          <:
          Core.Ops.Control_flow.t_ControlFlow t_z_89_ t_z_89_)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Hacspec_ovn.Ovn_traits.t_Group t_g_z_89_ =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_12632649257025169145 = FStar.Tactics.Typeclasses.solve;
    _super_8099741844003281729 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_17605656595743636193 = FStar.Tactics.Typeclasses.solve;
    f_Z = t_z_89_;
    f_Z_5568683927164688039 = FStar.Tactics.Typeclasses.solve;
    f_g_pre = (fun (_: Prims.unit) -> true);
    f_g_post = (fun (_: Prims.unit) (out: t_g_z_89_) -> true);
    f_g = (fun (_: Prims.unit) -> { f_g_val = 3uy } <: t_g_z_89_);
    f_hash_pre = (fun (x: Alloc.Vec.t_Vec t_g_z_89_ Alloc.Alloc.t_Global) -> true);
    f_hash_post = (fun (x: Alloc.Vec.t_Vec t_g_z_89_ Alloc.Alloc.t_Global) (out: t_z_89_) -> true);
    f_hash
    =
    (fun (x: Alloc.Vec.t_Vec t_g_z_89_ Alloc.Alloc.t_Global) ->
        let res:t_z_89_ =
          Hacspec_ovn.Ovn_traits.f_field_one #t_z_89_ #FStar.Tactics.Typeclasses.solve ()
        in
        let res:t_z_89_ =
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec
                    t_g_z_89_ Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                x
              <:
              Alloc.Vec.Into_iter.t_IntoIter t_g_z_89_ Alloc.Alloc.t_Global)
            res
            (fun res y ->
                let res:t_z_89_ = res in
                let y:t_g_z_89_ = y in
                Hacspec_ovn.Ovn_traits.f_mul #t_z_89_
                  #FStar.Tactics.Typeclasses.solve
                  ({ f_z_val = y.f_g_val } <: t_z_89_)
                  res
                <:
                t_z_89_)
        in
        res);
    f_g_pow_pre = (fun (x: t_z_89_) -> true);
    f_g_pow_post = (fun (x: t_z_89_) (out: t_g_z_89_) -> true);
    f_g_pow
    =
    (fun (x: t_z_89_) ->
        Hacspec_ovn.Ovn_traits.f_pow #t_g_z_89_
          #FStar.Tactics.Typeclasses.solve
          (Hacspec_ovn.Ovn_traits.f_g #t_g_z_89_ #FStar.Tactics.Typeclasses.solve () <: t_g_z_89_)
          x);
    f_pow_pre = (fun (g: t_g_z_89_) (x: t_z_89_) -> true);
    f_pow_post = (fun (g: t_g_z_89_) (x: t_z_89_) (out: t_g_z_89_) -> true);
    f_pow
    =
    (fun (g: t_g_z_89_) (x: t_z_89_) ->
        let result:t_g_z_89_ =
          Hacspec_ovn.Ovn_traits.f_group_one #t_g_z_89_ #FStar.Tactics.Typeclasses.solve ()
        in
        let result:t_g_z_89_ =
          Rust_primitives.Hax.Folds.fold_range 0uy
            (x.f_z_val %!
              ((Hacspec_ovn.Ovn_traits.f_q #t_z_89_ #FStar.Tactics.Typeclasses.solve () <: t_z_89_)
                  .f_z_val -!
                1uy
                <:
                u8)
              <:
              u8)
            (fun result temp_1_ ->
                let result:t_g_z_89_ = result in
                let _:u8 = temp_1_ in
                true)
            result
            (fun result temp_1_ ->
                let result:t_g_z_89_ = result in
                let _:u8 = temp_1_ in
                Hacspec_ovn.Ovn_traits.f_prod #t_g_z_89_ #FStar.Tactics.Typeclasses.solve result g
                <:
                t_g_z_89_)
        in
        result);
    f_group_one_pre = (fun (_: Prims.unit) -> true);
    f_group_one_post = (fun (_: Prims.unit) (out: t_g_z_89_) -> true);
    f_group_one = (fun (_: Prims.unit) -> { f_g_val = 1uy } <: t_g_z_89_);
    f_prod_pre = (fun (x: t_g_z_89_) (y: t_g_z_89_) -> true);
    f_prod_post = (fun (x: t_g_z_89_) (y: t_g_z_89_) (out: t_g_z_89_) -> true);
    f_prod
    =
    (fun (x: t_g_z_89_) (y: t_g_z_89_) ->
        let q___:u8 =
          (Hacspec_ovn.Ovn_traits.f_q #t_z_89_ #FStar.Tactics.Typeclasses.solve ()).f_z_val
        in
        let x___:u16 = cast (x.f_g_val %! q___ <: u8) <: u16 in
        let y___:u16 = cast (y.f_g_val %! q___ <: u8) <: u16 in
        { f_g_val = cast ((x___ *! y___ <: u16) %! (cast (q___ <: u8) <: u16) <: u16) <: u8 }
        <:
        t_g_z_89_);
    f_group_inv_pre = (fun (x: t_g_z_89_) -> true);
    f_group_inv_post = (fun (x: t_g_z_89_) (out: t_g_z_89_) -> true);
    f_group_inv
    =
    fun (x: t_g_z_89_) ->
      Rust_primitives.Hax.Control_flow_monad.Mexception.run (let _:Prims.unit =
            Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.\nLoop without mutation?"
              "{\n        for j in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n            f_start: 0,\n            f_end: 89,\n        })) {\n            {\n                let g_value: hacspec_ovn::ovn_z_89_::t_g_z_89_ = {\n                    hacspec_ovn::ovn_z_89_::C_g_z_89_ {\n                        f_g_val: j,\n                    }\n                };\n                (if core::cmp::f_eq(\n                    hacspec_ovn::ovn_traits::f_prod(x, g_value),\n                    hacspec_ovn::ovn_traits::f_group_one(Tuple0),\n                ) {\n                    {\n                        #[note(\n                            \"rhs.typ=core::ops::control_flow::t_ControlFlow<hacspec_ovn::ovn_z_89_::t_g_z_89_, rust_primitives::hax::t_Never>\"\n                        )]\n                        #[monadic_let(MException<hacspec_ovn::ovn_z_89_::t_g_z_89_>)]\n                        let hoist15: rust_primitives::hax::t_Never = {\n                            core::ops::control_flow::ControlFlow_Break(g_value)\n                        };\n                        core::ops::control_flow::ControlFlow_Continue(\n                            rust_primitives::hax::never_to_any(hoist15),\n                        )\n                    }\n                } else {\n                    core::ops::control_flow::ControlFlow_Continue(Tuple0)\n                })\n            }\n        }\n    }"

          in
          let _:Prims.unit = Hax_lib.v_assert false in
          let! hoist16:Rust_primitives.Hax.t_Never =
            Core.Ops.Control_flow.ControlFlow_Break x
            <:
            Core.Ops.Control_flow.t_ControlFlow t_g_z_89_ Rust_primitives.Hax.t_Never
          in
          Core.Ops.Control_flow.ControlFlow_Continue (Rust_primitives.Hax.never_to_any hoist16)
          <:
          Core.Ops.Control_flow.t_ControlFlow t_g_z_89_ t_g_z_89_)
  }
