module Hacspec_ovn.Ovn_traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Concordium_contracts_common.Traits in
  ()

(* item error backend: (reject_TraitItemDefault) ExplicitRejection { reason: "a node of kind [Trait_item_default] have been found in the AST" }
Last available AST for this item:

/** Interface for field implementation */#[no_std()]#[feature(register_tool)]#[register_tool(hax)]#[no_std()]#[feature(register_tool)]#[register_tool(hax)]#[feature(trait_alias)]#[register_tool(_hax)]trait t_Field<Self_> where _:core::marker::t_Copy<Self>,_:core::cmp::t_PartialEq<Self, Self>,_:core::cmp::t_Eq<Self>,_:core::clone::t_Clone<Self>,_:concordium_contracts_common::traits::t_Serialize<Self>{#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_q_pre(_: tuple0) -> bool;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_q_post(_: tuple0,_: Self) -> bool;
fn f_q(_: tuple0) -> Self;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_random_field_elem_pre(_: int) -> bool;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_random_field_elem_post(_: int,_: Self) -> bool;
fn f_random_field_elem(_: int) -> Self;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_field_zero_pre(_: tuple0) -> bool;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_field_zero_post(_: tuple0,_: Self) -> bool;
fn f_field_zero(_: tuple0) -> Self;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_field_one_pre(_: tuple0) -> bool;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_field_one_post(_: tuple0,_: Self) -> bool;
fn f_field_one(_: tuple0) -> Self;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_add_pre(_: Self,_: Self) -> bool;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_add_post(_: Self,_: Self,_: Self) -> bool;
fn f_add(_: Self,_: Self) -> Self;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_opp_pre(_: Self) -> bool;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_opp_post(_: Self,_: Self) -> bool;
fn f_opp(_: Self) -> Self;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_mul_pre(_: Self,_: Self) -> bool;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_mul_post(_: Self,_: Self,_: Self) -> bool;
fn f_mul(_: Self,_: Self) -> Self;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_inv_pre(_: Self) -> bool;
#[_hax::json("\"TraitMethodNoPrePost\"")]fn f_inv_post(_: Self,_: Self) -> bool;
fn f_inv(_: Self) -> Self;
#[_hax::json("{\"ItemStatus\":{\"Included\":{\"late_skip\":true}}}")]fn f____(()) -> tuple0{Tuple0}
#[_hax::json("{\"ItemStatus\":{\"Included\":{\"late_skip\":true}}}")]fn f____1(()) -> tuple0{Tuple0}
#[_hax::json("\"Lemma\"")]fn f_addC<Z>((x: Z,y: Z)) -> tuple0 where _:hacspec_ovn::ovn_traits::t_Field<Z>{Tuple0}}

Last AST:
/** print_rust: pitem: not implemented  (item: { Concrete_ident.T.def_id =
  { Concrete_ident.Imported.krate = "hacspec_ovn";
    path =
    [{ Concrete_ident.Imported.data =
       (Concrete_ident.Imported.TypeNs "ovn_traits"); disambiguator = 0 };
      { Concrete_ident.Imported.data =
        (Concrete_ident.Imported.TypeNs "Field"); disambiguator = 0 }
      ]
    };
  kind = Concrete_ident.Kind.Value }) */
const _: () = ();
 *)

(** Interface for group implementation *)
class t_Group (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11581440318597584651:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12632649257025169145:Core.Cmp.t_PartialEq v_Self
    v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_8099741844003281729:Core.Cmp.t_Eq v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9442900250278684536:Core.Clone.t_Clone v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_17605656595743636193:Concordium_contracts_common.Traits.t_Serialize
  v_Self;
  f_Z:Type0;
  f_Z_5568683927164688039:t_Field f_Z;
  f_Z_6036424691684178845:Concordium_contracts_common.Traits.t_Serialize f_Z;
  f_Z_5944877312583825506:Concordium_contracts_common.Traits.t_Deserial f_Z;
  f_Z_2631562626655622548:Concordium_contracts_common.Traits.t_Serial f_Z;
  f_Z_7106659769471979108:Core.Clone.t_Clone f_Z;
  f_Z_5227107583605841272:Core.Cmp.t_Eq f_Z;
  f_Z_13069512637334391294:Core.Cmp.t_PartialEq f_Z f_Z;
  f_Z_16774959407837281168:Core.Marker.t_Copy f_Z;
  f_g_pre:Prims.unit -> Type0;
  f_g_post:Prims.unit -> v_Self -> Type0;
  f_g:x0: Prims.unit -> Prims.Pure v_Self (f_g_pre x0) (fun result -> f_g_post x0 result);
  f_g_pow_pre:f_Z -> Type0;
  f_g_pow_post:f_Z -> v_Self -> Type0;
  f_g_pow:x0: f_Z -> Prims.Pure v_Self (f_g_pow_pre x0) (fun result -> f_g_pow_post x0 result);
  f_pow_pre:v_Self -> f_Z -> Type0;
  f_pow_post:v_Self -> f_Z -> v_Self -> Type0;
  f_pow:x0: v_Self -> x1: f_Z
    -> Prims.Pure v_Self (f_pow_pre x0 x1) (fun result -> f_pow_post x0 x1 result);
  f_group_one_pre:Prims.unit -> Type0;
  f_group_one_post:Prims.unit -> v_Self -> Type0;
  f_group_one:x0: Prims.unit
    -> Prims.Pure v_Self (f_group_one_pre x0) (fun result -> f_group_one_post x0 result);
  f_prod_pre:v_Self -> v_Self -> Type0;
  f_prod_post:v_Self -> v_Self -> v_Self -> Type0;
  f_prod:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_prod_pre x0 x1) (fun result -> f_prod_post x0 x1 result);
  f_group_inv_pre:v_Self -> Type0;
  f_group_inv_post:v_Self -> v_Self -> Type0;
  f_group_inv:x0: v_Self
    -> Prims.Pure v_Self (f_group_inv_pre x0) (fun result -> f_group_inv_post x0 result);
  f_hash_pre:Alloc.Vec.t_Vec v_Self Alloc.Alloc.t_Global -> Type0;
  f_hash_post:Alloc.Vec.t_Vec v_Self Alloc.Alloc.t_Global -> f_Z -> Type0;
  f_hash:x0: Alloc.Vec.t_Vec v_Self Alloc.Alloc.t_Global
    -> Prims.Pure f_Z (f_hash_pre x0) (fun result -> f_hash_post x0 result)
}
