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

Require Import Hacspec_lib.

Notation SBox_t := (nseq int8 256).
Definition SBox : both (fset []) ([interface]) (SBox_t) -> both (fset []) ([interface]) (SBox_t) :=
  id.

Notation RCon_t := (nseq int8 15).
Definition RCon : both (fset []) ([interface]) (RCon_t) -> both (fset []) ([interface]) (RCon_t) :=
  id.

Notation PBytes256_t := (nseq int8 256).
Definition PBytes256 : both (fset []) ([interface]) (PBytes256_t) -> both (fset []) ([interface]) (PBytes256_t) :=
  id.

Equations SBOX : both (fset []) ([interface ]) (SBox_t) :=
  SBOX  :=
    lift_both (SBox (array_from_list [i8(99);
      i8(124);
      i8(119);
      i8(123);
      i8(242);
      i8(107);
      i8(111);
      i8(197);
      i8(48);
      i8(1);
      i8(103);
      i8(43);
      i8(254);
      i8(215);
      i8(171);
      i8(118);
      i8(202);
      i8(130);
      i8(201);
      i8(125);
      i8(250);
      i8(89);
      i8(71);
      i8(240);
      i8(173);
      i8(212);
      i8(162);
      i8(175);
      i8(156);
      i8(164);
      i8(114);
      i8(192);
      i8(183);
      i8(253);
      i8(147);
      i8(38);
      i8(54);
      i8(63);
      i8(247);
      i8(204);
      i8(52);
      i8(165);
      i8(229);
      i8(241);
      i8(113);
      i8(216);
      i8(49);
      i8(21);
      i8(4);
      i8(199);
      i8(35);
      i8(195);
      i8(24);
      i8(150);
      i8(5);
      i8(154);
      i8(7);
      i8(18);
      i8(128);
      i8(226);
      i8(235);
      i8(39);
      i8(178);
      i8(117);
      i8(9);
      i8(131);
      i8(44);
      i8(26);
      i8(27);
      i8(110);
      i8(90);
      i8(160);
      i8(82);
      i8(59);
      i8(214);
      i8(179);
      i8(41);
      i8(227);
      i8(47);
      i8(132);
      i8(83);
      i8(209);
      i8(0);
      i8(237);
      i8(32);
      i8(252);
      i8(177);
      i8(91);
      i8(106);
      i8(203);
      i8(190);
      i8(57);
      i8(74);
      i8(76);
      i8(88);
      i8(207);
      i8(208);
      i8(239);
      i8(170);
      i8(251);
      i8(67);
      i8(77);
      i8(51);
      i8(133);
      i8(69);
      i8(249);
      i8(2);
      i8(127);
      i8(80);
      i8(60);
      i8(159);
      i8(168);
      i8(81);
      i8(163);
      i8(64);
      i8(143);
      i8(146);
      i8(157);
      i8(56);
      i8(245);
      i8(188);
      i8(182);
      i8(218);
      i8(33);
      i8(16);
      i8(255);
      i8(243);
      i8(210);
      i8(205);
      i8(12);
      i8(19);
      i8(236);
      i8(95);
      i8(151);
      i8(68);
      i8(23);
      i8(196);
      i8(167);
      i8(126);
      i8(61);
      i8(100);
      i8(93);
      i8(25);
      i8(115);
      i8(96);
      i8(129);
      i8(79);
      i8(220);
      i8(34);
      i8(42);
      i8(144);
      i8(136);
      i8(70);
      i8(238);
      i8(184);
      i8(20);
      i8(222);
      i8(94);
      i8(11);
      i8(219);
      i8(224);
      i8(50);
      i8(58);
      i8(10);
      i8(73);
      i8(6);
      i8(36);
      i8(92);
      i8(194);
      i8(211);
      i8(172);
      i8(98);
      i8(145);
      i8(149);
      i8(228);
      i8(121);
      i8(231);
      i8(200);
      i8(55);
      i8(109);
      i8(141);
      i8(213);
      i8(78);
      i8(169);
      i8(108);
      i8(86);
      i8(244);
      i8(234);
      i8(101);
      i8(122);
      i8(174);
      i8(8);
      i8(186);
      i8(120);
      i8(37);
      i8(46);
      i8(28);
      i8(166);
      i8(180);
      i8(198);
      i8(232);
      i8(221);
      i8(116);
      i8(31);
      i8(75);
      i8(189);
      i8(139);
      i8(138);
      i8(112);
      i8(62);
      i8(181);
      i8(102);
      i8(72);
      i8(3);
      i8(246);
      i8(14);
      i8(97);
      i8(53);
      i8(87);
      i8(185);
      i8(134);
      i8(193);
      i8(29);
      i8(158);
      i8(225);
      i8(248);
      i8(152);
      i8(17);
      i8(105);
      i8(217);
      i8(142);
      i8(148);
      i8(155);
      i8(30);
      i8(135);
      i8(233);
      i8(206);
      i8(85);
      i8(40);
      i8(223);
      i8(140);
      i8(161);
      i8(137);
      i8(13);
      i8(191);
      i8(230);
      i8(66);
      i8(104);
      i8(65);
      i8(153);
      i8(45);
      i8(15);
      i8(176);
      i8(84);
      i8(187);
      i8(22)])) : both (fset []) ([interface ]) (SBox_t).
Fail Next Obligation.

Equations RCON : both (fset []) ([interface ]) (RCon_t) :=
  RCON  :=
    lift_both (RCon (array_from_list [i8(141);
      i8(1);
      i8(2);
      i8(4);
      i8(8);
      i8(16);
      i8(32);
      i8(64);
      i8(128);
      i8(27);
      i8(54);
      i8(108);
      i8(216);
      i8(171);
      i8(77)])) : both (fset []) ([interface ]) (RCon_t).
Fail Next Obligation.

Equations index_u32 {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (s : both L1 I1 (int128)) (i : both L2 I2 (uint_size)) : both (L1:|:L2) (I1:|:I2) (int32) :=
  index_u32 s i  :=
    lift_both (cast_int ((s shift_right (i.*i32(32))).%(i128(1) shift_left i32(32)))) : both (L1:|:L2) (I1:|:I2) (int32).
Fail Next Obligation.

Equations index_u8 {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (s : both L1 I1 (int32)) (i : both L2 I2 (uint_size)) : both (L1:|:L2) (I1:|:I2) (int8) :=
  index_u8 s i  :=
    lift_both (cast_int ((s shift_right (i.*i32(8))).%(i32(1) shift_left i32(8)))) : both (L1:|:L2) (I1:|:I2) (int8).
Fail Next Obligation.

Equations rebuild_u32 {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {L4 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} {I4 : Interface} (s0 : both L1 I1 (int8)) (s1 : both L2 I2 (int8)) (s2 : both L3 I3 (int8)) (s3 : both L4 I4 (int8)) : both (L1:|:L2:|:L3:|:L4) (I1:|:I2:|:I3:|:I4) (int32) :=
  rebuild_u32 s0 s1 s2 s3  :=
    lift_both ((cast_int s0).|(((cast_int s1) shift_left i32(8)).|(((cast_int s2) shift_left i32(16)).|((cast_int s3) shift_left i32(24))))) : both (L1:|:L2:|:L3:|:L4) (I1:|:I2:|:I3:|:I4) (int32).
Fail Next Obligation.

Equations rebuild_u128 {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {L4 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} {I4 : Interface} (s0 : both L1 I1 (int32)) (s1 : both L2 I2 (int32)) (s2 : both L3 I3 (int32)) (s3 : both L4 I4 (int32)) : both (L1:|:L2:|:L3:|:L4) (I1:|:I2:|:I3:|:I4) (int128) :=
  rebuild_u128 s0 s1 s2 s3  :=
    lift_both ((cast_int s0).|(((cast_int s1) shift_left i32(32)).|(((cast_int s2) shift_left i32(64)).|((cast_int s3) shift_left i32(96))))) : both (L1:|:L2:|:L3:|:L4) (I1:|:I2:|:I3:|:I4) (int128).
Fail Next Obligation.

Equations subword {L1 : {fset Location}} {I1 : Interface} (v : both L1 I1 (int32)) : both (L1) (I1) (int32) :=
  subword v  :=
    lift_both (rebuild_u32 (nseq_array_or_seq SBOX.[(index_u8 v i32(0))]) (nseq_array_or_seq SBOX.[(index_u8 v i32(1))]) (nseq_array_or_seq SBOX.[(index_u8 v i32(2))]) (nseq_array_or_seq SBOX.[(index_u8 v i32(3))])) : both (L1) (I1) (int32).
Fail Next Obligation.

Equations rotword {L1 : {fset Location}} {I1 : Interface} (v : both L1 I1 (int32)) : both (L1) (I1) (int32) :=
  rotword v  :=
    lift_both (rebuild_u32 (index_u8 v i32(1)) (index_u8 v i32(2)) (index_u8 v i32(3)) (index_u8 v i32(0))) : both (L1) (I1) (int32).
Fail Next Obligation.

Equations vpshufd1 {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (s : both L1 I1 (int128)) (o : both L2 I2 (int8)) (i : both L3 I3 (uint_size)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) (int32) :=
  vpshufd1 s o i  :=
    lift_both (index_u32 (s shift_right (i32(32).*(cast_int ((o shift_right (i32(2).*i)).%i8(4))))) i32(0)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) (int32).
Fail Next Obligation.

Equations vpshufd {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (s : both L1 I1 (int128)) (o : both L2 I2 (int8)) : both (L1:|:L2) (I1:|:I2) (int128) :=
  vpshufd s o  :=
    lift_both (letb d1 := (vpshufd1 s o i32(0)) : both _ _ (int32) in
    letb d2 := (vpshufd1 s o i32(1)) : both _ _ (int32) in
    letb d3 := (vpshufd1 s o i32(2)) : both _ _ (int32) in
    letb d4 := (vpshufd1 s o i32(3)) : both _ _ (int32) in
    rebuild_u128 d1 d2 d3 d4) : both (L1:|:L2) (I1:|:I2) (int128).
Fail Next Obligation.

Equations vshufps {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (s1 : both L1 I1 (int128)) (s2 : both L2 I2 (int128)) (o : both L3 I3 (int8)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) (int128) :=
  vshufps s1 s2 o  :=
    lift_both (letb d1 := (vpshufd1 s1 o i32(0)) : both _ _ (int32) in
    letb d2 := (vpshufd1 s1 o i32(1)) : both _ _ (int32) in
    letb d3 := (vpshufd1 s2 o i32(2)) : both _ _ (int32) in
    letb d4 := (vpshufd1 s2 o i32(3)) : both _ _ (int32) in
    rebuild_u128 d1 d2 d3 d4) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) (int128).
Fail Next Obligation.

Equations key_combine {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (rkey : both L1 I1 (int128)) (temp1 : both L2 I2 (int128)) (temp2 : both L3 I3 (int128)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ((int128 × int128)) :=
  key_combine rkey temp1 temp2  :=
    lift_both (letb temp1 := (vpshufd temp1 i8(255)) : both _ _ (int128) in
    letb temp2 := (vshufps temp2 rkey i8(16)) : both _ _ (int128) in
    letb rkey := (rkey.^temp2) : both _ _ (int128) in
    letb temp2 := (vshufps temp2 rkey i8(140)) : both _ _ (int128) in
    letb rkey := (rkey.^temp2) : both _ _ (int128) in
    letb rkey := (rkey.^temp1) : both _ _ (int128) in
    prod_b(rkey,temp2)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ((int128 × int128)).
Fail Next Obligation.

Equations aeskeygenassist {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (v1 : both L1 I1 (int128)) (v2 : both L2 I2 (int8)) : both (L1:|:L2) (I1:|:I2) (int128) :=
  aeskeygenassist v1 v2  :=
    lift_both (letb x1 := (index_u32 v1 i32(1)) : both _ _ (int32) in
    letb x3 := (index_u32 v1 i32(3)) : both _ _ (int32) in
    letb y0 := (subword x1) : both _ _ (int32) in
    letb y1 := ((rotword y0).^(cast_int v2)) : both _ _ (int32) in
    letb y2 := (subword x3) : both _ _ (int32) in
    letb y3 := ((rotword y2).^(cast_int v2)) : both _ _ (int32) in
    rebuild_u128 y0 y1 y2 y3) : both (L1:|:L2) (I1:|:I2) (int128).
Fail Next Obligation.

Equations key_expand {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (rcon : both L1 I1 (int8)) (rkey : both L2 I2 (int128)) (temp2 : both L3 I3 (int128)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ((int128 × int128)) :=
  key_expand rcon rkey temp2  :=
    lift_both (letb temp1 := (aeskeygenassist rkey rcon) : both _ _ (int128) in
    key_combine rkey temp1 temp2) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ((int128 × int128)).
Fail Next Obligation.

Notation KeyList_t := (Seq_t (int128)).

Definition key_loc : Location :=
  (int128 ; 0%nat).
Equations keys_expand {L1 : {fset Location}} {I1 : Interface} (key : both L1 I1 (int128)) : both (L1 :|: fset [key_loc]) (I1) (Seq_t (int128)) :=
  keys_expand key  :=
    lift_both (letb rkeys := (new_seq i32(0)) : both _ _ (Seq_t (int128)) in
    letbm key loc(key_loc) := (key) : both _ _ (int128) in
    letb rkeys := (push rkeys key) : both _ _ (Seq_t (int128)) in
    letb temp2 := (i128(0)) : both _ _ (int128) in
    letb '(key,rkeys,temp2) := (foldi_both (into_iter (Build_Range_t i32(1)i32(11))) (fun {L I _ _} =>fun round =>
        (ssp (fun '(key,rkeys,temp2) =>
          lift_both (letb rcon := (nseq_array_or_seq RCON.[round]) : both _ _ (int8) in
          letb '(key_temp,temp2_temp) := (key_expand rcon key temp2) : both _ _ ((int128 × int128)) in
          letb key := (key_temp) : both _ _ (int128) in
          letb temp2 := (temp2_temp) : both _ _ (int128) in
          letb rkeys := (push rkeys key) : both _ _ (Seq_t (int128)) in
          prod_b(key,rkeys,temp2)) ))) prod_b(key,rkeys,temp2)) : both _ _ ((int128 × Seq_t (int128) × int128)) in
    rkeys) : both (L1 :|: fset [key_loc]) (I1) (Seq_t (int128)).
Fail Next Obligation.

Equations subbytes {L1 : {fset Location}} {I1 : Interface} (s : both L1 I1 (int128)) : both (L1) (I1) (int128) :=
  subbytes s  :=
    lift_both (rebuild_u128 (subword (index_u32 s i32(0))) (subword (index_u32 s i32(1))) (subword (index_u32 s i32(2))) (subword (index_u32 s i32(3)))) : both (L1) (I1) (int128).
Fail Next Obligation.

Equations matrix_index {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (s : both L1 I1 (int128)) (i : both L2 I2 (uint_size)) (j : both L3 I3 (uint_size)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) (int8) :=
  matrix_index s i j  :=
    lift_both (index_u8 (index_u32 s j) i) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) (int8).
Fail Next Obligation.

Equations shiftrows {L1 : {fset Location}} {I1 : Interface} (s : both L1 I1 (int128)) : both (L1) (I1) (int128) :=
  shiftrows s  :=
    lift_both (rebuild_u128 (rebuild_u32 (matrix_index s i32(0) i32(0)) (matrix_index s i32(1) i32(1)) (matrix_index s i32(2) i32(2)) (matrix_index s i32(3) i32(3))) (rebuild_u32 (matrix_index s i32(0) i32(1)) (matrix_index s i32(1) i32(2)) (matrix_index s i32(2) i32(3)) (matrix_index s i32(3) i32(0))) (rebuild_u32 (matrix_index s i32(0) i32(2)) (matrix_index s i32(1) i32(3)) (matrix_index s i32(2) i32(0)) (matrix_index s i32(3) i32(1))) (rebuild_u32 (matrix_index s i32(0) i32(3)) (matrix_index s i32(1) i32(0)) (matrix_index s i32(2) i32(1)) (matrix_index s i32(3) i32(2)))) : both (L1) (I1) (int128).
Fail Next Obligation.

Equations xtime {L1 : {fset Location}} {I1 : Interface} (x : both L1 I1 (int8)) : both (L1) (I1) (int8) :=
  xtime x  :=
    lift_both (letb x1 := (x shift_left i32(1)) : both _ _ (int8) in
    letb x7 := (x shift_right i32(7)) : both _ _ (int8) in
    letb x71 := (x7.&i8(1)) : both _ _ (int8) in
    letb x711b := (x71.*i8(27)) : both _ _ (int8) in
    x1.^x711b) : both (L1) (I1) (int8).
Fail Next Obligation.

Equations mixcolumn {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (c : both L1 I1 (uint_size)) (state : both L2 I2 (int128)) : both (L1:|:L2) (I1:|:I2) (int32) :=
  mixcolumn c state  :=
    lift_both (letb s0 := (matrix_index state i32(0) c) : both _ _ (int8) in
    letb s1 := (matrix_index state i32(1) c) : both _ _ (int8) in
    letb s2 := (matrix_index state i32(2) c) : both _ _ (int8) in
    letb s3 := (matrix_index state i32(3) c) : both _ _ (int8) in
    letb tmp := (((s0.^s1).^s2).^s3) : both _ _ (int8) in
    letb r0 := ((s0.^tmp).^(xtime (s0.^s1))) : both _ _ (int8) in
    letb r1 := ((s1.^tmp).^(xtime (s1.^s2))) : both _ _ (int8) in
    letb r2 := ((s2.^tmp).^(xtime (s2.^s3))) : both _ _ (int8) in
    letb r3 := ((s3.^tmp).^(xtime (s3.^s0))) : both _ _ (int8) in
    rebuild_u32 r0 r1 r2 r3) : both (L1:|:L2) (I1:|:I2) (int32).
Fail Next Obligation.

Equations mixcolumns {L1 : {fset Location}} {I1 : Interface} (state : both L1 I1 (int128)) : both (L1) (I1) (int128) :=
  mixcolumns state  :=
    lift_both (letb c0 := (mixcolumn i32(0) state) : both _ _ (int32) in
    letb c1 := (mixcolumn i32(1) state) : both _ _ (int32) in
    letb c2 := (mixcolumn i32(2) state) : both _ _ (int32) in
    letb c3 := (mixcolumn i32(3) state) : both _ _ (int32) in
    rebuild_u128 c0 c1 c2 c3) : both (L1) (I1) (int128).
Fail Next Obligation.

Equations aesenc {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (state : both L1 I1 (int128)) (rkey : both L2 I2 (int128)) : both (L1:|:L2) (I1:|:I2) (int128) :=
  aesenc state rkey  :=
    lift_both (letb state := (shiftrows state) : both _ _ (int128) in
    letb state := (subbytes state) : both _ _ (int128) in
    letb state := (mixcolumns state) : both _ _ (int128) in
    state.^rkey) : both (L1:|:L2) (I1:|:I2) (int128).
Fail Next Obligation.

Equations aesenclast {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (state : both L1 I1 (int128)) (rkey : both L2 I2 (int128)) : both (L1:|:L2) (I1:|:I2) (int128) :=
  aesenclast state rkey  :=
    lift_both (letb state := (shiftrows state) : both _ _ (int128) in
    letb state := (subbytes state) : both _ _ (int128) in
    state.^rkey) : both (L1:|:L2) (I1:|:I2) (int128).
Fail Next Obligation.

Program Definition aes_rounds {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (rkeys : both L1 I1 (Seq_t (int128))) (inp : both L2 I2 (int128)) : both (L1:|:L2) (I1:|:I2) (int128) :=
  (* aes_rounds rkeys inp  := *)
    lift_both (letb state := (inp.^(seq_array_or_seq rkeys.[i32(0)])) : both _ _ (int128) in
    letb state := (foldi_both (into_iter (Build_Range_t i32(1)i32(10))) (fun {L I _ _} =>fun round =>
        (ssp (fun state =>
           (aesenc state (seq_array_or_seq rkeys.[round]))) )) state) : both _ _ (int128) in
                 aesenclast state (seq_array_or_seq rkeys.[i32(10)])) (fsubset_loc := _) (fsubset_opsig := _) : both (L1:|:L2) (I1:|:I2) (int128).
Fail Next Obligation.

Equations aes {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (key : both L1 I1 (int128)) (inp : both L2 I2 (int128)) : both (L1:|:L2 :|: fset [key_loc]) (I1:|:I2) (int128) :=
  aes key inp  :=
    lift_both (letb rkeys := (keys_expand key) : both _ _ (Seq_t (int128)) in
    aes_rounds rkeys inp) : both (L1:|:L2 :|: fset [key_loc]) (I1:|:I2) (int128).
Fail Next Obligation.