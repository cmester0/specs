(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(*Not implemented yet? todo(item)*)

Require Import Hacspec_lib.

Inductive Error_t : Type :=
| InvalidAdditionError_t.

Definition BITS : uint_size :=
  (@repr WORDSIZE32 256).

Notation FieldCanvas := (nseq int8 256).
Notation P256FieldElement_t := (nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff).
Definition P256FieldElement : P256FieldElement_t -> P256FieldElement_t :=
  id.

Notation ScalarCanvas := (nseq int8 256).
Notation P256Scalar_t := (nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551).
Definition P256Scalar : P256Scalar_t -> P256Scalar_t :=
  id.

Notation Affine_t := ((P256FieldElement_t × P256FieldElement_t)).

Notation AffineResult_t := (Result_t ((P256FieldElement_t × P256FieldElement_t)) (Error_t)).

Notation P256Jacobian_t := ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)).

Notation JacobianResult_t := (Result_t ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (Error_t)).

Notation Element_t := (nseq int8 32).
Definition Element : Element_t -> Element_t :=
  id.

Definition jacobian_to_affine (p : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) : (P256FieldElement_t × P256FieldElement_t) :=
  let '(x,y,z) := (p) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
  let z2 := (exp z (@repr WORDSIZE32 2)) : P256FieldElement_t in
  let z2i := (inv z2) : P256FieldElement_t in
  let z3 := (z.*z2) : _ in
  let z3i := (inv z3) : P256FieldElement_t in
  let x := (x.*z2i) : _ in
  let y := (y.*z3i) : _ in
  (x,y).

Definition affine_to_jacobian (p : (P256FieldElement_t × P256FieldElement_t)) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) :=
  let '(x,y) := (p) : (P256FieldElement_t × P256FieldElement_t) in
  (x,y,from_literal (@repr WORDSIZE128 1)).

Definition point_double (p : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) :=
  let '(x1,y1,z1) := (p) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
  let delta := (exp z1 (@repr WORDSIZE32 2)) : P256FieldElement_t in
  let gamma := (exp y1 (@repr WORDSIZE32 2)) : P256FieldElement_t in
  let beta := (x1.*gamma) : _ in
  let alpha_1 := (x1.-delta) : _ in
  let alpha_2 := (x1.+delta) : _ in
  let alpha := ((from_literal (@repr WORDSIZE128 3)).*(alpha_1.*alpha_2)) : _ in
  let x3 := ((exp alpha (@repr WORDSIZE32 2)).-((from_literal (@repr WORDSIZE128 8)).*beta)) : _ in
  let z3_ := (exp (y1.+z1) (@repr WORDSIZE32 2)) : P256FieldElement_t in
  let z3 := (z3_.-(gamma.+delta)) : _ in
  let y3_1 := (((from_literal (@repr WORDSIZE128 4)).*beta).-x3) : _ in
  let y3_2 := ((from_literal (@repr WORDSIZE128 8)).*(gamma.*gamma)) : _ in
  let y3 := ((alpha.*y3_1).-y3_2) : _ in
  (x3,y3,z3).

Definition is_point_at_infinity (p : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) : bool :=
  let '(_x,_y,z) := (p) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
  equal z (from_literal (@repr WORDSIZE128 0)).

Definition s1_equal_s2 (s1 : P256FieldElement_t) (s2 : P256FieldElement_t) : Result_t ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (Error_t) :=
  if
    equal s1 s2
  then
    Err InvalidAdditionError_t
  else
    Ok (from_literal (@repr WORDSIZE128 0),from_literal (@repr WORDSIZE128 1),from_literal (@repr WORDSIZE128 0)).

Definition point_add_jacob (p : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (q : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) : Result_t ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (Error_t) :=
  let result := (Ok q) : Result_t ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (Error_t) in
  let result := (if
      MachineIntegers.not (is_point_at_infinity p)
    then
      if
        is_point_at_infinity q
      then
        let result := (Ok p) : Result_t ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (Error_t) in
        result
      else
        let '(x1,y1,z1) := (p) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
        let '(x2,y2,z2) := (q) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
        let z1z1 := (exp z1 (@repr WORDSIZE32 2)) : P256FieldElement_t in
        let z2z2 := (exp z2 (@repr WORDSIZE32 2)) : P256FieldElement_t in
        let u1 := (x1.*z2z2) : _ in
        let u2 := (x2.*z1z1) : _ in
        let s1 := ((y1.*z2).*z2z2) : _ in
        let s2 := ((y2.*z1).*z1z1) : _ in
        if
          equal u1 u2
        then
          let result := (s1_equal_s2 s1 s2) : Result_t ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (Error_t) in
          result
        else
          let h := (u2.-u1) : _ in
          let i := (exp ((from_literal (@repr WORDSIZE128 2)).*h) (@repr WORDSIZE32 2)) : P256FieldElement_t in
          let j := (h.*i) : _ in
          let r := ((from_literal (@repr WORDSIZE128 2)).*(s2.-s1)) : _ in
          let v := (u1.*i) : _ in
          let x3_1 := ((from_literal (@repr WORDSIZE128 2)).*v) : _ in
          let x3_2 := ((exp r (@repr WORDSIZE32 2)).-j) : _ in
          let x3 := (x3_2.-x3_1) : _ in
          let y3_1 := (((from_literal (@repr WORDSIZE128 2)).*s1).*j) : _ in
          let y3_2 := (r.*(v.-x3)) : _ in
          let y3 := (y3_2.-y3_1) : _ in
          let z3_ := (exp (z1.+z2) (@repr WORDSIZE32 2)) : P256FieldElement_t in
          let z3 := ((z3_.-(z1z1.+z2z2)).*h) : _ in
          let result := (Ok (x3,y3,z3)) : Result_t ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (Error_t) in
          result
    else
      result) : Result_t ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (Error_t) in
  result.

Definition ltr_mul (k : P256Scalar_t) (p : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) : Result_t ((P256FieldElement_t × P256FieldElement_t × P256FieldElement_t)) (Error_t) :=
  let q := ((from_literal (@repr WORDSIZE128 0),from_literal (@repr WORDSIZE128 1),from_literal (@repr WORDSIZE128 0))) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
  let q := (fold (into_iter (Build_Range_t (@repr WORDSIZE32 0)BITS)) q (fun i q =>
      let q := (point_double q) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
      if
        equal (get_bit k ((BITS.-(@repr WORDSIZE32 1)).-i)) ONE
      then
        let hoist1 := (point_add_jacob q p) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
        Ok (let q := (hoist1) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
        q)
      else
        Ok q)) : (P256FieldElement_t × P256FieldElement_t × P256FieldElement_t) in
  Ok q.

Definition p256_point_mul (k : P256Scalar_t) (p : (P256FieldElement_t × P256FieldElement_t)) : Result_t ((P256FieldElement_t × P256FieldElement_t)) (Error_t) :=
  let jac := (from_residual (ltr_mul k (affine_to_jacobian p))) : Result_t ((P256FieldElement_t × P256FieldElement_t)) (Error_t) in
  Ok (jacobian_to_affine jac).

Definition p256_point_mul_base (k : P256Scalar_t) : Result_t ((P256FieldElement_t × P256FieldElement_t)) (Error_t) :=
  let base_point := ((from_byte_seq_be (Element (array_from_list [secret (@repr WORDSIZE8 107);
        secret (@repr WORDSIZE8 23);
        secret (@repr WORDSIZE8 209);
        secret (@repr WORDSIZE8 242);
        secret (@repr WORDSIZE8 225);
        secret (@repr WORDSIZE8 44);
        secret (@repr WORDSIZE8 66);
        secret (@repr WORDSIZE8 71);
        secret (@repr WORDSIZE8 248);
        secret (@repr WORDSIZE8 188);
        secret (@repr WORDSIZE8 230);
        secret (@repr WORDSIZE8 229);
        secret (@repr WORDSIZE8 99);
        secret (@repr WORDSIZE8 164);
        secret (@repr WORDSIZE8 64);
        secret (@repr WORDSIZE8 242);
        secret (@repr WORDSIZE8 119);
        secret (@repr WORDSIZE8 3);
        secret (@repr WORDSIZE8 125);
        secret (@repr WORDSIZE8 129);
        secret (@repr WORDSIZE8 45);
        secret (@repr WORDSIZE8 235);
        secret (@repr WORDSIZE8 51);
        secret (@repr WORDSIZE8 160);
        secret (@repr WORDSIZE8 244);
        secret (@repr WORDSIZE8 161);
        secret (@repr WORDSIZE8 57);
        secret (@repr WORDSIZE8 69);
        secret (@repr WORDSIZE8 216);
        secret (@repr WORDSIZE8 152);
        secret (@repr WORDSIZE8 194);
        secret (@repr WORDSIZE8 150)])),from_byte_seq_be (Element (array_from_list [secret (@repr WORDSIZE8 79);
        secret (@repr WORDSIZE8 227);
        secret (@repr WORDSIZE8 66);
        secret (@repr WORDSIZE8 226);
        secret (@repr WORDSIZE8 254);
        secret (@repr WORDSIZE8 26);
        secret (@repr WORDSIZE8 127);
        secret (@repr WORDSIZE8 155);
        secret (@repr WORDSIZE8 142);
        secret (@repr WORDSIZE8 231);
        secret (@repr WORDSIZE8 235);
        secret (@repr WORDSIZE8 74);
        secret (@repr WORDSIZE8 124);
        secret (@repr WORDSIZE8 15);
        secret (@repr WORDSIZE8 158);
        secret (@repr WORDSIZE8 22);
        secret (@repr WORDSIZE8 43);
        secret (@repr WORDSIZE8 206);
        secret (@repr WORDSIZE8 51);
        secret (@repr WORDSIZE8 87);
        secret (@repr WORDSIZE8 107);
        secret (@repr WORDSIZE8 49);
        secret (@repr WORDSIZE8 94);
        secret (@repr WORDSIZE8 206);
        secret (@repr WORDSIZE8 203);
        secret (@repr WORDSIZE8 182);
        secret (@repr WORDSIZE8 64);
        secret (@repr WORDSIZE8 104);
        secret (@repr WORDSIZE8 55);
        secret (@repr WORDSIZE8 191);
        secret (@repr WORDSIZE8 81);
        secret (@repr WORDSIZE8 245)])))) : (P256FieldElement_t × P256FieldElement_t) in
  p256_point_mul k base_point.

Definition point_add_distinct (p : (P256FieldElement_t × P256FieldElement_t)) (q : (P256FieldElement_t × P256FieldElement_t)) : Result_t ((P256FieldElement_t × P256FieldElement_t)) (Error_t) :=
  let r := (from_residual (point_add_jacob (affine_to_jacobian p) (affine_to_jacobian q))) : Result_t ((P256FieldElement_t × P256FieldElement_t)) (Error_t) in
  Ok (jacobian_to_affine r).

Definition point_add (p : (P256FieldElement_t × P256FieldElement_t)) (q : (P256FieldElement_t × P256FieldElement_t)) : Result_t ((P256FieldElement_t × P256FieldElement_t)) (Error_t) :=
  if
    ne p q
  then
    point_add_distinct p q
  else
    Ok (jacobian_to_affine (point_double (affine_to_jacobian p))).

Definition p256_validate_private_key (k : Seq_t U8_t) : bool :=
  let valid := (true) : bool in
  let k_element := (from_byte_seq_be k) : P256Scalar_t in
  let k_element_bytes := (to_byte_seq_be k_element) : Seq_t U8_t in
  let all_zero := (true) : bool in
  let '(all_zero,valid) := (fold (into_iter (Build_Range_t (@repr WORDSIZE32 0)(len k))) (all_zero,valid) (fun i '(all_zero,valid) =>
      let all_zero := (if
          MachineIntegers.not (equal (k.[i]) (secret (@repr WORDSIZE8 0)))
        then
          let all_zero := (false) : bool in
          all_zero
        else
          all_zero) : bool in
      if
        MachineIntegers.not (equal (k_element_bytes.[i]) (k.[i]))
      then
        let valid := (false) : bool in
        (all_zero,valid)
      else
        (all_zero,valid))) : (bool × bool) in
  andb valid (MachineIntegers.not all_zero).

Definition p256_validate_public_key (p : (P256FieldElement_t × P256FieldElement_t)) : bool :=
  let b := (from_byte_seq_be (from_vec (into_vec (unsize (array_from_list [secret (@repr WORDSIZE8 90);
      secret (@repr WORDSIZE8 198);
      secret (@repr WORDSIZE8 53);
      secret (@repr WORDSIZE8 216);
      secret (@repr WORDSIZE8 170);
      secret (@repr WORDSIZE8 58);
      secret (@repr WORDSIZE8 147);
      secret (@repr WORDSIZE8 231);
      secret (@repr WORDSIZE8 179);
      secret (@repr WORDSIZE8 235);
      secret (@repr WORDSIZE8 189);
      secret (@repr WORDSIZE8 85);
      secret (@repr WORDSIZE8 118);
      secret (@repr WORDSIZE8 152);
      secret (@repr WORDSIZE8 134);
      secret (@repr WORDSIZE8 188);
      secret (@repr WORDSIZE8 101);
      secret (@repr WORDSIZE8 29);
      secret (@repr WORDSIZE8 6);
      secret (@repr WORDSIZE8 176);
      secret (@repr WORDSIZE8 204);
      secret (@repr WORDSIZE8 83);
      secret (@repr WORDSIZE8 176);
      secret (@repr WORDSIZE8 246);
      secret (@repr WORDSIZE8 59);
      secret (@repr WORDSIZE8 206);
      secret (@repr WORDSIZE8 60);
      secret (@repr WORDSIZE8 62);
      secret (@repr WORDSIZE8 39);
      secret (@repr WORDSIZE8 210);
      secret (@repr WORDSIZE8 96);
      secret (@repr WORDSIZE8 75)]))))) : P256FieldElement_t in
  let point_at_infinity := (is_point_at_infinity (affine_to_jacobian p)) : bool in
  let '(x,y) := (p) : (P256FieldElement_t × P256FieldElement_t) in
  let on_curve := (eq (y.*y) ((((x.*x).*x).-((from_literal (@repr WORDSIZE128 3)).*x)).+b)) : bool in
  andb (MachineIntegers.not point_at_infinity) on_curve.

Definition p256_calculate_w (x : P256FieldElement_t) : P256FieldElement_t :=
  let b := (from_byte_seq_be (from_vec (into_vec (unsize (array_from_list [secret (@repr WORDSIZE8 90);
      secret (@repr WORDSIZE8 198);
      secret (@repr WORDSIZE8 53);
      secret (@repr WORDSIZE8 216);
      secret (@repr WORDSIZE8 170);
      secret (@repr WORDSIZE8 58);
      secret (@repr WORDSIZE8 147);
      secret (@repr WORDSIZE8 231);
      secret (@repr WORDSIZE8 179);
      secret (@repr WORDSIZE8 235);
      secret (@repr WORDSIZE8 189);
      secret (@repr WORDSIZE8 85);
      secret (@repr WORDSIZE8 118);
      secret (@repr WORDSIZE8 152);
      secret (@repr WORDSIZE8 134);
      secret (@repr WORDSIZE8 188);
      secret (@repr WORDSIZE8 101);
      secret (@repr WORDSIZE8 29);
      secret (@repr WORDSIZE8 6);
      secret (@repr WORDSIZE8 176);
      secret (@repr WORDSIZE8 204);
      secret (@repr WORDSIZE8 83);
      secret (@repr WORDSIZE8 176);
      secret (@repr WORDSIZE8 246);
      secret (@repr WORDSIZE8 59);
      secret (@repr WORDSIZE8 206);
      secret (@repr WORDSIZE8 60);
      secret (@repr WORDSIZE8 62);
      secret (@repr WORDSIZE8 39);
      secret (@repr WORDSIZE8 210);
      secret (@repr WORDSIZE8 96);
      secret (@repr WORDSIZE8 75)]))))) : P256FieldElement_t in
  let exp := (from_byte_seq_be (from_vec (into_vec (unsize (array_from_list [secret (@repr WORDSIZE8 63);
      secret (@repr WORDSIZE8 255);
      secret (@repr WORDSIZE8 255);
      secret (@repr WORDSIZE8 255);
      secret (@repr WORDSIZE8 192);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 64);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 64);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0);
      secret (@repr WORDSIZE8 0)]))))) : P256FieldElement_t in
  let z := ((((x.*x).*x).-((from_literal (@repr WORDSIZE128 3)).*x)).+b) : _ in
  pow_felem z exp.
