(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(*Not implemented yet? todo(item)*)

Require Import Hacspec_lib.

Record WeiestrassCurve_tWeiestrassCurve : Type :={
  bit_size_of_scalar_field : uint_size;
  a6 : T;
  a5 : T;
  a4 : T;
  a3 : T;
  a2 : T;
  a1 : T;
}.

(*trait self todo(item)*)

Instance WeiestrassCurve_t T_Default : Default WeiestrassCurve_t T := {
  default := Build_WeiestrassCurve_t defaultdefaultdefaultdefaultdefaultdefault(@repr WORDSIZE32 0);
}.

Record EllipticCurvePoint_tEllipticCurvePoint : Type :={
  curve : WeiestrassCurve_t T;
  isPointAtInfinity : bool;
  y : T;
  x : T;
}.

(*trait self todo(item)*)

Instance EllipticCurvePoint_t T_Add : Add EllipticCurvePoint_t T EllipticCurvePoint_t T := {
  Output := EllipticCurvePoint_t T;
  add (self : EllipticCurvePoint_t T) (other : EllipticCurvePoint_t T) := run (let curve := (curve self) : WeiestrassCurve_t T in
  let _ := (if
      isPointAtInfinity self
    then
      Break other
    else
      Continue tt) : unit in
  let _ := (if
      isPointAtInfinity other
    then
      Break self
    else
      Continue tt) : unit in
  let _ := (if
      eq self other
    then
      Break (double self)
    else
      Continue tt) : unit in
  let _ := (if
      eq self (neg other)
    then
      Break (Build_EllipticCurvePoint_t defaultdefaulttrue(curve self))
    else
      Continue tt) : unit in
  let x_diff := ((x other).-(x self)) : _ in
  let y_diff := ((y other).-(y self)) : _ in
  let lambda := (div y_diff x_diff) : _ in
  let x3 := (((((exp lambda (@repr WORDSIZE32 2)).+((a1 curve).*lambda)).-(a2 curve)).-(x self)).-(x other)) : _ in
  let y3 := (((((lambda.*(x self)).-((a1 curve).*x3)).-(a3 curve)).-(lambda.*x3)).-(y self)) : _ in
  Break (Build_EllipticCurvePoint_t x3y3false(curve self)));
}.

Instance EllipticCurvePoint_t T_Mul : Mul EllipticCurvePoint_t T U := {
  Output := EllipticCurvePoint_t T;
  mul (self : EllipticCurvePoint_t T) (rhs : U) := run (let _ := (if
      isPointAtInfinity self
    then
      Break self
    else
      Continue tt) : unit in
  Continue (let t := (self) : EllipticCurvePoint_t T in
  let t := (Build_EllipticCurvePoint_t default) : EllipticCurvePoint_t T in
  let t := (Build_EllipticCurvePoint_t default) : EllipticCurvePoint_t T in
  let t := (Build_EllipticCurvePoint_t true) : EllipticCurvePoint_t T in
  let bit_size_of_field := (bit_size_of_scalar_field (curve self)) : uint_size in
  let t := (fold (into_iter (Build_Range_t (@repr WORDSIZE32 0)(bit_size_of_scalar_field (curve self)))) t (fun i t =>
      let t := (double t) : EllipticCurvePoint_t T in
      if
        eq (get_bit rhs ((bit_size_of_field.-(@repr WORDSIZE32 1)).-i)) ONE
      then
        let t := (t.+self) : _ in
        t
      else
        t)) : EllipticCurvePoint_t T in
  t));
}.

Instance EllipticCurvePoint_t T_PartialEq : PartialEq EllipticCurvePoint_t T EllipticCurvePoint_t T := {
  eq (self : EllipticCurvePoint_t T) (other : EllipticCurvePoint_t T) := run (let _ := (if
      ne (x self) (x other)
    then
      Break false
    else
      Continue tt) : unit in
  let _ := (if
      ne (y self) (y other)
    then
      Break false
    else
      Continue tt) : unit in
  let _ := (if
      (isPointAtInfinity self)<>(isPointAtInfinity other)
    then
      Break false
    else
      Continue tt) : unit in
  Break true);
}.

Instance EllipticCurvePoint_t T_Default : Default EllipticCurvePoint_t T := {
  default := Build_EllipticCurvePoint_t defaultdefaulttruedefault;
}.