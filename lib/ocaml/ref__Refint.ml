(* This file has been generated from Why3 module ref.Refint *)

let incr (r: (Why3__BuiltIn.int Pervasives.ref)) =
  let o =
    (let o1 = (Pervasives.(!) r) in
    (Int__Int.infix_pl o1 (Why3__BuiltIn.int_constant "1"))) in
  ((Pervasives.(:=) r) o)

let decr (r1: (Why3__BuiltIn.int Pervasives.ref)) =
  let o =
    (let o1 = (Pervasives.(!) r1) in
    (Int__Int.infix_mn o1 (Why3__BuiltIn.int_constant "1"))) in
  ((Pervasives.(:=) r1) o)

let infix_pleq (r2: (Why3__BuiltIn.int Pervasives.ref))
  (v: Why3__BuiltIn.int) =
  let o = (let o1 = (Pervasives.(!) r2) in
    (Int__Int.infix_pl o1 v)) in
  ((Pervasives.(:=) r2) o)

let infix_mneq (r3: (Why3__BuiltIn.int Pervasives.ref))
  (v1: Why3__BuiltIn.int) =
  let o = (let o1 = (Pervasives.(!) r3) in
    (Int__Int.infix_mn o1 v1)) in
  ((Pervasives.(:=) r3) o)

let infix_aseq (r4: (Why3__BuiltIn.int Pervasives.ref))
  (v2: Why3__BuiltIn.int) =
  let o = (let o1 = (Pervasives.(!) r4) in
    (Int__Int.infix_as o1 v2)) in
  ((Pervasives.(:=) r4) o)


