(* Experimental module under development *)

exception Undetermined

open Mlmpfr_wrapper
type real = mpfr_float * mpfr_float

(* TODO in all the following getting to plus_infinity or to zero on both side of
   the interval should always be seen as an error. The precision should be
   increased in those cases.
   For example, we cannot simplify multiplication of [0; 0] with ]+inf; +inf[
   because both may mean that the underlying floats overflow/underflow and the
   result can be far from the solutions we get. Example: divide a number by 10 a
   lot and then multiply the result by 10 the same number of time + 1. You would
   obtain 0 whereas you would like to obtain number * 10.
*)

(* TODO precision cannot be changed once launched the first time. So we need
   to init it once. *)
let init, set_exponents, get_prec =
  let emin = ref (-148) in
  let emax = ref 128 in
  let prec = ref 24 in
  (fun emin_i emax_i prec_i ->
    emin := emin_i;
    emax := emax_i;
    prec := prec_i),
  (fun () ->
    set_emin !emin;
    set_emax !emax),
  (fun () -> !prec)

let add (xmin, xmax) (ymin, ymax) =
  (* Exponents can be changed if floats occur in the code. *)
  set_exponents ();
  let prec = get_prec () in
  let res_min = add ~prec ~rnd:Toward_Minus_Infinity xmin ymin in
  let res_max = add ~prec ~rnd:Toward_Plus_Infinity xmax ymax in
  (res_min, res_max)

let neg (xmin, xmax) =
  set_exponents ();
  let prec = get_prec () in
  let res_min = neg ~prec ~rnd:Toward_Minus_Infinity xmax in
  let res_max = neg ~prec ~rnd:Toward_Plus_Infinity xmin in
  (res_min, res_max)

let mul (xmin, xmax) (ymin, ymax) =
  set_exponents ();
  let prec = get_prec () in
  let min = min ~prec ~rnd:Toward_Minus_Infinity in
  let max = max ~prec ~rnd:Toward_Plus_Infinity in
  let mul1_min = mul ~prec ~rnd:Toward_Minus_Infinity xmin ymin in
  let mul2_min = mul ~prec ~rnd:Toward_Minus_Infinity xmin ymax in
  let mul3_min = mul ~prec ~rnd:Toward_Minus_Infinity xmax ymin in
  let mul4_min = mul ~prec ~rnd:Toward_Minus_Infinity xmax ymax in
  let res_min = List.fold_left min mul1_min [mul2_min; mul3_min; mul4_min] in
  let mul1_max = mul ~prec ~rnd:Toward_Plus_Infinity xmin ymin in
  let mul2_max = mul ~prec ~rnd:Toward_Plus_Infinity xmin ymax in
  let mul3_max = mul ~prec ~rnd:Toward_Plus_Infinity xmax ymin in
  let mul4_max = mul ~prec ~rnd:Toward_Plus_Infinity xmax ymax in
  let res_max = List.fold_left max mul1_max [mul2_max; mul3_max; mul4_max] in
  (res_min, res_max)

let inv (xmin, xmax) =
  set_exponents ();
  let prec = get_prec () in
  (* If 0 is inside the interval we cannot compute the expression. The precision
     should be increased. *)
  if signbit xmin <> signbit xmax then
    raise Undetermined
  else
    let one = make_from_int ~prec ~rnd:Toward_Minus_Infinity 1 in
    let inv1_min = div ~prec ~rnd:Toward_Minus_Infinity one xmin in
    let inv2_min = div ~prec ~rnd:Toward_Minus_Infinity one xmax in
    let res_min = min inv1_min inv2_min in
    let inv1_max = div ~prec ~rnd:Toward_Plus_Infinity one xmin in
    let inv2_max = div ~prec ~rnd:Toward_Plus_Infinity one xmax in
    let res_max = max inv1_max inv2_max in
    (res_min, res_max)

let div x y =
  mul x (inv y)

let sqrt (xmin, xmax) =
  set_exponents ();
  let prec = get_prec() in
  if lessequal_p (make_zero ~prec Positive) xmin then
    let res_min = sqrt ~rnd:Toward_Minus_Infinity ~prec xmin in
    let res_max = sqrt ~rnd:Toward_Plus_Infinity ~prec xmax in
    (res_min, res_max)
  else
    raise Undetermined

let real_from_str s =
  let prec = get_prec () in
  let n = make_from_str ~prec ~base:10 s in
  (n, n)

let real_from_fraction p q =
  let p = real_from_str p in
  let q = real_from_str q in
  div p q

let print_real fmt r =
  let (x, y) = r in
  let x = get_formatted_str ~base:10 x in
  let y = get_formatted_str ~base:10 y in
  Format.fprintf fmt "[%s, %s]" x y

let eq (xmin, xmax) (ymin, ymax) =
  if (equal_p xmin xmax) && (equal_p ymin ymax) then
    equal_p xmin ymin
  else
    raise Undetermined

let lt x y =
  if less_p (snd x) (fst y) then
    true
  else
    if less_p (fst x) (snd y) then
      false
    else
      raise Undetermined

let le x y =
  if lessequal_p (snd x) (fst y) then
    true
  else
    if less_p (snd y) (fst x) then
      false
    else
      raise Undetermined

let pi =
  let prec = get_prec () in
  const_pi prec, const_pi prec
