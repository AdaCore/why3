
open Why3__BigInt_compat

type t = Why3__BigInt_compat.big_int

let compare = compare_big_int

let zero = zero_big_int
let one = unit_big_int

let succ = succ_big_int
let pred = pred_big_int

let add_int = add_int_big_int
let mul_int = mult_int_big_int

let add = add_big_int
let sub = sub_big_int
let mul = mult_big_int
let minus = minus_big_int

let sign = sign_big_int

let eq = eq_big_int
let lt = lt_big_int
let gt = gt_big_int
let le = le_big_int
let ge = ge_big_int

let lt_nat x y = le zero y && lt x y
let lex (x1,x2) (y1,y2) = lt x1 y1 || eq x1 y1 && lt x2 y2

let euclidean_div_mod x y =
  if eq y zero then zero, zero else quomod_big_int x y

let euclidean_div x y = fst (euclidean_div_mod x y)
let euclidean_mod x y = snd (euclidean_div_mod x y)

let computer_div_mod x y =
  let q,r = euclidean_div_mod x y in
  (* when y <> 0, we have x = q*y + r with 0 <= r < |y| *)
  if sign x < 0 then
    if sign y < 0
    then (pred q, add r y)
    else (succ q, sub r y)
  else (q,r)

let computer_div x y = fst (computer_div_mod x y)
let computer_mod x y = snd (computer_div_mod x y)

let min = min_big_int
let max = max_big_int
let abs = abs_big_int

let pow_int_pos = power_int_positive_int

let to_string = string_of_big_int
let of_string = big_int_of_string

let to_int = int_of_big_int
let of_int = big_int_of_int

let to_int32 = int32_of_big_int
let of_int32 = big_int_of_int32

let to_int64 = int64_of_big_int
let of_int64 = big_int_of_int64

let power x y =
  try power_big_int_positive_big_int x y
  with Invalid_argument _ -> zero

let print n = Pervasives.print_string (to_string n)
let chr n = Pervasives.char_of_int (to_int n)
let code c = of_int (Pervasives.int_of_char c)


let random_int n =
  try let n = int64_of_big_int n in
      if n >= 0L then big_int_of_int64 (Random.int64 n) else raise Exit
  with _ -> invalid_arg "Why3__BigInt.random"
