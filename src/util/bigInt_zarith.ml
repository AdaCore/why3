
type t = Z.t
let compare = compare_big_int

let zero = zero_big_int
let of_int = big_int_of_int

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


let euclidean_div_mod = quomod_big_int

let euclidean_div x y = fst (euclidean_div_mod x y)

let euclidean_mod x y = snd (euclidean_div_mod x y)

let computer_div_mod x y =
  let q,r = quomod_big_int x y in
  (* we have x = q*y + r with 0 <= r < |y| *)
  if sign x < 0 then
    if sign y < 0 
    then (pred q, add r y)
    else (succ q, sub r y)
  else (q,r)

let computer_div x y = fst (computer_div_mod x y)

let computer_mod x y = snd (computer_div_mod x y)

let min = min_big_int
let max = max_big_int

let pow_int_pos = power_int_positive_int

let to_string = string_of_big_int
let of_string = big_int_of_string
