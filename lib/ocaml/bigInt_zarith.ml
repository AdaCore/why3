
open Big_int_Z

type t = Z.t
let compare = compare_big_int

let zero = zero_big_int
let one = unit_big_int
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

let lt_nat x y = le zero y && lt x y
let lex (x1,x2) (y1,y2) = lt x1 y1 || eq x1 y1 && lt x2 y2

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
let abs = abs_big_int

let pow_int_pos = power_int_positive_int

let to_string = string_of_big_int
let of_string = big_int_of_string
let to_int = int_of_big_int

(* the code below is to be used in OCaml extracted code (see ocaml.drv) *)

let power x y = try power_big x y with Invalid_argument _ -> zero

let rec fact n = if le n one then one else mul n (fact (pred n))

let fib n =
  let n = to_int n in
  if n = 0 then zero else if n = 1 then one else
  let a = Array.make (n + 1) zero in
  a.(1) <- one; for i = 2 to n do a.(i) <- add a.(i-2) a.(i-1) done; a.(n)

let rec for_loop_to x1 x2 body =
  if le x1 x2 then begin
    body x1;
    for_loop_to (succ x1) x2 body
  end

let rec for_loop_downto x1 x2 body =
  if ge x1 x2 then begin
    body x1;
    for_loop_downto (pred x1) x2 body
  end

module Array = struct
  type 'a t = 'a array
  let get a i = a.(to_int i)
  let set a i v = a.(to_int i) <- v
  let length a = of_int (Array.length a)
  exception OutOfBounds
  let check_bounds a i = if i < 0 || i >= Array.length a then raise OutOfBounds
  let defensive_get a i = let i = to_int i in check_bounds a i; a.(i)
  let defensive_set a i v = let i = to_int i in check_bounds a i; a.(i) <- v
  let make n v = Array.make (to_int n) v
  let append = Array.append
  let sub a ofs len = Array.sub a (to_int ofs) (to_int len)
  let copy = Array.copy
  let fill a ofs len v = Array.fill a (to_int ofs) (to_int len) v
  let blit a1 ofs1 a2 ofs2 len =
    Array.blit a1 (to_int ofs1) a2 (to_int ofs2) (to_int len)
end
