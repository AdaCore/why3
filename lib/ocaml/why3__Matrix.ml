
open Why3__BigInt

type 'a t = 'a array array
let get m i j = m.(to_int i).(to_int j)
let set m i j v = m.(to_int i).(to_int j) <- v
let rows m = of_int (Array.length m)
let columns m =
  if Array.length m = 0 then invalid_arg "Why3__Matrix.columns";
  of_int (Array.length m.(0))
exception OutOfBounds
let check_bounds a i = if i < 0 || i >= Array.length a then raise OutOfBounds
let defensive_get m i j =
  let i = to_int i in let j = to_int j in
  check_bounds m i; check_bounds m.(i) j; m.(i).(j)
let defensive_set m i j v =
  let i = to_int i in let j = to_int j in
  check_bounds m i; check_bounds m.(i) j; m.(i).(j) <- v
let make n m v = Array.make_matrix (to_int n) (to_int m) v
let copy m = Array.map Array.copy m
