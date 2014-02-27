
open Why3__BigInt

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
