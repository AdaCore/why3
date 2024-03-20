
open Format
open Residual

let r1 = Concat (Star (Alt (Char 'a', Char 'b')), Char 'a')

let () = assert (decide "a" r1)
let () = assert (decide "aaaa" r1)
let () = assert (decide "ba" r1)
let () = assert (decide "aba" r1)
let () = assert (not (decide "" r1))
let () = assert (not (decide "b" r1))
let () = assert (not (decide "ab" r1))
