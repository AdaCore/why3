
open Why3__BigInt

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

