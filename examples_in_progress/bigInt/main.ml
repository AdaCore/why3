
open Why3extract
open Format

let usage () =
  eprintf "Usage: %s <decimal number>@." Sys.argv.(0);
  exit 2

let input =
  if Array.length Sys.argv <> 2 then usage ();
  Sys.argv.(1)

open BigInt__N

let input_num =
  try let a,i = Parse.parse_dec input 0 in a
  with Parse.SyntaxError -> usage ()

let () =
  let a = add input_num input_num in
  let a = add a input_num in
  for i=0 to Array.length a.digits - 1 do
    printf "a[%d] = %d@." i a.digits.(i)
  done
