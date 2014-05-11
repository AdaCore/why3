
open Why3extract
open Format

let usage () =
  eprintf "Usage: %s <decimal number>@." Sys.argv.(0);
  exit 2

let input =
  if Array.length Sys.argv <> 2 then usage ();
  Sys.argv.(1)

open Mp__N

let input_num =
  try let a,i = Parse.parse_dec input 0 in a
  with Parse.SyntaxError -> usage ()

let () =
  Format.printf "zero   : %a@." Parse.pr (zero ());
  Format.printf "one    : %a@." Parse.pr (from_limb 1L);
  Format.printf "2^{32} : %a@." Parse.pr (from_limb 0x100000000L);
  Format.printf "input  : %a@." Parse.pr input_num;
  let a = add input_num input_num in
  Format.printf "times 2: %a@." Parse.pr a;
  let a = add a input_num in
  Format.printf "times 3: %a@." Parse.pr a
