
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
  try let a,i = Parse.parse_dec_ip input 0 in a
  with Parse.SyntaxError -> usage ()

let () =
  let z = zero () in
  Format.printf "zero       : %a@." Parse.pr z;
  let a = from_limb 1L in
  Format.printf "one        : %a@." Parse.pr a;
  let a = from_limb 0xFFFFFFFFL in
  Format.printf "2^{32}-1   : %a@." Parse.pr a;
  add_in_place z a;
  Format.printf "0 + 2^{32}-1 : %a@." Parse.pr z;
  add_in_place a (from_limb 1L);
  Format.printf "2^{32}-1+1 : %a@." Parse.pr a;
  let a = copy input_num in
  Format.printf "input      : %a@." Parse.pr a;
  add_in_place a input_num;
  Format.printf "times 2    : %a@." Parse.pr a;
  add_in_place a input_num ;
  Format.printf "times 3    : %a@." Parse.pr a
