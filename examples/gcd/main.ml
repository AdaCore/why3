
open Why3extract
open Format

let () =
  printf "%d@."
    (Gcd__EuclideanAlgorithm31.euclid (int_of_string  Sys.argv.(1)) (int_of_string  Sys.argv.(2)))

(*
let usage () =
  eprintf "Reduction of combinator terms@.";
  eprintf "Usage: %s <combinator term>@." Sys.argv.(0);
  exit 2

let input =
  if Array.length Sys.argv <> 2 then usage ();
  Sys.argv.(1)

let input_term =
  if input = "go" then
    let i = Vstte12_combinators__Combinators.i in
    Vstte12_combinators__Combinators.App(i,i)
  else
    try Parse.parse_term input
    with _ ->
      begin
        eprintf "syntax error@.";
        usage ()
      end

let () =
  let a = Vstte12_combinators__Combinators.reduction input_term in
  printf "The normal form of %a is %a@."
    Parse.pr input_term Parse.pr a
*)
