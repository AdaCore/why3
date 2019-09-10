
open Format

let usage () =
  eprintf "Reduction of combinator terms@.";
  eprintf "Usage: %s <combinator term>@." Sys.argv.(0);
  exit 2

let input =
  if Array.length Sys.argv <> 2 then usage ();
  Sys.argv.(1)

let input_term =
  if input = "go" then
    let i = Vstte12_combinators.i in
    Vstte12_combinators.App(i,i)
  else
    try Parse.parse_term input
    with _ ->
      begin
        eprintf "syntax error@.";
        usage ()
      end

let () =
  let a = Vstte12_combinators.reduction input_term in
  printf "The normal form of %a is %a@."
    Parse.pr input_term Parse.pr a
