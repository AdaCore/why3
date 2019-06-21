
open Format

let usage () =
  eprintf "Euler001: sum of all the multiples of 3 or 5 below a given number@.";
  eprintf "Usage: %s <decimal number>@." Sys.argv.(0);
  exit 2

let input =
  if Array.length Sys.argv <> 2 then usage ();
  Sys.argv.(1)

(*
let () =
  if input = "go" then begin
    Euler001.go ();
    exit 0
  end
*)

let input_num =
  try
    Z.of_string input
  with _ -> usage ()

let () =
  let a = Euler001.solve input_num in
  printf "The sum of all the multiples of 3 or 5 below %s is %s@."
    (Z.to_string input_num) (Z.to_string a)
