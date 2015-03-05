
open Why3extract
open Format

let usage () =
  eprintf "Sudoku: solve a Sudoku puzzle@.";
  eprintf "Usage: %s <comma separated sequence of 81 non-zero digits>@." Sys.argv.(0);
  exit 2

let input =
  if Array.length Sys.argv <> 2 then usage ();
  Sys.argv.(1)

let input_grid =
  if String.length input <> 161 then usage ();
  for i=0 to 79 do
    if input.[i+i+1] <> ',' then usage ();
  done;
  let a = Array.make 81 Why3__BigInt.zero in
  for i=0 to 80 do
    match input.[i+i] with
      | '0'..'9' as c -> a.(i) <-
        Why3__BigInt.of_int (Char.code c - Char.code '0')
      | _ -> usage ()
  done;
  a

let print_grid fmt a =
  fprintf fmt "@[";
  for i=0 to 80 do
    if i mod 9 = 8
    then fprintf fmt "%s@\n" (Why3__BigInt.to_string a.(i))
    else fprintf fmt "%s " (Why3__BigInt.to_string a.(i))
  done;
  fprintf fmt "@]"

let () =
  let sudoku = Sudoku__TheClassicalSudokuGrid.classical_sudoku () in
  printf "Problem: %a@." print_grid input_grid;
  let a = Sudoku__Solver.solve sudoku input_grid
  in
  printf "Solution: %a@." print_grid a

(*
test:

2,0,9,0,0,0,0,1,0,0,0,0,0,6,0,0,0,0,0,5,3,8,0,2,7,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,7,5,0,0,3,0,4,1,2,0,8,9,0,0,0,0,4,0,9,0,0,2,0,8,0,0,0,0,1,0,0,5,0,0,0,0,0,0,0,7,6

that is

2 0 9 0 0 0 0 1 0
0 0 0 0 6 0 0 0 0
0 5 3 8 0 2 7 0 0
3 0 0 0 0 0 0 0 0
0 0 0 0 7 5 0 0 3
0 4 1 2 0 8 9 0 0
0 0 4 0 9 0 0 2 0
8 0 0 0 0 1 0 0 5
0 0 0 0 0 0 0 7 6

should give:

2 6 9 3 5 7 8 1 4
1 8 7 9 6 4 5 3 2
4 5 3 8 1 2 7 6 9
3 7 5 6 4 9 2 8 1
9 2 8 1 7 5 6 4 3
6 4 1 2 3 8 9 5 7
7 1 4 5 9 6 3 2 8
8 3 6 7 2 1 4 9 5
5 9 2 4 8 3 1 7 6

*)

(* other tests:

7,0,0,0,0,0,0,0,8,0,9,0,7,0,6,0,3,0,0,0,1,0,0,0,9,0,0,0,7,0,1,0,4,0,5,0,0,0,0,0,6,0,0,0,0,0,5,0,3,0,7,0,1,0,0,0,2,0,0,0,1,0,0,0,1,0,9,0,8,0,7,0,8,0,0,0,0,0,0,0,6

0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,8,5,0,0,1,0,2,0,0,0,0,0,0,0,5,0,7,0,0,0,0,0,4,0,0,0,1,0,0,0,9,0,0,0,0,0,0,0,5,0,0,0,0,0,0,7,3,0,0,2,0,1,0,0,0,0,0,0,0,0,4,0,0,0,9

*)
