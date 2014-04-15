
open Why3extract
open Format

let usage () =
  eprintf "Exercises on CPS and de-functionalization@.";
  eprintf "Usage: %s" Sys.argv.(0);
  exit 2

let input =
  if Array.length Sys.argv <> 1 then usage ()


open Defunctionalization__Expr

let rec p_expr fmt e =
  match e with
    | Cte n -> fprintf fmt "%s" (Why3__BigInt.to_string n)
    | Sub(e1,e2) -> 
      fprintf fmt "(%a - %a)" p_expr e1 p_expr e2
  
let p_prog fmt p = p_expr fmt p

let p_value fmt v = 
  fprintf fmt "%s" (Why3__BigInt.to_string v)

let run s f p =
  let v = f p in
  printf "%s %a : %a@." s p_prog p p_value v

let () =
  printf "Exercise 0: direct semantics@.";
  let i = Defunctionalization__DirectSem.interpret_0 in
  run "interpret_0" i Defunctionalization__Expr.p0;
  run "interpret_0" i Defunctionalization__Expr.p1;
  run "interpret_0" i Defunctionalization__Expr.p2;
  run "interpret_0" i Defunctionalization__Expr.p3;
  run "interpret_0" i Defunctionalization__Expr.p4;
  printf "Done.@\n@."

(* does not work because lambda is not extracted into OCaml 
   (fun ... -> ...)

let () =
  printf "Exercise 1: CPS@.";
  let i = Defunctionalization__CPS.interpret_1 in
  run "interpret_1" i Defunctionalization__Expr.p0;
  run "interpret_1" i Defunctionalization__Expr.p1;
  run "interpret_1" i Defunctionalization__Expr.p2;
  run "interpret_1" i Defunctionalization__Expr.p3;
  run "interpret_1" i Defunctionalization__Expr.p4;
  printf "Done.@\n@."

*)

let () =
  printf "Exercise 2: Defunctionalization@.";
  let i = Defunctionalization__Defunctionalization.interpret_2 in
  run "interpret_2" i Defunctionalization__Expr.p0;
  run "interpret_2" i Defunctionalization__Expr.p1;
  run "interpret_2" i Defunctionalization__Expr.p2;
  run "interpret_2" i Defunctionalization__Expr.p3;
  run "interpret_2" i Defunctionalization__Expr.p4;
  printf "Done.@\n@."

