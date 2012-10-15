#!/usr/bin/env ocaml
#load "unix.cma";;

open Format

let print_args fmt =
  for i = 1 to Array.length Sys.argv - 1 do
    fprintf fmt "%s" Sys.argv.(i);
    if i <> Array.length Sys.argv - 1
    then fprintf fmt " "
  done

let max_sleep =
  try float_of_string (Sys.argv.(1))
  with _ -> 1.0

let () =
  Random.self_init ();
  let sleep = Random.float max_sleep in
  printf "echo %f wait %t@." sleep print_args;
  ignore (Unix.select [] [] [] sleep);
  printf "echo done %t@." print_args
