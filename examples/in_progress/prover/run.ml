
open Firstorder_symbol_impl__Types
open Firstorder_term_impl__Types
open Firstorder_formula_impl__Types
open Firstorder_formula_list_impl__Types

open Format

let pr_symbol fmt s =
  match s with
  | NLFVar_symbol v ->
    fprintf fmt "f%s" (Why3extract.Why3__BigInt.to_string v)
  | NLBruijn_symbol n ->
    fprintf fmt "v%s" (Why3extract.Why3__BigInt.to_string n)

let rec pr_term fmt t =
  match t with
  | NLFVar_fo_term v ->
    fprintf fmt "f%s" (Why3extract.Why3__BigInt.to_string v)
  | NLBruijn_fo_term n ->
    fprintf fmt "v%s" (Why3extract.Why3__BigInt.to_string n)
  | NL_App(s,tl) ->
    fprintf fmt "%a%a" pr_symbol s pr_term_list tl

and pr_term_list fmt tl =
  match tl with
  | NL_FONil -> fprintf fmt "()"
  | NL_FOCons(t,tl) ->
      fprintf fmt "@[<hov 2>(%a%a)@]" pr_term t pr_term_list_tail tl

and pr_term_list_tail fmt tl =
  match tl with
    | NL_FONil -> ()
    | NL_FOCons(t,tl) ->
      fprintf fmt ",@ %a%a" pr_term t pr_term_list_tail tl

let pr_term_impl fmt t = pr_term fmt t.nlrepr_fo_term_field

let rec pr_formula fmt f =
  match f with
  | NL_Forall f -> fprintf fmt "@[<hov 2>(forall@ %a)@]" pr_formula f
  | NL_Exists f  -> fprintf fmt "@[<hov 2>(exists@ %a)@]" pr_formula f
  | NL_And(f1,f2) ->
    fprintf fmt "@[<hov 2>(%a@ and %a)@]" pr_formula f1 pr_formula f2
  | NL_Or(f1,f2) ->
    fprintf fmt "@[<hov 2>(%a@ or %a)@]" pr_formula f1 pr_formula f2
  | NL_Not f -> fprintf fmt "@[<hov 2>(not@ %a)@]" pr_formula f
  | NL_FTrue -> fprintf fmt "true"
  | NL_FFalse -> fprintf fmt "false"
  | NL_PApp(s,tl) ->
    fprintf fmt "@[<hov 2>%a%a@]" pr_symbol s pr_term_list tl

and pr_formula_list fmt l =
  match l with
  | NL_FOFNil -> fprintf fmt "[]"
  | NL_FOFCons(f,l) ->
    fprintf fmt "@[<hov 2>[ %a%a ]@]" pr_formula f pr_formula_list_tail l

and pr_formula_list_tail fmt l =
  match l with
  | NL_FOFNil -> ()
  | NL_FOFCons(f,l) ->
    fprintf fmt ";@ %a%a" pr_formula f pr_formula_list_tail l

let pr_formula_impl fmt f = pr_formula fmt f.nlrepr_fo_formula_field

let pr_formula_list_impl fmt l =
  pr_formula_list fmt l.nlrepr_fo_formula_list_field

let n = Why3extract.Why3__BigInt.of_int

let run_test name l =
  Format.printf "Running the test '%s'@." name;
  Format.printf "Formulas: %a@." pr_formula_list_impl l;
  let t = Unix.gettimeofday () in
  ProverMain__Impl.main l (n 1);
  let t = Unix.gettimeofday () -. t in
  Format.printf "Unsat (time = %.02f)@.@." t

let run_all_tests () =
  run_test "drinker" (ProverTest__Impl.drinker ());
  run_test "group" (ProverTest__Impl.group ());
  run_test "bidon1" (ProverTest__Impl.bidon1 ());
  run_test "bidon2" (ProverTest__Impl.bidon2 ());
  run_test "bidon3" (ProverTest__Impl.bidon3 ());
  run_test "bidon4" (ProverTest__Impl.bidon4 ());
  run_test "pierce" (ProverTest__Impl.pierce ());
  run_test "zenon5" (ProverTest__Impl.zenon5 ());
(* too long -> sat ?
  run_test "zenon6" (ProverTest__Impl.zenon6 ());
*)
  run_test "zenon10 2" (ProverTest__Impl.zenon10 (n 2));
(* too long -> sat !
  run_test "zenon10 3" (ProverTest__Impl.zenon10 (n 3))
*)
  run_test "zenon10 4" (ProverTest__Impl.zenon10 (n 4));
  run_test "zenon10 6" (ProverTest__Impl.zenon10 (n 6));
  run_test "zenon10 8" (ProverTest__Impl.zenon10 (n 8));
  run_test "zenon10 10" (ProverTest__Impl.zenon10 (n 10));
  run_test "zenon10 12" (ProverTest__Impl.zenon10 (n 12));
(* warning: the following needs around 6 minutes *)
(*
  run_test "zenon10 14" (ProverTest__Impl.zenon10 (n 14));
*)
  printf "End of tests.@."

let run_file file =
  try
    let _ast = Tptp_lexer.load file in
  (* check_file ast; *)
  (* printf "%a@." pr_file ast; *)
    printf "File '%s' is OK.@." file;
    exit 0
  with
  | Tptp_lexer.FileNotFound f ->
    eprintf "File not found: %s@." f; exit 2
(*
  | Unsupported s ->
      eprintf "File %s: '%s' is not supported@." file s; exit 1
*)
  | e ->
    eprintf "Parsing error: %a@." Why3.Exn_printer.exn_printer e;
    exit 2

let () =
  if Array.length Sys.argv = 1 then run_all_tests ()
  else
    if Array.length Sys.argv = 2 then run_file Sys.argv.(1)
    else
      begin
        eprintf "Usage: %s [file]@\nInternal tests are run if no file is given@." Sys.argv.(0);
        exit 2
      end
