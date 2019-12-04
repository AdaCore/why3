(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Why3
open Stdlib
open Wstdlib

exception Unwraaap
let unwrap = function
  | Some s -> s
  | None -> raise Unwraaap

let usage_msg = sprintf
  "Usage: %s [options] file"
  (Filename.basename Sys.argv.(0))

let opt_file = ref None

let add_opt x =
  if !opt_file = None then opt_file := Some x
  else
    begin
      Format.eprintf "Only one file at a time.@.";
      exit 1
    end

let opt_parser = ref None

let option_list = [
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F" ]

let config, _, env =
  Whyconf.Args.initialize option_list add_opt usage_msg

let () =
  if !opt_file = None then Whyconf.Args.exit_with_usage option_list usage_msg

let do_input f =
  let format = !opt_parser in
  let mm = match f with
    | "-" ->
        Env.read_channel Pmodule.mlw_language ?format env "stdin" stdin
    | file ->
        fst (Env.read_file Pmodule.mlw_language ?format env file)
  in
  let all_while = ref [] in
  let open Pdecl in
  let open Expr in
  let do_infer mid m =
    let open Pmodule in
    Mstr.iter (fun k ps -> match ps with
        | PV a -> (* this is a val - nothing to do *) ()
        | RS(rsym) -> begin
          let decl = Ident.Mid.find Expr.(rsym.rs_name) m.mod_known in
          match decl.pd_node with
          | PDlet(let_expr) ->
            begin match let_expr with
              | LDvar(_) -> Format.eprintf "ldvar not handled@."
              | LDsym(rsym_, cexp) ->
                assert (rs_equal rsym_ rsym);
                begin
                  match cexp.c_node with
                  | Cfun e ->
                    let preconditions = Ity.(Expr.(cexp.c_cty.cty_pre)) in
                    Format.eprintf "@.";
                    let module Abstract_interpreter =
                      Ai_cfg.Make(struct
                        let env = env
                        let pmod = m
                        let widening = 3
                        module D = Disjunctive_domain_fast.Make(Domain.Polyhedra)
                      end) in
                    let cfg = Abstract_interpreter.start_cfg rsym in
                    let context = Abstract_interpreter.empty_context () in
                    List.iter (Abstract_interpreter.add_variable cfg context)
                      Ity.(cexp.c_cty.cty_args);
                    Expr.print_expr Format.err_formatter e;
                    Format.eprintf "@.";
                    ignore (Abstract_interpreter.put_expr_with_pre cfg context e preconditions);
                    (* will hold the diffrent file offsets (useful when writing multiple invariants) *)
                    let fixp = Abstract_interpreter.eval_fixpoints cfg context
                    |> List.map (fun (expr, domain) ->
                                  let inv =
                                    Abstract_interpreter.domain_to_term cfg context domain
                                    |> Pretty.print_term Format.str_formatter
                                    |> Format.flush_str_formatter
                                    |> Format.sprintf "invariant { %s }\n"
                                  in
                                  expr, inv)
                    in
                    all_while := fixp :: !all_while;
                  | Cany ->
                    Format.eprintf "rs:";
                    Expr.print_rs Format.err_formatter rsym;
                    Format.eprintf " -> not a fun: any@."
                  | Cpur(_) ->
                    Format.eprintf "rs:";
                    Expr.print_rs Format.err_formatter rsym;
                    Format.eprintf " -> not a fun: pur@."
                  | Capp(_) ->
                    Format.eprintf "rs:";
                    Expr.print_rs Format.err_formatter rsym;
                    Format.eprintf " -> not a fun: app@."
                end
              | LDrec(_) -> Format.eprintf "LDrec not handled@."
            end
          | _ -> ()
          end
        | _ -> assert false
      ) m.mod_export.ns_ps
  in
  (*let open Pmodule in
  let module Infer_ai =
    Infer_ai.Make(struct
      let env = env
      let pmod = Mstr.choose mm |> snd
      let widening = 6
      module D = Disjunctive_domain.Make(Domain.Polyhedra)
    end) in
  ignore (Infer_ai.infer_loop_invariants (Mstr.choose mm |> snd));*)
  Mstr.iter do_infer mm;
  let copying_informations = Hashtbl.create 100 in
  !all_while
  |> List.concat
  |> List.sort (fun (e1, _) (e2, _) ->
                        let e1 = match e1.e_node with
                          | Ewhile(_, _, _, e1) | Efor(_, _, _, _, e1)
                            -> e1
                          | _ -> assert false
                        in
                        let e2 = match e2.e_node with
                          | Ewhile(_, _, _, e1) | Efor(_, _, _, _, e1)
                            -> e1
                          | _ -> assert false
                        in
                        compare e1.e_loc e2.e_loc
                      )
  |> List.iter begin fun (expr, inv) ->
    match expr.e_node with
    | Ewhile(_, _, _, expr) | Efor(_, _, _, _, expr) ->
      Pretty.forget_all ();
      ignore @@ Format.flush_str_formatter ();
      let file, line_number, _, _ = Expr.(expr.e_loc) |> unwrap |> Loc.get in
      let line_number = line_number - 1 in (* we want to insert the invariant
                                              before the loop *)
      let new_file = Format.sprintf "%s_inferred.mlw" file in
      let o, fin, fout =
        try
          Hashtbl.find copying_informations file
        with
        | Not_found ->
          let v = 0, open_in file, open_out new_file in
          Hashtbl.add copying_informations file v; v
      in
      let number_of_lines_to_read = line_number - (o + 1) in (* the file was copied up to o *)
      assert (number_of_lines_to_read >= -1);
      for i = 0 to number_of_lines_to_read do
        input_line fin |> Format.sprintf "%s\n" |> output_string fout;
      done;
      output_string fout inv;
      Hashtbl.replace copying_informations file (line_number, fin, fout);
    | _ -> assert false
  end;
  Hashtbl.iter (fun _ (o, fin, fout) ->
      try
        while true do
          input_line fin |> Format.sprintf "%s\n" |> output_string fout;
        done;
      with
      | End_of_file -> ()) copying_informations

let () =
  try
    Opt.iter do_input !opt_file
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1
