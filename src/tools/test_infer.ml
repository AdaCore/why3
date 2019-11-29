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


exception File_too_small

exception Unwraaap
let unwrap = function
  | Some s -> s
  | None -> raise Unwraaap

let assert_ n b =
  if b then
    Format.printf "%s \027[32m passed\027[0m.@." n
  else
    Format.printf "%s \027[31m failed\027[0m.@." n


(* can't be used because why3 does not seem to keep a good character count (?) *)
let insert_at filename filename_2 offset to_add =
  let buf = Bytes.create offset in
  let fin = open_in filename in
  let fout = open_out filename_2 in
  begin
    try
      really_input fin buf 0 offset;
      output_bytes fout buf;
    with End_of_file ->
      raise File_too_small
  end;
  let buf_inserted = Bytes.of_string to_add in
  output_bytes fout buf_inserted;
  begin
    try
      while true do
        really_input fin buf 0 offset;
        output_bytes fout buf;
      done;
    with End_of_file ->
      close_in fin; close_out fout
  end

let insert_at_lines filename filename_2 offset to_add =
  let fin = open_in filename in
  let fout = open_out filename_2 in
  begin
    try
      for i = 0 to offset-1 do
        input_line fin
        |> Format.sprintf "%s\n"
        |> output_string fout;
      done;
    with End_of_file ->
      raise File_too_small
  end;
  output_string fout to_add;
  begin
    try
      while true do
        input_line fin
        |> Format.sprintf "%s\n"
        |> output_string fout;
      done;
    with End_of_file ->
      close_in fin; close_out fout
  end

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

let do_input way f =
  let format = !opt_parser in
  let mm = match f with
    | "-" ->
        Env.read_channel Pmodule.mlw_language ?format env "stdin" stdin
    | file ->
        fst (Env.read_file Pmodule.mlw_language ?format env file)
  in
  let open Pdecl in
  let open Expr in
  let do_infer mid m =
    let open Pmodule in
    Mstr.iter (fun k ps -> match ps with
        | PV a -> (* this is a val - nothing to do *) ()
        | RS(rsym) ->
          let function_name = Ident.(rsym.rs_name.id_string) in
          let decl = Ident.Mid.find Expr.(rsym.rs_name) m.mod_known in
          begin match decl.pd_node with
          | PDlet(let_expr) ->
            begin match let_expr with
              | LDvar(_) -> Format.eprintf "ldvar not handled@."
              | LDsym(rsym_, cexp) ->
                if Some (f ^ ":" ^ function_name) = !opt_file || Some f = !opt_file || !opt_file = None then
                begin
                  match cexp.c_node with
                  | Cfun e ->
                    let open Expr in
                    let preconditions = Ity.(Expr.(cexp.c_cty.cty_pre)) in
                    let module Abstract_interpreter =
                      Ai_cfg.Make(struct
                        let env = env
                        let pmod = m
                        let widening = 4
                        module D = Disjunctive_domain_fast.Make(Domain.Polyhedra)
                      end) in
                    let cfg = Abstract_interpreter.start_cfg rsym in
                    let context = Abstract_interpreter.empty_context () in
                    let rec while_invariants context e =
                      let r = while_invariants context in
                      match e.e_node with
                      | Elet(LDvar(pv, e), e2) ->
                        r e @ r e2
                      | Evar(_) | Econst(_) | Eassign(_)
                      | Eabsurd | Epure (_) | Eassert(_) | Eexec(_) | Elet(_)
                        -> []
                      | Eif(e1, e2, e3) ->
                        r e1 @ r e2 @ r e3
                      | Ematch (e, pats, exns) ->
                        r e @
                        Ity.Mxs.fold_left (fun l _ (pvs, e) ->
                            r e @ l) (r e) exns
                      | Eraise(x, e_) ->
                        r e_
                      | Eghost(e) ->
                        r e
                      | Ewhile(e_cond, invs, _, e_loop) ->
                        begin
                          match invs with
                          | inv::_ ->
                            let man = Abstract_interpreter.domain_manager context in
                            Abstract_interpreter.Domain.meet_term man inv
                          | _ -> assert false
                        end ::
                        r e_cond @
                        r e_loop
                      | Efor(pv, (f, d, to_), inv, _, e_loop) ->
                        r e_loop;
                      | _ -> assert false
                    in
                    List.iter (Abstract_interpreter.add_variable cfg context)
                      Ity.(cexp.c_cty.cty_args);
                    ignore (Abstract_interpreter.put_expr_with_pre cfg context e preconditions);
                    let whole_e = e in
                    let invs = while_invariants context e in
                    (* will hold the diffrent file offsets (useful when writing multiple invariants) *)
                    let fixp = Abstract_interpreter.eval_fixpoints cfg context
                               |> List.combine invs
                    in
                    List.iter (fun (meet_term, (e, d)) ->
                        match e.e_node with
                        | Ewhile(_, inv::_, _, _) ->
                          let man = Abstract_interpreter.domain_manager context in
                          let expected_d = Abstract_interpreter.Domain.top man () |> meet_term in
                          let b = Abstract_interpreter.Domain.is_leq man d expected_d in
                          assert_ (f ^ ":" ^ function_name) (b <> way);
                          if b = way then
                            begin
                              let s =
                                Abstract_interpreter.domain_to_term cfg context d
                                |> Pretty.print_term Format.str_formatter
                                |> Format.flush_str_formatter
                                |> Format.sprintf "invariant computed { %s }\n"
                              in
                              Expr.print_expr Format.std_formatter whole_e;
                              Format.printf "@.For expression: @.";
                              Expr.print_expr Format.std_formatter e;
                              Format.printf "@.";
                              Format.printf "%s@." s;
                              Format.printf "vs.@.";
                              let s =
                                Abstract_interpreter.domain_to_term cfg context expected_d
                                |> Pretty.print_term Format.str_formatter
                                |> Format.flush_str_formatter
                                |> Format.sprintf "invariant { %s }\n"
                              in
                              Format.printf "%s@." s;
                              Abstract_interpreter.Domain.print Format.std_formatter d;
                              Format.printf "@.";
                              Abstract_interpreter.Domain.print Format.std_formatter expected_d;
                              Format.printf "@.";
                            end
                        | _ -> assert false
                      ) fixp
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
                end;
              | LDrec(_) -> Format.eprintf "LDrec not handled@."
            end
          | _ -> () end
        | _ -> assert false
      ) m.mod_export.ns_ps
  in
  Mstr.iter do_infer mm;
  ()

let () =
  try
    List.iter (do_input false)
      [
        "tests_ai/auto_cst1.mlw";
        "tests_ai/auto_list1.mlw";
        "tests_ai/auto_ref0.mlw";
        "tests_ai/auto_ref1.mlw";
        "tests_ai/auto_ref2.mlw";
        "tests_ai/auto_ref3.mlw";
        "tests_ai/uf1.mlw";
        "tests_ai/mccarthy.mlw";
        "tests_ai/auto_array1.mlw";
        "tests_ai/bool.mlw"
      ];
    List.iter (do_input true)
      [
        "tests_ai/auto_list1false.mlw";
        "tests_ai/auto_array_false.mlw";
        "tests_ai/auto_ref_false.mlw";
      ];
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1
