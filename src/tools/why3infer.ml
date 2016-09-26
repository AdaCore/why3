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
        Env.read_file Pmodule.mlw_language ?format env file
  in
  let do_infer mid m =
    let open Pmodule in
    Mstr.iter (fun k ps -> match ps with
        | PV a ->
          failwith "PV not handled"
        | RS(rsym) ->
          let decl = Ident.Mid.find Expr.(rsym.rs_name) m.mod_known in
          let open Pdecl in
          let open Expr in
          match decl.pd_node with
          | PDlet(let_expr) ->
            (*
            Format.printf "rs:@.";
            Expr.print_rs Format.std_formatter a;
            Format.printf "@.";
            *)
            begin match let_expr with
              | LDvar(_) -> Format.eprintf "ldvar not handled@."
              | LDsym(rsym_, cexp) ->
                assert (rs_equal rsym_ rsym);
                begin
                  match cexp.c_node with
                  | Cfun e ->
                    Expr.print_expr Format.err_formatter e; Format.eprintf "@.";
                    begin
                      match e.e_node with
                      | Eexec(_) -> Format.eprintf "exec@.";
                        Expr.print_expr Format.err_formatter e; Format.eprintf "@."
                      | _ -> Format.eprintf "else@."
                    end
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

      ) m.mod_export.ns_ps
  in
  Mstr.iter do_infer mm

let () =
  try
    Opt.iter do_input !opt_file
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. byte"
End:
*)
