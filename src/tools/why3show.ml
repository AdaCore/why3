(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

let sort_pair (x,_) (y,_) = String.compare x y

type cmd = {
    cmd_desc : string;
    cmd_usage : string;
    cmd_name : string;
    cmd_run : unit -> unit;
  }

module ListAttrs = struct

  let run () =
    Format.printf "@[<v>%a@]@."
      (Pp.print_list Pp.newline Pp.string)
      (List.sort String.compare (Ident.list_attributes ()))

  let cmd = {
      cmd_desc = "list WhyML attributes";
      cmd_usage = "\nList the WhyML attributes known by Why3.";
      cmd_name = "attributes";
      cmd_run = run;
    }

end

module ListFormats = struct

  let run () =
    let print1 fmt s = Format.fprintf fmt "%S" s in
    let print fmt (p, l, f) =
      Format.fprintf fmt "@[%s [%a]@\n  @[%a@]@]"
        p (Pp.print_list Pp.comma print1) l
        Pp.formatted f
    in
    Format.printf "@[<v>%a@]@."
      (Pp.print_list Pp.newline2 print)
      (List.sort (fun (u,_,_) (v,_,_) -> String.compare u v)
         (Env.list_formats Env.base_language))

  let cmd = {
      cmd_desc = "list input formats";
      cmd_usage = "\nList the input formats known by Why3.";
      cmd_name = "formats";
      cmd_run = run;
    }

end

module ListMetas = struct

  let run () =
    let open Theory in
    let print fmt m =
      Format.fprintf fmt "@[<v 2>@[<4>%s %s%a@]@,@[<hov>%a@]@]"
        (let s = m.meta_name in
         if String.contains s ' ' then "\"" ^ s ^ "\"" else s)
        (if m.meta_excl then "(flag) " else "")
        (Pp.print_list Pp.space Pretty.print_meta_arg_type) m.meta_type
        Pp.formatted m.meta_desc in
    let cmp m1 m2 = String.compare m1.meta_name m2.meta_name in
    Format.printf "@[<v>%a@]@."
      (Pp.print_list Pp.newline2 print) (List.sort cmp (list_metas ()))

  let cmd = {
      cmd_desc = "list meta directives";
      cmd_usage = "\nList the meta directives known by Why3.";
      cmd_name = "metas";
      cmd_run = run;
    }

end

module ListPrinters = struct

  let run () =
    let print_printer_desc fmt (s,f) =
      Format.fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" s Pp.formatted f in
    Format.printf "@[<v>%a@]@."
      (Pp.print_list Pp.newline2 print_printer_desc)
      (List.sort sort_pair (Printer.list_printers ()))

  let cmd = {
      cmd_desc = "list printers";
      cmd_usage = "\nList the printers known by Why3.";
      cmd_name = "printers";
      cmd_run = run;
    }

end

module ListTransforms = struct

  let run () =
    Format.printf "%a@." Server_utils.print_list_transforms ()

  let cmd = {
      cmd_desc = "list transformations";
      cmd_usage = "\nList the transformations known by Why3.";
      cmd_name = "transformations";
      cmd_run = run;
    }

end

let cmds = [
    ListAttrs.cmd;
    ListFormats.cmd;
    ListMetas.cmd;
    ListPrinters.cmd;
    ListTransforms.cmd;
  ]

let print_commands fmt =
  let maxl = List.fold_left
    (fun acc e -> max acc (String.length e.cmd_name)) 0 cmds in
  Format.fprintf fmt "Available commands:@\n%a"
    (Pp.print_list_suf Pp.newline
       (fun fmt e -> Format.fprintf fmt "  %s   @[<hov>%s@]"
         (Strings.pad_right ' ' e.cmd_name maxl) e.cmd_desc)) cmds

module Main : functor () -> sig end
 = functor () -> struct

let anon_file x = raise (Getopt.GetoptFailure (Printf.sprintf "unexpected argument: %s" x))

let usage_msg = "<command>\nExecute the given subcommand.\n"
let extra_help = Format.asprintf "%t" print_commands

let () =
  let options = Whyconf.Args.all_options [] usage_msg extra_help in
  let i = Getopt.parse_many options Sys.argv !Whyconf.Args.first_arg in
  if i = Array.length Sys.argv then
    Whyconf.Args.exit_with_usage ~extra_help usage_msg;
  let cmd_name = Sys.argv.(i) in
  let cmd =
    match List.find (fun e -> e.cmd_name = cmd_name) cmds with
    | cmd -> cmd
    | exception Not_found ->
        Format.eprintf "'%s' is not a why3show command.@\n@\n%t"
          cmd_name print_commands;
        exit 1 in
  Whyconf.Args.add_command cmd_name;
  let options = Whyconf.Args.all_options [] cmd.cmd_usage "" in
  Getopt.parse_all ~i:(i + 1) options anon_file Sys.argv;
  let _, _ = Whyconf.Args.complete_initialization () in
  try
    cmd.cmd_run ()
  with e when not (Debug.test_flag Debug.stack_trace) ->
    Format.eprintf "@.%a@." Exn_printer.exn_printer e;
    exit 1

end

let () = Whyconf.register_command "show" (module Main)
