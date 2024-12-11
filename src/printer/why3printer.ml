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

(** Why3 printer *)

open Format
open Ident
open Printer

let iprinter,aprinter,tprinter,pprinter =
  let bl = Keywords.keywords in
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:isanitize

module P = (val (Pretty.create ~do_forget_all:false iprinter aprinter tprinter pprinter))

let print_attr = Debug.lookup_flag "print_attributes"

let print_tdecls =
  let print_tdecl sm fmt td =
    Format.fprintf fmt "%a" P.print_tdecl td;
    sm, [] in
  let print_tdecl = Printer.sprint_tdecl print_tdecl in
  let print_tdecl task acc = print_tdecl task.Task.task_decl acc in
  Discriminate.on_syntax_map (fun sm -> Trans.fold print_tdecl (sm,[]))

let print_task args ?old:_ fmt task =
  (* In trans-based p-printing [forget_all] IST STRENG VERBOTEN *)
  (* forget_all (); *)
  print_prelude fmt args.prelude;
  fprintf fmt "@[<v 0>theory Task@\n";
  print_th_prelude task fmt args.th_prelude;
  let rec print = function
    | x :: r -> print r; Pp.string fmt x
    | [] -> () in
  let fl = Debug.test_flag print_attr in
  Debug.set_flag print_attr;
  print (snd (Trans.apply print_tdecls task));
  if not fl then Debug.unset_flag print_attr;
  fprintf fmt "@\nend@]@."

let () = register_printer "why3" print_task
  ~desc:"Printer@ for@ the@ logical@ format@ of@ Why3.@ Used@ for@ debugging."
