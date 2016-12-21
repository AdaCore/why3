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

(** Printer for extracted OCaml code *)

open Compile
open Format
open Pmodule
open Theory
open Ident
open Printer
open Pp

module Print = struct

  open ML

  let ocaml_keywords =
    ["and"; "as"; "assert"; "asr"; "begin";
     "class"; "constraint"; "do"; "done"; "downto"; "else"; "end";
     "exception"; "external"; "false"; "for"; "fun"; "function";
     "functor"; "if"; "in"; "include"; "inherit"; "initializer";
     "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match";
     "method"; "mod"; "module"; "mutable"; "new"; "object"; "of";
     "open"; "or"; "private"; "rec"; "sig"; "struct"; "then"; "to";
     "true"; "try"; "type"; "val"; "virtual"; "when"; "while"; "with";
     "raise";]

  let iprinter =
    let isanitize = sanitizer char_to_alpha char_to_alnumus in
    create_ident_printer ocaml_keywords ~sanitizer:isanitize

  let print_ident fmt id =
    let s = id_unique iprinter id in
    fprintf fmt "%s" s

  let print_path =
    print_list dot pp_print_string (* point-free *)

  let print_path_id fmt = function
    | [], id -> print_ident fmt id
    | p, id  -> fprintf fmt "%a.%a" print_path p print_ident id

  let print_theory_name fmt th =
    print_path_id fmt (th.th_path, th.th_name)

  let print_module_name fmt m =
    print_theory_name fmt m.mod_theory

  let rec print_enode fmt = function
    | Eident id ->
       print_ident fmt id
    | _ -> assert false (* TODO *)

  let print_expr fmt e =
    print_enode fmt e.e_node

  let print_decl fmt = function
    | Dlet (isrec, [id, _, e]) ->
       fprintf fmt "@[<hov 2>%s %a =@ %a@]"
               (if isrec then "let rec" else "let")
               print_ident id
               print_expr e;
       fprintf fmt "@\n@\n"
    | _ -> assert false (* TODO *)

end

let extract_module fmt m =
  fprintf fmt
    "(* This file has been generated from Why3 module %a *)@\n@\n"
    Print.print_module_name m;
  let mdecls = Translate.module_ m in
  print_list nothing Print.print_decl fmt mdecls;
  fprintf fmt "@."
