(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Theory
open Task

(** Register printers *)

type prelude = string list
type prelude_map = prelude Mid.t
type syntax_map = string Mid.t

type 'a pp = formatter -> 'a -> unit

type printer = prelude -> prelude_map -> syntax_map -> task pp

let printers : (string, printer) Hashtbl.t = Hashtbl.create 17

exception KnownPrinter of string
exception UnknownPrinter of string

let register_printer s p =
  if Hashtbl.mem printers s then raise (KnownPrinter s);
  Hashtbl.replace printers s p

let lookup_printer s =
  try Hashtbl.find printers s
  with Not_found -> raise (UnknownPrinter s)

let list_printers ()  = Hashtbl.fold (fun k _ acc -> k::acc) printers []

(** Syntax substitutions *)

let opt_search_forward re s pos =
  try Some (Str.search_forward re s pos) with Not_found -> None

let global_substitute_fmt expr repl_fun text fmt =
  let rec replace start last_was_empty =
    let startpos = if last_was_empty then start + 1 else start in
    if startpos > String.length text then
      pp_print_string fmt (Str.string_after text start)
    else
      match opt_search_forward expr text startpos with
      | None ->
          pp_print_string fmt (Str.string_after text start)
      | Some pos ->
          let end_pos = Str.match_end () in
          pp_print_string fmt (String.sub text start (pos - start));
          repl_fun text fmt;
          replace end_pos (end_pos = pos)
  in
  replace 0 false

let iter_group expr iter_fun text =
  let rec iter start last_was_empty =
    let startpos = if last_was_empty then start + 1 else start in
    if startpos < String.length text then
      match opt_search_forward expr text startpos with
      | None -> ()
      | Some pos ->
          let end_pos = Str.match_end () in
          iter_fun text;
          iter end_pos (end_pos = pos)
  in
  iter 0 false

let regexp_arg_pos = Str.regexp "%\\([0-9]+\\)"

exception BadSyntaxIndex of int
exception BadSyntaxArity of int * int

let check_syntax s len =
  let arg s =
    let i = int_of_string (Str.matched_group 1 s) in
    if i <= 0 then raise (BadSyntaxIndex i);
    if i > len then raise (BadSyntaxArity (len,i));
  in
  iter_group regexp_arg_pos arg s

let syntax_arguments s print fmt l =
  let args = Array.of_list l in
  let repl_fun s fmt =
    let i = int_of_string (Str.matched_group 1 s) in
    print fmt args.(i-1) in
  global_substitute_fmt regexp_arg_pos repl_fun s fmt

(** {2 use printers} *)

let print_prelude fmt pl =
  fprintf fmt "%a@\n" (print_list newline pp_print_string) pl

let print_th_prelude task fmt pm =
  let th_used = task_fold (fun acc -> function
    | { td_node = Clone (th,tm,lm,pm) }
      when Mts.is_empty tm && Mls.is_empty lm && Mpr.is_empty pm -> th::acc
    | _ -> acc) [] task
  in
  List.iter (fun th ->
    let prel = try Mid.find th.th_name pm with Not_found -> [] in
    print_prelude fmt prel) th_used

exception KnownTypeSyntax of tysymbol
exception KnownLogicSyntax of lsymbol

let add_ts_syntax ts s sm =
  check_syntax s (List.length ts.ts_args);
  if Mid.mem ts.ts_name sm then raise (KnownTypeSyntax ts);
  Mid.add ts.ts_name s sm

let add_ls_syntax ls s sm =
  check_syntax s (List.length ls.ls_args);
  if Mid.mem ls.ls_name sm then raise (KnownLogicSyntax ls);
  Mid.add ls.ls_name s sm

let query_syntax sm id =
  try Some (Mid.find id sm) with Not_found -> None

let meta_remove_type  = register_meta "remove_type" [MTtysymbol]
let meta_remove_logic = register_meta "remove_logic" [MTlsymbol]
let meta_remove_prop  = register_meta "remove_prop" [MTprsymbol]

let remove_type  ts = create_meta meta_remove_type  [MAts ts]
let remove_logic ls = create_meta meta_remove_logic [MAls ls]
let remove_prop  pr = create_meta meta_remove_prop  [MApr pr]

let get_remove_set task =
  let add_ts td s = match td.td_node with
    | Meta (_,[MAts ts]) -> Sid.add ts.ts_name s
    | _ -> assert false
  in
  let add_ls td s = match td.td_node with
    | Meta (_,[MAls ls]) -> Sid.add ls.ls_name s
    | _ -> assert false
  in
  let add_pr td s = match td.td_node with
    | Meta (_,[MApr pr]) -> Sid.add pr.pr_name s
    | _ -> assert false
  in
  let s = Sid.empty in
  let s = Stdecl.fold add_ts (find_meta task meta_remove_type).tds_set s in
  let s = Stdecl.fold add_ls (find_meta task meta_remove_logic).tds_set s in
  let s = Stdecl.fold add_pr (find_meta task meta_remove_prop).tds_set s in
  s

(** {2 exceptions to use in transformations and printers} *)

exception UnsupportedType of ty   * string
exception UnsupportedExpr of expr * string
exception UnsupportedDecl of decl * string
exception NotImplemented  of        string
exception Unsupported     of        string

(** {3 functions that catch inner error} *)

let unsupportedType e s = raise (UnsupportedType (e,s))
let unsupportedTerm e s = raise (UnsupportedExpr (Term e,s))
let unsupportedFmla e s = raise (UnsupportedExpr (Fmla e,s))
let unsupportedExpr e s = raise (UnsupportedExpr (e,s))
let unsupportedDecl e s = raise (UnsupportedDecl (e,s))
let notImplemented    s = raise (NotImplemented s)
let unsupported       s = raise (Unsupported s)

let catch_unsupportedType f e =
  try f e with Unsupported s -> unsupportedType e s

let catch_unsupportedTerm f e =
  try f e with Unsupported s -> unsupportedTerm e s

let catch_unsupportedFmla f e =
  try f e with Unsupported s -> unsupportedFmla e s

let catch_unsupportedExpr f e =
  try f e with Unsupported s -> unsupportedExpr e s

let catch_unsupportedDecl f e =
  try f e with Unsupported s -> unsupportedDecl e s

let () = Exn_printer.register (fun fmt exn -> match exn with
  | KnownPrinter s ->
      fprintf fmt "Printer '%s' is already registered" s
  | UnknownPrinter s ->
      fprintf fmt "Unknown printer '%s'" s
  | KnownTypeSyntax ts ->
      fprintf fmt "Syntax for type symbol %a is already defined"
        Pretty.print_ts ts
  | KnownLogicSyntax ls ->
      fprintf fmt "Syntax for logical symbol %a is already defined"
        Pretty.print_ls ls
  | BadSyntaxIndex i ->
      fprintf fmt "Bad argument index %d, must start with 1" i
  | BadSyntaxArity (i1,i2) ->
      fprintf fmt "Bad argument index %d, must end with %d" i2 i1
  | Unsupported s ->
      fprintf fmt "@[<hov 3> Uncatched exception 'Unsupported %s'@]" s
  | UnsupportedType (e,s) ->
      fprintf fmt "@[<hov 3> This type isn't supported:@\n%a@\n%s@]"
        Pretty.print_ty e s
  | UnsupportedExpr (e,s) ->
      fprintf fmt "@[<hov 3> This expression isn't supported:@\n%a@\n%s@]"
        Pretty.print_expr e s
  | UnsupportedDecl (d,s) ->
      fprintf fmt "@[<hov 3> This declaration isn't supported:@\n%a@\n%s@]"
        Pretty.print_decl d s
  | NotImplemented (s) ->
      fprintf fmt "@[<hov 3> Unimplemented feature:@\n%s@]" s
  | e -> raise e)

