(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

type 'a pp = formatter -> 'a -> unit

type printer = Env.env -> prelude -> prelude_map -> ?old:in_channel -> task pp

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
  let println fmt s = fprintf fmt "%s@\n" s in
  print_list nothing println fmt pl

let print_prelude_of_theories th_used fmt pm =
  List.iter (fun th ->
	       let prel = Mid.find_default th.th_name [] pm in
	       print_prelude fmt prel) th_used

let print_th_prelude task fmt pm =
  let th_used = task_fold (fun acc -> function
    | { td_node = Clone (th,sm) } when is_empty_sm sm -> th::acc
    | _ -> acc) [] task
  in
  print_prelude_of_theories th_used fmt pm

let print_prelude_for_theory th fmt pm =
  let th_used = List.fold_left (fun acc -> function
    | { td_node = Clone (th,sm) } when is_empty_sm sm -> th::acc
    | _ -> acc) [] th.th_decls
  in
  print_prelude_of_theories th_used fmt pm

exception KnownTypeSyntax of tysymbol
exception KnownLogicSyntax of lsymbol

let meta_syntax_type  = register_meta "syntax_type" [MTtysymbol; MTstring]
let meta_syntax_logic = register_meta "syntax_logic" [MTlsymbol; MTstring]
let meta_remove_prop  = register_meta "remove_prop" [MTprsymbol]

let syntax_type ts s =
  check_syntax s (List.length ts.ts_args);
  create_meta meta_syntax_type [MAts ts; MAstr s]

let syntax_logic ls s =
  check_syntax s (List.length ls.ls_args);
  create_meta meta_syntax_logic [MAls ls; MAstr s]

let remove_prop pr =
  create_meta meta_remove_prop [MApr pr]

let get_syntax_map, get_syntax_map_of_theory =
  let add_ts m = function
    | [MAts ts; MAstr s] ->
        Mid.add_new ts.ts_name s (KnownTypeSyntax ts) m
    | _ -> assert false
  in
  let add_ls m = function
    | [MAls ls; MAstr s] ->
        Mid.add_new ls.ls_name s (KnownLogicSyntax ls) m
    | _ -> assert false
  in
  (fun task ->
    let m = Mid.empty in
    let m = Task.on_meta meta_syntax_logic add_ls m task in
    let m = Task.on_meta meta_syntax_type add_ts m task in
    m),
  (fun theory ->
    let m = Mid.empty in
    let m = Theory.on_meta meta_syntax_logic add_ls m theory in
    let m = Theory.on_meta meta_syntax_type add_ts m theory in
    m)


let get_remove_set task =
  let add_ts s = function
    | [MAts ts; _] -> Sid.add ts.ts_name s
    | _ -> assert false
  in
  let add_ls s = function
    | [MAls ls; _] -> Sid.add ls.ls_name s
    | _ -> assert false
  in
  let add_pr s = function
    | [MApr pr] -> Sid.add pr.pr_name s
    | _ -> assert false
  in
  let s = Sid.empty in
  let s = Task.on_meta meta_syntax_type add_ts s task in
  let s = Task.on_meta meta_syntax_logic add_ls s task in
  let s = Task.on_meta meta_remove_prop add_pr s task in
  s

let query_syntax sm id = Mid.find_option id sm

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

