(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Pp

open Stdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Task

(** Register printers *)

type prelude = string list
type prelude_map = prelude Mid.t
type blacklist = string list

type 'a pp = Pp.formatter -> 'a -> unit

type printer_mapping = {
  lsymbol_m     : string -> Term.lsymbol;
  vc_line       : Loc.position option;
  queried_terms : Term.term list;
}

type printer_args = {
  env        : Env.env;
  prelude    : prelude;
  th_prelude : prelude_map;
  blacklist  : blacklist;
  mutable printer_mapping : printer_mapping;
}

type printer = printer_args -> ?old:in_channel -> task pp

type reg_printer = Pp.formatted * printer

let printers : reg_printer Hstr.t = Hstr.create 17

exception KnownPrinter of string
exception UnknownPrinter of string

let get_default_printer_mapping = {
  lsymbol_m = (function _ -> raise Not_found);
  vc_line = None;
  queried_terms = [];
}

let register_printer ~desc s p =
  if Hstr.mem printers s then raise (KnownPrinter s);
  Hstr.replace printers s (desc, p)

let lookup_printer s =
  try snd (Hstr.find printers s)
  with Not_found -> raise (UnknownPrinter s)

let list_printers () =
  Hstr.fold (fun k (desc,_) acc -> (k,desc)::acc) printers []

let () = register_printer
  ~desc:"Dummy@ printer@ with@ no@ output@ (used@ for@ debugging)." "(null)"
  (fun _ ?old:_ _ _ -> ())

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
let regexp_arg_pos_typed = Str.regexp "%\\([tv]?[0-9]+\\)"

exception BadSyntaxIndex of int
exception BadSyntaxArity of int * int

let check_syntax s len =
  let arg s =
    let i = int_of_string (Str.matched_group 1 s) in
    if i <= 0 then raise (BadSyntaxIndex i);
    if i > len then raise (BadSyntaxArity (len,i));
  in
  iter_group regexp_arg_pos arg s

let check_syntax_logic ls s =
  let len = List.length ls.ls_args in
  let ret = ls.ls_value <> None in
  let nfv = Stv.cardinal (ls_ty_freevars ls) in
  let arg s =
    let grp = (Str.matched_group 1 s) in
    if grp.[0] = 't' then begin
      let grp = String.sub grp 1 (String.length grp - 1) in
      let i = int_of_string grp in
      if i < 0 || (not ret && i = 0) then raise (BadSyntaxIndex i);
      if i > len then raise (BadSyntaxArity (len,i))
    end else if grp.[0] = 'v' then begin
      let grp = String.sub grp 1 (String.length grp - 1) in
      let i = int_of_string grp in
      if i < 0 || i >= nfv then raise (BadSyntaxIndex i)
    end else begin
      let i = int_of_string grp in
      if i <= 0 then raise (BadSyntaxIndex i);
      if i > len then raise (BadSyntaxArity (len,i));
    end
  in
  iter_group regexp_arg_pos_typed arg s

let syntax_arguments s print fmt l =
  let args = Array.of_list l in
  let repl_fun s fmt =
    let i = int_of_string (Str.matched_group 1 s) in
    print fmt args.(i-1) in
  global_substitute_fmt regexp_arg_pos repl_fun s fmt

(* return the type arguments of a symbol application, sorted according
   to their (formal) names *)
let get_type_arguments t = match t.t_node with
  | Tapp (ls, tl) ->
      let m = oty_match Mtv.empty ls.ls_value t.t_ty in
      let m = List.fold_left2
        (fun m ty t -> oty_match m (Some ty) t.t_ty) m ls.ls_args tl in
      let name tv = Stdlib.Mstr.add tv.tv_name.id_string in
      let m = Mtv.fold name m Stdlib.Mstr.empty in
      Array.of_list (Stdlib.Mstr.values m)
  | _ ->
      [||]

let gen_syntax_arguments_typed ty_of tys_of s print_arg print_type t fmt l =
  let args = Array.of_list l in
  let repl_fun s fmt =
    let grp = (Str.matched_group 1 s) in
    if grp.[0] = 't' then
      let grp = String.sub grp 1 (String.length grp - 1) in
      let i = int_of_string grp in
      if i = 0
      then print_type fmt (ty_of t)
      else print_type fmt (ty_of args.(i-1))
    else if grp.[0] = 'v' then
      let grp = String.sub grp 1 (String.length grp - 1) in
      let m = tys_of t in
      print_type fmt m.(int_of_string grp)
    else
      let i = int_of_string grp in
      print_arg fmt args.(i-1) in
  global_substitute_fmt regexp_arg_pos_typed repl_fun s fmt

let syntax_arguments_typed =
  gen_syntax_arguments_typed t_type get_type_arguments

(** {2 use printers} *)

let print_prelude fmt pl =
  let println fmt s = fprintf fmt "%s@\n" s in
  print_list nothing println fmt pl

let print_prelude_of_theories th_used fmt pm =
  let ht = Hid.create 5 in
  List.iter (fun { th_name = id } ->
    if not (Hid.mem ht id) then begin
      print_prelude fmt (Mid.find_def [] id pm);
      Hid.add ht id () end) th_used

let print_th_prelude task fmt pm =
  let th_used = task_fold (fun acc -> function
    | { td_node = Clone (th,_) } -> th::acc
    | _ -> acc) [] task
  in
  print_prelude_of_theories th_used fmt pm

(*
let print_prelude_for_theory th fmt pm =
  let rec get_th_used acc th = List.fold_left (fun acc -> function
    | { td_node = Use th } -> th :: get_th_used acc th
    | { td_node = Clone (th,_) } -> th::acc
    | _ -> acc) acc th.th_decls
  in
  let th_used = List.rev (get_th_used [] th) in
  print_prelude_of_theories th_used fmt pm
*)

exception KnownTypeSyntax of tysymbol
exception KnownLogicSyntax of lsymbol
exception KnownConverterSyntax of lsymbol

let meta_syntax_type = register_meta "syntax_type" [MTtysymbol; MTstring]
  ~desc:"Specify@ the@ syntax@ used@ to@ pretty-print@ a@ type@ symbol.@ \
         Can@ be@ specified@ in@ the@ driver@ with@ the@ 'syntax type'@ rule."

let meta_syntax_logic = register_meta "syntax_logic" [MTlsymbol; MTstring]
  ~desc:"Specify@ the@ syntax@ used@ to@ pretty-print@ a@ function/predicate@ \
         symbol.@ \
         Can@ be@ specified@ in@ the@ driver@ with@ the@ 'syntax function'@ \
         or@ 'syntax predicate'@ rules."

let meta_syntax_converter = register_meta "syntax_converter" [MTlsymbol; MTstring]
  ~desc:"Specify@ the@ syntax@ used@ to@ pretty-print@ a@ converter@ \ symbol.@ \
         Can@ be@ specified@ in@ the@ driver@ with@ the@ 'syntax converter'@ \
         rules."

let meta_remove_prop = register_meta "remove_prop" [MTprsymbol]
    ~desc:"Remove@ a@ logical@ proposition@ from@ proof@ obligations.@ \
           Can@ be@ specified@ in@ the@ driver@ with@ the@ 'remove prop'@ rule."

let meta_remove_type = register_meta "remove_type" [MTtysymbol]
  ~desc:"Remove@ a@ type@ symbol@ from@ proof@ obligations.@ \
         Used@ in@ bisection."

let meta_remove_logic = register_meta "remove_logic" [MTlsymbol]
  ~desc:"Remove@ a@ function/predicate@ symbol@ from@ proof@ obligations.@ \
         Used@ in@ bisection."

let meta_realized_theory = register_meta "realized_theory" [MTstring; MTstring]
  ~desc:"Specify@ that@ a@ Why3@ theory@ is@ realized@ as@ a@ module@ \
         in@ an@ ITP."

let check_syntax_type ts s = check_syntax s (List.length ts.ts_args)

let syntax_type ts s =
  check_syntax_type ts s;
  create_meta meta_syntax_type [MAts ts; MAstr s]

let syntax_logic ls s =
  check_syntax_logic ls s;
  create_meta meta_syntax_logic [MAls ls; MAstr s]

let syntax_converter ls s =
  check_syntax_logic ls s;
  create_meta meta_syntax_converter [MAls ls; MAstr s]

let remove_prop pr =
  create_meta meta_remove_prop [MApr pr]

type syntax_map = string Mid.t
type converter_map = string Mls.t

let sm_add_ts sm = function
  | [MAts ts; MAstr rs] -> Mid.add_new (KnownTypeSyntax ts) ts.ts_name rs sm
  | _ -> assert false

let sm_add_ls sm = function
  | [MAls ls; MAstr rs] -> Mid.add_new (KnownLogicSyntax ls) ls.ls_name rs sm
  | _ -> assert false

let sm_add_pr sm = function
  | [MApr pr] -> Mid.add pr.pr_name "" sm
  | _ -> assert false

let cm_add_ls cm = function
  | [MAls ls; MAstr rs] -> Mls.add_new (KnownConverterSyntax ls) ls rs cm
  | _ -> assert false

let get_syntax_map task =
  let sm = Mid.empty in
  let sm = Task.on_meta meta_syntax_type sm_add_ts sm task in
  let sm = Task.on_meta meta_syntax_logic sm_add_ls sm task in
  let sm = Task.on_meta meta_remove_prop sm_add_pr sm task in
  sm

let get_converter_map task =
  Task.on_meta meta_syntax_converter cm_add_ls Mls.empty task

let add_syntax_map td sm = match td.td_node with
  | Meta (m, args) when meta_equal m meta_syntax_type      -> sm_add_ts sm args
  | Meta (m, args) when meta_equal m meta_syntax_logic     -> sm_add_ls sm args
  | Meta (m, args) when meta_equal m meta_remove_prop      -> sm_add_pr sm args
  | _ -> sm

let add_converter_map td cm = match td.td_node with
  | Meta (m, args) when meta_equal m meta_syntax_converter -> cm_add_ls cm args
  | _ -> cm

let query_syntax sm id = Mid.find_opt id sm

let query_converter cm ls = Mls.find_opt ls cm

let on_syntax_map fn =
  Trans.on_meta meta_syntax_type (fun sts ->
  Trans.on_meta meta_syntax_logic (fun sls ->
  Trans.on_meta meta_remove_prop (fun spr ->
    let sm = Mid.empty in
    let sm = List.fold_left sm_add_ts sm sts in
    let sm = List.fold_left sm_add_ls sm sls in
    let sm = List.fold_left sm_add_pr sm spr in
    fn sm)))

let on_converter_map fn =
  Trans.on_meta meta_syntax_converter (fun scs ->
    fn (List.fold_left cm_add_ls Mls.empty scs))

let sprint_tdecl (fn : 'a -> Format.formatter -> tdecl -> 'a * string list) =
  let buf = Buffer.create 2048 in
  let fmt = Format.formatter_of_buffer buf in
  fun td (acc,strl) ->
    Buffer.reset buf;
    let acc, urg = fn acc fmt td in
    Format.pp_print_flush fmt ();
    acc, Buffer.contents buf :: List.rev_append urg strl

let sprint_decl (fn : 'a -> Format.formatter -> decl -> 'a * string list) =
  let buf = Buffer.create 2048 in
  let fmt = Format.formatter_of_buffer buf in
  fun td (acc,strl) -> match td.td_node with
    | Decl d ->
        Buffer.reset buf;
        let acc, urg = fn acc fmt d in
        Format.pp_print_flush fmt ();
        acc, Buffer.contents buf :: List.rev_append urg strl
    | _ -> acc, strl

(** {2 exceptions to use in transformations and printers} *)

exception UnsupportedType of ty   * string
exception UnsupportedTerm of term * string
exception UnsupportedPattern of pattern * string
exception UnsupportedDecl of decl * string
exception NotImplemented  of        string
exception Unsupported     of        string

(** {3 functions that catch inner error} *)

let unsupportedType e s = raise (UnsupportedType (e,s))
let unsupportedTerm e s = raise (UnsupportedTerm (e,s))
let unsupportedPattern p s = raise (UnsupportedPattern (p,s))
let unsupportedDecl e s = raise (UnsupportedDecl (e,s))
let notImplemented    s = raise (NotImplemented s)
let unsupported       s = raise (Unsupported s)

let catch_unsupportedType f e =
  try f e with Unsupported s -> unsupportedType e s

let catch_unsupportedTerm f e =
  try f e with Unsupported s -> unsupportedTerm e s

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
  | KnownConverterSyntax ls ->
      fprintf fmt "Converter syntax for logical symbol %a is already defined"
        Pretty.print_ls ls
  | BadSyntaxIndex i ->
      fprintf fmt "Bad argument index %d, must start with 1" i
  | BadSyntaxArity (i1,i2) ->
      fprintf fmt "Bad argument index %d, must end with %d" i2 i1
  | Unsupported s ->
      fprintf fmt "@[<hov 3> Uncatched exception 'Unsupported %s'@]" s
  | UnsupportedType (e,s) ->
      fprintf fmt "@[@[<hov 3> This type isn't supported:@\n%a@]@\n %s@]"
        Pretty.print_ty e s
  | UnsupportedTerm (e,s) ->
      fprintf fmt "@[@[<hov 3> This expression isn't supported:@\n%a@]@\n %s@]"
        Pretty.print_term e s
  | UnsupportedPattern (p,s) ->
      fprintf fmt "@[@[<hov 3> This pattern isn't supported:@\n%a@]@\n %s@]"
        Pretty.print_pat p s
  | UnsupportedDecl (d,s) ->
      fprintf fmt "@[@[<hov 3> This declaration isn't supported:@\n%a@]@\n %s@]"
        Pretty.print_decl d s
  | NotImplemented (s) ->
      fprintf fmt "@[<hov 3> Unimplemented feature:@\n%s@]" s
  | e -> raise e)
