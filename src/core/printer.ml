(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Pp

open Wstdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Task

(** Comments *)
let comment_regex = Str.regexp "comment:\\(.*\\)"
let line_delim = Str.regexp "[\n\r]+"

let check_comment attr acc =
  if Str.string_match comment_regex attr.attr_string 0 then
    let comment = String.sub attr.attr_string 8
                             ((String.length attr.attr_string) - 8) in
    comment :: acc
  else
    acc

let split_lines = Str.split line_delim

let print_comment fmt start_tok ?end_tok:(end_tok="") comment =
  let com_lines = split_lines comment in
  let block_width =
    if end_tok <> "" then
      List.fold_left (fun max s ->
                      let len = String.length s in
                      if max < len then len else max) 0 com_lines
    else 0 in
  fprintf fmt "@[";
  let print_comment_line =
    (fun s ->
     fprintf fmt "%s %s" start_tok s;
     let spaces = if block_width <> 0 then
                    String.make (block_width - String.length s + 1) ' '
                  else "" in
     fprintf fmt "%s%s@\n" spaces end_tok) in
  List.iter print_comment_line com_lines;
  fprintf fmt "@]"

let print_comments fmt start_tok ?end_tok:(end_tok="") term =
  let comments = Sattr.fold check_comment term.t_attrs [] in
  List.iter (print_comment fmt start_tok ~end_tok) comments


(** Register printers *)

type prelude = string list
type prelude_map = prelude Mid.t
type interface = string list
type interface_map = interface Mid.t
type blacklist = string list

type 'a pp = Pp.formatter -> 'a -> unit

type printer_mapping = {
  lsymbol_m     : string -> Term.lsymbol;
  vc_term_loc   : Loc.position option;
  queried_terms : Term.term Mstr.t;
  list_projections: Ident.ident Mstr.t;
  list_fields: Ident.ident Mstr.t;
  list_records: ((string * string) list) Mstr.t;
  noarg_constructors: string list;
  set_str: Sattr.t Mstr.t
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
  vc_term_loc = None;
  queried_terms = Mstr.empty;
  list_projections = Mstr.empty;
  list_fields = Mstr.empty;
  list_records = Mstr.empty;
  noarg_constructors = [];
  set_str = Mstr.empty
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

(*
let opt_search_forward re s pos =
  try Some (Str.search_forward re s pos) with Not_found -> None
*)

(* specialized version of opt_search_forward, searching for strings
   matching '%' [tv]? [0-9]+ [search_forward s pos] search from
   starting position [pos], in the string [s], and returns either None
   if no substrings match, or [Some(b,e)] if the substring between
   positions [b] included and [e] excluded matches (without the leading '%').
*)

let is_digit ch = match ch with '0'..'9' -> true | _ -> false

let opt_search_forward s pos =
  let l = String.length s in
  let b = ref pos in
  let i = ref pos in
  try
    while !i < l-1 do
      if s.[!i] = '%' then begin
        incr i;
        b := !i;
        begin match s.[!i] with
        | 't' | 'v' -> incr i
        | _ -> ()
        end;
        let e = !i in
        while !i < l && is_digit s.[!i] do incr i done;
        if !i > e then raise Exit
      end;
      incr i
    done;
    None
  with Exit -> Some(!b,!i)

let opt_search_forward_literal_format s pos =
  let l = String.length s in
  let b = ref pos in
  let i = ref pos in
  try
    while !i < l-1 do
      if s.[!i] = '%' then begin
        incr i;
        b := !i;
        begin match s.[!i] with
        | 's' | 'e' | 'm' -> incr i; (* float literals *)
        | _ -> ()
        end;
        while !i < l && is_digit s.[!i] do incr i done;
        begin match s.[!i] with
        | 'b' | 'x' | 'o' | 'd' -> incr i; raise Exit
        | _ -> ()
        end;
      end;
      incr i
    done;
    None
  with Exit -> Some(!b,!i)

let global_substitute_fmt search_fun repl_fun text fmt =
  let len = String.length text in
  let rec replace start =
    match search_fun text start with
    | None ->
      pp_print_string fmt (String.sub text start (len - start))
    | Some(pos,end_pos) ->
      pp_print_string fmt (String.sub text start (pos - start - 1));
      repl_fun text pos end_pos fmt;
      replace end_pos
  in
  replace 0

let iter_group search_fun iter_fun text =
  let rec iter start last_was_empty =
    let startpos = if last_was_empty then start + 1 else start in
    if startpos < String.length text then
      match search_fun text startpos with
      | None -> ()
      | Some (pos,end_pos) ->
          iter_fun text pos end_pos;
          iter end_pos (end_pos = pos)
  in
  iter 0 false

exception BadSyntaxIndex of int
exception BadSyntaxArity of int * int

let int_of_string s =
  try int_of_string s
  with _ ->
    Format.eprintf "bad argument for int_of_string: %s@." s;
    assert false

let check_syntax s len =
  let arg s b e =
    let i = int_of_string (String.sub s b (e-b)) in
    if i <= 0 then raise (BadSyntaxIndex i);
    if i > len then raise (BadSyntaxArity (len,i));
    ()
  in
  iter_group opt_search_forward arg s

let check_syntax_logic ls s =
  let len = List.length ls.ls_args in
  let ret = ls.ls_value <> None in
  let nfv = Stv.cardinal (ls_ty_freevars ls) in
  let arg s b e =
    if s.[b] = 't' then begin
      let grp = String.sub s (b+1) (e-b-1) in
      let i = int_of_string grp in
      if i < 0 || (not ret && i = 0) then raise (BadSyntaxIndex i);
      if i > len then raise (BadSyntaxArity (len,i))
    end else if s.[b] = 'v' then begin
      let grp = String.sub s (b+1) (e-b-1) in
      let i = int_of_string grp in
      if i < 0 || i >= nfv then raise (BadSyntaxIndex i)
    end else begin
      let grp = String.sub s b (e-b) in
      let i = int_of_string grp in
      if i <= 0 then raise (BadSyntaxIndex i);
      if i > len then raise (BadSyntaxArity (len,i));
    end
  in
  iter_group opt_search_forward arg s

let check_syntax_literal _ts s =
  let count = ref 0 in
  let arg _s _b _e =
    incr count;
  (* nothing else to check ?! *)
  in
  iter_group opt_search_forward_literal_format arg s
  (* if !count <> 1 then *)
    (* raise (BadSyntaxArity (1,!count)) *)

let syntax_arguments s print fmt l =
  let args = Array.of_list l in
  let repl_fun s b e fmt =
    let i = int_of_string (String.sub s b (e-b)) in
    print fmt args.(i-1) in
  global_substitute_fmt opt_search_forward repl_fun s fmt

(* return the type arguments of a symbol application, sorted according
   to their (formal) names *)
let get_type_arguments t = match t.t_node with
  | Tapp (ls, tl) ->
      let m = oty_match Mtv.empty ls.ls_value t.t_ty in
      let m = List.fold_left2
        (fun m ty t -> oty_match m (Some ty) t.t_ty) m ls.ls_args tl in
      let name tv = Mstr.add tv.tv_name.id_string in
      let m = Mtv.fold name m Mstr.empty in
      Array.of_list (Mstr.values m)
  | _ ->
      [||]

let gen_syntax_arguments_typed ty_of tys_of s print_arg print_type t fmt l =
  let args = Array.of_list l in
  let repl_fun s b e fmt =
    if s.[b] = 't' then
      let grp = String.sub s (b+1) (e-b-1) in
      let i = int_of_string grp in
      if i = 0
      then print_type fmt (ty_of t)
      else print_type fmt (ty_of args.(i-1))
    else if s.[b] = 'v' then
      let grp = String.sub s (b+1) (e-b-1) in
      let m = tys_of t in
      print_type fmt m.(int_of_string grp)
    else
      let grp = String.sub s b (e-b) in
      let i = int_of_string grp in
      print_arg fmt args.(i-1) in
  global_substitute_fmt opt_search_forward repl_fun s fmt

let syntax_arguments_typed =
  gen_syntax_arguments_typed t_type get_type_arguments

let syntax_range_literal s fmt c =
  let f s b e fmt =
    let v = Number.compute_int_literal c.Number.ic_abs in
    let base = match s.[e-1] with
      | 'x' -> 16
      | 'd' -> 10
      | 'o' -> 8
      | 'b' -> 2
      | _ -> assert false
    in
    let digits =
      if e > b + 1 then
        Some (int_of_string (String.sub s b (e-b-1)))
      else
        None
    in
    if base = 10 then begin
        if c.Number.ic_negative then fprintf fmt "-";
        Number.print_in_base base digits fmt v
      end
    else
      let v =
        if c.Number.ic_negative then
          match digits with
            | Some d ->
               BigInt.sub (BigInt.pow_int_pos base d) v
            | None -> failwith ("number of digits must be given for printing negative literals in base " ^ string_of_int base)
        else v
      in
      Number.print_in_base base digits fmt v
  in
  global_substitute_fmt opt_search_forward_literal_format f s fmt

let syntax_float_literal s fp fmt c =
  let f s b e fmt =
    let base = match s.[e-1] with
      | 'x' -> 16
      | 'd' -> 10
      | 'o' -> 8
      | 'b' -> 2
      | _ -> assert false
    in
    let digits =
      if e > b + 2 then
        Some (int_of_string (String.sub s (b+1) (e-b-2)))
      else
        None
    in
    let e,m = Number.compute_float c.Number.rc_abs fp in
    let sg = if c.Number.rc_negative then BigInt.one else BigInt.zero in
    match s.[b] with
    | 's' -> Number.print_in_base base digits fmt sg
    | 'e' -> Number.print_in_base base digits fmt e
    | 'm' -> Number.print_in_base base digits fmt m
    | _ -> assert false
  in
  global_substitute_fmt opt_search_forward_literal_format f s fmt

(** {2 use printers} *)

let print_prelude fmt pl =
  let println fmt s = fprintf fmt "%s@\n" s in
  print_list nothing println fmt pl

let print_interface = print_prelude

let print_prelude_of_theories th_used fmt pm =
  let ht = Hid.create 5 in
  List.iter (fun { th_name = id } ->
    if not (Hid.mem ht id) then begin
      print_prelude fmt (Mid.find_def [] id pm);
      Hid.add ht id () end) th_used

let print_th_prelude task fmt pm =
  let th_used = task_fold (fun acc -> function
    | { td_node = Use th | Clone (th,_) } -> th::acc
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
exception TooManyTypeOverride of tysymbol
exception TooManyLogicOverride of lsymbol

let meta_syntax_type = register_meta "syntax_type" [MTtysymbol; MTstring; MTint]
  ~desc:"Specify@ the@ syntax@ used@ to@ pretty-print@ a@ type@ symbol.@ \
         Can@ be@ specified@ in@ the@ driver@ with@ the@ 'syntax type'@ rule."

let meta_syntax_logic = register_meta "syntax_logic" [MTlsymbol; MTstring; MTint]
  ~desc:"Specify@ the@ syntax@ used@ to@ pretty-print@ a@ function/predicate@ \
         symbol.@ \
         Can@ be@ specified@ in@ the@ driver@ with@ the@ 'syntax function'@ \
         or@ 'syntax predicate'@ rules."

let meta_syntax_literal = register_meta "syntax_literal" [MTtysymbol; MTstring; MTint]
  ~desc:"Specify@ the@ syntax@ used@ to@ pretty-print@ a@ range@ literal.@ \
         Can@ be@ specified@ in@ the@ driver@ with@ the@ 'syntax literal'@ \
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

let syntax_type ts s b =
  check_syntax_type ts s;
  create_meta meta_syntax_type [MAts ts; MAstr s; MAint (if b then 1 else 0)]

let syntax_logic ls s b =
  check_syntax_logic ls s;
  create_meta meta_syntax_logic [MAls ls; MAstr s; MAint (if b then 1 else 0)]

let syntax_literal ts s b =
  check_syntax_literal ts s;
  create_meta meta_syntax_literal [MAts ts; MAstr s; MAint (if b then 1 else 0)]

let remove_prop pr =
  create_meta meta_remove_prop [MApr pr]

type syntax_map = (string * int) Mid.t

let change_override e e' rs ov = function
  | None         -> Some (rs,ov)
  | Some (_,0)   ->
    begin match ov with
      | 0 -> raise e
      | 1 -> Some (rs, 2)
      | _ -> assert false
    end
  | Some (rs',1) ->
    begin match ov with
      | 0 -> Some (rs',2)
      | 1 -> raise e'
      | _ -> assert false
    end
  | Some (_,2)   -> raise e'
  | _            -> assert false

let sm_add_ts sm = function
  | [MAts ts; MAstr rs; MAint ov] ->
    Mid.change
      (change_override (KnownTypeSyntax ts) (TooManyTypeOverride ts)
         rs ov) ts.ts_name sm
  | _ -> assert false

let sm_add_ls sm = function
  | [MAls ls; MAstr rs; MAint ov] ->
    Mid.change
      (change_override (KnownLogicSyntax ls) (TooManyLogicOverride ls)
         rs ov) ls.ls_name sm
  | _ -> assert false

let sm_add_pr sm = function
  | [MApr pr] -> Mid.add pr.pr_name ("",0) sm
  | _ -> assert false

let get_syntax_map task =
  let sm = Mid.empty in
  let sm = Task.on_meta meta_syntax_type sm_add_ts sm task in
  let sm = Task.on_meta meta_syntax_logic sm_add_ls sm task in
  let sm = Task.on_meta meta_remove_prop sm_add_pr sm task in
  sm

let get_rliteral_map task =
  Task.on_meta meta_syntax_literal sm_add_ts Mid.empty task

let add_syntax_map td sm = match td.td_node with
  | Meta (m, args) when meta_equal m meta_syntax_type ->
      sm_add_ts sm args
  | Meta (m, args) when meta_equal m meta_syntax_logic ->
      sm_add_ls sm args
  | Meta (m, args) when meta_equal m meta_remove_prop ->
      sm_add_pr sm args
  | _ -> sm

let add_rliteral_map td sm = match td.td_node with
  | Meta (m, args) when meta_equal m meta_syntax_literal ->
      sm_add_ts sm args
  | _ -> sm

let query_syntax sm id =
  try Some (fst (Mid.find id sm)) with Not_found -> None

let on_syntax_map fn =
  Trans.on_meta meta_syntax_type (fun sts ->
  Trans.on_meta meta_syntax_logic (fun sls ->
  Trans.on_meta meta_remove_prop (fun spr ->
    let sm = Mid.empty in
    let sm = List.fold_left sm_add_ts sm sts in
    let sm = List.fold_left sm_add_ls sm sls in
    let sm = List.fold_left sm_add_pr sm spr in
    fn sm)))

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
  | TooManyTypeOverride ts ->
      fprintf fmt "Too many syntax overriding for type symbol %a"
        Pretty.print_ts ts
  | TooManyLogicOverride ls ->
      fprintf fmt "Too many syntax overriding for logic symbol %a"
        Pretty.print_ls ls
  | BadSyntaxIndex i ->
      fprintf fmt "Bad argument index %d, must start with 1" i
  | BadSyntaxArity (i1,i2) ->
      fprintf fmt "Bad argument index %d, must end with %d" i2 i1
  | Unsupported s ->
      fprintf fmt "@[<hov 3> Uncaught exception 'Unsupported %s'@]" s
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
