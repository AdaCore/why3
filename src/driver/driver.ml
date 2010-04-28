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
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task
open Driver_ast
open Call_provers

(** error handling *)

type error = string

exception Error of error

let report = pp_print_string

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let errorm ?loc f =
  let buf = Buffer.create 512 in
  let fmt = formatter_of_buffer buf in
  kfprintf
    (fun _ ->
       pp_print_flush fmt ();
       let s = Buffer.contents buf in
       Buffer.clear buf;
       error ?loc s)
    fmt f

(** syntax substitutions *)

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

let check_syntax loc s len =
  let arg s =
    let i = int_of_string (Str.matched_group 1 s) in
    if i = 0 then errorm ~loc "bad index '%%0': start with '%%1'";
    if i > len then
      errorm ~loc "bad index '%%%i': the symbol has %i arguments" i len
  in
  iter_group regexp_arg_pos arg s

let syntax_arguments s print fmt l =
  let args = Array.of_list l in
  let repl_fun s fmt =
    let i = int_of_string (Str.matched_group 1 s) in
    print fmt args.(i-1) in
  global_substitute_fmt regexp_arg_pos repl_fun s fmt

(** drivers *)

type driver = {
  drv_env       : Env.env;
  drv_printer   : string option;
  drv_prelude   : string list;
  drv_filename  : string option;
  drv_transform : string list;
  drv_thprelude : string list Mid.t;
  drv_tags      : Sstr.t Mid.t;
  drv_tags_cl   : Sstr.t Mid.t;
  drv_syntax    : string Mid.t;
  drv_remove    : Sid.t;
  drv_remove_cl : Sid.t;
  drv_regexps   : (Str.regexp * Call_provers.prover_answer) list;
  drv_exitcodes : (int * Call_provers.prover_answer) list;
  drv_tag       : int
}

(** parse a driver file *)

let load_plugin dir (byte,nat) =
  if not Config.why_plugins then errorm "Plugins not supported";
  let file = if Config.Dynlink.is_native then nat else byte in
  let file = Filename.concat dir file in
  Config.Dynlink.loadfile_private file

let load_file file =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let f = Driver_lexer.parse_file lb in
  close_in c;
  f

let string_of_qualid thl idl =
  String.concat "." thl ^ "." ^ String.concat "." idl

let load_driver = let driver_tag = ref (-1) in fun env file ->
  let prelude   = ref [] in
  let regexps   = ref [] in
  let exitcodes = ref [] in
  let filename  = ref None in
  let printer   = ref None in
  let transform = ref [] in

  let set_or_raise loc r v error = match !r with
    | Some _ -> errorm ~loc "duplicate %s" error
    | None   -> r := Some v
  in
  let add_to_list r v = (r := v :: !r) in
  let add_global (loc, g) = match g with
    | Prelude s -> add_to_list prelude s
    | RegexpValid s -> add_to_list regexps (Str.regexp s, Valid)
    | RegexpInvalid s -> add_to_list regexps (Str.regexp s, Invalid)
    | RegexpTimeout s -> add_to_list regexps (Str.regexp s, Timeout)
    | RegexpUnknown (s,t) -> add_to_list regexps (Str.regexp s, Unknown t)
    | RegexpFailure (s,t) -> add_to_list regexps (Str.regexp s, Failure t)
    | ExitCodeValid s -> add_to_list exitcodes (s, Valid)
    | ExitCodeInvalid s -> add_to_list exitcodes (s, Invalid)
    | ExitCodeTimeout s -> add_to_list exitcodes (s, Timeout)
    | ExitCodeUnknown (s,t) -> add_to_list exitcodes (s, Unknown t)
    | ExitCodeFailure (s,t) -> add_to_list exitcodes (s, Failure t)
    | Filename s -> set_or_raise loc filename s "filename"
    | Printer s -> set_or_raise loc printer s "printer"
    | Transform s -> add_to_list transform s
    | Plugin files -> load_plugin (Filename.dirname file) files
  in
  let f = load_file file in
  List.iter add_global f.f_global;

  let thprelude = ref Mid.empty in
  let tags      = ref Mid.empty in
  let tags_cl   = ref Mid.empty in
  let syntax    = ref Mid.empty in
  let remove    = ref Sid.empty in
  let remove_cl = ref Sid.empty in
  let qualid    = ref [] in

  let find_pr th (loc,q) = try ns_find_pr th.th_export q with Not_found ->
    errorm ~loc "unknown proposition %s" (string_of_qualid !qualid q)
  in
  let find_ls th (loc,q) = try ns_find_ls th.th_export q with Not_found ->
    errorm ~loc "unknown logic symbol %s" (string_of_qualid !qualid q)
  in
  let find_ts th (loc,q) = try ns_find_ts th.th_export q with Not_found ->
    errorm ~loc "unknown type symbol %s" (string_of_qualid !qualid q)
  in
  let add_syntax loc k (_,q) id n s =
    check_syntax loc s n;
    if Mid.mem id !syntax then
      errorm ~loc "duplicate syntax rule for %s symbol %s"
        k (string_of_qualid !qualid q);
    syntax := Mid.add id s !syntax;
    remove := Sid.add id !remove
  in
  let add_tag c id s =
    let mr = if c then tags_cl else tags in
    let im = try Mid.find id !mr with Not_found -> Sstr.empty in
    mr := Mid.add id (Sstr.add s im) !mr
  in
  let add_local th (loc,rule) = match rule with
    | Rprelude s ->
        let l = try Mid.find th.th_name !thprelude with Not_found -> [] in
        thprelude := Mid.add th.th_name (s::l) !thprelude
    | Rsyntaxls (q,s) ->
        let ls = find_ls th q in
        add_syntax loc "logic" q ls.ls_name (List.length ls.ls_args) s
    | Rsyntaxts (q,s) ->
        let ts = find_ts th q in
        add_syntax loc "type"  q ts.ts_name (List.length ts.ts_args) s
    | Rremovepr (c,q) ->
        let sr = if c then remove_cl else remove in
        sr := Sid.add (find_pr th q).pr_name !sr
    | Rtagts (c,q,s) -> add_tag c (find_ts th q).ts_name s
    | Rtagls (c,q,s) -> add_tag c (find_ls th q).ls_name s
    | Rtagpr (c,q,s) -> add_tag c (find_pr th q).pr_name s
  in
  let add_theory { thr_name = (loc,q); thr_rules = trl } =
    let f,id = let l = List.rev q in List.rev (List.tl l),List.hd l in
    let th = try Env.find_theory env f id with Env.TheoryNotFound (l,s) ->
      errorm ~loc "theory %s.%s not found" (String.concat "." l) s
    in
    qualid := q;
    List.iter (add_local th) trl
  in
  List.iter add_theory f.f_rules;
  transform := List.rev !transform;
  incr driver_tag;
  {
    drv_env       = env;
    drv_printer   = !printer;
    drv_prelude   = !prelude;
    drv_filename  = !filename;
    drv_transform = !transform;
    drv_thprelude = !thprelude;
    drv_tags      = !tags;
    drv_tags_cl   = !tags_cl;
    drv_syntax    = !syntax;
    drv_remove    = !remove;
    drv_remove_cl = !remove_cl;
    drv_regexps   = !regexps;
    drv_exitcodes = !exitcodes;
    drv_tag       = !driver_tag;
  }

(** query drivers *)

type driver_query = {
  query_syntax : ident -> string option;
  query_remove : ident -> bool;
  query_tags   : ident -> Sstr.t;
  query_driver : driver;
  query_lclone : task;
  query_tag    : int;
}

module Hsdq = Hashcons.Make (struct
  type t = driver_query

  let equal q1 q2 = q1.query_driver == q2.query_driver &&
    task_equal q1.query_lclone q2.query_lclone

  let hash q = Hashcons.combine q.query_driver.drv_tag
    (option_apply 0 (fun t -> 1 + t.task_tag) q.query_lclone)

  let tag n q = { q with query_tag = n }
end)

module Dq = StructMake (struct
  type t = driver_query
  let tag q = q.query_tag
end)

module Sdq = Dq.S
module Mdq = Dq.M
module Hdq = Dq.H

let get_tags map id = try Mid.find id map with Not_found -> Sstr.empty
let add_tags drv id acc = Sstr.union (get_tags drv.drv_tags_cl id) acc
let add_remove drv id acc = acc || Sid.mem id drv.drv_remove_cl

let driver_query drv task =
  let clone = task_clone task in
  let htags = Hid.create 7 in
  let query_tags id = try Hid.find htags id with Not_found ->
    let r = try Mid.find id clone with Not_found -> Sid.empty in
    let s = Sid.fold (add_tags drv) r (get_tags drv.drv_tags id) in
    Hid.replace htags id s; s
  in
  let hremove = Hid.create 7 in
  let query_remove id = try Hid.find hremove id with Not_found ->
    let r = try Mid.find id clone with Not_found -> Sid.empty in
    let s = Sid.fold (add_remove drv) r (Sid.mem id drv.drv_remove) in
    Hid.replace hremove id s; s
  in
  let query_syntax id =
    try Some (Mid.find id drv.drv_syntax) with Not_found -> None
  in
  Hsdq.hashcons {
    query_syntax = query_syntax;
    query_remove = query_remove;
    query_tags   = query_tags;
    query_driver = drv;
    query_lclone = last_clone task;
    query_tag    = -1 }

let query_syntax dq = dq.query_syntax
let query_remove dq = dq.query_remove
let query_tags   dq = dq.query_tags
let query_driver dq = dq.query_driver
let query_env    dq = dq.query_driver.drv_env
let query_clone  dq = task_clone (dq.query_lclone)
let query_tag    dq = dq.query_tag

(** apply drivers *)

let get_transform drv = drv.drv_transform
let get_printer drv = drv.drv_printer
let get_env drv = drv.drv_env

let print_prelude_list fmt prel =
  let pr_pr s () = fprintf fmt "%s@\n" s in
  List.fold_right pr_pr prel ()

let print_prelude drv task fmt =
  print_prelude_list fmt drv.drv_prelude;
  let seen = Hid.create 17 in
  let rec print_prel th_name th =
    if Hid.mem seen th_name then () else begin
      Hid.add seen th_name ();
      Mid.iter print_prel th.th_used;
      let prel =
        try Mid.find th_name drv.drv_thprelude
        with Not_found -> []
      in
      print_prelude_list fmt prel
    end
  in
  Mid.iter print_prel (task_used task);
  fprintf fmt "@."

let print_full_prelude dq = print_prelude dq.query_driver

let print_global_prelude dq fmt =
  print_prelude_list fmt dq.query_driver.drv_prelude

let print_theory_prelude dq th_name fmt =
  let prel =
    try Mid.find th_name dq.query_driver.drv_thprelude
    with Not_found -> []
  in
  print_prelude_list fmt prel

let filename_regexp = Str.regexp "%\\(.\\)"

let get_filename drv input_file theory_name goal_name =
  let file = match drv.drv_filename with
    | Some f -> f
    | None -> "%f-%t-%g.dump"
  in
  let replace s = match Str.matched_group 1 s with
    | "%" -> "%"
    | "f" -> input_file
    | "t" -> theory_name
    | "g" -> goal_name
    | _ -> errorm "unknown format specifier, use %%f, %%t or %%g"
  in
  Str.global_substitute filename_regexp replace file

let file_of_task drv input_file theory_name task =
  get_filename drv input_file theory_name (task_goal task).pr_name.id_short

let call_on_buffer ?debug ~command ?timelimit ?memlimit drv buffer =
  let regexps = drv.drv_regexps in
  let exitcodes = drv.drv_exitcodes in
  let filename = get_filename drv "" "" "" in
  Call_provers.call_on_buffer
    ?debug ~command ?timelimit ?memlimit ~regexps ~exitcodes ~filename buffer

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. test"
End:
*)
