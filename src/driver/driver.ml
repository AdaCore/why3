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

open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task
open Register
open Driver_ast
open Call_provers

(** error handling *)

type error = string

exception Error of string

let report = Format.pp_print_string

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let errorm ?loc f =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
       Format.pp_print_flush fmt ();
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
      Format.pp_print_string fmt (Str.string_after text start)
    else
      match opt_search_forward expr text startpos with
      | None ->
          Format.pp_print_string fmt (Str.string_after text start)
      | Some pos ->
          let end_pos = Str.match_end () in
          Format.pp_print_string fmt (String.sub text start (pos - start));
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

type driver_query = {
  query_syntax : ident -> string option;
  query_remove : ident -> bool;
  query_tags   : ident -> Sstr.t;
}

type printer = driver_query -> Format.formatter -> task -> unit

type driver = {
  drv_env       : Env.env;
  drv_printer   : printer option;
  drv_prelude   : string list;
  drv_filename  : string option;
  drv_transform : task trans_reg;
  drv_thprelude : string list Mid.t;
  drv_tags      : Sstr.t Mid.t;
  drv_tags_cl   : Sstr.t Mid.t;
  drv_syntax    : string Mid.t;
  drv_remove    : Sid.t;
  drv_remove_cl : Sid.t;
  drv_regexps   : (Str.regexp * Call_provers.prover_answer) list;
  drv_exitcodes : (int * Call_provers.prover_answer) list;
}

(** register printers and transformations *)

let printers : (string, printer) Hashtbl.t = Hashtbl.create 17
let register_printer name printer = Hashtbl.replace printers name printer
let list_printers () = Hashtbl.fold (fun k _ acc -> k::acc) printers []

let transforms : (string, task trans_reg) Hashtbl.t = Hashtbl.create 17
let register_transform name trans = Hashtbl.replace transforms name trans
let list_transforms () = Hashtbl.fold (fun k _ acc -> k::acc) transforms []

let transforms_l : (string, task tlist_reg) Hashtbl.t = Hashtbl.create 17
let register_transform_l name trans = Hashtbl.replace transforms_l name trans
let list_transforms_l () = Hashtbl.fold (fun k _ ac -> k::ac) transforms_l []

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

let load_driver env file =
  let prelude   = ref [] in
  let regexps   = ref [] in
  let exitcodes = ref [] in
  let filename  = ref None in
  let printer   = ref None in
  let transform = ref identity in

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
    | Printer s -> begin
        try set_or_raise loc printer (Hashtbl.find printers s) "printer"
        with Not_found -> errorm ~loc "unknown printer %s" s end
    | Transform s -> begin
        try transform := compose !transform (Hashtbl.find transforms s)
        with Not_found -> errorm ~loc "unknown transformation %s" s end
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
    syntax := Mid.add id s !syntax
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
  }

(** query drivers *)

let get_tags map id = try Mid.find id map with Not_found -> Sstr.empty
let add_tags drv id acc = Sstr.union (get_tags drv.drv_tags_cl id) acc
let add_remove drv id acc = acc || Sid.mem id drv.drv_remove_cl

let query_driver drv clone =
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
  { query_syntax = query_syntax;
    query_remove = query_remove;
    query_tags   = query_tags }

(** apply drivers *)

let print_prelude drv used fmt =
  let pr_pr s () = Format.fprintf fmt "%s@\n" s in
  List.fold_right pr_pr drv.drv_prelude ();
  let seen = Hid.create 17 in
  let rec print_prel th_name th =
    if Hid.mem seen th_name then () else begin
      Hid.add seen th_name ();
      Mid.iter print_prel th.th_used;
      let prel =
        try Mid.find th_name drv.drv_thprelude
        with Not_found -> []
      in
      List.fold_right pr_pr prel ()
    end
  in
  Mid.iter print_prel used;
  Format.fprintf fmt "@."

let print_task drv fmt task =
  let task = apply_env drv.drv_transform drv.drv_env task in
  let printer = match drv.drv_printer with
    | None -> errorm "no printer specified in the driver file"
    | Some p -> p (query_driver drv (task_clone task))
  in
  print_prelude drv (task_used task) fmt;
  Format.fprintf fmt "@[%a@]@?" printer task

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

let call_on_buffer ?debug ~command ~timelimit ~memlimit drv buffer =
  let regexps = drv.drv_regexps in
  let exitcodes = drv.drv_exitcodes in
  let filename = get_filename drv "" "" "" in
  Call_provers.call_on_buffer
    ?debug ~command ~timelimit ~memlimit ~regexps ~exitcodes ~filename buffer

let prove_task ?debug ~command ~timelimit ~memlimit drv task =
  let buf = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer buf in
  print_task drv fmt task; Format.pp_print_flush fmt ();
  call_on_buffer ?debug ~command ~timelimit ~memlimit drv buf

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. test"
End:
*)
