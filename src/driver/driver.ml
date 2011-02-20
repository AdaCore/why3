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
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task
open Printer
open Trans
open Driver_ast
open Call_provers

(** drivers *)

type driver = {
  drv_env         : Env.env;
  drv_printer     : string option;
  drv_filename    : string option;
  drv_transform   : string list;
  drv_prelude     : prelude;
  drv_thprelude   : prelude_map;
  drv_meta        : (theory * Stdecl.t) Mid.t;
  drv_meta_cl     : (theory * Stdecl.t) Mid.t;
  drv_regexps     : (Str.regexp * prover_answer) list;
  drv_timeregexps : Call_provers.timeregexp list;
  drv_exitcodes   : (int * prover_answer) list;
}

(** parse a driver file *)

exception NoPlugins

let load_plugin dir (byte,nat) =
  if not Config.plugins then raise NoPlugins;
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

exception Duplicate    of string
exception UnknownType  of (string list * string list)
exception UnknownLogic of (string list * string list)
exception UnknownProp  of (string list * string list)

let load_driver = let driver_tag = ref (-1) in fun env file ->
  let prelude   = ref [] in
  let regexps   = ref [] in
  let exitcodes = ref [] in
  let filename  = ref None in
  let printer   = ref None in
  let transform = ref [] in
  let timeregexps = ref [] in

  let set_or_raise loc r v error = match !r with
    | Some _ -> raise (Loc.Located (loc, Duplicate error))
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
    | TimeRegexp r -> add_to_list timeregexps (Call_provers.timeregexp r)
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
  let meta      = ref Mid.empty in
  let meta_cl   = ref Mid.empty in
  let qualid    = ref [] in

  let find_pr th (loc,q) = try ns_find_pr th.th_export q
    with Not_found -> raise (Loc.Located (loc, UnknownProp (!qualid,q)))
  in
  let find_ls th (loc,q) = try ns_find_ls th.th_export q
    with Not_found -> raise (Loc.Located (loc, UnknownLogic (!qualid,q)))
  in
  let find_ts th (loc,q) = try ns_find_ts th.th_export q
    with Not_found -> raise (Loc.Located (loc, UnknownType (!qualid,q)))
  in
  let add_meta th td m =
    let s = try snd (Mid.find th.th_name !m) with Not_found -> Stdecl.empty in
    m := Mid.add th.th_name (th, Stdecl.add td s) !m
  in
  let add_local th = function
    | Rprelude s ->
        let l = try Mid.find th.th_name !thprelude with Not_found -> [] in
        thprelude := Mid.add th.th_name (l @ [s]) !thprelude
    | Rsyntaxts (c,q,s) ->
        let td = syntax_type (find_ts th q) s in
        add_meta th td (if c then meta_cl else meta)
    | Rsyntaxls (c,q,s) ->
        let td = syntax_logic (find_ls th q) s in
        add_meta th td (if c then meta_cl else meta)
    | Rremovepr (c,q) ->
        let td = remove_prop (find_pr th q) in
        add_meta th td (if c then meta_cl else meta)
    | Rmeta (c,s,al) ->
        let convert = function
          | PMAts q  -> MAts (find_ts th q)
          | PMAls q  -> MAls (find_ls th q)
          | PMApr q  -> MApr (find_pr th q)
          | PMAstr s -> MAstr s
          | PMAint i -> MAint i
        in
        let m = lookup_meta s in
        let td = create_meta m (List.map convert al) in
        add_meta th td (if c then meta_cl else meta)
  in
  let add_local th (loc,rule) =
    try add_local th rule with e -> raise (Loc.Located (loc,e))
  in
  let add_theory { thr_name = (loc,q); thr_rules = trl } =
    let f,id = let l = List.rev q in List.rev (List.tl l),List.hd l in
    let th =
      try Env.find_theory env f id with e -> raise (Loc.Located (loc,e))
    in
    qualid := q;
    List.iter (add_local th) trl
  in
  List.iter add_theory f.f_rules;
  transform := List.rev !transform;
  incr driver_tag;
  {
    drv_env         = env;
    drv_printer     = !printer;
    drv_prelude     = !prelude;
    drv_filename    = !filename;
    drv_transform   = !transform;
    drv_thprelude   = !thprelude;
    drv_meta        = !meta;
    drv_meta_cl     = !meta_cl;
    drv_regexps     = List.rev !regexps;
    drv_timeregexps = List.rev !timeregexps;
    drv_exitcodes   = List.rev !exitcodes;
  }

(** apply drivers *)

exception UnknownSpec of string

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
    | s   -> raise (UnknownSpec s)
  in
  Str.global_substitute filename_regexp replace file

let file_of_task drv input_file theory_name task =
  get_filename drv input_file theory_name (task_goal task).pr_name.id_string

let call_on_buffer ~command ?timelimit ?memlimit drv buffer =
  let regexps = drv.drv_regexps in
  let timeregexps = drv.drv_timeregexps in
  let exitcodes = drv.drv_exitcodes in
  let filename = get_filename drv "" "" "" in
  Call_provers.call_on_buffer
    ~command ?timelimit ?memlimit ~regexps ~timeregexps
    ~exitcodes ~filename buffer

(** print'n'prove *)

exception NoPrinter

let update_task drv task =
  let task, goal = match task with
    | Some { task_decl = g ; task_prev = t } -> t,g
    | None -> raise Task.GoalNotFound
  in
  let task =
    Mid.fold (fun _ (th,s) task ->
      if Task.on_used_theory th task then
        Stdecl.fold (fun tdm task ->
          add_tdecl task tdm
        ) s task
      else task
    ) drv.drv_meta task
  in
  let task =
    Mid.fold (fun _ (th,s) task ->
      Task.on_theory th (fun task sm ->
        Stdecl.fold (fun tdm task ->
          add_tdecl task (clone_meta tdm sm)
        ) s task
      ) task task
    ) drv.drv_meta_cl task
  in
  add_tdecl task goal

let print_task ?old drv fmt task =
  let p = match drv.drv_printer with
    | None -> raise NoPrinter
    | Some p -> p
  in
  let printer =
    lookup_printer p drv.drv_env drv.drv_prelude drv.drv_thprelude
  in
  let lookup_transform t = t, lookup_transform t drv.drv_env in
  let transl = List.map lookup_transform drv.drv_transform in
  let apply task (_t, tr) =
(*  Format.printf "@\n@\n[%f] %s@." (Sys.time ()) t; *)
    Trans.apply tr task
  in
(*Format.printf "@\n@\nTASK";*)
  let task = update_task drv task in
  let task = List.fold_left apply task transl in
  fprintf fmt "@[%a@]@?" (printer ?old) task

let prove_task ~command ?timelimit ?memlimit ?old drv task =
  let buf = Buffer.create 1024 in
  let fmt = formatter_of_buffer buf in
  print_task ?old drv fmt task; pp_print_flush fmt ();
  let res = call_on_buffer ~command ?timelimit ?memlimit drv buf in
  Buffer.reset buf;
  res

(* exception report *)

let string_of_qualid thl idl =
  String.concat "." thl ^ "." ^ String.concat "." idl

let () = Exn_printer.register (fun fmt exn -> match exn with
  | NoPrinter -> Format.fprintf fmt
      "No printer specified in the driver file"
  | NoPlugins -> Format.fprintf fmt
      "Plugins are not supported, recomplie Why"
  | Duplicate s -> Format.fprintf fmt
      "Duplicate %s specification" s
  | UnknownType (thl,idl) -> Format.fprintf fmt
      "Unknown type symbol %s" (string_of_qualid thl idl)
  | UnknownLogic (thl,idl) -> Format.fprintf fmt
      "Unknown logical symbol %s" (string_of_qualid thl idl)
  | UnknownProp (thl,idl) -> Format.fprintf fmt
      "Unknown proposition %s" (string_of_qualid thl idl)
  | UnknownSpec s -> Format.fprintf fmt
      "Unknown format specifier '%%%s', use %%f, %%t or %%g" s
  | e -> raise e)

