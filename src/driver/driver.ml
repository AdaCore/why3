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

type translation =
  | Remove
  | Syntax of string
  | Tag of Sstr.t

let translation_union t1 t2 = match t1, t2 with
  | Remove, _ | _, Remove -> Remove
  | ((Syntax _ as s), _) | (_,(Syntax _ as s)) -> s
  | Tag s1, Tag s2 -> Tag (Sstr.union s1 s2)

let print_translation fmt = function
  | Remove -> Format.fprintf fmt "remove"
  | Syntax s -> Format.fprintf fmt "syntax %s" s
  | Tag s -> Format.fprintf fmt "tag %a"
      (Pp.print_iter1 Sstr.iter Pp.comma Pp.string) s

type printer = (ident -> translation) -> Format.formatter -> task -> unit

type driver = {
  drv_env          : Env.env;
  drv_printer      : printer option;
  drv_prelude      : string list;
  drv_filename     : string option;
  drv_transform    : task trans_reg;
  drv_thprelude    : string list Mid.t;
  drv_translations : (translation * translation) Mid.t;
  drv_regexps      : (Str.regexp * Call_provers.prover_answer) list;
  drv_exitcodes    : (int * Call_provers.prover_answer) list;
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

let add_htheory tmap cloned id t =
  try
    let t2,t3 = Mid.find id tmap in
    let t23 = if cloned
      then translation_union t t2, t3
      else t2, translation_union t t3
    in
    Mid.add id t23 tmap
  with Not_found ->
    let t23 = if cloned
      then Tag Sstr.empty, t
      else t, Tag Sstr.empty
    in
    Mid.add id t23 tmap

let load_rules env (pmap,tmap) { thr_name = (loc,qualid); thr_rules = trl } =
  let qfile,id = let l = List.rev qualid in List.rev (List.tl l),List.hd l in
  let th = try Env.find_theory env qfile id with Env.TheoryNotFound (l,s) ->
    errorm ~loc "theory %s.%s not found" (String.concat "." l) s
  in
  let find_pr (loc,q) = try ns_find_pr th.th_export q with Not_found ->
    errorm ~loc "Unknown proposition %s" (string_of_qualid qualid q)
  in
  let find_ls (loc,q) = try ns_find_ls th.th_export q with Not_found ->
    errorm ~loc "Unknown logic symbol %s" (string_of_qualid qualid q)
  in
  let find_ts (loc,q) = try ns_find_ts th.th_export q with Not_found ->
    errorm ~loc "Unknown type symbol %s" (string_of_qualid qualid q)
  in
  let add (pmap,tmap) (loc,rule) = match rule with
    | Rremove (c,q) ->
        pmap, add_htheory tmap c (find_pr q).pr_name Remove
    | Rsyntaxls (q,s) -> let ls = find_ls q in
        check_syntax loc s (List.length ls.ls_args);
        pmap, add_htheory tmap false ls.ls_name (Syntax s)
    | Rsyntaxty (q,s) -> let ts = find_ts q in
        check_syntax loc s (List.length ts.ts_args);
        pmap, add_htheory tmap false ts.ts_name (Syntax s)
    | Rtagls (c,q,s) ->
        pmap, add_htheory tmap c (find_ls q).ls_name (Tag (Sstr.singleton s))
    | Rtagty (c,q,s) ->
        pmap, add_htheory tmap c (find_ts q).ts_name (Tag (Sstr.singleton s))
    | Rtagpr (c,q,s) ->
        pmap, add_htheory tmap c (find_pr q).pr_name (Tag (Sstr.singleton s))
    | Rprelude s ->
        let l = try Mid.find th.th_name pmap with Not_found -> [] in
        Mid.add th.th_name (s::l) pmap, tmap
  in
  List.fold_left add (pmap,tmap) trl

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
  let add (loc, g) = match g with
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
        try transform := compose (Hashtbl.find transforms s) !transform
        with Not_found -> errorm ~loc "unknown transformation %s" s end
    | Plugin files -> load_plugin (Filename.dirname file) files
  in
  let f = load_file file in
  List.iter add f.f_global;
  let (pmap,tmap) =
      List.fold_left (load_rules env) (Mid.empty,Mid.empty) f.f_rules
  in
  {
    drv_env          = env;
    drv_printer      = !printer;
    drv_prelude      = !prelude;
    drv_filename     = !filename;
    drv_transform    = !transform;
    drv_thprelude    = pmap;
    drv_translations = tmap;
    drv_regexps      = !regexps;
    drv_exitcodes    = !exitcodes;
  }

(** querying drivers *)

let query_ident drv clone =
  let h = Hid.create 7 in
  fun id ->
    try
      Hid.find h id
    with Not_found ->
      let r = try
        Mid.find id clone
      with Not_found -> Sid.empty in
      let tr = try fst (Mid.find id drv.drv_translations)
      with Not_found -> Tag Sstr.empty in
      let tr = Sid.fold
        (fun id acc -> try translation_union acc
           (snd (Mid.find id drv.drv_translations))
         with Not_found -> acc) r tr in
      Hid.add h id tr;
      tr

(** using drivers *)

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
    | Some p -> p (query_ident drv (task_clone task))
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
