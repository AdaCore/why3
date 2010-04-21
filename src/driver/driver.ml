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
open Register
open Driver_ast
open Call_provers

(* Utils from Str *)

(* From global_substitute of str *)
open Str
let opt_search_forward re s pos =
  try Some(search_forward re s pos) with Not_found -> None

let global_substitute_fmt expr repl_fun text fmt =
  let rec replace start last_was_empty =
    let startpos = if last_was_empty then start + 1 else start in
    if startpos > String.length text then
      pp_print_string fmt (string_after text start)
    else
      match opt_search_forward expr text startpos with
      | None ->
          pp_print_string fmt (string_after text start)
      | Some pos ->
          let end_pos = match_end() in
          pp_print_string fmt (String.sub text start (pos-start));
          repl_fun text fmt;
          replace end_pos (end_pos = pos)
  in
    (replace 0 false)

let iter_group expr iter_fun text =
  let rec iter start last_was_empty =
    let startpos = if last_was_empty then start + 1 else start in
    if startpos < String.length text then
      match opt_search_forward expr text startpos with
        | None -> ()
        | Some pos ->
            let end_pos = match_end() in
            iter_fun text;
            iter end_pos (end_pos = pos)
  in
  iter 0 false
 
(* *)

type error = string

exception Error of string

let report = pp_print_string

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

(** creating drivers *)

type theory_driver = {
  thd_prelude : string list;
  thd_tsymbol : unit ;
}

type translation = 
  | Remove
  | Syntax of string
  | Tag of Sstr.t

let translation_union t1 t2 = match t1, t2 with
  | Remove, _ | _, Remove -> Remove
  | ((Syntax _ as s), _) | (_,(Syntax _ as s)) -> s
  | Tag s1, Tag s2 -> Tag (Sstr.union s1 s2)

let print_translation fmt = function
  | Remove -> fprintf fmt "remove" 
  | Syntax s -> fprintf fmt "syntax %s" s
  | Tag s -> fprintf fmt "tag %a" 
      (Pp.print_iter1 Sstr.iter Pp.comma Pp.string) s

type printer = (ident -> translation) -> formatter -> task -> unit

type driver = {
  drv_env          : Env.env;
  drv_printer      : printer option;
  drv_prelude      : string list;
  drv_filename     : string option;
  drv_transforms   : task tlist_reg;
  drv_thprelude    : string list Mid.t;
  drv_translations : (translation * translation) Mid.t;
  drv_regexps      : (Str.regexp * Call_provers.prover_answer) list;
  drv_exitcodes    : (int * Call_provers.prover_answer) list; 
}

(** registering transformation *)

let (transforms : (string, task tlist_reg) Hashtbl.t) = Hashtbl.create 17
let register_transform_l name trans = Hashtbl.replace transforms name trans
let register_transform name t = register_transform_l name (singleton t)
let list_transforms () = Hashtbl.fold (fun k _ acc -> k::acc) transforms []

(** registering printers *)

let (printers : (string, printer) Hashtbl.t) = Hashtbl.create 17
let register_printer name printer = Hashtbl.replace printers name printer
let list_printers () = Hashtbl.fold (fun k _ acc -> k::acc) printers []

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
  let thl = String.concat "." thl in
  let idl = String.concat "." idl in
  thl^"."^idl

let regexp_arg_pos = Str.regexp "%\\([0-9]+\\)"

let check_syntax loc s len =
  let arg s =
    let i = int_of_string (matched_group 1 s) in
    if i = 0 then errorm ~loc "bad index '%%0': start with '%%1'";
    if i > len then 
      errorm ~loc "bad index '%%%i': the symbol has %i arguments" i len
  in
  iter_group regexp_arg_pos arg s 

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

let load_rules env (pmap,tmap) {thr_name = loc,qualid; thr_rules = trl} =
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
  let add (pmap,tmap) = function
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
    | Rprelude (_loc,s) -> 
        let l = try Mid.find th.th_name pmap with Not_found -> [] in
        Mid.add th.th_name (s::l) pmap, tmap
  in
  List.fold_left add (pmap,tmap) trl

let load_driver file env =
  let f = load_file file in
  let prelude     = ref [] in
  let printer     = ref None in
  let filename    = ref None in
  let ltransforms = ref None in
  let regexps     = ref [] in
  let exitcodes   = ref [] in
  let set_or_raise loc r v error =
    if !r <> None then errorm ~loc "duplicate %s" error
    else r := Some v 
  in 
  let add (loc, g) = match g with
    | Printer _ when !printer <> None -> 
	errorm ~loc "duplicate printer"
    | Printer s when Hashtbl.mem printers s ->
	printer := Some (Hashtbl.find printers s)
    | Printer s -> 
	errorm ~loc "unknown printer %s" s 
    | Prelude s -> prelude := s :: !prelude
    | RegexpValid s -> regexps:=(s,Valid)::!regexps
    | RegexpInvalid s -> regexps:=(s,Invalid)::!regexps
    | RegexpTimeout s -> regexps:=(s,Timeout)::!regexps
    | RegexpUnknown (s1,s2) -> regexps:=(s1,Unknown s2)::!regexps
    | RegexpFailure (s1,s2) -> regexps:=(s1,Failure s2)::!regexps
    | ExitCodeValid s -> exitcodes:=(s,Valid)::!exitcodes
    | ExitCodeInvalid s -> exitcodes:=(s,Invalid)::!exitcodes
    | ExitCodeTimeout s -> exitcodes:=(s,Timeout)::!exitcodes
    | ExitCodeUnknown (s1,s2) -> exitcodes:=(s1,Unknown s2)::!exitcodes
    | ExitCodeFailure (s1,s2) -> exitcodes:=(s1,Failure s2)::!exitcodes
    | Filename s -> set_or_raise loc filename s "filename"
    | Transforms s -> set_or_raise loc ltransforms s "transform"
    | Plugin files -> load_plugin (Filename.dirname file) files
  in
  List.iter add f.f_global;
  let regexps = List.map (fun (s,a) -> (Str.regexp s,a)) !regexps in
  let trans r =
    let transformations = match !r with
      | Some l -> l
      | None -> [] 
    in
    List.fold_left 
      (fun acc (loc,s) -> 
         let t = 
           try Hashtbl.find transforms s
           with Not_found -> errorm ~loc "unknown transformation %s" s in
         compose_l acc t
      )
      identity_l transformations
  in
  let transforms = trans ltransforms in
  let (pmap,tmap) = 
      List.fold_left (load_rules env) (Mid.empty,Mid.empty) f.f_rules 
  in
  { 
    drv_env          = env;
    drv_printer      = !printer;
    drv_prelude      = !prelude;
    drv_filename     = !filename;
    drv_transforms   = transforms;
    drv_thprelude    = pmap;
    drv_translations = tmap;
    drv_regexps      = regexps;
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

let syntax_arguments s print fmt l =
  let args = Array.of_list l in
  let repl_fun s fmt = 
    let i = int_of_string (matched_group 1 s) in
    print fmt args.(i-1) in
  global_substitute_fmt regexp_arg_pos repl_fun s fmt
 
let get_regexps drv = drv.drv_regexps

(** using drivers *)

let apply_transforms drv = 
(*  apply_clone drv.drv_raw.drv_transforms drv.drv_env drv.drv_clone *)
  apply_env drv.drv_transforms drv.drv_env

let print_prelude drv used fmt =
  let pr_pr s () = fprintf fmt "%s@\n" s in
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
  fprintf fmt "@."

let print_task drv fmt task = match drv.drv_printer with
  | None -> 
      errorm "no printer"
  | Some f -> 
      print_prelude drv (task_used task) fmt;
      f (query_ident drv (task_clone task)) fmt task 

let file_of_task drv input_file theory_name task =
  let filename_regexp = Str.regexp "%\\(.\\)" in
  let replace s = match matched_group 1 s with
    | "%" -> "%"
    | "f" -> input_file
    | "t" -> theory_name
    | "g" -> (task_goal task).pr_name.id_short
    | _ -> errorm "unknown format specifier, use %%f, %%t or %%g"
  in
  let file = match drv.drv_filename with
    | Some f -> f
    | None -> "%f_%t_%g.dump"
  in
  global_substitute filename_regexp replace file

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. test"
End: 
*)
