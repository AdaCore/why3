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
open Ty
open Term
open Theory
open Driver_ast
open Ident

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

type prover_answer = 
    Call_provers.prover_answer =
  | Valid
  | Invalid
  | Unknown of string
  | Failure of string
  | Timeout
  | HighFailure

type theory_driver = {
  thd_prelude : string option;
  thd_tsymbol : unit ;
}


type translation = 
  | Remove
  | Syntax of string
  | Tag of Snm.t

let translation_union t1 t2 =
  match t1, t2 with
    | Remove, _ | _, Remove -> Remove
    | ((Syntax _ as s), _) | (_,(Syntax _ as s)) -> s
    | Tag s1, Tag s2 -> Tag (Snm.union s1 s2)

let print_translation fmt = function
  | Remove -> fprintf fmt "remove" 
  | Syntax s -> fprintf fmt "syntax %s" s
  | Tag s -> fprintf fmt "tag %a" 
      (Pp.print_iter1 Snm.iter Pp.comma Pp.string) s

type printer = driver -> formatter -> context -> unit

and driver = {
  drv_printer     : printer option;
  drv_context     : context;
  drv_prover      : Call_provers.prover;
  drv_prelude     : string option;
  drv_filename    : string option;
  drv_transforms  : Transform.ctxt_list_t;
  drv_rules       : theory_rules list;
  drv_thprelude   : string Hid.t;
  (* the first is the translation only for this ident, the second is also for representant *)
  drv_theory      : (translation * translation) Hid.t;
  drv_with_ctxt   : translation Hid.t;
}

(*
let print_driver fmt driver =
  printf "drv_theory %a@\n" 
    (Pp.print_iter2 Hid.iter Pp.semi Pp.comma print_ident
       (Pp.print_pair print_translation print_translation))
    driver.drv_theory
*)

(** registering transformation *)

let (transforms : (string, unit -> Transform.ctxt_list_t) Hashtbl.t) 
    = Hashtbl.create 17

let register_transform' name transform = Hashtbl.replace transforms name transform
let register_transform name t = register_transform' name 
  (fun () -> Transform.singleton (t ()))
let list_transforms () = Hashtbl.fold (fun k _ acc -> k::acc) transforms []

(** registering printers *)

let (printers : (string, printer) Hashtbl.t) = Hashtbl.create 17

let register_printer name printer = Hashtbl.replace printers name printer

let list_printers () = Hashtbl.fold (fun k _ acc -> k::acc) printers []

(*
let () = 
  Dynlink.allow_only ["Theory";"Term";"Ident";"Transform";"Driver";
                     "Pervasives";"Format";"List";"Sys";"Unix"]
*)

open Dynlink_compat

let load_plugin dir (byte,nat) =
  if Dynlink.is_native_not_defined then 
    errorm 
"Why has been compiled with a version of caml which doesn't allow\
 native dynlink. So Why chooses to refuse plugin.";
  let file = if Dynlink.is_native then nat else byte in
  let file = Filename.concat dir file in
  Dynlink.loadfile_private file

let load_file file =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let f = Driver_lexer.parse_file lb in 
  close_in c;
  f

let rec qualid_to_slist = function
  | [] -> assert false
  | [a] -> a,[]
  | a::l -> let id,l = qualid_to_slist l in (id,a::l)

let string_of_qualid thl idl = 
  let thl = String.concat "." thl in
  let idl = String.concat "." idl in
  thl^"."^idl

let regexp_arg_pos = Str.regexp "%\\([0-9]+\\)"

let check_syntax loc s len = 
  iter_group regexp_arg_pos 
    (fun s ->
       let i = int_of_string (matched_group 1 s) in
       if i=0 then errorm ~loc "invalid indice of argument : the first one is %%1 and not %%0";
       if i>len then errorm ~loc "invalid indice of argument \"%%%i\" this logic has only %i argument" i len) s


let load_rules driver {thr_name = loc,qualid; thr_rules = trl} =
  let id,qfile = qualid_to_slist qualid in
  let th = try
    find_theory driver.drv_context.ctxt_env qfile id 
  with Not_found -> errorm ~loc "theory %s not found" 
    (String.concat "." qualid) in
  let add_htheory cloned id t =
    try
      let t2,t3 = Hid.find driver.drv_theory id in
      let t23 = 
        if cloned then (translation_union t t2),t3
        else t2,(translation_union t t3) in
      Hid.replace driver.drv_theory id t23 
    with Not_found ->
      let t23 = if cloned then (Tag Snm.empty),t else t,(Tag Snm.empty) in
      Hid.add driver.drv_theory id t23 in
  let add = function
    | Rremove (c,(loc,q)) -> 
        begin
          try
            add_htheory c 
              (pr_name (ns_find_prop th.th_export q)) Remove
          with Not_found -> errorm ~loc "Unknown axioms %s" 
            (string_of_qualid qualid q)
        end 
    | Rsyntaxls ((loc,q),s) -> 
        begin
          try
            let ls = ns_find_ls th.th_export q in
            check_syntax loc s (List.length ls.ls_args);
            add_htheory false ls.ls_name (Syntax s)
          with Not_found -> errorm ~loc "Unknown logic %s" 
            (string_of_qualid qualid q)
        end 
    | Rsyntaxty ((loc,q),s) -> 
        begin
          try
            let ts = ns_find_ts th.th_export q in
            check_syntax loc s (List.length ts.ts_args);
            add_htheory false ts.ts_name (Syntax s)
          with Not_found -> errorm ~loc "Unknown type %s" 
            (string_of_qualid qualid q)
        end
    | Rtagls (c,(loc,q),s) ->
        begin
          try
            add_htheory c (ns_find_ls th.th_export q).ls_name 
              (Tag (Snm.singleton s))
          with Not_found -> errorm ~loc "Unknown logic %s" 
            (string_of_qualid qualid q)
        end
    | Rtagty (c,(loc,q),s) ->
        begin
          try
            add_htheory c (ns_find_ts th.th_export q).ts_name 
              (Tag (Snm.singleton s))
          with Not_found -> errorm ~loc "Unknown type %s" 
            (string_of_qualid qualid q)
        end
    | Rtagpr (c,(loc,q),s) ->
        begin
          try
            add_htheory c (pr_name (ns_find_prop th.th_export q))
              (Tag (Snm.singleton s))
          with Not_found -> errorm ~loc "Unknown proposition %s" 
            (string_of_qualid qualid q)
        end
    | Rprelude (loc,s) -> if Hid.mem driver.drv_thprelude th.th_name
      then errorm ~loc "duplicate prelude"
      else Hid.add driver.drv_thprelude th.th_name s in
  List.iter add trl

let load_driver file env =
  let f = load_file file in
  let prelude     = ref None in
  let printer     = ref None in
  let call_stdin  = ref None in
  let call_file   = ref None in
  let filename    = ref None in
  let ltransforms = ref None in
  let regexps     = ref [] in
  let set_or_raise loc r v error =
    if !r <> None then errorm ~loc "duplicate %s" error
    else r := Some v in 
  let add (loc, g) = match g with
    | Printer _ when !printer <> None -> 
	errorm ~loc "duplicate printer"
    | Printer s when Hashtbl.mem printers s ->
	printer := Some (Hashtbl.find printers s)
    | Printer s -> 
	errorm ~loc "unknown printer %s" s 
    | Prelude s -> set_or_raise loc prelude s "prelude"
    | CallStdin s -> set_or_raise loc call_stdin s "callstdin"
    | CallFile s -> set_or_raise loc call_file s "callfile"
    | RegexpValid s -> regexps:=(s,Valid)::!regexps
    | RegexpInvalid s -> regexps:=(s,Invalid)::!regexps
    | RegexpUnknown (s1,s2) -> regexps:=(s1,Unknown s2)::!regexps
    | RegexpFailure (s1,s2) -> regexps:=(s1,Failure s2)::!regexps
    | Filename s -> set_or_raise loc filename s "filename"
    | Transforms s -> set_or_raise loc ltransforms s "transform"
    | Plugin files -> load_plugin (Filename.dirname file) files
  in
  List.iter add f.f_global;
  let regexps = List.map (fun (s,a) -> (Str.regexp s,a)) !regexps in
  let trans r =
    let transformations = match !r with
      | None -> [] | Some l -> l in
    List.fold_left 
      (fun acc (loc,s) -> 
         let t = 
           try (Hashtbl.find transforms s) () 
           with Not_found -> errorm ~loc "unknown transformation %s" s in
         Transform.compose' acc t
      )
      Transform.identity' transformations in
    let transforms = trans ltransforms in
  { drv_printer     = !printer;
    drv_context     = Context.init_context env;
    drv_prover      = {Call_provers.pr_call_stdin = !call_stdin;
                       pr_call_file               = !call_file;
                       pr_regexps                 = regexps};
    drv_prelude     = !prelude;
    drv_filename    = !filename;
    drv_transforms  = transforms;
    drv_rules       = f.f_rules;
    drv_thprelude   = Hid.create 1;
    drv_theory      = Hid.create 1;
    drv_with_ctxt   = Hid.create 1;
  }

(** querying drivers *)

let query_ident drv id =
  try
    Hid.find drv.drv_with_ctxt id
  with Not_found ->
    let r = try
      Mid.find id drv.drv_context.ctxt_cloned
    with Not_found -> Sid.empty in
    let tr = try fst (Hid.find drv.drv_theory id) 
    with Not_found -> Tag Snm.empty in 
    let tr = Sid.fold 
      (fun id acc -> try translation_union acc 
         (snd (Hid.find drv.drv_theory id)) 
       with Not_found -> acc) r tr in
    Hid.add drv.drv_with_ctxt id tr;
    tr

let syntax_arguments s print fmt l =
  let args = Array.of_list l in
  let repl_fun s fmt = 
    let i = int_of_string (matched_group 1 s) in
    print fmt args.(i-1) in
  global_substitute_fmt regexp_arg_pos repl_fun s fmt
 
(** using drivers *)

let apply_transforms drv = Transform.apply drv.drv_transforms

let print_context drv fmt ctxt = match drv.drv_printer with
  | None -> errorm "no printer"
  | Some f -> let drv = {drv with drv_context = ctxt;
                   drv_thprelude  = Hid.create 17;
                   drv_theory     = Hid.create 17;
                   drv_with_ctxt  = Hid.create 17} in
    List.iter (load_rules drv) drv.drv_rules;
    f drv fmt ctxt 

let regexp_filename = Str.regexp "%\\([a-z]\\)"

let filename_of_goal drv ident_printer filename theory_name ctxt =
  match drv.drv_filename with
    | None -> errorm "no filename syntax given"
    | Some f -> 
        let pr_name = pr_name (Transform.goal_of_ctxt ctxt) in
        let repl_fun s = 
          let i = matched_group 1 s in
          match i with
            | "f" -> filename
            | "t" -> theory_name
            | "s" -> id_unique ident_printer pr_name
            | _ -> errorm "substitution variable are only %%f %%t and %%s" in
        global_substitute regexp_filename repl_fun f

let file_printer = 
  create_ident_printer ~sanitizer:(sanitizer char_to_alnumus char_to_alnumus)
    []

let call_prover_on_file ?debug ?timeout drv filename =
  Call_provers.on_file drv.drv_prover filename 
let call_prover_on_buffer ?debug ?timeout ?filename drv ib = 
  Call_provers.on_buffer ?debug ?timeout ?filename drv.drv_prover ib 


let call_prover ?debug ?timeout drv ctx =
  let filename = 
    match drv.drv_filename with
      | None -> None
      | Some _ -> Some (filename_of_goal drv file_printer "" "" ctx) in
  let buffer = Buffer.create 128 in
  bprintf buffer "%a@?" (print_context drv) ctx;
  call_prover_on_buffer ?debug ?timeout ?filename drv buffer



(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. test"
End: 
*)
