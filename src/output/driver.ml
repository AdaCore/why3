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
  | Valid
  | Invalid
  | Unknown of string
  | Failure of string
  | Timeout

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
  drv_printer    : printer option;
  drv_context    : context;
  drv_call_stdin : string option;
  drv_call_file  : string option;
  drv_regexps    : (string * prover_answer) list;
  drv_prelude    : string option;
  drv_thprelude  : string Hid.t;
  (* the first is the translation only for this ident, the second is also for representant *)
  drv_theory     : (translation * translation) Hid.t;
  drv_with_ctxt  : translation Hid.t;
  drv_env : Typing.env;
}


let print_driver fmt driver =
  printf "drv_theory %a@\n" 
    (Pp.print_iter2 Hid.iter Pp.semi Pp.comma print_ident
       (Pp.print_pair print_translation print_translation))
    driver.drv_theory


(** registering printers *)

let (printers : (string, printer) Hashtbl.t) = Hashtbl.create 17

let register_printer name printer = Hashtbl.replace printers name printer

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

let load_rules env driver {thr_name = loc,qualid; thr_rules = trl} =
  let id,qfile = qualid_to_slist qualid in
  let th = Typing.find_theory env qfile id in
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
  let rec find_lident ns = function
    | [] -> assert false
    | [a] -> (Mnm.find a ns.ns_ls).ls_name
    | a::l -> find_lident (Mnm.find a ns.ns_ns) l in
  let rec find_tyident ns = function
    | [] -> assert false
    | [a] -> (Mnm.find a ns.ns_ts).ts_name
    | a::l -> find_tyident (Mnm.find a ns.ns_ns) l in
  let rec find_prident ns = function
    | [] -> assert false
    | [a] -> (Mnm.find a ns.ns_pr).pr_name
    | a::l -> find_prident (Mnm.find a ns.ns_ns) l in
  let add = function
    | Rremove (c,(loc,q)) -> 
        begin
          try
            add_htheory c (find_prident th.th_export q) Remove
          with Not_found -> errorm ~loc "Unknown axioms %s" 
            (string_of_qualid qualid q)
        end 
    | Rsyntax ((loc,q),s) -> 
        begin
          try
            add_htheory false (find_lident th.th_export q) (Syntax s)
          with Not_found -> errorm ~loc "Unknown logic %s" 
            (string_of_qualid qualid q)
        end 
    | Rtag (c,(loc,q),s) ->
        begin
          try
            add_htheory c (find_lident th.th_export q) (Tag (Snm.singleton s))
          with Not_found -> errorm ~loc "Unknown logic %s" 
            (string_of_qualid qualid q)
        end
    | Rprelude (loc,s) -> if Hid.mem driver.drv_thprelude th.th_name
      then errorm ~loc "duplicate prelude"
      else Hid.add driver.drv_thprelude th.th_name s in
  List.iter add trl

let load_driver file env =
  let f = load_file file in
  let prelude = ref None in
  let printer = ref None in
  let call_stdin = ref None in
  let call_file = ref None in
  let regexps = ref [] in
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
  in
  List.iter add f.f_global;
  let driver =   { drv_printer    = !printer;
                   drv_context    = Context.init_context;
                   drv_call_stdin = !call_stdin;
                   drv_call_file  = !call_file;
                   drv_regexps    = !regexps;
                   drv_prelude    = !prelude;
                   drv_thprelude  = Hid.create 16;
                   drv_theory     = Hid.create 16;
                   drv_with_ctxt  = Hid.create 16;
                   drv_env        = env;
  } in
  List.iter (load_rules env driver) f.f_rules;
  driver

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
(** using drivers *)

let print_context drv fmt ctxt = match drv.drv_printer with
  | None -> errorm "no printer"
  | Some f -> f {drv with drv_context = ctxt} fmt ctxt 

let call_prover drv ctx = assert false (*TODO*)
let call_prover_on_file drv filename = assert false (*TODO*)
let call_prover_on_channel drv filename ic = assert false (*TODO*)

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. test"
End: 
*)
