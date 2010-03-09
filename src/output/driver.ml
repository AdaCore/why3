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
open Theory
open Driver_ast

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

type printer = driver -> formatter -> context -> unit

and driver = {
  drv_printer    : printer option;
  drv_context    : context;
  drv_call_stdin : string option;
  drv_call_file  : string option;
  drv_regexps    : (string * prover_answer) list;
  drv_prelude    : string option;
  drv_rules      : (string list, theory_rules) Hashtbl.t;
  drv_theory     : (string list, theory_driver) Hashtbl.t;
}

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

let load_driver file env =
  let f = load_file file in
  let printer = ref (None : printer option) in
  let add (loc, g) = match g with
    | Printer _ when !printer <> None -> 
	errorm ~loc "duplicate printer"
    | Printer s when Hashtbl.mem printers s ->
	printer := Some (Hashtbl.find printers s)
    | Printer s -> 
	errorm ~loc "unknown printer %s" s 
    | _ -> 
	() (* TODO *)
  in
  List.iter add f.f_global;
  { drv_printer    = !printer;
    drv_context    = Context.init_context;
    drv_call_stdin = None;
    drv_call_file  = None;
    drv_regexps    = [];
    drv_prelude    = None;
    drv_rules      = Hashtbl.create 17;
    drv_theory     = Hashtbl.create 17;
  }

(** querying drivers *)

type translation = 
  | Remove
  | Syntax of string
  | Tag of string list

let query_ident dr id =
  assert false (*TODO*)

(** using drivers *)

let print_context drv = match drv.drv_printer with
  | None -> errorm "no printer"
  | Some f -> f drv

let call_prover drv ctx = assert false (*TODO*)
let call_prover_on_file drv filename = assert false (*TODO*)
let call_prover_on_channel drv filename ic = assert false (*TODO*)

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. test"
End: 
*)
