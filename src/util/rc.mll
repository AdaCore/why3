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

{

  open Lexing
  open Util

  let get_home_dir () =
    try Sys.getenv "HOME"
    with Not_found -> 
      (* try windows env var *)
      try Sys.getenv "USERPROFILE"
      with Not_found -> ""

exception Bad_value_type of string * string * string
(** key * expected * found *)
exception Key_not_found of string
(** key *)
exception Multiple_value of string
(** key *)
exception Multiple_section of string
exception Section_b_family of string
exception Family_two_many_args of string
exception Not_exhaustive of  string
exception Yet_defined_section of string
exception Yet_defined_key of string

type rc_value =
  | RCint of int
  | RCbool of bool
  | RCfloat of float
  | RCstring of string
  | RCident of string

type section = rc_value list Mstr.t
type family  = (string * section) list
type ofamily  = (string option * section) list
type t = ofamily Mstr.t

let empty = Mstr.empty
let empty_section = Mstr.empty

let make_t tl =
  let add_key acc (key,value) =
    let l = try Mstr.find key acc with Not_found -> [] in
    Mstr.add key (value::l) acc in
  let add_section t (args,sectionl) =
    let sname,arg = match args with
      | []    -> assert false
      | [sname]    -> sname,None
      | [sname;arg] -> sname,Some arg
      | sname::_     -> raise (Family_two_many_args sname) in
    let m = List.fold_left add_key empty_section sectionl in
    let m = Mstr.map List.rev m in
    let l = try Mstr.find sname t with Not_found -> [] in
    Mstr.add sname ((arg,m)::l) t in
  List.fold_left add_section empty tl

let get_section t sname =
  try
    let l = Mstr.find sname t in
    match l with
      | [None,v] -> Some v
      | [Some _,_] -> raise (Section_b_family sname)
      | _ -> raise (Multiple_section sname)
  with Not_found -> None

let get_family t sname =
  try
    let l = Mstr.find sname t in
    let get (arg,section) =
      (match arg with None -> raise (Section_b_family sname) | Some v -> v,
        section) in
    List.map get l
  with Not_found -> []


let set_section t sname section =
  Mstr.add sname [None,section] t

let set_family t sname sections =
  if sections = [] then Mstr.remove sname t else
    let set (arg,section) = (Some arg,section) in
    Mstr.add sname (List.map set sections) t

let get_value read ?default section key =
  try
    let l = Mstr.find key section in
    match l with
      | [v] -> read v
      | _ -> raise (Multiple_value key)
  with Not_found ->
    match default with
      | None -> raise (Key_not_found key)
      | Some v -> v

let get_valuel read ?default section key =
  try
    let l = Mstr.find key section in
    List.map read l
  with Not_found ->
    match default with
      | None -> raise (Key_not_found key)
      | Some v -> v

let set_value write section key value =
  Mstr.add key [write value] section

let set_valuel write section key valuel =
  if valuel = [] then Mstr.remove key section else
    Mstr.add key (List.map write valuel) section

let rint = function
  | RCint n -> n
  | _ -> failwith "Rc.int"

let wint i = RCint i

let rbool = function
  | RCbool b -> b
  | _ -> failwith "Rc.bool"

let wbool b = RCbool b

let rstring = function
  | RCident s | RCstring s -> s
  | _ -> failwith "Rc.string"

let wstring s = RCstring s

let get_int = get_value rint
let get_intl = get_valuel rint
let set_int = set_value wint
let set_intl = set_valuel wint

let get_bool = get_value rbool
let get_booll = get_valuel rbool
let set_bool = set_value wbool
let set_booll = set_valuel wbool

let get_string = get_value rstring
let get_stringl = get_valuel rstring
let set_string = set_value wstring
let set_stringl = set_valuel wstring

let check_exhaustive section keyl =
  let test k _ = if Sstr.mem k keyl then ()
    else raise (Not_exhaustive k) in
  Mstr.iter test section

let buf = Buffer.create 17

let current_rec = ref []
let current_list = ref []
let current = ref []

let push_field key value =
  current_list := (key,value) :: !current_list

let push_record () =
  if !current_list <> [] then
    current := (!current_rec,List.rev !current_list) :: !current;
  current_rec := [];
  current_list := []

}

let space = [' ' '\t' '\r' '\n']+
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let ident = (letter | '_') (letter | digit | '_' | '-' | '(' | ')') * 
let sign = '-' | '+' 
let integer = sign? digit+
let mantissa = ['e''E'] sign? digit+
let real = sign? digit* '.' digit* mantissa?
let escape = ['\\''"''n''t''r']

rule record = parse
  | space 
      { record lexbuf }
  | '[' (ident as key) space*
      { header [key] lexbuf }
  | eof 
      { push_record () }
  | (ident as key) space* '=' space* 
      { value key lexbuf }
  | _ as c
      { failwith ("Rc: invalid keyval pair starting with " ^ String.make 1 c) }

and header keylist = parse
  | (ident as key) space*
      { header (key::keylist) lexbuf }
  | ']'
      { push_record ();
        current_rec := List.rev keylist;
        record lexbuf }
  | eof
      { failwith "Rc: unterminated header" }
  | _ as c
      { failwith ("Rc: invalid header starting with " ^ String.make 1 c) }

and value key = parse
  | integer as i
      { push_field key (RCint (int_of_string i));
        record lexbuf }
  | real as r
      { push_field key (RCfloat (float_of_string r));
        record lexbuf }
  | '"' 
      { Buffer.clear buf;
	string_val key lexbuf } 
  | "true"
      { push_field key (RCbool true);
        record lexbuf }
  | "false"
      { push_field key (RCbool false);
        record lexbuf }
  | ident as id
      { push_field key (RCident (*kind_of_ident*) id);
        record lexbuf }
  | eof
      { failwith "Rc: unterminated keyval pair" }
  | _ as c
      { failwith ("Rc: invalid value starting with " ^ String.make 1 c) }

and string_val key = parse 
  | '"' 
      { push_field key (RCstring (Buffer.contents buf));
	record lexbuf
      }
  | [^ '\\' '"'] as c
      { Buffer.add_char buf c;
        string_val key lexbuf }
  | '\\' (['\\''\"'] as c)   
      { Buffer.add_char buf c;
        string_val key lexbuf }
  | '\\' 'n'
      { Buffer.add_char buf '\n';
        string_val key lexbuf }
  | '\\' (_ as c)
      { Buffer.add_char buf '\\';
        Buffer.add_char buf c;
        string_val key lexbuf }
  | eof
      { failwith "Rc: unterminated string" }


{

  let from_file f =
      let c = 
	try open_in f 
	with Sys_error _ -> raise Not_found
(*
	  Format.eprintf "Cannot open file %s@." f;
	  exit 1
*)
      in
      current := [];
      let lb = from_channel c in
      record lb;
      close_in c;
      make_t !current

open Format

let to_file s t =
  let print_value fmt = function
      | RCint i -> pp_print_int fmt i
      | RCbool b -> pp_print_bool fmt b
      | RCfloat f -> pp_print_float fmt f
      | RCstring s -> fprintf fmt "%S" s
      | RCident s -> pp_print_string fmt s in
  let print_kv k fmt v = fprintf fmt "%s = %a" k print_value v in
  let print_kvl fmt k vl = Pp.print_list Pp.newline (print_kv k) fmt vl in
  let print_section sname fmt (h,l) =
    fprintf fmt "[%s %a]@\n%a"
      sname (Pp.print_option Pp.string) h
      (Pp.print_iter22 Mstr.iter Pp.newline2 print_kvl) l in
  let print_sectionl fmt sname l =
    Pp.print_list Pp.newline (print_section sname) fmt l in
  let print_t fmt t =
    Pp.print_iter22 Mstr.iter Pp.newline2 print_sectionl fmt t in
  let out = open_out s in
  let fmt = formatter_of_out_channel out in
  print_t fmt t;
  pp_print_flush fmt ();
  close_out out



}
