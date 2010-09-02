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

  let get_home_dir () =
    try Sys.getenv "HOME"
    with Not_found -> 
      (* try windows env var *)
      try Sys.getenv "USERPROFILE"
      with Not_found -> ""

type rc_value =
  | RCint of int
  | RCbool of bool
  | RCfloat of float
  | RCstring of string
  | RCident of string

let int = function
  | RCint n -> n
  | _ -> failwith "Rc.int"

let bool = function
  | RCbool b -> b
  | _ -> failwith "Rc.bool"

let string = function
  | RCident s | RCstring s -> s
  | _ -> failwith "Rc.string"

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
    List.rev !current
      
  open Format
  open Pp

  let print_value fmt = function
    | RCint n -> fprintf fmt "%d" n
    | RCbool b -> fprintf fmt "%b" b
    | RCfloat f -> fprintf fmt "%f" f
    | RCstring s -> fprintf fmt "\"%s\"" s
    | RCident i -> fprintf fmt "%s" i

  let record fmt (keys,fl) =
    fprintf fmt "[%a]@\n" (print_list space pp_print_string) keys;
    List.iter
      (fun (f,v) -> fprintf fmt "%s = %a@\n" f print_value v)
      fl;
    fprintf fmt "@."

  let to_file f l =
    let c = 
      try open_out f 
      with Sys_error _ -> raise Not_found
    in
    let fmt = formatter_of_out_channel c in
    List.iter (record fmt) l;
    close_out c
      
}
