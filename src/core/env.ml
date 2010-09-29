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

open Ident
open Theory

(** Environment *)

type env = {
  env_retrieve : retrieve_theory;
  env_memo     : (string list, theory Mnm.t) Hashtbl.t;
  env_tag      : Hashweak.tag;
}

and retrieve_theory = env -> string list -> theory Mnm.t

let create_env = let c = ref (-1) in fun retrieve ->
  let env = {
    env_retrieve = retrieve;
    env_memo     = Hashtbl.create 17;
    env_tag      = (incr c; Hashweak.create_tag !c) }
  in
  let add th m = Mnm.add th.th_name.id_string th m in
  let m = Mnm.empty in
  let m = add builtin_theory m in
  let m = add highord_theory m in
  let m = add (tuple_theory 0) m in
  let m = add (tuple_theory 1) m in
  let m = add (tuple_theory 2) m in
  Hashtbl.add env.env_memo [] m;
  env

exception TheoryNotFound of string list * string

let find_theory env sl s =
  try
    let m =
      try
	Hashtbl.find env.env_memo sl
      with Not_found ->
	Hashtbl.add env.env_memo sl Mnm.empty;
	let m = env.env_retrieve env sl in
	Hashtbl.replace env.env_memo sl m;
	m
    in
    Mnm.find s m
  with Not_found ->
    raise (TheoryNotFound (sl, s))

let env_tag env = env.env_tag


(** Parsers *)

type read_channel = env -> string -> in_channel -> theory Mnm.t

let read_channel_table = Hashtbl.create 17 (* parser name -> read_channel *)
let suffixes_table     = Hashtbl.create 17 (* suffix -> parser name *)

let register_format name suffixes rc =
  Hashtbl.add read_channel_table name rc;
  List.iter (fun s -> Hashtbl.add suffixes_table ("." ^ s) name) suffixes

exception NoFormat
exception UnknownExtension of string 
exception UnknownFormat of string (* parser name *)

let parser_for_file ?format file = match format with
  | None ->
      begin try
	let ext =
	  let s = Filename.chop_extension file in
	  let n = String.length s in
	  String.sub file n (String.length file - n)
	in
        try
	  Hashtbl.find suffixes_table ext
        with Not_found -> raise (UnknownExtension ext)
      with 
        | Invalid_argument _ -> raise NoFormat
      end
  | Some n ->
      n

let find_parser table n =
  try Hashtbl.find table n
  with Not_found -> raise (UnknownFormat n)

let read_channel ?format env file ic =
  let n = parser_for_file ?format file in
  let rc = find_parser read_channel_table n in
  rc env file ic

let read_file ?format env file =
  let cin = open_in file in
  let m = read_channel ?format env file cin in
  close_in cin;
  m

let list_formats () =
  let h = Hashtbl.create 17 in
  let add s p =
    let l = try Hashtbl.find h p with Not_found -> [] in
    Hashtbl.replace h p (s :: l)
  in
  Hashtbl.iter add suffixes_table;
  Hashtbl.fold (fun p l acc -> (p, l) :: acc) h []

(* Exception reporting *)

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | TheoryNotFound (sl, s) ->
      Format.fprintf fmt "Theory not found: %a.%s"
        (Pp.print_list Pp.dot Format.pp_print_string) sl s
  | UnknownFormat s ->
      Format.fprintf fmt "Unknown input format: %s" s
  | UnknownExtension s ->
      Format.fprintf fmt "Unknown file extension: %s" s
  | NoFormat ->
      Format.fprintf fmt "No input format given"
  | _ -> raise exn
  end

