(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Theory

(** Library environment *)

type fformat = string (* format name *)
type filename = string (* file name *)
type extension = string (* file extension *)
type pathname = string list (* library path *)

exception KnownFormat of fformat
exception UnknownFormat of fformat
exception UnknownExtension of extension
exception UnspecifiedFormat

exception LibFileNotFound of pathname
exception TheoryNotFound of pathname * string
exception AmbiguousPath of filename * filename

type env = {
  env_path : Sstr.t;
  env_tag  : Weakhtbl.tag;
}

let env_tag env = env.env_tag

module Wenv = Weakhtbl.Make(struct type t = env let tag = env_tag end)

(** Environment construction and utilisation *)

let create_env = let c = ref (-1) in fun lp -> {
  env_path = List.fold_right Sstr.add lp Sstr.empty;
  env_tag  = (incr c; Weakhtbl.create_tag !c)
}

let get_loadpath env = Sstr.elements env.env_path

let read_format_table = Hstr.create 17 (* format name -> read_format *)
let extensions_table  = Hstr.create 17 (* suffix -> format name *)

let lookup_format name =
  try Hstr.find read_format_table name
  with Not_found -> raise (UnknownFormat name)

let list_formats () =
  let add n (_,_,l,desc) acc = (n,l,desc)::acc in
  Hstr.fold add read_format_table []

let get_extension file =
  let s = try Filename.chop_extension file
    with Invalid_argument _ -> raise UnspecifiedFormat in
  let n = String.length s + 1 in
  String.sub file n (String.length file - n)

let get_format file =
  let ext = get_extension file in
  try Hstr.find extensions_table ext
  with Not_found -> raise (UnknownExtension ext)

let read_channel ?format env file ic =
  let name = match format with
    | Some name -> name
    | None -> get_format file in
  let rc,_,_,_ = lookup_format name in
  rc env file ic

let read_file ?format env file =
  let ic = open_in file in
  try
    let mth = read_channel ?format env file ic in
    close_in ic;
    mth
  with e -> close_in ic; raise e

let read_theory ~format env path th =
  let _,rl,_,_ = lookup_format format in
  rl env path th

let find_theory = read_theory ~format:"why"

(** Navigation in the library *)

exception InvalidQualifier of string

let check_qualifier s =
  if (s = Filename.parent_dir_name ||
      s = Filename.current_dir_name ||
      Filename.basename s <> s)
  then raise (InvalidQualifier s)

let locate_lib_file env path exts =
  if path = [] || path = ["why3"] then raise (LibFileNotFound path);
  List.iter check_qualifier path;
  let file = List.fold_left Filename.concat "" path in
  let add_ext ext = file ^ "." ^ ext in
  let fl = if exts = [] then [file] else List.map add_ext exts in
  let add_dir dir = List.map (Filename.concat dir) fl in
  let fl = List.concat (List.map add_dir (get_loadpath env)) in
  match List.filter Sys.file_exists fl with
  | [] -> raise (LibFileNotFound path)
  | [file] -> file
  | file1 :: file2 :: _ -> raise (AmbiguousPath (file1, file2))

(** Input formats *)

exception CircularDependency of pathname

type 'a contents = 'a * theory Mstr.t

module Hpath = Hashtbl.Make(struct
  type t = pathname
  let hash = Hashtbl.hash
  let equal = (=)
end)

type 'a library = {
  lib_env  : env;
  lib_read : 'a read_format;
  lib_exts : extension list;
  lib_memo : ('a contents option) Hpath.t;
}

and 'a read_format =
  'a library -> pathname -> filename -> in_channel -> 'a contents

let mk_library read exts env = {
  lib_env  = env;
  lib_read = read;
  lib_exts = exts;
  lib_memo = Hpath.create 17;
}

let env_of_library lib = lib.lib_env

let read_lib_file lib path =
  let file = locate_lib_file lib.lib_env path lib.lib_exts in
  let ic = open_in file in
  try
    Hpath.replace lib.lib_memo path None;
    let res = lib.lib_read lib path file ic in
    Hpath.replace lib.lib_memo path (Some res);
    close_in ic;
    res
  with e ->
    Hpath.remove lib.lib_memo path;
    close_in ic;
    raise e

let read_lib_file lib path =
  try match Hpath.find lib.lib_memo path with
    | Some res -> res
    | None -> raise (CircularDependency path)
  with Not_found -> read_lib_file lib path

let get_builtin s =
  if s = builtin_theory.th_name.id_string then builtin_theory else
  if s = bool_theory.th_name.id_string then bool_theory else
  if s = unit_theory.th_name.id_string then unit_theory else
  if s = highord_theory.th_name.id_string then highord_theory else
  match tuple_theory_name s with
  | Some n -> tuple_theory n
  | None -> raise (TheoryNotFound ([],s))

let read_lib_theory lib path th =
  if path = [] || path = ["why3"] then get_builtin th else
  let _,mth = read_lib_file lib path in
  try Mstr.find th mth with Not_found ->
  raise (TheoryNotFound (path,th))

let register_format ~(desc:Pp.formatted) name exts read =
  if Hstr.mem read_format_table name then raise (KnownFormat name);
  let getlib = Wenv.memoize 5 (mk_library read exts) in
  let rc env file ic = snd (read (getlib env) [] file ic) in
  let rl env path th = read_lib_theory (getlib env) path th in
  Hstr.add read_format_table name (rc,rl,exts,desc);
  List.iter (fun s -> Hstr.replace extensions_table s name) exts;
  getlib

let locate_lib_file env format path =
  let _,_,exts,_ = lookup_format format in
  locate_lib_file env path exts

(* Exception reporting *)

let print_path fmt sl =
  Pp.print_list (Pp.constant_string ".") Format.pp_print_string fmt sl

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | CircularDependency sl ->
      Format.fprintf fmt "Circular dependency in %a" print_path sl
  | LibFileNotFound sl ->
      Format.fprintf fmt "Library file not found: %a" print_path sl
  | TheoryNotFound (sl,s) ->
      Format.fprintf fmt "Theory not found: %a" print_path (sl @ [s])
  | KnownFormat s ->
      Format.fprintf fmt "Format %s is already registered" s
  | UnknownFormat s ->
      Format.fprintf fmt "Unknown input format: %s" s
  | UnknownExtension s ->
      Format.fprintf fmt "Unknown file extension: `%s'" s
  | UnspecifiedFormat ->
      Format.fprintf fmt "Format not specified"
  | AmbiguousPath (f1,f2) ->
      Format.fprintf fmt "Ambiguous path:@ both `%s'@ and `%s'@ match" f1 f2
  | InvalidQualifier s ->
      Format.fprintf fmt "Invalid qualifier `%s'" s
  | _ -> raise exn
  end

