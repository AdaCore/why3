(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

let backup_file f =
  if Sys.file_exists f then begin
    let fb = f ^ ".bak" in
    if Sys.file_exists fb then Sys.remove fb;
    Sys.rename f fb
  end

let channel_contents_fmt cin fmt =
  let buff = Bytes.create 1024 in
  let n = ref 0 in
  while n := input cin buff 0 1024; !n <> 0 do
    Format.pp_print_string fmt
      (if !n = 1024 then
         Bytes.unsafe_to_string buff
       else
         Bytes.sub_string buff 0 !n)
  done

let channel_contents_buf cin =
  let buf = Buffer.create 1024 in
  let buff = Bytes.create 1024 in
  let n = ref 0 in
  while n := input cin buff 0 1024; !n <> 0 do
    Buffer.add_subbytes buf buff 0 !n
  done;
  buf

let channel_contents cin = Buffer.contents (channel_contents_buf cin)

let rec fold_channel f acc cin =
  try
    fold_channel f (f acc (input_line cin)) cin
  with End_of_file -> acc

let file_contents_fmt f fmt =
  try
    let cin = open_in f in
    channel_contents_fmt cin fmt;
    close_in cin
  with _ ->
    invalid_arg (Printf.sprintf "(cannot open %s)" f)

let file_contents_buf f =
  try
    let cin = open_in f in
    let buf = channel_contents_buf cin in
    close_in cin;
    buf
  with _ ->
    invalid_arg (Printf.sprintf "(cannot open %s)" f)

let file_contents f = Buffer.contents (file_contents_buf f)

let write_file f c =
  let oc = open_out f in
  output_string oc c;
  close_out oc

let open_temp_file ?(debug=false) filesuffix usefile =
  let file,cout = Filename.open_temp_file "why" filesuffix in
  try
    let res = usefile file cout in
    if not debug then Sys.remove file;
    close_out cout;
    res
  with
    | e ->
        if not debug then Sys.remove file;
        close_out cout;
        raise e

let copy_file from to_ =
  let cin = open_in from in
  let cout = open_out to_ in
  let buff = Bytes.create 1024 in
  let n = ref 0 in
  while n := input cin buff 0 1024; !n <> 0 do
    output cout buff 0 !n
  done;
  close_out cout;
  close_in  cin

let rec copy_dir from to_ =
  if not (Sys.file_exists to_) then Unix.mkdir to_ 0o755;
  let files = Sys.readdir from in
  let copy fname =
    let src = Filename.concat from fname in
    let dst = Filename.concat to_ fname in
    if Sys.is_directory src
    then copy_dir src dst
    else copy_file src dst in
  Array.iter copy files

let concat f1 f2 =
  if Filename.is_relative f2 then Filename.concat f1 f2 else f2

type file_path = string list
let empty_path = []
let add_to_path p fn = p @ [fn]
let is_empty_path p = match p with [] -> true | _ -> false
let decompose_path p = p

let rec basename p =
  match p with
  | [] -> raise Not_found
  | [f] -> f
  | _ :: tl -> basename tl

(* deprecated: let string_of_file_path p = String.concat "/" p *)
let print_file_path fmt p = Format.fprintf fmt "%a" (Pp.print_list Pp.slash Pp.string) p


let system_independent_path_of_file f =
  let rec aux acc f =
    let d = Filename.dirname f in
    if d = Filename.current_dir_name then
      (* f is relative to the current dir *)
      let b = Filename.basename f in
      b::acc
    else if f=d then
      (* we are at the root *)
      acc
    else
      let b = Filename.basename f in
      aux (b::acc) d
  in
  aux [] f

(*
let test x = (Filename.dirname x, Filename.basename x)

let _ = test "file"
let _ = test "/file"
let _ = test "/"
let _ = test "f1/f2"
let _ = test "/f1/f2"

let p1 = path_of_file "/bin/bash"

let p1 = path_of_file "../src/f.why"
  *)

let is_regular_dir fn =
  match Unix.lstat fn with
  | s -> s.Unix.st_kind = Unix.S_DIR
  | exception _ -> false

let system_dependent_absolute_path dir p =
  let rec aux dir l =
    match l with
    | [] -> dir
    | ".." :: xs when is_regular_dir dir -> aux (Filename.dirname dir) xs
    | x :: xs -> aux (Filename.concat dir x) xs
  in
  aux dir p

let relativize_filename base f =
  let rec aux abs ab af =
    match ab,af with
      | x::rb, y::rf when x=y -> aux (x::abs) rb rf
      | _ ->
          let rec aux2 abs rel p =
            match p with
              | [] -> rel
              | x::rb ->
                (if x = Filename.current_dir_name then
                   aux2 abs rel rb
                 else if x = Filename.parent_dir_name then
                   match abs with
                   | x::rem -> aux2 rem (x::rel) rb
                   | [] -> aux2 [] rel rb
                 else
                   aux2 (x::abs) (Filename.parent_dir_name::rel) rb)
          in aux2 abs af ab
  in
  aux [] (system_independent_path_of_file base) (system_independent_path_of_file f)



(*
let p1 = relativize_filename "/bin/bash" "src/f.why"

let p1 = relativize_filename "test"
  "/home/cmarche/recherche/why3/src/ide/f.why"
*)

let uniquify file =
  (* Uniquify the filename if it exists on disk *)
  let i =
    try String.rindex file '.'
    with _ -> String.length file
  in
  let name = String.sub file 0 i in
  let ext = String.sub file i (String.length file - i) in
  let i = ref 1 in
  while Sys.file_exists
    (name ^ "_" ^ (string_of_int !i) ^ ext) do
    incr i
  done;
  let file = name ^ "_" ^ (string_of_int !i) ^ ext in
  file
