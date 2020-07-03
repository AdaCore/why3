(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*
type lexing_loc = Lexing.position * Lexing.position
*)

open Mysexplib.Std [@@warning "-33"]
open Lexing

let current_offset = ref 0
let reloc p = { p with pos_cnum = p.pos_cnum + !current_offset }

let set_file file lb =
  lb.Lexing.lex_curr_p <-
    { lb.Lexing.lex_curr_p with Lexing.pos_fname = file }

let transfer_loc lb_from lb_to =
  lb_to.lex_start_p <- lb_from.lex_start_p;
  lb_to.lex_curr_p <- lb_from.lex_curr_p


(*s Error locations. *)

(* dead code
let finally ff f x =
  let y = try f x with e -> ff (); raise e in ff (); y
*)

open Format

(*s Line number *)

(*
let report_line fmt l = fprintf fmt "%s:%d:" l.pos_fname l.pos_lnum
*)

type position = string * int * int * int
[@@deriving sexp_of]

let user_position fname lnum cnum1 cnum2 = (fname,lnum,cnum1,cnum2)

let get loc = loc

let dummy_position = ("",0,0,0)

let join (f1,l1,b1,e1) (f2,l2,_b2,e2) =
  assert (f1 = f2);
  if l1 = l2 then (f1,l1,b1,e2)
  else
    (* There is no way to get an always right join in this case *)
    (f1, l1, b1, e1 + e2)

let extract (b,e) =
  let f = b.pos_fname in
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol in
  let lc = e.pos_cnum - b.pos_bol in
  (f,l,fc,lc)

let compare = Pervasives.compare
let equal = Pervasives.(=)
let hash = Hashtbl.hash

let gen_report_position fmt (f,l,b,e) =
  fprintf fmt "File \"%s\", line %d, characters %d-%d" f l b e

let report_position fmt = fprintf fmt "%a:@\n" gen_report_position

(* located exceptions *)

exception Located of position * exn

let error ?loc e = match loc with
  | Some loc -> raise (Located (loc, e))
  | None -> raise e

let try1 ?loc f x =
  if Debug.test_flag Debug.stack_trace then f x else
  try f x with Located _ as e -> raise e | e -> error ?loc e

let try2 ?loc f x y =
  if Debug.test_flag Debug.stack_trace then f x y else
  try f x y with Located _ as e -> raise e | e -> error ?loc e

let try3 ?loc f x y z =
  if Debug.test_flag Debug.stack_trace then f x y z else
  try f x y z with Located _ as e -> raise e | e -> error ?loc e

let try4 ?loc f x y z t =
  if Debug.test_flag Debug.stack_trace then f x y z t else
  try f x y z t with Located _ as e -> raise e | e -> error ?loc e

let try5 ?loc f x y z t u =
  if Debug.test_flag Debug.stack_trace then f x y z t u else
  try f x y z t u with Located _ as e -> raise e | e -> error ?loc e

let try6 ?loc f x y z t u v =
  if Debug.test_flag Debug.stack_trace then f x y z t u v else
  try f x y z t u v with Located _ as e -> raise e | e -> error ?loc e

let try7 ?loc f x y z t u v w =
  if Debug.test_flag Debug.stack_trace then f x y z t u v w else
  try f x y z t u v w with Located _ as e -> raise e | e -> error ?loc e

(* located messages *)

exception Message of string

let errorm ?loc f =
  Format.kasprintf (fun s -> error ?loc (Message s)) ("@[" ^^ f ^^ "@]")

let () = Exn_printer.register
  (fun fmt exn -> match exn with
    | Located (loc,e) ->
        fprintf fmt "%a%a" report_position loc Exn_printer.exn_printer e
    | Message s ->
        fprintf fmt "%s" s
    | _ ->
        raise exn)

let loc lb = extract (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb)

let with_location f lb =
  if Debug.test_flag Debug.stack_trace then f lb else
    try f lb with
    | Located _ as e -> raise e
    | e -> raise (Located (loc lb, e))

let get_line_lengths f =
  let lengths = ref [] in
  let ch = open_in f in
  ( try
      while true do
        let line = input_line ch in
        lengths := String.length line :: !lengths;
      done
    with End_of_file -> () );
  close_in ch;
  Array.of_list (List.rev !lengths)

let get_line_lengths =
  let module Str = struct include String let hash = Hashtbl.hash end in
  let module Hstr = Hashtbl.Make (Str) in
  let cache = Hstr.create 5 in
  fun f ->
    try Hstr.find cache f
    with Not_found ->
      let l = get_line_lengths f in
      Hstr.add cache f l;
      l

let get_multiline (f, bl, bc, ec) =
  if Sys.file_exists f then
    let ls = get_line_lengths f in
    let el, ec = ref bl, ref ec in
    assert (!el > 0); (* lines are 1-indexed *)
    while !el < Array.length ls && !ec > ls.(!el-1) do
      ec := !ec - ls.(!el-1) - 1; (* newlines are counted in multi-line locs *)
      incr el
    done;
    f, (bl, bc), (!el, !ec)
  else
    f, (bl, bc), (bl, ec)
