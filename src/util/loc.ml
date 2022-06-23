(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


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


type position = string * int * int
(*

To reduce memory consumption, a pair (line,col) is stored in a single
   int using

     (line << 12) | col

   This will thus support column numbers up to 4095 and line numbers up
   to 2^18 on 32-bit architecture.

*)

let user_position f bl bc el ec =
  (f, (bl lsl 12) lor bc, (el lsl 12) lor ec)

let get (f,b,e) =
  (f, b lsr 12, b land 0x0FFF, e lsr 12, e land 0x0FFF)

let sexp_of_expanded_position _ = assert false  [@@warning "-32"]
(* default value if the line below does not produce anything, i.e.,
   when ppx_sexp_conv is not installed *)

type expanded_position = string * int * int * int * int
[@@deriving sexp_of]

let sexp_of_position loc =
  let eloc = get loc in sexp_of_expanded_position eloc


let dummy_position = ("",0,0)

let join (f1,b1,e1) (f2,b2,e2) =
  assert (f1 = f2);
  (f1, min b1 b2, max e1 e2)

let extract (b,e) =
  let f = b.pos_fname in
  let bl = b.pos_lnum in
  let bc = b.pos_cnum - b.pos_bol in
  let el = e.pos_lnum in
  let ec = e.pos_cnum - e.pos_bol in
  user_position f bl bc el ec

let compare = Pervasives.compare
let equal = Pervasives.(=)
let hash = Hashtbl.hash

let pp_position_tail fmt bl bc el ec =
  let open Format in
  fprintf fmt "line %d, character" bl;
  if bl=el then
    fprintf fmt "s %d-%d" bc ec
  else
    fprintf fmt " %d to line %d, character %d" bc el ec

let pp_position fmt loc =
  let open Format in
  let (f,bl,bc,el,ec) = get loc in
  if f <> "" then fprintf fmt "\"%s\", " f;
  pp_position_tail fmt bl bc el ec

let pp_position_no_file fmt loc =
  let (_,bl,bc,el,ec) = get loc in
  pp_position_tail fmt bl bc el ec

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
  (fun fmt exn ->
    let open Format in
    match exn with
    | Located (loc,e) ->
        fprintf fmt "@[File %a:@ %a@]" pp_position loc Exn_printer.exn_printer e
    | Message s ->
        pp_print_string fmt s
    | _ ->
        raise exn)

let with_location f lb =
  if Debug.test_flag Debug.stack_trace then f lb else
    try f lb with
    | Located _ as e -> raise e
    | e ->
       let loc = extract (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb) in
       raise (Located (loc, e))
