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

(*

To reduce memory consumption, a pair (line,col) is stored in a single
   int using

     (line << bits) | col

  On 32-bits architecture, bits is 12. This will thus support column
   numbers up to 4095 and line numbers up to 2^19

  On 64-bits architecture, bits is 16. This will thus support column
   numbers up to 65535 and line numbers up to 2^47

  The file names are also hashed to ensure an optimal sharing
*)

module FileTags = struct

  open Wstdlib

  let tag_counter = ref 0

  let file_tags = Hstr.create 7
  let tag_to_file = Hint.create 7

  let get_file_tag file =
    try
      Hstr.find file_tags file
    with Not_found ->
      let n = !tag_counter in
      Hstr.add file_tags file n;
      Hint.add tag_to_file n file;
      incr tag_counter;
      n

  let tag_to_file tag =
    Hint.find tag_to_file tag

end


type position = {
    pos_file_tag : int;
    pos_start : int (* compressed line/col *);
    pos_end : int (* compressed line/col *);
  }

let bits_col =
  if Sys.word_size = 32 then 12 else
  if Sys.word_size = 64 then 16 else
    failwith "word size should be 32 or 64"

let mask_col = (1 lsl bits_col) - 1

let max_line = (1 lsl (Sys.word_size - bits_col - 1)) - 1

let get p =
  let f = FileTags.tag_to_file p.pos_file_tag in
  let b = p.pos_start in
  let e = p.pos_end in
  (f, b lsr bits_col, b land mask_col, e lsr bits_col, e land mask_col)

let sexp_of_expanded_position _ = assert false  [@@warning "-32"]
(* default value if the line below does not produce anything, i.e.,
   when ppx_sexp_conv is not installed *)

type expanded_position = string * int * int * int * int  [@@warning "-34"]
[@@deriving sexp_of]

let sexp_of_position loc =
  let eloc = get loc in sexp_of_expanded_position eloc
                          [@@warning "-32"]

let dummy_position =
  let tag = FileTags.get_file_tag "" in
  { pos_file_tag = tag; pos_start = 0; pos_end = 0 }

let join p1 p2 =
  assert (p1.pos_file_tag = p2.pos_file_tag);
  { p1 with
    pos_start = min p1.pos_start p2.pos_start;
    pos_end = max p1.pos_end p2.pos_end }

let compare = Stdlib.compare
let equal = Stdlib.(=)
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

(* warnings *)

let default_hook ?loc s =
  let open Format in
  match loc with
  | None -> eprintf "Warning: %s@." s
  | Some l -> eprintf "Warning, file %a: %s@." pp_position l s

let warning_hook = ref default_hook
let set_warning_hook = (:=) warning_hook

let warning ?loc p =
  let open Format in
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  pp_set_margin fmt 1000000000;
  pp_open_box fmt 0;
  let handle fmt =
    pp_print_flush fmt (); !warning_hook ?loc (Buffer.contents b) in
  kfprintf handle fmt p

(* user positions *)

let warning_emitted = ref false

let user_position f bl bc el ec =
  if bl < 0 || bl > max_line then
    failwith ("Loc.user_position: start line number `" ^
                string_of_int bl ^ "` out of bounds");
  if bc < 0 then
    failwith ("Loc.user_position: start char number `" ^
                string_of_int bc ^ "` out of bounds");
  if bc > mask_col && not !warning_emitted then
    begin
      warning "Loc.user_position: start char number `%d` overflows on next line" bc;
      warning_emitted := true;
    end;
  if el < 0 || el > max_line then
    failwith ("Loc.user_position: end line number `" ^
                string_of_int el ^ "` out of bounds");
  if ec < 0 then
    failwith ("Loc.user_position: end char number `" ^
                string_of_int ec ^ "` out of bounds");
  if ec >= mask_col  && not !warning_emitted then
    begin
      warning "Loc.user_position: end char number `%d` overflows on next line" ec;
      warning_emitted := true;
    end;
  let tag = FileTags.get_file_tag f in
  { pos_file_tag = tag;
    pos_start = (bl lsl bits_col) lor bc;
    pos_end = (el lsl bits_col) lor ec }

let extract (b,e) =
  let f = b.pos_fname in
  let bl = b.pos_lnum in
  let bc = b.pos_cnum - b.pos_bol in
  let el = e.pos_lnum in
  let ec = e.pos_cnum - e.pos_bol in
  user_position f bl bc el ec


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
