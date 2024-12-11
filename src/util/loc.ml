(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
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
let expanded_position_of_sexp _ = assert false  [@@warning "-32"]
(* default values if the line below does not produce anything, i.e.,
   when ppx_sexp_conv is not installed *)

type expanded_position = string * int * int * int * int  [@@warning "-34"]
[@@deriving sexp]

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

type warning_id = string

type warning = { descr: Pp.formatted ; mutable enabled : bool }

let warning_table : (warning_id, warning) Hashtbl.t = Hashtbl.create 17

exception UnknownWarning of warning_id

let lookup_flag (s : warning_id) : warning =
  try Hashtbl.find warning_table s with Not_found -> raise (UnknownWarning s)

let unset_flag s = s.enabled <- false

let register_warning name (descr : Pp.formatted) =
  if Hashtbl.mem warning_table name then
    name
  else begin
    Hashtbl.replace warning_table name { descr; enabled = true };
    name
  end

let warn_unknown_warning =
  register_warning "unknown_warning" "Warn when an unknown warning flag is invoked"

let warning_active id =
  (Hashtbl.find warning_table id).enabled

let disable_warning id = unset_flag (lookup_flag id)

let without_warning name inner =
  let old = Hashtbl.find warning_table name in
  if not old.enabled then inner ()
  else
    try
      old.enabled <- false;
      let res = inner () in
      old.enabled <- true;
      res
    with e when not (Debug.test_flag Debug.stack_trace) ->
      old.enabled <- true;
      raise e

let warning id ?loc p =
    let open Format in
    let b = Buffer.create 100 in
    let fmt = formatter_of_buffer b in
    pp_set_margin fmt 1000000000;
    pp_open_box fmt 0;
    let handle fmt =
      pp_print_flush fmt (); !warning_hook ?loc (Buffer.contents b) in
    if warning_active id then kfprintf handle fmt p else ifprintf fmt p

module Args = struct
  open Getopt

  type spec = key * handler * doc

  let desc_warning_list, option_list =
    let opt_list_flags = ref false in
    let desc =
      KLong "list-warning-flags", Hnd0 (fun () -> opt_list_flags := true),
      " list warnings" in
    let list () =
      if !opt_list_flags then begin
        let list : (_ * _) list =
          Hashtbl.fold (fun s (desc) acc -> (s,desc.descr)::acc)
            warning_table [] in
        let print fmt (p,desc) =
          Format.fprintf fmt "@[%s@\n  @[%a@]@]"
            p
            Pp.formatted desc
        in
        Format.printf "@[<v>%a@]@."
          (Pp.print_list Pp.newline print)
          (List.sort Stdlib.compare list);
      end;
      !opt_list_flags in
    desc,list

  let opt_list_flags = Queue.create ()

  let add_flag s = Queue.add s opt_list_flags

  let desc_no_warn =
    KLong "warn-off", Hnd1 (AList (',', AString), fun l -> List.iter add_flag l),
    "<flag>,... disable some warnings"

  let set_flags_selected ?(silent=false) () =
    let check flag =
      match lookup_flag flag with
      | f -> unset_flag f
      | exception UnknownWarning _ when silent -> ()
      | exception UnknownWarning _ ->
          warning warn_unknown_warning "unknown warning flag `%s'" flag in
    Queue.iter check opt_list_flags
end



(* user positions *)

let warn_start_overflow =
  register_warning "start_overflow" "Warn when the start character of a source location overflows into the next line"

let warn_end_overflow =
  register_warning "end_overflow" "Warn when the end character of a source location overflows into the next line"

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
      warning warn_start_overflow "Loc.user_position: start char number `%d` overflows on next line" bc;
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
      warning warn_end_overflow "Loc.user_position: end char number `%d` overflows on next line" ec;
      warning_emitted := true;
    end;
  let tag = FileTags.get_file_tag f in
  { pos_file_tag = tag;
    pos_start = (bl lsl bits_col) lor bc;
    pos_end = (el lsl bits_col) lor ec }


let position_of_sexp sexp =
  let (s,bl,bc,el,ec) = expanded_position_of_sexp sexp in
  user_position s bl bc el ec
                          [@@warning "-32"]


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
