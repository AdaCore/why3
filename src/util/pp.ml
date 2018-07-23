(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*i $Id: pp.ml,v 1.22 2009-10-19 11:55:33 bobot Exp $ i*)

(*s Pretty-print library *)

open Format

type 'a pp = formatter -> 'a -> unit

let print_option f fmt = function
  | None -> ()
  | Some x -> f fmt x

let print_option_or_default default f fmt = function
  | None -> fprintf fmt "%s" default
  | Some x -> f fmt x

let rec print_list_pre sep print fmt = function
  | [] -> ()
  | x :: r -> sep fmt (); print fmt x; print_list_pre sep print fmt r

let rec print_list_suf sep print fmt = function
  | [] -> ()
  | x :: r -> print fmt x; sep fmt (); print_list_suf sep print fmt r

let print_list sep print fmt = function
  | [] -> ()
  | [x] -> print fmt x
  | x :: r -> print fmt x; print_list_pre sep print fmt r

let print_list_or_default default sep print fmt = function
  | [] -> fprintf fmt "%s" default
  | l -> print_list sep print fmt l

let print_list_par sep pr fmt l =
  print_list sep (fun fmt x -> fprintf fmt "(%a)" pr x) fmt l

let print_list_delim ~start ~stop ~sep pr fmt = function
  | [] -> ()
  | l -> fprintf fmt "%a%a%a" start () (print_list sep pr) l stop ()

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r ->
      print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let print_iter1 iter sep print fmt l =
  let first = ref true in
  iter (fun x ->
          if !first
          then first := false
          else sep fmt ();
          print fmt x ) l

let print_iter2 iter sep1 sep2 print1 print2 fmt l =
  let first = ref true in
  iter (fun x y ->
          if !first
          then first := false
          else sep1 fmt ();
          print1 fmt x;sep2 fmt (); print2 fmt y) l


let print_iter22 iter sep print fmt l =
  let first = ref true in
  iter (fun x y ->
          if !first
          then first := false
          else sep fmt ();
          print fmt x y) l


let print_pair_delim start sep stop pr1 pr2 fmt (a,b) =
  fprintf fmt "%a%a%a%a%a" start () pr1 a sep () pr2 b stop ()


type formatted = (unit, unit, unit, unit, unit, unit) format6
let empty_formatted : formatted = ""

let dot fmt () = fprintf fmt ".@ "
let comma fmt () = fprintf fmt ",@ "
let star fmt () = fprintf fmt "*@ "
let simple_comma fmt () = fprintf fmt ", "
let underscore fmt () = fprintf fmt "_"
let slash fmt () = fprintf fmt "/"
let semi fmt () = fprintf fmt ";@ "
let colon fmt () = fprintf fmt ":@ "
let space fmt () = fprintf fmt "@ "
let alt fmt () = fprintf fmt "|@ "
let alt2 fmt () = fprintf fmt "@ | "
let equal fmt () = fprintf fmt "@ =@ "
let newline fmt () = fprintf fmt "@\n"
let newline2 fmt () = fprintf fmt "@\n@\n"
let arrow fmt () = fprintf fmt "@ -> "
let lbrace fmt () = fprintf fmt "{"
let rbrace fmt () = fprintf fmt "}"
let lsquare fmt () = fprintf fmt "["
let rsquare fmt () = fprintf fmt "]"
let lparen fmt () = fprintf fmt "("
let rparen fmt () = fprintf fmt ")"
let lchevron fmt () = fprintf fmt "<"
let rchevron fmt () = fprintf fmt ">"
let nothing _fmt _ = ()
let string = pp_print_string
let float = pp_print_float
let int = pp_print_int
let constant_string s fmt () = string fmt s
let formatted fmt x = Format.fprintf fmt "%( %)" x
let constant_formatted f fmt () = formatted fmt f
let print0 fmt () = pp_print_string fmt "\000"
let add_flush sep fmt x = sep fmt x; pp_print_flush fmt ()

let asd f fmt x = fprintf fmt "\"%a\"" f x

let print_pair pr1 = print_pair_delim lparen comma rparen pr1

let hov n f fmt x = pp_open_hovbox fmt n; f fmt x; pp_close_box fmt ()
let indent n f fmt x =
  for _i = 0 to n do
    pp_print_char fmt ' '
  done;
  hov 0 f fmt x

let open_formatter ?(margin=78) cout =
  let fmt = formatter_of_out_channel cout in
  pp_set_margin fmt margin;
  pp_open_box fmt 0;
  fmt

let close_formatter fmt =
  pp_close_box fmt ();
  pp_print_flush fmt ()

let open_file_and_formatter ?(margin=78) f =
  let cout = open_out f in
  let fmt = open_formatter ~margin cout in
  cout,fmt

let close_file_and_formatter (cout,fmt) =
  close_formatter fmt;
  close_out cout

let print_in_file_no_close ?(margin=78) p f =
  let cout,fmt = open_file_and_formatter ~margin f in
  p fmt;
  close_formatter fmt;
  cout

let print_in_file ?(margin=78) p f =
  let cout = print_in_file_no_close ~margin p f in
  close_out cout



(* With optional separation *)
let rec print_list_opt sep print fmt = function
  | [] -> false
  | [x] -> print fmt x
  | x :: r ->
      let notempty1 = print fmt x in
      if notempty1 then sep fmt ();
      let notempty2 = print_list_opt sep print fmt r in
      notempty1 || notempty2


let string_of ?max_boxes p x =
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  Opt.iter (fun x ->
    Format.pp_set_ellipsis_text fmt "...";
    Format.pp_set_max_boxes fmt x) max_boxes;
  fprintf fmt "%a@?" p x;
  Buffer.contents b

let wnl fmt =
(*
  let out,flush,_newline,spaces =
    pp_get_all_formatter_output_functions fmt () in
  pp_set_all_formatter_output_functions fmt
    ~out ~flush ~newline:(fun () -> spaces 1) ~spaces
*)
  let o = pp_get_formatter_out_functions fmt () in
  pp_set_formatter_out_functions fmt
    { o with out_newline = (fun () -> o.out_spaces 1) }


let string_of_wnl p x =
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  wnl fmt;
  fprintf fmt "%a@?" p x;
  Buffer.contents b

let sprintf p =
  (* useless: this is the same as Format.asprintf *)
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  kfprintf (fun fmt -> Format.pp_print_flush fmt (); Buffer.contents b) fmt p

let sprintf_wnl p =
  let b = Buffer.create 100 in
  let fmt = formatter_of_buffer b in
  wnl fmt;
  kfprintf (fun fmt -> Format.pp_print_flush fmt (); Buffer.contents b) fmt p

let html_char fmt c =
  match c with
  | '\"' -> pp_print_string fmt "&quot;"
  | '\'' -> pp_print_string fmt "&#39;"
  | '<' -> pp_print_string fmt "&lt;"
  | '>' -> pp_print_string fmt "&gt;"
  | '&' -> pp_print_string fmt "&amp;"
  | c -> pp_print_char fmt c

let html_string fmt s =
  for i=0 to String.length s - 1 do
    html_char fmt (String.get s i)
  done


module Ansi =
  struct

    let set_column fmt n = fprintf fmt "\027[%iG" n
end

type formatter = Format.formatter
