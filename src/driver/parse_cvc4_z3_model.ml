(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* Parses the model returned by CVC4 and Z3. *)

open Printer
open Ident
open Term

exception EndOfStringExc;;

let add_chr str chr num_opened =
  if num_opened >= 0 then (str ^ Char.escaped chr)
  else str

(* Gets the position of the closing bracket of the string 
starting in the pos in str assuming that the given number
of brackets are opened in this position. 
Assumes that at least one bracket is opened.
Example: get_in_brackets "a)" 0 1
   returns 1
 *)
let rec get_in_brackets str pos opened =
  if pos >= String.length str then raise (EndOfStringExc)
  else begin
    let chr = str.[pos] in
    match chr with
    | '(' -> begin
      get_in_brackets str (pos+1) (opened+1)
    end
    | ')' -> begin
      if opened-1 = 0 then pos
      else 
	get_in_brackets str (pos+1) (opened-1)
    end
    | _ -> begin
      get_in_brackets str (pos+1) opened
    end
  end

let _ = get_in_brackets "(2)" 1 1;;


let rec find_first char str pos =
  if pos >= String.length str then raise (EndOfStringExc)
  else begin
    let chr = str.[pos] in
    if char == chr then pos
    else find_first char str (pos+1);
  end

let find_first_open_bracket = find_first '('

let find_first_space = find_first ' '

let find_first_closing_bracket = find_first ')'

let _ = find_first_open_bracket "dasfd dfd (" 0

(* Finds the end of term.
Assumes that the term has a form: "term: (anything) | any_string_delimited_by_space" *)
let term_end ch_delimit str pos =
  let chr_first = str.[pos] in
  let t_end = match chr_first with
    | '(' -> get_in_brackets str (pos+1) 1
    | _ -> (find_first ch_delimit str (pos+1))-1 in
  t_end

(* Parses one pair of terms. Returns positions of the terms.
Assumes that the part has a form: "pair: [(term1 term2)]*" *)
let parse_pair str pos =
  let start_first = pos + 1 in

  let end_first = term_end ' ' str start_first in
  let start_second = end_first+2 in
  let end_second = term_end ')' str start_second in
  start_first, end_first, start_second, end_second

let _ = parse_pair "(x 1)" 0
let _ = parse_pair "((s(s)) 1)" 0
let _ = parse_pair "((sdfd()) (dsf)" 0
let _ = parse_pair "((= (+ (+ (+ (+ (+ (+ (+ x1 x2) x3) x4) x5) x6) x7) x8) 2) false)" 0

(* Parses a sequence of pairs from str. Returns the list of pairs.
Assumes that the parts have a form: "parts: [pair]*\)" *)
let rec parse_pairs str pos list =
  try 
    let start_pos = find_first '(' str pos in

    let (start1, end1, start2, end2) = parse_pair str start_pos in   
    let part1 = String.sub str start1 (end1-start1+1) in
    let part2 = String.sub str start2 (end2-start2+1) in

    let newlist = (part1, part2)::list in

    parse_pairs str end2 newlist
  with EndOfStringExc -> (pos, list)
    
let _ = parse_pairs "((s(s)) 1) (x 1))" 0 []
let _ = parse_pairs "((= (+ (+ (+ (+ (+ (+ (+ x1 x2) x3) x4) x5) x6) x7) x8) 2) false))" 0 []

let rec extract_term_string labels raw_string regexp =
  match labels with
  | [] -> raw_string
  | label::labels_tail ->
    let l_string = label.lab_string in
    begin 
      try 
	    ignore(Str.search_forward regexp l_string 0);
	    let end_pos = Str.match_end () in
	    String.sub l_string end_pos ((String.length l_string) - end_pos)
      with Not_found -> extract_term_string labels_tail raw_string regexp
    end
    

let get_term_string term raw_string  =
  let labels = Slab.elements term.t_label in
  let regexp = Str.regexp "model_trace:" in
  extract_term_string labels raw_string regexp
  

let rec get_terms_values_strings raw_strings terms collected_strings =
  match raw_strings with
  | [] -> collected_strings
  | (raw_term_string, value)::raw_strings_tail ->
    let (term_string, terms_tail) = match terms with
      | [] -> (raw_term_string, [])
      | term::t_tail -> ((get_term_string term raw_term_string), t_tail) in
    get_terms_values_strings raw_strings_tail terms_tail (collected_strings @ [(term_string, value)])

(* Parses the model returned by CVC4 or Z3.
Assumes that the model has the following form "model: (pairs)"
Returns the list of pairs term - value *)
let parse model printer_mapping =
  try
    let r = Str.regexp "unknown\\|sat" in
    let start_m = Str.search_forward r model 0 in
    let start = find_first_open_bracket model start_m in
    let raw_terms_values_strings = snd(parse_pairs model (start+1) []) in
    get_terms_values_strings raw_terms_values_strings printer_mapping.queried_terms []
  with Not_found -> [] 

let _ = parse "dasfdfd dafsd ( dasfdf ) dfa unknown ((x 1))" Printer.get_default_printer_mapping

let () = Model_parser.register_model_parser "cvc4_z3" parse
  ~desc:"Parser@ for@ the@ model@ of@ cv4@ and@ z3."
