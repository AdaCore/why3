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
open Model_parser
open Lexing

let debug = Debug.register_info_flag "parse_smtv2_model"
  ~desc:"Print@ debugging@ messages@ about@ parsing@ model@ \
         returned@ from@ cvc4@ or@ z3."

(*
*************************************************************** 
**  Estabilish mapping to why3 code
****************************************************************
*)
let rec extract_element_name labels raw_string regexp =
  match labels with
  | [] -> raw_string
  | label::labels_tail ->
    let l_string = label.lab_string in
    begin 
      try 
	ignore(Str.search_forward regexp l_string 0);
	let end_pos = Str.match_end () in
	String.sub l_string end_pos ((String.length l_string) - end_pos)
      with Not_found -> extract_element_name labels_tail raw_string regexp
    end
    
let get_element_name term raw_string  =
  let labels = Slab.elements term.t_label in
  let regexp = Str.regexp "model_trace:" in
  extract_element_name labels raw_string regexp
    
(* Uses got from printer mapping to update model names and locations in model.
   Assumes that the ordering of elements of terms corresponds the ordering 
   in raw_model. That is nth element of raw_model corresponds to the nth 
   element of terms. *)
let rec update_element_names_and_locations raw_model terms updated_model =
  match raw_model with
  | [] -> updated_model
  | model_element::raw_strings_tail ->
    let (element_name, element_location, element_term, terms_tail) = 
      match terms with
      | [] -> (model_element.me_name, None, None, [])
      | term::t_tail -> 
        ((get_element_name term model_element.me_name), 
         term.t_loc, 
         Some term, t_tail) in
    let new_model_element = create_model_element
      ~name:element_name 
      ~value:model_element.me_value 
      ?location:element_location 
      ?term:element_term 
      () in
    let updated_model = updated_model @ [new_model_element] in
    update_element_names_and_locations 
      raw_strings_tail 
      terms_tail 
      updated_model
      
(*
*************************************************************** 
**   Parser
****************************************************************
*)
let get_position lexbuf =
  let pos = lexbuf.lex_curr_p in
  let cnum = pos.pos_cnum - pos.pos_bol + 1 in
  Loc.user_position 
    "Model string returned from the prover"  
    pos.pos_lnum
    cnum
    cnum

let do_parsing model =
  let lexbuf = Lexing.from_string model in
  try
    Parse_smtv2_model_parser.output Parse_smtv2_model_lexer.token lexbuf
  with
  | Parse_smtv2_model_lexer.SyntaxError -> 
    Warning.emit 
      ~loc:(get_position lexbuf)
      "Error@ during@ lexing@ of@ smtlib@ model:@ unexpected character";
    []
  | Parse_smtv2_model_parser.Error ->
    begin
      let loc = get_position lexbuf in
      Warning.emit ~loc:loc "Error@ during@ parsing@ of@ smtlib@ model";
      []
    end
      
(* Parses the model returned by CVC4 or Z3.
   Returns the list of pairs term - value *)
let parse input printer_mapping =
  try
    let r = Str.regexp "unknown\\|sat" in
    ignore (Str.search_forward r input 0);
    let match_end = Str.match_end () in
    let model_string = 
      String.sub input match_end ((String.length input) - match_end) in
    
    let raw_model = do_parsing model_string in
    
    update_element_names_and_locations 
      raw_model 
      printer_mapping.queried_terms 
      []
  with 
  | Not_found -> [] 

    
let () = register_model_parser "smtv2" parse
  ~desc:"Parser@ for@ the@ model@ of@ cv4@ and@ z3."
