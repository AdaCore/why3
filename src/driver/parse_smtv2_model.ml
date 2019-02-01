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

(* Parses the model returned by CVC4 and Z3. *)
open Model_parser
open Lexing

let debug = Debug.register_info_flag "parse_smtv2_model"
  ~desc:"Print@ debugging@ messages@ about@ parsing@ model@ \
         returned@ from@ cvc4@ or@ z3."

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
    Debug.dprintf debug "Entering smtv2 model parser@.";
    let x = Parse_smtv2_model_parser.output Parse_smtv2_model_lexer.token lexbuf in
    Debug.dprintf debug "smtv2 model parser: OK@.";
    x
  with
  | Parse_smtv2_model_lexer.SyntaxError ->
     let l = Lexing.lexeme lexbuf in
     Debug.dprintf debug "smtv2 model parser: SyntaxError on lexeme '%s'@." l;
     Warning.emit
       ~loc:(get_position lexbuf)
       "Error@ during@ lexing@ of@ smtlib@ model:@ unexpected text '%s'"
       l;
     Wstdlib.Mstr.empty
  | Parse_smtv2_model_parser.Error ->
     let l = Lexing.lexeme lexbuf in
     Debug.dprintf debug "smtv2 model parser: Error on lexeme '%s'@." l;
     let loc = get_position lexbuf in
     Warning.emit
       ~loc:loc
       "Error@ during@ parsing@ of@ smtlib@ model:  unexpected text '%s'"
       l;
     Wstdlib.Mstr.empty

let do_parsing list_proj list_fields list_records noarg_constructors set_str model =
  let m = do_parsing model in
  Collect_data_model.create_list list_proj list_fields list_records noarg_constructors set_str m

(* Parses the model returned by CVC4, Z3 or Alt-ergo.
   Returns the list of pairs term - value *)
(* For Alt-ergo the output is not the same and we
   match on "I don't know". But we also need to begin
   parsing on a fresh new line ".*" ensures it *)
let parse : raw_model_parser =
  fun list_proj list_fields list_records noarg_constructors set_str input ->
  try
(*    let r = Str.regexp "unknown\\|sat\\|\\(I don't know.*\\)" in
    ignore (Str.search_forward r input 0);
    let match_end = Str.match_end () in*)
    let nr = Str.regexp "^)+" in
    let res = Str.search_backward nr input (String.length input) in
    let model_string = String.sub input 0 (res + String.length (Str.matched_string input)) in
    do_parsing list_proj list_fields list_records noarg_constructors set_str model_string
  with
  | Not_found -> []


let () = register_model_parser "smtv2" parse
  ~desc:"Parser@ for@ the@ model@ of@ cv4@ and@ z3."
