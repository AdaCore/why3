(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Theory

let files = ref []
let parse_only = ref false
let type_only = ref false
let debug = ref false
let loadpath = ref []
let print_stdout = ref false
let simplify_recursive = ref false
let inlining = ref false
let alt_ergo = ref false

let () = 
  Arg.parse 
    ["--parse-only", Arg.Set parse_only, "stops after parsing";
     "--type-only", Arg.Set type_only, "stops after type-checking";
     "--debug", Arg.Set debug, "sets the debug flag";
     "-I", Arg.String (fun s -> loadpath := s :: !loadpath), 
       "<dir>  adds dir to the loadpath";
     "--print-stdout", Arg.Set print_stdout, "print the results to stdout";
     "--simplify-recursive", Arg.Set simplify_recursive, "simplify recursive definition";
     "--inline", Arg.Set inlining, "inline the definition not recursive";
     "--alt-ergo", Arg.Set alt_ergo, "output for Alt-Ergo on stdout";
    ]
    (fun f -> files := f :: !files)
    "usage: why [options] files..."

let in_emacs = Sys.getenv "TERM" = "dumb"
let transform = !simplify_recursive || !inlining

let rec report fmt = function
  | Lexer.Error e ->
      fprintf fmt "lexical error: %a" Lexer.report e;
  | Loc.Located (loc, e) ->
      fprintf fmt "%a%a" Loc.report_position loc report e
  | Parsing.Parse_error ->
      fprintf fmt "syntax error"
  | Typing.Error e ->
      Typing.report fmt e
  | Context.UnknownIdent i ->
      fprintf fmt "anomaly: unknownident %s" i.Ident.id_short
  | e ->
      if in_emacs then
        let dir = Filename.dirname (Filename.dirname Sys.executable_name) in
        fprintf fmt "Entering directory `%s'@\n" dir; 
        fprintf fmt "anomaly:@\n%s" (Printexc.to_string e)
      else 
        fprintf fmt "anomaly: %s" (Printexc.to_string e)
let type_file env file =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let f = Lexer.parse_logic_file lb in 
  close_in c;
  if !parse_only then env else Typing.add_theories env f

let extract_goals ctxt =
  Transform.apply Transform.extract_goals ctxt

let transform l =
  let l = List.map (fun t -> t,t.th_ctxt) (Typing.list_theory l) in
  let l = if !simplify_recursive 
  then List.map (fun (t,dl) -> t,Transform.apply 
                   Simplify_recursive_definition.t dl) l 
  else l in
  let l = if !inlining
  then List.map (fun (t,dl) -> t,Transform.apply Inlining.all dl) l
  else l in
  if !print_stdout then 
    List.iter (fun (t,ctxt) -> Why3.print_context_th std_formatter t.th_name ctxt) l
  else if !alt_ergo then match l with
    | (_,ctxt) :: _ -> begin match extract_goals ctxt with
	| g :: _ -> Alt_ergo.print_goal std_formatter g
	| [] -> ()
      end	
    | [] -> ()

	

let () =
  try
    let env = Typing.create !loadpath in
    let l = List.fold_left type_file env !files in
    transform l
  with e when not !debug ->
    eprintf "%a@." report e;
    exit 1

(****

#load "hashcons.cmo";;
#load "name.cmo";;
#load "term.cmo";;
#load "pp.cmo";;
#load "pretty.cmo";;
#install_printer Name.print;;
#install_printer Pretty.print_ty;;
#install_printer Pretty.print_term;;

open Term

let alpha = Name.from_string "alpha"
let var_alpha = Ty.ty_var alpha

let list = Ty.create_tysymbol (Name.from_string "list") [alpha] None

let list_alpha = Ty.ty_app list [var_alpha]
let list_list_alpha = Ty.ty_app list [list_alpha]

let nil = create_fsymbol (Name.from_string "nil") ([], list_alpha)
let t_nil = t_app nil [] list_alpha
let tt_nil = t_app nil [] list_list_alpha

let cons = create_fsymbol (Name.from_string "cons") 
  ([var_alpha; list_alpha], list_alpha)

let int_ = Ty.create_tysymbol (Name.from_string "int") [] None

let _ = t_app cons [t_nil; tt_nil] list_list_alpha

****)
