
(* main module for whyl *)

open Format

let files = ref []
let parse_only = ref false
let type_only = ref false
let debug = ref false
let loadpath = ref []

let () = 
  Arg.parse 
    ["--parse-only", Arg.Set parse_only, "stops after parsing";
     "--type-only", Arg.Set type_only, "stops after type-checking";
     "--debug", Arg.Set debug, "sets the debug flag";
     "-I", Arg.String (fun s -> loadpath := s :: !loadpath), 
       "<dir>  adds dir to the loadpath";
    ]
    (fun f -> files := f :: !files)
    "usage: whyl [options] files..."

let rec report fmt = function
  | Lexer.Error e ->
      fprintf fmt "lexical error: %a" Lexer.report e;
  | Pgm_lexer.Error e ->
      fprintf fmt "lexical error: %a" Pgm_lexer.report e;
  | Loc.Located (loc, e) ->
      fprintf fmt "%a%a" Loc.report_position loc report e
  | Parsing.Parse_error ->
      fprintf fmt "syntax error"
  | Typing.Error e ->
      Typing.report fmt e
  | e ->
      fprintf fmt "anomaly: %s" (Printexc.to_string e)

open Pgm_ptree
open Theory

let env = Env.create_env (Typing.retrieve !loadpath)

let type_file file =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let p = Pgm_lexer.parse_file lb in 
  close_in c;
  if !parse_only then raise Exit;
  let uc = Theory.create_theory (Ident.id_fresh "Pgm") in
  let _uc = 
    List.fold_left
      (fun uc d -> match d with
	 | LogicDecl dl -> List.fold_left (Typing.add_decl env Mnm.empty) uc dl)
      uc p
  in
  ()

let handle_file file =
  try
    type_file file
  with Exit -> 
    ()

let () =
  try
    List.iter handle_file !files
  with e when not !debug ->
    eprintf "%a@." report e;
    exit 1

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
