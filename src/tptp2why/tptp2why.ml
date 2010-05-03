(** this is a tool to convert tptp files (.p files) to .why files *)

open TptpTree


(** ugly basic printer for trees *)
module Print : sig

  val printDecl : decl -> unit
  val printFmla : Format.formatter -> fmla -> unit
  val printFile : string -> unit

end = struct

  open Format

  let show_type ty = match ty with
  | Axiom -> "axiom"
  | Conjecture -> "conjecture"

  let show_fbinop op = match op with
  | And -> "and"
  | Or -> "or"
  | Implies -> "->"
  | Equiv -> "<->"

  let show_funop = function
  | Not -> "not"

  let show_tbinop = function
  | Equal -> "="
  | NotEqual -> "<>"

  let show_quantifier = function
  | Forall -> "forall"
  | Exist -> "exists"

  (** prints a list of items with printer *)
  let rec print_list printer fmter = function
  | x::xs when xs <> [] -> fprintf fmter "%a@, %a" printer x (print_list printer) xs
  | x::[] -> fprintf fmter "%a" printer x
  | [] -> ()

  let rec printTerm fmter = function
  | TAtom atom -> pp_print_string fmter atom
  | TConst c -> pp_print_string fmter c
  | TVar v -> pp_print_string fmter v
  | TFunctor (atom, terms) ->
    fprintf fmter "%s(@%a)" atom (print_list printTerm) terms

  let rec printFmla fmter = function
  | FBinop (op, f1, f2) ->
    fprintf fmter "%a @%s %a" printFmla f1 (show_fbinop op) printFmla f2
  | FUnop (op, f) ->
    fprintf fmter "@[(%s %a)@]" (show_funop op) printFmla f
  | FQuant (quant, vars, f) ->
    fprintf fmter "%s@ %a.@ (%a)" (show_quantifier quant)
      (print_list pp_print_string) vars printFmla f
  | FPred (pred, terms) ->
    fprintf fmter "%s(@%a)" pred (print_list printTerm) terms
  | FTermBinop (op, t1, t2) ->
    fprintf fmter "@[%a %s %a@]" printTerm t1 (show_tbinop op) printTerm t2


  let printDecl = function
  | Fof (name, ty, fmla) ->
    printf "fof(%s, %s, %a).\n" name (show_type ty) printFmla fmla

  let printFile filename =
    let input = open_in filename in
    let decls = Tptp_parser.tptp Tptp_lexer.token (Lexing.from_channel input) in
    close_in input;
    List.iter printDecl decls

end


(** main function and arg parsing *)

open Arg

let debug = ref false
let print_in = ref false
let input_files = ref []

let options = [
  ("-debug", Set debug, "activates debug mode");
  ("-print-in", Set print_in, "prints parsed input")
]
let usage = "tptp2why [-debug] [-print-in] file1 [file2...]
It parses tptp files (fof format) and prints a why file
with one theory per input file."

let _ =
  parse options (fun file -> input_files := file :: (!input_files)) usage;
  input_files := List.rev !input_files;
  if !print_in
    then List.iter Print.printFile !input_files
    else failwith "not implemented !"
