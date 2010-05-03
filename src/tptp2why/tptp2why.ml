(** this is a tool to convert tptp files (.p files) to .why files *)

open TptpTree


(** ugly basic printer for trees *)
module Print : sig

  val printDecl : Format.formatter -> decl -> unit
  val printFmla : Format.formatter -> fmla -> unit
  val printTheory : Format.formatter -> string -> decl list -> unit
  val printFile : Format.formatter -> string -> string -> unit

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
  let rec print_list ?sep:(sep=", ") printer fmter = function
  | x::xs when xs <> [] -> fprintf fmter "%a%s%a" printer x sep (print_list printer) xs
  | x::[] -> fprintf fmter "%a" printer x
  | [] -> ()

  let rec printTerm fmter = function
  | TAtom atom -> pp_print_string fmter atom
  | TConst c -> pp_print_string fmter c
  | TVar v -> pp_print_string fmter v
  | TFunctor (atom, terms) ->
    fprintf fmter "%s(@[%a@])" atom (print_list printTerm) terms

  let rec printFmla fmter = function
  | FBinop (op, f1, f2) ->
    fprintf fmter "%a@ %s@ %a" printFmla f1 (show_fbinop op) printFmla f2
  | FUnop (op, f) ->
    fprintf fmter "@[(%s %a)@]" (show_funop op) printFmla f
  | FQuant (quant, vars, f) ->
    fprintf fmter "%s@ %a.@ (%a)" (show_quantifier quant)
      (print_list pp_print_string) vars printFmla f
  | FPred (pred, terms) ->
    fprintf fmter "%s(@[%a@])" pred (print_list printTerm) terms
  | FTermBinop (op, t1, t2) ->
    fprintf fmter "@[%a %s %a@]" printTerm t1 (show_tbinop op) printTerm t2


  let printDecl fmter = function
  | Fof (name, ty, fmla) ->
    fprintf fmter "fof(%s, %s, @[%a@]).\n" name (show_type ty) printFmla fmla

  (** create a theory with name @name@ *)
  let printTheory fmter name decls =
    fprintf fmter "theory %s@\n @[<hov 2> %a @]@\nend\n"
        name (print_list ~sep:"\n" printDecl) decls

  let printFile fmter theoryName filename =
    let input = open_in filename in
    let decls = Tptp_parser.tptp Tptp_lexer.token (Lexing.from_channel input) in
    close_in input;
    printTheory fmter theoryName decls

end



(** main function and arg parsing *)

open Arg

let input_files = ref []
let output_chan = ref (Format.formatter_of_out_channel stdout)

let output_updater filename = if filename <> "-"
  then output_chan := Format.formatter_of_out_channel (open_out filename)
  else ()

let options = [
  ("-o", String output_updater, "outputs to a file")
]

let usage = "tptp2why file1 [file2...] [-o file]
It parses tptp files (fof format) and prints a why file
with one theory per input file."

let _ =
  print_endline "parses options";
  parse options (fun file -> input_files := file :: (!input_files)) usage;
  input_files := List.rev !input_files;
  let theoryCounter = ref 0 in
  List.iter
    (fun x -> print_endline ("parses "^x);
              let theoryName = "Theory"^(string_of_int !theoryCounter) in
              incr theoryCounter;
              Print.printFile !output_chan theoryName x)
    !input_files
