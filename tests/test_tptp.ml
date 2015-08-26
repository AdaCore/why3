

open Why3
open Tptp_ast
open Format

let pr_kind fmt k =
  match k with
  | TFF -> fprintf fmt "TFF"
  | FOF -> fprintf fmt "FOF"
  | CNF -> fprintf fmt "CNF"

let pr_role fmt r =
  match r with
  | Axiom -> fprintf fmt "Axiom"
  | Hypothesis -> fprintf fmt "Hypothesis"
  | Definition -> fprintf fmt "Definition"
  | Assumption -> fprintf fmt "Assumption"
  | Corollary -> fprintf fmt "Corollary"
  | Lemma -> fprintf fmt "Lemma"
  | Theorem -> fprintf fmt "Theorem"
  | Conjecture -> fprintf fmt "Conjecture"
  | Negated_conjecture -> fprintf fmt "Negated_conjecture"
  | Type -> fprintf fmt "Type"

let pr_op fmt op =
  match op with
  | BOequ -> fprintf fmt "equ"
  | BOnequ -> fprintf fmt "nequ"
  | BOimp -> fprintf fmt "imp"
  | BOpmi -> fprintf fmt "pmi"
  | BOand -> fprintf fmt "and"
  | BOor -> fprintf fmt "or"
  | BOnand -> fprintf fmt "nand"
  | BOnor -> fprintf fmt "nor"

let rec pr_expr fmt e =
  match e.e_node with
  | Elet(e1,e2) -> fprintf fmt "Elet(...)"
  | Eite(e1,e2,e3) -> fprintf fmt "Eite(...)"
  | Eqnt(q,vl,e) -> fprintf fmt "Eqnt(...)"
  | Ebin(op,e1,e2) ->
    fprintf fmt "Ebin(%a,%a,%a)" pr_op op pr_expr e1 pr_expr e2
  | Enot e -> fprintf fmt "Enot(%a)" pr_expr e
  | Eequ(e1,e2) -> fprintf fmt "Equ(%a,%a)" pr_expr e1 pr_expr e2
  | Eapp(w,el) ->
    fprintf fmt "Eapp(%s,[%a])" w (Pp.print_list Pp.comma pr_expr) el
  | Edef(w,el) -> fprintf fmt "Edef(...)"
  | Evar v -> fprintf fmt "Evar(%s)" v
  | Edob d -> fprintf fmt "Edob(...)"
  | Enum n -> fprintf fmt "Enum(...)"

let pr_top_formula fmt f =
  match f with
  | LogicFormula e -> fprintf fmt "LogicFormula(%a)" pr_expr e
  | TypedAtom(a,t) -> fprintf fmt "TypedAtom"
  | Sequent(l1,l2) -> fprintf fmt "Sequent"

let pr_decl fmt d =
  match d with
  | Formula(kind,name,role,top_formula,loc) ->
    fprintf fmt "@[<hov 2>{ kind = %a,@ name = '%s',@ role = %a,@ form = %a }@]"
      pr_kind kind name pr_role role pr_top_formula top_formula
  | Include(file,namelist,loc) ->
    fprintf fmt "include file '%s'" file

let pr_file fmt a =
  Pp.print_list Pp.newline pr_decl fmt a

let rec load file =
  let ch = open_in file in
  let ast = Tptp_lexer.parse ch in
  close_in ch;
  let ast =
    List.fold_left
      (fun acc d ->
        match d with
        | Formula _ -> d::acc
        | Include(file,_,_) ->
          let fn = String.sub file 1 (String.length file - 2) in
          let ast = load fn in
          List.rev_append ast acc)
      [] ast
  in List.rev ast


let () =
  if Array.length Sys.argv <> 2 then
    eprintf "Usage: %s <file>@." Sys.argv.(0)
  else
    try
      let ast = load Sys.argv.(1) in
      printf "%a@." pr_file ast
    with e ->
      eprintf "Parsing error: %a@." Exn_printer.exn_printer e

(*
Local Variables:
compile-command: "ocamlc -I /home/cmarche/.opam/4.02.1/lib/zip -I /home/cmarche/.opam/4.02.1/lib/menhirLib -I ../lib/why3 -I ../plugins/tptp unix.cma nums.cma dynlink.cma str.cma menhirLib.cmo zip.cma why3.cma tptp_ast.cmo tptp_typing.cmo tptp_parser.cmo tptp_lexer.cmo test_tptp.ml -o test_tptp"
End:
*)
