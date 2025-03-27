

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

exception Unsupported of string

let unsupported s = raise (Unsupported s)

let check_op op =
  match op with
  | BOequ -> unsupported "BOequ"
  | BOnequ -> unsupported "BOnequ"
  | BOimp -> ()
  | BOpmi -> unsupported "BOpmi"
  | BOand -> ()
  | BOor -> ()
  | BOnand -> ()
  | BOnor -> ()

let rec check_expr e = match e.e_node with
  | Elet(e1,e2) -> unsupported "let"
  | Eite(e1,e2,e3) -> unsupported "ite"
  | Eqnt(q,vl,e) -> check_expr e
  | Ebin(op,e1,e2) -> check_op op; check_expr e1; check_expr e2
  | Enot e -> check_expr e
  | Eequ(e1,e2) -> unsupported "equ"
  | Eapp(w,el) -> List.iter check_expr el
  | Edef(w,el) -> unsupported "def"
  | Evar v -> ()
  | Edob d -> unsupported "dob"
  | Enum n -> unsupported "num"

let check_top_formula f =
  match f with
  | LogicFormula e -> check_expr e
  | TypedAtom _ -> unsupported "TypedAtom"
  | Sequent _ -> unsupported "Sequent"

let check_role r =
  match r with
  | Axiom -> ()
  | Hypothesis -> ()
  | Definition -> unsupported "Definition"
  | Assumption -> ()
  | Corollary -> ()
  | Lemma -> ()
  | Theorem -> ()
  | Conjecture -> ()
  | Negated_conjecture -> ()
  | Type -> unsupported "Type"


let check_kind k =
  match k with
  | TFF -> unsupported "TFF"
  | FOF -> ()
  | CNF -> ()

let check_decl d =
  match d with
  | Include _ -> unsupported "Include"
  | Formula(kind,_,role,top_formula,_) ->
    check_kind kind; check_role role; check_top_formula top_formula

let check_file a = List.iter check_decl a

let () =
  if Array.length Sys.argv <> 2 then
    begin
      eprintf "Usage: %s <file>@." Sys.argv.(0);
      exit 2
    end
  else
    let file = Sys.argv.(1) in
    try
      let ast = Tptp_lexer.load file in
      check_file ast;
      (* printf "%a@." pr_file ast; *)
      printf "File '%s' is OK.@." file;
      exit 0
    with
    | Tptp_lexer.FileNotFound f ->
      eprintf "File not found: %s@." f; exit 2
    | Unsupported s ->
      eprintf "File %s: '%s' is not supported@." file s; exit 1
    | e ->
      eprintf "Parsing error: %a@." Exn_printer.exn_printer e;
      exit 2
