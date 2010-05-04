(** this is a tool to convert tptp files (.p files) to .why files *)

open TptpTree

(** very basic name sanitizer for axioms and goals *)
let sanitize =
  let module M = Map.Make(struct type t=string let compare = String.compare end) in
  let m = ref M.empty in
  fun name -> if M.mem name !m
    then begin
      let cur = M.find name !m in
      m := M.add name (cur+1) !m;
      name ^ (string_of_int cur)
    end else begin
      m := M.add name 0 !m;
      name
    end


module S = Set.Make(struct type t=string let compare = String.compare end)
module M = Map.Make(struct type t=string let compare = String.compare end)

(** exploratory module, to find atoms and functors to be declared first *)
module Summary : sig
  type indic = Pred | Term
  val findAtoms : S.t -> fmla -> S.t
  val findFunctors : (indic * int) M.t ->
        TptpTree.fmla -> (indic * int) M.t
  val findAllAtoms : decl list -> S.t
  val findAllFunctors : TptpTree.decl list -> (indic * int) M.t
end = struct
  type indic = Pred | Term

  let rec findAtoms_t s = function
  | TAtom a -> S.add a s
  | TConst _ | TVar _ -> s
  | TFunctor (_, terms) ->
    List.fold_left findAtoms_t s terms

  let rec findAtoms s = function
  | FBinop (_, f1, f2) -> S.union (findAtoms s f1) (findAtoms s f2)
  | FUnop (_, f) -> findAtoms s f
  | FQuant (_, _, f) -> findAtoms s f
  | FPred (_, terms) -> List.fold_left findAtoms_t s terms
  | FTermBinop (_, t1, t2) -> S.union (findAtoms_t s t1) (findAtoms_t s t2)

  let union_map = M.fold M.add

  let rec findFunctors_t m = function
  | TAtom _ | TConst _ | TVar _ -> m
  | TFunctor (f, terms) -> M.add f (Term, List.length terms) m

  let rec findFunctors m = function
  | FBinop (_, f1, f2) -> union_map (findFunctors m f1) (findFunctors m f2)
  | FUnop (_, f) -> findFunctors m f
  | FQuant (_, _, f) -> findFunctors m f
  | FPred (p, terms) -> let new_m = M.add p (Pred, List.length terms) m in
      List.fold_left findFunctors_t new_m terms
  | FTermBinop (_, t1, t2) ->
      union_map (findFunctors_t m t1) (findFunctors_t m t2)

  let findAllAtoms decls =
    let helper m = function Fof(_, _, f) -> findAtoms m f in
    List.fold_left helper S.empty decls

  let findAllFunctors decls =
    let helper s = function Fof(_, _, f) -> findFunctors s f in
    List.fold_left helper M.empty decls

end

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
  | Conjecture -> "goal"

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
  | x::xs when xs <> [] -> fprintf fmter "%a%s%a" printer x sep
      (print_list ~sep:sep printer) xs
  | x::[] -> fprintf fmter "%a" printer x
  | [] -> ()

  let printVar fmter v = pp_print_string fmter (String.uncapitalize v)
  let printAtom fmter a = pp_print_string fmter (String.uncapitalize a)

  let rec printTerm fmter = function
  | TAtom atom -> printAtom fmter atom
  | TConst c -> pp_print_string fmter c
  | TVar v -> printVar fmter v
  | TFunctor (atom, terms) ->
    fprintf fmter "@[%s(%a)@]" atom (print_list printTerm) terms

  let rec printFmla fmter = function
  | FBinop (op, f1, f2) ->
    fprintf fmter "(@[%a@ %s@ %a@])" printFmla f1 (show_fbinop op) printFmla f2
  | FUnop (op, f) ->
    fprintf fmter "@[(%s %a)@]" (show_funop op) printFmla f
  | FQuant (quant, vars, f) ->
    fprintf fmter "@[%s@ %a:t.@] %a" (show_quantifier quant)
      (print_list printVar) vars printFmla f
  | FPred (pred, terms) ->
    fprintf fmter "%s(@[%a@])" pred (print_list printTerm) terms
  | FTermBinop (op, t1, t2) ->
    fprintf fmter "(@[%a %s %a@])" printTerm t1 (show_tbinop op) printTerm t2


  let printDecl fmter = function
  | Fof (name, ty, fmla) ->
    fprintf fmter "%s %s :@\n @[%a@]\n" (show_type ty)
      (sanitize (String.capitalize name)) printFmla fmla

  (** prints the declaration of a functor : logic f(t, t, t... t) *)
  let printFunctorDecl fmter (f,(ty,arity)) =
    let ty_print = match ty with Summary.Pred -> "" | Summary.Term -> ":t" in
    let rec helper fmter arity = match arity with
    | 0 -> pp_print_string fmter "" | 1 -> pp_print_string fmter "t"
    | arity -> fprintf fmter "%s, %a" "t" helper (arity-1) in
    fprintf fmter "logic %a(%a) %s" pp_print_string f helper arity ty_print

  let printAtomDecl fmter atom =
    fprintf fmter "logic %s : t" (String.uncapitalize atom)

  (** prints forward declarations *)
  let printPreambule fmter decls =
    let functors = Summary.findAllFunctors decls in
    let atoms = Summary.findAllAtoms decls in
    begin
      fprintf fmter "type t\n";
      print_list ~sep:"\n" printAtomDecl fmter (S.fold (fun x y->x::y) atoms []);
      fprintf fmter "\n\n";
      print_list ~sep:"\n" printFunctorDecl fmter
        (M.fold (fun x y acc -> (x,y)::acc) functors []);
      fprintf fmter "\n\n"
    end

  (** create a theory with name @name@ and a type t*)
  let printTheory fmter name decls =
    fprintf fmter "theory %s@\n@[<hov 2>%a %a@]@\nend\n\n"
        name printPreambule decls (print_list ~sep:"\n" printDecl) decls

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
  parse options (fun file -> input_files := file :: (!input_files)) usage;
  input_files := List.rev !input_files;
  let theoryCounter = ref 0 in
  List.iter
    (fun x -> let theoryName = "Theory"^(string_of_int !theoryCounter) in
              incr theoryCounter;
              Print.printFile !output_chan theoryName x)
    !input_files
