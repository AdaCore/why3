(** this is a tool to convert tptp files (.p files) to .why files *)

open TptpTree

open Why


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
  val findAllIncludes : TptpTree.decl list -> string list
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
    let helper m = function Fof(_, _, f) -> findAtoms m f | _ -> assert false in
    List.fold_left helper S.empty decls

  let findAllFunctors decls =
    let helper s = function Fof(_, _, f) -> findFunctors s f | _ -> assert false in
    List.fold_left helper M.empty decls

  let rec findAllIncludes = function
  | ((Include x)::xs) -> x :: findAllIncludes xs
  | (_::xs) -> findAllIncludes xs
  | [] -> []

end


(* TODO : update code *)
(** module to process a single file *)
module Process : sig

  val printFile : Format.formatter -> string -> string -> string -> unit

end= struct

  let fromInclude = function | Include x -> x | _ -> assert false
  (** for a given file, returns the list of declarations
  for this file and all the files it includes, recursively *)
  let rec getAllDecls ?first:(first=false) include_dir filename =
    try
      let filename = if first then filename else include_dir^"/"^filename in
      let input = open_in filename in
      let decls = Tptp_parser.tptp Tptp_lexer.token (Lexing.from_channel input) in
      let isInclude = function | Include _ -> true | _ -> false in
      close_in input;
      let (to_include, real_decl) = List.partition isInclude decls in
      let to_include = List.map fromInclude to_include in (* remove Include *)
      let all_decls = List.concat (List.map (getAllDecls include_dir) to_include) in
      all_decls @ real_decl
    with (Sys_error _) as e ->
      print_endline ("error : unable to open "^filename);
      raise e


  (** process a single file and all includes inside *)
  let printFile fmter include_dir theoryName filename =
    let decls = getAllDecls ~first:true include_dir filename in
    let theory = TptpTranslate.theory_of_decls theoryName decls in
    Pretty.print_theory fmter theory

end



(** main function and arg parsing *)

open Arg

module Init = struct

  let input_files = ref []
  let output_chan = ref (Format.formatter_of_out_channel stdout)
  let include_dir = ref "."

  let output_updater filename = if filename <> "-"
    then output_chan := Format.formatter_of_out_channel (open_out filename)
    else ()

  let include_updater s = include_dir := s

  let options = [
    ("-o", String output_updater, "outputs to a file");
    ("-I", String include_updater, "search for included files in this dir")
  ]

  let usage = "tptp2why file1 [file2...] [-o file] [-I dir]
  It parses tptp files (fof format) and prints a why file
  with one theory per input file."

end

open Init

let _ =
  parse options (fun file -> input_files := file :: (!input_files)) usage;
  input_files := List.rev !input_files;
  let theoryCounter = ref 0 in
  List.iter
    (fun x -> let theoryName = "Theory"^(string_of_int !theoryCounter) in
              incr theoryCounter;
              Process.printFile !output_chan !include_dir theoryName x)
    !input_files
