(** module to translate from the basic abstract tree from the parser
to a proper why internal representation to be pretty-printed *)

open TptpTree

open Why
open Why.Ident

module S = Set.Make(String)
module M = Map.Make(String)

(** exploratory module, to find atoms and functors to be declared first *)
module Summary : sig
  type indic = Pred | Term
  val findAtoms : S.t -> fmla -> S.t
  val findFunctors : (indic * int) M.t ->
        TptpTree.fmla -> (indic * int) M.t
  val findAllAtoms : TptpTree.decl list -> S.t
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
    let helper m = function Fof(_, _, f) -> findAtoms m f | _ -> assert false in
    List.fold_left helper S.empty decls

  let findAllFunctors decls =
    let helper s = function Fof(_, _, f) -> findFunctors s f | _ -> assert false in
    List.fold_left helper M.empty decls


end

(*s this module manages scoping of vars using a stack of
variables bindings *)
module Scope
  (T : sig
    type key
    type value
    val create : key -> value
  end) = struct

  (* TODO : write a more efficient implementation, for example with maps *)
  let scope = ref []

  let is_empty () = !scope = []

  (** adds a new scope with fresh vars *)
  let push_scope vars =
    let bindings = List.map (fun x -> (x, T.create x)) vars in
    scope := bindings :: !scope

  (** exits the outermost scope and forgets all bindings inside *)
  let pop_scope () = begin
      assert (not (is_empty ()));
      scope := List.tl !scope
    end

  (** finds a symbol in any scope, including deeper ones.
  If the symbol cannot be found, a new binding is created. *)
  let find symbol =
    let rec helper = function
    | [] -> raise Not_found
    | (x::_) when List.mem_assoc symbol x -> List.assoc symbol x
    | (_::xs) -> helper xs in
    try helper !scope
    with Not_found -> begin
      let v = T.create symbol in
      scope := ( match !scope with
        | [] -> [[symbol, v]]
        | (hd::tl) -> ((symbol,v)::hd)::tl );
      v
    end

  let depth () = List.length !scope

end

let const x _ = x;;

let rec range n obj = match n with
| 0 -> []
| n -> obj::range (n-1) obj

(*s module to translate a basic tptp originated tree into a why AST tree *)
module Translate = struct

  (** an abstract type for the whole theory *)
  let ts = Ty.create_tysymbol (Ident.id_fresh "t") [] None
  let t = Ty.ty_app ts []

  (* TODO : replace it by a simple Map *)
  module EnvVar = Scope(
    struct
      type key = variable
      type value = Term.vsymbol
      let create v = Term.create_vsymbol (id_fresh (String.uncapitalize v)) t
    end)
  module EnvFunctor = Scope(
    struct
      type key = (atom * Ty.ty list * Summary.indic)
      type value = Term.lsymbol
      let create (v,l,ty) = match ty with
      | Summary.Term -> Term.create_fsymbol (id_fresh (String.uncapitalize v)) l t
      | Summary.Pred -> Term.create_psymbol (id_fresh (String.uncapitalize v)) l
    end)

  (** translation for terms *)
  let rec term2term = function
  | TAtom x -> Term.t_app (EnvFunctor.find (x, [], Summary.Term)) [] t
  | TConst x -> Term.t_app (EnvFunctor.find (x, [], Summary.Term)) [] t
  | TVar x -> Term.t_var (EnvVar.find x)
  | TFunctor (f, terms) ->
      Term.t_app
        (EnvFunctor.find (f, List.map (const t) terms, Summary.Term))
        (List.map term2term terms)
        t

  (** translation for formulae *)
  let translate_binop = function | And -> Term.Fand | Or -> Term.For
    | Implies -> Term.Fimplies | Equiv -> Term.Fiff
  let translate_quant = function | Forall -> Term.Fforall | Exist -> Term.Fexists

  let rec fmla2fmla = function
  | FBinop (op, f1, f2) ->
    Term.f_binary
      (translate_binop op)
      (fmla2fmla f1)
      (fmla2fmla f2)
  | FUnop (op, f) ->
    assert (op = Not);
    Term.f_not (fmla2fmla f)
  | FQuant (quant, vars, f) -> begin
    (* Format.printf "@[<hov 2>quantifier %s %s (depth %d)@]\n" (if quant=Forall then "forall" else "exists") (String.concat ", " vars) (EnvVar.depth ()); *)
    EnvVar.push_scope vars; (* new scope *)
    let answer = Term.f_quant
      (translate_quant quant)
      (List.map EnvVar.find vars)
      [] (* no triggers *)
      (fmla2fmla f) in
    EnvVar.pop_scope (); (* exit scope *)
    answer
  end
  | FPred (p, terms) ->
    Term.f_app
      (EnvFunctor.find (p, List.map (const t) terms, Summary.Pred))
      (List.map term2term terms)
  | FTermBinop (op, t1, t2) ->
      ( match op with
        | Equal -> Term.f_equ_simp
        | NotEqual -> Term.f_neq_simp)
      (term2term t1) (term2term t2)

  let translatePropKind = function
  | Axiom -> Decl.Paxiom
  | Conjecture -> Decl.Pgoal

  (** add a declaration to a theory, after translation *)
  let addDecl theory = function
  | Fof(name, ty, f) ->
      let fmla = fmla2fmla f in
      (* print_endline ("adds declaration of "^name); *)
      Theory.add_prop_decl theory (translatePropKind ty)
        (Decl.create_prsymbol (id_fresh name)) fmla
  | Include _ -> assert false


  (** forward declaration of atoms and functors *)
  let addAtomForwardDecl name theory =
    (* Format.printf "declares %s\n (depth %d)" name (EnvVar.depth ()); *)
    let logic_decl = Decl.create_logic_decl
      [(EnvFunctor.find (name, [], Summary.Term)), None] in
    Theory.add_decl theory logic_decl

  let addFunctorsForwardDecl name obj theory =
    (* Format.printf "declares functor %s (type %s) (depth %d)\n" name (if fst obj = Summary.Pred then "pred" else "term"); *) 
    let logic_decl = Decl.create_logic_decl
      [(EnvFunctor.find (name, range (snd obj) t, (fst obj))), None] in
    Theory.add_decl theory logic_decl

  (** from a list of untyped declarations, translates them into a why theory *)
  let theory_of_decls theoryName decls =
    let theory = Theory.create_theory (Ident.id_fresh theoryName) in
    let theory = Theory.add_ty_decl theory [ts, Decl.Tabstract] in
    let theory = S.fold addAtomForwardDecl (Summary.findAllAtoms decls) theory in
    let theory = M.fold addFunctorsForwardDecl (Summary.findAllFunctors decls) theory in
    let theory = List.fold_left addDecl theory decls in
    Theory.close_theory theory

end

let theory_of_decls = Translate.theory_of_decls
