(** module to translate from the basic abstract tree from the parser
to a proper why internal representation to be pretty-printed *)

open TptpTree

open Why
open Why.Ident

(*s this module manages scoping of vars using a stack of
variables bindings *)
module Scope
  (T : sig
    type key
    type value
    val create : key -> value
  end) = struct

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

end

let const x _ = x;;

(*s module to translate a basic tptp originated tree into a why AST tree *)
module Translate = struct

  (** an abstract type for the whole theory *)
  let t =
    let tv = Ty.create_tvsymbol (Ident.id_fresh "t") in
    Ty.ty_var tv

  module EnvVar = Scope(
    struct
      type key = variable
      type value = Term.vsymbol
      let create v = Term.create_vsymbol (id_fresh (String.uncapitalize v)) t
    end)
  module EnvFunctor = Scope(
    struct
      type key = (atom * Ty.ty list)
      type value = Term.lsymbol
      let create (v,l)  = Term.create_fsymbol (id_fresh (String.uncapitalize v)) l t
    end)

  (** translation for terms *)
  let rec term2term = function
  | TAtom x -> Term.t_app (EnvFunctor.find (x, [])) [] t
  | TConst x -> Term.t_app (EnvFunctor.find (x, [])) [] t
  | TVar x -> Term.t_var (EnvVar.find x)
  | TFunctor (f, terms) ->
      Term.t_app
        (EnvFunctor.find (f, List.map (const t) terms))
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
    EnvVar.push_scope []; (* new scope *)
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
      (EnvFunctor.find (p, List.map (const t) terms))
      (List.map term2term terms)
  | FTermBinop (op, t1, t2) ->
    Term.f_app
      ( match op with
        | Equal -> EnvFunctor.find ("=", [t;t])
        | NotEqual -> EnvFunctor.find ("<>", [t;t]) )
      [term2term t1; term2term t2]

  let theory_of_decls theoryName decls = assert false;

end

let theory_of_decls = Translate.theory_of_decls
