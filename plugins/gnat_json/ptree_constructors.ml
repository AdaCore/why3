open Why3
open Ptree

(** Smart constructors for [Ptree] nodes *)

let loc_counter = ref 0

let get_pos ?loc () = match loc with
  | Some loc ->
      loc
  | None ->
      incr loc_counter;
      Loc.user_position "<dummy>" !loc_counter 0 0

let mk_ident attrs s = {
  id_str = s;
  id_ats = attrs;
  id_loc = get_pos ();
}

let mk_qualid l =
  let rec aux l =
    match l with
    | [] -> failwith "mk_qualid"
    | [x] -> Qident x
    | x::r -> Qdot (aux r, x)
  in
  aux (List.rev l)

let mk_qualid' l =
  mk_qualid (List.map (mk_ident []) l)

let mk_expr ?loc e =
  { expr_desc = e; expr_loc = get_pos ?loc () }

let mk_term ?loc t =
  { term_desc = t; term_loc = get_pos ?loc () }

let mk_pat ?loc p =
  { pat_desc = p; pat_loc = get_pos ?loc () }

module Ty = struct
  type t = pty
  let mk_var id = PTtyvar id
  let mk_idapp qid args = PTtyapp (qid, args)
  let mk_atomic_type l = PTtyapp (mk_qualid' l, [])
  let mk_tuple args = PTtuple args
  let mk_ref args = PTref args
  let mk_arrow t1 t2 = PTarrow (t1, t2)
  let mk_scope qid t = PTscope (qid, t)
  let mk_paren t = PTparen t
  let mk_pure t = PTpure t
end

(** Constructors that are shared between expressions and terms *)
module type E_or_T = sig
  type t (* Ptree.expr or Ptree.term *)
  val target : [`Expr|`Term]
  val mk_const : ?loc:Loc.position -> Constant.constant -> t
  val mk_idapp : ?loc:Loc.position -> qualid -> t list -> t
  val mk_apply : ?loc:Loc.position -> t -> t -> t
  val mk_var : ?loc:Loc.position -> qualid -> t
  val mk_cast : ?loc:Loc.position -> t -> pty -> t
  val mk_case : ?loc:Loc.position -> t -> (pattern * t) list -> t
  val mk_tuple : ?loc:Loc.position -> t list -> t
  val mk_record : ?loc:Loc.position -> (qualid * t) list -> t
  val mk_update : ?loc:Loc.position -> t -> (qualid * t) list -> t
  val mk_binop : ?loc:Loc.position -> t -> [`And_asym|`Or_asym] -> t -> t
  val mk_not : ?loc:Loc.position -> t -> t
  val mk_infix : ?loc:Loc.position -> t -> ident -> t -> t
  val mk_innfix : ?loc:Loc.position -> t -> ident -> t -> t
  val mk_let : ?loc:Loc.position -> ident -> t -> t -> t
  val mk_scope : ?loc:Loc.position -> qualid -> t -> t
  val mk_if : ?loc:Loc.position -> t -> t -> t -> t
  val mk_truth : ?loc:Loc.position -> bool -> t
  val mk_attr : ?loc:Loc.position -> attr -> t -> t
  val mk_attrs : ?loc:Loc.position -> attr list -> t -> t
  val expr_or_term : ?expr:(unit -> expr) -> ?term:(unit -> term) -> unit -> t
end

module P = struct
  let mk = mk_pat
  let mk_wild ?loc () = mk ?loc Pwild
  let mk_var ?loc id = mk ?loc (Pvar id)
end

module E = struct
  type t = expr
  let target = `Expr
  let mk = mk_expr
  let mk_assert ?loc kind t =
    mk ?loc (Eassert (kind, t))
  let mk_const ?loc i = mk ?loc (Econst i)
  let mk_idapp ?loc f li = mk ?loc (Eidapp (f, li))
  let mk_apply ?loc e1 e2 = mk ?loc (Eapply (e1, e2))
  let mk_var ?loc x = mk ?loc (Eident x)
  let mk_cast ?loc e pty = mk ?loc (Ecast (e, pty))
  let mk_tuple ?loc es = mk ?loc (Etuple es)
  let mk_case ?loc e cases = mk ?loc (Ematch (e, cases, []))
  let mk_record ?loc fields = mk ?loc (Erecord fields)
  let mk_update ?loc e fields = mk ?loc (Eupdate (e, fields))
  let mk_not ?loc e = mk ?loc (Enot e)
  let mk_if ?loc e1 e2 e3 = mk ?loc (Eif (e1, e2, e3))
  let mk_binop ?loc e1 op e2 =
    mk ?loc
      (match op with
        | `And_asym -> Eand (e1, e2)
        | `Or_asym -> Eor (e1, e2))
  let mk_seq ?loc e1 e2 =
    mk ?loc (Esequence (e1, e2))
  let mk_infix ?loc e1 op e2 =
    mk ?loc (Einfix (e1, op, e2))
  let mk_innfix ?loc e1 op e2 =
    mk ?loc (Einnfix (e1, op, e2))
  let mk_let ?loc id e1 e2 =
    mk ?loc (Elet (id, false, Expr.RKnone, e1, e2))
  let mk_scope ?loc qid e =
    mk ?loc (Escope (qid, e))
  let mk_any ?loc params kind res_pty pat mask spec =
    mk ?loc (Eany (params, kind, res_pty, pat, mask, spec))
  let mk_fun ?loc binders res_pty pat mask spec expr =
    mk ?loc (Efun (binders, res_pty, pat, mask, spec, expr))
  let mk_truth ?loc b = mk ?loc (if b then Etrue else Efalse)
  let mk_attr ?loc a e = mk ?loc (Eattr (a, e))
  let mk_attrs ?loc = List.fold_right (mk_attr ?loc)
  let mk_match ?loc e regs exns = mk ?loc (Ematch (e, regs, exns))
  let mk_raise ?loc qid opt_e = mk ?loc (Eraise (qid, opt_e))
  let mk_while ?loc cond inv var body = mk ?loc (Ewhile (cond, inv, var, body))
  let mk_assign ?loc e1 qid_opt e2 =
    mk ?loc (Eassign [e1, qid_opt, e2])
  let mk_absurd ?loc () =
    mk ?loc Eabsurd
  let expr_or_term ?(expr:(unit -> expr) option) ?term:(_:(unit -> term) option) () : expr =
    match expr with
    | Some e -> e ()
    | None -> failwith "expr_or_term: no expr"
end

module T = struct
  type t = term
  let target = `Term

  let operator = function
    | `And_asym -> Dterm.DTand_asym
    | `Or_asym -> Dterm.DTor_asym
    | `And -> Dterm.DTand
    | `Or -> Dterm.DTor
    | `Implies -> Dterm.DTimplies
    | `Iff -> Dterm.DTiff
    | `By -> Dterm.DTby
    | `So -> Dterm.DTso
  let mk = mk_term
  let mk_truth ?loc b = mk ?loc (if b then Ttrue else Tfalse)
  let mk_const ?loc i = mk ?loc (Tconst i)
  let mk_idapp ?loc f li = mk ?loc (Tidapp (f, li))
  let mk_apply ?loc t1 t2 = mk ?loc (Tapply (t1, t2))
  let mk_var ?loc x = mk ?loc (Tident x)
  let mk_cast ?loc t pty = mk ?loc (Tcast (t, pty))
  let mk_tuple ?loc ts = mk ?loc (Ttuple ts)
  let mk_case ?loc t cases = mk ?loc (Tcase (t, cases))
  let mk_record ?loc fields = mk ?loc (Trecord fields)
  let mk_update ?loc t fields = mk ?loc (Tupdate (t, fields))
  let mk_not ?loc t = mk ?loc (Tnot t)
  let mk_if ?loc e1 e2 e3 = mk ?loc (Tif (e1, e2, e3))
  let mk_binop ?loc t1 op t2 =
    mk ?loc (Tbinop (t1, operator op, t2))
  let mk_binnop ?loc t1 op t2 =
    mk ?loc (Tbinnop (t1, operator op, t2))
  let mk_infix ?loc t1 op t2 =
    mk ?loc (Tinfix (t1, op, t2))
  let mk_innfix ?loc t1 op t2 =
    mk ?loc (Tinnfix (t1, op, t2))
  let mk_let ?loc id t1 t2 =
    mk ?loc (Tlet (id, t1, t2))
  let mk_scope ?loc qid e =
    mk ?loc (Tscope (qid, e))
  let mk_attr ?loc a t =
    mk ?loc (Tattr (a, t))
  let mk_attrs ?loc = List.fold_right (mk_attr ?loc)
  let mk_at ?loc t id =
    mk ?loc (Tat (t, id))
  let mk_eps ?loc id pty t =
    mk ?loc (Teps ((id, pty), t))
  let mk_quant ?loc quant binders triggers term =
    mk ?loc (Tquant (quant, binders, triggers, term))
  let name_term name t =
    mk_attr
      (ATstr (Ident.create_attribute ("hyp_name:"^name)))
      t
  let expr_or_term ?expr:(_:(unit -> expr) option) ?(term:(unit -> term) option) () : term =
    match term with
    | Some t -> t ()
    | None -> failwith "expr_or_term: no term"
end

module D = struct
  type t = decl
  let mk_type decls = Dtype decls
  let mk_logic decls = Dlogic decls
  let mk_ind sign decls = Dind (sign, decls)
  let mk_prop kind ident term = Dprop (kind, ident, term)
  let mk_let ident ghost kind expr = Dlet (ident, ghost, kind, expr)
  let mk_rec defs = Drec defs
  let mk_exn id pty mask = Dexn (id, pty, mask)
  let mk_meta ident args = Dmeta (ident, args)
  let mk_cloneexport qid substs = Dcloneexport (qid, substs)
  let mk_useexport qid = Duseexport qid
  let mk_cloneimport ?loc export qid opt_id substs =
    Dcloneimport (get_pos ?loc (), export, qid, opt_id, substs)
  let mk_useimport ?loc export renames =
    Duseimport (get_pos ?loc (), export, renames)
  let mk_import qid = Dimport qid
  let mk_scope ?loc export id decls =
    Dscope (get_pos ?loc (), export, id, decls)
end

let mk_spec ?(pre=[]) ?(post=[]) ?(xpost=[]) ?(reads=[]) ?(writes=[]) ?(alias=[]) ?(variant=[])
    ?checkrw ?(diverge=false) ?(partial=false) () =
  let checkrw = match checkrw with Some x -> x | None -> reads <> [] || writes <> [] || alias <> [] in
  {sp_pre = pre; sp_post = post; sp_xpost = xpost;
   sp_reads = reads; sp_writes = writes; sp_alias = alias; sp_variant = variant;
   sp_checkrw = checkrw; sp_diverge = diverge; sp_partial = partial}

let mk_pos loc =
  ATpos loc

let mk_str s =
  ATstr (Ident.create_attribute s)

let result_ident = mk_ident [] "result"

let requires t =
  T.name_term "Requires" t

let ensures ?loc t =
  let result = mk_ident [] "result" in
  get_pos ?loc (), [P.mk_var result, T.name_term "Ensures" t]
