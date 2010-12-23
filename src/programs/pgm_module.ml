
open Why
open Util
open Ident
open Theory
open Term

open Pgm_types
open Pgm_types.T
open Pgm_ttree

module Mnm = Mstr

type namespace = {
  ns_pr : psymbol   Mnm.t;  (* program symbols *)
  ns_ex : esymbol   Mnm.t;  (* exceptions*)
  ns_mt : mtsymbol  Mnm.t;  (* mutable types *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_pr = Mnm.empty;
  ns_ex = Mnm.empty;
  ns_mt = Mnm.empty;
  ns_ns = Mnm.empty;
}

exception ClashSymbol of string

let ns_replace eq chk x vo vn =
  if not chk then vn else
  if eq vo vn then vo else
  raise (ClashSymbol x)

let ns_union eq chk =
  Mnm.union (fun x vn vo -> Some (ns_replace eq chk x vo vn))

let rec merge_ns chk ns1 ns2 =
  let fusion _ ns1 ns2 = Some (merge_ns chk ns1 ns2) in
  { ns_pr = ns_union p_equal  chk ns1.ns_pr ns2.ns_pr;
    ns_ex = ns_union ls_equal chk ns1.ns_ex ns2.ns_ex;
    ns_mt = ns_union mt_equal chk ns1.ns_mt ns2.ns_mt;
    ns_ns = Mnm.union fusion      ns1.ns_ns ns2.ns_ns; }

let nm_add chk x ns m = Mnm.change x (function
  | None -> Some ns
  | Some os -> Some (merge_ns chk ns os)) m

let ns_add eq chk x v m = Mnm.change x (function
  | None -> Some v
  | Some vo -> Some (ns_replace eq chk x vo v)) m

let pr_add = ns_add p_equal
let ex_add = ns_add ls_equal
let mt_add = ns_add mt_equal

let add_pr chk x ts ns = { ns with ns_pr = pr_add chk x ts ns.ns_pr }
let add_ex chk x ls ns = { ns with ns_ex = ex_add chk x ls ns.ns_ex }
let add_mt chk x mt ns = { ns with ns_mt = mt_add chk x mt ns.ns_mt }
let add_ns chk x nn ns = { ns with ns_ns = nm_add chk x nn ns.ns_ns }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mnm.find a (get_map ns)
  | a::l -> ns_find get_map (Mnm.find a ns.ns_ns) l

let ns_find_pr = ns_find (fun ns -> ns.ns_pr)
let ns_find_ex = ns_find (fun ns -> ns.ns_ex)
let ns_find_mt = ns_find (fun ns -> ns.ns_mt)
let ns_find_ns = ns_find (fun ns -> ns.ns_ns)

(* modules under construction *)

type uc = {
  uc_name   : Ident.ident;
  uc_th     : theory_uc; (* the logic theory used to type annotations *)
  uc_decls  : decl list; (* the program declarations *)
  uc_import : namespace list;
  uc_export : namespace list;
}

let namespace uc = List.hd uc.uc_import
let theory_uc uc = uc.uc_th

let add_pervasives uc =
  (* type unit = () *)
  let ts = 
    Ty.create_tysymbol (id_fresh "unit") [] (Some (Ty.ty_app (Ty.ts_tuple 0) []))
  in
  add_ty_decl uc [ts, Decl.Tabstract]

let create_module n =
  let uc = Theory.create_theory n in
  (* let uc = add_pervasives uc in *)
  { uc_name = id_register n;
    uc_th = uc;
    uc_decls = [];
    uc_import = [empty_ns];
    uc_export = [empty_ns];
  }

let open_namespace uc = match uc.uc_import with
  | ns :: _ -> { uc with
      uc_th     = Theory.open_namespace uc.uc_th;
      uc_import =       ns :: uc.uc_import;
      uc_export = empty_ns :: uc.uc_export; }
  | [] -> assert false

exception NoOpenedNamespace

let close_namespace uc import s =
  match uc.uc_import, uc.uc_export with
  | _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = match s with Some s -> add_ns false s e0 i1 | _ -> i1 in
      let e1 = match s with Some s -> add_ns true  s e0 e1 | _ -> e1 in
      let th = Theory.close_namespace uc.uc_th import s in
      { uc with uc_th = th; uc_import = i1 :: sti; uc_export = e1 :: ste; }
  | [_], [_] -> raise NoOpenedNamespace
  | _ -> assert false

(** Insertion of new declarations *)

let add_symbol add id v uc =
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = add false id.id_string v i0 :: sti;
      uc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_psymbol ps uc =
  add_symbol add_pr ps.p_name ps uc

let add_esymbol ls uc =
  add_symbol add_ex ls.ls_name ls uc

let add_mtsymbol mt uc =
  add_symbol add_mt mt.mt_name mt uc

let add_decl d uc =
  { uc with uc_decls = d :: uc.uc_decls }

let add_logic_decl d uc =
  let th = Typing.with_tuples Theory.add_decl uc.uc_th d in
  { uc with uc_th = th }

(** Modules *)

type t = {
  m_name   : Ident.ident;
  m_th     : theory;
  m_decls  : decl list;
  m_export : namespace;
}

exception CloseModule

let close_module uc = match uc.uc_export with
  | [e] ->
      { m_name = uc.uc_name;
	m_decls = List.rev uc.uc_decls;
	m_export = e;
	m_th = close_theory uc.uc_th; }
  | _ ->
      raise CloseModule

(** Use *)

let use_export uc m =
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = merge_ns false m.m_export i0 :: sti;
      uc_export = merge_ns true  m.m_export e0 :: ste }
  | _ -> assert false

(* parsing LOGIC strings using functions from src/parser/
   requires proper relocation *)

let reloc loc lb =
  lb.Lexing.lex_curr_p <- loc;
  lb.Lexing.lex_abs_pos <- loc.Lexing.pos_cnum + 1

let parse_string f loc s =
  let lb = Lexing.from_string s in
  reloc loc lb;
  f lb

let logic_lexpr ((pos, _), s) =
  parse_string Lexer.parse_lexpr pos s

let parse_logic_decls env ((loc, _), s) uc =
  let parse = Lexer.parse_list0_decl env Theory.Mnm.empty uc.uc_th in
  { uc with uc_th = parse_string parse loc s }




(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
