
open Why
open Util
open Ident
open Theory
open Term

open Pgm_types
open Pgm_types.T
open Pgm_ttree

type namespace = {
  ns_pr : psymbol   Mnm.t;  (* program symbols *)
  ns_ex : esymbol   Mnm.t;  (* exceptions*)
  ns_mt : mtsymbol  Mnm.t;  (* types *)
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
  { ns_pr = ns_union ps_equal chk ns1.ns_pr ns2.ns_pr;
    ns_ex = ns_union ls_equal chk ns1.ns_ex ns2.ns_ex;
    ns_mt = ns_union mt_equal chk ns1.ns_mt ns2.ns_mt;
    ns_ns = Mnm.union fusion      ns1.ns_ns ns2.ns_ns; }

let nm_add chk x ns m = Mnm.change x (function
  | None -> Some ns
  | Some os -> Some (merge_ns chk ns os)) m

let ns_add eq chk x v m = Mnm.change x (function
  | None -> Some v
  | Some vo -> Some (ns_replace eq chk x vo v)) m

let pr_add = ns_add ps_equal
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
  uc_impure : theory_uc; (* the theory used for program types *)
  uc_effect : theory_uc; (* the theory used for typing effects *)
  uc_pure   : theory_uc; (* the logic theory used to type annotations *)
  uc_decls  : decl list; (* the program declarations *)
  uc_import : namespace list;
  uc_export : namespace list;
}

let namespace uc = List.hd uc.uc_import
let impure_uc uc = uc.uc_impure
let effect_uc uc = uc.uc_effect
let pure_uc   uc = uc.uc_pure

let add_pervasives uc =
  (* type unit = () *)
  let ts = 
    Ty.create_tysymbol 
      (id_fresh "unit") [] (Some (Ty.ty_app (Ty.ts_tuple 0) []))
  in
  add_ty_decl uc [ts, Decl.Tabstract]

let open_namespace uc = match uc.uc_import with
  | ns :: _ -> { uc with
      uc_impure = Theory.open_namespace uc.uc_impure;
      uc_effect = Theory.open_namespace uc.uc_effect;
      uc_pure   = Theory.open_namespace uc.uc_pure;
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
      let ith = Theory.close_namespace uc.uc_impure import s in
      let eth = Theory.close_namespace uc.uc_effect import s in
      let pth = Theory.close_namespace uc.uc_pure   import s in
      { uc with uc_impure = ith; uc_effect = eth; uc_pure = pth;
	        uc_import = i1 :: sti; uc_export = e1 :: ste; }
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
  add_symbol add_pr (ps_name ps) ps uc

let add_esymbol ls uc =
  add_symbol add_ex ls.ls_name ls uc

let add_decl d uc =
  { uc with uc_decls = d :: uc.uc_decls }

let add_pure_decl d uc =
  let th = Typing.with_tuples Theory.add_decl uc.uc_pure d in
  { uc with uc_pure = th }

let add_effect_decl d uc =
  let th = Typing.with_tuples Theory.add_decl uc.uc_effect d in
  { uc with uc_effect = th }

let add_mtsymbol mt uc =
  (***
  (* added in the logic as an abstract type *)
  let uc = 
    let d = Decl.create_ty_decl [mt.mt_abstr, Decl.Tabstract] in
    add_logic_decl d uc 
  in
  ***)
  add_symbol add_mt mt.mt_impure.Ty.ts_name mt uc

(***
let add_rtsymbol rt uc =
  (* added in the logic as an abstract type *)
  let uc = 
    let d = Decl.create_ty_decl [rt.rt_abstr, Decl.Tabstract] in
    add_logic_decl d uc 
  in
  add_symbol add_rt rt.rt_name rt uc
***)

let ls_Exit = create_lsymbol (id_fresh "%Exit") [] (Some ty_exn)

let create_module n =
  let m = { 
    uc_name = id_register n;
    uc_impure = Theory.create_theory n;
    uc_effect = Theory.create_theory n;
    uc_pure = Theory.create_theory n;
    uc_decls = [];
    uc_import = [empty_ns];
    uc_export = [empty_ns]; } 
  in
  (* pervasives *)
  let m = add_esymbol  ls_Exit    m in
  (***
  let m = add_mtsymbol mt_ghost   m in
  let m = add_psymbol  ps_ghost   m in
  let m = add_psymbol  ps_unghost m in
  ***)
  m

(** Modules *)

type t = {
  m_name   : Ident.ident;
  m_impure : theory;
  m_effect : theory;
  m_pure   : theory;
  m_decls  : decl list;
  m_export : namespace;
}

exception CloseModule

let close_module uc = match uc.uc_export with
  | [e] ->
      { m_name = uc.uc_name;
	m_decls = List.rev uc.uc_decls;
	m_export = e;
	m_impure = close_theory uc.uc_impure; 
	m_effect = close_theory uc.uc_effect; 
	m_pure = close_theory uc.uc_pure; 
      }
  | _ ->
      raise CloseModule

(** Use *)

let use_export uc m =
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = merge_ns false m.m_export i0 :: sti;
      uc_export = merge_ns true  m.m_export e0 :: ste;
      uc_impure = Theory.use_export uc.uc_impure m.m_impure; 
      uc_effect = Theory.use_export uc.uc_effect m.m_effect; 
      uc_pure   = Theory.use_export uc.uc_pure   m.m_pure; }
  | _ -> assert false

let use_export_theory uc th =
  let uc =
    { uc with 
	uc_impure = Theory.use_export uc.uc_impure th;
	uc_effect = Theory.use_export uc.uc_effect th;
	uc_pure   = Theory.use_export uc.uc_pure   th; }
  in
  (* all type symbols from th are added as (pure) mtsymbols *)
  let add _ ts uc = 
    add_mtsymbol 
      (create_mtsymbol ~impure:ts ~effect:ts ~pure:ts ~singleton:false) uc 
  in
  let rec add_ns ns uc =
    let uc = Mnm.fold add ns.Theory.ns_ts uc in
    Mnm.fold (fun _ -> add_ns) ns.Theory.ns_ns uc
  in
  add_ns th.th_export uc

let add_impure_typedecl env d uc =
  { uc with uc_impure = 
      Typing.add_decl env Mnm.empty uc.uc_impure (Ptree.TypeDecl d) }

let add_effect_typedecl env d uc =
  { uc with uc_effect = 
      Typing.add_decl env Mnm.empty uc.uc_effect (Ptree.TypeDecl d); }

let add_pure_pdecl env ltm d uc =
  { uc with uc_pure = Typing.add_decl env ltm uc.uc_pure d; }

let add_pdecl env ltm d uc =
  { uc with 
      uc_impure = Typing.add_decl env ltm uc.uc_impure d;
      uc_effect = Typing.add_decl env ltm uc.uc_effect d;
      uc_pure   = Typing.add_decl env ltm uc.uc_pure   d; }


(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
