(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Stackify
open Cfg_ast
open Ptree

let warn_deprecated_named_invariant =
    Loc.register_warning "deprecated_named_invariant" "Named invariants in MLCFG are deprecated. Use hyp_name: attribute to provide hypothesis names instead"

let debug = Debug.register_flag "cfg" ~desc:"CFG plugin debug flag"
let unit_type = PTtuple [] [@@warning "-32"]
let mk_id ~loc name = { id_str = name; id_ats = []; id_loc = loc }
let mk_expr ~loc d = { expr_desc = d; expr_loc = loc }
let mk_unit ~loc = mk_expr ~loc (Etuple [])
let mk_check ~loc t = mk_expr ~loc (Eassert (Expr.Check, t)) [@@warning "-32"]
let mk_assume ~loc t = mk_expr ~loc (Eassert (Expr.Assume, t)) [@@warning "-32"]
let mk_seq ~loc e1 e2 = mk_expr ~loc (Esequence (e1, e2))
let mk_pat ~loc d = { pat_desc = d; pat_loc = loc }
let pat_wild ~loc = mk_pat ~loc Pwild

let empty_spec =
  {
    sp_pre = [];
    sp_post = [];
    sp_xpost = [];
    sp_reads = [];
    sp_writes = [];
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
    sp_partial = false;
  }

let pp_id fmt id = Format.pp_print_string fmt id.id_str

let rec pp_qid fmt qid =
  match qid with Qident id -> pp_id fmt id | Qdot (q, id) -> Format.fprintf fmt "%a.%a" pp_qid q pp_id id

let rec pp_pty fmt t =
  match t with
  | PTtyapp (qid, l) -> Format.fprintf fmt "@[%a %a@]" pp_qid qid (Pp.print_list Pp.semi pp_pty) l
  | _ -> Format.pp_print_string fmt "<unknown pp_pty>"

let divergent_attr = ATstr Vc.nt_attr

exception CFGError of string [@@warning "-38"]

let () =
  Exn_printer.register (fun fmt exn ->
      match exn with CFGError msg -> Format.fprintf fmt "CFG translation error: %s" msg | _ -> raise exn)

let mk_loop_continue entry : Ptree.expr = mk_expr ~loc:entry.id_loc (Eraise (Qident entry, None))

let mk_loop_expr entry (invariants : (loop_clause * ident option * term * int option ref) list) (e : Ptree.expr) : Ptree.expr =
  let continue = mk_expr ~loc:Loc.dummy_position (Eoptexn (entry, Ity.MaskVisible, e)) in
  let invariants, variants =
    List.partition_map
      (fun (claus, id, t, _) ->
        if id <> None then
          Loc.warning ~loc:t.term_loc warn_deprecated_named_invariant  "Named invariants are deprecated. Please use the `hyp_name` attribute directly";

        match claus with Invariant -> Either.Left t | Variant -> Either.Right (t, None))
      invariants
  in
  let infinite_loop =
    mk_expr ~loc:entry.id_loc (Ewhile (mk_expr ~loc:Loc.dummy_position Etrue, invariants, variants, continue))
  in
  (* adding a "absurd" after the infinite loop to avoid generation of
     meaningless VCs *)
  let absurd = mk_expr ~loc:Loc.dummy_position Eabsurd in
  mk_expr ~loc:entry.id_loc (Esequence (infinite_loop, absurd))

let mk_scope_break entry ?(loc = entry.id_loc) () = mk_expr ~loc (Eraise (Qident entry, None))

let mk_scope_expr entry inner outer =
  mk_seq ~loc:Loc.dummy_position (mk_expr ~loc:entry.id_loc (Eoptexn (entry, Ity.MaskVisible, inner))) outer

let translate_instr (i : Cfg_ast.cfg_instr) : Ptree.expr =
  match i.cfg_instr_desc with CFGinvariant _inv -> mk_unit ~loc:Loc.dummy_position (* temporary *) | CFGexpr e -> e

let rec translate_term subst (t : Cfg_ast.cfg_term) : Ptree.expr =
  match t.cfg_term_desc with
  | CFGgoto l -> begin
      match List.find_opt (fun (l', _) -> l'.id_str = l.id_str) subst with
      | Some (_, e) -> e
      | _ -> mk_scope_break l ~loc:t.cfg_term_loc ()
    end
  | CFGreturn e -> mk_expr ~loc:t.cfg_term_loc (Eraise (Qident (mk_id ~loc:Loc.dummy_position "Return"), Some e))
  | CFGswitch (e, brs) ->
      (* TODO: why arent we using fall and can we remove it? *)
      let mk_switch _fall branches =
        let branches = List.map (fun (pat, term) -> (pat, translate_term subst term)) branches in
        mk_expr ~loc:t.cfg_term_loc (Ematch (e, branches, []))
      in
      let rec duplicates p xs =
        match xs with x :: xs -> if List.exists (p x) xs then x :: duplicates p xs else duplicates p xs | [] -> []
      in
      let dup_targets = duplicates (fun a b -> a.id_str = b.id_str) (targets t) in
      let here, subst = List.partition (fun (a, _) -> List.exists (fun b -> b.id_str = a.id_str) dup_targets) subst in

      List.fold_left (fun acc (l, e) -> mk_scope_expr l acc e) (mk_switch subst brs) here
  | CFGabsurd -> mk_expr ~loc:t.cfg_term_loc Eabsurd

let translate_block subst (instrs, term) : Ptree.expr =
  List.fold_right (fun i t -> mk_seq ~loc:Loc.dummy_position (translate_instr i) t) instrs (translate_term subst term)

let rec translate_exp subst (es : Stackify.exp_tree) : Ptree.expr =
  match es with
  | Scope (lbl, usage, bound, inner) ->
      (* invariant: a scope must be followed by at least one block *)
      let entry = lbl in
      let outer = translate_exp subst bound in
      (* print_exp_structure' inner; *)
      let scope =
        match usage with
        | One -> translate_exp ((entry, outer) :: subst) inner
        | Multi -> mk_scope_expr entry (translate_exp subst inner) outer
      in
      scope
  | Loop (invs, body) ->
      let label = fst (entry body) in
      let loop_continue = mk_loop_continue label in
      let loop_body = mk_loop_expr label invs (translate_exp [ (label, loop_continue) ] body) in
      List.fold_left (fun acc (l, e) -> mk_scope_expr l acc e) loop_body subst
  | Block (_, blk) -> translate_block subst blk

let translate_cfg block (blocks : (label * block) list) =
  let startlabel = mk_id ~loc:Loc.dummy_position "start" in
  let s = stackify ((startlabel, block) :: blocks) startlabel in
  let e = translate_exp [] s in
  e

let e_ref = mk_expr ~loc:Loc.dummy_position Eref

let declare_local (ghost, id, ty, init) body =
  let loc = id.id_loc in
  Debug.dprintf debug "declaring local variable %a of type %a@." pp_id id pp_pty ty;
  let e : expr =
    match init with
    | Some e -> e
    | None -> mk_expr ~loc (Eany ([], Expr.RKnone, Some ty, pat_wild ~loc, Ity.MaskVisible, empty_spec))
  in
  let e = mk_expr ~loc (Eapply (e_ref, e)) in
  let id = { id with id_ats = ATstr Pmodule.ref_attr :: id.id_ats } in
  mk_expr ~loc:id.id_loc (Elet (id, ghost, Expr.RKnone, e, body))

let translate_cfg_fundef cf =
  Debug.dprintf debug "translating cfg function `%s`@." cf.cf_name.id_str;
  Debug.dprintf debug "return type is `%a`@." pp_pty cf.cf_retty;
  let body = translate_cfg cf.cf_block0 cf.cf_blocks in
  let loc = Loc.dummy_position in
  let body = List.fold_right declare_local cf.cf_locals body in
  let body = mk_seq ~loc body (mk_expr ~loc Eabsurd) in
  let body = mk_expr ~loc (Eoptexn (mk_id ~loc "Return", cf.cf_mask, body)) in
  (* ignore termination *)
  let body = mk_expr ~loc (Eattr (divergent_attr, body)) in
  let body = List.fold_right (fun a e -> mk_expr ~loc (Eattr (a, e))) cf.cf_attrs body in
  (cf.cf_name, false, Expr.RKnone, cf.cf_args, Some cf.cf_retty, cf.cf_pat, cf.cf_mask, cf.cf_spec, body)

open Cfg_main

let () = set_stackify translate_cfg_fundef
