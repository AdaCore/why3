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

open Ident
open Ity
open Expr

let infer_flag =
  Debug.register_flag "infer:loop" ~desc:"Infer loop invariants"

let print_inferred_invs =
  Debug.register_flag "infer:print_inferred_invs" ~desc:"Print inferred invariant"

let is_infer_attr s = Strings.has_prefix "infer" s || s = "infer"

let attrs_has_infer attrs =
  Sattr.exists (fun a -> is_infer_attr a.attr_string) attrs

let attrs_get_infer attrs =
  let s = Sattr.filter (fun a -> is_infer_attr a.attr_string) attrs in
  Sattr.choose s

type domain = Polyhedra | Box | Oct

let def_domain = Polyhedra
let def_wid = 3

let apply_to_inv = ref (fun _ -> ())

let select_domain_module ?(dom=def_domain) ?(wid=def_wid) env tkn mkn
    : (module Infer_cfg.INFERCFG) =
  let module Infer_why3 =
    Infer_why3.Make(struct
        let       env = env
        let  th_known = tkn
        let mod_known = mkn
      end) in
  let module Infer =
    Infer_cfg.Make (struct
        module Infer_why3 = Infer_why3
        let      widening = wid
      end) in
  match dom with
  | Polyhedra -> (module (Infer(Domain.Polyhedra)))
  | Box -> (module (Infer(Domain.Box)))
  | Oct -> (module (Infer(Domain.Oct)))

let infer_loops ?(dom=def_domain) ?(wid=def_wid) env tkn mkn e cty =
  let module Infer = (val (select_domain_module ~dom ~wid env tkn mkn)) in
  let cfg = Infer.start_cfg () in
  let context = Infer.empty_context () in
  List.iter (Infer.add_variable context) cty.cty_args;
  Mpv.iter (fun pv _ -> Infer.add_variable context pv) cty.cty_effect.eff_reads;
  ignore (Infer.put_expr_with_pre cfg context e cty.cty_pre);
  let (n,h) = Infer.cfg_size cfg in
  Format.eprintf "CFG size: %d nodes, %d hyperedges@." n h;
  let fixp = Infer.eval_fixpoints cfg context in
  let domain2term (e,d) =
    let expl = "infer:inferred with apron" in
    let t    = Infer.domain_to_term cfg context d in
    let t    = Term.t_attr_add (Ident.create_attribute expl) t in
    (e,t) in
  let invs = List.map domain2term fixp in
  !apply_to_inv invs;
  if Debug.test_flag print_inferred_invs then begin
      Format.printf "### Debug: inferred invariants ###@\n";
      let print_i (_,t) = Format.printf "%a@\n" Pretty.print_term t in
      List.iter print_i invs;
      Format.printf "###@."
    end;
  invs

exception Parse_error

let parse_attr a =
  let parse_domain d =
    match String.lowercase_ascii d with
    | "polyhedra" -> Polyhedra
    | "box" -> Box
    | "oct" -> Oct
    | _ -> raise Parse_error in
  let parse_int i =
    try int_of_string i with
    | Failure _ (* "int_of_string" *) -> raise Parse_error in
  let al = String.split_on_char ':' a in
  match al with
  | ["infer"] -> def_domain, def_wid
  | ["infer";x] ->
     begin try parse_domain x, def_wid with
             Parse_error -> def_domain, parse_int x end
  | ["infer";x;y] ->
     begin try parse_domain x, parse_int y with
             Parse_error -> parse_domain y, parse_int x end
  | _ -> raise Parse_error

let infer_loops attrs env tkn mkn e cty =
  if attrs_has_infer attrs then
    let dom, wid =
      let attr = attrs_get_infer attrs in
      try parse_attr attr.attr_string with Parse_error ->
        Loc.warning ?loc:e.e_loc
          "invalid@ infer@ attribute@ (using@ default@ values)";
        def_domain, def_wid in
    infer_loops ~dom ~wid env tkn mkn e cty
  else if Debug.test_flag infer_flag then
    infer_loops env tkn mkn e cty
  else []

let register_hook f = apply_to_inv := f

let () = Vc.set_infer_invs infer_loops
