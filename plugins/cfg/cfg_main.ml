(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Pmodule
open Cfg_ast
open Ptree

let debug = Debug.register_flag "cfg"
  ~desc:"CFG plugin debug flag"

let unit_type = PTtuple []

let mk_id ~loc name =
  { id_str = name; id_ats = []; id_loc = loc }

let mk_term ~loc d =
  { term_desc = d; term_loc = loc }

let term_true ~loc = mk_term ~loc Ttrue

let term_false ~loc = mk_term ~loc Tfalse

let mk_expr ~loc d =
  { expr_desc = d; expr_loc = loc }

let mk_unit ~loc =
  mk_expr ~loc (Etuple [])

let mk_assert ~loc t =
  mk_expr ~loc (Eassert(Expr.Assert,t))

let mk_check ~loc t =
  mk_expr ~loc (Eassert(Expr.Check,t))

let mk_assume ~loc t =
  mk_expr ~loc (Eassert(Expr.Assume,t))

let mk_seq ~loc e1 e2 = mk_expr ~loc (Esequence(e1,e2))

let mk_pat ~loc d =
  { pat_desc = d; pat_loc = loc }

let pat_wild ~loc = mk_pat ~loc Pwild

let empty_spec = {
  sp_pre     = [];
  sp_post    = [];
  sp_xpost   = [];
  sp_reads   = [];
  sp_writes  = [];
  sp_alias   = [];
  sp_variant = [];
  sp_checkrw = false;
  sp_diverge = false;
  sp_partial = false;
}


let pp_id fmt id =
  Format.fprintf fmt "%s" id.id_str

let rec pp_qid fmt qid =
  match qid with
  | Qident id -> pp_id fmt id
  | Qdot(q,id) -> Format.fprintf fmt "%a.%a" pp_qid q pp_id id

let rec pp_pty fmt t =
  match t with
  | PTtyapp(qid,l) ->
     Format.fprintf fmt "@[%a %a@]"
       pp_qid qid
       (Pp.print_list Pp.semi pp_pty) l
  | _ ->
     Format.fprintf fmt "<unknown pp_pty>"

let divergent_attr = ATstr (Ident.create_attribute "vc:divergent")

let translate_cfg preconds block blocks =
  let blocks =
    List.fold_left
      (fun acc (l,b) -> Wstdlib.Mstr.add l.id_str b acc)
      Wstdlib.Mstr.empty
      blocks
  in
  let startlabel = "start" in
  let visited = ref [startlabel] in
  let funs = ref [] in
  let rec traverse_block bl : Ptree.expr =
    match bl with
    | [] -> mk_unit ~loc:Loc.dummy_position
    | i :: rem ->
       let loc = i.cfg_instr_loc in
       match i.cfg_instr_desc with
       | CFGgoto l ->
          let bl =
            try
              Wstdlib.Mstr.find l.id_str blocks
            with Not_found -> Format.eprintf "Label %a not found for goto@." pp_id l; exit 1
          in
          traverse_block bl
       | CFGinvariant(id,t) ->
          (* TODO: if next instruction is also an invariant, groupe them together *)
          let attr = ATstr (Ident.create_attribute ("hyp_name:" ^ id.id_str)) in
          (* TODO : add also an "expl:" *)
          let t = { t with term_desc = Tattr(attr,t) } in
          let e = mk_check ~loc t in
          let k = mk_expr ~loc (Eidapp(Qident (mk_id ~loc ("_from_" ^ id.id_str)),[mk_unit ~loc])) in
          let e = mk_seq ~loc e k in
          if not (List.mem id.id_str !visited) then
            begin
              visited := id.id_str :: !visited;
              traverse_from_entry_point id.id_str [t] rem
            end;
          e
       | CFGswitch(e,cases) ->
          let branches =
            List.map
              (fun (pat,bl) ->
                let e = traverse_block bl in
                (pat,e))
              cases
          in
          mk_expr ~loc (Ematch(e,branches,[]))
       | CFGexpr e when rem=[] -> e
       | CFGexpr e1 ->
          let e2 = traverse_block rem in
          mk_seq ~loc e1 e2

  and traverse_from_entry_point startlabel preconds block =
    let e = traverse_block block in
    funs := (startlabel, preconds, e) :: !funs

  in

  traverse_from_entry_point startlabel preconds block;
  !funs

let e_ref = mk_expr ~loc:Loc.dummy_position Eref

let declare_local (ghost,id,ty) body =
  let loc = id.id_loc in
  Debug.dprintf debug "declaring local variable %a of type %a@." pp_id id pp_pty ty ;
  let e = Eany([],Expr.RKnone,Some ty,pat_wild ~loc,Ity.MaskVisible,empty_spec) in
  let e = mk_expr ~loc (Eapply(e_ref,mk_expr ~loc e)) in
  let id = { id with id_ats = (ATstr Pmodule.ref_attr) :: id.id_ats } in
  mk_expr ~loc:id.id_loc (Elet(id,ghost,Expr.RKnone,e,body))


let build_path_function retty pat mask postconds (startlabel, preconds, body) : Ptree.fundef =
  let body =
    List.fold_left
      (fun acc t ->
        let loc = t.term_loc in
        let e = mk_assume ~loc t in
        mk_seq ~loc e acc)
      body preconds
  in
  let loc = Loc.dummy_position in
  let spec = { empty_spec with sp_post = postconds} in
  let id = mk_id ~loc ("_from_" ^ startlabel) in
  let arg = (loc,None,false,Some unit_type) in
  (id,false,Expr.RKnone, [arg], Some retty, pat, mask, spec, body)


let translate_letcfg (id,args,retty,pat,mask,spec,locals,block,blocks) =
  Debug.dprintf debug "translating cfg function `%s`@." id.id_str;
  Debug.dprintf debug "return type is `%a`@." pp_pty retty;
  let funs = translate_cfg spec.sp_pre block blocks in
  let loc = Loc.dummy_position in
  let body =
    mk_expr ~loc (Eidapp(Qident (mk_id ~loc "_from_start"),[mk_unit ~loc]))
  in
  let defs =
    List.map (build_path_function retty pat mask spec.sp_post) funs
  in
  let body =
    mk_expr ~loc (Erec(defs,body))
  in
  let body =
    List.fold_right declare_local locals body
  in
  (* ignore termination *)
  let body =
    mk_expr ~loc (Eattr(divergent_attr,body))
  in
  let f =
    Efun(args, Some retty, pat, mask, spec, body)
  in
  Dlet (id,false,Expr.RKnone,mk_expr ~loc:id.id_loc f)

let translate_decl d acc =
  match d with
  | Dmlw_decl d -> d :: acc
  | Dletcfg l -> List.fold_right (fun d acc -> (translate_letcfg d)::acc) l acc

let translate (m,dl) =
  (m,List.fold_right translate_decl dl [])

let read_channel env _path file c =
  let f : Cfg_ast.cfg_file =
    try
      Cfg_lexer.parse_channel file c
    with Loc.Located(loc,e) ->
      Format.eprintf "%a%a@." Loc.report_position loc Exn_printer.exn_printer e;
      exit 1
  in
  Debug.dprintf debug "%s parsed successfully.@." file;
  let ptree = Modules (List.map translate f) in
  let mm = try
      Typing.type_mlw_file env [] (file ^ ".mlw") ptree
    with
      Loc.Located(loc,e) ->
      let msg = Format.asprintf "%a" Exn_printer.exn_printer e in
      Format.eprintf "%a%s@." Loc.report_position loc msg;
      Debug.dprintf debug "%a@."
        (Mlw_printer.with_marker ~msg loc Mlw_printer.pp_mlw_file)
        ptree;
      exit 1
  in
  Debug.dprintf debug "%a@." Mlw_printer.pp_mlw_file ptree;
  mm

let () =
  Env.register_format mlw_language "mlcfg" ["mlcfg"] read_channel
    ~desc:"whyml extending with functions implemented by control-flow-graphs"
