(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
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

let mk_expr ~loc d =
  { expr_desc = d; expr_loc = loc }

let mk_unit ~loc =
  mk_expr ~loc (Etuple [])

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
  Format.pp_print_string fmt id.id_str

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
     Format.pp_print_string fmt "<unknown pp_pty>"

let divergent_attr = ATstr (Ident.create_attribute "vc:divergent")

exception CFGError of string

let () = Exn_printer.register (fun fmt exn -> match exn with
  | CFGError msg -> Format.fprintf fmt "CFG translation error: %s" msg
  | _ -> raise exn)

let translate_cfg preconds block (blocks : (label * block) list) =
  let blocks =
    List.fold_left
      (fun acc (l,b) -> Wstdlib.Mstr.add l.id_str b acc)
      Wstdlib.Mstr.empty
      blocks
  in
  let thestartlabel = "start" in
  let visited_entry_points = ref [thestartlabel] in
  let funs = ref [] in

  let rec translate_term startlabel visited_terms (t : cfg_term) : Ptree.expr =
    let loc = t.cfg_term_loc in
    if List.memq t visited_terms then
      begin
        let msg = "cycle without invariant" in
        let msg = if startlabel = thestartlabel then msg else
                   msg ^ " starting from `" ^ startlabel ^ "`"
        in
        raise (Loc.Located(loc,CFGError msg))
      end;
    match t.cfg_term_desc with
    | CFGgoto l -> translate_goto startlabel (t :: visited_terms) l
    | CFGreturn e -> e
    | CFGabsurd -> mk_expr ~loc:t.cfg_term_loc Eabsurd
    | CFGswitch(e,cases) ->
      let branches =
        List.map
          (fun (pat, l) ->
            let e = translate_term startlabel (t :: visited_terms) l in
            (pat,e))
          cases
      in
      mk_expr ~loc (Ematch(e,branches,[]))
  and translate_goto startlabel visited_terms (l : label) : Ptree.expr =
    let bl =try
      Wstdlib.Mstr.find l.id_str blocks
    with Not_found ->
      raise (Loc.Located(l.id_loc,CFGError ("label " ^ l.id_str ^ " not found for goto")))
    in
    traverse_block startlabel visited_terms bl
  and traverse_block startlabel visited_terms (blk : block) : Ptree.expr =
    let (instrs, term ) = blk in
    begin match instrs with
    | [] -> translate_term startlabel visited_terms term
    | i :: rem ->
       let loc = i.cfg_instr_loc in
       let traverse_block = traverse_block startlabel visited_terms in
       begin match i.cfg_instr_desc, rem with
       | CFGinvariant l1, { cfg_instr_desc = CFGinvariant l2 } :: rem ->
          traverse_block ({ i with cfg_instr_desc = CFGinvariant (l1 @ l2)}:: rem, term)
       | CFGinvariant l, _ ->
          let id =
            match l with
            | [] -> assert false
            | (id,_)::_ -> id
          in
          let l = List.map
                (fun (id,t) ->
                  let attr = ATstr (Ident.create_attribute ("hyp_name:" ^ id.id_str)) in
                  (* TODO : add also an "expl:" *)
                  { t with term_desc = Tattr(attr,t) })
                l
          in
          if not (List.mem id.id_str !visited_entry_points) then
            begin
              visited_entry_points := id.id_str :: !visited_entry_points;
              traverse_from_entry_point id.id_str l (rem, term)
            end;
          let k =
            mk_expr ~loc (Eidapp(Qident (mk_id ~loc ("_from_" ^ id.id_str)),[mk_unit ~loc]))
          in
          List.fold_right
            (fun t acc ->
              let e = mk_check ~loc:t.term_loc t in
              mk_seq ~loc e acc)
            l
            k
       | CFGexpr e1,_ ->
          let e2 = traverse_block (rem, term) in
          mk_seq ~loc e1 e2
        end
    end
  and traverse_from_entry_point startlabel preconds (block : block) =
    let e = traverse_block startlabel [] (block : block) in
    funs := (startlabel, preconds, e) :: !funs
  in

  traverse_from_entry_point thestartlabel preconds (block : block);
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


let translate_cfg_fundef (id,args,retty,pat,mask,spec,locals,block,blocks) =
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
  (id,false,Expr.RKnone, args, Some retty, pat, mask, spec, body)

let translate_letcfg d =
  let loc = Loc.dummy_position in
  let (id, ghost, rk, args, retty, pat, mask, spec, body) = translate_cfg_fundef d in

  Dlet (id, ghost, rk, mk_expr ~loc (Efun (args, retty, pat, mask, spec, body)))

let translate_reccfg ds =
  let translated_fundefs = List.map translate_cfg_fundef ds in

  Drec translated_fundefs

(* mk_expr ~loc:id.id_loc *)
let rec translate_decl d acc =
  match d with
  | Dmlw_decl d -> d :: acc
  | Dletcfg d -> (translate_letcfg d)::acc
  | Dreccfg l -> translate_reccfg l :: acc
  | Cfg_ast.Dscope (l, b, i, ds) -> Ptree.Dscope (l, b, i, List.fold_right translate_decl ds []) :: acc

let translate (m,dl) =
  (m,List.fold_right translate_decl dl [])

let read_channel env _path file c =
  let f : Cfg_ast.cfg_file = Cfg_lexer.parse_channel file c in
  let ptree = Modules (List.map translate f) in
  Debug.dprintf debug "%a@." (Mlw_printer.pp_mlw_file ~attr:true) ptree;
  let mm = Typing.type_mlw_file env [] (file ^ ".mlw") ptree in
  mm

let () =
  Env.register_format mlw_language "mlcfg" ["mlcfg"] read_channel
    ~desc:"whyml extending with functions implemented by control-flow-graphs"
