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

open Cfg_paths
open Cfg_ast
open Why3
open Pmodule
open Ptree

let has_stackify = ref false
let stackify = ref (fun _ -> failwith "stackify not compiled. Install `ocamlgraph` to enable.")

let set_stackify f =
  stackify := f;
  has_stackify := true

let stackify_attr = Ident.create_attribute "cfg:stackify"
let subregion_attr = Ident.create_attribute "cfg:subregion_analysis"

let has_attr id attr =
  List.exists (function ATstr a -> Ident.attr_equal a attr | _ -> false) id.id_ats

let translate_cfg_fundef (cf : cfg_fundef) =
  if has_attr cf.cf_name stackify_attr
  then !stackify cf else Cfg_paths.translate_cfg_fundef cf

let translate_letcfg d =
  let loc = Loc.dummy_position in
  let (id, ghost, rk, args, retty, pat, mask, spec, body) = translate_cfg_fundef d in
  let r =
    Dlet (id, ghost, rk, Ptree_helpers.expr ~loc (Efun (args, retty, pat, mask, spec, body)))
  in
  Debug.dprintf Cfg_paths.debug "%a@." (Mlw_printer.pp_decl ~attr:true) r;
  r

let translate_reccfg ds =
  let translated_fundefs = List.map translate_cfg_fundef ds in
  Drec translated_fundefs

let rec translate_decl d acc =
  match d with
  | Dmlw_decl d -> d :: acc
  | Dletcfg d -> translate_letcfg d :: acc
  | Dreccfg l -> translate_reccfg l :: acc
  | Cfg_ast.Dscope (l, b, i, ds) ->
      Ptree.Dscope (l, b, i, List.fold_right translate_decl ds []) :: acc

let translate (m, dl) = (m, List.fold_right translate_decl dl [])

module Typing = struct
  open Theory
  open Pmodule
  open Typing
  open Wstdlib
  open Ident

  let update_any kind e =
    match e.expr_desc with
    | Ptree.Eany (pl, _, pty, pat, msk, sp) ->
        { e with expr_desc = Ptree.Eany (pl, kind, pty, pat, msk, sp) }
    | _ -> e

  let add_decl muc env file d =
    let vc = muc.muc_theory.uc_path = [] && Debug.test_noflag debug_type_only in
    match d with
    | Ptree.Dlet (id, gh, kind, e) ->
        let e = update_any kind e in
        let ld = (Unsafe.create_user_prog_id id, gh, kind, Unsafe.dexpr muc Dexpr.denv_empty e) in
        let ld = Dexpr.let_defn ~keep_loc:true ld in
        let ld =
          if has_attr id subregion_attr then Subregion_analysis.transform_letdefn muc ld else ld
        in
        add_pdecl ~vc muc (Pdecl.create_let_decl ld)
    | Ptree.Drec fdl ->
        let fst = List.hd fdl in
        let (id, _, _ ,_ , _, _, _ , _ , _) = fst in
        let _, rd = Unsafe.drec_defn muc Dexpr.denv_empty fdl in
        let rd = Dexpr.rec_defn ~keep_loc:true rd in
        let rd =
          if has_attr id subregion_attr then Subregion_analysis.transform_letdefn muc rd else rd
        in
        add_pdecl ~vc muc (Pdecl.create_let_decl rd)
    | _ -> Unsafe.add_decl muc env file d

  let type_module file env loc path (id, dl) =
    let muc = create_module env ~path (Unsafe.create_user_id id) in
    (* Technically, `add_pdecl` will do this, but if we don't do it upfront it breaks
         the sub-region analysis (name tbd) as we won't have imported ref. Since mlcfg always
       uses refs, we just import it straight up *)
    let muc = use_export muc ref_module in
    let add_decl_env_file muc d = add_decl muc env file d in
    let muc = List.fold_left add_decl_env_file muc dl in
    let m = Loc.try1 ~loc Pmodule.close_module muc in
    let file = Mstr.add m.mod_theory.th_name.id_string m file in
    file

  let type_mlw_file env path filename mlw_file =
    if Debug.test_flag Glob.flag then Glob.clear filename;
    let file = Mstr.empty in
    let loc = Loc.user_position filename 0 0 0 0 in
    let file =
      match mlw_file with
      | Ptree.Decls decls ->
          type_module file env loc path (Ptree.{ id_str = ""; id_ats = []; id_loc = loc }, decls)
      | Ptree.Modules m_or_t ->
          let type_module_env_loc_path file (id, dl) = type_module file env loc path (id, dl) in
          List.fold_left type_module_env_loc_path file m_or_t
    in
    file
end

let read_channel env _path file c =
  let f : Cfg_ast.cfg_file = Cfg_lexer.parse_channel file c in
  let ptree = Modules (List.map translate f) in
  Debug.dprintf debug "%a@." (Mlw_printer.pp_mlw_file ~attr:true) ptree;
  let mm = Typing.type_mlw_file env [] (file ^ ".mlw") ptree in
  mm

let () =
  Env.register_format mlw_language "mlcfg" [ "mlcfg"; "stdout" ] read_channel
    ~desc:"whyml extended with functions implemented by control-flow-graphs"
