open Cfg_paths
open Cfg_ast
open Why3
open Pmodule
open Ptree

let has_stackify = ref false
let stackify = ref (fun _ -> failwith "stackify is not compiled")

let set_stackify f = stackify := f; has_stackify := true

let stackify_attr = ATstr (Ident.create_attribute "cfg:stackify")

let translate_cfg_fundef (x : cfg_fundef) =
  let (id, _, _, _, _, _, _, _, _) = x in
  if List.exists (function ATstr a -> a.attr_string = "cfg:stackify" | _ -> false) id.id_ats
  then !stackify x else Cfg_paths.translate_cfg_fundef x

let translate_letcfg d =
  let loc = Loc.dummy_position in
  let (id, ghost, rk, args, retty, pat, mask, spec, body) = translate_cfg_fundef d in

  let r = Dlet (id, ghost, rk, mk_expr ~loc (Efun (args, retty, pat, mask, spec, body))) in
  Debug.dprintf debug "%a@." (Mlw_printer.pp_decl ~attr:true) r;
  r

let translate_reccfg ds =
  let translated_fundefs = List.map translate_cfg_fundef ds in

  Drec translated_fundefs

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
  Env.register_format mlw_language "mlcfg" ["mlcfg"; "stdout"] read_channel
    ~desc:"whyml extending with functions implemented by control-flow-graphs"
