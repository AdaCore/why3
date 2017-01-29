
open Why3
open Mlw_module
open Ptree
open Stdlib

let debug = Debug.register_flag "mini-python"
  ~desc:"mini-python plugin debug flag"

let read_channel env path file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let f = Loc.with_location (Py_parser.file Py_lexer.next_token) lb in
  Debug.dprintf debug "%s parsed successfully.@." file;
  let file = Filename.basename file in
  let file = Filename.chop_extension file in
  let name = String.capitalize_ascii file in
  Debug.dprintf debug "building module %s.@." name;
  let inc = Mlw_typing.open_file env path in
  let id = { id_str = name; id_lab = []; id_loc = Loc.dummy_position } in
  inc.open_module id;
  (* Typing.add_decl id.id_loc *)
  (*   (Duse (Qdot (Qident (mk_id "ocaml"), mk_id "OCaml") )); *)
  (* Typing.close_scope id.id_loc ~import:true; *)
  (*  List.iter (fun x -> add_decl (loc_of_decl x) x) f; *)
  inc.close_module ();
  let mm, _ as res = Mlw_typing.close_file () in
  if path = [] && Debug.test_flag debug then begin
    let add_m _ m modm = Ident.Mid.add m.mod_theory.Theory.th_name m modm in
    let modm = Mstr.fold add_m mm Ident.Mid.empty in
    let print_m _ m = Format.eprintf
      "@[<hov 2>module %a@\n%a@]@\nend@\n@." Pretty.print_th m.mod_theory
      (Pp.print_list Pp.newline2 Mlw_pretty.print_pdecl) m.mod_decls in
    Ident.Mid.iter print_m modm
  end;
  res

let () =
  Env.register_format mlw_language "python" ["py"] read_channel
    ~desc:"mini-Python format"
