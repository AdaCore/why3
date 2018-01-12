(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Mlw_module

let debug = Debug.register_info_flag "print_modules"
  ~desc:"Print@ program@ modules@ after@ typechecking."

let read_channel env path file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let inc = Mlw_typing.open_file env path in
  Lexer.parse_program_file inc lb;
  let mm, tm = Mlw_typing.close_file () in
  if path = [] && Debug.test_flag debug then begin
    let add_m _ m modm = Ident.Mid.add m.mod_theory.Theory.th_name m modm in
    let modm = Mstr.fold add_m mm Ident.Mid.empty in
    let print_m _ m = Format.eprintf
      "@[<hov 2>module %a@\n%a@]@\nend@\n@." Pretty.print_th m.mod_theory
      (Pp.print_list Pp.newline2 Mlw_pretty.print_pdecl) m.mod_decls in
    Ident.Mid.iter print_m modm
  end;
  mm, tm

let () = Env.register_format mlw_language "whyml" ["mlw"] read_channel
  ~desc:"WhyML@ programming@ language"
