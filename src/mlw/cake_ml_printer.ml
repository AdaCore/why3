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

module Print = struct

  let print_decl info fmt d = assert false (* TODO *)

end

let print_decl =
  let memo = Hashtbl.create 16 in
  fun pargs ?old ?fname ~flat ({mod_theory = th} as m) fmt d ->
    ignore (old);
    let info = {
      info_syn          = pargs.Pdriver.syntax;
      info_convert      = pargs.Pdriver.converter;
      info_literal      = pargs.Pdriver.literal;
      info_current_th   = th;
      info_current_mo   = Some m;
      info_th_known_map = th.th_known;
      info_mo_known_map = m.mod_known;
      info_fname        = Opt.map Compile.clean_name fname;
      info_flat         = flat;
      info_current_ph   = [];
    } in
    if not (Hashtbl.mem memo d) then begin Hashtbl.add memo d ();
      Print.print_decl info fmt d end

let fg ?fname m =
  let mod_name = m.mod_theory.th_name.id_string in
  let path     = m.mod_theory.th_path in
  (module_name ?fname path mod_name) ^ ".cml"

let () = Pdriver.register_printer "cakeml"
    ~desc:"printer for CakeML code" fg print_decl
