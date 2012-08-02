(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Why3
open Util
open Mlw_module
open Mlw_typing

let debug = Debug.register_flag "print_modules"

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

let library_of_env = Env.register_format "whyml" ["mlw"] read_channel
