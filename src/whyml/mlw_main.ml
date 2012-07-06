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

let read_channel env path file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let ml = Lexer.parse_program_file lb in
  if Debug.test_flag Typing.debug_parse_only then
    Mstr.empty, Mstr.empty
  else
    let mm, tm =
      List.fold_left (add_theory_module env path) (Mstr.empty, Mstr.empty) ml
    in
    Mstr.iter (fun _ m ->
      Format.fprintf Format.err_formatter
        "@[<hov 2>module %a@\n%a@]@\nend@." Pretty.print_th m.mod_theory
        (Pp.print_list Pp.newline2 Mlw_pretty.print_pdecl) m.mod_decls;
      Format.pp_print_newline Format.err_formatter ()) mm;
    mm, tm

let library_of_env = Env.register_format "whyml-exp" ["mlx"] read_channel
