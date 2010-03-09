(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

type loc = Loc.position

type ident = Ptree.ident

type qualid = Ptree.qualid

type cloned = bool

type trule =
  | Rremove of cloned * qualid
  | Rsyntax of qualid * string
  | Rtag    of cloned * qualid * string

type theory_rules = {
  th_name    : qualid;
  th_prelude : string option;
  th_rules   : trule list;
}

type file = {
  f_prelude : string option;
  f_rules   : theory_rules list;
}
