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

type qualid = loc * string list

type cloned = bool

type trule =
  | Rremove of cloned * qualid
  | Rsyntaxty of qualid * string
  | Rsyntaxls of qualid * string
  | Rtagty    of cloned * qualid * string
  | Rtagls    of cloned * qualid * string
  | Rtagpr    of cloned * qualid * string
  | Rprelude of loc * string

type theory_rules = {
  thr_name    : qualid;
  thr_rules   : trule list;
}

type global =
  | Prelude of string
  | Printer of string
  | CallStdin of string
  | CallFile of string
  | RegexpValid of string
  | RegexpInvalid of string
  | RegexpUnknown of string * string
  | RegexpFailure of string * string
  | Filename of string
  | Transforms of (loc * string) list
  | Plugin of (string * string)

type file = {
  f_global : (loc * global) list;
  f_rules  : theory_rules list;
}
