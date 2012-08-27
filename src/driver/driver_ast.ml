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

type loc = Loc.position

type qualid = loc * string list

type cloned = bool

type metarg =
  | PMAts  of qualid
  | PMAfs  of qualid
  | PMAps  of qualid
  | PMApr  of qualid
  | PMAstr of string
  | PMAint of int

type th_rule =
  | Rprelude  of string
  | Rsyntaxts of cloned * qualid * string
  | Rsyntaxfs of cloned * qualid * string
  | Rsyntaxps of cloned * qualid * string
  | Rremovepr of cloned * qualid
  | Rmeta     of cloned * string * metarg list

type theory_rules = {
  thr_name  : qualid;
  thr_rules : (loc * th_rule) list;
}

type mo_rule =
  | MRtheory    of th_rule
  | MRexception of cloned * qualid * string
  | MRval       of cloned * qualid * string

type module_rules = {
  mor_name  : qualid;
  mor_rules : (loc * mo_rule) list;
}

type global =
  | Prelude of string
  | Printer of string
  | RegexpValid of string
  | RegexpInvalid of string
  | RegexpTimeout of string
  | RegexpOutOfMemory of string
  | RegexpUnknown of string * string
  | RegexpFailure of string * string
  | TimeRegexp of string
  | ExitCodeValid of int
  | ExitCodeInvalid of int
  | ExitCodeTimeout of int
  | ExitCodeOutOfMemory of int
  | ExitCodeUnknown of int * string
  | ExitCodeFailure of int * string
  | Filename of string
  | Transform of string
  | Plugin of (string * string)
  | Blacklist of string list

type file = {
  f_global : (loc * global) list;
  f_rules  : theory_rules list;
}

type file_extract = {
  fe_global   : (loc * global) list;
  fe_th_rules : theory_rules list;
  fe_mo_rules : module_rules list;
}
