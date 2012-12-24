(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type loc = Loc.position

type qualid = loc * string list

type cloned = bool

type pty =
  | PTyvar of string
  | PTyapp of qualid * pty list
  | PTuple of pty list

type metarg =
  | PMAty  of pty
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

type global_extract =
  | EPrelude   of string
  | EPrinter   of string
  | EBlacklist of string list

type file_extract = {
  fe_global   : (loc * global_extract) list;
  fe_th_rules : theory_rules list;
  fe_mo_rules : module_rules list;
}
