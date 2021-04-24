(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type loc = Loc.position

type qualid = loc * string list

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

(* Extraction preludes and interfaces of a program module
   are flagged with "export" if they should be printed
   in modules that depend on it.
   This flag is ignored by in prover drivers. *)

type export = bool

type th_rule =
  | Rprelude   of string * export
  | Rsyntaxts  of qualid * string * bool
  | Rsyntaxfs  of qualid * string * bool
  | Rsyntaxps  of qualid * string * bool
  | Rliteral   of qualid * string * bool
  | Rremovepr  of qualid
  | Rremoveall
  | Rmeta      of string * metarg list
  | Ruse       of qualid

type theory_rules = {
  thr_name  : qualid;
  thr_rules : (loc * th_rule) list;
}

type mo_rule =
  | MRtheory    of th_rule
  | MRinterface of string * export
  | MRexception of qualid * string
  | MRval       of qualid * string * int list
  | MRnoextract

type module_rules = {
  mor_name  : qualid;
  mor_rules : (loc * mo_rule) list;
}

type global =
  | Prelude of string
  | Printer of string
  | ModelParser of string
  | RegexpValid of string
  | RegexpInvalid of string
  | RegexpTimeout of string
  | RegexpOutOfMemory of string
  | RegexpStepLimitExceeded of string
  | RegexpUnknown of string * string
  | RegexpFailure of string * string
  | TimeRegexp of string
  | StepRegexp of string * int
  | ExitCodeValid of int
  | ExitCodeInvalid of int
  | ExitCodeTimeout of int
  | ExitCodeStepLimitExceeded of int
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
