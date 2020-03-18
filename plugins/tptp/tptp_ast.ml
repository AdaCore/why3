(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type loc = Why3.Loc.position

type atomic_word = string
type variable = string
type distinct = string

type defined_type =
  | DTtype   | DTprop   | DTuniv   | DTint
  | DTrat    | DTreal   | DTdummy (* placeholder *)

type defined_func =
  | DFumin   | DFsum    | DFdiff   | DFprod
  | DFquot   | DFquot_e | DFquot_t | DFquot_f
  | DFrem_e  | DFrem_t  | DFrem_f
  | DFfloor  | DFceil   | DFtrunc  | DFround
  | DFtoint  | DFtorat  | DFtoreal

type defined_pred =
  | DPtrue   | DPfalse  | DPdistinct
  | DPless   | DPlesseq | DPgreater | DPgreatereq
  | DPisint  | DPisrat

type defined_word =
  | DT of defined_type
  | DF of defined_func
  | DP of defined_pred

(** Formula *)

type binop =
  | BOequ | BOnequ | BOimp  | BOpmi
  | BOand | BOor   | BOnand | BOnor

type quant = Qforall | Qexists

type num_integer = string
type num_rational = string * string
type num_real = string * string option * string option

type number =
  | Nint  of num_integer
  | Nrat  of num_rational
  | Nreal of num_real

type expr = { e_node : expr_node ; e_loc : loc }

and expr_node =
  | Elet of expr * expr
  | Eite of expr * expr * expr
  | Eqnt of quant * tyvar list * expr
  | Ebin of binop * expr * expr
  | Enot of expr
  | Eequ of expr * expr
  | Eapp of atomic_word * expr list
  | Edef of defined_word * expr list
  | Evar of variable
  | Edob of distinct
  | Enum of number

and tyvar = variable * expr

type top_type = tyvar list * (expr list * expr)

type top_formula =
  | LogicFormula of expr
  | TypedAtom of atomic_word * top_type
  | Sequent of expr list * expr list

(** Top level *)

type kind = TFF | FOF | CNF

type name = string
type file = string

type role =
  | Axiom | Hypothesis | Definition  | Assumption | Corollary
  | Lemma | Theorem    | Conjecture  | Negated_conjecture | Type

type input =
  | Formula of kind * name * role * top_formula * loc
  | Include of file * name list * loc

type tptp_file = input list

