(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

type atomic_word = string
type variable = string
type distinct = string

(** TFF type *)

type defined_type =
  | DTtype | DTprop | DTuniv
  | DTint  | DTrat  | DTreal
  | DTunknown of string

type tff_type_node =
  | TVar of variable
  | TConstr of atomic_word * tff_type list
  | TDef of defined_type

and tff_type = { ty_node : tff_type_node ; ty_loc : loc }

type top_type = variable list * tff_type list * tff_type

(** Formula *)

type binop = BOequ | BOimp | BOpmi | BOand | BOor | BOnand | BOnor

type quant = Qforall | Qexists

type tyvar = variable * tff_type

type defined_pred =
  | DPtrue  | DPfalse  | DPdistinct
  | DPless  | DPlesseq | DPgreater | DPgreatereq
  | DPisint | DPisrat  | DPequal   | DPnoneq
  | DPunknown of string

type defined_func =
  | DFumin   | DFsum    | DFdiff
  | DFprod   | DFquot
  | DFquot_e | DFquot_t | DFquot_f
  | DFrem_e  | DFrem_t  | DFrem_f
  | DFfloor  | DFceil
  | DFtrunc  | DFround
  | DFtoint  | DFtorat  | DFtoreal
  | DFunknown of string

type num_integer = string
type num_rational = string * string
type num_real = string * string option * string option

type number =
  | Nint of num_integer
  | Nrat of num_rational
  | Nreal of num_real

type formula_node =
  | LFqnt of quant * tyvar list * formula
  | LFbin of binop * formula * formula
  | LFnot of formula
  | LFite of formula * formula * formula
  | LFapp of atomic_word * term list
  | LFdef of defined_pred * term list
  | LFvar of variable

and term_node =
  | LTite of formula * term * term
  | LTapp of atomic_word * term list
  | LTdef of defined_func * term list
  | LTvar of variable
  | LTdob of distinct
  | LTnum of number

and binding_node =
  | LBform of variable * formula
  | LBterm of variable * term
  | LBtype of variable * tff_type

and formula = { f_node : formula_node ; f_loc : loc }
and term    = { t_node : term_node    ; t_loc : loc }
and binding = { b_node : binding_node ; b_loc : loc }

type top_formula =
  | LogicFormula of formula
  | TypedAtom of atomic_word * top_type
  | Sequent of formula list * formula list

(** Top level *)

type kind = TFF | FOF | CNF

type name = string
type file = string

type role =
  | Axiom | Hypothesis | Definition  | Assumption
  | Lemma | Theorem    | Conjecture  | Negated_conjecture
  | Type  | Unknown of string

type input =
  | Formula of kind * name * role * top_formula * loc
  | Include of file * name list * loc

type tptp_file = tptp_input list

