(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Runtime Assertion Checkers for WhyML programs} *)

open Pinterp_core

type oracle_quant_var = env -> Term.vsymbol -> Value.value option
(** An oracle to get all-quantified variables during RAC. Used to progress
    when the transformation ["compute_in_goal"] blocks on a quantifier. *)

val oracle_quant_var_dummy : oracle_quant_var
(** Always returns in [None]. *)

val oracle_quant_var :
  ?bind_univ_quant_vars:bool -> ?bind_univ_quant_vars_default:bool ->
  oracle -> oracle_quant_var
(** Derive an oracle for quantified variables from a normal oracle. *)

(** {1 RAC implementation using a Why3 transformation and prover}

    The RAC implementation is based on a Why3 transformation (usually
    [compute_in_goal]) and a Why3 prover. The procedure to decide (check) a
    term uses three steps, and terminates with the first step that gives a
    definitive answer (i.e. the term is valid or invalid) and progresses with
    the next if a step doesn't yield a definitive answer (the step is
    incomplete for the term).

    {ol
    {- Apply the transformation. The term is valid (resp. invalid) if it is
       reduced to [true] (resp. [false]), and otherwise the step is incomplete.}
    {- Apply the prover. The term is valid (resp. invalid) if the prover shows
       that it is valid (resp. invalid), and otherwise the step is incomplete.}
    {- Apply the prover to the negation of the term. The term is valid (resp.
       invalid) if the prover shows that it is invalid (resp. valid), and
       otherwise the step, and hence the whole procedure, is incomplete.}}
 *)
module Why : sig

  type why_prover = {
    command: string;
    driver: Driver.driver;
    limits: Call_provers.resource_limits;
  }
  (** The configuration of the prover used for reducing terms in RAC *)

  val mk_why_prover :
    command:string -> Driver.driver -> Call_provers.resource_limits -> why_prover

  val mk_check_term :
    ?metas:(Theory.meta * Theory.meta_arg list) list ->
    ?trans:Task.task Trans.tlist ->
    ?why_prover:why_prover ->
    ?oracle_quant_var:oracle_quant_var ->
    config:Whyconf.config ->
    elim_eps:Task.task Trans.trans ->
    unit -> check_term
  (** Metas are applied to all tasks, the tasks are first reduce using [trans],
     and if this is insufficient for deciding the term, checked using
     [why_prover]. The oracle [oracle_quant_var] is used to instantiate
     variables in top-level universal quantifications during reduction with
     [trans]. By default, all arguments are empty or dummy. *)

  val mk_check_term_lit :
    Whyconf.config -> Env.env ->
    ?metas:(string * string option) list ->
    ?trans:string ->
    why_prover:(string * Call_provers.resource_limits) option ->
    ?oracle_quant_var:oracle_quant_var ->
    unit -> check_term
  (** [mk_rac_lit cnf env ?metas ?trans ?prover ?try_negate ()]
      configures the term reduction of RAC. [trans] is the name of a
      transformation ("compute_in_goal" by default). [why_prover] is a
      pair of a prover string (of the command-line shape
      "<provername>,<version>,<alternative>") and a set of resource
      limits.

      If the environment variable [WHY3RACTASKDIR] is set, it is used as a
      directory to print all SMT tasks sent to the RAC prover, if
      [--debug=rac-check-term-sat] is set. *)

  val mk_compute_term :
    ?metas:(Theory.meta * Theory.meta_arg list) list ->
    ?trans:Task.task list Trans.trans ->
    ?oracle_quant_var:oracle_quant_var ->
    unit -> compute_term

  val mk_compute_term_lit :
    Env.env ->
    ?metas:(string * string option) list ->
    ?trans:string ->
    ?oracle_quant_var:oracle_quant_var ->
    unit -> compute_term
  (** Create a [compute_term] function. The transformation [trans] is
      ["compute_in_goal"] by default. *)
end
