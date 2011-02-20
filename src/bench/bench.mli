(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

open Why
open Env
open Theory
open Task
open Trans
open Driver
open Call_provers
open Scheduler


val maximum_running_proofs: int ref
(** bound on the number of prover processes running in parallel.
    default is 2 *)

type 'a tool = {
  tval     : 'a;
  ttrans   : task trans;
  tdriver  : driver;
  tcommand : string;
  tenv     : env;        (** Allow to compare axiomatic easily *)
  tuse     : task;
  ttime    : int;
  tmem     : int;
}

type 'a prob = {
  ptask  : env -> task -> ('a * task) list; (** needed for tenv and tuse *)
  ptrans : env -> task list trans; (** perhaps should be merged in
                                       ptask *)
}

type why_result =
  | InternalFailure of exn
  | Done of prover_result

val print_why_result : Format.formatter -> why_result -> unit

type ('a,'b) result = {tool   : 'a;
                       prob   : 'b;
                       task   : Decl.prsymbol;
                       idtask : int;
                       result : why_result}

type ('a,'b) callback = 'a -> 'b -> task -> int -> why_result -> unit

val all_list_tp :
  ?callback:('a,'b) callback ->
  'a tool list -> 'b prob list -> ('a,'b) result list

val all_list_pt :
  ?callback:('a,'b) callback ->
  'a tool list -> 'b prob list -> ('a,'b) result list

val all_array :
  ?callback:('a,'b) callback ->
  'a tool array -> 'b prob array -> ('a,'b) result list array array

val any :
  ?callback:('a,'b) callback ->
  ('a tool * 'b prob) list -> ('a,'b) result list


val all_list_tools :
  ?callback:('a,'b) callback ->
  'a tool list -> 'b prob list -> ('a * ('a,'b) result list) list


type output =
  (** on stdout *)
  |Average of string
  |Timeline of string
  (** In a file *)
  |Csv of string

type ('a,'b) bench =
    {
      bname  : string;
      btools : 'a tool list;
      bprobs : 'b prob list;
      boutputs : output list;
    }

val run_bench :
  ?callback:('a,'b) callback -> ('a,'b) bench  -> ('a,'b) result list


val run_benchs :
  ?callback:('a,'b) callback -> ('a,'b) bench list ->
  (('a,'b) bench * ('a,'b) result list) list

val run_benchs_tools :
  ?callback:('a,'b) callback -> ('a,'b) bench list ->
  (('a,'b) bench * ('a * ('a,'b) result list) list) list


type nb_avg = int * float

val print_nb_avg : Format.formatter -> nb_avg -> unit

type tool_res =
    { valid : nb_avg;
      timeout : nb_avg;
      unknown : nb_avg;
      invalid : nb_avg;
      failure : nb_avg}

val print_tool_res : Format.formatter -> tool_res -> unit

val compute_average : ('a,'b) result list -> tool_res
val compute_timeline :
  float -> float -> float -> ('a,'b) result list -> int list

val filter_timeline : ('a,'b) result list -> ('a,'b) result list

val max_time : ('a,'b) result list -> float

open Format

val print_csv :
  ('b -> 'b -> int)         ->
  (formatter -> 'a -> unit) ->
  (formatter -> 'b -> unit) ->
  formatter ->
  ('a * ('a,'b) result list) list -> unit

val print_output :
  ('b -> 'b -> int)         ->
  (formatter -> 'a -> unit) ->
  (formatter -> 'b -> unit) ->
  ('a,'b) bench * ('a * ('a,'b) result list) list -> unit
