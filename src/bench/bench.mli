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


type ('a,'b) result = {tool   : 'a;
                       prob   : 'b;
                       task   : task;
                       idtask : int;
                       result : prover_result}

type ('a,'b) callback = 'a -> 'b -> task -> int -> proof_attempt_status -> unit

val all_list :
  ?callback:('a,'b) callback ->
  'a tool list -> 'b prob list -> ('a,'b) result list

val all_array :
  ?callback:('a,'b) callback ->
  'a tool array -> 'b prob array -> ('a,'b) result list array array

val any :
  ?callback:('a,'b) callback ->
  ('a tool * 'b prob) list -> ('a,'b) result list
