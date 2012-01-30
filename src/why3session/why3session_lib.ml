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

open Why3
module S = Session
module C = Whyconf

type spec_list = (Arg.key * Arg.spec * Arg.doc) list

type cmd =
    {
      cmd_spec : spec_list;
      cmd_desc : string;
      cmd_name : string;
      cmd_run  : unit -> unit;
    }

let files = Queue.create ()
let iter_files f = Queue.iter f files
let anon_fun (f:string) = Queue.add f files

let opt_version = ref false

let print_version () =
  Format.printf "Why3 session, version %s (build date: %s)@."
    Config.version Config.builddate

let simple_spec = [
  ("-v", Arg.Set opt_version, " print version information") ;
  Debug.Opt.desc_debug_list;
  Debug.Opt.desc_debug_all;
  Debug.Opt.desc_debug;
]

let read_simple_spec () =
  if !opt_version then begin
    print_version (); exit 0
  end;
  Debug.Opt.set_flags_selected ();
  Debug.Opt.option_list ()



let includes = ref []
let opt_config = ref None
let opt_loadpath = ref []

let env_spec = [
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> Add <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      " same as -L";
]@simple_spec


let read_env_spec () =
  (** Configuration *)
  let config = Whyconf.read_config !opt_config in
  let main = Whyconf.get_main config in
  Whyconf.load_plugins main;
  let loadpath = (Whyconf.loadpath (Whyconf.get_main config))
    @ List.rev !includes in
  let env = Env.create_env loadpath in
  env,config,read_simple_spec ()


let read_update_session ~allow_obsolete env config fname =
  let project_dir = Session.get_project_dir fname in
  let session = Session.read_session project_dir in
  Session.update_session ~keygen:(fun ?parent:_ _ -> ())
    ~allow_obsolete session env config

(** filter *)
type filter_prover =
  | Prover of Whyconf.prover
  | ProverId of string

let filter_prover = Stack.create ()

let read_opt_prover s =
  let sl = Util.split_string_rev s ',' in
  (* reverse order *)
  let prover =
    match sl with
      | [altern;version;name] ->
        Prover {C.prover_name = name; prover_version = version;
                prover_altern = altern}
      | [version;name] ->
        Prover {C.prover_name = name; prover_version = version;
                prover_altern = ""}
      | [id] -> ProverId id
      | _ -> raise (Arg.Bad "--filter-prover [name,version[,alternative]|id]")
  in prover


let add_filter_prover s = Stack.push (read_opt_prover s) filter_prover

let filter_spec =
  ["--filter-prover", Arg.String add_filter_prover,
   " [name,version[,alternative]|id] \
the proof containing this prover will be transformed"]

type filters = C.Sprover.t (* if empty : every provers *)
    (* * ... *)

let prover_of_filter_prover whyconf = function
  | Prover p -> p
  | ProverId id -> (C.prover_by_id whyconf id).C.prover

let read_filter_spec whyconf : filters * bool =
  let should_exit = ref false in
  let s = ref C.Sprover.empty in
  let iter p =
    try
      s := C.Sprover.add (prover_of_filter_prover whyconf p) !s
    with C.ProverNotFound (_,id) ->
      Format.eprintf
        "The prover %s is not found in the configuration file %s@."
        id (Whyconf.get_conf_file whyconf);
      should_exit := true in
  Stack.iter iter filter_prover;
  !s,!should_exit

let session_iter_proof_attempt_by_filter provers f session =
  let iter a = if C.Sprover.mem a.S.proof_prover provers then f a in
  if C.Sprover.is_empty provers
  (** if no prover is filtered then they are all taken *)
  then S.session_iter_proof_attempt f session
  else S.session_iter_proof_attempt iter session
