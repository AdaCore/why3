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

let read_simple_spec () =
  if !opt_version then begin
    print_version (); exit 0
  end;
  Debug.Opt.set_flags_selected ();
  Debug.Opt.option_list ()



let opt_config = ref None
let opt_loadpath = ref []
let opt_extra = ref []

let common_options = [
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> reads configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      "<file> same as -C";
  "--extra-config", Arg.String (fun s -> opt_extra := !opt_extra @ [s]),
      "<file> reads additional configuration from <file>";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> adds <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> same as -L";
  "-v", Arg.Set opt_version, " prints version information" ;
  Debug.Opt.desc_debug_list;
  Debug.Opt.desc_debug_all;
  Debug.Opt.desc_debug;
]

(* dead code
let env_spec = common_options 
*)

let read_env_spec () =
  (** Configuration *)
  let config = Whyconf.read_config !opt_config in
  let config = List.fold_left Whyconf.merge_config config !opt_extra in
  let main = Whyconf.get_main config in
  Whyconf.load_plugins main;
  let loadpath = (Whyconf.loadpath (Whyconf.get_main config))
    @ List.rev !opt_loadpath in
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
| FilterProver of Whyconf.filter_prover

let filter_prover = Stack.create ()

let read_opt_prover s =
  try
    let l = Util.split_string_rev s ',' in
    match l with
    | [altern;version;name] when List.for_all (fun s -> s.[0] <> '^') l ->
      Prover {Whyconf.prover_name = name;
              prover_version = version;
              prover_altern = altern}
    | _ -> FilterProver (Whyconf.parse_filter_prover s)
  with Whyconf.ParseFilterProver _ ->
    raise (Arg.Bad
             "--filter-prover name[,version[,alternative]|,,alternative] \
                regexp must start with ^")


let add_filter_prover s = Stack.push (read_opt_prover s) filter_prover

type filter_three = | FT_Yes | FT_No | FT_All

let opt_filter_archived = ref FT_No
let opt_filter_obsolete = ref FT_All
let opt_filter_verified_goal = ref FT_All
let opt_filter_verified = ref FT_All

let add_filter_three r = function
  | "no" -> r := FT_No
  | "yes" -> r := FT_Yes
  | "all" -> r := FT_All
  | _ -> assert false

let opt_three r = Arg.Symbol (["yes";"no";"all"], add_filter_three r)

let filter_spec =
  ["--filter-prover", Arg.String add_filter_prover,
   " [name,version[,alternative]|id] \
the proof containing this prover are selected";
   "--filter-obsolete", opt_three opt_filter_obsolete,
   " no: only non-obsolete, yes: only obsolete (default all)";
   "--filter-archived", opt_three opt_filter_archived,
   " no: only unarchived, yes: only archived (default no)";
   "--filter-verified-goal", opt_three opt_filter_verified_goal,
   " no: only parent goal not verified, yes: only verified (default all)";
   "--filter-verified", opt_three opt_filter_verified,
   " no: only not verified, yes: only verified (default all)";
]

type filters =
    { provers : C.Sprover.t; (* if empty : every provers *)
      obsolete : filter_three;
      archived : filter_three;
      verified : filter_three;
      verified_goal : filter_three;
    }

let provers_of_filter_prover whyconf = function
  | Prover p        -> C.Sprover.singleton p
  | FilterProver fp ->
    C.Mprover.map (Util.const ()) (C.filter_provers whyconf fp)

let prover_of_filter_prover whyconf = function
  | Prover p        -> p
  | FilterProver fp ->
    (C.filter_one_prover whyconf fp).C.prover


let read_filter_spec whyconf : filters * bool =
  let should_exit = ref false in
  let s = ref C.Sprover.empty in
  let iter p =
    try
      s := C.Sprover.union (provers_of_filter_prover whyconf p) !s
    with C.ProverNotFound (_,fp) ->
      Format.eprintf
        "The prover %a is not found in the configuration file %s@."
        Whyconf.print_filter_prover fp
        (Whyconf.get_conf_file whyconf);
      should_exit := true in
  Stack.iter iter filter_prover;
  {provers = !s;
   obsolete = !opt_filter_obsolete;
   archived = !opt_filter_archived;
   verified = !opt_filter_verified;
   verified_goal = !opt_filter_verified_goal;
  },!should_exit

let session_iter_proof_attempt_by_filter filters f session =
  (** provers *)
  let iter_provers a =
    if C.Sprover.mem a.S.proof_prover filters.provers then f a in
  let f = if C.Sprover.is_empty filters.provers then f else iter_provers in
  (** three value *)
  let three_value f v p =
    let iter_obsolete a =
      match v with
        | FT_No  when not (p a) -> f a
        | FT_Yes when     (p a) -> f a
        | _ -> () (** FT_All treated after *) in
    if v = FT_All then f else iter_obsolete in
  (** obsolete *)
  let f = three_value f filters.obsolete (fun a -> a.S.proof_obsolete) in
  (** archived *)
  let f = three_value f filters.archived (fun a -> a.S.proof_archived) in
  (** verified_goal *)
  let f = three_value f filters.verified_goal
    (fun a -> a.S.proof_parent.S.goal_verified) in
  (** verified *)
  let f = three_value f filters.verified S.proof_verified in
  S.session_iter_proof_attempt f session


let set_filter_verified_goal t = opt_filter_verified_goal := t

let opt_force_obsolete = ref false

let force_obsolete_spec =
  ["-F", Arg.Set opt_force_obsolete,
   " transform obsolete session"]
