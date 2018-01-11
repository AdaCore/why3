(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

module S = Session
module C = Whyconf

let verbose = Debug.register_info_flag "verbose"
    ~desc:"Increase verbosity."

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

let read_simple_spec () =
  Debug.Args.set_flags_selected ();
  Debug.Args.option_list ()

let opt_config = ref None
let opt_loadpath = ref []
let opt_extra = ref []

let common_options = [
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      "<file> same as -C";
  "--extra-config", Arg.String (fun s -> opt_extra := !opt_extra @ [s]),
      "<file> read additional configuration from <file>";
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> add <dir> to the library search path";
  "--library", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> same as -L";
  Debug.Args.desc_shortcut "verbose" "--verbose" "increase verbosity";
  Debug.Args.desc_debug_list;
  Debug.Args.desc_debug_all;
  Debug.Args.desc_debug;
]

(* dead code
let env_spec = common_options
*)

let read_env_spec () =
  (* Configuration *)
  let config = Whyconf.read_config !opt_config in
  let config = List.fold_left Whyconf.merge_config config !opt_extra in
  let main = Whyconf.get_main config in
  Whyconf.load_plugins main;
  let loadpath = (Whyconf.loadpath (Whyconf.get_main config))
    @ List.rev !opt_loadpath in
  let env = Env.create_env loadpath in
  env,config,read_simple_spec ()

let read_update_session ~allow_obsolete env config fname =
  let project_dir = S.get_project_dir fname in
  let session,use_shapes = S.read_session project_dir in
  let ctxt = S.mk_update_context
    ~allow_obsolete_goals:allow_obsolete
    ~use_shapes_for_pairing_sub_goals:use_shapes
    (fun ?parent:_ () -> ())
  in
  S.update_session ~ctxt session env config

(** filter *)
type filter_prover =
| Prover of Whyconf.prover
| FilterProver of Whyconf.filter_prover

let filter_prover = Stack.create ()

let read_opt_prover s =
  try
    let l = Strings.rev_split ',' s in
    match l with
    (* A prover specified uniquely *)
    | [altern;version;name]
      when List.for_all (fun s -> s = "" || s.[0] <> '^') l ->
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

let opt_status = ref []

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
   "--filter-highfailure",
   Arg.Unit (fun () -> opt_status := Call_provers.HighFailure::!opt_status),
   " filter the call that fail in an unexpeted way";
   "--filter-valid",
   Arg.Unit (fun () -> opt_status := Call_provers.Valid::!opt_status),
   " filter the valid goals (can be obsolete)";
   "--filter-invalid",
   Arg.Unit (fun () -> opt_status := Call_provers.Invalid::!opt_status),
   " filter the invalid goals";
   "--filter-unknown",
   Arg.String (fun s -> opt_status := Call_provers.Unknown (s, None)::!opt_status),
   " filter when the prover reports it can't determine if the task is valid";
   "--filter-failure",
   Arg.String (fun s -> opt_status := Call_provers.Failure s::!opt_status),
   " filter when the prover reports a failure";
]

type filters =
    { provers : C.Sprover.t; (* if empty : every provers *)
      obsolete : filter_three;
      archived : filter_three;
      verified : filter_three;
      verified_goal : filter_three;
      status : Call_provers.prover_answer list; (* if empty : any answer *)
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
   status = !opt_status;
  },!should_exit

let iter_proof_attempt_by_filter iter filters f session =
  (* provers *)
  let iter_provers a =
    if C.Sprover.mem a.S.proof_prover filters.provers then f a in
  let f = if C.Sprover.is_empty filters.provers then f else iter_provers in
  (* three value *)
  let three_value f v p =
    let iter_obsolete a =
      match v, p a with
        | FT_No, false -> f a
        | FT_Yes, true -> f a
        | _ -> () (* FT_All treated after *) in
    if v = FT_All then f else iter_obsolete in
  (* obsolete *)
  let f = three_value f filters.obsolete (fun a -> a.S.proof_obsolete) in
  (* archived *)
  let f = three_value f filters.archived (fun a -> a.S.proof_archived) in
  (* verified_goal *)
  let f = three_value f filters.verified_goal
    (fun a -> Opt.inhabited (S.goal_verified a.S.proof_parent)) in
  (* verified *)
  let f = three_value f filters.verified
    (fun p -> Opt.inhabited (S.proof_verified p)) in
  (* status *)
  let f = if filters.status = [] then f else
      (fun a -> match a.S.proof_state with
      | S.Done pr when List.mem pr.Call_provers.pr_answer filters.status -> f a
      | _ -> ()) in
  iter f session

let theory_iter_proof_attempt_by_filter filters f th =
  iter_proof_attempt_by_filter S.theory_iter_proof_attempt filters f th
let session_iter_proof_attempt_by_filter filters f s =
  iter_proof_attempt_by_filter S.session_iter_proof_attempt filters f s

let set_filter_verified_goal t = opt_filter_verified_goal := t

let opt_force_obsolete = ref false

let force_obsolete_spec =
  ["-F", Arg.Set opt_force_obsolete,
   " transform obsolete session"]



let rec ask_yn () =
  Format.printf "(y/n)@.";
  let answer = read_line () in
  match answer with
    | "y" -> true
    | "n" -> false
    | _ -> ask_yn ()

let ask_yn_nonblock ~callback =
  let b = Buffer.create 3 in
  let s = Bytes.create 1 in
  Format.printf "(y/n)@.";
  fun () ->
    match Unix.select [Unix.stdin] [] [] 0. with
    | [],_,_ -> true
    | _ ->
      if Unix.read Unix.stdin s 1 0 = 0 then
        begin (* EndOfFile *) callback false; false end
      else begin
        let c = Bytes.get s 0 in
        if c <> '\n'
        then (Buffer.add_char b c; true)
        else
          match Buffer.contents b with
          | "y" -> callback true; false
          | "n" | "" -> callback false; false
          | _ ->
            Format.printf "(y/N)@.";
            Buffer.clear b;
            true
      end
