
open Format
open Session_itp

(* TODO: raise exceptions instead of using explicit eprintf/exit *)
let cont_from_files spec usage_str env files provers =
  if Queue.is_empty files then Whyconf.Args.exit_with_usage spec usage_str;
  let fname = Queue.peek files in
  (* extract project directory, and create it if needed *)
  let dir =
    if Filename.check_suffix fname ".why" ||
       Filename.check_suffix fname ".mlw"
    then Filename.chop_extension fname
    else let _ = Queue.pop files in fname
  in
  if Sys.file_exists dir then
    begin
      if not (Sys.is_directory dir) then
        begin
          Format.eprintf
            "[Error] @[When@ more@ than@ one@ file@ is@ given@ on@ the@ \
             command@ line@ the@ first@ one@ must@ be@ the@ directory@ \
             of@ the@ session.@]@.";
          Arg.usage spec usage_str; exit 1
        end
    end
  else
    begin
      eprintf "[GUI] '%s' does not exist. \
               Creating directory of that name for the project@." dir;
      Unix.mkdir dir 0o777
    end;
  (* we load the session *)
  let ses,use_shapes = load_session dir in
  eprintf "using shapes: %a@." pp_print_bool use_shapes;
  (* create the controller *)
  let c = Controller_itp.create_controller env ses in
 (* update the session *)
  Controller_itp.reload_files c env ~use_shapes;
  (* add files to controller *)
  Queue.iter (fun fname -> Controller_itp.add_file c fname) files;
  (* load provers drivers *)
  Whyconf.Mprover.iter
    (fun _ p ->
       try
         let d = Driver.load_driver env p.Whyconf.driver [] in
         Whyconf.Hprover.add c.Controller_itp.controller_provers p.Whyconf.prover (p,d)
       with e ->
         let p = p.Whyconf.prover in
         eprintf "Failed to load driver for %s %s: %a@."
           p.Whyconf.prover_name p.Whyconf.prover_version
           Exn_printer.exn_printer e)
    provers;
  (* return the controller *)
  c

(*********************)
(* Terminal historic *)
(*********************)

module type Historic_type = sig
  type historic

  val create_historic: unit -> historic
  val print_next_command: historic -> string option
  val print_prev_command: historic -> string option
  val add_command: historic -> string -> unit

end

module Historic : Historic_type = struct
  type 'a hole_list = 'a list * 'a list

  (* TODO this looks like we can make it more efficient either with imperative
     feature or by being more clever.  With DLlists, we could have added a
     command in O(1). *)
  let add e l =
    match l with
    | ll, lr ->  [], e :: (List.rev ll) @ lr

  let next l =
    match l with
    | ll, [] -> ll, []
    | ll, [hd] -> ll, [hd]
    (* Get acts on the right list so we never empty right list *)
    | ll, cur :: lr -> cur :: ll, lr

  let prev l =
    match l with
    | hd :: ll, lr -> ll, hd :: lr
    | [], lr -> [], lr

  let get l =
    match l with
    | _, hd :: _ -> Some hd
    | _, [] -> None

  type historic = {mutable lc : string hole_list;
                   mutable tr : bool}
(* tr is used to know what was the last query from user because cases for the
   first element of the historic and other elements is not the same *)

  let create_historic () : historic =
    {lc = [], [];
     tr = false}

  let get_current h =
    get h.lc

  let print_next_command h =
    if h.tr then
      begin
        h.lc <- next h.lc;
        get_current h
      end
    else
      begin
        let s = get_current h in
        h.tr <- true;
        s
      end

  let print_prev_command h =
    if h.tr then
      begin
        h.lc <- prev h.lc;
        get_current h
      end
    else
      None

  let add_command h e =
    h.lc <- add e h.lc;
    h.tr <- false

end

(***************** strategies *****************)

let loaded_strategies = ref []

let strategies env config =
  match !loaded_strategies with
    | [] ->
      let strategies = Whyconf.get_strategies config in
      let strategies =
        Stdlib.Mstr.fold_left
          (fun acc _ st ->
            let name = st.Whyconf.strategy_name in
            try
              let code = st.Whyconf.strategy_code in
              let code = Strategy_parser.parse2 env config code in
              let shortcut = st.Whyconf.strategy_shortcut in
              Format.eprintf "[Why3shell] Strategy '%s' loaded.@." name;
              (name, shortcut, st.Whyconf.strategy_desc, code) :: acc
            with Strategy_parser.SyntaxError msg ->
              Format.eprintf
                "[Why3shell warning] Loading strategy '%s' failed: %s@." name msg;
              acc)
          []
          strategies
      in
      let strategies = List.rev strategies in
      loaded_strategies := strategies;
      strategies
    | l -> l


(**** interpretation of command-line *********************)

let sort_pair (x,_) (y,_) = String.compare x y

let list_transforms _args =
  let l =
    List.rev_append
    (List.rev_append (Trans.list_transforms ()) (Trans.list_transforms_l ()))
    (List.rev_append (Trans.list_transforms_with_args ()) (Trans.list_transforms_with_args_l ()))
  in
  let print_trans_desc fmt (x,r) =
    fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" x Pp.formatted r
  in
  Pp.string_of (Pp.print_list Pp.newline2 print_trans_desc)
               (List.sort sort_pair l)

let find_any_id nt s =
  try (Stdlib.Mstr.find s nt.Theory.ns_pr).Decl.pr_name with
  | Not_found -> try (Stdlib.Mstr.find s nt.Theory.ns_ls).Term.ls_name with
    | Not_found -> (Stdlib.Mstr.find s nt.Theory.ns_ts).Ty.ts_name

(* The id you are trying to use is undefined *)
exception Undefined_id
(* Bad number of arguments *)
exception Number_of_arguments

let print_id s task =
  let tables = Args_wrapper.build_name_tables task in
  let km = tables.Args_wrapper.known_map in
  let id = try find_any_id tables.Args_wrapper.namespace s with
  | Not_found -> raise Undefined_id in
  let d =
    try Ident.Mid.find id km with
    | Not_found -> raise Not_found (* Should not happen *)
  in
  Pp.string_of (Why3printer.print_decl tables) d

let print_id task args =
  match args with
  | [s] -> print_id s task
  | _ -> raise Number_of_arguments

let search s task =
  let tables = Args_wrapper.build_name_tables task in
  let id_decl = tables.Args_wrapper.id_decl in
  let id = try find_any_id tables.Args_wrapper.namespace s with
  | Not_found -> raise Undefined_id  in
  let l =
    try Ident.Mid.find id id_decl with
    | Not_found -> raise Not_found (* Should not happen *)
  in
  Pp.string_of (Pp.print_list Pp.newline2 (Why3printer.print_decl tables)) l

let search_id task args =
  match args with
  | [s] -> search s task
  | _ -> raise Number_of_arguments

let commands =
  [
    "list-transforms", "list available transformations", (fun _ -> list_transforms);
(*
    "list-provers", "list available provers", list_provers;
    "list-strategies", "list available strategies", list_strategies;
*)
    "print", "<s> print the declaration where s was defined", print_id;
    "search", "<s> print some declarations where s appear", search_id;
(*
    "r", "reload the session (test only)", test_reload;
    "rp", "replay", test_replay;
    "s", "save the current session", test_save_session;
    "ng", "go to the next goal", then_print (move_to_goal_ret_p next_node);
    "pg", "go to the prev goal", then_print (move_to_goal_ret_p prev_node);
    "gu", "go to the goal up",  then_print (move_to_goal_ret_p zipper_up);
    "gd", "go to the goal down",  then_print (move_to_goal_ret_p zipper_down);
    "gr", "go to the goal right",  then_print (move_to_goal_ret_p zipper_right);
    "gl", "go to the goal left",  then_print (move_to_goal_ret_p zipper_left)
 *)
  ]

let commands_table = Stdlib.Hstr.create 17
let () =
  List.iter
    (fun (c,_,f) -> Stdlib.Hstr.add commands_table c f)
    commands

let split_args s =
  let args = ref [] in
  let b = Buffer.create 17 in
  let state = ref 0 in
  for i = 0 to String.length s - 1 do
    let c = s.[i] in
    match !state, c with
    | 0,' ' -> ()
    | 0,'"' -> state := 1
    | 0,_ -> Buffer.add_char b c; state := 2
    | 1,'"' -> args := Buffer.contents b :: !args; Buffer.clear b; state := 0
    | 1,_ -> Buffer.add_char b c
    | 2,' ' -> args := Buffer.contents b :: !args; Buffer.clear b; state := 0
    | 2,_ -> Buffer.add_char b c
    | _ -> assert false
  done;
  begin
    match !state with
      | 0 -> ()
      | 1 -> args := Buffer.contents b :: !args (* TODO : report missing '"' *)
      | 2 -> args := Buffer.contents b :: !args
      | _ -> assert false
  end;
  match List.rev !args with
    | a::b -> a,b
    | [] -> "",[]

type command =
  | Transform of string * Trans.gentrans * string list
  | Query of string
  | Other of string * string list

let interp env id ses s =
  let task = Session_itp.get_task ses id in
  let cmd,args = split_args s in
  try
    let f = Stdlib.Hstr.find commands_table cmd in
    Query (f task args)
  with Not_found ->
       try
         let t = Trans.lookup_trans env cmd in
         Transform (cmd,t,args)
       with Trans.UnknownTrans _ ->
            Other(cmd,args)


(********* Callbacks tools *******)

(* Return the prover corresponding to given name. name is of the form
  | name
  | name, version
  | name, altern
  | name, version, altern *)
let return_prover name config =
  let fp = Whyconf.parse_filter_prover name in
  (** all provers that have the name/version/altern name *)
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    Format.eprintf "Prover corresponding to %s has not been found@." name;
    None
  end else
    Some (snd (Whyconf.Mprover.choose provers))

(* Parses the Other command. If it fails to parse it, it answers None otherwise
   it returns the config of the prover together with the ressource_limit *)
let parse_prover_name config name args :
  (Whyconf.config_prover * Call_provers.resource_limit) option =
  let main = Whyconf.get_main config in
  match (return_prover name config) with
  | None -> None
  | Some prover_config ->
    begin
      if (List.length args > 2) then None else
      match args with
      | [] ->
        let default_limit = Call_provers.{limit_time = Whyconf.timelimit main;
                                          limit_mem = Whyconf.memlimit main;
                                          limit_steps = 0} in
          Some (prover_config, default_limit)
      | [timeout] -> Some (prover_config,
                           Call_provers.{empty_limit with
                                         limit_time = int_of_string timeout})
      | [timeout; oom ] ->
        Some (prover_config, Call_provers.{limit_time = int_of_string timeout;
                                           limit_mem = int_of_string oom;
                                           limit_steps = 0})
      | _ -> Format.eprintf "Parse_prover_name. Should not happen. Please report@."; None
    end
