open Format
open Stdlib
open Session_itp

exception NotADirectory of string
exception BadFileName of string

(******************************)
(* Creation of the controller *)
(******************************)

let cont_from_session_dir cont dir =
  (* create project directory if needed *)
  if Sys.file_exists dir then
    begin
      if not (Sys.is_directory dir) then raise (NotADirectory dir)
    end
  else
    begin
      eprintf "'%s' does not exist. \
               Creating directory of that name for the project@." dir;
      Unix.mkdir dir 0o777
    end;
  (* we load the session *)
  let ses,use_shapes = load_session dir in
  eprintf "using shapes: %a@." pp_print_bool use_shapes;
  (* create the controller *)
  Controller_itp.init_controller ses cont;
 (* update the session *)
  Controller_itp.reload_files cont ~use_shapes

(* If we have a file we chop it and return new session based on the directory *)
let cont_from_file cont f =
  let dir = try (Filename.chop_extension f) with
  | Invalid_argument _ -> raise (BadFileName f) in
  cont_from_session_dir cont dir


(******************)
(* Simple queries *)
(******************)

(**** interpretation of command-line ****)

let sort_pair (x,_) (y,_) = String.compare x y

let list_transforms () =
    List.rev_append
      (List.rev_append (Trans.list_transforms ()) (Trans.list_transforms_l ()))
      (List.rev_append (Trans.list_transforms_with_args ()) (Trans.list_transforms_with_args_l ()))

let list_transforms_query _cont _args =
  let l = list_transforms () in
  let print_trans_desc fmt (x,r) =
    fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" x Pp.formatted r
  in
  Pp.string_of (Pp.print_list Pp.newline2 print_trans_desc)
    (List.sort sort_pair l)

let list_provers cont _args =
  let l =
    Whyconf.Hprover.fold
      (fun p _ acc -> (Pp.sprintf "%a" Whyconf.print_prover p)::acc)
      cont.Controller_itp.controller_provers
      []
  in
  let l = List.sort String.compare l in
  Pp.sprintf "%a" (Pp.print_list Pp.newline Pp.string) l


let find_any_id nt s =
  try (Stdlib.Mstr.find s nt.Theory.ns_pr).Decl.pr_name with
  | Not_found -> try (Stdlib.Mstr.find s nt.Theory.ns_ls).Term.ls_name with
    | Not_found -> (Stdlib.Mstr.find s nt.Theory.ns_ts).Ty.ts_name

(* The id you are trying to use is undefined *)
exception Undefined_id of string
(* Bad number of arguments *)
exception Number_of_arguments

let print_id s tables =
  (* let tables = Args_wrapper.build_name_tables task in*)
  let km = tables.Task.known_map in
  let id = try find_any_id tables.Task.namespace s with
  | Not_found -> raise (Undefined_id s) in
  let d =
    try Ident.Mid.find id km with
    | Not_found -> raise Not_found (* Should not happen *)
  in
  Pp.string_of (Why3printer.print_decl tables) d

let print_id _cont task args =
  match args with
  | [s] -> print_id s task
  | _ -> raise Number_of_arguments

let search s tables =
  (*let tables = Args_wrapper.build_name_tables task in*)
  let id_decl = tables.Task.id_decl in
  let id = try find_any_id tables.Task.namespace s with
  | Not_found -> raise (Undefined_id s) in
  let l =
    try Ident.Mid.find id id_decl with
    | Not_found -> raise Not_found (* Should not happen *)
  in
  Pp.string_of (Pp.print_list Pp.newline2 (Why3printer.print_decl tables)) l

let search_id _cont task args =
  match args with
  | [s] -> search s task
  | _ -> raise Number_of_arguments

type query =
  | Qnotask of (Controller_itp.controller -> string list -> string)
  | Qtask of (Controller_itp.controller -> Task.name_tables -> string list -> string)

let help_on_queries fmt commands =
  let l = List.rev_map (fun (c,h,_) -> (c,h)) commands in
  let l = List.sort sort_pair l in
  let p fmt (c,help) = fprintf fmt "%20s : %s" c help in
  Format.fprintf fmt "%a" (Pp.print_list Pp.newline p) l

(* TODO remove reference to eprintf in this *)
let strategies env config loaded_strategies =
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
    (*Format.eprintf "Prover corresponding to %s has not been found@." name;*)
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
      | _ -> None
    end

(*******************************)
(* Prover command line parsing *)
(*******************************)


(* splits input string [s] into substrings separated by space
   spaces inside quotes or parentheses are not separator.
   implemented as a hardcoded automaton:
*)
let split_args s =
  let args = ref [] in
  let par_depth = ref 0 in
  let b = Buffer.create 17 in
  let push_arg () =
    let x = Buffer.contents b in
    if String.length x > 0 then (args := x :: !args; Buffer.clear b)
  in
  let push_char c = Buffer.add_char b c in
  let state = ref 0 in
  for i = 0 to String.length s - 1 do
    let c = s.[i] in
    match !state, c with
    | 0,' ' -> if !par_depth > 0 then push_char c else push_arg ()
    | 0,'(' -> incr par_depth; push_char c
    | 0,')' -> decr par_depth; push_char c
    | 0,'"' -> state := 1; if !par_depth > 0 then push_char c
    | 0,_ -> push_char c
    | 1,'"' -> state := 0; if !par_depth > 0 then push_char c
    | 1,_ -> push_char c
    | _ -> assert false
  done;
  push_arg ();
  match List.rev !args with
    | a::b -> a,b
    | [] -> "",[]

type command =
  | Transform    of string * Trans.gentrans * string list
  | Prove        of Whyconf.config_prover * Call_provers.resource_limit
  | Strategies   of string
  | Help_message of string
  | Query        of string
  | QError       of string
  | Other        of string * string list

let interp_others commands config cmd args =
  match parse_prover_name config cmd args with
  | Some (prover_config, limit) ->
      Prove (prover_config, limit)
  | None ->
      match cmd with
      | "auto" ->
          let s =
            match args with
            | "2"::_ -> "2"
            | _ -> "1"
          in
          Strategies s
      | "help" ->
          let text = Pp.sprintf
                          "Please type a command among the following (automatic completion available)@\n\
                           @\n\
                           @ <transformation name> [arguments]@\n\
                           @ <prover name> [<time limit> [<mem limit>]]@\n\
                           @ <query> [arguments]@\n\
                           @ auto [auto level]@\n\
                           @\n\
                           Available queries are:@\n@[%a@]" help_on_queries commands
          in
          Help_message text
      | _ ->
          Other (cmd, args)

let interp commands commands_table config cont id s =
  let cmd,args = split_args s in
  try
    let f = Stdlib.Hstr.find commands_table cmd in
    match f,id with
    | Qnotask f, _ -> Query (f cont args)
    | Qtask _, None -> QError "please select a goal first"
    | Qtask f, Some id ->
       let tables = match Session_itp.get_tables cont.Controller_itp.controller_session id with
       | None -> raise (Task.Bad_name_table "interp")
       | Some tables -> tables in
       let s = try Query (f cont tables args) with
       | Undefined_id s -> QError ("No existing id corresponding to " ^ s)
       | Number_of_arguments -> QError "Bad number of arguments"
       in s
  with Not_found ->
    try
      let t = Trans.lookup_trans cont.Controller_itp.controller_env cmd in
      Transform (cmd,t,args)
    with Trans.UnknownTrans _ ->
      interp_others commands config cmd args
