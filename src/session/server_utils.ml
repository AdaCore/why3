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

let debug = Debug.register_flag ~desc:"ITP server" "itp_server"

let has_extension f =
  try
    let _ = Filename.chop_extension f in true
  with Invalid_argument _ -> false

let get_session_dir ~allow_mkdir files =
  if Queue.is_empty files then invalid_arg "no files given";
  let first = Queue.pop files in
  (* The remaining files in [files] are going to be open *)
  let dir =
    if Sys.file_exists first then
      if Sys.is_directory first then
        (* first is a directory *)
        first
      else if Filename.basename first = "why3session.xml" then
        (* first is a session file *)
        Filename.dirname first
      else
        if Queue.is_empty files then
          (* first was the only file *)
          let d =
            try Filename.chop_extension first
            with Invalid_argument _ ->
              invalid_arg ("'" ^ first ^ "' has no extension and is not a directory")
          in
          Queue.push first files; (* we need to open [first] *)
          d
        else
          invalid_arg ("'" ^ first ^ "' is not a directory")
    else
      (* first does not exists *)
      if has_extension first then
        invalid_arg ("file not found: " ^ first)
      else first
  in
  if not (Sys.file_exists dir) then
    begin
      if allow_mkdir then Unix.mkdir dir 0o777 else
        invalid_arg ("session directory '" ^ dir ^ "' not found")
    end;
  dir




(******************************)
(* Creation of the controller *)
(******************************)

(* [cont_from_session]: returns an option to a boolean which returns None in
   case of failure, true if nothing is left to do and false if sessions was
   loaded but [f] should still be added to the session as a file. *)
(*
let cont_from_session ~notify cont f : bool option =
  (* If a file is given, find the corresponding directory *)
  let dir = try (Filename.chop_extension f) with
  | Invalid_argument _ -> f in
  (* create project directory if needed *)
  if Sys.file_exists dir then
    begin
      (* Case of user giving a file that gets chopped to an other file *)
      if not (Sys.is_directory dir) then
        begin
          Format.eprintf "Not a directory: %s@." dir;
          exit 1
        end
    end
  else
    begin
      Format.dprintf debug "'%s' does not exist. \
               Creating directory of that name for the Why3 session@." dir;
      Unix.mkdir dir 0o777
    end;
  (* we load the session *)
  let ses,use_shapes = load_session dir in
  Format.dprintf debug "using shapes: %b@." use_shapes;
  (* temporary, this should not be donne like this ! *)
  Controller_itp.set_session cont ses;
  (* update the session *)
  try (Controller_itp.reload_files cont ~use_shapes;
    (* Check if the initial file given was a file or not. If it was, we return
       that it should be added to the session.  *)
    if Sys.file_exists f && not (Sys.is_directory f) then
      Some false
    else
      Some true) with
  | e ->
    begin
      let s = Format.asprintf "%a@." Exn_printer.exn_printer e in
      notify (Message (Parse_Or_Type_Error s));
      None
    end
*)



(******************)
(* Simple queries *)
(******************)

(**** interpretation of command-line ****)

let sort_pair (x,_) (y,_) = String.compare x y

let list_transforms () =
  let l =
    List.rev_append
      (List.rev_append (Trans.list_transforms ()) (Trans.list_transforms_l ()))
      (List.rev_append (Trans.list_transforms_with_args ()) (Trans.list_transforms_with_args_l ()))
  in List.sort sort_pair l

let list_transforms_query _cont _args =
  let l = list_transforms () in
  let print_trans_desc fmt (x,r) =
    Format.fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" x Pp.formatted r
  in
  Pp.string_of (Pp.print_list Pp.newline2 print_trans_desc) l

let list_provers cont _args =
  let l =
    Whyconf.Hprover.fold
      (fun p _ acc -> (Pp.sprintf "%a" Whyconf.print_prover p)::acc)
      cont.Controller_itp.controller_provers
      []
  in
  let l = List.sort String.compare l in
  Pp.sprintf "%a" (Pp.print_list Pp.newline Pp.string) l

let load_strategies cont =
  let config = cont.Controller_itp.controller_config in
  let env = cont.Controller_itp.controller_env in
  let strategies = Whyconf.get_strategies config in
  Stdlib.Mstr.iter
    (fun _ st ->
     let name = st.Whyconf.strategy_name in
     try
       let code = st.Whyconf.strategy_code in
       let code = Strategy_parser.parse env config code in
       let shortcut = st.Whyconf.strategy_shortcut in
       Debug.dprintf debug "[session server info] Strategy '%s' loaded.@." name;
       Stdlib.Hstr.add cont.Controller_itp.controller_strategies name
                       (name, shortcut, st.Whyconf.strategy_desc, code)
     with Strategy_parser.SyntaxError msg ->
       Format.eprintf "Fatal: loading strategy '%s' failed: %s@." name msg;
       exit 1)
    strategies

let list_strategies cont =
  Stdlib.Hstr.fold (fun _ (name,short,_,_) acc -> (short,name)::acc) cont.Controller_itp.controller_strategies []


let symbol_name s =
  match s with
  | Args_wrapper.Tstysymbol ts -> ts.Ty.ts_name
  | Args_wrapper.Tsprsymbol pr -> pr.Decl.pr_name
  | Args_wrapper.Tslsymbol ls -> ls.Term.ls_name

(* The id you are trying to use is undefined *)
exception Undefined_id of string
(* Bad number of arguments *)
exception Number_of_arguments

let print_id s tables =
  (* let tables = Args_wrapper.build_name_tables task in*)
  let km = tables.Trans.known_map in
  let id = try Args_wrapper.find_symbol s tables with
  | Args_wrapper.Arg_parse_type_error _
  | Args_wrapper.Arg_qid_not_found _ -> raise (Undefined_id s) in
  let d =
    try Ident.Mid.find (symbol_name id) km with
    | Not_found -> raise Not_found (* Should not happen *)
    | Args_wrapper.Arg_parse_type_error _
    | Args_wrapper.Arg_qid_not_found _ -> raise (Undefined_id s)
  in
  let pr = tables.Trans.printer in
  let apr = tables.Trans.aprinter in
  let module P = (val Pretty.create pr apr pr pr false) in
  Pp.string_of P.print_decl d



(* searching ids in declarations *)

let occurs_in_type id = Ty.ty_s_any (fun ts -> Ident.id_equal ts.Ty.ts_name id)

let occurs_in_term id =
  Term.t_s_any (occurs_in_type id) (fun ls -> Ident.id_equal id ls.Term.ls_name)

let occurs_in_constructor id (cs,projs) =
  Ident.id_equal cs.Term.ls_name id ||
    List.exists (function Some ls -> Ident.id_equal ls.Term.ls_name id | None -> false) projs

let occurs_in_defn id (ls,def) =
  Ident.id_equal ls.Term.ls_name id ||
  let (_vl,t) = Decl.open_ls_defn def in occurs_in_term id t

let occurs_in_ind_decl id (_,clauses) =
  List.exists (fun (_,t) -> occurs_in_term id t) clauses

let occurs_in_decl d id =
  Decl.(match d.d_node with
  | Decl.Dtype ts -> Ident.id_equal ts.Ty.ts_name id (* look through ts.ys_def *)
  | Decl.Ddata dl ->
      List.exists
        (fun ((ts,c): data_decl) ->
         Ident.id_equal ts.Ty.ts_name id || List.exists (occurs_in_constructor id) c)
        dl
  | Decl.Dparam ls -> Ident.id_equal ls.Term.ls_name id
  | Decl.Dlogic dl -> List.exists (occurs_in_defn id) dl
  | Decl.Dind (_, il) -> List.exists (occurs_in_ind_decl id) il
  | Dprop ((Paxiom|Plemma), pr, t) -> Ident.id_equal pr.pr_name id || occurs_in_term id t
  | Dprop _ -> false)

let do_search ~search_both km idl =
  Ident.Mid.fold
    (fun _ d acc ->
      if search_both then
        (if List.exists (occurs_in_decl d) idl then Decl.Sdecl.add d acc else acc)
      else
        (if List.for_all (occurs_in_decl d) idl then Decl.Sdecl.add d acc else acc)) km Decl.Sdecl.empty

let search ~search_both s tables =
  let ids = List.rev_map
              (fun s -> try symbol_name (Args_wrapper.find_symbol s tables)
                        with Args_wrapper.Arg_parse_type_error _ |
                             Args_wrapper.Arg_qid_not_found _ -> raise (Undefined_id s)) s
  in
  let l = do_search ~search_both tables.Trans.known_map ids in
  if Decl.Sdecl.is_empty l then
    (* In case where search_both is true, this error cannot appear because there
       is at least one declaration: the definition of the ident. *)
       Pp.sprintf
         "No declaration contain all the %d identifiers @[%a@]"
         (List.length ids)
         (Pp.print_list Pp.space (fun fmt id -> Pp.string fmt id.Ident.id_string))
         ids
    else let l = Decl.Sdecl.elements l in
         let pr = tables.Trans.printer in
         let apr = tables.Trans.aprinter in
         let module P = (val Pretty.create pr apr pr pr false) in
         Pp.string_of (Pp.print_list Pp.newline2 P.print_decl) l

let print_id _cont task args =
  match args with
  | [s] -> print_id s task
  | _ -> raise Number_of_arguments

let search_id ~search_both _cont task args =
  match args with
  | [] -> raise Number_of_arguments
  | _ -> search ~search_both args task

type query =
  | Qnotask of (Controller_itp.controller -> string list -> string)
  | Qtask of (Controller_itp.controller -> Trans.naming_table -> string list -> string)


let help_on_queries fmt commands =
  let l = Stdlib.Hstr.fold (fun c (h,_) acc -> (c,h)::acc) commands [] in
  let l = List.sort sort_pair l in
  let p fmt (c,help) = Format.fprintf fmt "%20s : %s" c help in
  Format.fprintf fmt "%a" (Pp.print_list Pp.newline p) l

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
    Debug.dprintf debug "Prover corresponding to %s has not been found@." name;
    None
  end else
    Some (snd (Whyconf.Mprover.choose provers))

let session_timelimit = ref 2
let session_memlimit = ref 1000
let set_session_timelimit n = session_timelimit := n
let set_session_memlimit n = session_memlimit := n


(* Parses the Other command. If it fails to parse it, it answers None otherwise
   it returns the config of the prover together with the ressource_limit *)
let parse_prover_name config name args :
  (Whyconf.config_prover * Call_provers.resource_limit) option =
  match (return_prover name config) with
  | None -> None
  | Some prover_config ->
    begin
      if (List.length args > 2) then None else
      match args with
      | [] ->
        let default_limit = Call_provers.{empty_limit with
                                          limit_time = !session_timelimit;
                                          limit_mem = !session_memlimit} in
          Some (prover_config, default_limit)
      | [timeout] -> Some (prover_config,
                           Call_provers.{empty_limit with
                                          limit_time = int_of_string timeout;
                                          limit_mem = !session_memlimit})
      | [timeout; oom ] ->
        Some (prover_config, Call_provers.{empty_limit with
                                           limit_time = int_of_string timeout;
                                           limit_mem = int_of_string oom})
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
  | Edit         of Whyconf.config_prover
  | Bisect
  | Replay       of bool
  | Clean
  | Mark_Obsolete
  | Help_message of string
  | Query        of string
  | QError       of string
  | Other        of string * string list

let query_on_task cont f id args =
  let _,table = Session_itp.get_task_name_table cont.Controller_itp.controller_session id in
  try Query (f cont table args) with
    | Undefined_id s -> QError ("No existing id corresponding to " ^ s)
    | Number_of_arguments -> QError "Bad number of arguments"


let interp commands_table cont id s =
  let cmd,args = split_args s in
  (* We first try to apply a command from commands_table (itp_server.ml) *)
  match Stdlib.Hstr.find commands_table cmd with
  | (_, f) ->
    begin
      match f,id with
      | Qnotask f, _ -> Query (f cont args)
      | Qtask f, Some (Session_itp.APn id) ->
          query_on_task cont f id args
      | Qtask f, Some (Session_itp.APa pid) ->
          let id = Session_itp.get_proof_attempt_parent
              cont.Controller_itp.controller_session pid
          in
          query_on_task cont f id args
      | Qtask _, _ -> QError "please select a goal first"
    end
  | exception Not_found ->
     (* If the command entered is not in the commands_table, we first try to
        apply a transformation, then a prover, then a strategy and finally an
        interactive command.
      *)
   if id != None &&
     Session_itp.is_detached cont.Controller_itp.controller_session (Opt.get id)
   then
      match cmd, args with
      | "help", _ ->
        let text = Pp.sprintf
                         "Please type a command among the following (automatic completion available)@\n\
                          @\n\
                          @ <transformation name> [arguments]@\n\
                          @ <prover shortcut> [<time limit> [<mem limit>]]@\n\
                          @ <query> [arguments]@\n\
                          @ <strategy shortcut>@\n\
                          @ mark @\n\
                          @ clean @\n\
                          @ replay @\n\
                          @ bisect @\n\
                          @ help <transformation_name> @\n\
                          @ list_ide_command @ \n\
                          @\n\
                          Available queries are:@\n@[%a@]" help_on_queries commands_table
                  in
                  Help_message text
      | _ -> QError ("Command cannot be applied on a detached node")
   else
     begin
       try
         let t = Trans.lookup_trans cont.Controller_itp.controller_env cmd in
         match id with
         | Some (Session_itp.APn _id) -> Transform (cmd,t,args)
         | Some (Session_itp.ATn _tid) -> Transform (cmd, t, args)
         | _ -> QError ("Please select a goal or trans node in the task tree")
       with
       | Trans.UnknownTrans _ ->
          match parse_prover_name cont.Controller_itp.controller_config cmd args with
          | Some (prover_config, limit) ->
             if prover_config.Whyconf.interactive then
               Edit (prover_config)
             else
               Prove (prover_config, limit)
          | None ->
             if Stdlib.Hstr.mem cont.Controller_itp.controller_strategies cmd then
               Strategies cmd
             else
               match cmd, args with
               | "edit", _ ->
                  begin
                    match id with
                    | Some (Session_itp.APa id) ->
                       let pa =
                         Session_itp.get_proof_attempt_node
                           cont.Controller_itp.controller_session id in
                       begin try
                           let p,_ = Whyconf.Hprover.find
                                     cont.Controller_itp.controller_provers
                                     pa.Session_itp.prover in
                           Edit p
                         with Not_found ->
                              QError "cannot edit: uninstalled prover"
                       end
                    | _ ->  QError ("Please select a proof node in the task tree")
                  end
               | "bisect", _ ->
                  begin
                    match id with
                    | Some (Session_itp.APa _) -> Bisect
                    | _ ->  QError ("Please select a proof node in the task tree")
                  end
               | "replay", args ->
                   begin
                     match args with
                     | [] -> Replay true
                     | ["all"] -> Replay false
                     | _ -> QError ("replay expects either no arguments or `all`")
                   end
               | "mark", _ ->
                   Mark_Obsolete
               | "clean", _ ->
                   Clean
               | "help", [trans] ->
                  let print_trans_desc fmt r =
                    Format.fprintf fmt "@[%s:\n%a@]" trans Pp.formatted r
                  in
                  (try
                      let desc = Trans.lookup_trans_desc trans in
                      Help_message (Pp.string_of print_trans_desc desc)
                    with
                    | Not_found -> QError (Pp.sprintf "Transformation %s does not exists" trans))
               | "help", _ ->
                  let text = Pp.sprintf
                               "Please type a command among the following (automatic completion available)@\n\
                                @\n\
                                @ <transformation name> [arguments]@\n\
                                @ <prover shortcut> [<time limit> [<mem limit>]]@\n\
                                @ <query> [arguments]@\n\
                                @ <strategy shortcut>@\n\
                                @ mark @\n\
                                @ clean @\n\
                                @ replay @\n\
                                @ bisect @\n\
                                @ help <transformation_name> @\n\
                                @ list_ide_command @ \n\
                                @\n\
                                Available queries are:@\n@[%a@]" help_on_queries commands_table
                  in
                  Help_message text
               | _ ->
                  Other (cmd, args)
      end

(***********************)
(* First Unproven goal *)
(***********************)

(* Children should not give the proof attempts *)
let rec unproven_goals_below_node ~proved ~children ~is_goal acc node =
  if proved node then
    acc
  else
    let nodes = children node in
    if is_goal node && nodes = [] then
      node :: acc
    else
      List.fold_left (unproven_goals_below_node ~proved ~children ~is_goal)
        acc nodes

(* [split_list l node] returns a pair of list which contains the elements that
   appear before node (respectively after node). *)
let split_list l node =
  let rec split_list l acc =
    match l with
    | [] -> ([], List.rev acc)
    | hd :: tl ->
        if hd = node then
          (List.rev acc, tl)
        else
          split_list tl (hd :: acc)
  in
  split_list l []

let get_first_unproven_goal_around
    ~proved ~children ~get_parent ~is_goal ~is_pa node =
  let rec look_around node =
    match get_parent node with
    | None -> unproven_goals_below_node ~proved ~children ~is_goal [] node
    | Some parent ->
        if proved parent then
          look_around parent
        else
          unproven_goals_below_node ~proved ~children ~is_goal [] parent
  in
  let node = if is_pa node then Opt.get (get_parent node) else node in
  let node_list = look_around node in
  (* We look into this list of brothers in case the original node is inside it.
     If it is inside the list, we want to get the first non proved node after
     the original node. *)
  let (before_node, after_node) = split_list (List.rev node_list) node in
  match after_node with
  | [] ->
    begin
      match before_node with
      | [] -> None
      | hd :: _tl -> Some hd
    end
  | hd :: _tl  -> Some hd
