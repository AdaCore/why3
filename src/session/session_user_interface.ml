open Format
open Session_itp
open Controller_itp

(* TODO: raise exceptions instead of using explicit eprintf/exit *)
let cont_from_files cont spec usage_str env files provers =
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
  Controller_itp.init_controller ses cont;
 (* update the session *)
  Controller_itp.reload_files cont env ~use_shapes;
  (* add files to controller *)
  Queue.iter (fun fname -> Controller_itp.add_file cont fname) files;
  (* load provers drivers *)
  Whyconf.Mprover.iter
    (fun _ p ->
       try
         let d = Driver.load_driver env p.Whyconf.driver [] in
         Whyconf.Hprover.add cont.Controller_itp.controller_provers p.Whyconf.prover (p,d)
       with e ->
         let p = p.Whyconf.prover in
         eprintf "Failed to load driver for %s %s: %a@."
           p.Whyconf.prover_name p.Whyconf.prover_version
           Exn_printer.exn_printer e)
    provers

(**********************************)
(* list unproven goal and related *)
(**********************************)

(* If the transformation is proved, return acc.
   Else, return the concatenation of the reversed list of unproven
   goals below the transformation and acc *)
let rec unproven_goals_below_tn cont acc tn =
  if tn_proved cont tn then
    acc                         (* we ignore "dead" goals *)
  else
    let sub_tasks = get_sub_tasks cont.controller_session tn in
    List.fold_left (unproven_goals_below_pn cont) acc sub_tasks

(* Same as unproven_goals_below_tn; note that if goal is not proved
   and there is no transformation, goal is returned (else it is not) *)
and unproven_goals_below_pn cont acc goal =
  if pn_proved cont goal then
    acc                         (* we ignore "dead" transformations *)
  else
    match get_transformations cont.controller_session goal with
    | [] -> goal :: acc
    | tns -> List.fold_left (unproven_goals_below_tn cont) acc tns

(* Same as unproven_goals_below_tn *)
let unproven_goals_below_th cont acc th =
  if th_proved cont th then
    acc
  else
    let goals = theory_goals th in
    List.fold_left (unproven_goals_below_pn cont) acc goals

(* Same as unproven_goals_below_tn *)
let unproven_goals_below_file cont file =
  if file_proved cont file then
    []
  else
    let theories = file.file_theories in
    List.fold_left (unproven_goals_below_th cont) [] theories

(* returns the list of unproven goals in the controller session *)
let unproven_goals_in_session cont =
  let files = get_files cont.controller_session in
  Stdlib.Hstr.fold (fun _key file acc ->
      let file_goals = unproven_goals_below_file cont file in
      List.rev_append file_goals acc)
    files []

(* [get_first_unproven_goal_around_pn cont pn]
   returns the `first unproven goal' 'after' [pn]. Precisely:
   (1) it finds the youngest ancestor a of [pn] that is not proved
   (2) it returns the first unproved leaf of a
   it returns None if all ancestors are proved *)
let get_first_unproven_goal_around_pn cont pn =
  let ses = cont.controller_session in
  let rec look_around pn =
    match get_proof_parent ses pn with
    | Trans tn  ->
      if tn_proved cont tn
      then look_around (get_trans_parent ses tn)
      else unproven_goals_below_tn cont [] tn
    | Theory th ->
      if th_proved cont th then begin
        let parent = (theory_parent ses th) in
        if file_proved cont parent
        then unproven_goals_in_session cont
        else unproven_goals_below_file cont parent
      end else
        unproven_goals_below_th cont [] th
  in
  match look_around pn with
  | [] -> None
  | l -> Some (List.hd (List.rev l))

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

let commands =
  [
    "list-transforms", "list available transformations", Qnotask list_transforms_query;
    "list-provers", "list available provers", Qnotask list_provers;
(*
    "list-strategies", "list available strategies", list_strategies;
*)
    "print", "<s> print the declaration where s was defined", Qtask print_id;
    "search", "<s> print some declarations where s appear", Qtask search_id;
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

let help_on_queries fmt () =
  let l = List.rev_map (fun (c,h,_) -> (c,h)) commands in
  let l = List.sort sort_pair l in
  let p fmt (c,help) = fprintf fmt "%20s : %s" c help in
  Format.fprintf fmt "%a" (Pp.print_list Pp.newline p) l

let commands_table = Stdlib.Hstr.create 17
let () =
  List.iter
    (fun (c,_,f) -> Stdlib.Hstr.add commands_table c f)
    commands

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

let interp_others config cmd args =
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
                           Available queries are:@\n@[%a@]" help_on_queries ()
          in
          Help_message text
      | _ ->
          Other (cmd, args)

let interp config cont id s =
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
      interp_others config cmd args

(*
let interp cont id cmd =
  try
  match interp cont id cmd with
    | Transform(s,_t,args) ->
       clear_command_entry ();
       apply_transform cont s args
    | Query s ->
       clear_command_entry ();
       message_zone#buffer#set_text s
    | Other(s,args) ->
      begin
        match parse_prover_name gconfig.config s args with
        | Some (prover_config, limit) ->
          clear_command_entry ();
Prove          test_schedule_proof_attempt cont prover_config limit
        | None ->
          match s with
Strategies
          | "auto" ->
             let s =
               match args with
               | "2"::_ -> "2"
               | _ -> "1"
             in
             clear_command_entry ();
             run_strategy_on_task s
          | "help" ->
             clear_command_entry ();
             let text = Pp.sprintf
                          "Please type a command among the following (automatic completion available)@\n\
                           @\n\
                           @ <transformation name> [arguments]@\n\
                           @ <prover name> [<time limit> [<mem limit>]]@\n\
                           @ <query> [arguments]@\n\
                           @ auto [auto level]@\n\
                           @\n\
                           Available queries are:@\n@[%a@]" help_on_queries ()
             in
             message_zone#buffer#set_text text
          | _ ->
             message_zone#buffer#set_text ("unknown command '"^s^"'")
      end
  with e when not (Debug.test_flag Debug.stack_trace) ->
       message_zone#buffer#set_text (Pp.sprintf "anomaly: %a" Exn_printer.exn_printer e)

*)










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
      | _ -> (*Format.eprintf "Parse_prover_name. Should not happen. Please report@."; *) None
    end


(****** Exception handling *********)

let print_term s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_term tables fmt t

let print_type s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_ty tables fmt t

let print_ts s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_ts tables fmt t

let print_ls s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_ls tables fmt t

let print_tv s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_tv tables fmt t

let print_vsty s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_forget_vsty tables fmt t

let print_pr s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_pr tables fmt t

let print_pat s id fmt t =
  let tables = match (Session_itp.get_tables s id) with
  | None -> Args_wrapper.build_name_tables (Session_itp.get_task s id)
  | Some tables -> tables in
  Why3printer.print_pat tables fmt t

(* Exception reporting *)

(* TODO remove references to id.id_string in this function *)
let bypass_pretty s id =
  begin fun fmt exn -> match exn with
  | Ty.TypeMismatch (t1,t2) ->
      fprintf fmt "Type mismatch between %a and %a"
        (print_type s id) t1 (print_type s id) t2
  | Ty.BadTypeArity ({Ty.ts_args = []} as ts, _) ->
      fprintf fmt "Type symbol %a expects no arguments" (print_ts s id) ts
  | Ty.BadTypeArity (ts, app_arg) ->
      let i = List.length ts.Ty.ts_args in
      fprintf fmt "Type symbol %a expects %i argument%s but is applied to %i"
        (print_ts s id) ts i (if i = 1 then "" else "s") app_arg
  | Ty.DuplicateTypeVar tv ->
      fprintf fmt "Type variable %a is used twice" (print_tv s id) tv
  | Ty.UnboundTypeVar tv ->
      fprintf fmt "Unbound type variable: %a" (print_tv s id) tv
  | Ty.UnexpectedProp ->
      fprintf fmt "Unexpected propositional type"
  | Term.BadArity ({Term.ls_args = []} as ls, _) ->
      fprintf fmt "%s %a expects no arguments"
        (if ls.Term.ls_value = None then "Predicate" else "Function") (print_ls s id) ls
  | Term.BadArity (ls, app_arg) ->
      let i = List.length ls.Term.ls_args in
      fprintf fmt "%s %a expects %i argument%s but is applied to %i"
        (if ls.Term.ls_value = None then "Predicate" else "Function")
        (print_ls s id) ls i (if i = 1 then "" else "s") app_arg
  | Term.EmptyCase ->
      fprintf fmt "Empty match expression"
  | Term.DuplicateVar vs ->
      fprintf fmt "Variable %a is used twice" (print_vsty s id) vs
  | Term.UncoveredVar vs ->
      fprintf fmt "Variable %a uncovered in \"or\"-pattern" (print_vsty s id) vs
  | Term.FunctionSymbolExpected ls ->
      fprintf fmt "Not a function symbol: %a" (print_ls s id) ls
  | Term.PredicateSymbolExpected ls ->
      fprintf fmt "Not a predicate symbol: %a" (print_ls s id) ls
  | Term.ConstructorExpected ls ->
      fprintf fmt "%s %a is not a constructor"
        (if ls.Term.ls_value = None then "Predicate" else "Function") (print_ls s id) ls
  | Term.TermExpected t ->
      fprintf fmt "Not a term: %a" (print_term s id) t
  | Term.FmlaExpected t ->
      fprintf fmt "Not a formula: %a" (print_term s id) t
  | Pattern.ConstructorExpected (ls,ty) ->
      fprintf fmt "%s %a is not a constructor of type %a"
        (if ls.Term.ls_value = None then "Predicate" else "Function") (print_ls s id) ls
        (print_type s id) ty
  | Pattern.NonExhaustive pl ->
      fprintf fmt "Pattern not covered by a match:@\n  @[%a@]"
        (print_pat s id) (List.hd pl)
  | Decl.BadConstructor ls ->
      fprintf fmt "Bad constructor: %a" (print_ls s id) ls
  | Decl.BadRecordField ls ->
      fprintf fmt "Not a record field: %a" (print_ls s id) ls
  | Decl.RecordFieldMissing (_cs,ls) ->
      fprintf fmt "Field %a is missing" (print_ls s id) ls
  | Decl.DuplicateRecordField (_cs,ls) ->
      fprintf fmt "Field %a is used twice in the same constructor" (print_ls s id) ls
  | Decl.IllegalTypeAlias ts ->
      fprintf fmt
        "Type symbol %a is a type alias and cannot be declared as algebraic"
        (print_ts s id) ts
  | Decl.NonFoundedTypeDecl ts ->
      fprintf fmt "Cannot construct a value of type %a" (print_ts s id) ts
  | Decl.NonPositiveTypeDecl (_ts, ls, ty) ->
      fprintf fmt "Constructor %a \
          contains a non strictly positive occurrence of type %a"
        (print_ls s id) ls (print_type s id) ty
  | Decl.InvalidIndDecl (_ls, pr) ->
      fprintf fmt "Ill-formed inductive clause %a"
        (print_pr s id) pr
  | Decl.NonPositiveIndDecl (_ls, pr, ls1) ->
      fprintf fmt "Inductive clause %a contains \
          a non strictly positive occurrence of symbol %a"
        (print_pr s id) pr (print_ls s id) ls1
  | Decl.BadLogicDecl (ls1,ls2) ->
      fprintf fmt "Ill-formed definition: symbols %a and %a are different"
        (print_ls s id) ls1 (print_ls s id) ls2
  | Decl.UnboundVar vs ->
      fprintf fmt "Unbound variable: %a" (print_vsty s id) vs
  | Decl.ClashIdent id ->
      fprintf fmt "Ident %s is defined twice" id.Ident.id_string
  | Decl.EmptyDecl ->
      fprintf fmt "Empty declaration"
  | Decl.EmptyAlgDecl ts ->
      fprintf fmt "Algebraic type %a has no constructors" (print_ts s id) ts
  | Decl.EmptyIndDecl ls ->
      fprintf fmt "Inductive predicate %a has no constructors" (print_ls s id) ls
  | Decl.KnownIdent id ->
      fprintf fmt "Ident %s is already declared" id.Ident.id_string
  | Decl.UnknownIdent id ->
      fprintf fmt "Ident %s is not yet declared" id.Ident.id_string
  | Decl.RedeclaredIdent id ->
      fprintf fmt "Ident %s is already declared, with a different declaration"
        id.Ident.id_string
  | Decl.NoTerminationProof ls ->
      fprintf fmt "Cannot prove the termination of %a" (print_ls s id) ls
  | _ -> Format.fprintf fmt "Uncaught: %a" Exn_printer.exn_printer exn
  end

let get_exception_message ses id fmt e =
  match e with
  | Case.Arg_trans_type (s, ty1, ty2) ->
      Format.fprintf fmt "Error in transformation %s during unification of the following terms:\n %a \n %a"
        s (print_type ses id) ty1 (print_type ses id) ty2
  | Case.Arg_trans_term (s, t1, t2) ->
      Format.fprintf fmt "Error in transformation %s during unification of following two terms:\n %a \n %a" s
        (print_term ses id) t1 (print_term ses id) t2
  | Case.Arg_trans (s) ->
      Format.fprintf fmt "Error in transformation function: %s \n" s
  | Case.Arg_hyp_not_found (s) ->
      Format.fprintf fmt "Following hypothesis was not found: %s \n" s
  | Args_wrapper.Arg_theory_not_found (s) ->
      Format.fprintf fmt "Theory not found: %s" s
  | e ->
      bypass_pretty ses id fmt e
