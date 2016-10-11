
(* TODO *)
let proof_general = true

module Unix_scheduler = struct

    (* the private list of functions to call on idle, sorted higher
       priority first. *)
    let idle_handler = ref []

    (* [insert_idle_handler p f] inserts [f] as a new function to call
       on idle, with priority [p] *)
    let insert_idle_handler p f =
      let rec aux l =
        match l with
          | [] -> [p,f]
          | (p1,_) as hd :: rem ->
             if p > p1 then (p,f) :: l else hd :: aux rem
      in
      idle_handler := aux !idle_handler

    (* the private list of functions to call on timeout, sorted on
       earliest trigger time first. *)
    let timeout_handler = ref []

    (* [insert_timeout_handler ms t f] inserts [f] as a new function to call
       on timeout, with time step of [ms] and first call time as [t] *)
    let insert_timeout_handler ms t f =
      let rec aux l =
        match l with
          | [] -> [ms,t,f]
          | (_,t1,_) as hd :: rem ->
             if t < t1 then (ms,t,f) :: l else hd :: aux rem
      in
      timeout_handler := aux !timeout_handler

    (* public function to register a task to run on idle *)
    let idle ~(prio:int) f = insert_idle_handler prio f

    (* public function to register a task to run on timeout *)
    let timeout ~ms f =
      assert (ms > 0);
      let ms = float ms /. 1000.0 in
      let time = Unix.gettimeofday () in
      insert_timeout_handler ms (time +. ms) f

     (* buffer for storing character read on stdin *)
     let buf = Bytes.create 256

     let show_prompt = ref 0
     let prompt = ref "> "

     (* [main_loop interp] starts the scheduler. On idle, standard input is
        read.  When a complete line is read from stdin, it is passed
        as a string to the function [interp] *)
     let main_loop interp =
       try
         while true do
           show_prompt := !show_prompt + 1;
           if !show_prompt = 2 then begin
             Format.printf "%s@?" !prompt;
             show_prompt := 0;
           end;
           (* attempt to run the first timeout handler *)
           (let time = Unix.gettimeofday () in
           match !timeout_handler with
           | (ms,t,f) :: rem when t <= time ->
              timeout_handler := rem;
              let b = f () in
              let time = Unix.gettimeofday () in
              if b then insert_timeout_handler ms (ms +. time) f
           | _ ->
              (* time is not yet passed *)
              (* attempt to run the first idle handler *)
              match !idle_handler with
              | (p,f) :: rem ->
                 idle_handler := rem;
                 let b = f () in
                 if b then insert_idle_handler p f
              | [] ->
                 (* no idle handler *)
                 (* check stdin for a some delay *)
                 let delay =
                   match !timeout_handler with
                   | [] -> 0.125
                   (* 1/8 second by default *)
                   | (_,t,_) :: _ -> t -. time
                   (* or the time left until the next timeout otherwise *)
                 in
                 let a,_,_ = Unix.select [Unix.stdin] [] [] delay in
                 match a with
                 | [_] ->
                    let n = Unix.read Unix.stdin buf 0 256 in
                    interp (Bytes.sub_string buf 0 (n-1));
                    show_prompt := 0
                 | [] -> () (* nothing read *)
                 | _ -> assert false);
         done
       with Exit -> ()

end



(************************)
(* parsing command line *)
(************************)

open Why3
open Format

let files = Queue.create ()

let spec = Arg.align [
]

let usage_str = Format.sprintf
  "Usage: %s [options] [ <file.xml> | <f1.why> <f2.mlw> ...]"
  (Filename.basename Sys.argv.(0))


let config, base_config, _env =
  Why3.Whyconf.Args.initialize spec (fun f -> Queue.add f files) usage_str

let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)


module C = Why3.Controller_itp.Make(Unix_scheduler)

let cont =
  if Queue.is_empty files then Why3.Whyconf.Args.exit_with_usage spec usage_str;
  let fname = Queue.pop files in
  let ses =
    if Filename.check_suffix fname ".xml" then
      Session_itp.load_session fname
    else
      begin
        Queue.push fname files;
        Session_itp.empty_session ()
      end
  in
  let c = Controller_itp.create_controller env ses in
  Queue.iter (fun fname -> C.add_file c fname) files;
  c

(* loading the drivers *)
let () =
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

(* One prover named Alt-Ergo in the config file *)
let alt_ergo =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
  (** all provers that have the name "Alt-Ergo" *)
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else
    snd (Whyconf.Mprover.choose provers)

let test_idle fmt _args =
  Unix_scheduler.idle
    ~prio:0
    (fun () -> fprintf fmt "idle@."; false)

let test_timeout fmt _args =
  Unix_scheduler.timeout
    ~ms:1000
    (let c = ref 10 in
     fun () -> decr c;
               if !c > 0 then
                 (fprintf fmt "%d@." !c; true)
               else
                 (fprintf fmt "boom!@."; false))

let list_provers _fmt _args =
  let l =
    Whyconf.Hprover.fold
      (fun p _ acc -> (Pp.sprintf "%a" Whyconf.print_prover p)::acc)
      cont.Controller_itp.controller_provers
      []
  in
  let l = List.sort String.compare l in
  printf "@[<hov 2>== Known provers ==@\n%a@]@."
          (Pp.print_list Pp.newline Pp.string) l

let sort_pair (x,_) (y,_) = String.compare x y

let list_transforms _fmt _args =
  let l =
    List.rev_append (Trans.list_transforms ()) (Trans.list_transforms_l ())
  in
  let print_trans_desc fmt (x,r) =
    fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" x Pp.formatted r in
  printf "@[<hov 2>== Known transformations ==@\n%a@]@\n@."
         (Pp.print_list Pp.newline2 print_trans_desc)
         (List.sort sort_pair l)

open Controller_itp
open Session_itp
(* _____________________________________________________________________ *)
(* -------------------- zipper ----------------------------------------- *)
type proof_hole =
    Th of theory list * theory * theory list |
    Pn of proofNodeID list * proofNodeID * proofNodeID list |
    Tn of transID list * transID * transID list

type proof_zipper = { mutable cursor : proof_hole; ctxt : proof_hole Stack.t }

let ctxt = Stack.create ()

let zipper =
  let files =
    get_files cont.Controller_itp.controller_session
  in
  let file = ref None in
  Stdlib.Hstr.iter (fun _ f -> file := Some f) files;
  let file = Opt.get !file in
  match file.file_theories with
  | th :: tail -> { cursor = (Th ([], th, tail)); ctxt }
  | _ -> assert false

let zipper_init () =
  let files =
    get_files cont.Controller_itp.controller_session
  in
  let file = ref None in
  Stdlib.Hstr.iter (fun _ f -> file := Some f) files;
  let file = Opt.get !file in
  match file.file_theories with
  | th :: tail -> zipper.cursor <- (Th ([], th, tail));
      while not (Stack.is_empty zipper.ctxt) do ignore (Stack.pop zipper.ctxt) done
  | _ -> assert false


let zipper_down () =
  match zipper.cursor with
  | Th (_,th,_) ->
    (match theory_goals th with
    | pn::l ->
      Stack.push zipper.cursor zipper.ctxt;
      zipper.cursor <- Pn ([],pn,l);
      true
    | _ -> false)
  | Pn (_,pn,_) ->
    (match get_transformations cont.controller_session pn with
    | tn::l ->
      Stack.push zipper.cursor zipper.ctxt;
      zipper.cursor <- Tn ([],tn,l);
      true
    | _ -> false)
  | Tn (_,tn,_) ->
    (match get_sub_tasks cont.controller_session tn with
    | pn::l ->
      Stack.push zipper.cursor zipper.ctxt;
      zipper.cursor <- Pn ([],pn,l);
      true
    | _ -> false)

let zipper_up () =
  if not (Stack.is_empty zipper.ctxt) then begin
    zipper.cursor <- Stack.pop zipper.ctxt;
    true
  end else
    false

let zipper_right () =
  match zipper.cursor with
  | Th (l,cs,hd::r) ->
    zipper.cursor <- Th (cs::l,hd,r);
    true
  | Pn (l,cs,hd::r) ->
    zipper.cursor <- Pn (cs::l,hd,r);
    true
  | Tn (l,cs,hd::r) ->
    zipper.cursor <- Tn (cs::l,hd,r);
    true
  | _ -> false

let zipper_left () =
  match zipper.cursor with
  | Th (hd::l,cs,r) ->
    zipper.cursor <- Th (l,hd,cs::r);
    true
  | Pn (hd::l,cs,r) ->
    zipper.cursor <- Pn (l,hd,cs::r);
    true
  | Tn (hd::l,cs,r) ->
    zipper.cursor <- Tn (l,hd,cs::r);
    true
  | _ -> false

(* _____________________________________________________________________ *)
(* -------------------- moving around ---------------------------------- *)

let rec next_node () =
  zipper_down () || zipper_right () || (zipper_up () && next_node_no_down ())
and next_node_no_down () =
  zipper_right () || (zipper_up () && next_node_no_down ())

let prev_node () = zipper_left () || zipper_up ()

(* This function try to reach a goal from the current position using
   the move function *)
let rec move_to_goal move =
  if move () then
    match zipper.cursor with
    | Pn (_,pn,_) -> Some pn
    | _  -> move_to_goal move
  else
    None

let move_to_goal_ret move =
  match
    (match move_to_goal move with
    | None -> Printf.printf "No more goal right; back to root@.";
	zipper_init(); move_to_goal next_node
    | Some id -> Some id) with
  | None -> failwith "After initialization there is no goal to go to@."
  | Some id -> id

let move_to_goal_ret_p move _ _ = ignore (move_to_goal_ret move)

(* The cursor of the zipper is on a goal *)
let is_goal_cursor () =
  match zipper.cursor with
  | Pn (_, pn, _) -> Some pn
  | _ -> None

(* If on goal, do nothing else go to next_goal *)
let nearest_goal () =
  match is_goal_cursor () with
  | None -> move_to_goal_ret next_node
  | Some id -> id

(* _____________________________________________________________________ *)
(* -------------------- printing --------------------------------------- *)

let print_proof_attempt fmt pa =
  fprintf fmt "%a tl=%d %a"
          Whyconf.print_prover pa.prover
          pa.limit.Call_provers.limit_time
          (Pp.print_option Call_provers.print_prover_result) pa.proof_state

let rec print_proof_node s (fmt: Format.formatter) p =
  let parent = match get_proof_parent s p with
  | Theory t -> (theory_name t).Ident.id_string
  | Trans id -> get_transf_name s id
  in
  let current_goal =
    match is_goal_cursor () with
    | Some pn -> pn = p
    | _ -> false
  in
  if current_goal then
    fprintf fmt "**";
  if Controller_itp.pn_proved cont p then
    fprintf fmt "P";

  fprintf fmt
    "@[<hv 2> Goal %s; parent %s;@ @[<hov 2>[%a]@]@ @[<hov 2>[%a]@]@]"
    (get_proof_name s p).Ident.id_string parent
    (Pp.print_list Pp.semi print_proof_attempt)
    (get_proof_attempts s p)
    (Pp.print_list Pp.semi (print_trans_node s)) (get_transformations s p);

  if current_goal then
    fprintf fmt " **"

and print_trans_node s fmt id =
  let name = get_transf_name s id in
  let args = get_transf_args s id in
  let l = get_sub_tasks s id in
  let parent = (get_proof_name s (get_trans_parent s id)).Ident.id_string in
  if Controller_itp.tn_proved cont id then
    fprintf fmt "P";
  fprintf fmt "@[<hv 2> Trans %s; args %a; parent %s;@ [%a]@]" name (Pp.print_list Pp.semi pp_print_string) args parent
    (Pp.print_list Pp.semi (print_proof_node s)) l

let print_theory s fmt th : unit =
  if Controller_itp.th_proved cont (theory_name th) then
    fprintf fmt "P";
  fprintf fmt "@[<hv 2> Theory %s;@ [%a]@]" (theory_name th).Ident.id_string
    (Pp.print_list Pp.semi (fun fmt a -> print_proof_node s fmt a)) (theory_goals th)

let print_file s fmt (file, thl) =
  fprintf fmt "@[<hv 2> File %s;@ [%a]@]" file.file_name
    (Pp.print_list Pp.semi (print_theory s)) thl

let print_s s fmt =
  fprintf fmt "@[%a@]" (Pp.print_list Pp.semi (print_file s))

let print_session fmt s =
  let l = Stdlib.Hstr.fold (fun _ f acc -> (f,f.file_theories) :: acc) (get_files s) [] in
  fprintf fmt "%a@." (print_s s) l;;

let dump_session_raw fmt _args =
  fprintf fmt "%a@." print_session cont.Controller_itp.controller_session


let print_position (s: session) (cursor: proof_zipper) fmt: unit =
  match cursor.cursor with
  | Th (_, th, _) -> fprintf fmt "%a@." (print_theory s) th
  | Pn (_, pn, _) -> fprintf fmt "%a@." (print_proof_node s) pn
  | Tn (_, tn, _) -> fprintf fmt "%a@." (print_trans_node s) tn

let print_position_p s cursor fmt _ = print_position s cursor fmt

let task_driver =
  let d = Filename.concat (Whyconf.datadir main)
                          (Filename.concat "drivers" "why3_itp.drv")
  in
  Driver.load_driver env d []

(* Print current goal or nearest next goal if we are not on a goal *)
let test_print_goal fmt _args =
  (* temporary : get the first goal *)
  let id = nearest_goal () in
  let task = Session_itp.get_task cont.Controller_itp.controller_session id in
  fprintf fmt "@[====================== Task =====================@\n%a@]@."
          (*Pretty.print_task*)
          (Driver.print_task ~cntexample:false task_driver)
          task

(* Execute f and then print the goal *)
let then_print f fmt args =
  f fmt args;
  test_print_goal fmt []

(* _____________________________________________________________________ *)
(* -------------------- test with transformations ---------------------- *)

let test_schedule_proof_attempt fmt _args =
  (* temporary : get the first goal *)
  let id = nearest_goal () in
  let callback status =
    fprintf fmt "status: %a@."
            Controller_itp.print_status status
  in
  let limit = Call_provers.{empty_limit with limit_time = 2} in
  C.schedule_proof_attempt
    cont id alt_ergo.Whyconf.prover
    ~limit ~callback

let apply_transform fmt args =
  match args with
    | tr :: tl ->
       let id = nearest_goal () in
       let callback status =
         fprintf fmt "transformation status: %a@."
                 Controller_itp.print_trans_status status
       in
       C.schedule_transformation cont id tr tl ~callback
    | _ -> printf "Error: Give the name of the transformation@."

(*******)

let test_save_session _fmt args =
  match args with
  | file :: _ ->
    Session_itp.save_session (file ^ ".xml") cont.Controller_itp.controller_session;
    printf "session saved@."
  | [] ->
    printf "missing session file name@."

let test_reload fmt _args =
  fprintf fmt "Reloading... @?";
  C.reload_files cont;
  fprintf fmt "done @."

let test_transform_and_display fmt args =
  match args with
    | tr :: tl ->
       let id = nearest_goal () in
       let callback status =
         fprintf fmt "transformation status: %a@."
                 Controller_itp.print_trans_status status;
         match status with
         | TSdone _tid -> (ignore (move_to_goal_ret next_node);
             dump_session_raw fmt []; test_print_goal fmt [])
         | _ -> ()
       in
       C.schedule_transformation cont id tr tl ~callback
    | _ -> printf "Error: Give the name of the transformation@."


(***************** strategy *****************)

let loaded_strategies = ref []

let strategies () =
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

let list_strategies _fmt _args =
  let l = strategies () in
  let pp_strat fmt (n,s,_,_) = fprintf fmt "%s: %s" s n in
  printf "@[<hov 2>== Known strategies ==@\n%a@]@."
          (Pp.print_list Pp.newline pp_strat) l

(*******)


let print_known_map _fmt _args =
  let id = nearest_goal () in
  let task = get_task cont.controller_session id in
  let km = Task.task_known task in
  Ident.Mid.iter
    (fun id _d ->
     printf "known: %s@." id.Ident.id_string)
    km

(****)


let commands =
  [
    "k", "list known identifiers", print_known_map;
    "list-provers", "list available provers", list_provers;
    "list-transforms", "list available transformations", list_transforms;
    "list-strategies", "list available strategies", list_strategies;
    "a", "<transname> <args>: apply the transformation <transname> with arguments <args>", apply_transform;
    "b", "<transname> <args>: behave like a but add function to display into the callback", test_transform_and_display;
    "p", "print the session in raw form", dump_session_raw;
    "t", "test schedule_proof_attempt with alt-ergo on the first goal", test_schedule_proof_attempt;
    "g", "prints the first goal", test_print_goal;
    "r", "reload the session (test only)", test_reload;
    "s", "[s my_session] save the current session in my_session.xml", test_save_session;
    "ng", "get to the next goal", then_print (move_to_goal_ret_p next_node);
    "pg", "get to the prev goal", then_print (move_to_goal_ret_p prev_node);
    "gu", "get to the goal up",  then_print (move_to_goal_ret_p zipper_up);
    "gd", "get to the goal down",  then_print (move_to_goal_ret_p zipper_down);
    "gr", "get to the goal right",  then_print (move_to_goal_ret_p zipper_right);
    "gl", "get to the goal left",  then_print (move_to_goal_ret_p zipper_left);
    "pcur", "print tree rooted at current position", (print_position_p cont.controller_session zipper);
    "test", "test register known_map",
    (fun _ _ ->
      try
        let id = nearest_goal () in
        let task = get_task cont.controller_session id in
        let _ = Args_wrapper.build_name_tables task in
        ()
      with e when not (Debug.test_flag Debug.stack_trace) ->
        Format.eprintf
          "@[Exception raised :@ %a@.@]" Exn_printer.exn_printer e);
    "zu", "navigation up, parent", (fun _ _ -> ignore (zipper_up ()));
    "zd", "navigation down, left child", (fun _ _ -> ignore (zipper_down ()));
    "zl", "navigation left, left brother", (fun _ _ -> ignore (zipper_left ()));
    "zr", "navigation right, right brother", (fun _ _ -> ignore (zipper_right ()))
  ]

let commands_table = Stdlib.Hstr.create 17
let () =
  List.iter
    (fun (c,_,f) -> Stdlib.Hstr.add commands_table c f)
    commands

let help () =
  printf "== Available commands ==@\n";
  let l = ("q", "exit the shell") ::
            List.rev_map (fun (c,h,_) -> (c,h)) commands
  in
  let l = List.sort sort_pair l in
  List.iter (fun (c,help) -> printf "%20s : %s@\n" c help) l;
  printf "@."


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

let interp chout fmt s =
  let cmd,args = split_args s in
  match cmd with
    | "?" -> help ()
    | "q" ->
       fprintf fmt "Shell exited@.";
       close_out chout;
       exit 0
    | _ ->
      let f =
        try
          Some (Stdlib.Hstr.find commands_table cmd)
        with Not_found ->
          None
      in
      match f with
      | Some f -> f fmt args
      | None -> printf "unknown command '%s'@." cmd

let () =
  printf "Welcome to Why3 shell. Type '?' for help.@.";
  let chout = open_out "why3shell.out" in
  let fmt = if proof_general then formatter_of_out_channel stdout else formatter_of_out_channel chout in
  Unix_scheduler.main_loop (interp chout fmt)
