
open Format

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
  let ses,use_shapes = Session_itp.load_session dir in
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
