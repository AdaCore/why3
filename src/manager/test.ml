
open Why

let autodetection () = 
  Whyconf.set_loadpath [Filename.concat Config.datadir "theories"];
(*
  Whyconf.set_driverpath (Filename.concat Config.datadir "drivers");
*)
  Whyconf.add_driver_config "Alt-Ergo 0.9" "alt_ergo.drv" "alt-ergo";
  Whyconf.add_driver_config "Z3 2.2" "z3.drv" "z3";
  Whyconf.add_driver_config "CVC3 2.1" "cvc3.drv" "cvc3";
  Whyconf.add_driver_config "Coq 8.3" "coq.drv" "coqc";
  Whyconf.save ()

let () = 
  try 
    Whyconf.read_config_file ()
  with Not_found -> 
    Format.eprintf "No .why.conf file found. Running autodetection of provers.@.";
    autodetection ();
    exit 0



let provers = Whyconf.known_provers ()

open Format

let () =
  printf "Provers: ";
  List.iter
    (fun name ->
       printf " %s, " name) provers;
  printf "@."
   


let fname = "test"

let loadpath = ["../theories"]

let env = Why.Env.create_env (Why.Typing.retrieve loadpath)

let m =
  let cin = open_in (fname ^ ".why") in
  let m = Why.Typing.read_channel env fname cin in
  close_in cin;
  m


let () = Db.init_base (fname ^ ".prm")

let do_task tname (th : Why.Theory.theory) (task : Why.Task.task) : unit =
(*
  if !opt_prove then begin
    let res = Driver.call_prover ~debug:!opt_debug ?timeout drv task in
    printf "%s %s %s : %a@." fname tname
      ((task_goal task).Decl.pr_name).Ident.id_long
      Call_provers.print_prover_result res
  end else match !opt_output with
    | None ->
        printf "@[%a@]@?" (Driver.print_task drv) task
    | Some dir ->
        let file =
          let file = Filename.basename fname in
          try Filename.chop_extension file
          with Invalid_argument _ -> file
        in
        let tname = th.th_name.Ident.id_short in
        let dest = Driver.filename_of_goal drv file tname task in
        (* Uniquify the filename before the extension if it exists*)
        let i = try String.rindex dest '.' with _ -> String.length dest in
        let name = Ident.string_unique !fname_printer (String.sub dest 0 i) in
        let ext = String.sub dest i (String.length dest - i) in
        let cout = open_out (Filename.concat dir (name ^ ext)) in
        let fmt = formatter_of_out_channel cout in
        fprintf fmt "@[%a@]@?" (Driver.print_task drv) task;
        close_out cout
*)
  Db.add_or_replace_task tname task

let do_theory tname th glist =
  let add acc (x,l) =
    let pr = try Why.Theory.ns_find_pr th.Why.Theory.th_export l with Not_found ->
      Format.eprintf "Goal '%s' not found in theory '%s'.@." x tname;
      exit 1
    in
    Why.Decl.Spr.add pr acc
  in
  let prs = Some (Queue.fold add Why.Decl.Spr.empty glist) in
  let prs = if Queue.is_empty glist then None else prs in
  let tasks = Why.Task.split_theory th prs in
  List.iter (do_task tname th) tasks

let () =
  let glist = Queue.create () in
  let add_th t th mi = Why.Ident.Mid.add th.Why.Theory.th_name (t,th) mi in
  let do_th _ (t,th) = do_theory t th glist in
  Why.Ident.Mid.iter do_th (Why.Theory.Mnm.fold add_th m Why.Ident.Mid.empty)




