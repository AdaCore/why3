
(* example of an option 
module OutputFile =
  Self.EmptyString
    (struct
       let option_name = "-jessie3-output"
       let help = "output file for intermediate Why3 code"
       let arg_name = "filename"
     end)

*)

open Why3

let run_on_task prover prover_driver t =
  let result =
    Call_provers.wait_on_call
      (Why3.Driver.prove_task 
         ~command:prover.Whyconf.command
         ~timelimit:3
         prover_driver t ()) ()
  in
  let p = prover.Whyconf.prover in
  ACSLtoWhy3.Self.result "Status with %s %s: %a" p.Whyconf.prover_name
    p.Whyconf.prover_version
    Call_provers.print_prover_answer result.Call_provers.pr_answer

let get_prover config env acc name =
  let prover = 
    try
      let fp = Whyconf.parse_filter_prover name in
      let provers = Whyconf.filter_one_prover config fp in
      provers
    with
    | Whyconf.ProverNotFound _ ->
        ACSLtoWhy3.Self.fatal "Prover %s not installed or not configured@." name
  in
  (* loading the driver *)
  let driver : Why3.Driver.driver =
    try
      Why3.Driver.load_driver env prover.Whyconf.driver []
    with e ->
      ACSLtoWhy3.Self.fatal "Failed to load driver for %s: %a@." name
        Exn_printer.exn_printer e
  in
  (prover,driver)::acc

let process () =
  let prog = Ast.get () in
  (* File.pretty_ast (); *)
  let provers = 
    List.fold_left (get_prover ACSLtoWhy3.config ACSLtoWhy3.env) []
      [ "Alt-Ergo,0.94";
        "Z3,3.2"; "Z3,4.0";
        "CVC3,2.2"; "CVC3,2.4.1"] 
  in
  let theories = ACSLtoWhy3.prog prog in
  try
    List.iter (fun th ->
      ACSLtoWhy3.Self.result "running theory 1:";
      ACSLtoWhy3.Self.result "@[<hov 2>%a@]" Pretty.print_theory th;
      let tasks = Task.split_theory th None None in
      let _ =
        List.fold_left (fun n t ->
          ACSLtoWhy3.Self.result "Dealing with task %d" n;
          List.iter (fun (p,d) -> run_on_task p d t) provers;
          n+1) 1 tasks
      in ())
    theories
  with e ->
    ACSLtoWhy3.Self.fatal "Exception raised when running provers:@ %a" Exn_printer.exn_printer e


let (_unused : (unit -> unit) -> unit -> unit) =
  Dynamic.register
    ~plugin:"Jessie3"
    "process"
    ~journalize:true
    (Datatype.func Datatype.unit Datatype.unit)

let run () =  if ACSLtoWhy3.Enabled.get () then process ()
let () = Db.Main.extend run
