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

(*
let () = Debug.set_flag Call_provers.debug
*)

let limit = Call_provers.{ limit_time = 1 ;
                           limit_mem  = 1000;
                           limit_steps = -1;}

let run_on_task fmt prover prover_driver t =
  let limit = { Call_provers.empty_limit with Call_provers.limit_time = 3 } in
  let result =
    Call_provers.wait_on_call
      (Why3.Driver.prove_task
         ~command:prover.Whyconf.command
         ~limit
         prover_driver t)
  in
  Format.fprintf fmt "%a" Call_provers.print_prover_answer result.Call_provers.pr_answer;
  match result.Call_provers.pr_answer with
  | Call_provers.Failure _ | Call_provers.HighFailure ->
    Format.fprintf fmt "@\n=======@\n%s@\n======@\n" result.Call_provers.pr_output
  | _ -> ()

let get_prover config env acc (short, name) =
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
      Why3.Whyconf.load_driver (Why3.Whyconf.get_main config) env prover.Whyconf.driver []
    with e ->
      ACSLtoWhy3.Self.fatal "Failed to load driver for %s: %a@." name
        Exn_printer.exn_printer e
  in
  (short,prover,driver)::acc

let process () =
  let prog = Ast.get () in
  (* File.pretty_ast ();  *)
  let provers =
    try
      ACSLtoWhy3.Self.result "Loading prover drivers...";
      List.fold_left
        (get_prover ACSLtoWhy3.config ACSLtoWhy3.env)
        []
        [ "C415", "CVC4,1.5,";
          "Z460", "Z3,4.6.0,";
          "A220", "Alt-Ergo,2.2.0,";
        ]
    with e ->
      ACSLtoWhy3.Self.fatal "Exception raised when loading prover drivers:@ %a"
        Exn_printer.exn_printer e
  in
  let theories =
    (* try *)
      ACSLtoWhy3.Self.result "Translating to Why3...";
      ACSLtoWhy3.prog prog
    (* with e -> *)
    (*   ACSLtoWhy3.Self.fatal "Exception raised while translating to Why3:@ %a" *)
    (*     Exn_printer.exn_printer e *)
  in
  try
    ACSLtoWhy3.Self.result "Running provers...";
    List.iter
      (fun th ->
       let th = th.Pmodule.mod_theory in
       ACSLtoWhy3.Self.result "running theory 1:";
       ACSLtoWhy3.Self.result "@[<hov 2>%a@]" Pretty.print_theory th;
       let tasks = Task.split_theory th None None in
       ACSLtoWhy3.Self.result "@[<h 0>Provers: %a@]"
                              (Pp.print_list Pp.comma
                                             (fun fmt (_n,p,_d) ->
                                              let p = p.Whyconf.prover in
                                              Format.fprintf fmt "%s %s" p.Whyconf.prover_name p.Whyconf.prover_version))
                              provers;
       let _ =
        List.fold_left
          (fun n t ->
           let l = Trans.apply_transform "split_goal_wp" ACSLtoWhy3.env t in
           List.fold_left
             (fun n t ->
              let (g,expl,t) = Termcode.goal_expl_task ~root:false t in
              ACSLtoWhy3.Self.result
                "@[<h 0>Task %d (%s) (%a): %a@]" n g.Ident.id_string
                (Pp.print_option Format.pp_print_string) expl
                (Pp.print_list Pp.comma (fun fmt (_n,p,d) -> run_on_task fmt p d t))
                provers;
              n+1)
             n l)
          1 tasks
      in ())
    theories
  with e ->
    ACSLtoWhy3.Self.fatal "Exception raised when running provers:@ %a"
      Exn_printer.exn_printer e


let (_unused : (unit -> unit) -> unit -> unit) =
  Dynamic.register
    ~plugin:"Jessie3"
    "process"
    ~journalize:true
    (Datatype.func Datatype.unit Datatype.unit)

let run () =  if ACSLtoWhy3.Enabled.get () then process ()

let () =
  (* try *)
    Db.Main.extend run
  (* with e -> *)
  (*   ACSLtoWhy3.Self.fatal "Exception raised when loading Jessie3:@ %a" *)
  (*     Exn_printer.exn_printer e *)
