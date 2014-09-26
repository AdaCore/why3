(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
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

let run_on_task fmt prover prover_driver t =
  let result =
    Call_provers.wait_on_call
      (Why3.Driver.prove_task
         ~command:prover.Whyconf.command
         ~timelimit:3
         prover_driver t ()) ()
  in
  Format.fprintf fmt "%a" Call_provers.print_prover_answer result.Call_provers.pr_answer

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
      Why3.Driver.load_driver env prover.Whyconf.driver []
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
        [ "Z431", "Z3,4.3.1";
          "Z32 ", "Z3,3.2";
          "C241", "CVC3,2.4.1";
          "C414", "CVC4,1.4";
          "A952", "Alt-Ergo,0.95.2,";
        ]
    with e ->
      ACSLtoWhy3.Self.fatal "Exception raised when loading prover drivers:@ %a"
        Exn_printer.exn_printer e
  in
  let theories =
    try
      ACSLtoWhy3.Self.result "Translating to Why3...";
      ACSLtoWhy3.prog prog
    with e ->
      ACSLtoWhy3.Self.fatal "Exception raised when loading prover drivers:@ %a"
        Exn_printer.exn_printer e
  in
  try
    ACSLtoWhy3.Self.result "Running provers...";
    List.iter (fun th ->
      ACSLtoWhy3.Self.result "running theory 1:";
      ACSLtoWhy3.Self.result "@[<hov 2>%a@]" Pretty.print_theory th;
      let tasks = List.rev (Task.split_theory th None None) in
      ACSLtoWhy3.Self.result "@[<h 0>Provers: %a@]"
        (Pp.print_list Pp.comma
           (fun fmt (_n,p,_d) ->
             let p = p.Whyconf.prover in
             Format.fprintf fmt "%s %s" p.Whyconf.prover_name p.Whyconf.prover_version))
        provers;
      let _ =
        List.fold_left (fun n t ->
          let g = Task.task_goal t in
          ACSLtoWhy3.Self.result "@[<h 0>Task %d (%s): %a@]" n g.Decl.pr_name.Ident.id_string
            (Pp.print_list Pp.comma (fun fmt (_n,p,d) -> run_on_task fmt p d t))
            provers;
          n+1) 1 tasks
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
  try
    Db.Main.extend run
  with e ->
    ACSLtoWhy3.Self.fatal "Exception raised when loading Jessie3:@ %a"
      Exn_printer.exn_printer e
