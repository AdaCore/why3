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

open Format
open Worker_proto

module Worker = Js_of_ocaml.Worker
module SAT = (val (Sat_solver.get_current ()) : Sat_solver_sig.S)
module FE = Frontend.Make (SAT)

let print_status fmt _d status steps =
  match status with
  | FE.Unsat _dep ->
    fprintf fmt "Proved (%Ld steps)" steps
  | FE.Inconsistent -> ()
    (* fprintf fmt "Inconsistent assumption" *)
  | FE.Unknown _t | FE.Sat _t ->
      fprintf fmt "Unknown (%Ld steps)@." steps


let report_status report _d status _steps =
  match status with
  | FE.Unsat _dep -> report Valid
  | FE.Inconsistent -> ()
  | FE.Unknown _t | FE.Sat _t -> report (Unknown "unknown")

let run_alt_ergo_on_task text =
  let lb = Lexing.from_string text in
(* from Alt-Ergo, src/main/frontend.ml *)
  let a = Why_parser.file_parser Why_lexer.parse_token lb in
  Parsing.clear_parser ();
  let ltd, _typ_env = Typechecker.file false Typechecker.empty_env a in
  match Typechecker.split_goals ltd with
  | [d] ->
    let d = Cnf.make (List.map (fun (f, _env) -> f, true) d) in
    SAT.reset_refs ();
    let stat = ref (Invalid "no answer from Alt-Ergo") in
    let f s = stat := s in
    begin
      try
        let _x = Queue.fold (FE.process_decl (report_status f))
          (SAT.empty (), true, Explanation.empty) d
        in
        !stat
      with Fun_sat.StepsLimitReached -> Unknown "steps limit reached"
    end
  | _ -> Invalid "zero or more than 1 goal to solve"




let () =
  Options.set_steps_bound 100;
  Options.set_is_gui false;
  Worker.set_onmessage (fun msg ->
			match unmarshal msg with
			  Goal (id, text, steps) ->
			  let old_steps = Options.steps_bound () in
			  if steps > 0 then Options.set_steps_bound steps;
			  let result = run_alt_ergo_on_task text in
			  Options.set_steps_bound old_steps;
			  Worker.post_message (marshal (id,result))
			| OptionSteps i -> Options.set_steps_bound i)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. trywhy3"
End:
*)
