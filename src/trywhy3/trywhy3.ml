(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* simple helpers *)

let get_opt o = Js.Opt.get o (fun () -> assert false)

let log s = Firebug.console ## log (Js.string s)


(* module for generating HTML elements *)

module Html = struct

let d = Dom_html.document

let node x = (x : #Dom.node Js.t :> Dom.node Js.t)

let of_string s = node (d##createTextNode (Js.string s))

let img i =
  let x = Dom_html.createImg d in
  x##src <- Js.string i;
  x##height <- 12;
  (* X##align <- Js.string "bottom"; *)
  node x

let img_accept () = img "accept32.png"
let img_help () = img "help32.png"
let img_bug () = img "bug32.png"

let par nl =
  let x = d##createElement (Js.string "p") in
  List.iter (Dom.appendChild x) nl;
  node x

let ul nl =
  let x = d##createElement (Js.string "ul") in
  List.iter
    (fun n ->
      let y =  d##createElement (Js.string "li") in
      List.iter (Dom.appendChild y) n;
      Dom.appendChild x (node y))
    nl;
  node x

end


(* Interface to Why3 and Alt-Ergo *)

let why3_conf_file = "/trywhy3.conf"

open Why3
open Format

(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config (Some why3_conf_file)
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* One prover named Alt-Ergo in the config file *)
let alt_ergo : Whyconf.config_prover =
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else snd (Whyconf.Mprover.choose provers)

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

let alt_ergo_driver : Driver.driver =
  try
    Printexc.record_backtrace true;
    Driver.load_driver env alt_ergo.Whyconf.driver []
  with e ->
    let s = Printexc.get_backtrace () in
    eprintf "Failed to load driver for alt-ergo: %a@.%s@."
      Exn_printer.exn_printer e s;
  exit 1

module SAT = (val (Sat_solvers.get_current ()) : Sat_solvers.S)
module FE = Frontend.Make (SAT)

let print_status fmt _d status steps =
  match status with
  | FE.Unsat _dep ->
    fprintf fmt "Proved (%Ld steps)" steps
  | FE.Inconsistent -> ()
    (* fprintf fmt "Inconsistent assumption" *)
  | FE.Unknown _t | FE.Sat _t ->
      fprintf fmt "Unknown (%Ld steps)@." steps

type prover_answer = Valid | Unknown of string | Error of string

let report_status report _d status _steps =
  match status with
  | FE.Unsat _dep -> report Valid
  | FE.Inconsistent -> ()
  | FE.Unknown _t | FE.Sat _t -> report (Unknown "unknown")

let run_alt_ergo_on_task t =
  (* printing the task in a string *)
  Driver.print_task alt_ergo_driver str_formatter t;
  let text = flush_str_formatter () in
  let lb = Lexing.from_string text in
(* from Alt-Ergo, src/main/frontend.ml *)
  let a = Why_parser.file Why_lexer.token lb in
  Parsing.clear_parser ();
  let ltd, _typ_env = Why_typing.file false Why_typing.empty_env a in
  match Why_typing.split_goals ltd with
  | [d] ->
    let d = Cnf.make (List.map (fun (f, _env) -> f, true) d) in
    SAT.reset_steps ();
    let stat = ref (Error "no answer from Alt-Ergo") in
    let f s = stat := s in
    begin
      try
        let _x = Queue.fold (FE.process_decl (report_status f))
          (SAT.empty (), true, Explanation.empty) d
        in
        !stat
      with Sat_solvers.StepsLimitReached -> Unknown "steps limit reached"
    end
  | _ -> Error "zero or more than 1 goal to solve"

let split_trans = Trans.lookup_transform_l "split_goal_wp" env

let why3_prove theories =
  let theories =
    Stdlib.Mstr.fold
      (fun thname th acc ->
        let tasks = Task.split_theory th None None in
        let tasks = List.rev_map
          (fun t ->
            let (id,expl,_) = Termcode.goal_expl_task ~root:true t in
            let expl = match expl with
              | Some s -> s
              | None -> id.Ident.id_string
            in
            let tl = Trans.apply split_trans t in
            let tasks =
              List.map
                (fun task ->
                  let (id,expl,_) = Termcode.goal_expl_task ~root:false task in
                  let expl = match expl with
                    | Some s -> s
                    | None -> id.Ident.id_string
                  in
                  let result = run_alt_ergo_on_task task in
                  let img,res = match result with
                    | Valid -> Html.img_accept, expl
                    | Unknown s -> Html.img_help, expl ^ " (" ^ s ^ ")"
                    | Error s -> Html.img_bug, expl ^ " (" ^ s ^ ")"
                  in
                  [img (); Html.of_string (" " ^ res)])
                tl
            in
            [Html.of_string expl; Html.ul tasks])
          tasks
        in
        let loc =
          Opt.get_def Loc.dummy_position th.Theory.th_name.Ident.id_loc
        in
        (loc,[ Html.of_string thname; Html.ul tasks]) :: acc)
      theories []
  in
  let s =
    List.sort
      (fun (l1,_) (l2,_) -> Loc.compare l2 l1)
      theories
  in
  Html.ul (List.rev_map snd s)

let execute_symbol m fmt ps =
  match Mlw_decl.find_definition m.Mlw_module.mod_known ps with
  | None ->
    fprintf fmt "function '%s' has no definition"
      ps.Mlw_expr.ps_name.Ident.id_string
  | Some d ->
    let lam = d.Mlw_expr.fun_lambda in
    match lam.Mlw_expr.l_args with
    | [pvs] when
        Mlw_ty.ity_equal pvs.Mlw_ty.pv_ity Mlw_ty.ity_unit ->
      begin
        let spec = lam.Mlw_expr.l_spec in
        let eff = spec.Mlw_ty.c_effect in
        let writes = eff.Mlw_ty.eff_writes in
        let body = lam.Mlw_expr.l_expr in
        try
          let res, _final_env =
            Mlw_interp.eval_global_expr env m.Mlw_module.mod_known
              m.Mlw_module.mod_theory.Theory.th_known writes body
          in
          match res with
          | Mlw_interp.Normal v -> Mlw_interp.print_value fmt v
          | Mlw_interp.Excep(x,v) ->
            fprintf fmt "exception %s(%a)"
              x.Mlw_ty.xs_name.Ident.id_string Mlw_interp.print_value v
          | Mlw_interp.Irred e ->
            fprintf fmt "cannot execute expression@ @[%a@]"
              Mlw_pretty.print_expr e
          | Mlw_interp.Fun _ ->
            fprintf fmt "result is a function"
        with e ->
          fprintf fmt
            "failure during execution of function: %a (%s)"
            Exn_printer.exn_printer e
            (Printexc.to_string e)
    end
  | _ ->
    fprintf fmt "Only functions with one unit argument can be executed"

let why3_execute (modules,_theories) =
  let mods =
    Stdlib.Mstr.fold
      (fun _k m acc ->
        let th = m.Mlw_module.mod_theory in
        let modname = th.Theory.th_name.Ident.id_string in
        try
          let ps =
            Mlw_module.ns_find_ps m.Mlw_module.mod_export ["main"]
          in
          let result = Pp.sprintf "%a" (execute_symbol m) ps in
          let loc =
            Opt.get_def Loc.dummy_position th.Theory.th_name.Ident.id_loc
          in
          (loc,[Html.of_string (modname ^ ".main() returns " ^ result)])
          :: acc
        with Not_found -> acc)
      modules []
  in
  match mods with
  | [] -> Html.par [Html.of_string "No main function found"]
  | _ ->
    let s =
      List.sort
        (fun (l1,_) (l2,_) -> Loc.compare l2 l1)
        mods
    in
    Html.ul (List.rev_map snd s)


(* Connecting Why3 calls to the interface *)

let temp_file_name = "/input.mlw"

let () = Sys_js.register_file ~name:temp_file_name ~content:""

let run_why3 f lang global text =
  let ch = open_out temp_file_name in
  output_string ch text;
  close_out ch;
  try
    (* TODO: add a function Env.read_string or Env.read_from_lexbuf ? *)
    let theories = Env.read_file lang env temp_file_name in
    f theories
  with
  | Loc.Located(loc,e') ->
    let (_,l,b,e) = Loc.get loc in
    ignore (Js.Unsafe.meth_call global "highlightError"
	      (Array.map Js.Unsafe.inject [| l-1; b; l-1; e |]));
    Html.par
      [Html.of_string
          (Pp.sprintf
             "error line %d, columns %d-%d: %a" l b e
             Exn_printer.exn_printer e')]
  | e ->
    Html.par
      [Html.of_string
          (Pp.sprintf
             "unexpected exception: %a (%s)" Exn_printer.exn_printer e
             (Printexc.to_string e))]

let add_why3_cmd buttonname f input_lang =
  let handler = Dom.handler
    (fun _ev ->
      let global = Js.Unsafe.global in
      let editor = Js.Unsafe.get global (Js.string "editor") in
      let lang = "en"
(*
        Js.to_string
          (Js.Unsafe.meth_call editor "getAttribute"
             [| Js.Unsafe.inject (Js.string "lang") |])
*)
      in
      let code = Js.to_string (Js.Unsafe.meth_call editor "getValue" [| |]) in
      log ("Why3 is running, lang = " ^ lang);
      let answer = run_why3 f input_lang global code in
      log "Why3 answer given";
      let console =
        get_opt (Dom_html.document ## getElementById (Js.string "console"))
      in
      (* remove the previous answer if any *)
      Js.Opt.iter (console##lastChild) (Dom.removeChild console);
      (* put the new answer *)
      Dom.appendChild console answer;
      (* give the focus back to the editor *)
      ignore (Js.Unsafe.meth_call editor "focus" [| |]);
      Js._false)
  in
  let button =
    get_opt (Dom_html.document ## getElementById (Js.string buttonname))
  in
  button ## onclick <- handler

let () =
  add_why3_cmd "prove" why3_prove Env.base_language;
  add_why3_cmd "run" why3_execute Mlw_module.mlw_language


(* Predefined examples *)

let add_file_example buttonname file =
  let handler = Dom.handler
    (fun _ev ->
      let text = Sysutil.file_contents file in
      let global = Js.Unsafe.global in
      let editor = Js.Unsafe.get global (Js.string "editor") in
      Js.Unsafe.set global (Js.string "loadedBuffer") (Js.string text);
      let loaded = Filename.basename file in
      Js.Unsafe.set global (Js.string "loadedFilename") (Js.string loaded);
      ignore (Js.Unsafe.meth_call global "replaceWithLoaded" [| |]);
      ignore (Js.Unsafe.meth_call editor "focus" [| |]);
      Js._false)
  in
  let button =
    get_opt (Dom_html.document ## getElementById (Js.string buttonname))
  in
  button ## onclick <- handler

let () =
  add_file_example "drinkers" "/drinkers.why";
(*  add_file_example "simplearith" "/simplearith.why";*)
  add_file_example "bin_mult" "/bin_mult.mlw";
  add_file_example "fact" "/fact.mlw";
  add_file_example "isqrt" "/isqrt.mlw";
  Options.set_steps_bound 100


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. src/trywhy3/trywhy3.js"
End:
*)
