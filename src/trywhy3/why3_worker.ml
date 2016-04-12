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


(* Interface to Why3 and Alt-Ergo *)

let why3_conf_file = "/trywhy3.conf"

open Why3
open Format
open Worker_proto

let () = log_time ("Initialising why3 worker: start ")


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

let () = log_time ("Initialising why3 worker: end ")



let split_trans = Trans.lookup_transform_l "split_goal_wp" env

let task_to_string t =
  ignore (flush_str_formatter ());
  Driver.print_task alt_ergo_driver str_formatter t;
  flush_str_formatter ()

let gen_id =
  let c = ref 0 in
  fun () -> incr c; "id" ^ (string_of_int !c)

let send msg =
  Worker.post_message (marshal msg)

let why3_parse_theories theories =
  let theories =
    Stdlib.Mstr.fold
      (fun thname th acc ->
       let loc =
         Opt.get_def Loc.dummy_position th.Theory.th_name.Ident.id_loc
       in
       (loc, (thname, th)) :: acc) theories []
  in
  let theories = List.sort  (fun (l1,_) (l2,_) -> Loc.compare l1 l2) theories in
  List.iter
    (fun (_, (th_name, th)) ->
     let th_id = gen_id () in
     let tasks = Task.split_theory th None None in
     List.iter
       (fun task ->
	let (id,expl,_) = Termcode.goal_expl_task ~root:true task in
        let task_name = match expl with
          | Some s -> s
          | None -> id.Ident.id_string
        in
	let task_id = gen_id () in
	List.iter
	  (fun vc ->
	   let vc_id = gen_id () in
	   let id, expl, _ = Termcode.goal_expl_task ~root:false vc in
	   let expl = match expl with
             | Some s -> s
             | None -> id.Ident.id_string
           in
	   let msg = Tasks ((th_id, th_name),
			    (task_id, task_name),
			    (vc_id, expl, task_to_string vc))
	   in
	   send msg)
	  (Trans.apply split_trans task)
       ) (List.rev tasks)
    ) theories

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
  let result =
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
           (loc, modname ^ ".main() returns " ^ result)
           :: acc
         with Not_found -> acc)
	modules []
    in
    match mods with
    | [] -> Error "No main function found"
    | _ ->
       let s =
	 List.sort
           (fun (l1,_) (l2,_) -> Loc.compare l2 l1)
           mods
       in
       (Result (List.rev_map snd s) )
  in
  send result

let temp_file_name = "/input.mlw"

let () = Sys_js.register_file ~name:temp_file_name ~content:""

let why3_run f lang code =
  try
    log_time "Why3 worker : start writing file";
    let ch = open_out temp_file_name in
    output_string ch code;
    close_out ch;
    log_time "Why3 worker : stop writing file";

    (* TODO: add a function Env.read_string or Env.read_from_lexbuf ? *)
    log_time "Why3 worker : start parsing file";

    let theories = Env.read_file lang env temp_file_name in
    log_time "Why3 worker : stop parsing file";
    f theories
  with
  | Loc.Located(loc,e') ->
     let _, l, b, e = Loc.get loc in
     send (ErrorLoc ((l-1,b, l-1, e),
		     Pp.sprintf
		       "error line %d, columns %d-%d: %a" l b e
		       Exn_printer.exn_printer e'))
  | e ->
     send (Error (Pp.sprintf
		    "unexpected exception: %a (%s)" Exn_printer.exn_printer e
		    (Printexc.to_string e)))


let () =
  
  Worker.set_onmessage
    (fun ev ->

     log_time ("Entering why3 worker ");
     let ev = unmarshal ev in
     log_time ("After unmarshal ");
     match ev with
     | ParseBuffer code ->
       why3_run why3_parse_theories Env.base_language code
     | ExecuteBuffer code ->
	why3_run why3_execute Mlw_module.mlw_language code
    )
(*
Local Variables:
compile-command: "unset LANG; make -C ../.. src/trywhy3/trywhy3.js"
End:
*)
