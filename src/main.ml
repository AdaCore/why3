(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Theory
open Driver
open Transform

let files = Queue.create ()
let parse_only = ref false
let type_only = ref false
let debug = ref false
let loadpath = ref []
let driver = ref None
type which_goals =
  | Gall
  | Gtheory of string
  | Ggoal of string
let which_goals = ref Gall
let timeout = ref 10
let call = ref false
let output = ref None
let list_printers = ref false
let list_transforms = ref false

let () = 
  Arg.parse 
    ["--parse-only", Arg.Set parse_only, "stops after parsing";
     "--type-only", Arg.Set type_only, "stops after type-checking";
     "--debug", Arg.Set debug, "sets the debug flag";
     "-I", Arg.String (fun s -> loadpath := s :: !loadpath), 
     "<dir>  adds dir to the loadpath";
     "--all_goals", Arg.Unit (fun () -> which_goals := Gall), 
     "apply on all the goals of the file";
     "--goals_of", Arg.String (fun s -> which_goals := Gtheory s), 
     "apply on all the goals of the theory given (ex. --goal T)";
     "--goal", Arg.String (fun s -> which_goals := Ggoal s), 
     "apply only on the goal given (ex. --goal T.g)";
     "--output", Arg.String (fun s -> output := Some s), 
     "choose to output each goals in the directory given.\
 Can't be used with --call";
     "--call", Arg.Set call, 
     "choose to call the prover on each goals.\
 Can't be used with --output"; (* Why not? *)
     "--driver", Arg.String (fun s -> driver := Some s),
     "<file>  set the driver file";
     "--timeout", Arg.Set_int timeout, "set the timeout used when calling provers (0 unlimited, default 10)";
     "--list-printers", Arg.Set list_printers, "list the printers registered";
     "--list-transforms", Arg.Set list_transforms, "list the transformation registered";
    ]
    (fun f -> Queue.push f files)
    "usage: why [options] files..."

let () = 
  match !output with
    | None when not !call -> type_only := true
    | Some _ when !call -> 
        eprintf "--output and --call can't be use at the same time.(Whynot?)@.";
        exit 1
    | _ -> ()

let timeout = if !timeout <= 0 then None else Some !timeout

(*
let transformation l = 
  let t1 = Simplify_recursive_definition.t in
  let t2 = Inlining.all in
  List.map (fun (t,c) ->
              let c = if !simplify_recursive 
              then Transform.apply t1 c
              else c in
              let c = if !inlining then Transform.apply t2 c
              else c in
              (t,c)) l
*)
let rec report fmt = function
  | Lexer.Error e ->
      fprintf fmt "lexical error: %a" Lexer.report e;
  | Loc.Located (loc, e) ->
      fprintf fmt "%a%a" Loc.report_position loc report e
  | Parsing.Parse_error ->
      fprintf fmt "syntax error"
  | Typing.Error e ->
      Typing.report fmt e
  | Context.UnknownIdent i ->
      fprintf fmt "anomaly: unknownident %s" i.Ident.id_short
  | Driver.Error e ->
      Driver.report fmt e
  | Dynlink.Error e ->
      fprintf fmt "Dynlink : %s" (Dynlink.error_message e)
  | e -> fprintf fmt "anomaly: %s" (Printexc.to_string e)

(*
let transform env l =
  let l = 
    List.map 
      (fun t -> t, Context.use_export (Context.init_context env) t) 
      l
  in
  (*let l = transformation l in*)
  if !print_stdout then 
    List.iter 
      (fun (t,ctxt) -> Pretty.print_named_context
        std_formatter t.th_name.Ident.id_long ctxt) l
  else match !driver with
    | None ->
	()
    | Some file ->

	begin match l with
	  | (_,ctxt) :: _ -> begin match extract_goals ctxt with
	      | g :: _ -> 
		  Driver.print_context drv std_formatter g
	      | [] -> 
		  eprintf "no goal@."
	    end
	  | [] -> ()
	end
*)


let extract_goals env drv acc th =
  let ctxt = Context.use_export (Context.init_context env) th in
  let ctxt = Driver.apply_before_split drv ctxt in
  let l = Transform.apply Transform.split_goals ctxt in
  let l = List.rev_map (fun ctxt -> (th,ctxt)) l in
  List.rev_append l acc

let file_sanitizer = Ident.sanitizer Ident.char_to_alnumus Ident.char_to_alnumus

let do_file env drv filename_printer file =
  if !parse_only then begin
    let c = open_in file in
    let lb = Lexing.from_channel c in
    Loc.set_file file lb;
    let _ = Lexer.parse_logic_file lb in 
    close_in c
  end else begin
    let m = Typing.read_file env file in
    if not !type_only then
      let drv =  
        match drv with
          | None -> eprintf "a driver is needed@."; exit 1
          | Some drv -> drv in
      (* Extract the goal(s) *)
      let goals = 
        match !which_goals with
          | Gall ->  Mnm.fold (fun _ th acc -> extract_goals env drv acc th) m []
          | Gtheory s ->  
              begin
                try 
                  extract_goals env drv [] (Mnm.find s m)
                with Not_found -> 
                  eprintf "File %s : --goals_of : Unknown theory %s@." file s; exit 1
              end
          | Ggoal s ->
              let l = Str.split (Str.regexp "\\.") s in
              let tname, l = 
                match l with
                  | [] | [_] -> 
                      eprintf "--goal : Must be a qualified name (%s)@." s;
                      exit 1
                  | a::l -> a,l in
              let rec find_pr ns = function
                | [] -> assert false
                | [a] -> Mnm.find a ns.ns_pr
                | a::l -> find_pr (Mnm.find a ns.ns_ns) l in
              let th =try Mnm.find tname m with Not_found -> 
                eprintf "File %s : --goal : Unknown theory %s@." file tname; exit 1 in
              let pr = try find_pr th.th_export l with Not_found ->
                eprintf "File %s : --goal : Unknown goal %s@." file s ; exit 1 in
              let goals = extract_goals env drv [] th in
              List.filter (fun (_,ctxt) ->
                             match ctxt.ctxt_decl.d_node with
                               | Dprop (_,pr',_) -> pr == pr'
                               | _ -> assert false) goals in
      (* Apply transformations *)
      let goals = List.map 
        (fun (th,ctxt) -> (th,Driver.apply_after_split drv ctxt))
        goals in
      (* Pretty-print the goals or call the prover *)
      match !output with
        | None (* we are in the call mode *) -> 
            let call (th,ctxt) = 
              let res = Driver.call_prover ~debug:!debug ?timeout drv ctxt in
              printf "%s %s %s : %a@." 
                file th.th_name.Ident.id_short 
                (pr_name (goal_of_ctxt ctxt)).Ident.id_long
                Call_provers.print_prover_result res in
            List.iter call goals
        | Some dir (* we are in the output mode *) -> 
            let file = 
              let file = Filename.basename file in
              let file = Filename.chop_extension file in
              Ident.id_unique filename_printer 
                (Ident.id_register (Ident.id_fresh file)) in
            let ident_printer = Ident.create_ident_printer 
              ~sanitizer:file_sanitizer [] in
            List.iter 
              (fun (th,ctxt) ->
                 let cout = 
                   if dir = "-" 
                   then stdout
                   else
                     let filename = 
                       Driver.filename_of_goal drv ident_printer 
                         file th.th_name.Ident.id_short ctxt in
                     let filename = Filename.concat dir filename in
                     open_out filename in
                 let fmt = formatter_of_out_channel cout in
                 fprintf fmt "%a@?" (Driver.print_context drv) ctxt;
                 close_out cout) goals
  end

let () =
  try
    let env = create_env (Typing.retrieve !loadpath) in
    let drv = match !driver with
      | None -> None
      | Some file -> Some (load_driver file env) in
    if !list_printers then 
      begin
        printf "@[<hov 2>printers :@\n%a@]@."
          (Pp.print_list Pp.newline Pp.string) (Driver.list_printers ());
        exit 0
      end;
    if !list_transforms then 
      begin
        printf "@[<hov 2>transforms :@\n%a@]@."
          (Pp.print_list Pp.newline Pp.string) (Driver.list_transforms ());
        exit 0          
      end;
    let filename_printer = Ident.create_ident_printer 
      ~sanitizer:file_sanitizer [] in
    Queue.iter (do_file env drv filename_printer) files
  with e when not !debug ->
    eprintf "%a@." report e;
    exit 1

(*
Local Variables: 
compile-command: "unset LANG; make -C .. test"
End: 
*)

(****

#load "hashcons.cmo";;
#load "name.cmo";;
#load "term.cmo";;
#load "pp.cmo";;
#load "pretty.cmo";;
#install_printer Name.print;;
#install_printer Pretty.print_ty;;
#install_printer Pretty.print_term;;

open Term

let alpha = Name.from_string "alpha"
let var_alpha = Ty.ty_var alpha

let list = Ty.create_tysymbol (Name.from_string "list") [alpha] None

let list_alpha = Ty.ty_app list [var_alpha]
let list_list_alpha = Ty.ty_app list [list_alpha]

let nil = create_fsymbol (Name.from_string "nil") ([], list_alpha)
let t_nil = t_app nil [] list_alpha
let tt_nil = t_app nil [] list_list_alpha

let cons = create_fsymbol (Name.from_string "cons") 
  ([var_alpha; list_alpha], list_alpha)

let int_ = Ty.create_tysymbol (Name.from_string "int") [] None

let _ = t_app cons [t_nil; tt_nil] list_list_alpha

****)
