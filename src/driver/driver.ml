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
open Wstdlib
open Ident
open Term
open Decl
open Theory
open Task
open Printer
open Trans
open Driver_ast
open Call_provers

let driver_debug =
  Debug.register_flag "interm_task"
    ~desc:"Print intermediate task generated during processing of a driver"

(** drivers *)

type driver = {
  drv_env         : Env.env;
  drv_printer     : string option;
  drv_filename    : string option;
  drv_transform   : string list;
  drv_prelude     : prelude;
  drv_thprelude   : prelude_map;
  drv_thuse       : (theory * theory) Mid.t;
  drv_blacklist   : string list;
  drv_meta        : (theory * Stdecl.t) Mid.t;
  drv_res_parser  : prover_result_parser;
  drv_tag         : int;
}

(** parse a driver file *)

let load_plugin dir (byte,nat) =
  let file = if Dynlink.is_native then nat else byte in
  let file = Filename.concat dir file in
  Dynlink.loadfile_private file

let load_file file =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let to_close = Stack.create () in
  Stack.push c to_close;
  let input_lexer filename =
    let c = open_in filename in
    Stack.push c to_close;
    let lb = Lexing.from_channel c in
    Loc.set_file filename lb;
    lb
  in
  let f = Driver_lexer.parse_file input_lexer lb in
  Stack.iter close_in to_close;
  f

exception Duplicate    of string
exception UnknownType  of (string list * string list)
exception UnknownLogic of (string list * string list)
exception UnknownProp  of (string list * string list)
exception FSymExpected of lsymbol
exception PSymExpected of lsymbol

let load_driver_absolute = let driver_tag = ref (-1) in fun env file extra_files ->
  let prelude   = ref [] in
  let regexps   = ref [] in
  let exitcodes = ref [] in
  let filename  = ref None in
  let printer   = ref None in
  let model_parser = ref "no_model" in
  let transform = ref [] in
  let timeregexps = ref [] in
  let stepregexps = ref [] in
  let blacklist = Queue.create () in

  let set_or_raise loc r v error = match !r with
    | Some _ -> raise (Loc.Located (loc, Duplicate error))
    | None   -> r := Some v
  in
  let add_to_list r v = (r := v :: !r) in
  let add_global (loc, g) = match g with
    | Prelude s -> add_to_list prelude s
    | RegexpValid s -> add_to_list regexps (s, Valid)
    | RegexpInvalid s -> add_to_list regexps (s, Invalid)
    | RegexpTimeout s -> add_to_list regexps (s, Timeout)
    | RegexpOutOfMemory s -> add_to_list regexps (s, OutOfMemory)
    | RegexpStepLimitExceeded s ->
      add_to_list regexps (s, StepLimitExceeded)
    | RegexpUnknown (s,t) -> add_to_list regexps (s, Unknown t)
    | RegexpFailure (s,t) -> add_to_list regexps (s, Failure t)
    | TimeRegexp r -> add_to_list timeregexps (Call_provers.timeregexp r)
    | StepRegexp (r,ns) ->
      add_to_list stepregexps (Call_provers.stepregexp r ns)
    | ExitCodeValid s -> add_to_list exitcodes (s, Valid)
    | ExitCodeInvalid s -> add_to_list exitcodes (s, Invalid)
    | ExitCodeTimeout s -> add_to_list exitcodes (s, Timeout)
    | ExitCodeStepLimitExceeded s ->
      add_to_list exitcodes (s, StepLimitExceeded)
    | ExitCodeUnknown (s,t) -> add_to_list exitcodes (s, Unknown t)
    | ExitCodeFailure (s,t) -> add_to_list exitcodes (s, Failure t)
    | Filename s -> set_or_raise loc filename s "filename"
    | Printer s -> set_or_raise loc printer s "printer"
    | ModelParser s -> model_parser := s
    | Transform s -> add_to_list transform s
    | Plugin files -> load_plugin (Filename.dirname file) files
    | Blacklist sl -> List.iter (fun s -> Queue.add s blacklist) sl
  in
  let f = load_file file in
  List.iter add_global f.f_global;

  let thprelude     = ref Mid.empty in
  let meta          = ref Mid.empty in
  let qualid        = ref [] in
  let thuse         = ref Mid.empty in

  let find_pr th (loc,q) = try ns_find_pr th.th_export q
    with Not_found -> raise (Loc.Located (loc, UnknownProp (!qualid,q)))
  in
  let find_ls th (loc,q) = try ns_find_ls th.th_export q
    with Not_found -> raise (Loc.Located (loc, UnknownLogic (!qualid,q)))
  in
  let find_ts th (loc,q) = try ns_find_ts th.th_export q
    with Not_found -> raise (Loc.Located (loc, UnknownType (!qualid,q)))
  in
  let find_fs th q =
    let ls = find_ls th q in
    if ls.ls_value = None then raise (FSymExpected ls) else ls in
  let find_ps th q =
    let ls = find_ls th q in
    if ls.ls_value <> None then raise (PSymExpected ls) else ls in
  let add_meta th td m =
    let s = try snd (Mid.find th.th_name !m) with Not_found -> Stdecl.empty in
    m := Mid.add th.th_name (th, Stdecl.add td s) !m
  in
  (* th_uc is the theory built with the uses forced by the driver *)
  let add_local th th_uc = function
    | Rprelude s ->
        let l = Mid.find_def [] th.th_name !thprelude in
        thprelude := Mid.add th.th_name (s::l) !thprelude;
        th_uc
    | Rsyntaxts (q,s,b) ->
        let td = syntax_type (find_ts th q) s b in
        add_meta th td meta;
        th_uc
    | Rsyntaxfs (q,s,b) ->
        let td = syntax_logic (find_fs th q) s b in
        add_meta th td meta;
        th_uc
    | Rsyntaxps (q,s,b) ->
        let td = syntax_logic (find_ps th q) s b in
        add_meta th td meta;
        th_uc
    | Rremovepr (q) ->
        let td = remove_prop (find_pr th q) in
        add_meta th td meta;
        th_uc
    | Rremoveall ->
      let it key _ = match (Mid.find key th.th_known).d_node with
        | Dprop (_,symb,_) -> add_meta th (remove_prop symb) meta
        | _ -> ()
      in
      Mid.iter it th.th_local;
      th_uc
    | Rliteral (q,s,b) ->
        let cs = syntax_literal (find_ts th q) s b in
        add_meta th cs meta;
        th_uc
    | Rmeta (s,al) ->
        let rec ty_of_pty = function
          | PTyvar x ->
              Ty.ty_var (Ty.tv_of_string x)
          | PTyapp ((loc,_) as q,tyl) ->
              let ts = find_ts th q in
              let tyl = List.map ty_of_pty tyl in
              Loc.try2 ~loc Ty.ty_app ts tyl
          | PTuple tyl ->
              let ts = Ty.ts_tuple (List.length tyl) in
              Ty.ty_app ts (List.map ty_of_pty tyl)
        in
        let convert = function
          | PMAty (PTyapp (q,[]))
                     -> MAts (find_ts th q)
          | PMAty ty -> MAty (ty_of_pty ty)
          | PMAfs q  -> MAls (find_fs th q)
          | PMAps q  -> MAls (find_ps th q)
          | PMApr q  -> MApr (find_pr th q)
          | PMAstr s -> MAstr s
          | PMAint i -> MAint i
        in
        let m = lookup_meta s in
        let td = create_meta m (List.map convert al) in
        add_meta th td meta;
        th_uc
    | Ruse (loc,q) ->
      let file, th = Lists.chop_last q in
      let th = Loc.try3 ~loc Env.read_theory env file th in
      Theory.use_export th_uc th
  in
  let add_local th th_uc (loc,rule) = Loc.try2 ~loc add_local th th_uc rule in
  let add_theory { thr_name = (loc,q); thr_rules = trl } =
    let f,id = Lists.chop_last q in
    let th = Loc.try3 ~loc Env.read_theory env f id in
    let th_uc = Theory.create_theory (Ident.id_fresh ~loc ("driver export for "^th.th_name.id_string)) in
    qualid := q;
    let th_uc' = List.fold_left (add_local th) th_uc trl in
    if th_uc != th_uc' then
      thuse := Mid.add th.th_name (th, Theory.close_theory th_uc') !thuse
  in
  List.iter add_theory f.f_rules;
  List.iter (fun f -> List.iter add_theory (load_file f).f_rules) extra_files;
  incr driver_tag;
  {
    drv_env         = env;
    drv_printer     = !printer;
    drv_prelude     = List.rev !prelude;
    drv_filename    = !filename;
    drv_transform   = List.rev !transform;
    drv_thprelude   = Mid.map List.rev !thprelude;
    drv_blacklist   = Queue.fold (fun l s -> s :: l) [] blacklist;
    drv_meta        = !meta;
    drv_res_parser =
      {
      prp_regexps     = List.rev !regexps;
      prp_timeregexps = List.rev !timeregexps;
      prp_stepregexps = List.rev !stepregexps;
      prp_exitcodes   = List.rev !exitcodes;
      prp_model_parser = Model_parser.lookup_model_parser !model_parser
    };
    drv_tag         = !driver_tag;
    drv_thuse       = !thuse;
  }

let syntax_map drv =
  let addth _ (_,tds) acc = Stdecl.fold Printer.add_syntax_map tds acc in
  Mid.fold addth drv.drv_meta Mid.empty

(** apply drivers *)

exception UnknownSpec of string

let filename_regexp = Str.regexp "%\\(.\\)"

let get_filename drv input_file theory_name goal_name =
  let sanitize = Ident.sanitizer
    Ident.char_to_alnumus Ident.char_to_alnumus in
  let file = match drv.drv_filename with
    | Some f -> f
    | None -> "%f-%t-%g.dump"
  in
  let replace s = match Str.matched_group 1 s with
    | "%" -> "%"
    | "f" -> sanitize input_file
    | "t" -> sanitize theory_name
    | "g" -> sanitize goal_name
    | s   -> raise (UnknownSpec s)
  in
  Str.global_substitute filename_regexp replace file

let get_extension drv =
  match drv.drv_filename with
  | None -> ".dump"
  | Some f ->
      (* We search a bit naively for the first dot starting from the end, but
         this will work fine for all current "filename" attributes in Why3
         drivers *)
      let i = String.rindex f '.' in
      String.sub f i (String.length f - i)

let file_of_task drv input_file theory_name task =
  get_filename drv input_file theory_name (task_goal task).pr_name.id_string

let file_of_theory drv input_file th =
  get_filename drv input_file th.th_name.Ident.id_string "null"

let call_on_buffer ~command ~limit ~gen_new_file ?inplace ~filename
    ~printer_mapping drv buffer =
  Call_provers.call_on_buffer
    ~command ~limit ~gen_new_file ~res_parser:drv.drv_res_parser
    ~filename ~printer_mapping ?inplace buffer

(** print'n'prove *)

exception NoPrinter

let update_task = let ht = Hint.create 5 in fun drv ->
    let update task0 =
      (** add requested theorie *)
      let task0 = Mid.fold (fun _ (th,th') task ->
          let tdcs = (Task.find_clone_tds task0 th).tds_set in
          Stdecl.fold (fun tdc task -> match tdc.td_node with
              | Use _ -> Task.use_export task th'
              | Clone (_,_) ->
                  (** We do nothing in case of clone *)
                  task
              | _ -> assert false
            ) tdcs task
        ) drv.drv_thuse task0
      in
      (** apply metas *)
      let task0 = Mid.fold (fun _ (th,tdms) task ->
          let tdcs = (Task.find_clone_tds task0 th).tds_set in
          Stdecl.fold (fun tdc task ->
              Stdecl.fold (fun tdm task -> match tdc.td_node with
                  | Use _ -> add_tdecl task tdm
                  | Clone (_,sm) ->
                      let tdm = Theory.clone_meta tdm th sm in
                      Opt.fold add_tdecl task tdm
                  | _ -> assert false
                ) tdms task
            ) tdcs task
        ) drv.drv_meta task0
      in
      task0
    in
  function
  | Some {task_decl = {td_node = Decl {d_node = Dprop (Pgoal,_,_)}} as goal;
          task_prev = task} ->
      (* we cannot add metas nor memoize after goal *)
      let update = try Hint.find ht drv.drv_tag with Not_found ->
        let upd = Trans.store update in
        Hint.add ht drv.drv_tag upd; upd in
      let task = Trans.apply update task in
      add_tdecl task goal
    | task -> update task

(* Apply driver's transformations to the task *)
let prepare_task drv task =
  let lookup_transform t =
    let stat_name = "gnatwhy3.transformations." ^ t in
    stat_name, lookup_transform t drv.drv_env, t in
  let transl = List.map lookup_transform drv.drv_transform in
  let apply task (stat_name, tr, name) =
    let task = Trans.apply tr task in
    Util.timing_step_completed stat_name;
    Debug.dprintf driver_debug "Task after transformation: %s\n%a@."
      name Pretty.print_task task;
    task
  in
  Debug.dprintf driver_debug "Task before driver's transformation\n%a@."
    Pretty.print_task task;
  let task = update_task drv task in
  Debug.dprintf driver_debug "Task after update\n%a@."
    Pretty.print_task task;
  List.fold_left apply task transl

let print_task_prepared ?old drv fmt task =
  let p = match drv.drv_printer with
    | None -> raise NoPrinter
    | Some p -> p
  in
  let printer_args = { Printer.env = drv.drv_env;
      prelude     = drv.drv_prelude;
      th_prelude  = drv.drv_thprelude;
      blacklist   = drv.drv_blacklist;
      printer_mapping = get_default_printer_mapping;
    } in
  let printer = lookup_printer p printer_args in
  fprintf fmt "@[%a@]@?" (printer ?old) task;
  printer_args.printer_mapping

let print_task ?old drv fmt task =
  let task = prepare_task drv task in
  let _ = print_task_prepared ?old drv fmt task in
  ()

let print_theory ?old drv fmt th =
  let task = Task.use_export None th in
  print_task ?old drv fmt task

let file_name_of_task ?old ?inplace ?interactive drv task =
  match old, inplace with
    | Some fn, Some true ->
        (* Example: Isabelle. No file should be generated, it should be done
           in_place and we keep the same file. *)
        false, fn
    | Some fn, _ when interactive <> Some true ->
        (* Example: cvc4. If a file is provided, it means it was passed to
           schedule_proof_attempt via its save_to argument. So we ask to erase
           and regenerate the file (the advantage is that we decide the location
           of the file).
        *)
        false, fn
    | Some _, _ ->
        (* Example: Coq.
           For Coq, the interactively edited file should be kept (not erased)
           and a new temp file is generated using the old one.
        *)
        let pr = Task.task_goal task in
        let fn = match pr.pr_name.id_loc with
          | Some loc -> let fn,_,_,_ = Loc.get loc in Filename.basename fn
          | None -> "" in
        let fn = try Filename.chop_extension fn with Invalid_argument _ -> fn in
        true, get_filename drv fn "T" pr.pr_name.id_string
    | _ ->
        (* Example: cvc4 without ?save_to argument
           No file were provided. We have to generate a new one.
        *)
        let pr = Task.task_goal task in
        let fn = match pr.pr_name.id_loc with
          | Some loc -> let fn,_,_,_ = Loc.get loc in Filename.basename fn
          | None -> "" in
        let fn = try Filename.chop_extension fn with Invalid_argument _ -> fn in
        true, get_filename drv fn "T" pr.pr_name.id_string

let prove_task_prepared ~command ~limit ?old ?inplace ?interactive drv task =
  let buf = Buffer.create 1024 in
  let fmt = formatter_of_buffer buf in
  let old_channel = Opt.map open_in old in
  let gen_new_file, filename = file_name_of_task ?old ?inplace ?interactive drv task in
  let printer_mapping =
    if Opt.get_def false inplace || interactive = Some true then
      print_task_prepared ?old:old_channel drv fmt task
    else
      print_task_prepared drv fmt task
  in
  pp_print_flush fmt ();
  Opt.iter close_in old_channel;
  let res =
    call_on_buffer ~command ~limit ~gen_new_file
                   ?inplace ~filename ~printer_mapping drv buf in
  Buffer.reset buf;
  ServerCall res

let prove_task ~command ~limit ?old ?inplace ?interactive drv task =
  let task = prepare_task drv task in
  prove_task_prepared ~command ~limit ?interactive ?old ?inplace drv task

(* exception report *)

let string_of_qualid thl idl =
  String.concat "." thl ^ "." ^ String.concat "." idl

let () = Exn_printer.register (fun fmt exn -> match exn with
  | NoPrinter -> Format.fprintf fmt
      "No printer specified in the driver file"
  | Duplicate s -> Format.fprintf fmt
      "Duplicate %s specification" s
  | UnknownType (thl,idl) -> Format.fprintf fmt
      "Unknown type symbol %s" (string_of_qualid thl idl)
  | UnknownLogic (thl,idl) -> Format.fprintf fmt
      "Unknown logical symbol %s" (string_of_qualid thl idl)
  | UnknownProp (thl,idl) -> Format.fprintf fmt
      "Unknown proposition %s" (string_of_qualid thl idl)
  | UnknownSpec s -> Format.fprintf fmt
      "Unknown format specifier '%%%s', use %%f, %%t or %%g" s
  | FSymExpected ls -> Format.fprintf fmt
      "%a is not a function symbol" Pretty.print_ls ls
  | PSymExpected ls -> Format.fprintf fmt
      "%a is not a predicate symbol" Pretty.print_ls ls
  | e -> raise e)
