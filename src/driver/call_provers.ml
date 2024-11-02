(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Model_parser

let debug = Debug.register_info_flag "call_prover"
  ~desc:"Print@ debugging@ messages@ about@ prover@ calls@ \
         and@ keep@ temporary@ files."

let debug_analyse_result = Debug.register_info_flag "analyse_result"
  ~desc:"Print@ debugging@ messages@ about@ analysis@ of@ answers@ of@ provers."

let debug_attrs = Debug.register_info_flag "print_model_attrs"
    ~desc:"Print@ attrs@ of@ identifiers@ and@ expressions@ in@ CE@ model."

(* BEGIN{proveranswer} anchor for automatic documentation, do not remove *)
type prover_answer =
  | Valid
  | Invalid
  | Timeout
  | OutOfMemory
  | StepLimitExceeded
  | Unknown of string
  | Failure of string
  | HighFailure of string
(* END{proveranswer} anchor for automatic documentation, do not remove *)

(* BEGIN{proverresult} anchor for automatic documentation, do not remove *)
type prover_result = {
  pr_answer : prover_answer;
  pr_status : Unix.process_status;
  pr_output : string;
  pr_time   : float;
  pr_steps  : int;		(* -1 if unknown *)
  pr_models : (prover_answer * model) list;
}
(* END{proverresult} anchor for automatic documentation, do not remove *)

(* BEGIN{resourcelimit} anchor for automatic documentation, do not remove *)
type resource_limits = {
  limit_time  : float;
  limit_mem   : int;
  limit_steps : int;
}
(* END{resourcelimit} anchor for automatic documentation, do not remove *)

let empty_limits = { limit_time = 0. ; limit_mem = 0; limit_steps = 0 }

let limit_max =
  let single_limit_max a b = if a = 0 || b = 0 then 0 else max a b in
  let single_limit_maxf a b = if a = 0. || b = 0. then 0. else max a b in
  fun a b ->
    { limit_time = single_limit_maxf a.limit_time b.limit_time;
      limit_steps = single_limit_max a.limit_steps b.limit_steps;
      limit_mem = single_limit_max a.limit_mem b.limit_mem; }

type timeunit =
  | Hour
  | Min
  | Sec
  | Msec

type timeregexp = {
  re    : Re.Str.regexp;
  group : timeunit array; (* i-th corresponds to the group i+1 *)
}

type stepregexp = {
  steps_re        : Re.Str.regexp;
  steps_group_num : int;
  (* the number of matched group which corresponds to the number of steps *)
}

let timeregexp s =
  let cmd_regexp = Re.Str.regexp "%\\(.\\)" in
  let nb = ref 0 in
  let l = ref [] in
  let add_unit x = l := (!nb,x) :: !l; incr nb; "\\([0-9]+.?[0-9]*\\)" in
  let replace s = match Re.Str.matched_group 1 s with
    | "%" -> "%"
    | "h" -> add_unit Hour
    | "m" -> add_unit Min
    | "s" -> add_unit Sec
    | "i" -> add_unit Msec
    | x -> failwith ("unknown time format specifier: %%" ^
            x ^ " (should be either %%h, %%m, %%s or %%i")
  in
  let s = Re.Str.global_substitute cmd_regexp replace s in
  let group = Array.make !nb Hour in
  List.iter (fun (i,u) -> group.(i) <- u) !l;
  { re = Re.Str.regexp s; group = group }

let rec grep_time out = function
  | [] -> None
  | re :: l ->
      begin try
        ignore (Re.Str.search_forward re.re out 0);
        let t = ref 0. in
        Array.iteri (fun i u ->
          let v = Re.Str.matched_group (succ i) out in
          match u with
          | Hour -> t := !t +. float_of_string v *. 3600.
          | Min  -> t := !t +. float_of_string v *. 60.
          | Sec  -> t := !t +. float_of_string v
          | Msec -> t := !t +. float_of_string v /. 1000.) re.group;
        Some !t
      with _ -> grep_time out l end

let stepregexp s_re s_group_num =
  {steps_re = (Re.Str.regexp s_re); steps_group_num = s_group_num}

let rec grep_steps out = function
  | [] -> None
  | re :: l ->
      begin try
        ignore (Re.Str.search_forward re.steps_re out 0);
        let v = Re.Str.matched_group (re.steps_group_num) out in
        Some(int_of_string v)
      with _ -> grep_steps out l end

(*
let grep_reason_unknown out =
  try
    (* TODO: this is SMTLIB specific, should be done in drivers instead *)
    let re = Re.Str.regexp "^(:reason-unknown \\([^)]*\\)" in
    ignore (Re.Str.search_forward re out 0);
    match (Re.Str.matched_group 1 out) with
    | "resourceout" -> Resourceout
    | _ -> Other
  with Not_found ->
    Other
 *)

type prover_result_parser = {
  prp_regexps     : (string * prover_answer) list;
  prp_timeregexps : timeregexp list;
  prp_stepregexps : stepregexp list;
  prp_exitcodes   : (int * prover_answer) list;
  prp_model_parser : model_parser;
}

let print_prover_answer fmt = function
  | Valid -> pp_print_string fmt "Valid"
  | Invalid -> pp_print_string fmt "Invalid"
  | Timeout -> pp_print_string fmt "Timeout"
  | OutOfMemory -> fprintf fmt "Out@ of@ memory"
  | StepLimitExceeded -> fprintf fmt "Step@ limit@ exceeded"
  | Unknown s -> fprintf fmt "Unknown@ (%s)" s
  | Failure s -> fprintf fmt "Failure@ (%s)" s
  | HighFailure s -> fprintf fmt "High failure (%s)" s

let print_prover_status fmt = function
  | Unix.WSTOPPED n -> fprintf fmt "stopped by signal %d" n
  | Unix.WSIGNALED n -> fprintf fmt "killed by signal %d" n
  | Unix.WEXITED n -> fprintf fmt "exited with status %d" n

let print_steps fmt s =
  if s >= 0 then fprintf fmt ", %d steps" s

let read_and_delete_file fn =
  let cin = open_in fn in
  let out = Sysutil.channel_contents cin in
  close_in cin;
  if Debug.test_noflag debug then Sys.remove fn;
  out

let json_prover_result r =
  let open Json_base in
  let convert_model (a, m) =
    if not (is_model_empty m) then
      Record [
          "model", json_model m;
          "answer", String (asprintf "%a" print_prover_answer a)
        ]
    else Null in
  Record [
      "answer", String (asprintf "%a" print_prover_answer r.pr_answer);
      "time", Float r.pr_time;
      "step", Int r.pr_steps;
      "ce-models", List (List.map convert_model r.pr_models);
      "status", String (asprintf "%a" print_prover_status r.pr_status)
    ]

let print_prover_result ?(json=false) fmt r =
  if json then
    Json_base.print_json fmt (json_prover_result r)
  else
    let color = match r.pr_answer with | Valid -> "green" | Invalid -> "red" | _ -> "cyan" in
    fprintf fmt "@{<bold %s>%a@}@ (%.2fs%a)"
      color print_prover_answer r.pr_answer r.pr_time print_steps r.pr_steps;
    match r.pr_answer with
    | HighFailure s ->
      fprintf fmt "HighFailure (%s),@\nProver@ exit@ status:@ %a@\nprover@ output:@\n%s@\n"
        s print_prover_status r.pr_status r.pr_output
    | _ -> ()

let rec grep out l = match l with
  | [] -> HighFailure "no match found from given regexps"
  | (re,pa) :: l ->
      begin try
        ignore (Re.Str.search_forward re out 0);
        match pa with
        | Valid | Invalid | Timeout | OutOfMemory | StepLimitExceeded -> pa
        | Unknown s -> Unknown (Re.Str.replace_matched s out)
        | Failure s -> Failure (Re.Str.replace_matched s out)
        | HighFailure _ -> assert false
      with Not_found -> grep out l end

(* Create a regexp matching the same as the union of all regexp of the list. *)
let craft_efficient_re l =
  let s = Format.asprintf "%a"
    (Pp.print_list_delim
       ~start:(fun fmt () -> Format.pp_print_string fmt "\\(")
       ~stop:(fun fmt () -> Format.pp_print_string fmt "\\)")
       ~sep:(fun fmt () -> Format.pp_print_string fmt "\\|")
       (fun fmt (a, _b) -> Format.pp_print_string fmt a)) l
  in
  Re.Str.regexp s

let debug_print_model ~print_attrs model =
  Debug.dprintf debug "Call_provers: %a@." (print_model ~print_attrs) model

type answer_or_model = Answer of prover_answer | Model of string

let analyse_result exit_result res_parser get_model out =
  let list_re = res_parser.prp_regexps in
  let re = craft_efficient_re list_re in
  let list_re = List.map (fun (a, b) -> Re.Str.regexp a, b) list_re in
  let result_list = Re.Str.full_split re out in
  let result_list =
    List.fold_right
      (fun s acc ->
        match s with
        | Re.Str.Delim r -> Answer (grep r list_re) :: acc
        | Re.Str.Text "\n" -> acc
        | Re.Str.Text t -> Model t :: acc)
      result_list
      exit_result
  in

  let merge_answers ans1 opt_ans2 =
    match opt_ans2 with
    | None -> ans1
    | Some ans2 ->
        match ans1 with
        (* prefer any answer over HighFailure *)
        | HighFailure _ -> ans2
        | _ -> ans1
  in

  let rec analyse saved_models saved_res l =
    match l with
    | [] ->
        Option.value ~default:(HighFailure "default answer") saved_res, List.rev saved_models
    | Answer Valid :: _ ->
        (* answer Valid is always a priority *)
        Valid, []
    | Answer res :: (Answer (HighFailure s) :: []) ->
        Debug.dprintf debug_analyse_result
          "@[[Call_provers.analyse_result] answer followed by HighFailure (%s):@ @[%a@]@]@." s
          print_prover_answer res;
        (* FIXME (see https://gitlab.inria.fr/why3/why3/-/issues/648)
        This case is a specific treatment for cases when Answer HighFailure
        is appended at the end of result_list because signaled is true in the function
        parse_prover_run.
        Without this hack, if a regexp matches exactly the last line of the prover output
        and if Answer HighFailure has been appended at the end, we might end up with two
        consecutive answers in result_list that are ignored by the more general case
        Answer res1 :: (Answer res2 :: tl as tl1). *)
        merge_answers res saved_res, List.rev saved_models
    | Answer res1 :: (Answer res2 :: tl as tl1) ->
        Debug.dprintf debug_analyse_result
          "@[[Call_provers.analyse_result] two consecutive answers:@ @[%a@] and @[%a@]@]@."
          print_prover_answer res1 print_prover_answer res2;
        (* two consecutive answers may happen when one ask for (reason-unknown) *)
       begin
         match res1,res2 with
         | StepLimitExceeded, Unknown "resourceout"
         | Unknown _, Unknown "resourceout" ->
             (* "resourceout" here is a reason given *)
            analyse saved_models saved_res (Answer StepLimitExceeded :: tl)
         | Timeout, Unknown "timeout"
         | Unknown _, Unknown "timeout" ->
             (* "timeout" here is a reason given *)
            analyse saved_models saved_res (Answer Timeout :: tl)
         | (Unknown _, Unknown "")| (_, Unknown "(not unknown!)") ->
             (* "(not unknown!)" is a reason given when previous answer was not unknown *)
            analyse saved_models saved_res (Answer res1 :: tl)
         | Unknown "", Unknown _ ->
            analyse saved_models saved_res tl1
         | Unknown s1, Unknown s2 ->
            analyse saved_models saved_res (Answer (Unknown (s1 ^ " + " ^ s2)) :: tl)
         | _,_ -> (
            Loc.warning
              (Loc.register_warning "consecutive_answers" "Warn when one of two consecutive prover answers is ignored.@.")
              "two consecutive answers returned by the prover, will ignore the first one.@.\
              First answer: %a@.Second answer: %a@."
              print_prover_answer res1 print_prover_answer res2;
            analyse saved_models saved_res tl1)
       end
    | Answer res :: Model model_str :: tl ->
        Debug.dprintf debug_analyse_result
          "@[[Call_provers.analyse_result] answer followed by model:@ @[%a@]@]@."
          print_prover_answer res;
        assert (res <> Valid);
        record_model saved_models saved_res res model_str tl
    | Answer res :: tl ->
        Debug.dprintf debug_analyse_result
          "@[[Call_provers.analyse_result] answer not followed by model:@ @[%a@]@]@."
          print_prover_answer res;
        assert (res <> Valid);
        analyse saved_models (Some (merge_answers res saved_res)) tl
    | Model model_str :: tl ->
        Debug.dprintf debug_analyse_result
          "@[[Call_provers.analyse_result] model NOT PRECEDED by answer!@]@.";
        (* this is not supposed to happen, but it happens. Possibly because the driver is missing
           a regexp for a possible answer. Let us assume the answer is equivalent to unknown
        *)
        record_model saved_models saved_res (HighFailure "unrecognized prover answer") model_str tl
  and record_model saved_models saved_res res model_str tl =
    match get_model with
    | Some printing_info ->
        let m = res_parser.prp_model_parser printing_info model_str in
        Debug.dprintf debug "Call_provers: model:@.";
        debug_print_model ~print_attrs:false m;
        analyse ((res, m) :: saved_models) (Some res) tl
    | None ->
        analyse saved_models (Some (merge_answers res saved_res)) tl
  in
  analyse [] None result_list

let backup_file f = f ^ ".save"

let parse_prover_run res_parser signaled time out exitcode limit get_model =
  Debug.dprintf debug "Call_provers: exited with status %Ld@." exitcode;
  (* the following conversion is incorrect (but does not fail) on 32bit, but if
     the incoming exitcode was really outside the bounds of [int], its exact
     value is meaningless for Why3 anyway (e.g. some windows status codes). If
     it becomes meaningful, we might want to change the conversion here *)
  let int_exitcode = Int64.to_int exitcode in
  let ans, models =
    let exit_result =
      if signaled then [Answer (HighFailure "signaled")] else
      try [Answer (List.assoc int_exitcode res_parser.prp_exitcodes)]
      with Not_found -> []
    in analyse_result exit_result res_parser get_model out
  in
  Debug.dprintf debug "Call_provers: prover output:@\n%s@." out;
  let time = Option.value ~default:(time) (grep_time out res_parser.prp_timeregexps) in
  let steps = Option.value ~default:(-1) (grep_steps out res_parser.prp_stepregexps) in
  let tlimit = limit.limit_time in
  let stepslimit = limit.limit_steps in
  let ans, time, steps =
    (* HighFailure or Unknown when steps >= stepslimit are assumed to be StepLimitExceeded *)
    if stepslimit > 0 && steps >= stepslimit then
      match ans with
      | HighFailure _ | Unknown _ | StepLimitExceeded ->
          Debug.dprintf debug
            "[Call_provers.parse_prover_run] answer after %d steps >= stepslimit -> StepLimitExceeded@." steps;
          StepLimitExceeded, time, steps
      | _ -> ans, time, steps
    else
      (* HighFailure or Unknown close to time limit are assumed to be timeouts *)
    if tlimit > 0.0 && time >= 0.9 *. tlimit -. 0.1 then
      match ans with
      | HighFailure _ | Unknown _ | Timeout ->
          Debug.dprintf debug
            "[Call_provers.parse_prover_run] answer after %f >= 0.9 * timelimit - 0.1 -> Timeout@." time;
          Timeout, tlimit, steps
      | _ -> ans, time, steps
    else
      ans, time, steps
  in
  (* We avoid times smaller than 1/1000000s*)
  let time = max 0.000001 time in
  { pr_answer = ans;
    pr_status = if signaled then Unix.WSIGNALED int_exitcode else Unix.WEXITED int_exitcode;
    pr_output = out;
    pr_time   = time;
    pr_steps  = steps;
    pr_models = models;
  }

let parse_prover_run res_parser signaled time outfile exitcode limit get_model =
  if outfile = "" then
    { pr_answer = Unknown "empty prover answer";
      pr_status = Unix.WEXITED 1;
      pr_output = "";
      pr_time = time;
      pr_steps = 0;
      pr_models = [] }
  else
    let out = read_and_delete_file outfile in
    parse_prover_run res_parser signaled time out exitcode limit get_model

let actualcommand ~config command limit file =
  let stime = string_of_int (Float.to_int (Float.ceil limit.limit_time)) in
  let stimef = string_of_float limit.limit_time in
  let stimems = string_of_int (Float.to_int (limit.limit_time *. 1000.)) in
  let smem = string_of_int limit.limit_mem in
  let arglist = Cmdline.cmdline_split command in
  let use_stdin = ref true in
  let on_timelimit = ref false in
  let cmd_regexp = Re.Str.regexp "%\\([.]?.\\)" in
  let replace s = match Re.Str.matched_group 1 s with
    | "%" -> "%"
    | "f" -> use_stdin := false; file
    | "t" -> on_timelimit := true; stime
    | ".t" -> on_timelimit := true; stimef
    | "T" -> on_timelimit := true; stimems
    | "m" -> smem
    | "l" -> Whyconf.libdir config
    | "d" -> Whyconf.datadir config
    | "S" -> string_of_int limit.limit_steps
    | _ -> failwith "unknown specifier, use %%, %f, %t, %.t, %T, %m, %l, %d or %S"
  in
  let args =
    List.map (Re.Str.global_substitute cmd_regexp replace) arglist
  in
  args, !use_stdin, !on_timelimit

let actualcommand ~cleanup ~inplace ~config command limit file =
  try
    let (cmd, _,_) as x =
      actualcommand ~config command limit file
    in
    Debug.dprintf debug "@[<hv 2>Call_provers: actual command is:@ @[%a@]@]@."
                  (Pp.print_list Pp.space pp_print_string) cmd;
    x
  with e ->
    Debug.dprintf
      debug
      "@[<hv 2>Call_provers: failed to build an actual corresponding to@ %s@]@."
      command;
    if cleanup then Sys.remove file;
    if inplace then Sys.rename (backup_file file) file;
    raise e

let adapt_limits limit on_timelimit =
  if limit.limit_time = empty_limits.limit_time then limit
  else
    { limit with limit_time =
      (* for steps limit use 2 * t + 1 time *)
      if limit.limit_steps <> empty_limits.limit_steps
      then (2. *. limit.limit_time +. 1.)
      (* if prover implements time limit, use 4t + 1 *)
      else if on_timelimit then 4. *. limit.limit_time +. 1.
      (* otherwise use t *)
      else limit.limit_time }

type server_id = int

let gen_id =
  let x = ref 0 in
  fun () ->
    incr x;
    !x

type save_data = {
  vc_file         : string;
  inplace         : bool;
  limits          : resource_limits;
  res_parser      : prover_result_parser;
  get_model       : Printer.printing_info option;
}

let saved_data : (int, save_data) Hashtbl.t = Hashtbl.create 17

open Prove_client

let handle_answer answer =
  match answer with
  | Finished { id; time; timeout; out_file; exit_code } ->
      let save = Hashtbl.find saved_data id in
      Hashtbl.remove saved_data id;
      let keep_vcs =
        try let flag = Debug.lookup_flag "keep_vcs" in Debug.test_flag flag with
        | _ -> false
      in
      if Debug.test_noflag debug && not keep_vcs then begin
        Sys.remove save.vc_file;
        if save.inplace then Sys.rename (backup_file save.vc_file) save.vc_file
      end;
      let ans = parse_prover_run save.res_parser timeout time out_file exit_code
          save.limits save.get_model in
      id, Some ans
  | Started id ->
      id, None

let wait_for_server_result ~blocking =
  List.map handle_answer (read_answers ~blocking)

type prover_call =
  | ServerCall of server_id
  | EditorCall of int

let call_on_file
      ~config ~command ~limits ~res_parser ~get_model ?(inplace=false) fin =
  let id = gen_id () in
  let cmd, use_stdin, on_timelimit =
    actualcommand ~cleanup:true ~inplace ~config command limits fin in
  let save = {
    vc_file         = fin;
    inplace         = inplace;
    limits          = limits;
    res_parser      = res_parser;
    get_model       = get_model;
  } in
  Hashtbl.add saved_data id save;
  let limits = adapt_limits limits on_timelimit in
  let use_stdin = if use_stdin then Some fin else None in
  Debug.dprintf
    debug
    "Request sent to prove_client:@ timelimit=%.2f@ memlimit=%d@ cmd=@[[%a]@]@."
    limits.limit_time limits.limit_mem
    (Pp.print_list Pp.comma Pp.string) cmd;
  let libdir = Whyconf.libdir config in
  send_request ~libdir ~use_stdin ~id
                            ~timelimit:limits.limit_time
                            ~memlimit:limits.limit_mem
                            ~cmd;
  ServerCall id

type prover_update =
  | NoUpdates
  | ProverInterrupted
  | InternalFailure of exn
  | ProverStarted
  | ProverFinished of prover_result

let result_buffer : (server_id, prover_update) Hashtbl.t = Hashtbl.create 17

let fetch_new_results ~blocking = (* TODO: handle ProverStarted events *)
  List.iter (fun (id, r) ->
    let x = match r with
    | Some r -> ProverFinished r
    | None -> ProverStarted in
    Hashtbl.add result_buffer id x)
    (wait_for_server_result ~blocking)

let get_new_results ~blocking =
  fetch_new_results ~blocking;
  let q = ref [] in
  Hashtbl.iter (fun key element ->
    if element = ProverStarted && blocking then
      ()
    else
      q := (ServerCall key, element) :: !q) result_buffer;
  Hashtbl.clear result_buffer;
  !q

let query_result_buffer id =
  try let r = Hashtbl.find result_buffer id in
      Hashtbl.remove result_buffer id; r
  with Not_found -> NoUpdates

let editor_result ret = {
  pr_answer = Unknown "not yet edited";
  pr_status = ret;
  pr_output = "";
  pr_time   = 0.0;
  pr_steps  = 0;
  pr_models = [];
}

let query_call = function
  | ServerCall id ->
      fetch_new_results ~blocking:false;
      query_result_buffer id
  | EditorCall pid ->
      let pid, ret = Unix.waitpid [Unix.WNOHANG] pid in
      if pid = 0 then NoUpdates else
      ProverFinished (editor_result ret)

let interrupt_call ~config = function
  | ServerCall id ->
     let libdir = Whyconf.libdir config in
     Prove_client.send_interrupt ~id ~libdir
  | EditorCall pid ->
     (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ())

let rec wait_on_call = function
  | ServerCall id as pc ->
      begin match query_result_buffer id with
        | ProverFinished r -> r
        | _ ->
            fetch_new_results ~blocking:true;
            wait_on_call pc
      end
  | EditorCall pid ->
      let _, ret = Unix.waitpid [] pid in
      editor_result ret

let call_on_buffer ~command ~config ~limits ~res_parser ~filename ~get_model
    ~gen_new_file ?(inplace=false) buffer =
  let fin,cin =
    if gen_new_file then
      Filename.open_temp_file "why_" ("_" ^ filename)
    else
      begin
        let filename = Sysutil.concat (Sys.getcwd ()) filename in
        if inplace then
          Sys.rename filename (backup_file filename);
        filename, open_out filename
      end
  in
  Buffer.output_buffer cin buffer; close_out cin;
  call_on_file ~command ~config ~limits ~res_parser ~get_model ~inplace fin

let call_editor ~config ~command fin =
  let command, use_stdin, _ =
    actualcommand
      ~cleanup:false ~inplace:false ~config command empty_limits fin
  in
  let exec = List.hd command in
  let argarray = Array.of_list command in
  let fd_in =
    if use_stdin then Unix.openfile fin [Unix.O_RDONLY] 0 else Unix.stdin in
  let pid = Unix.create_process exec argarray fd_in Unix.stdout Unix.stderr in
  if use_stdin then Unix.close fd_in;
  EditorCall pid
