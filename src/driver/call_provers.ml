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
open Sysutil

type prover_answer =
  | Valid
  | Invalid
  | Timeout
  | Unknown of string
  | Failure of string
  | HighFailure

type prover_result = {
  pr_answer : prover_answer;
  pr_output : string;
  pr_time   : float;
}

let print_prover_answer fmt = function
  | Valid -> fprintf fmt "Valid"
  | Invalid -> fprintf fmt "Invalid"
  | Timeout -> fprintf fmt "Timeout"
  | Unknown s -> fprintf fmt "Unknown: %s" s
  | Failure s -> fprintf fmt "Failure: %s" s
  | HighFailure -> fprintf fmt "HighFailure"

let print_prover_result fmt {pr_answer=ans; pr_output=out; pr_time=t} =
  fprintf fmt "%a (%.2fs)" print_prover_answer ans t;
  if ans == HighFailure then fprintf fmt "@\nProver output:@\n%s@." out

let rec grep out l = match l with
  | [] -> HighFailure
  | (re,pa)::l ->
      begin try
        ignore (Str.search_forward re out 0);
        match pa with
        | Valid | Invalid | Timeout -> pa
        | Unknown s -> Unknown (Str.replace_matched s out)
        | Failure s -> Failure (Str.replace_matched s out)
        | HighFailure -> assert false
      with Not_found -> grep out l end

let call_prover debug command opt_cout buffer =
  let time = Unix.time () in
  let (cin,cout) as p = Unix.open_process command in
  let cout = match opt_cout with Some c -> c | _ -> cout in
  Buffer.output_buffer cout buffer; close_out cout;
  let out = channel_contents cin in
  let ret = Unix.close_process p in
  let time = Unix.time () -. time in
  if debug then eprintf "Call_provers: prover output:@\n%s@." out;
  ret, out, time

let call_on_buffer ?(debug=false) ~command ~timelimit ~memlimit
                                  ~regexps ~exitcodes ~filename buffer () =
  let on_stdin = ref false in
  let cmd_regexp = Str.regexp "%\\(.\\)" in
  let replace file s = match Str.matched_group 1 s with
    | "%" -> "%"
    | "f" -> on_stdin := false; file
    | "t" -> string_of_int timelimit
    | "m" -> string_of_int memlimit
    | _ -> failwith "unknown format specifier, use %%f, %%t or %%m"
  in
  let cmd = Str.global_substitute cmd_regexp (replace "") command in
  let ret, out, time =
    if !on_stdin then call_prover debug cmd None buffer else begin
      let fout,cout = Filename.open_temp_file "why_" ("_" ^ filename) in
      try
        let cmd = Str.global_substitute cmd_regexp (replace fout) command in
        let res = call_prover debug cmd (Some cout) buffer in
        if not debug then Sys.remove fout;
        res
      with e ->
        close_out cout;
        if not debug then Sys.remove fout;
        raise e
    end
  in
  let ans = match ret with
    | Unix.WSTOPPED n ->
        if debug then eprintf "Call_provers: stopped by signal %d@." n;
        HighFailure
    | Unix.WSIGNALED n ->
        if debug then eprintf "Call_provers: killed by signal %d@." n;
        HighFailure
    | Unix.WEXITED n ->
        if debug then eprintf "Call_provers: exited with status %d@." n;
        (try List.assoc n exitcodes with Not_found -> grep out regexps)
  in
  let ans = match ans with
    | HighFailure 
      when timelimit > 0 && time >= (0.9 *. float timelimit) -> Timeout
    | _ -> ans
  in
  { pr_answer = ans;
    pr_output = out;
    pr_time   = time }

(*
let is_true_cygwin = Sys.os_type = "Cygwin"

(* this should be replaced by a proper use of fork/waitpid() *)
let dirname = Filename.dirname Sys.argv.(0)
let cpulimit_local = Filename.concat dirname "why-cpulimit"
let cpulimit_commands = ["why-cpulimit"; cpulimit_local ; "timeout"]
let cpulimit = (
  let tmp = ref "" in
  try
    List.iter
      (fun s ->
         (*let r = Sys.command (s^" 1 echo") in
         if r=0 then (tmp:=s; raise Exit)*)
         let pid = Unix.create_process s [|s;"1";"true"|]
           Unix.stdin Unix.stdout Unix.stderr in
         match Unix.waitpid [] pid with
           | _,Unix.WEXITED 0 -> (tmp:=s; raise Exit)
           | _ -> ()
      )
    cpulimit_commands;
    failwith ("need shell command among: "^
                (String.concat " ," cpulimit_commands))
  with Exit -> tmp)



(* Utils *)

let remove_file ?(debug=false) f =
  if not debug then try Sys.remove f with _ -> ()

(*let environment = Unix.environment ()*)

let () = Sys.set_signal Sys.sigpipe Sys.Signal_ignore

let timed_sys_command ?formatter ?buffer ?(debug=false) ?timeout cmd =
  let t0 = Unix.times () in
  let cmd = match timeout with
    | None -> sprintf "%s 2>&1" cmd
    | Some timeout -> sprintf "%s %d %s 2>&1" !cpulimit timeout cmd in
  if debug then eprintf "command line: %s@." cmd;
  let (cin,cout) as p = Unix.open_process cmd in
  (* Write the formatter to the stdin of the prover *)
  begin try
    (match formatter with
       | None -> ()
       | Some formatter ->
           let fmt = formatter_of_out_channel cout in
           formatter fmt);
  with Sys_error s ->
    if debug then eprintf "Sys_error : %s@." s
  end;
  (* Write the buffer to the stdin of the prover *)
  begin try
    (match buffer with
       | None -> ()
       | Some buffer ->
           Buffer.output_buffer cout buffer);
  with Sys_error s ->
    if debug then eprintf "Sys_error : %s@." s
  end;
  close_out cout;
  let out = Sysutil.channel_contents cin in
  let ret = Unix.close_process p in
  let t1 = Unix.times () in
  let cpu_time = t1.Unix.tms_cutime -. t0.Unix.tms_cutime in
  if debug then eprintf "Call_provers : Command output : %s@." out;
  (cpu_time,ret,out)

let grep re str =
  try
    let _ = Str.search_forward re str 0 in true
  with Not_found -> false

  (*   match buffers,p.DpConfig.stdin_switch,filename with *)
  (*     | None,_, Some f -> *)
  (*         let cmd = sprintf "%s %s %s %s"  *)
  (*           p.DpConfig.command p.DpConfig.command_switches switch f  *)
  (*         in *)
  (*         cmd,timed_sys_command ~debug timeout cmd *)
  (*     | Some buffers, Some stdin_s, _ -> *)
  (*         let cmd = sprintf "%s %s %s %s"  *)
  (*           p.DpConfig.command p.DpConfig.command_switches switch stdin_s *)
  (*         in *)
  (*         cmd,timed_sys_command ~stdin:buffers ~debug timeout cmd *)
  (*     | Some buffers, None, Some f -> *)
  (*         let f = Filename.temp_file "" f in *)
  (*         let cout = open_out f in *)
  (*         List.iter (Buffer.output_buffer cout) buffers; *)
  (*         close_out cout; *)
  (*         let cmd = sprintf "%s %s %s %s"  *)
  (*           p.DpConfig.command p.DpConfig.command_switches switch f *)
  (*         in *)
  (*         cmd,timed_sys_command ~debug timeout cmd *)
  (*     | _ -> invalid_arg  *)
  (*         "Calldp.gen_prover_call : filename must be given if the prover
             can't use stdin."  *)
  (* in *)


let treat_result pr (t,c,outerr) =
  let answer =
    match c with
      | Unix.WSTOPPED 24 | Unix.WSIGNALED 24 | Unix.WEXITED 124
      | Unix.WEXITED 152 ->
          (* (*128 +*) SIGXCPU signal (i.e. 24, /usr/include/bits/signum.h) *)
          (* TODO : if somebody use why_cpulimit to call "why -timeout
             0", Why will think that he called why_cpulimit (WEXITED
             152) and will return Timeout instead of exit 152. In fact
             in this case Why will receive a SIGXCPU in less than 1
             sec (soft limit) (ie man setrlimit ). The problem can be
             here or in the use of why_cpulimit *)
          Timeout
      | Unix.WSTOPPED _ | Unix.WSIGNALED _ -> HighFailure
      | Unix.WEXITED _ ->
          let rec greps res = function
            | [] -> HighFailure
            | (r,pa)::l ->
                if grep r res
                then match pa with
                  | Valid | Invalid -> pa
                  | Unknown s -> Unknown (Str.replace_matched s res)
                  | Failure s -> Failure (Str.replace_matched s res)
                  | Timeout | HighFailure -> assert false
                else greps outerr l in
          greps outerr pr.pr_regexps in
  { pr_time = t;
    pr_answer = answer;
    pr_stderr = ""; (*Fill it with something real*)
    pr_stdout = outerr} (* Split it in two...*)
  (* *)


let check_prover prover =
  if prover.pr_call_file = None && prover.pr_call_stdin = None then
    raise NoCommandlineProvided

let regexp_call_file = Str.regexp "%\\([a-z]\\)"

let rec on_file ?debug ?timeout pr filename =
  check_prover pr;
  match pr.pr_call_file with
    | Some cmd ->
        let filename = if is_true_cygwin
        then
          let cin = Unix.open_process_in
            (sprintf "cygpath -am \"%s\"" filename) in
          let f = input_line cin in
          close_in cin; f
        else filename in
        let cmd =
          let repl_fun s =
            match Str.matched_group 1 s with
              | "s" -> filename
              | _ -> assert false in (*TODO mettre une belle exception*)
          Str.global_substitute regexp_call_file repl_fun cmd in
        let res = timed_sys_command ?debug ?timeout cmd in
        treat_result pr res
    | None ->
        let formatter = Sysutil.file_contents_fmt filename in
        on_formatter ?timeout ?debug pr formatter

and on_formatter ?debug ?timeout ?filename pr formatter =
  check_prover pr;
  match pr.pr_call_stdin with
    | Some cmd ->
        let res = timed_sys_command ?debug ?timeout ~formatter cmd in
        treat_result pr res
    | None ->
        match filename with
          | None -> raise NoCommandlineProvided
          | Some filename -> Sysutil.open_temp_file ?debug filename
              (fun file cout ->
                 let fmt = formatter_of_out_channel cout in
                 formatter fmt;
                 pp_print_flush fmt ();
                 on_file ?timeout ?debug pr file)


let on_buffer ?debug ?timeout ?filename pr buffer =
  check_prover pr;
  match pr.pr_call_stdin with
    | Some cmd ->
        let res = timed_sys_command ?debug ?timeout ~buffer cmd in
        treat_result pr res
    | None ->
        match filename with
          | None -> raise NoCommandlineProvided
          | Some filename -> Sysutil.open_temp_file ?debug filename
              (fun file cout ->
                 Buffer.output_buffer cout buffer;
                 on_file ?timeout ?debug pr file)
*)
