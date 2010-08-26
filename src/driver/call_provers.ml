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
  | [] ->
      HighFailure
  | (re,pa) :: l ->
      begin try
        ignore (Str.search_forward re out 0);
        match pa with
        | Valid | Invalid | Timeout -> pa
        | Unknown s -> Unknown (Str.replace_matched s out)
        | Failure s -> Failure (Str.replace_matched s out)
        | HighFailure -> assert false
      with Not_found -> grep out l end

let call_prover debug command opt_cout buffer =
  let time = Unix.gettimeofday () in
  let (cin,_) as p = match opt_cout with
    | Some cout ->
        Buffer.output_buffer cout buffer; close_out cout;
        Unix.open_process command
    | None ->
        let (_,cout) as p = Unix.open_process command in
        Buffer.output_buffer cout buffer; close_out cout;
        p
  in
  let out = channel_contents cin in
  let ret = Unix.close_process p in
  let time = Unix.gettimeofday () -. time in
  if debug then eprintf "Call_provers: prover output:@\n%s@." out;
  ret, out, time

let debug = Debug.register_flag "call_prover"

let call_on_buffer ~command ?(timelimit=0) ?(memlimit=0)
                   ~regexps ~exitcodes ~filename buffer () =
  let debug = Debug.test_flag debug in
  let on_stdin = ref true in
  let on_timelimit = ref false in
  let cmd_regexp = Str.regexp "%\\(.\\)" in
  let replace file s = match Str.matched_group 1 s with
    | "%" -> "%"
    | "f" -> on_stdin := false; file
    | "t" -> on_timelimit := true; string_of_int timelimit
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
    | HighFailure when !on_timelimit && timelimit > 0
      && time >= (0.9 *. float timelimit) -> Timeout
    | _ -> ans
  in
  { pr_answer = ans;
    pr_output = out;
    pr_time   = time }

