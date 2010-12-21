(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

(** time regexp "%h:%m:%s" *)
type timeunit =
  | Hour
  | Min
  | Sec
  | Msec

type timeregexp = {
  re    : Str.regexp;
  group : timeunit array; (* i-th corresponds to the group i+1 *)
}

let timeregexp s =
  let cmd_regexp = Str.regexp "%\\(.\\)" in
  let nb = ref 0 in
  let l = ref [] in
  let add_unit x = l := (!nb,x) :: !l; incr nb; "\\([0-9]+.?[0-9]*\\)" in
  let replace s = match Str.matched_group 1 s with
    | "%" -> "%"
    | "h" -> add_unit Hour
    | "m" -> add_unit Min
    | "s" -> add_unit Sec
    | "i" -> add_unit Msec
    | _ -> failwith "unknown format specifier, use %%h, %%m, %%s, %%i"
  in
  let s = Str.global_substitute cmd_regexp replace s in
  let group = Array.make !nb Hour in
  List.iter (fun (i,u) -> group.(i) <- u) !l;
  { re = Str.regexp s; group = group}

let rec grep_time out = function
  | [] -> None
  | re :: l ->
    begin try
            ignore (Str.search_forward re.re out 0);
            let t = ref 0. in
            Array.iteri (fun i u ->
              let v = float_of_string (Str.matched_group (succ i) out) in
              match u with
                | Hour -> t := !t +. v *. 3600.
                | Min  -> t := !t +. v *. 60.
                | Sec  -> t := !t +. v
                | Msec -> t := !t +. v /. 1000.) re.group;
            Some !t
      with _ -> grep_time out l end

(** *)

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


let debug = Debug.register_flag "call_prover"

let call_prover command opt_cout buffer =
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
  Debug.dprintf debug "Call_provers: prover output:@\n%s@." out;
  ret, out, time

type post_prover_call = unit -> prover_result

type bare_prover_call = unit -> post_prover_call

let call_on_buffer ~command ?(timelimit=0) ?(memlimit=0)
                   ~regexps ~timeregexps ~exitcodes ~filename buffer =
  let on_stdin = ref true in
  let on_timelimit = ref false in
  let cmd_regexp = Str.regexp "%\\(.\\)" in
  let replace file s = match Str.matched_group 1 s with
    | "%" -> "%"
    | "f" -> on_stdin := false; file
    | "t" -> on_timelimit := true; string_of_int timelimit
    | "m" -> string_of_int memlimit
    | "b" -> string_of_int (memlimit * 1024)
    | _ -> failwith "unknown format specifier, use %%f, %%t, %%m or %%b"
  in
  let cmd = Str.global_substitute cmd_regexp (replace "") command in
  let on_stdin = !on_stdin in
  let cmd,fout,cout = if on_stdin then cmd, "", None else
    let fout,cout = Filename.open_temp_file "why_" ("_" ^ filename) in
    let cmd =
      try Str.global_substitute cmd_regexp (replace fout) command
      with e -> close_out cout; Sys.remove fout; raise e
    in
    cmd, fout, Some cout
  in
  fun () ->
    let ret,out,time = call_prover cmd cout buffer in
    fun () ->
      if not on_stdin && Debug.nottest_flag debug then Sys.remove fout;
      let ans = match ret with
        | Unix.WSTOPPED n ->
            Debug.dprintf debug "Call_provers: stopped by signal %d@." n;
            HighFailure
        | Unix.WSIGNALED n ->
            Debug.dprintf debug "Call_provers: killed by signal %d@." n;
            HighFailure
        | Unix.WEXITED n ->
            Debug.dprintf debug "Call_provers: exited with status %d@." n;
            (try List.assoc n exitcodes with Not_found -> grep out regexps)
      in
      let time = Util.default_option time (grep_time out timeregexps) in
      let ans = match ans with
        | HighFailure when !on_timelimit && timelimit > 0
          && time >= (0.9 *. float timelimit) -> Timeout
        | _ -> ans
      in
      { pr_answer = ans;
        pr_output = out;
        pr_time   = time }

