(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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
  | OutOfMemory
  | Unknown of string
  | Failure of string
  | HighFailure

type prover_result = {
  pr_answer : prover_answer;
  pr_status : Unix.process_status;
  pr_output : string;
  pr_time   : float;
}

let print_prover_answer fmt = function
  | Valid -> fprintf fmt "Valid"
  | Invalid -> fprintf fmt "Invalid"
  | Timeout -> fprintf fmt "Timeout"
  | OutOfMemory -> fprintf fmt "Ouf Of Memory"
  | Unknown "" -> fprintf fmt "Unknown"
  | Failure "" -> fprintf fmt "Failure"
  | Unknown s -> fprintf fmt "Unknown: %s" s
  | Failure s -> fprintf fmt "Failure: %s" s
  | HighFailure -> fprintf fmt "HighFailure"

let print_prover_status fmt = function
  | Unix.WSTOPPED n -> fprintf fmt "stopped by signal %d" n
  | Unix.WSIGNALED n -> fprintf fmt "killed by signal %d" n
  | Unix.WEXITED n -> fprintf fmt "exited with status %d" n

let print_prover_result fmt
  {pr_answer=ans; pr_status=status; pr_output=out; pr_time=t} =
  fprintf fmt "%a (%.2fs)" print_prover_answer ans t;
  if ans == HighFailure then
    fprintf fmt "@\nProver exit status: %a@\nProver output:@\n%s@."
      print_prover_status status out

let rec grep out l = match l with
  | [] ->
      HighFailure
  | (re,pa) :: l ->
      begin try
        ignore (Str.search_forward re out 0);
        match pa with
        | Valid | Invalid | Timeout | OutOfMemory -> pa
        | Unknown s -> Unknown (Str.replace_matched s out)
        | Failure s -> Failure (Str.replace_matched s out)
        | HighFailure -> assert false
      with Not_found -> grep out l end


let debug = Debug.register_flag "call_prover"

type post_prover_call = unit -> prover_result
type prover_call = Unix.wait_flag list -> post_prover_call
type pre_prover_call = unit -> prover_call

let call_on_file ~command ?(timelimit=0) ?(memlimit=0)
                 ~regexps ~timeregexps ~exitcodes
                 ?(cleanup=false) fin =

  let arglist = Cmdline.cmdline_split command in
  let command = List.hd arglist in
  let on_timelimit = ref false in
  let cmd_regexp = Str.regexp "%\\(.\\)" in
  let replace s = match Str.matched_group 1 s with
    | "%" -> "%"
    | "f" -> fin
    | "t" -> on_timelimit := true; string_of_int timelimit
    | "T" -> string_of_int (16 * succ timelimit)
    | "m" -> string_of_int memlimit
    (* FIXME: libdir and datadir can be changed in the configuration file
       Should we pass them as additional arguments? Or would it be better
       to prepare the command line in a separate function? *)
    | "l" -> Relocatable.libdir
    | "d" -> Relocatable.datadir
    | _ -> failwith "unknown specifier, use %%f, %%t, %%m, %%l, or %%d"
  in
  let subst s =
    try Str.global_substitute cmd_regexp replace s
    with e -> if cleanup then Sys.remove fin; raise e
  in
  let argarray = Array.of_list (List.map subst arglist) in

  fun () ->
    let fd_in = Unix.openfile fin [Unix.O_RDONLY] 0 in
    let fout,cout = Filename.open_temp_file (Filename.basename fin) ".out" in
    let fd_out = Unix.descr_of_out_channel cout in
    let time = Unix.gettimeofday () in
    let pid = Unix.create_process command argarray fd_in fd_out fd_out in
    Unix.close fd_in;
    close_out cout;

    fun wait_flags ->
      (* TODO? check that we haven't given the result earlier *)
      let res,ret = Unix.waitpid wait_flags pid in
      if res = 0 then raise Exit;
      let time = Unix.gettimeofday () -. time in
      let cout = open_in fout in
      let out = Sysutil.channel_contents cout in
      close_in cout;

      fun () ->
        if Debug.nottest_flag debug then begin
          if cleanup then Sysutil.safe_remove fin;
          Sysutil.safe_remove fout;
        end;
        let ans = match ret with
          | Unix.WSTOPPED n ->
              Debug.dprintf debug "Call_provers: stopped by signal %d@." n;
              grep out regexps
          | Unix.WSIGNALED n ->
              Debug.dprintf debug "Call_provers: killed by signal %d@." n;
              grep out regexps
          | Unix.WEXITED n ->
              Debug.dprintf debug "Call_provers: exited with status %d@." n;
              (try List.assoc n exitcodes with Not_found -> grep out regexps)
        in
        Debug.dprintf debug "Call_provers: prover output:@\n%s@." out;
        let time = Util.def_option time (grep_time out timeregexps) in
        let ans = match ans with
          | HighFailure when !on_timelimit && timelimit > 0
            && time >= (0.9 *. float timelimit) -> Timeout
          | _ -> ans
        in
        { pr_answer = ans;
          pr_status = ret;
          pr_output = out;
          pr_time   = time }

let call_on_buffer ~command ?(timelimit=0) ?(memlimit=0)
                   ~regexps ~timeregexps ~exitcodes ~filename buffer =

  let fin,cin = Filename.open_temp_file "why_" ("_" ^ filename) in
  Buffer.output_buffer cin buffer; close_out cin;
  call_on_file ~command ~timelimit ~memlimit
               ~regexps ~timeregexps ~exitcodes ~cleanup:true fin

let query_call call = try Some (call [Unix.WNOHANG]) with Exit -> None

let wait_on_call call = call []

