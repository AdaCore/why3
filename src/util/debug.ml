(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

let formatter = ref Format.err_formatter

exception UnknownFlag of string

type flag = { flag_name : string;
              mutable flag_value : bool }

let flag_table = Hashtbl.create 17

let fst3 (flag,_,_) = flag

let gen_register_flag (desc : Pp.formatted) s info =
  try
    fst3 (Hashtbl.find flag_table s)
  with Not_found ->
    let flag = { flag_name = s; flag_value = false } in
    Hashtbl.replace flag_table s (flag,info,desc);
    flag

let register_info_flag ~desc s = gen_register_flag desc s true
let register_flag      ~desc s = gen_register_flag desc s false

let list_flags () =
  Hashtbl.fold (fun s (v,info,desc) acc -> (s,v,info,desc)::acc) flag_table []

let lookup_flag s =
  try fst3 (Hashtbl.find flag_table s) with Not_found -> raise (UnknownFlag s)

let test_flag s = s.flag_value
let test_noflag s = not s.flag_value

let set_flag s = s.flag_value <- true
let unset_flag s = s.flag_value <- false
let toggle_flag s = s.flag_value <- not s.flag_value

let () = Exn_printer.register (fun fmt e -> match e with
  | UnknownFlag s -> Format.fprintf fmt "unknown debug flag '%s'" s
  | _ -> raise e)

let stack_trace = register_info_flag "stack_trace"
  ~desc:"Avoid@ catching@ exceptions@ in@ order@ to@ get@ the@ stack@ trace."

let timestamp = register_info_flag "timestamp"
  ~desc:"Print@ a@ timestamp@ before@ debugging@ messages."

let time_start = Unix.gettimeofday ()

let set_debug_formatter f =
  (* enable the usual behavior of stderr: flush at every new line *)
  let o = Format.pp_get_formatter_out_functions f () in
  Format.pp_set_formatter_out_functions f
    { o with Format.out_newline =
        (fun () -> o.Format.out_newline (); o.Format.out_flush ()) };
  formatter := f

let get_debug_formatter () = !formatter

let () = set_debug_formatter Format.err_formatter

let dprintf flag s =
  if flag.flag_value then
    begin
      if timestamp.flag_value then Format.fprintf !formatter "<%f,%s>"
                                        (Unix.gettimeofday () -. time_start) flag.flag_name
      else Format.fprintf !formatter "<%s>" flag.flag_name;
      Format.fprintf !formatter s
    end
  else Format.ifprintf !formatter s


(*** Command-line arguments ****)

module Args = struct
  open Getopt

  type spec = key * handler * doc

  let desc_debug_list, option_list =
    let opt_list_flags = ref false in
    let desc =
      KLong "list-debug-flags", Hnd0 (fun () -> opt_list_flags := true),
      " list known flags ('*' marks those for --debug-all)" in
    let list () =
      if !opt_list_flags then begin
        let list =
          Hashtbl.fold (fun s (_,info,desc) acc -> (s,info,desc)::acc)
            flag_table [] in
        let print fmt (p,info,desc) =
          Format.fprintf fmt "@[%s%s@\n  @[%a@]@]"
            p (if info then " *" else "")
            Pp.formatted desc
        in
        Format.printf "@[<v>%a@]@."
          (Pp.print_list Pp.newline print)
          (List.sort Stdlib.compare list);
      end;
      !opt_list_flags in
    desc,list

  let opt_list_flags = Queue.create ()

  let add_flag s = Queue.add s opt_list_flags

  let desc_shortcut flag option desc =
    let desc = Printf.sprintf "%s (same as --debug=%s)" desc flag in
    (option, Hnd0 (fun () -> add_flag flag), desc)

  let desc_debug =
    KLong "debug", Hnd1 (AList (',', AString), fun l -> List.iter add_flag l),
    "<flag>,... set some debug flags"

  let opt_debug_all = ref false

  let desc_debug_all =
    KLong "debug-all", Hnd0 (fun () -> opt_debug_all := true),
    " set all debug flags that do not change Why3 behavior"

  let set_flags_selected ?(silent=false) () =
    if !opt_debug_all then
      List.iter (fun (_,f,info,_) -> if info then set_flag f) (list_flags ());
    let check flag =
      match lookup_flag flag with
      | f -> set_flag f
      | exception UnknownFlag _ when silent -> () in
    Queue.iter check opt_list_flags;
    if test_flag stack_trace then Printexc.record_backtrace true
end

(** Stats *)
let stats = register_info_flag "stats"
  ~desc:"Compute and print statistics."

type 'a stat = {
  mutable value:'a;
  printer: Format.formatter -> 'a -> unit;
  name   : string;
}

module Stats = struct

let timing_map = Hashtbl.create 42

let get_timings () = timing_map

let add_timing name time =
  let old_t, old_n =
    try Hashtbl.find timing_map name
    with Not_found -> 0.0, 0 in
  Hashtbl.replace timing_map name (old_t +. time, old_n + 1)

let record_timing name f =
  if test_flag stats then
    let begin_time = Unix.gettimeofday () in
    Fun.protect f
      ~finally:(fun () -> add_timing name (Unix.gettimeofday () -. begin_time))
  else f ()

  let registered_stats :  (Format.formatter -> unit) list ref = ref []

  let print fmt =
    List.iter (fun s -> Format.fprintf fmt "<stats>@[%t@]@." s) !registered_stats;
    Hashtbl.iter (fun s (t, n) ->
        Format.fprintf fmt "<stats>@[%s: %f, %d@]@." s t n)
      timing_map

  let () =
    at_exit (fun () ->
        if test_flag stats then begin
            print !formatter;
            Format.pp_print_flush !formatter ()
          end)

(* top-level code disabled because issue #383 and nobody knows why this code was for

  (** SIGXCPU cpu time limit reached *)
  let _ =
    (* TODO? have a possible callback for printing different message*)
    Sys.signal Sys.sigint (Sys.Signal_handle (fun _ -> exit 2))
*)

  let register ~print ~name ~init =
    let s = {name = name; printer = print; value = init} in
    registered_stats :=
      (fun fmt -> Format.fprintf fmt "%s: %a" s.name s.printer s.value)
      :: !registered_stats;
    s

  let mod0 stat f =
    if test_flag stats then stat.value <- f stat.value
  let mod1 stat f x =
    if test_flag stats then stat.value <- f stat.value x
  let mod2 stat f x y =
    if test_flag stats then stat.value <- f stat.value x y

  let register_int ~name ~init =
    register ~print:Format.pp_print_int ~name ~init

  let incr r = if test_flag stats then r.value <- r.value + 1
  let decr r = if test_flag stats then r.value <- r.value - 1

end
