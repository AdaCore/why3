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

let formatter = ref Format.err_formatter

exception UnknownFlag of string

type flag = { flag_name : string;
              mutable flag_value : bool }

let flag_table = Hashtbl.create 17

let fst3 (flag,_,_) = flag
let snd3 (_,info,_) = info
let thd3 (_,_,desc) = desc

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
  Hashtbl.fold (fun s (v,_,desc) acc -> (s,v,v.flag_value,desc)::acc) flag_table []

let lookup_flag s =
  try fst3 (Hashtbl.find flag_table s) with Not_found -> raise (UnknownFlag s)

let is_info_flag s =
  try snd3 (Hashtbl.find flag_table s) with Not_found -> raise (UnknownFlag s)

let flag_desc s =
  try thd3 (Hashtbl.find flag_table s) with Not_found -> raise (UnknownFlag s)

let test_flag s = s.flag_value
let test_noflag s = not s.flag_value

let set_flag s = s.flag_value <- true
let unset_flag s = s.flag_value <- false
let toggle_flag s = s.flag_value <- not s.flag_value

let () = Exn_printer.register (fun fmt e -> match e with
  | UnknownFlag s -> Format.fprintf fmt "unknown debug flag `%s'@." s
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
  type spec = (Arg.key * Arg.spec * Arg.doc)

  let desc_debug_list, option_list =
    let opt_list_flags = ref false in
    let desc =
      "--list-debug-flags", Arg.Set opt_list_flags,
      " list known debug flags" in
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
        Format.printf "@[<hov 2>Known debug flags \
            (`*' marks the flags selected by --debug-all):@\n%a@]@."
          (Pp.print_list Pp.newline print)
          (List.sort Pervasives.compare list);
      end;
      !opt_list_flags in
    desc,list

  let opt_list_flags = Queue.create ()

  let add_flag s = Queue.add s opt_list_flags

  let desc_shortcut flag option desc =
    let set_flag () = add_flag flag in
    let desc = Pp.sprintf "%s (same as --debug %s)" desc flag in
    (option, Arg.Unit set_flag, desc)

  let desc_debug =
    ("--debug", Arg.String add_flag, "<flag> set a debug flag")

  let opt_debug_all = ref false

  let desc_debug_all =
    let desc_debug =
      Pp.sprintf
        " set all debug flags that do not change Why3 behaviour" in
    ("--debug-all", Arg.Set opt_debug_all, desc_debug)

  let set_flags_selected () =
    if !opt_debug_all then
      List.iter
        (fun (s,f,_,_) -> if is_info_flag s then set_flag f)
        (list_flags ());
    Queue.iter (fun flag -> let flag = lookup_flag flag in set_flag flag)
      opt_list_flags;
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
  let max_name_size = ref 0

  let registered_stats :  (Format.formatter -> unit) list ref = ref []

  let rec print_nb_char fmt = function
    | n when n <= 0 -> ()
    | n -> Format.pp_print_char fmt ' '; print_nb_char fmt (n-1)


  let print_stat fmt stat =
    Format.fprintf fmt "@[%s%a: %a@]"
      stat.name print_nb_char (!max_name_size - String.length stat.name)
      stat.printer stat.value

  let print () =
    dprintf stats "@[%a@]@\n"
      (Pp.print_list Pp.newline (fun fmt f -> f fmt))
      !registered_stats


  let () = at_exit (fun () ->
    print ();
    Format.pp_print_flush !formatter ())

  (** SIGXCPU cpu time limit reached *)
  let _ =
    (* TODO? have a possible callback for printing different message*)
    Sys.signal Sys.sigint (Sys.Signal_handle (fun _ -> exit 2))

  let register ~print ~name ~init =
    let s = {name = name; printer = print; value = init} in
    max_name_size := max !max_name_size (String.length name);
    registered_stats := (fun fmt -> print_stat fmt s)::!registered_stats;
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
