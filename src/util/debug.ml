(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

let formatter = ref Format.err_formatter

exception UnknownFlag of string

type flag = bool ref

let flag_table = Hashtbl.create 17

let fst3 (flag,_,_) = flag
let snd3 (_,info,_) = info
let thd3 (_,_,desc) = desc

let gen_register_flag (desc : Pp.formatted) s info =
  try
    fst3 (Hashtbl.find flag_table s)
  with Not_found ->
    let flag = ref false in
    Hashtbl.replace flag_table s (flag,info,desc);
    flag

let register_info_flag ~desc s = gen_register_flag desc s true
let register_flag      ~desc s = gen_register_flag desc s false

let list_flags () =
  Hashtbl.fold (fun s (v,_,desc) acc -> (s,v,!v,desc)::acc) flag_table []

let lookup_flag s =
  try fst3 (Hashtbl.find flag_table s) with Not_found -> raise (UnknownFlag s)

let is_info_flag s =
  try snd3 (Hashtbl.find flag_table s) with Not_found -> raise (UnknownFlag s)

let flag_desc s =
  try thd3 (Hashtbl.find flag_table s) with Not_found -> raise (UnknownFlag s)

let test_flag s = !s
let test_noflag s = not !s

let set_flag s = s := true
let unset_flag s = s := false
let toggle_flag s = s := not !s

let () = Exn_printer.register (fun fmt e -> match e with
  | UnknownFlag s -> Format.fprintf fmt "unknown debug flag `%s'@." s
  | _ -> raise e)

let stack_trace = register_info_flag "stack_trace"
  ~desc:"Avoid@ catching@ exceptions@ in@ order@ to@ get@ the@ stack@ trace."

let timestamp = register_info_flag "timestamp"
  ~desc:"Print@ a@ timestamp@ before@ debugging@ messages."

let time_start = Unix.gettimeofday ()

let set_debug_formatter = (:=) formatter
let get_debug_formatter () = !formatter

let dprintf flag s =
  if !flag then
    begin
      if !timestamp then Format.fprintf !formatter "<%f>"
        (Unix.gettimeofday () -. time_start);
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
      " List known debug flags" in
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
    ("--debug", Arg.String add_flag, "<flag> Set a debug flag")

  let opt_debug_all = ref false

  let desc_debug_all =
    let desc_debug =
      Pp.sprintf
        " Set all debug flags that do not change Why3 behaviour" in
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
