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

open Why3
open Util
open Ident
open Ty
open Term
open Theory
open Printer
open Driver_ast
open Mlw_ty
open Mlw_expr
open Mlw_module

type driver = {
  drv_lib         : Mlw_typing.mlw_library;
  drv_printer     : string option;
  drv_prelude     : Printer.prelude;
  drv_thprelude   : Printer.prelude_map;
  drv_blacklist   : Printer.blacklist;
  drv_syntax      : Printer.syntax_map;
}

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
  let f = Driver_lexer.parse_file_extract input_lexer lb in
  Stack.iter close_in to_close;
  f

(* dead code
exception NoPrinter
*)
exception Duplicate    of string
exception UnknownType  of (string list * string list)
exception UnknownLogic of (string list * string list)
exception UnknownProp  of (string list * string list)
exception UnknownVal   of (string list * string list)
exception UnknownExn   of (string list * string list)
exception FSymExpected of lsymbol
exception PSymExpected of lsymbol

let load_driver lib file extra_files =
  let prelude   = ref [] in
  let printer   = ref None in
  let blacklist = Queue.create () in

  let set_or_raise loc r v error = match !r with
    | Some _ -> raise (Loc.Located (loc, Duplicate error))
    | None   -> r := Some v
  in
  let add_to_list r v = (r := v :: !r) in
  let add_global (loc, g) = match g with
    | EPrelude s -> add_to_list prelude s
    | EPrinter s -> set_or_raise loc printer s "printer"
    | EBlacklist sl -> List.iter (fun s -> Queue.add s blacklist) sl
  in
  let f = load_file file in
  List.iter add_global f.fe_global;

  let thprelude = ref Mid.empty in
  let syntax_map = ref Mid.empty in
  let qualid    = ref [] in

  let find_pr th (loc,q) = try Theory.ns_find_pr th.th_export q
    with Not_found -> raise (Loc.Located (loc, UnknownProp (!qualid,q)))
  in
  let find_ls th (loc,q) = try Theory.ns_find_ls th.th_export q
    with Not_found -> raise (Loc.Located (loc, UnknownLogic (!qualid,q)))
  in
  let find_ts th (loc,q) = try Theory.ns_find_ts th.th_export q
    with Not_found -> raise (Loc.Located (loc, UnknownType (!qualid,q)))
  in
  let find_fs th q =
    let ls = find_ls th q in
    if ls.ls_value = None then raise (FSymExpected ls) else ls in
  let find_ps th q =
    let ls = find_ls th q in
    if ls.ls_value <> None then raise (PSymExpected ls) else ls in
  let add_syntax id s = syntax_map := Mid.add id s !syntax_map in
  let add_local th = function
    | Rprelude s ->
        let l = Mid.find_def [] th.th_name !thprelude in
        thprelude := Mid.add th.th_name (s::l) !thprelude
    | Rsyntaxts (_,q,s) ->
        let ts = find_ts th q in
        check_syntax_type ts s;
        add_syntax ts.ts_name s
    | Rsyntaxfs (_,q,s) ->
        let fs = find_fs th q in
        check_syntax_logic fs s;
        add_syntax fs.ls_name s
    | Rsyntaxps (_,q,s) ->
        let ps = find_ps th q in
        check_syntax_logic ps s;
        add_syntax ps.ls_name s
    | Rremovepr (_,q) ->
        ignore (find_pr th q)
    | Rmeta (_,s,al) ->
        let convert = function
          | PMAts q  -> MAts (find_ts th q)
          | PMAfs q  -> MAls (find_fs th q)
          | PMAps q  -> MAls (find_ps th q)
          | PMApr q  -> MApr (find_pr th q)
          | PMAstr s -> MAstr s
          | PMAint i -> MAint i
        in
        let m = lookup_meta s in
        ignore (create_meta m (List.map convert al))
  in
  let add_local th (loc,rule) =
    try add_local th rule with e -> raise (Loc.Located (loc,e))
  in
  let find_val m (loc,q) =
    try match ns_find_ps m.mod_export q with
    | PV pv -> pv.pv_vs.vs_name
    | PS ps -> ps.ps_name
    | PL _ | XS _ | LS _ -> raise Not_found
    with Not_found -> raise (Loc.Located (loc, UnknownVal (!qualid,q)))
  in
  let find_xs m (loc,q) =
    try match ns_find_ps m.mod_export q with
    | XS xs -> xs
    | PV _ | PS _ | PL _ | LS _ -> raise Not_found
    with Not_found -> raise (Loc.Located (loc, UnknownExn (!qualid,q)))
  in
  let add_local_module loc m = function
    | MRtheory trule -> add_local m.mod_theory (loc,trule)
    | MRexception (_,q,s) ->
        let xs = find_xs m q in
        add_syntax xs.xs_name s
    | MRval (_,q,s) ->
        let id = find_val m q in
        add_syntax id s
  in
  let add_local_module m (loc,rule) =
    try add_local_module loc m rule with e -> raise (Loc.Located (loc,e))
  in
  let add_theory { thr_name = (loc,q); thr_rules = trl } =
    let f,id = let l = List.rev q in List.rev (List.tl l),List.hd l in
    let th =
      try Env.read_theory ~format:"why" (Env.env_of_library lib) f id
      with e -> raise (Loc.Located (loc,e))
    in
    qualid := q;
    List.iter (add_local th) trl
  in
  let add_module { mor_name = (loc,q); mor_rules = mrl } =
    let f,id = let l = List.rev q in List.rev (List.tl l),List.hd l in
    let m =
      try let mm, _ = Env.read_lib_file lib f in Mstr.find id mm
      with e -> raise (Loc.Located (loc,e))
    in
    qualid := q;
    List.iter (add_local_module m) mrl
  in
  List.iter add_theory f.fe_th_rules;
  List.iter add_module f.fe_mo_rules;
  List.iter (fun f ->
    let fe = load_file f in
    List.iter add_theory fe.fe_th_rules;
    List.iter add_module fe.fe_mo_rules)
    extra_files;
  {
    drv_lib         = lib;
    drv_printer     = !printer;
    drv_prelude     = List.rev !prelude;
    drv_thprelude   = Mid.map List.rev !thprelude;
    drv_blacklist   = Queue.fold (fun l s -> s :: l) [] blacklist;
    drv_syntax      = !syntax_map;
  }



(* exception report *)

let string_of_qualid thl idl =
  String.concat "." thl ^ "." ^ String.concat "." idl

let () = Exn_printer.register (fun fmt exn -> match exn with
(* dead code
  | NoPrinter -> Format.fprintf fmt
      "No printer specified in the driver file"
*)
  | Duplicate s -> Format.fprintf fmt
      "Duplicate %s specification" s
  | UnknownType (thl,idl) -> Format.fprintf fmt
      "Unknown type symbol %s" (string_of_qualid thl idl)
  | UnknownLogic (thl,idl) -> Format.fprintf fmt
      "Unknown logical symbol %s" (string_of_qualid thl idl)
  | UnknownProp (thl,idl) -> Format.fprintf fmt
      "Unknown proposition %s" (string_of_qualid thl idl)
  | UnknownVal (thl,idl) -> Format.fprintf fmt
      "Unknown val %s" (string_of_qualid thl idl)
  | UnknownExn (thl,idl) -> Format.fprintf fmt
      "Unknown exception %s" (string_of_qualid thl idl)
  | FSymExpected ls -> Format.fprintf fmt
      "%a is not a function symbol" Pretty.print_ls ls
  | PSymExpected ls -> Format.fprintf fmt
      "%a is not a predicate symbol" Pretty.print_ls ls
  | e -> raise e)


