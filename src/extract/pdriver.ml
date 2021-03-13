(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Theory
open Driver_ast

let debug =
  Debug.register_info_flag "extraction"
    ~desc:"Print@ details@ of@ program@ extraction."

type driver = {
  drv_env         : Env.env;
  drv_printer     : string option;
  drv_prelude     : Printer.prelude;
  drv_thprelude   : Printer.prelude_map;
  drv_thexportpre : Printer.prelude_export_map;
  drv_thinterface : Printer.interface_map;
  drv_thexportint : Printer.interface_export_map;
  drv_blacklist   : Printer.blacklist;
  drv_syntax      : Printer.syntax_map;
  drv_literal     : Printer.syntax_map;
  drv_prec        : (int list) Mid.t;
  drv_noextract   : Sid.t;
}


type printer_args = {
  env         : Env.env;
  prelude     : Printer.prelude;
  thprelude   : Printer.prelude_map;
  thexportpre : Printer.prelude_export_map;
  thinterface : Printer.interface_map;
  thexportint : Printer.interface_export_map;
  blacklist   : Printer.blacklist;
  syntax      : Printer.syntax_map;
  literal     : Printer.syntax_map;
  prec        : (int list) Mid.t;
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

exception Duplicate    of string
exception UnknownType  of (string list * string list)
exception UnknownLogic of (string list * string list)
exception UnknownProp  of (string list * string list)
exception UnknownVal   of (string list * string list)
exception UnknownExn   of (string list * string list)
exception FSymExpected of lsymbol
exception PSymExpected of lsymbol

let load_driver env file extra_files =
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
  let thexportprelude = ref Mid.empty in
  let thinterface = ref Mid.empty in
  let thexportinterface = ref Mid.empty in
  let noextract = ref Sid.empty in
  let syntax_map = ref Mid.empty in
  let literal_map = ref Mid.empty in
  let prec_map  = ref Mid.empty in
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
  let add_syntax id s b =
    syntax_map := Mid.add id (s,if b then 1 else 0) !syntax_map in
  let add_literal id s b =
    literal_map := Mid.add id (s,if b then 1 else 0) !literal_map in

  let add_local th = function
    | Rprelude (s, false) ->
        let l = Mid.find_def [] th.th_name !thprelude in
        thprelude := Mid.add th.th_name (s::l) !thprelude
    | Rprelude (s, true) ->
        let l = Mid.find_def [] th.th_name !thexportprelude in
        thexportprelude := Mid.add th.th_name (s::l) !thexportprelude
    | Rsyntaxts (q,s,b) ->
        let ts = find_ts th q in
        Printer.check_syntax_type ts s;
        add_syntax ts.ts_name s b
    | Rsyntaxfs _ | Rsyntaxps _ as r ->
        let syntaxes =
          match r with
          | Rsyntaxfs _ -> "`syntax constant' and `syntax function' are"
          | Rsyntaxps _ -> "`syntax predicate' is"
          | _ -> assert false in
        Format.eprintf "%s invalid in extraction drivers, use `syntax val' instead." syntaxes;
        exit 1
    | Rliteral (q,s,b) ->
        let ts = find_ts th q in
        add_literal ts.ts_name s b
    | Rremovepr (q) ->
      ignore (find_pr th q)
    | Rremoveall ->
      let it key _ = match (Mid.find key th.th_known).Decl.d_node with
        | Decl.Dprop (_,symb,_) -> ignore symb
        | _ -> ()
      in
      Mid.iter it th.th_local
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
        ignore (create_meta m (List.map convert al))
    | Ruse _ ->
        Loc.errorm "theory use cannot be used in extraction driver"
  in
  let add_local th (loc,rule) = Loc.try2 ~loc add_local th rule in
  let open Pmodule in
  let find_val m (loc,q) =
    try match ns_find_prog_symbol m.mod_export q with
    | PV pv -> pv.Ity.pv_vs.vs_name
    | RS rs -> rs.Expr.rs_name
    | OO _ -> raise Not_found (* TODO: proper error message *)
    with Not_found -> Loc.error ~loc (UnknownVal (!qualid,q))
  in
  let find_xs m (loc,q) =
    try ns_find_xs m.mod_export q
    with Not_found -> Loc.error ~loc (UnknownExn (!qualid,q))
  in
  let add_local_module loc m = function
    | MRinterface (s, false) ->
       let th = m.mod_theory in
       let l = Mid.find_def [] th.th_name !thinterface in
       thinterface := Mid.add th.th_name (s::l) !thinterface
    | MRinterface (s, true) ->
       let th = m.mod_theory in
       let l = Mid.find_def [] th.th_name !thexportinterface in
       thexportinterface := Mid.add th.th_name (s::l) !thexportinterface
    | MRexception (q,s) ->
        let xs = find_xs m q in
        add_syntax xs.Ity.xs_name s false
    | MRval (q,s,p) ->
        let id = find_val m q in
        add_syntax id s false;
        prec_map := Mid.add id p !prec_map;
    | MRnoextract ->
        noextract := Sid.add m.mod_theory.th_name !noextract
    | MRtheory trule ->
        add_local m.mod_theory (loc,trule)
  in
  let add_local_module m (loc,rule) =
    Loc.try3 ~loc add_local_module loc m rule
  in
  let add_theory { thr_name = (loc,q); thr_rules = trl } =
    let f,id = let l = List.rev q in List.rev (List.tl l),List.hd l in
    let th = Loc.try3 ~loc Env.read_theory env f id in
    qualid := q;
    List.iter (add_local th) trl
  in
  let add_module { mor_name = (loc,q); mor_rules = mrl } =
    let f,id = let l = List.rev q in List.rev (List.tl l),List.hd l in
    let m = Loc.try3 ~loc read_module env f id in
    qualid := q;
    List.iter (add_local_module m) mrl
  in
  List.iter add_theory f.fe_th_rules;
  List.iter add_module f.fe_mo_rules;
  List.iter (fun f ->
    let fe = load_file f in
    List.iter add_theory fe.fe_th_rules;
    List.iter add_module fe.fe_mo_rules;
    List.iter add_global fe.fe_global)
    extra_files;
  {
    drv_env         = env;
    drv_printer     = !printer;
    drv_prelude     = List.rev !prelude;
    drv_thprelude   = Mid.map List.rev !thprelude;
    drv_thexportpre = Mid.map List.rev !thexportprelude;
    drv_thinterface = Mid.map List.rev !thinterface;
    drv_thexportint = Mid.map List.rev !thexportinterface;
    drv_blacklist   = Queue.fold (fun l s -> s :: l) [] blacklist;
    drv_syntax      = !syntax_map;
    drv_literal     = !literal_map;
    drv_prec        = !prec_map;
    drv_noextract   = !noextract;
  }

(* registering printers for programs *)

open Wstdlib

type filename_generator = ?fname:string -> Pmodule.pmodule -> string

type decl_printer =
  printer_args -> ?old:in_channel -> ?fname:string ->
  Pmodule.pmodule -> Mltree.decl Pp.pp

(** Things to print as header/footer. *)
type border_printer =
  printer_args -> ?old:in_channel -> ?fname:string ->
  Pmodule.pmodule Pp.pp

(** Things to do at the beginning of a module, e.g. open/#include.
    Only used in modular extraction. *)
type prelude_printer =
  printer_args -> ?old:in_channel -> ?fname:string ->
  deps:Pmodule.pmodule list ->
  global_prelude:Printer.prelude ->
  prelude:Printer.prelude ->
  Pmodule.pmodule Pp.pp

type file_printer = {
  filename_generator : filename_generator;
  decl_printer : decl_printer;
  header_printer : border_printer;
  prelude_printer : prelude_printer;
  footer_printer : border_printer;
}

type printer = {
  desc           : Pp.formatted;
  implem_printer : file_printer;
  interf_printer : file_printer option;
  flat_printer   : file_printer;
}

let default_prelude_printer _ ?old:_ ?fname:_ ~deps:_ ~global_prelude
      ~prelude fmt _ =
  Printer.print_prelude fmt global_prelude;
  Printer.print_prelude fmt prelude

let dummy_border_printer _ ?old:_ ?fname:_ _ _ = ()

let printers : printer Hstr.t = Hstr.create 17

exception KnownPrinter of string
exception UnknownPrinter of string
exception NoPrinter

let register_printer s p =
  if Hstr.mem printers s then raise (KnownPrinter s);
  Hstr.replace printers s p

let lookup_printer drv =
  let p = match drv.drv_printer with
    | None -> raise NoPrinter
    | Some p -> p
  in
  let printer_args = {
      env         = drv.drv_env;
      prelude     = drv.drv_prelude;
      thprelude   = drv.drv_thprelude;
      thexportpre = drv.drv_thexportpre;
      thinterface = drv.drv_thinterface;
      thexportint = drv.drv_thexportint;
      blacklist   = drv.drv_blacklist;
      syntax      = drv.drv_syntax;
      literal     = drv.drv_literal;
      prec        = drv.drv_prec;
    }
  in
  try
    let printer = Hstr.find printers p in printer_args, printer
  with Not_found -> raise (UnknownPrinter p)

let list_printers () =
  Hstr.fold (fun k { desc = desc; _ } acc -> (k,desc)::acc) printers []

(* exception report *)

let string_of_qualid thl idl =
  String.concat "." thl ^ "." ^ String.concat "." idl

let () = Exn_printer.register (fun fmt exn ->
  let open Format in
  match exn with
  | Duplicate s -> fprintf fmt
      "Duplicate %s specification" s
  | UnknownType (thl,idl) -> fprintf fmt
      "Unknown type symbol %s" (string_of_qualid thl idl)
  | UnknownLogic (thl,idl) -> fprintf fmt
      "Unknown logical symbol %s" (string_of_qualid thl idl)
  | UnknownProp (thl,idl) -> fprintf fmt
      "Unknown proposition %s" (string_of_qualid thl idl)
  | UnknownVal (thl,idl) -> fprintf fmt
      "Unknown val %s" (string_of_qualid thl idl)
  | UnknownExn (thl,idl) -> fprintf fmt
      "Unknown exception %s" (string_of_qualid thl idl)
  | FSymExpected ls -> fprintf fmt
      "%a is not a function symbol" Pretty.print_ls ls
  | PSymExpected ls -> fprintf fmt
      "%a is not a predicate symbol" Pretty.print_ls ls
  | NoPrinter ->
      fprintf fmt "Missing printer in driver"
  | KnownPrinter s ->
      fprintf fmt "Program printer '%s' is already registered" s
  | UnknownPrinter s ->
      fprintf fmt "Unknown program printer '%s'" s
  | e -> raise e)
