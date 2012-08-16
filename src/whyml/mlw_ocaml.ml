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
open Why3
open Pp
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Printer
open Mlw_expr
open Mlw_decl
open Mlw_module

let debug =
  Debug.register_info_flag
    ~desc:"Print details on program extraction." "extraction"

(** Driver *)

(* (path,id) -> string Hid *)
let stdlib = Hashtbl.create 17
let is_stdlib path id = Hashtbl.mem stdlib (path, id)

(** Printers *)

let iprinter,aprinter,tprinter,pprinter =
  let bl = (* OCaml keywords *)
    ["and"; "as"; "assert"; "asr"; "begin";
     "class"; "constraint"; "do"; "done"; "downto"; "else"; "end";
     "exception"; "external"; "false"; "for"; "fun"; "function";
     "functor"; "if"; "in"; "include"; "inherit"; "initializer";
     "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match";
     "method"; "mod"; "module"; "mutable"; "new"; "object"; "of";
     "open"; "or"; "private"; "rec"; "sig"; "struct"; "then"; "to";
     "true"; "try"; "type"; "val"; "virtual"; "when"; "while"; "with";
     "raise";]
  in
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:isanitize

let forget_tvs () =
  forget_all aprinter

let forget_all () =
  forget_all iprinter;
  forget_all aprinter;
  forget_all tprinter;
  forget_all pprinter

(* info *)

type info = {
  info_syn: syntax_map;
  current_theory: string;
  known_map: Decl.known_map;
  (* symbol_printers : (string * ident_printer) Mid.t; *)
}

let is_constructor info ls = match Mid.find ls.ls_name info.known_map with
  | { d_node = Ddata dl } ->
      let constr (_,csl) = List.exists (fun (cs,_) -> ls_equal cs ls) csl in
      List.exists constr dl
  | _ -> false

(* type variables always start with a quote *)
let print_tv fmt tv =
  fprintf fmt "'%s" (id_unique aprinter tv.tv_name)

(* logic variables always start with a lower case letter *)
let print_vs fmt vs =
  let sanitizer = String.uncapitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer vs.vs_name)

let forget_var vs = forget_id iprinter vs.vs_name
let forget_vars = List.iter forget_var

let print_ident fmt id =
  let s = id_unique iprinter id in
  fprintf fmt "%s" s

let print_path = print_list dot pp_print_string

let print_qident ~sanitizer info fmt id =
  let s = id_unique ~sanitizer iprinter id in
  try
    let _lp, t, _p = Theory.restore_path id in
    (* fprintf fmt "%a/%s/%a" print_path lp t print_path p *)
    if t = info.current_theory then
      fprintf fmt "%s" s
    else
      fprintf fmt "%s.%s" t s
  with Not_found ->
    fprintf fmt "%s" s

let print_lident = print_qident ~sanitizer:String.uncapitalize
let print_uident = print_qident ~sanitizer:String.capitalize

let print_ls info fmt ls = print_lident info fmt ls.ls_name
let print_cs info fmt ls = print_uident info fmt ls.ls_name
let print_ts info fmt ts = print_lident info fmt ts.ts_name

let print_path_id fmt = function
  | [], id -> print_ident fmt id
  | p , id -> fprintf fmt "%a.%a" print_path p print_ident id

let print_theory_name fmt th = print_path_id fmt (th.th_path, th.th_name)
let print_module_name fmt m  = print_theory_name fmt m.mod_theory

let to_be_implemented fmt s =
  fprintf fmt "failwith \"to be implemented\" (* %s *)" s

let tbi s = "failwith \"to be implemented\" (* " ^^ s ^^ " *)"

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let star fmt () = fprintf fmt " *@ "

let rec print_ty_node inn info fmt ty = match ty.ty_node with
  | Tyvar v ->
      print_tv fmt v
  | Tyapp (ts, []) when is_ts_tuple ts ->
      fprintf fmt "unit"
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      fprintf fmt "(%a)" (print_list star (print_ty_node false info)) tl
  | Tyapp (ts, tl) ->
      begin match query_syntax info.info_syn ts.ts_name with
        | Some s -> syntax_arguments s (print_ty_node true info) fmt tl
        | None ->
          begin match tl with
            | [] ->
                print_ts info fmt ts
            | [ty] ->
                fprintf fmt (protect_on inn "%a@ %a")
                  (print_ty_node true info) ty (print_ts info) ts
            | _ ->
                fprintf fmt (protect_on inn "(%a)@ %a")
                  (print_list comma (print_ty_node false info)) tl
                  (print_ts info) ts
        end
      end

let print_ty = print_ty_node false

let print_vsty info fmt v =
  fprintf fmt "%a:@ %a" print_vs v (print_ty info) v.vs_ty

let print_tv_arg = print_tv
let print_tv_args fmt = function
  | [] -> ()
  | [tv] -> fprintf fmt "%a@ " print_tv_arg tv
  | tvl -> fprintf fmt "(%a)@ " (print_list comma print_tv_arg) tvl

let print_ty_arg info fmt ty = fprintf fmt "%a" (print_ty_node true info) ty
let print_vs_arg info fmt vs = fprintf fmt "(%a)" (print_vsty info) vs

(* FIXME: print projections! *)
let print_constr info ty fmt (cs,_) =
  let ty_val = of_option cs.ls_value in
  let m = ty_match Mtv.empty ty_val ty in
  let tl = List.map (ty_inst m) cs.ls_args in
  match tl with
    | [] ->
        fprintf fmt "@[<hov 4>| %a@]" (print_cs info) cs
    | _ ->
        fprintf fmt "@[<hov 4>| %a of %a@]" (print_cs info) cs
          (print_list star (print_ty_arg info)) tl

let print_type_decl info fmt ts = match ts.ts_def with
  | None ->
      fprintf fmt "@[<hov 2>type %a%a@]"
        print_tv_args ts.ts_args (print_ts info) ts
  | Some ty ->
      fprintf fmt "@[<hov 2>type %a%a =@ %a@]"
        print_tv_args ts.ts_args (print_ts info) ts (print_ty info) ty

let print_type_decl info fmt ts =
  print_type_decl info fmt ts; forget_tvs ()

let print_data_decl info fst fmt (ts,csl) =
  let ty = ty_app ts (List.map ty_var ts.ts_args) in
  fprintf fmt "@[<hov 2>%s %a%a =@\n@[<hov>%a@]@]"
    (if fst then "type" else "and")
    print_tv_args ts.ts_args (print_ts info) ts
    (print_list newline (print_constr info ty)) csl

let print_data_decl first info fmt d =
  print_data_decl first info fmt d; forget_tvs ()

(** Inductive *)

let name_args l =
  let r = ref 0 in
  let mk ty = incr r; create_vsymbol (id_fresh "x") ty in
  List.map mk l

let print_ind_decl info fst fmt (ps,_) =
  let vars = name_args ps.ls_args in
  fprintf fmt "@[<hov 2>%s %a %a : bool =@ @[<hov>%a@]@]"
    (if fst then "let rec" else "and") (print_ls info) ps
    (print_list space (print_vs_arg info)) vars
    to_be_implemented "inductive";
  forget_vars vars

let print_ind_decl first info fmt d =
  print_ind_decl first info fmt d; forget_tvs ()

(** Functions/Predicates *)

let rec is_exec_term t = match t.t_node with
  | Tvar _
  | Tconst _
  | Ttrue
  | Tfalse ->
      true
  | Tapp (_, tl) ->
      List.for_all is_exec_term tl
  | Tif (t1, t2, t3) ->
      is_exec_term t1 && is_exec_term t2 && is_exec_term t3
  | Tlet (t1, b2) ->
      is_exec_term t1 && let _, t2 = t_open_bound b2 in is_exec_term t2
  | Tcase (t1, bl) ->
      is_exec_term t1 && List.for_all is_exec_branch bl
  | Teps _ | Tquant _ ->
      false (* TODO: improve? *)
  | Tbinop (_, t1, t2) ->
      is_exec_term t1 && is_exec_term t2
  | Tnot t1 ->
      is_exec_term t1

and is_exec_branch b =
  let _, t = t_open_branch b in is_exec_term t

let print_const fmt = function
  | ConstInt (IConstDecimal s) -> fprintf fmt "(Num.num_of_string \"%s\")" s
  | ConstInt (IConstHexa s) -> fprintf fmt (tbi "0x%s") s
  | ConstInt (IConstOctal s) -> fprintf fmt (tbi "0o%s") s
  | ConstInt (IConstBinary s) -> fprintf fmt (tbi "0b%s") s
  | ConstReal (RConstDecimal (i,f,None)) -> fprintf fmt (tbi "%s.%s") i f
  | ConstReal (RConstDecimal (i,f,Some e)) -> fprintf fmt (tbi "%s.%se%s") i f e
  | ConstReal (RConstHexa (i,f,e)) -> fprintf fmt (tbi "0x%s.%sp%s") i f e

(* can the type of a value be derived from the type of the arguments? *)
let unambig_fs fs =
  let rec lookup v ty = match ty.ty_node with
    | Tyvar u when tv_equal u v -> true
    | _ -> ty_any (lookup v) ty
  in
  let lookup v = List.exists (lookup v) fs.ls_args in
  let rec inspect ty = match ty.ty_node with
    | Tyvar u when not (lookup u) -> false
    | _ -> ty_all inspect ty
  in
  option_apply true inspect fs.ls_value

(** Patterns, terms, and formulas *)

let rec print_pat_node pri info fmt p = match p.pat_node with
  | Term.Pwild ->
      fprintf fmt "_"
  | Term.Pvar v ->
      print_vs fmt v
  | Term.Pas (p, v) ->
      fprintf fmt (protect_on (pri > 1) "%a as %a")
        (print_pat_node 1 info) p print_vs v
  | Term.Por (p, q) ->
      fprintf fmt (protect_on (pri > 0) "%a | %a")
        (print_pat_node 0 info) p (print_pat_node 0 info) q
  | Term.Papp (cs, pl) when is_fs_tuple cs ->
      fprintf fmt "(%a)"
        (print_list comma (print_pat_node 1 info)) pl
  | Term.Papp (cs, pl) ->
    begin match query_syntax info.info_syn cs.ls_name with
      | Some s -> syntax_arguments s (print_pat_node 0 info) fmt pl
      | None when pl = [] -> print_cs info fmt cs
      | _ -> fprintf fmt (protect_on (pri > 1) "%a@ (%a)")
        (print_cs info) cs (print_list comma (print_pat_node 2 info)) pl
    end

let print_pat = print_pat_node 0

let print_binop fmt = function
  | Tand -> fprintf fmt "&&"
  | Tor -> fprintf fmt "||"
  | Tiff -> fprintf fmt "="
  | Timplies -> assert false

let prio_binop = function
  | Tand -> 3
  | Tor -> 2
  | Timplies -> 1
  | Tiff -> 1

let rec print_term info fmt t =
  print_lterm 0 info fmt t

and print_lterm pri info fmt t =
  print_tnode pri info fmt t

and print_app pri ls info fmt tl =
  let isc = is_constructor info ls in
  let print = if isc then print_cs else print_ls in
  match tl with
  | [] ->
      print info fmt ls
  | [t1] ->
      fprintf fmt (protect_on (pri > 4) "%a %a")
        (print info) ls (print_lterm 5 info) t1
  | tl when isc ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a@ (%a)@]")
        (print_cs info) ls (print_list comma (print_lterm 6 info)) tl
  | tl ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a@ %a@]")
        (print_ls info) ls (print_list space (print_lterm 6 info)) tl

and print_tnode pri info fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      print_const fmt c
  | Tapp (fs, tl) when is_fs_tuple fs ->
      fprintf fmt "(%a)" (print_list comma (print_term info)) tl
  | Tapp (fs, tl) ->
      begin match query_syntax info.info_syn fs.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None when unambig_fs fs -> print_app pri fs info fmt tl
      | None ->
          fprintf fmt (protect_on (pri > 0) "@[<hov 2>(%a:@ %a)@]")
            (print_app 5 fs info) tl (print_ty info) (t_type t)
      end
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on (pri > 0) "if @[%a@] then %a@ else %a")
        (print_term info) f (print_term info) t1 (print_term info) t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on (pri > 0) "let %a = @[%a@] in@ %a")
        print_vs v (print_lterm 4 info) t1 (print_term info) t2;
      forget_var v
  | Tcase (t1,bl) ->
      fprintf fmt "@[(match @[%a@] with@\n@[<hov>%a@])@]"
        (print_term info) t1 (print_list newline (print_tbranch info)) bl
  | Teps _
  | Tquant _ ->
      assert false
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tbinop (Timplies,f1,f2) ->
      fprintf fmt "(not (%a) || (%a))" (print_term info) f1 (print_term info) f2
  | Tbinop (b,f1,f2) ->
      let p = prio_binop b in
      fprintf fmt (protect_on (pri > p) "@[<hov 1>%a %a@ %a@]")
        (print_lterm (p + 1) info) f1 print_binop b (print_lterm p info) f2
  | Tnot f ->
      fprintf fmt (protect_on (pri > 4) "not %a") (print_lterm 4 info) f

and print_tbranch info fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" (print_pat info) p (print_term info) t;
  Svs.iter forget_var p.pat_vars

and print_tl info fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_term info))) tl


let print_ls_type info fmt = function
  | None -> fprintf fmt "bool"
  | Some ty -> print_ty info fmt ty

let print_defn info fmt e =
  if is_exec_term e then print_term info fmt e
  else to_be_implemented fmt "not executable"

let print_param_decl info fmt ls =
  let vars = name_args ls.ls_args in
  fprintf fmt "@[<hov 2>let %a %a : %a =@ %a@]"
    (print_ls info) ls
    (print_list space (print_vs_arg info)) vars
    (print_ls_type info) ls.ls_value
    to_be_implemented "uninterpreted symbol";
  forget_vars vars;
  forget_tvs ()

let print_logic_decl info fst fmt (ls,ld) =
  let vl,e = open_ls_defn ld in
  fprintf fmt "@[<hov 2>%s %a %a : %a =@ %a@]"
    (if fst then "let rec" else "and") (print_ls info) ls
    (print_list space (print_vs_arg info)) vl
    (print_ls_type info) ls.ls_value (print_defn info) e;
  forget_vars vl;
  forget_tvs ()

(** Logic Declarations *)

let print_list_next sep print fmt = function
  | [] ->
      ()
  | [x] ->
      print true fmt x
  | x :: r ->
      print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let logic_decl info fmt d = match d.d_node with
  | Dtype ts ->
      print_type_decl info fmt ts
  | Ddata tl ->
      print_list_next newline (print_data_decl info) fmt tl
  | Decl.Dparam ls ->
      print_param_decl info fmt ls
  | Dlogic ll ->
      print_list_next newline (print_logic_decl info) fmt ll
  | Dind (_, il) ->
      print_list_next newline (print_ind_decl info) fmt il
  | Dprop (pk, pr, _) ->
      fprintf fmt "(* %a %a *)" Pretty.print_pkind pk Pretty.print_pr pr

let logic_decl info fmt td = match td.td_node with
  | Decl d ->
      logic_decl info fmt d
  | Use th ->
      fprintf fmt "(* use %a *)" print_theory_name th
  | Clone (th, _) ->
      fprintf fmt "(* clone %a *)" print_theory_name th
  | Meta _ ->
      fprintf fmt "(* meta *)"

(** Theories *)

let ocaml_driver env =
  try
    let file = Filename.concat Config.datadir "drivers/ocaml.drv" in
    Driver.load_driver env file []
  with e ->
    eprintf "cannot find driver 'ocaml'@.";
    raise e

let extract_theory env ?old fmt th =
  ignore (old);
  let drv = ocaml_driver env in
  let sm = Driver.syntax_map drv in
  let info = {
    info_syn = sm;
    current_theory = th.th_name.id_string;
    known_map = Task.task_known (Task.use_export None th) } in
  fprintf fmt
    "(* This file has been generated from Why3 theory %a *)@\n@\n"
    print_theory_name th;
  print_list newline2 (logic_decl info) fmt th.th_decls;
  fprintf fmt "@."

(** Program expressions *)

let rec print_expr _fmt e = match e.e_node with
  | _ -> assert false (*TODO*)
(***
  | Elogic t ->
      print_term fmt t
  | Elocal v ->
      print_pv fmt v
  | Eglobal ps ->
      print_ls fmt ps.ps_pure
  | Efun (bl, t) ->
      fprintf fmt "@[<hov 2>fun %a ->@ %a@]"
        (print_list space print_pv_arg) bl print_triple t
  | Elet (v, e1, e2) ->
      fprintf fmt "@[<hv 0>@[<hov 2>let %a =@ %a in@]@ %a@]"
        print_vs v.pv_pure
        print_lexpr e1 print_lexpr e2;
    forget_var v.pv_pure

  | Eif (e1, e2, e3) ->
      fprintf fmt "@[if %a@ then@ %a else@ %a@]"
        print_lexpr e1 print_lexpr e2 print_lexpr e3

  | Eany _c ->
      fprintf fmt "assert false (* TODO: call *)"

  | Emark (_, _)  ->
      fprintf fmt "<todo: Emark>"
  | Eassert (_, f) ->
      fprintf fmt "@[assert {%a}@]" print_term f
  | Efor (_, _, _, _, _, e) ->
      fprintf fmt "@[<hov 2>for ... do@ %a@ done@]" print_lexpr e
  | Etry (e1, bl) ->
      let print_handler fmt (es, vs, e) =
        fprintf fmt "| %a %a -> %a" print_cs es (print_option print_pv) vs
          print_expr e
      in
      fprintf fmt "@[<hov 2>begin try@ %a@\nwith@\n%a end@]"
        print_expr e1 (print_list newline print_handler) bl
  | Eraise (es, e)  ->
      fprintf fmt "(raise (%a %a))" print_cs es (print_option print_expr) e
  | Ematch (v, cl) ->
      fprintf fmt "@[<hov 2>match %a with@ %a@]" print_pv v
        (print_list newline print_branch) cl
  | Eloop (_, e1) ->
      fprintf fmt "@[<hov 2>while true do@ %a done@]" print_expr e1
  | Eletrec (_, _)  ->
      fprintf fmt "<todo: Eletrec>"
  | Eabsurd ->
      fprintf fmt "assert false (* absurd *)"
  | Eabstract(e, _) ->
      fprintf fmt "@[%a (* abstract *)@]" print_expr e

and print_lexpr fmt e =
  print_expr fmt e

and print_pv fmt v =
  fprintf fmt "%a" print_vs v.pv_pure

and print_pv_arg fmt v =
  fprintf fmt "(%a)" print_vsty v.pv_pure

and print_triple fmt (_, e, _) =
  print_expr fmt e

and print_recfun fmt (v, bl, t, _) =
  fprintf fmt "@[<hov 2>rec %a@ %a =@ %a@]"
    print_pv v (print_list space print_pv_arg) bl print_triple t

and print_branch fmt (p, e) =
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pattern p print_expr e

and print_pattern fmt p =
  print_pat fmt p.ppat_pat
***)

(** Program Declarations *)

let pdecl _fmt pd = match pd.pd_node with
  | _ -> () (*TODO*)
(***
  | Dlet (ps, e) ->
      fprintf fmt "@[<hov 2>let %a =@ %a@]"
        print_ls ps.ps_pure print_expr e
  | Dletrec _dl ->
      fprintf fmt "(* pgm let rec *)" (* TODO *)
  | Dparam ps ->
      print_param_decl fmt ps.ps_pure
***)

(** Modules *)

let extract_module _env ?old fmt m =
  ignore (old);
  fprintf fmt
    "(* This file has been generated from Why3 module %a *)@\n@\n"
    print_module_name m;
  print_list newline2 pdecl fmt m.mod_decls;
  fprintf fmt "@."


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
