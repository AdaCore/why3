(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Pp

open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Printer
open Mlw_ty

let debug =
  Debug.register_info_flag
    ~desc:"Print details on program extraction." "extraction"

let clean_fname fname =
  let fname = Filename.basename fname in
  (try Filename.chop_extension fname with _ -> fname)

let modulename ?fname th =
  let fname = match fname, th.th_path with
    | Some fname, _ -> clean_fname fname
    | None, [] -> assert false
    | None, path -> String.concat "__" path
  in
  fname ^ "__" ^ th.th_name.Ident.id_string

let extract_filename ?fname th =
  (modulename ?fname th) ^ ".ml"

let modulename path t =
  String.capitalize
    (if path = [] then "why3__" ^ t else String.concat "__" path ^ "__" ^ t)

(** Driver *)

(* dead code

(* (path,id) -> string Hid *)
let stdlib = Hashtbl.create 17
let is_stdlib path id = Hashtbl.mem stdlib (path, id)

*)

(** Printers *)

let ocaml_keywords =
  ["and"; "as"; "assert"; "asr"; "begin";
   "class"; "constraint"; "do"; "done"; "downto"; "else"; "end";
   "exception"; "external"; "false"; "for"; "fun"; "function";
   "functor"; "if"; "in"; "include"; "inherit"; "initializer";
   "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match";
   "method"; "mod"; "module"; "mutable"; "new"; "object"; "of";
   "open"; "or"; "private"; "rec"; "sig"; "struct"; "then"; "to";
   "true"; "try"; "type"; "val"; "virtual"; "when"; "while"; "with";
   "raise";]

let is_ocaml_keyword =
  let h = Hashtbl.create 17 in
  List.iter (fun s -> Hashtbl.add h s ()) ocaml_keywords;
  Hashtbl.mem h

let iprinter,aprinter,_tprinter,_pprinter =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
  create_ident_printer ocaml_keywords ~sanitizer:isanitize,
  create_ident_printer ocaml_keywords ~sanitizer:lsanitize,
  create_ident_printer ocaml_keywords ~sanitizer:lsanitize,
  create_ident_printer ocaml_keywords ~sanitizer:isanitize

let forget_tvs () =
  forget_all aprinter

(* dead code
let forget_all () =
  forget_all iprinter;
  forget_all aprinter;
  forget_all tprinter;
  forget_all pprinter
*)

(* info *)

type info = {
  info_syn: syntax_map;
  current_theory: Theory.theory;
  th_known_map: Decl.known_map;
  mo_known_map: Mlw_decl.known_map;
  fname: string option;
  (* symbol_printers : (string * ident_printer) Mid.t; *)
}

let is_constructor info ls =
  (* eprintf "is_constructor: ls=%s@." ls.ls_name.id_string; *)
  match Mid.find_opt ls.ls_name info.th_known_map with
    | Some { d_node = Ddata dl } ->
        let constr (_,csl) = List.exists (fun (cs,_) -> ls_equal cs ls) csl in
        List.exists constr dl
    | _ -> false

let get_record info ls =
  match Mid.find_opt ls.ls_name info.th_known_map with
    | Some { d_node = Ddata dl } ->
        let rec lookup = function
        | [] -> []
        | (_, [cs, pjl]) :: _ when ls_equal cs ls ->
          (try List.map Opt.get pjl with _ -> [])
        | _ :: dl -> lookup dl
        in
        lookup dl
    | Some _ | None ->
        []

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
  try
    let lp, t, p =
      try Mlw_module.restore_path id
      with Not_found -> Theory.restore_path id in
    let s = String.concat "__" p in
    let s = Ident.sanitizer char_to_alpha char_to_alnumus s in
    let s = sanitizer s in
    let s = if is_ocaml_keyword s then s ^ "_renamed" else s in
    if Sid.mem id info.current_theory.th_local then
      fprintf fmt "%s" s
    else
      fprintf fmt "%s.%s" (modulename lp t) s
  with Not_found ->
    let s = id_unique ~sanitizer iprinter id in
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
let print_module_name fmt m  = print_theory_name fmt m.Mlw_module.mod_theory

let to_be_implemented fmt s =
  fprintf fmt "failwith \"to be implemented\" (* %s *)" s

let tbi s = "failwith \"to be implemented\" (* " ^^ s ^^ " *)"

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let star fmt () = fprintf fmt " *@ "

let has_syntax info id = Mid.mem id info.info_syn

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

let print_constr info fmt (cs,_) = match cs.ls_args with
  | [] ->
      fprintf fmt "@[<hov 4>| %a@]" (print_cs info) cs
  | tl ->
      fprintf fmt "@[<hov 4>| %a of %a@]" (print_cs info) cs
        (print_list star (print_ty_arg info)) tl

let print_type_decl info fmt ts = match ts.ts_def with
  | None ->
      fprintf fmt
        "@[<hov 2>type %a%a (* to be defined (uninterpreted type) *)@]"
        print_tv_args ts.ts_args (print_ts info) ts
  | Some ty ->
      fprintf fmt "@[<hov 2>type %a%a =@ %a@]"
        print_tv_args ts.ts_args (print_ts info) ts (print_ty info) ty

let print_type_decl info fmt ts =
  if has_syntax info ts.ts_name then
    fprintf fmt "(* type %a is overridden by driver *)"
      (print_lident info) ts.ts_name
  else begin print_type_decl info fmt ts; forget_tvs () end

let print_data_decl info fst fmt (ts,csl) =
  let print_default () = print_list newline (print_constr info) fmt csl in
  let print_field fmt ls =
    fprintf fmt "%a: %a"
      (print_ls info) ls (print_ty info) (Opt.get ls.ls_value) in
  let print_defn fmt = function
    | [cs, _] ->
        let pjl = get_record info cs in
        if pjl = [] then print_default ()
        else fprintf fmt "{ %a }" (print_list semi print_field) pjl
    | _ ->
        print_default ()
  in
  fprintf fmt "@[<hov 2>%s %a%a =@\n@[<hov>%a@]@]"
    (if fst then "type" else "and")
    print_tv_args ts.ts_args (print_ts info) ts print_defn csl

let print_data_decl info first fmt (ts, _ as d) =
  if has_syntax info ts.ts_name then
    fprintf fmt "(* type %a is overridden by driver *)"
      (print_lident info) ts.ts_name
  else begin print_data_decl info first fmt d; forget_tvs () end

let is_record = function
  | _, [_, pjl] -> List.for_all ((<>) None) pjl
  | _ -> false

let print_projections info fmt (_, csl) =
  let pjl = List.filter ((<>) None) (snd (List.hd csl)) in
  let pjl = List.map Opt.get pjl in
  let print ls =
    let print_branch fmt (cs, pjl) =
      let print_arg fmt = function
        | Some ls' when ls_equal ls' ls -> fprintf fmt "x"
        | _ -> fprintf fmt "_" in
      fprintf fmt "| %a (%a) -> x"
        (print_cs info) cs (print_list comma print_arg) pjl
    in
    fprintf fmt "@[<hov 2>let %a = function@\n" (print_ls info) ls;
    print_list newline print_branch fmt csl;
    fprintf fmt "@]@\n@\n"
  in
  List.iter print pjl

let print_projections info fmt (ts, _ as d) =
  if not (has_syntax info ts.ts_name) && not (is_record d) then begin
    print_projections info fmt d; forget_tvs ()
  end

(** Inductive *)

let name_args l =
  let r = ref 0 in
  let mk ty = incr r; create_vsymbol (id_fresh "x") ty in
  List.map mk l

let print_ind_decl info sign fst fmt (ps,_ as d) =
  let print_ind fmt d =
    if fst then Pretty.print_ind_decl fmt sign d
    else Pretty.print_next_ind_decl fmt d in
  let vars = name_args ps.ls_args in
  fprintf fmt "@[<hov 2>%s %a %a : bool =@ @[<hov>%a@\n(* @[%a@] *)@]@]"
    (if fst then "let rec" else "and") (print_ls info) ps
    (print_list space (print_vs_arg info)) vars
    to_be_implemented "inductive"
    print_ind d;
  forget_vars vars

let print_ind_decl info sign first fmt (ls, _ as d) =
  if has_syntax info ls.ls_name then
    fprintf fmt "(* inductive %a is overridden by driver *)"
      (print_lident info) ls.ls_name
  else begin print_ind_decl info sign first fmt d; forget_tvs () end

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
  | ConstInt (IConstDecimal s) ->
      fprintf fmt "(Why3__BuiltIn.int_constant \"%s\")" s
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
  Opt.fold (fun _ -> inspect) true fs.ls_value

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
  let isconstr = is_constructor info ls in
  let is_field (_, csl) = match csl with
    | [_, pjl] ->
        List.for_all ((<>) None) pjl && List.exists ((=) (Some ls)) pjl
    | _ -> false in
  let isfield = match Mid.find_opt ls.ls_name info.th_known_map with
    | Some { d_node = Ddata dl } -> not isconstr && List.exists is_field dl
    | _ -> false
  in
  let print = if isconstr then print_cs else print_ls in
  match tl with
  | [] ->
      print info fmt ls
  | [t1] when isfield ->
      fprintf fmt "(%a).%a" (print_term info) t1 (print info) ls
  | [t1] ->
      fprintf fmt (protect_on (pri > 4) "%a %a")
        (print info) ls (print_lterm 5 info) t1
  | tl when isconstr ->
      let pjl = get_record info ls in
      if pjl = [] then
        fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a@ (%a)@]")
          (print_cs info) ls (print_list comma (print_lterm 6 info)) tl
      else
        let print_field fmt (ls, t) =
          fprintf fmt "%a = %a" (print_ls info) ls (print_term info) t in
        fprintf fmt "@[<hov 1>{ %a }@]" (print_list semi print_field)
          (List.combine pjl tl)
  | tl ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a@ %a@]")
        (print_ls info) ls (print_list space (print_lterm 6 info)) tl

and print_tnode pri info fmt t = match t.t_node with
  | Tvar v ->
      let gh = try (restore_pv v).pv_vtv.vtv_ghost with Not_found -> false in
      if gh then fprintf fmt "()" else print_vs fmt v
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
      fprintf fmt (protect_on (pri > 4) "not %a") (print_lterm 5 info) f

and print_tbranch info fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" (print_pat info) p (print_term info) t;
  Svs.iter forget_var p.pat_vars

(* dead code
and print_tl info fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_term info))) tl
*)

let print_ls_type info fmt = function
  | None -> fprintf fmt "bool"
  | Some ty -> print_ty info fmt ty

let print_defn info fmt e =
  if is_exec_term e then print_term info fmt e
  else fprintf fmt "@[<hov>%a@ @[(* %a *)@]@]"
    to_be_implemented "not executable" Pretty.print_term e

let print_param_decl info fmt ls =
  if has_syntax info ls.ls_name then
    fprintf fmt "(* parameter %a is overridden by driver *)"
      (print_lident info) ls.ls_name
  else begin
    let vars = name_args ls.ls_args in
    fprintf fmt "@[<hov 2>let %a %a : %a =@ %a@]"
      (print_ls info) ls
      (print_list space (print_vs_arg info)) vars
      (print_ls_type info) ls.ls_value
      to_be_implemented "uninterpreted symbol";
    forget_vars vars;
    forget_tvs ()
  end

let print_logic_decl info isrec fst fmt (ls,ld) =
  if has_syntax info ls.ls_name then
    fprintf fmt "(* symbol %a is overridden by driver *)"
      (print_lident info) ls.ls_name
  else begin
    let vl,e = open_ls_defn ld in
    fprintf fmt "@[<hov 2>%s %a %a : %a =@ %a@]"
      (if fst then if isrec then "let rec" else "let" else "and")
      (print_ls info) ls
      (print_list space (print_vs_arg info)) vl
      (print_ls_type info) ls.ls_value (print_defn info) e;
    forget_vars vl;
    forget_tvs ()
  end

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
      print_type_decl info fmt ts;
      fprintf fmt "@\n@\n"
  | Ddata tl ->
      print_list_next newline (print_data_decl info) fmt tl;
      fprintf fmt "@\n@\n";
      print_list nothing (print_projections info) fmt tl
  | Decl.Dparam ls ->
      print_param_decl info fmt ls;
      fprintf fmt "@\n@\n"
  | Dlogic [ls,_ as ld] ->
      let isrec = Sid.mem ls.ls_name d.d_syms in
      print_logic_decl info isrec true fmt ld;
      fprintf fmt "@\n@\n"
  | Dlogic ll ->
      print_list_next newline (print_logic_decl info true) fmt ll;
      fprintf fmt "@\n@\n"
  | Dind (s, il) ->
      print_list_next newline (print_ind_decl info s) fmt il;
      fprintf fmt "@\n@\n"
  | Dprop (_pk, _pr, _) ->
      ()
      (* fprintf fmt "(* %a %a *)" Pretty.print_pkind pk Pretty.print_pr pr *)

let logic_decl info fmt td = match td.td_node with
  | Decl d ->
      let union = Sid.union d.d_syms d.d_news in
      let inter = Mid.set_inter union info.mo_known_map in
      if Sid.is_empty inter then logic_decl info fmt d
  | Use _ | Clone _ | Meta _ ->
      ()

(** Theories *)

let extract_theory drv ?old ?fname fmt th =
  ignore (old); ignore (fname);
  let sm = drv.Mlw_driver.drv_syntax in
  let info = {
    info_syn = sm;
    current_theory = th;
    th_known_map = th.th_known;
    mo_known_map = Mid.empty;
    fname = Opt.map clean_fname fname; } in
  fprintf fmt
    "(* This file has been generated from Why3 theory %a *)@\n@\n"
    print_theory_name th;
  print_list nothing (logic_decl info) fmt th.th_decls;
  fprintf fmt "@."

(** Programs *)

open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl
open Mlw_module

let print_its info fmt ts = print_ts info fmt ts.its_pure
let print_pv info fmt pv =
  if pv.pv_vtv.vtv_ghost then
    fprintf fmt "((* ghost %a *))" (print_lident info) pv.pv_vs.vs_name
  else
    print_lident info fmt pv.pv_vs.vs_name
let print_ps info fmt ps =
  if ps.ps_vta.vta_ghost then
    fprintf fmt "((* ghost %a *))" (print_lident info) ps.ps_name
  else
    print_lident info fmt ps.ps_name
let print_lv info fmt = function
  | LetV pv -> print_pv info fmt pv
  | LetA ps -> print_ps info fmt ps

let print_xs info fmt xs = print_uident info fmt xs.xs_name

let forget_ps ps = forget_id iprinter ps.ps_name
let forget_pv pv = forget_var pv.pv_vs
let forget_lv = function
  | LetV pv -> forget_pv pv
  | LetA ps -> forget_ps ps

let rec print_ity_node inn info fmt ity = match ity.ity_node with
  | Ityvar v ->
      print_tv fmt v
  | Itypur (ts, []) when is_ts_tuple ts ->
      fprintf fmt "unit"
  | Itypur (ts, tl) when is_ts_tuple ts ->
      fprintf fmt "(%a)" (print_list star (print_ity_node false info)) tl
  | Itypur (ts, tl) ->
      begin match query_syntax info.info_syn ts.ts_name with
        | Some s -> syntax_arguments s (print_ity_node true info) fmt tl
        | None -> begin match tl with
            | [] -> print_ts info fmt ts
            | [ity] -> fprintf fmt (protect_on inn "%a@ %a")
                  (print_ity_node true info) ity (print_ts info) ts
            | _ -> fprintf fmt (protect_on inn "(%a)@ %a")
              (print_list comma (print_ity_node false info)) tl
              (print_ts info) ts
        end
      end
  | Ityapp (ts, tl, _) ->
      begin match query_syntax info.info_syn ts.its_pure.ts_name with
        | Some s -> syntax_arguments s (print_ity_node true info) fmt tl
        | None -> begin match tl with
            | [] -> print_its info fmt ts
            | [ity] -> fprintf fmt (protect_on inn "%a@ %a")
                  (print_ity_node true info) ity (print_its info) ts
            | _ -> fprintf fmt (protect_on inn "(%a)@ %a")
              (print_list comma (print_ity_node false info)) tl
              (print_its info) ts
        end
      end

let print_ity info = print_ity_node false info

let print_vtv info fmt vtv = print_ity info fmt vtv.vtv_ity

let print_pvty info fmt pv =
  if pv.pv_vtv.vtv_ghost then fprintf fmt "((* ghost *))" else
  fprintf fmt "@[(%a:@ %a)@]"
    (print_lident info) pv.pv_vs.vs_name (print_vtv info) pv.pv_vtv

let rec print_vta info fmt vta =
  let print_arg fmt pv = print_vtv info fmt pv.pv_vtv in
  fprintf fmt "(%a -> %a)" (print_list arrow print_arg) vta.vta_args
    (print_vty info) vta.vta_result

and print_vty info fmt = function
  | VTvalue vtv -> print_vtv info fmt vtv
  | VTarrow vta -> print_vta info fmt vta

let is_letrec = function
  | [fd] -> Mid.mem fd.fun_ps.ps_name fd.fun_varm
  | _ -> true

let ity_mark = ity_pur Mlw_wp.ts_mark []

let rec print_expr info fmt e = print_lexpr 0 info fmt e

and print_lexpr pri info fmt e =
  if vty_ghost e.e_vty then
    fprintf fmt "((* ghost *))"
  else match e.e_node with
  | Elogic t ->
      fprintf fmt "(%a)" (print_term info) t
  | Evalue v ->
      print_pv info fmt v
  | Earrow a ->
      begin match query_syntax info.info_syn a.ps_name with
        | Some s -> syntax_arguments s (print_expr info) fmt []
        | None   -> print_ps info fmt a end
  | Eapp (e,v,_) ->
      fprintf fmt "(%a@ %a)" (print_lexpr pri info) e (print_pv info) v
  | Elet ({ let_expr = e1 }, e2) when vty_ghost e1.e_vty ->
      print_expr info fmt e2
  | Elet ({ let_sym = LetV pv }, e2)
    when ity_equal pv.pv_vtv.vtv_ity ity_mark ->
      print_expr info fmt e2
  | Elet ({ let_sym = LetV pv ; let_expr = e1 }, e2)
    when pv.pv_vs.vs_name.id_string = "_" &&
         ity_equal pv.pv_vtv.vtv_ity ity_unit ->
      fprintf fmt (protect_on (pri > 0) "@[begin %a;@ %a end@]")
        (print_expr info) e1 (print_expr info) e2;
  | Elet ({ let_sym = lv ; let_expr = e1 }, e2) ->
      fprintf fmt (protect_on (pri > 0) "@[<hov 2>let %a =@ %a@ in@]@\n%a")
        (print_lv info) lv (print_lexpr 4 info) e1 (print_expr info) e2;
      forget_lv lv
  | Eif (e0,e1,e2) ->
      fprintf fmt (protect_on (pri > 0)
                     "@[<hv>if %a@ @[<hov 2>then %a@]@ @[<hov 2>else %a@]@]")
        (print_expr info) e0 (print_expr info) e1 (print_expr info) e2
  | Eassign (e,_,pv) ->
      fprintf fmt (protect_on (pri > 0) "%a <- %a")
        (print_expr info) e (print_pv info) pv
  | Eloop (_,_,e) ->
      fprintf fmt "@[while true do@ %a@ done@]" (print_expr info) e
  | Efor (pv,(pvfrom,dir,pvto),_,e) ->
      fprintf fmt
        "@[<hov 2>(Int__Int.for_loop_%s %a %a@ (fun %a -> %a))@]"
        (if dir = To then "to" else "downto")
        (print_pv info) pvfrom (print_pv info) pvto
        (print_pv info) pv (print_expr info) e
  | Eraise (xs,e) ->
      begin match query_syntax info.info_syn xs.xs_name with
        | Some s -> syntax_arguments s (print_expr info) fmt [e]
        | None when ity_equal xs.xs_ity ity_unit ->
            fprintf fmt "raise %a" (print_xs info) xs
        | None ->
            fprintf fmt "raise (%a %a)" (print_xs info) xs (print_expr info) e
      end
  | Etry (e,bl) ->
      fprintf fmt "@[(try %a with@\n@[<hov>%a@])@]"
        (print_expr info) e (print_list newline (print_xbranch info)) bl
  | Eabstr (e,_) ->
      print_lexpr pri info fmt e
  | Eabsurd ->
      fprintf fmt "assert false (* absurd *)"
  | Eassert _ ->
      fprintf fmt "((* assert *))"
  | Eghost _ ->
      assert false
  | Eany _ ->
      fprintf fmt "@[(%a :@ %a)@]" to_be_implemented "any"
        (print_vty info) e.e_vty
  | Ecase (e1, bl) ->
      fprintf fmt "@[(match @[%a@] with@\n@[<hov>%a@])@]"
        (print_expr info) e1 (print_list newline (print_ebranch info)) bl
  | Erec (fdl, e) ->
      (* print non-ghost first *)
      let cmp {fun_ps=ps1} {fun_ps=ps2} =
        Pervasives.compare ps1.ps_vta.vta_ghost ps2.ps_vta.vta_ghost in
      let fdl = List.sort cmp fdl in
      fprintf fmt "@[<v>%a@\nin@\n%a@]"
        (print_list_next newline (print_rec_decl (is_letrec fdl) info)) fdl
        (print_expr info) e

and print_rec lr info fst fmt { fun_ps = ps ; fun_lambda = lam } =
  if ps.ps_vta.vta_ghost then
    fprintf fmt "(* %s %a *)"
      (if fst then if lr then "let rec" else "let" else "with")
      (print_ps info) ps
  else
    let print_arg fmt pv = fprintf fmt "@[%a@]" (print_pvty info) pv in
    fprintf fmt "@[<hov 2>%s %a %a =@ %a@]"
      (if fst then if lr then "let rec" else "let" else "and")
      (print_ps info) ps (print_list space print_arg) lam.l_args
      (print_expr info) lam.l_expr

and print_ebranch info fmt ({ppat_pattern=p}, e) =
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" (print_pat info) p (print_expr info) e;
  Svs.iter forget_var p.pat_vars

and print_xbranch info fmt (xs, pv, e) =
  begin match query_syntax info.info_syn xs.xs_name with
    | Some s -> syntax_arguments s (print_pv info) fmt [pv]
    | None when ity_equal xs.xs_ity ity_unit ->
        fprintf fmt "@[<hov 4>| %a ->@ %a@]"
          (print_xs info) xs (print_expr info) e
    | None ->
        fprintf fmt "@[<hov 4>| %a %a ->@ %a@]"
          (print_xs info) xs (print_pv info) pv (print_expr info) e
  end;
  forget_pv pv

and print_rec_decl lr info fst fmt fd =
  print_rec lr info fst fmt fd;
  forget_tvs ()

let print_rec_decl lr info fst fmt fd =
  let id = fd.fun_ps.ps_name in
  if has_syntax info id then
    fprintf fmt "(* symbol %a is overridden by driver *)" (print_lident info) id
  else
    print_rec_decl lr info fst fmt fd

let print_let_decl info fmt { let_sym = lv ; let_expr = e } =
  fprintf fmt "@[<hov 2>let %a =@ %a@]" (print_lv info) lv (print_expr info) e;
  forget_tvs ()

let lv_name = function
  | LetV pv -> pv.pv_vs.vs_name
  | LetA ps -> ps.ps_name

let is_ghost_lv = function
  | LetV pv -> pv.pv_vtv.vtv_ghost
  | LetA ps -> ps.ps_vta.vta_ghost

let print_let_decl info fmt ld =
  if is_ghost_lv ld.let_sym then
    fprintf fmt "(* let %a *)@\n@\n" (print_lv info) ld.let_sym
  else
    fprintf fmt "%a@\n@\n" (print_let_decl info) ld

let print_let_decl info fmt ld =
  let id = lv_name ld.let_sym in
  if has_syntax info id then
    fprintf fmt "(* symbol %a is overridden by driver *)" (print_lident info) id
  else
    print_let_decl info fmt ld

let rec extract_vta_args args vta =
  let new_args = List.map (fun pv -> pv.pv_vs) vta.vta_args in
  let args = List.rev_append new_args args in
  match vta.vta_result with
  | VTvalue vtv -> List.rev args, vtv
  | VTarrow vta -> extract_vta_args args vta

let extract_lv_args = function
  | LetV pv -> [], pv.pv_vtv
  | LetA ps -> extract_vta_args [] ps.ps_vta

let print_val_decl info fmt lv =
  let vars, vtv = extract_lv_args lv in
  fprintf fmt "@[<hov 2>let %a %a : %a =@ %a@]"
    (print_lv info) lv
    (print_list space (print_vs_arg info)) vars
    (print_vtv info) vtv
    to_be_implemented "val";
  forget_vars vars;
  forget_tvs ()

let print_val_decl info fmt lv =
  if is_ghost_lv lv then
    fprintf fmt "(* val %a *)@\n@\n" (print_lv info) lv
  else
    fprintf fmt "%a@\n@\n" (print_val_decl info) lv

let print_val_decl info fmt lv =
  let id = lv_name lv in
  if has_syntax info id then
    fprintf fmt "(* symbol %a is overridden by driver *)" (print_lident info) id
  else
    print_val_decl info fmt lv

let print_type_decl info fmt its = match its.its_def with
  | None ->
      fprintf fmt
        "@[<hov 2>type %a%a (* to be defined (uninterpreted type) *)@]@\n@\n"
        print_tv_args its.its_args (print_its info) its
  | Some ty ->
      fprintf fmt "@[<hov 2>type %a%a =@ %a@]@\n@\n"
        print_tv_args its.its_args (print_its info) its (print_ity info) ty

let print_type_decl info fmt its =
  if has_syntax info its.its_pure.ts_name then
    fprintf fmt "(* type %a is overridden by driver *)"
      (print_lident info) its.its_pure.ts_name
  else begin print_type_decl info fmt its; forget_tvs () end

let print_exn_decl info fmt xs =
  if ity_equal xs.xs_ity ity_unit then
    fprintf fmt "exception %a@\n@\n" (print_xs info) xs
  else
    fprintf fmt "exception %a of %a@\n@\n" (print_uident info) xs.xs_name
      (print_ity info) xs.xs_ity

let print_exn_decl info fmt xs =
  if has_syntax info xs.xs_name then
    fprintf fmt "(* symbol %a is overridden by driver *)"
      (print_lident info) xs.xs_name
  else
    print_exn_decl info fmt xs

let print_pconstr info fmt (cs,_) = match cs.pl_args with
  | [] ->
      fprintf fmt "@[<hov 4>| %a@]" (print_cs info) cs.pl_ls
  | tl ->
      let print_vtv fmt vtv =
        if vtv.vtv_ghost then fprintf fmt "unit" else print_vtv info fmt vtv in
      fprintf fmt "@[<hov 4>| %a of %a@]" (print_cs info) cs.pl_ls
        (print_list star print_vtv) tl

let print_pdata_decl info fst fmt (its, csl, _) =
  let print_default () = print_list newline (print_pconstr info) fmt csl in
  let print_field fmt (ls, vtv) =
    fprintf fmt "%s%a: "
      (if vtv.vtv_mut <> None then "mutable " else "") (print_ls info) ls;
    if vtv.vtv_ghost then fprintf fmt "unit" else print_vtv info fmt vtv in
  let print_defn fmt = function
    | [cs, _] ->
        let pjl = get_record info cs.pl_ls in
        if pjl = [] then print_default ()
        else fprintf fmt "{ %a }" (print_list semi print_field)
          (List.combine pjl cs.pl_args)
    | _ ->
        print_default ()
  in
  fprintf fmt "@[<hov 2>%s %a%a =@\n@[<hov>%a@]@]"
    (if fst then "type" else "and")
    print_tv_args its.its_args (print_its info) its print_defn csl

let print_pdata_decl info first fmt (its, _, _ as d) =
  if has_syntax info its.its_pure.ts_name then
    fprintf fmt "(* type %a is overridden by driver *)"
      (print_lident info) its.its_pure.ts_name
  else begin print_pdata_decl info first fmt d; forget_tvs () end

let is_record = function
  | _, [_, pjl], _ -> List.for_all ((<>) None) pjl
  | _ -> false

let print_pprojections info fmt (_, csl, _) =
  let pjl = List.filter ((<>) None) (snd (List.hd csl)) in
  let pjl = List.map Opt.get pjl in
  let print ls =
    let print_branch fmt (cs, pjl) =
      let print_arg fmt = function
        | Some ls' when pl_equal ls' ls -> fprintf fmt "x"
        | _ -> fprintf fmt "_" in
      fprintf fmt "| %a (%a) -> x"
        (print_cs info) cs.pl_ls (print_list comma print_arg) pjl
    in
    fprintf fmt "@[<hov 2>let %a = function@\n" (print_ls info) ls.pl_ls;
    print_list newline print_branch fmt csl;
    fprintf fmt "@]@\n@\n"
  in
  List.iter print pjl

let print_pprojections info fmt (ts, _, _ as d) =
  if not (has_syntax info ts.its_pure.ts_name) && not (is_record d) then begin
    print_pprojections info fmt d; forget_tvs ()
  end

let pdecl info fmt pd = match pd.pd_node with
  | PDtype ts ->
      print_type_decl info fmt ts;
      fprintf fmt "@\n@\n"
  | PDdata tl ->
      print_list_next newline (print_pdata_decl info) fmt tl;
      fprintf fmt "@\n@\n";
      print_list nothing (print_pprojections info) fmt tl
  | PDval lv ->
      print_val_decl info fmt lv;
      fprintf fmt "@\n@\n"
  | PDlet ld ->
      print_let_decl info fmt ld
  | PDrec fdl ->
      (* print defined, non-ghost first *)
      let cmp {fun_ps=ps1} {fun_ps=ps2} =
        Pervasives.compare
          (ps1.ps_vta.vta_ghost || has_syntax info ps1.ps_name)
          (ps2.ps_vta.vta_ghost || has_syntax info ps2.ps_name) in
      let fdl = List.sort cmp fdl in
      print_list_next newline (print_rec_decl (is_letrec fdl) info) fmt fdl;
      fprintf fmt "@\n@\n"
  | PDexn xs ->
      print_exn_decl info fmt xs

(** Modules *)

let extract_module drv ?old ?fname fmt m =
  ignore (old); ignore (fname);
  let sm = drv.Mlw_driver.drv_syntax in
  let th = m.mod_theory in
  let info = {
    info_syn = sm;
    current_theory = th;
    th_known_map = th.th_known;
    mo_known_map = m.mod_known;
    fname = Opt.map clean_fname fname; } in
  fprintf fmt
    "(* This file has been generated from Why3 module %a *)@\n@\n"
    print_module_name m;
  print_list nothing (logic_decl info) fmt th.th_decls;
  print_list nothing (pdecl info) fmt m.mod_decls;
  fprintf fmt "@."


(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
