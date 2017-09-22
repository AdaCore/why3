(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Why3 printer *)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Printer
open Theory

let iprinter,aprinter,tprinter,pprinter =
  let bl = ["theory"; "type"; "function"; "predicate"; "inductive";
            "axiom"; "lemma"; "goal"; "use"; "clone"; "prop"; "meta";
            "namespace"; "import"; "export"; "end";
            "forall"; "exists"; "not"; "true"; "false"; "if"; "then"; "else";
            "let"; "in"; "match"; "with"; "as"; "epsilon" ] in
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:isanitize

let forget_tvs () =
  forget_all aprinter

let _forget_all () =
  forget_all iprinter;
  forget_all aprinter;
  forget_all tprinter;
  forget_all pprinter

(* type variables always start with a quote *)
let print_tv fmt tv =
  fprintf fmt "'%s" (id_unique aprinter tv.tv_name)

(* logic variables always start with a lower case letter *)
let print_vs fmt vs =
  let sanitizer = Strings.uncapitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer vs.vs_name)

let forget_var vs = forget_id iprinter vs.vs_name

(* theory names always start with an upper case letter *)
let print_th fmt th =
  let sanitizer = Strings.capitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer th.th_name)

let print_ts fmt ts =
  fprintf fmt "%s" (id_unique tprinter ts.ts_name)

let print_ls fmt ls =
  fprintf fmt "%s" (id_unique iprinter ls.ls_name)

let print_cs fmt ls =
  let sanitizer = Strings.capitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer ls.ls_name)

let print_pr fmt pr =
  fprintf fmt "%s" (id_unique pprinter pr.pr_name)

(* info *)

type info = { info_syn : syntax_map }

let info = ref { info_syn = Mid.empty }

let query_syntax id = query_syntax !info.info_syn id
let query_remove id = Mid.mem id !info.info_syn

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_ty_node inn fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, tl) -> begin match query_syntax ts.ts_name with
      | Some s -> syntax_arguments s (print_ty_node false) fmt tl
      | None -> begin match tl with
          | [] -> print_ts fmt ts
          | tl -> fprintf fmt (protect_on inn "%a@ %a")
              print_ts ts (print_list space (print_ty_node true)) tl
          end
      end

let print_ty = print_ty_node false

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

let rec print_pat_node pri fmt p = match p.pat_node with
  | Pwild ->
      fprintf fmt "_"
  | Pvar v ->
      print_vs fmt v
  | Pas (p, v) ->
      fprintf fmt (protect_on (pri > 1) "%a as %a")
        (print_pat_node 1) p print_vs v
  | Por (p, q) ->
      fprintf fmt (protect_on (pri > 0) "%a | %a")
        (print_pat_node 0) p (print_pat_node 0) q
  | Papp (cs, pl) -> begin match query_syntax cs.ls_name with
      | Some s -> syntax_arguments s (print_pat_node 0) fmt pl
      | None -> begin match pl with
          | [] -> print_cs fmt cs
          | pl -> fprintf fmt (protect_on (pri > 1) "%a@ %a")
              print_cs cs (print_list space (print_pat_node 2)) pl
          end
      end

let print_pat = print_pat_node 0

let print_vsty fmt v =
  fprintf fmt "%a:@,%a" print_vs v print_ty v.vs_ty

let print_quant = Pretty.print_quant
let print_binop = Pretty.print_binop

let prio_binop = function
  | Tand -> 3
  | Tor -> 2
  | Timplies -> 1
  | Tiff -> 1

let print_label = Pretty.print_label
let print_labels = print_iter1 Slab.iter space print_label

let print_ident_labels fmt id =
  if not (Slab.is_empty id.id_label) then
    fprintf fmt "@ %a" print_labels id.id_label

let rec print_term fmt t = print_lterm 0 fmt t

and print_lterm pri fmt t =
  if Slab.is_empty t.t_label then print_tnode pri fmt t
  else fprintf fmt (protect_on (pri > 0) "%a %a")
      print_labels t.t_label (print_tnode 0) t

and print_app pri fs fmt tl =
  match query_syntax fs.ls_name with
    | Some s -> syntax_arguments s print_term fmt tl
    | None -> begin match tl with
        | [] -> print_ls fmt fs
        | tl -> fprintf fmt (protect_on (pri > 5) "%a@ %a")
            print_ls fs (print_list space (print_lterm 6)) tl
        end

and print_tnode pri fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      Number.print_constant fmt c
  | Tapp (fs, tl) when unambig_fs fs ->
      print_app pri fs fmt tl
  | Tapp (fs, tl) ->
      fprintf fmt (protect_on (pri > 0) "%a:%a")
        (print_app 5 fs) tl print_ty (t_type t)
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on (pri > 0) "if @[%a@] then %a@ else %a")
        print_term f print_term t1 print_term t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on (pri > 0) "let %a = @[%a@] in@ %a")
        print_vs v (print_lterm 4) t1 print_term t2;
      forget_var v
  | Tcase (t1,bl) ->
      fprintf fmt "match @[%a@] with@\n@[<hov>%a@]@\nend"
        print_term t1 (print_list newline print_tbranch) bl
  | Teps fb ->
      let vl,tl,e = t_open_lambda t in
      if vl = [] then begin
        let v,f = t_open_bound fb in
        fprintf fmt (protect_on (pri > 0) "epsilon %a.@ %a")
          print_vsty v print_term f;
        forget_var v
      end else begin
        fprintf fmt (protect_on (pri > 0) "\\ %a%a.@ %a")
          (print_list comma print_vsty) vl print_tl tl print_term e;
        List.iter forget_var vl
      end
  | Tquant (q,fq) ->
      let vl,tl,f = t_open_quant fq in
      fprintf fmt (protect_on (pri > 0) "%a %a%a.@ %a") print_quant q
        (print_list comma print_vsty) vl print_tl tl print_term f;
      List.iter forget_var vl
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tbinop (b,f1,f2) ->
      let asym = Slab.mem Term.asym_label f1.t_label in
      let p = prio_binop b in
      fprintf fmt (protect_on (pri > p) "%a %a@ %a")
        (print_lterm (p + 1)) f1 (print_binop ~asym) b (print_lterm p) f2
  | Tnot f ->
      fprintf fmt (protect_on (pri > 4) "not %a") (print_lterm 4) f

and print_tbranch fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_term t;
  Svs.iter forget_var p.pat_vars

and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_term)) tl

(** Declarations *)

let print_tv_arg fmt tv = fprintf fmt "@ %a" print_tv tv
let print_ty_arg fmt ty = fprintf fmt "@ %a" (print_ty_node true) ty
let print_vs_arg fmt vs = fprintf fmt "@ (%a)" print_vsty vs

let print_constr fmt (cs,pjl) =
  let add_pj pj ty pjl = (pj,ty)::pjl in
  let print_pj fmt (pj,ty) = match pj with
    | Some ls -> fprintf fmt "@ (%a:@,%a)" print_ls ls print_ty ty
    | None -> print_ty_arg fmt ty
  in
  fprintf fmt "@[<hov 4>| %a%a%a@]" print_cs cs
    print_ident_labels cs.ls_name
    (print_list nothing print_pj)
    (List.fold_right2 add_pj pjl cs.ls_args [])

let print_type_decl fmt ts = match ts.ts_def with
  | NoDef ->
      fprintf fmt "@[<hov 2>type %a%a%a@]@\n@\n"
        print_ts ts print_ident_labels ts.ts_name
        (print_list nothing print_tv_arg) ts.ts_args
  | Alias ty ->
      fprintf fmt "@[<hov 2>type %a%a%a =@ %a@]@\n@\n"
        print_ts ts print_ident_labels ts.ts_name
        (print_list nothing print_tv_arg) ts.ts_args print_ty ty
  | Range _ir -> (* TODO *)
      fprintf fmt "@[<hov 2>type %a%a%a =@ <range ...>@]@\n@\n"
        print_ts ts print_ident_labels ts.ts_name
        (print_list nothing print_tv_arg) ts.ts_args
  | Float _fp -> (* TODO *)
      fprintf fmt "@[<hov 2>type %a%a%a =@ <float ...>@]@\n@\n"
        print_ts ts print_ident_labels ts.ts_name
        (print_list nothing print_tv_arg) ts.ts_args

let print_type_decl fmt ts =
  if not (query_remove ts.ts_name) then
    (print_type_decl fmt ts; forget_tvs ())

let print_data_decl fst fmt (ts,csl) =
  fprintf fmt "@[<hov 2>%s %a%a%a =@\n@[<hov>%a@]@]@\n@\n"
    (if fst then "type" else "with") print_ts ts
    print_ident_labels ts.ts_name
    (print_list nothing print_tv_arg) ts.ts_args
    (print_list newline print_constr) csl

let print_data_decl first fmt d =
  if not (query_remove (fst d).ts_name) then
    (print_data_decl first fmt d; forget_tvs ())

let print_ls_type fmt = fprintf fmt " :@ %a" print_ty

let ls_kind ls = if ls.ls_value = None then "predicate" else "function"

let print_param_decl fmt ls =
  fprintf fmt "@[<hov 2>%s %a%a%a%a@]@\n@\n"
    (ls_kind ls) print_ls ls
    print_ident_labels ls.ls_name
    (print_list nothing print_ty_arg) ls.ls_args
    (print_option print_ls_type) ls.ls_value

let print_param_decl fmt ls =
  if not (query_remove ls.ls_name) then
    (print_param_decl fmt ls; forget_tvs ())

let print_logic_decl fst fmt (ls,ld) =
  let vl,e = open_ls_defn ld in
  fprintf fmt "@[<hov 2>%s %a%a%a%a =@ %a@]@\n@\n"
    (if fst then ls_kind ls else "with") print_ls ls
    print_ident_labels ls.ls_name
    (print_list nothing print_vs_arg) vl
    (print_option print_ls_type) ls.ls_value print_term e;
  List.iter forget_var vl

let print_logic_decl first fmt d =
  if not (query_remove (fst d).ls_name) then
    (print_logic_decl first fmt d; forget_tvs ())

let print_ind fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a%a :@ %a@]"
    print_pr pr print_ident_labels pr.pr_name print_term f

let ind_sign = function
  | Ind   -> "inductive"
  | Coind -> "coinductive"

let print_ind_decl s fst fmt (ps,bl) =
  fprintf fmt "@[<hov 2>%s %a%a%a =@ @[<hov>%a@]@]@\n@\n"
    (if fst then ind_sign s else "with") print_ls ps
    print_ident_labels ps.ls_name
    (print_list nothing print_ty_arg) ps.ls_args
    (print_list newline print_ind) bl

let print_ind_decl s first fmt d =
  if not (query_remove (fst d).ls_name) then
    (print_ind_decl s first fmt d; forget_tvs ())

let print_pkind = Pretty.print_pkind

let print_prop_decl fmt (k,pr,f) =
  fprintf fmt "@[<hov 2>%a %a%a : %a@]@\n@\n" print_pkind k
    print_pr pr print_ident_labels pr.pr_name print_term f

let print_prop_decl fmt (k,pr,f) = match k with
  | Paxiom when query_remove pr.pr_name -> ()
  | _ -> print_prop_decl fmt (k,pr,f); forget_tvs ()

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r -> print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let print_decl fmt d = match d.d_node with
  | Dtype ts  -> print_type_decl fmt ts
  | Ddata tl  -> print_list_next nothing print_data_decl fmt tl
  | Dparam ls -> print_param_decl fmt ls
  | Dlogic ll -> print_list_next nothing print_logic_decl fmt ll
  | Dind (s, il) -> print_list_next nothing (print_ind_decl s) fmt il
  | Dprop p   -> print_prop_decl fmt p

let print_inst_ts fmt (ts1,ts2) =
  fprintf fmt "type %a = %a" print_ts ts1 print_ts ts2

let print_inst_ls fmt (ls1,ls2) =
  fprintf fmt "%s %a = %a" (ls_kind ls1) print_ls ls1 print_ls ls2

let print_inst_pr fmt (pr1,pr2) =
  fprintf fmt "prop %a = %a" print_pr pr1 print_pr pr2

let print_meta_arg fmt = function
  | MAty ty -> fprintf fmt "type %a" print_ty ty; forget_tvs ()
  | MAts ts -> fprintf fmt "type %a" print_ts ts
  | MAls ls -> fprintf fmt "%s %a" (ls_kind ls) print_ls ls
  | MApr pr -> fprintf fmt "prop %a" print_pr pr
  | MAstr s -> fprintf fmt "\"%s\"" s
  | MAint i -> fprintf fmt "%d" i

let print_qt fmt th =
  if th.th_path = [] then print_th fmt th else
  fprintf fmt "%a.%a"
    (print_list (constant_string ".") string) th.th_path
    print_th th

let print_tdecl fmt td = match td.td_node with
  | Decl d ->
      print_decl fmt d
  | Use th ->
      fprintf fmt "@[<hov 2>(* use %a *)@]@\n@\n" print_qt th
  | Clone (th,sm) when is_empty_sm sm ->
      fprintf fmt "@[<hov 2>(* use %a *)@]@\n@\n" print_qt th
  | Clone (th,sm) ->
      let tm = Mts.fold (fun x y a -> (x,y)::a) sm.sm_ts [] in
      let lm = Mls.fold (fun x y a -> (x,y)::a) sm.sm_ls [] in
      let pm = Mpr.fold (fun x y a -> (x,y)::a) sm.sm_pr [] in
      fprintf fmt "@[<hov 2>(* clone %a with %a,@ %a,@ %a *)@]@\n@\n"
        print_qt th (print_list comma print_inst_ts) tm
                    (print_list comma print_inst_ls) lm
                    (print_list comma print_inst_pr) pm
  | Meta (m,al) ->
      fprintf fmt "@[<hov 2>(* meta %s %a *)@]@\n@\n"
        m.meta_name (print_list comma print_meta_arg) al

let print_tdecls =
  let print_tdecl sm fmt td =
    info := {info_syn = sm}; print_tdecl fmt td; sm, [] in
  let print_tdecl = Printer.sprint_tdecl print_tdecl in
  let print_tdecl task acc = print_tdecl task.Task.task_decl acc in
  Discriminate.on_syntax_map (fun sm -> Trans.fold print_tdecl (sm,[]))

let print_task args ?old:_ fmt task =
  (* In trans-based p-printing [forget_all] IST STRENG VERBOTEN *)
  (* forget_all (); *)
  print_prelude fmt args.prelude;
  fprintf fmt "theory Task@\n";
  print_th_prelude task fmt args.th_prelude;
  let rec print = function
    | x :: r -> print r; Pp.string fmt x
    | [] -> () in
  print (snd (Trans.apply print_tdecls task));
  fprintf fmt "end@."

let () = register_printer "why3" print_task
  ~desc:"Printer@ for@ the@ logical@ format@ of@ Why3.@ Used@ for@ debugging."
