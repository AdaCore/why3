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

open Format
open Pp
open Stdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Task

let why3_keywords =
  ["theory"; "type"; "constant"; "function"; "predicate"; "inductive";
   "axiom"; "lemma"; "goal"; "use"; "clone"; "prop"; "meta";
   "namespace"; "import"; "export"; "end";
   "forall"; "exists"; "not"; "true"; "false"; "if"; "then"; "else";
   "let"; "in"; "match"; "with"; "as"; "epsilon" ]

let debug_print_labels =
  Debug.register_info_flag
    "print_labels"
    ~desc:"Print@ labels@ of@ identifiers@ and@ expressions."

let debug_print_locs = Debug.register_info_flag "print_locs"
  ~desc:"Print@ locations@ of@ identifiers@ and@ expressions."



let create iprinter aprinter tprinter pprinter do_forget_all =
  (module (struct

let forget_tvs () =
  (* we always forget type variables between each declaration *)
  (* if do_forget_all then *) forget_all aprinter

let forget_all () =
  if do_forget_all then forget_all iprinter;
  if do_forget_all then forget_all aprinter;
  if do_forget_all then forget_all tprinter;
  if do_forget_all then forget_all pprinter

let print_label fmt l = fprintf fmt "\"%s\"" l.lab_string
let print_labels = print_iter1 Slab.iter space print_label

let print_loc fmt l =
  let (f,l,b,e) = Loc.get l in
  fprintf fmt "#\"%s\" %d %d %d#" f l b e

let print_id_labels fmt id =
  if Debug.test_flag debug_print_labels &&
      not (Slab.is_empty id.id_label) then
    fprintf fmt "@ %a" print_labels id.id_label;
  if Debug.test_flag debug_print_locs then
    Opt.iter (fprintf fmt "@ %a" print_loc) id.id_loc

(* type variables always start with a quote *)
let print_tv fmt tv =
  fprintf fmt "'%s" (id_unique aprinter tv.tv_name)

(* logic variables always start with a lower case letter *)
let print_vs fmt vs =
  let sanitizer = Strings.uncapitalize in
  pp_print_string fmt (id_unique iprinter ~sanitizer vs.vs_name)

let forget_var vs = forget_id iprinter vs.vs_name

(* pretty-print infix and prefix logic symbols *)

let extract_op ls =
  let s = ls.ls_name.id_string in
  let len = String.length s in
  if len < 7 then None else
  let inf = String.sub s 0 6 in
  if inf = "infix "  then Some (String.sub s 6 (len - 6)) else
  let prf = String.sub s 0 7 in
  if prf = "prefix " then Some (String.sub s 7 (len - 7)) else
  None

let tight_op s = let c = String.sub s 0 1 in c = "!" || c = "?"

let escape_op s =
  let len = String.length s in
  if len = 0 then s else
    let s = if String.get s (len - 1) = '*' then s ^ " " else s in
    let s = if String.get s 0 = '*' then " " ^ s else s in
   s

(* theory names always start with an upper case letter *)
let print_th fmt th =
  let sanitizer = Strings.capitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer th.th_name)

let print_ts fmt ts =
  fprintf fmt "%s" (id_unique tprinter ts.ts_name)

let print_ls fmt ls =
  if ls.ls_name.id_string = "mixfix []" then fprintf fmt "([])" else
  if ls.ls_name.id_string = "mixfix [<-]" then fprintf fmt "([<-])" else
  match extract_op ls with
  | Some s -> fprintf fmt "(%s)" (escape_op s)
  | None   -> fprintf fmt "%s" (id_unique iprinter ls.ls_name)

let print_cs fmt ls =
  let sanitizer = Strings.capitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer ls.ls_name)

let print_pr fmt pr =
  fprintf fmt "%s" (id_unique pprinter pr.pr_name)

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_ty_node pri fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, [t1;t2]) when ts_equal ts Ty.ts_func ->
      fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_ty_node 1) t1 (print_ty_node 0) t2
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      fprintf fmt "(%a)" (print_list comma (print_ty_node 0)) tl
  | Tyapp (ts, []) -> print_ts fmt ts
  | Tyapp (ts, tl) -> fprintf fmt (protect_on (pri > 1) "%a@ %a")
      print_ts ts (print_list space (print_ty_node 2)) tl

let print_ty fmt ty = print_ty_node 0 fmt ty

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
      print_vs fmt v; print_id_labels fmt v.vs_name
  | Pas (p, v) ->
      fprintf fmt (protect_on (pri > 1) "%a as %a%a")
        (print_pat_node 1) p print_vs v print_id_labels v.vs_name
  | Por (p, q) ->
      fprintf fmt (protect_on (pri > 0) "%a | %a")
        (print_pat_node 0) p (print_pat_node 0) q
  | Papp (cs, pl) when is_fs_tuple cs ->
      fprintf fmt (protect_on (pri > 0) "%a")
        (print_list comma (print_pat_node 1)) pl
  | Papp (cs, []) ->
      print_cs fmt cs
  | Papp (cs, pl) ->
      fprintf fmt (protect_on (pri > 1) "%a@ %a")
        print_cs cs (print_list space (print_pat_node 2)) pl

let print_pat = print_pat_node 0

let print_vsty fmt v =
  fprintf fmt "%a%a:@,%a" print_vs v
    print_id_labels v.vs_name print_ty v.vs_ty

let print_quant fmt = function
  | Tforall -> fprintf fmt "forall"
  | Texists -> fprintf fmt "exists"

let print_binop ~asym fmt = function
  | Tand when asym -> fprintf fmt "&&"
  | Tor when asym -> fprintf fmt "||"
  | Tand -> fprintf fmt "/\\"
  | Tor -> fprintf fmt "\\/"
  | Timplies -> fprintf fmt "->"
  | Tiff -> fprintf fmt "<->"

let prio_binop = function
  | Tand -> 4
  | Tor -> 3
  | Timplies -> 1
  | Tiff -> 1


let rec print_term fmt t = print_lterm 0 fmt t

and print_lterm pri fmt t =
  let print_tlab pri fmt t =
    if Debug.test_flag debug_print_labels && not (Slab.is_empty t.t_label)
    then fprintf fmt (protect_on (pri > 0) "@[<hov 0>%a@ %a@]")
      print_labels t.t_label (print_tnode 0) t
    else print_tnode pri fmt t in
  let print_tloc pri fmt t =
    if Debug.test_flag debug_print_locs && t.t_loc <> None
    then fprintf fmt (protect_on (pri > 0) "@[<hov 0>%a@ %a@]")
      (print_option print_loc) t.t_loc (print_tlab 0) t
    else print_tlab pri fmt t in
  print_tloc pri fmt t

and print_app pri ls fmt tl = match extract_op ls, tl with
  | _, [] ->
      print_ls fmt ls
  | Some s, [t1] when tight_op s ->
      fprintf fmt (protect_on (pri > 8) "@[%s%a@]")
        s (print_lterm 8) t1
  | Some s, [t1] ->
      fprintf fmt (protect_on (pri > 5) "@[%s %a@]")
        s (print_lterm 6) t1
  | Some s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 5) "@[%a@ %s %a@]")
        (print_lterm 6) t1 s (print_lterm 6) t2
  | _, [t1;t2] when ls.ls_name.id_string = "mixfix []" ->
      fprintf fmt (protect_on (pri > 7) "@[%a@,[%a]@]")
        (print_lterm 7) t1 print_term t2
  | _, [t1;t2;t3] when ls.ls_name.id_string = "mixfix [<-]" ->
      fprintf fmt (protect_on (pri > 7) "@[%a@,[%a <-@ %a]@]")
        (print_lterm 7) t1 (print_lterm 6) t2 (print_lterm 6) t3
  | _, tl ->
      fprintf fmt (protect_on (pri > 6) "@[%a@ %a@]")
        print_ls ls (print_list space (print_lterm 7)) tl

and print_tnode pri fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      Number.print_constant fmt c
  | Tapp (fs, tl) when is_fs_tuple fs ->
      fprintf fmt "(%a)" (print_list comma print_term) tl
  | Tapp (fs, tl) when unambig_fs fs ->
      print_app pri fs fmt tl
  | Tapp (fs, tl) ->
      fprintf fmt (protect_on (pri > 0) "@[%a:@ %a@]")
        (print_app 5 fs) tl print_ty (t_type t)
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on (pri > 0) "@[if %a@ then %a@ else %a@]")
        print_term f print_term t1 print_term t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on (pri > 0)
                              "@[@[<hv 0>let %a%a =@;<1 2>%a@;<1 0>in@]@ %a@]")
        print_vs v print_id_labels v.vs_name (print_lterm 5) t1 print_term t2;
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
        fprintf fmt (protect_on (pri > 0) "@[<hov 1>\\ %a%a.@ %a@]")
          (print_list comma print_vsty) vl print_tl tl print_term e;
        List.iter forget_var vl
      end
  | Tquant (q,fq) ->
      let vl,tl,f = t_open_quant fq in
      fprintf fmt (protect_on (pri > 0) "@[<hov 1>%a %a%a.@ %a@]") print_quant q
        (print_list comma print_vsty) vl print_tl tl print_term f;
      List.iter forget_var vl
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tbinop (Tand,f1,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) })
    when Slab.mem Term.asym_label f2.t_label ->
      fprintf fmt (protect_on (pri > 2) "@[<hov 1>%a so@ %a@]")
        (print_lterm 3) f1 (print_lterm 2) f2
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) },f1)
    when Slab.mem Term.asym_label f2.t_label ->
      fprintf fmt (protect_on (pri > 2) "@[<hov 1>%a by@ %a@]")
        (print_lterm 3) f1 (print_lterm 2) f2
  | Tbinop (b,f1,f2) ->
      let asym = Slab.mem Term.asym_label f1.t_label in
      let p = prio_binop b in
      fprintf fmt (protect_on (pri > p) "@[%a %a@ %a@]")
        (print_lterm (p + 1)) f1 (print_binop ~asym) b (print_lterm p) f2
  | Tnot f ->
      fprintf fmt (protect_on (pri > 5) "not %a") (print_lterm 5) f

and print_tbranch fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_term t;
  Svs.iter forget_var p.pat_vars

and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_term)) tl

(** Declarations *)

let print_tv_arg fmt tv = fprintf fmt "@ %a" print_tv tv
let print_ty_arg fmt ty = fprintf fmt "@ %a" (print_ty_node 2) ty
let print_vs_arg fmt vs = fprintf fmt "@ (%a)" print_vsty vs

let print_constr fmt (cs,pjl) =
  let add_pj pj ty pjl = (pj,ty)::pjl in
  let print_pj fmt (pj,ty) = match pj with
    | Some ls -> fprintf fmt "@ (%a:@,%a)" print_ls ls print_ty ty
    | None -> print_ty_arg fmt ty
  in
  fprintf fmt "@[<hov 4>| %a%a%a@]" print_cs cs
    print_id_labels cs.ls_name
    (print_list nothing print_pj)
    (List.fold_right2 add_pj pjl cs.ls_args [])

let print_ty_decl fmt ts =
  let print_def fmt = function
    | NoDef -> ()
    | Alias ty -> fprintf fmt " =@ %a" print_ty ty
    | Range _  -> fprintf fmt " =@ <range ...>" (* TODO *)
    | Float _  -> fprintf fmt " =@ <float ...>" (* TODO *)
  in
  fprintf fmt "@[<hov 2>type %a%a%a%a@]"
    print_ts ts print_id_labels ts.ts_name
    (print_list nothing print_tv_arg) ts.ts_args
    print_def ts.ts_def;
  forget_tvs ()

let print_data_decl fst fmt (ts,csl) =
  fprintf fmt "@[<hov 2>%s %a%a%a =@\n@[<hov>%a@]@]"
    (if fst then "type" else "with") print_ts ts
    print_id_labels ts.ts_name
    (print_list nothing print_tv_arg) ts.ts_args
    (print_list newline print_constr) csl;
  forget_tvs ()

let print_ls_type fmt = fprintf fmt " :@ %a" print_ty

let ls_kind ls =
  if ls.ls_value = None then "predicate"
  else if ls.ls_args = [] then "constant" else "function"

let print_param_decl fmt ls =
  fprintf fmt "@[<hov 2>%s %a%a%a%a@]"
    (ls_kind ls) print_ls ls
    print_id_labels ls.ls_name
    (print_list nothing print_ty_arg) ls.ls_args
    (print_option print_ls_type) ls.ls_value;
  forget_tvs ()

let print_logic_decl fst fmt (ls,ld) =
  let vl,e = open_ls_defn ld in
  fprintf fmt "@[<hov 2>%s %a%a%a%a =@ %a@]"
    (if fst then ls_kind ls else "with") print_ls ls
    print_id_labels ls.ls_name
    (print_list nothing print_vs_arg) vl
    (print_option print_ls_type) ls.ls_value print_term e;
  List.iter forget_var vl;
  forget_tvs ()

let print_ind fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a%a :@ %a@]"
    print_pr pr print_id_labels pr.pr_name print_term f

let ind_sign = function
  | Ind   -> "inductive"
  | Coind -> "coinductive"

let print_ind_decl s fst fmt (ps,bl) =
  fprintf fmt "@[<hov 2>%s %a%a%a =@ @[<hov>%a@]@]"
    (if fst then ind_sign s else "with") print_ls ps
    print_id_labels ps.ls_name
    (print_list nothing print_ty_arg) ps.ls_args
    (print_list newline print_ind) bl;
  forget_tvs ()

let sprint_pkind = function
  | Paxiom -> "axiom"
  | Plemma -> "lemma"
  | Pgoal  -> "goal"
  | Pskip  -> "skip"

let print_pkind fmt k = pp_print_string fmt (sprint_pkind k)

let print_prop_decl fmt (k,pr,f) =
  fprintf fmt "@[<hov 2>%a %a%a :@ %a@]" print_pkind k
    print_pr pr print_id_labels pr.pr_name print_term f;
  forget_tvs ()

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r -> print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let print_decl fmt d = match d.d_node with
  | Dtype ts  -> print_ty_decl fmt ts
  | Ddata tl  -> print_list_next newline print_data_decl fmt tl
  | Dparam ls -> print_param_decl fmt ls
  | Dlogic ll -> print_list_next newline print_logic_decl fmt ll
  | Dind (s, il) -> print_list_next newline (print_ind_decl s) fmt il
  | Dprop p   -> print_prop_decl fmt p

let print_next_data_decl  = print_data_decl false
let print_data_decl       = print_data_decl true
let print_next_logic_decl = print_logic_decl false
let print_logic_decl      = print_logic_decl true
let print_next_ind_decl   = print_ind_decl Ind false
let print_ind_decl fmt s  = print_ind_decl s true fmt

let print_inst_ts fmt (ts1,ts2) =
  fprintf fmt "type %a = %a" print_ts ts1 print_ts ts2

let print_inst_ls fmt (ls1,ls2) =
  fprintf fmt "%s %a = %a" (ls_kind ls1) print_ls ls1 print_ls ls2

let print_inst_pr fmt (pr1,pr2) =
  fprintf fmt "prop %a = %a" print_pr pr1 print_pr pr2

let print_meta_arg_type fmt = function
  | MTty       -> fprintf fmt "[type]"
  | MTtysymbol -> fprintf fmt "[type symbol]"
  | MTlsymbol  -> fprintf fmt "[function/predicate symbol]"
  | MTprsymbol -> fprintf fmt "[proposition]"
  | MTstring   -> fprintf fmt "[string]"
  | MTint      -> fprintf fmt "[integer]"

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
      fprintf fmt "@[<hov 2>(* use %a *)@]" print_qt th
  | Clone (th,sm) when is_empty_sm sm ->
      fprintf fmt "@[<hov 2>(* use %a *)@]" print_qt th
  | Clone (th,sm) ->
      let tm = Mts.fold (fun x y a -> (x,y)::a) sm.sm_ts [] in
      let lm = Mls.fold (fun x y a -> (x,y)::a) sm.sm_ls [] in
      let pm = Mpr.fold (fun x y a -> (x,y)::a) sm.sm_pr [] in
      fprintf fmt "@[<hov 2>(* clone %a with %a,@ %a,@ %a *)@]"
        print_qt th (print_list comma print_inst_ts) tm
                    (print_list comma print_inst_ls) lm
                    (print_list comma print_inst_pr) pm
  | Meta (m,al) ->
      fprintf fmt "@[<hov 2>(* meta %s %a *)@]"
        m.meta_name (print_list comma print_meta_arg) al

let print_theory fmt th =
  fprintf fmt "@[<hov 2>theory %a%a@\n%a@]@\nend@."
    print_th th print_id_labels th.th_name
    (print_list newline2 print_tdecl) th.th_decls

let print_task fmt task =
  forget_all ();
  fprintf fmt "@[<hov 2>theory Task@\n%a@]@\nend@."
    (print_list newline2 print_tdecl) (task_tdecls task)

module NsTree = struct
  type t =
    | Namespace of string * namespace * known_map
    | Leaf      of string

  let contents ns kn =
    let add_ns s ns acc = Namespace (s, ns, kn) :: acc in
    let add_pr s p  acc =
      let k, _ = find_prop_decl kn p in
      Leaf (sprint_pkind k ^ " " ^ s) :: acc in
    let add_ls s ls acc =
      if s = "infix ="  && ls_equal ls ps_equ then acc else
        Leaf (ls_kind ls ^ " " ^ s) :: acc
    in
    let add_ts s ts acc =
      if s = "int"  && ts_equal ts ts_int  then acc else
      if s = "real" && ts_equal ts ts_real then acc else
        Leaf ("type " ^ s) :: acc
    in
    let acc = Mstr.fold add_ns ns.ns_ns []  in
    let acc = Mstr.fold add_pr ns.ns_pr acc in
    let acc = Mstr.fold add_ls ns.ns_ls acc in
    let acc = Mstr.fold add_ts ns.ns_ts acc in acc

  let decomp = function
    | Namespace (s,ns,kn) -> s, contents ns kn
    | Leaf s              -> s, []
end

let print_namespace fmt name th =
  let module P = Print_tree.Make(NsTree) in
  fprintf fmt "@[<hov>%a@]@." P.print
    (NsTree.Namespace (name, th.th_export, th.th_known))


(* print task under the form of a sequent, with only local context, for the IDE *)

(*
let print_goal fmt d =
   match d.d_node with
   | Dprop (Pgoal,_pr,f) -> fprintf fmt "@[%a@]@\n" print_term f
   | _ -> assert false
*)

let print_sequent fmt task =
  let ut = Task.used_symbols (Task.used_theories task) in
  let ld = Task.local_decls task ut in
  let rec aux fmt l =
    match l with
      | [] -> assert false
      | [g] ->
         fprintf fmt "----------------------------- Goal ---------------------------@\n@\n";
         print_decl fmt g
      | d :: r ->
         fprintf fmt "@[%a@]@\n@\n" print_decl d;
         aux fmt r
  in
  fprintf fmt "----------------------------- Local context ---------------------------@\n@\n";
  fprintf fmt "@[<v 0>%a@]" aux ld




            end) : Pretty_sig.Printer) (* end of the first class module *)



module LegacyPrinter =
  (val (let iprinter,aprinter,tprinter,pprinter =
    let isanitize = sanitizer char_to_alpha char_to_alnumus in
    let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
    create_ident_printer why3_keywords ~sanitizer:isanitize,
    create_ident_printer why3_keywords ~sanitizer:lsanitize,
    create_ident_printer why3_keywords ~sanitizer:lsanitize,
    create_ident_printer why3_keywords ~sanitizer:isanitize
  in
  create iprinter aprinter tprinter pprinter true))

include LegacyPrinter


(* Exception reporting *)

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | Ty.TypeMismatch (t1,t2) ->
      fprintf fmt "Type mismatch between %a and %a"
        print_ty t1 print_ty t2
  | Ty.BadTypeArity ({ts_args = []} as ts, _) ->
      fprintf fmt "Type symbol %a expects no arguments" print_ts ts
  | Ty.BadTypeArity (ts, app_arg) ->
      let i = List.length ts.ts_args in
      fprintf fmt "Type symbol %a expects %i argument%s but is applied to %i"
        print_ts ts i (if i = 1 then "" else "s") app_arg
  | Ty.DuplicateTypeVar tv ->
      fprintf fmt "Type variable %a is used twice" print_tv tv
  | Ty.UnboundTypeVar tv ->
      fprintf fmt "Unbound type variable: %a" print_tv tv
  | Ty.UnexpectedProp ->
      fprintf fmt "Unexpected propositional type"
  | Ty.EmptyRange ->
      fprintf fmt "Empty integer range"
  | Ty.BadFloatSpec ->
      fprintf fmt "Invalid floating point format"
  | Ty.IllegalTypeParameters ->
      fprintf fmt "This type cannot have type parameters"
  | Term.BadArity ({ls_args = []} as ls, _) ->
      fprintf fmt "%s %a expects no arguments"
        (if ls.ls_value = None then "Predicate" else "Function") print_ls ls
  | Term.BadArity (ls, app_arg) ->
      let i = List.length ls.ls_args in
      fprintf fmt "%s %a expects %i argument%s but is applied to %i"
        (if ls.ls_value = None then "Predicate" else "Function")
        print_ls ls i (if i = 1 then "" else "s") app_arg
  | Term.EmptyCase ->
      fprintf fmt "Empty match expression"
  | Term.DuplicateVar vs ->
      fprintf fmt "Variable %a is used twice" print_vsty vs
  | Term.UncoveredVar vs ->
      fprintf fmt "Variable %a uncovered in \"or\"-pattern" print_vsty vs
  | Term.FunctionSymbolExpected ls ->
      fprintf fmt "Not a function symbol: %a" print_ls ls
  | Term.PredicateSymbolExpected ls ->
      fprintf fmt "Not a predicate symbol: %a" print_ls ls
  | Term.ConstructorExpected ls ->
      fprintf fmt "%s %a is not a constructor"
        (if ls.ls_value = None then "Predicate" else "Function") print_ls ls
  | Term.TermExpected t ->
      fprintf fmt "Not a term: %a" print_term t
  | Term.FmlaExpected t ->
      fprintf fmt "Not a formula: %a" print_term t
  | Term.InvalidLiteralType ty ->
      fprintf fmt "Type %a cannot be used for a numeric literal" print_ty ty
  | Pattern.ConstructorExpected (ls,ty) ->
      fprintf fmt "%s %a is not a constructor of type %a"
        (if ls.ls_value = None then "Predicate" else "Function") print_ls ls
        print_ty ty
  | Pattern.NonExhaustive pl ->
      fprintf fmt "Pattern not covered by a match:@\n  @[%a@]"
        print_pat (List.hd pl)
  | Decl.BadConstructor ls ->
      fprintf fmt "Bad constructor: %a" print_ls ls
  | Decl.BadRecordField ls ->
      fprintf fmt "Not a record field: %a" print_ls ls
  | Decl.RecordFieldMissing (_cs,ls) ->
      fprintf fmt "Field %a is missing" print_ls ls
  | Decl.DuplicateRecordField (_cs,ls) ->
      fprintf fmt "Field %a is used twice in the same constructor" print_ls ls
  | Decl.IllegalTypeAlias ts ->
      fprintf fmt
        "Type symbol %a is a type alias and cannot be declared as algebraic"
        print_ts ts
  | Decl.NonFoundedTypeDecl ts ->
      fprintf fmt "Cannot construct a value of type %a" print_ts ts
  | Decl.NonPositiveTypeDecl (_ts, ls, ty) ->
      fprintf fmt "Constructor %a \
          contains a non strictly positive occurrence of type %a"
        print_ls ls print_ty ty
  | Decl.InvalidIndDecl (_ls, pr) ->
      fprintf fmt "Ill-formed inductive clause %a"
        print_pr pr
  | Decl.NonPositiveIndDecl (_ls, pr, ls1) ->
      fprintf fmt "Inductive clause %a contains \
          a non strictly positive occurrence of symbol %a"
        print_pr pr print_ls ls1
  | Decl.BadLogicDecl (ls1,ls2) ->
      fprintf fmt "Ill-formed definition: symbols %a and %a are different"
        print_ls ls1 print_ls ls2
  | Decl.UnboundVar vs ->
      fprintf fmt "Unbound variable: %a" print_vsty vs
  | Decl.ClashIdent id ->
      fprintf fmt "Ident %s is defined twice" id.id_string
  | Decl.EmptyDecl ->
      fprintf fmt "Empty declaration"
  | Decl.EmptyAlgDecl ts ->
      fprintf fmt "Algebraic type %a has no constructors" print_ts ts
  | Decl.EmptyIndDecl ls ->
      fprintf fmt "Inductive predicate %a has no constructors" print_ls ls
  | Decl.KnownIdent id ->
      fprintf fmt "Ident %s is already declared" id.id_string
  | Decl.UnknownIdent id ->
      fprintf fmt "Ident %s is not yet declared" id.id_string
  | Decl.RedeclaredIdent id ->
      fprintf fmt "Ident %s is already declared, with a different declaration"
        id.id_string
  | Decl.NoTerminationProof ls ->
      fprintf fmt "Cannot prove the termination of %a" print_ls ls
  | _ -> raise exn
  end
