(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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
open Pp
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task

let debug_print_labels = Debug.register_flag "print_labels"

let iprinter,tprinter,lprinter,pprinter =
  let bl = ["theory"; "type"; "logic"; "inductive"; "meta";
            "axiom"; "lemma"; "goal"; "use"; "clone"; "prop";
            "namespace"; "import"; "export"; "end";
            "forall"; "exists"; "and"; "or"; "not";
            "true"; "false"; "if"; "then"; "else";
            "let"; "in"; "match"; "with"; "as"; "epsilon" ]
  in
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
  let usanitize = sanitizer char_to_ualpha char_to_alnumus in
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:lsanitize,
  create_ident_printer bl ~sanitizer:isanitize,
  create_ident_printer bl ~sanitizer:usanitize

let forget_all () =
  forget_all iprinter;
  forget_all tprinter;
  forget_all lprinter;
  forget_all pprinter

let tv_set = ref Sid.empty

(* type variables always start with a quote *)
let print_tv fmt tv =
  tv_set := Sid.add tv.tv_name !tv_set;
  let sanitizer n = "'" ^ n in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer tv.tv_name)

let forget_tvs () =
  Sid.iter (forget_id iprinter) !tv_set;
  tv_set := Sid.empty

(* logic variables always start with a lower case letter *)
let print_vs fmt vs =
  let sanitizer = String.uncapitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer vs.vs_name)

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
  let s = Str.replace_first (Str.regexp "^\\*.") " \\0" s in
  let s = Str.replace_first (Str.regexp ".\\*$") "\\0 " s in
  s

(* theory names always start with an upper case letter *)
let print_th fmt th =
  let sanitizer = String.capitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer th.th_name)

let print_ts fmt ts =
  fprintf fmt "%s" (id_unique tprinter ts.ts_name)

let print_ls fmt ls = match extract_op ls with
  | Some s -> fprintf fmt "(%s)" (escape_op s)
  | None   -> fprintf fmt "%s" (id_unique lprinter ls.ls_name)

let print_cs fmt ls =
  let sanitizer = String.capitalize in
  fprintf fmt "%s" (id_unique lprinter ~sanitizer ls.ls_name)

let print_pr fmt pr =
  fprintf fmt "%s" (id_unique pprinter pr.pr_name)

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_ty_node inn fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, tl) when is_ts_tuple ts -> fprintf fmt "(%a)"
      (print_list comma (print_ty_node false)) tl
  | Tyapp (ts, []) -> print_ts fmt ts
  | Tyapp (ts, tl) -> fprintf fmt (protect_on inn "%a@ %a")
      print_ts ts (print_list space (print_ty_node true)) tl

let print_ty = print_ty_node false

let print_const fmt = function
  | ConstInt s -> fprintf fmt "%s" s
  | ConstReal (RConstDecimal (i,f,None)) -> fprintf fmt "%s.%s" i f
  | ConstReal (RConstDecimal (i,f,Some e)) -> fprintf fmt "%s.%se%s" i f e
  | ConstReal (RConstHexa (i,f,e)) -> fprintf fmt "0x%s.%sp%s" i f e

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
  inspect (of_option fs.ls_value)

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
  fprintf fmt "%a:@,%a" print_vs v print_ty v.vs_ty

let print_quant fmt = function
  | Fforall -> fprintf fmt "forall"
  | Fexists -> fprintf fmt "exists"

let print_binop fmt = function
  | Fand -> fprintf fmt "and"
  | For -> fprintf fmt "or"
  | Fimplies -> fprintf fmt "->"
  | Fiff -> fprintf fmt "<->"

let prio_binop = function
  | Fand -> 3
  | For -> 2
  | Fimplies -> 1
  | Fiff -> 1

let print_label fmt (l,_) =
  if l = "" then () else fprintf fmt "\"%s\"" l

let print_ident_labels fmt id =
  if Debug.test_flag debug_print_labels && id.id_label <> []
  then fprintf fmt " %a" (print_list space print_label) id.id_label
  else ()

let rec print_term fmt t = print_lterm 0 fmt t
and     print_fmla fmt f = print_lfmla 0 fmt f

and print_lterm pri fmt t = match t.t_label with
  | _ when Debug.nottest_flag debug_print_labels
       -> print_tnode pri fmt t
  | [] -> print_tnode pri fmt t
  | ll -> fprintf fmt (protect_on (pri > 0) "%a %a")
      (print_list space print_label) ll (print_tnode 0) t

and print_lfmla pri fmt f = match f.f_label with
  | _ when Debug.nottest_flag debug_print_labels
       -> print_fnode pri fmt f
  | [] -> print_fnode pri fmt f
  | ll -> fprintf fmt (protect_on (pri > 0) "%a %a")
      (print_list space print_label) ll (print_fnode 0) f

and print_app pri ls fmt tl = match extract_op ls, tl with
  | _, [] ->
      print_ls fmt ls
  | Some s, [t1] when tight_op s ->
      fprintf fmt (protect_on (pri > 6) "%s%a")
        s (print_lterm 6) t1
  | Some s, [t1] ->
      fprintf fmt (protect_on (pri > 4) "%s %a")
        s (print_lterm 5) t1
  | Some s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 4) "%a %s@ %a")
        (print_lterm 5) t1 s (print_lterm 5) t2
  | _, tl ->
      fprintf fmt (protect_on (pri > 5) "%a@ %a")
        print_ls ls (print_list space (print_lterm 6)) tl

and print_tnode pri fmt t = match t.t_node with
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      print_const fmt c
  | Tapp (fs, tl) when is_fs_tuple fs ->
      fprintf fmt "(%a)" (print_list comma print_term) tl
  | Tapp (fs, tl) when unambig_fs fs ->
      print_app pri fs fmt tl
  | Tapp (fs, tl) ->
      fprintf fmt (protect_on (pri > 0) "%a:%a")
        (print_app 5 fs) tl print_ty t.t_ty
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on (pri > 0) "if @[%a@] then %a@ else %a")
        print_fmla f print_term t1 print_term t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on (pri > 0) "let %a = @[%a@] in@ %a")
        print_vs v (print_lterm 4) t1 print_term t2;
      forget_var v
  | Tcase (t1,bl) ->
      fprintf fmt "match @[%a@] with@\n@[<hov>%a@]@\nend"
        print_term t1 (print_list newline print_tbranch) bl
  | Teps fb ->
      let v,f = f_open_bound fb in
      fprintf fmt (protect_on (pri > 0) "epsilon %a.@ %a")
        print_vsty v print_fmla f;
      forget_var v

and print_fnode pri fmt f = match f.f_node with
  | Fapp (ps,tl) ->
      print_app pri ps fmt tl
  | Fquant (q,fq) ->
      let vl,tl,f = f_open_quant fq in
      fprintf fmt (protect_on (pri > 0) "%a %a%a.@ %a") print_quant q
        (print_list comma print_vsty) vl print_tl tl print_fmla f;
      List.iter forget_var vl
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fbinop (b,f1,f2) ->
      let p = prio_binop b in
      fprintf fmt (protect_on (pri > p) "%a %a@ %a")
        (print_lfmla (p + 1)) f1 print_binop b (print_lfmla p) f2
  | Fnot f ->
      fprintf fmt (protect_on (pri > 4) "not %a") (print_lfmla 4) f
  | Fif (f1,f2,f3) ->
      fprintf fmt (protect_on (pri > 0) "if @[%a@] then %a@ else %a")
        print_fmla f1 print_fmla f2 print_fmla f3
  | Flet (t,f) ->
      let v,f = f_open_bound f in
      fprintf fmt (protect_on (pri > 0) "let %a = @[%a@] in@ %a")
        print_vs v (print_lterm 4) t print_fmla f;
      forget_var v
  | Fcase (t,bl) ->
      fprintf fmt "match @[%a@] with@\n@[<hov>%a@]@\nend"
        print_term t (print_list newline print_fbranch) bl

and print_tbranch fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_term t;
  Svs.iter forget_var p.pat_vars

and print_fbranch fmt br =
  let p,f = f_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_fmla f;
  Svs.iter forget_var p.pat_vars

and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_expr)) tl

and print_expr fmt = e_apply (print_term fmt) (print_fmla fmt)

(** Declarations *)

let print_tv_arg fmt tv = fprintf fmt "@ %a" print_tv tv
let print_ty_arg fmt ty = fprintf fmt "@ %a" (print_ty_node true) ty
let print_vs_arg fmt vs = fprintf fmt "@ (%a)" print_vsty vs

let print_constr ty fmt cs =
  let ty_val = of_option cs.ls_value in
  let m = ty_match Mtv.empty ty_val ty in
  let tl = List.map (ty_inst m) cs.ls_args in
  fprintf fmt "@[<hov 4>| %a%a@]" print_cs cs
    (print_list nothing print_ty_arg) tl

let print_type_decl fst fmt (ts,def) = match def with
  | Tabstract -> begin match ts.ts_def with
      | None ->
          fprintf fmt "@[<hov 2>%s %a%a@]"
            (if fst then "type" else "with") print_ts ts
            (print_list nothing print_tv_arg) ts.ts_args
      | Some ty ->
          fprintf fmt "@[<hov 2>%s %a%a =@ %a@]"
            (if fst then "type" else "with") print_ts ts
            (print_list nothing print_tv_arg) ts.ts_args print_ty ty
      end
  | Talgebraic csl ->
      let ty = ty_app ts (List.map ty_var ts.ts_args) in
      fprintf fmt "@[<hov 2>%s %a%a =@\n@[<hov>%a@]@]"
        (if fst then "type" else "with") print_ts ts
        (print_list nothing print_tv_arg) ts.ts_args
        (print_list newline (print_constr ty)) csl

let print_type_decl fst fmt d = print_type_decl fst fmt d; forget_tvs ()

let print_ls_type fmt = fprintf fmt " :@ %a" print_ty

let print_logic_decl fst fmt (ls,ld) = match ld with
  | Some ld ->
      let vl,e = open_ls_defn ld in
      fprintf fmt "@[<hov 2>%s %a%a%a =@ %a@]"
        (if fst then "logic" else "with") print_ls ls
        (print_list nothing print_vs_arg) vl
        (print_option print_ls_type) ls.ls_value print_expr e;
      List.iter forget_var vl
  | None ->
      fprintf fmt "@[<hov 2>%s %a%a%a@]"
        (if fst then "logic" else "with") print_ls ls
        (print_list nothing print_ty_arg) ls.ls_args
        (print_option print_ls_type) ls.ls_value

let print_logic_decl fst fmt d = print_logic_decl fst fmt d; forget_tvs ()

let print_ind fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a%a : %a@]"
    print_pr pr print_ident_labels pr.pr_name print_fmla f

let print_ind_decl fst fmt (ps,bl) =
  fprintf fmt "@[<hov 2>%s %a%a =@ @[<hov>%a@]@]"
    (if fst then "inductive" else "with") print_ls ps
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
  fprintf fmt "@[<hov 2>%a %a%a : %a@]" print_pkind k
    print_pr pr print_ident_labels pr.pr_name print_fmla f;
  forget_tvs ()

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r -> print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let print_decl fmt d = match d.d_node with
  | Dtype tl  -> print_list_next newline print_type_decl fmt tl
  | Dlogic ll -> print_list_next newline print_logic_decl fmt ll
  | Dind il   -> print_list_next newline print_ind_decl fmt il
  | Dprop p   -> print_prop_decl fmt p

let print_next_type_decl  = print_type_decl false
let print_type_decl       = print_type_decl true
let print_next_logic_decl = print_logic_decl false
let print_logic_decl      = print_logic_decl true
let print_next_ind_decl   = print_ind_decl false
let print_ind_decl        = print_ind_decl true

let print_inst_ts fmt (ts1,ts2) =
  fprintf fmt "type %a = %a" print_ts ts1 print_ts ts2

let print_inst_ls fmt (ls1,ls2) =
  fprintf fmt "logic %a = %a" print_ls ls1 print_ls ls2

let print_inst_pr fmt (pr1,pr2) =
  fprintf fmt "prop %a = %a" print_pr pr1 print_pr pr2

let print_meta_arg_type fmt = function
  | MTty       -> fprintf fmt "[type]"
  | MTtysymbol -> fprintf fmt "[type symbol]"
  | MTlsymbol  -> fprintf fmt "[logic symbol]"
  | MTprsymbol -> fprintf fmt "[proposition]"
  | MTstring   -> fprintf fmt "[string]"
  | MTint      -> fprintf fmt "[integer]"

let print_meta_arg fmt = function
  | MAty ty -> fprintf fmt "type %a" print_ty ty
  | MAts ts -> fprintf fmt "type %a" print_ts ts
  | MAls ls -> fprintf fmt "logic %a" print_ls ls
  | MApr pr -> fprintf fmt "prop %a" print_pr pr
  | MAstr s -> fprintf fmt "\"%s\"" s
  | MAint i -> fprintf fmt "%d" i

let print_tdecl fmt td = match td.td_node with
  | Decl d ->
      print_decl fmt d
  | Use th ->
      fprintf fmt "@[<hov 2>(* use %a *)@]" print_th th
  | Clone (th,sm) when is_empty_sm sm ->
      fprintf fmt "@[<hov 2>(* use %a *)@]" print_th th
  | Clone (th,sm) ->
      let tm = Mts.fold (fun x y a -> (x,y)::a) sm.sm_ts [] in
      let lm = Mls.fold (fun x y a -> (x,y)::a) sm.sm_ls [] in
      let pm = Mpr.fold (fun x y a -> (x,y)::a) sm.sm_pr [] in
      fprintf fmt "@[<hov 2>(* clone %a with %a,@ %a,@ %a *)@]"
        print_th th (print_list comma print_inst_ts) tm
                    (print_list comma print_inst_ls) lm
                    (print_list comma print_inst_pr) pm
  | Meta (m,al) ->
      fprintf fmt "@[<hov 2>(* meta %s %a *)@]"
        m.meta_name (print_list comma print_meta_arg) al

let print_theory fmt th =
  fprintf fmt "@[<hov 2>theory %a%a@\n%a@]@\nend@."
    print_th th print_ident_labels th.th_name
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
        Leaf ("logic " ^ s) :: acc
    in
    let add_ts s ts acc =
      if s = "int"  && ts_equal ts ts_int  then acc else
      if s = "real" && ts_equal ts ts_real then acc else
        Leaf ("type " ^ s) :: acc
    in
    let acc = Mnm.fold add_ns ns.ns_ns []  in
    let acc = Mnm.fold add_pr ns.ns_pr acc in
    let acc = Mnm.fold add_ls ns.ns_ls acc in
    let acc = Mnm.fold add_ts ns.ns_ts acc in acc

  let decomp = function
    | Namespace (s,ns,kn) -> s, contents ns kn
    | Leaf s              -> s, []
end

let print_namespace fmt name th =
  let module P = Print_tree.Make(NsTree) in
  fprintf fmt "@[<hov>%a@]@." P.print
    (NsTree.Namespace (name, th.th_export, th.th_known))

(* Exception reporting *)

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | Ty.TypeMismatch (t1,t2) ->
      fprintf fmt "Type mismatch between %a and %a"
        print_ty t1 print_ty t2
  | Ty.BadTypeArity (ts, ts_arg, app_arg) ->
      fprintf fmt "Bad type arity: type symbol %a must be applied \
                   to %i arguments, but is applied to %i"
        print_ts ts ts_arg app_arg
  | Ty.DuplicateTypeVar tv ->
      fprintf fmt "Type variable %a is used twice" print_tv tv
  | Ty.UnboundTypeVar tv ->
      fprintf fmt "Unbound type variable: %a" print_tv tv
  | Term.BadArity (ls, ls_arg, app_arg) ->
      fprintf fmt "Bad arity: symbol %a must be applied \
                   to %i arguments, but is applied to %i"
        print_ls ls ls_arg app_arg
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
  | Term.NoMatch ->
      fprintf fmt "Uncatched Term.NoMatch exception: [tf]_match failed"
  | Pattern.ConstructorExpected ls ->
      fprintf fmt "The symbol %a is not a constructor"
        print_ls ls
  | Pattern.NonExhaustive pl ->
      fprintf fmt "Non-exhaustive pattern list:@\n@[<hov 2>%a@]"
        (print_list newline print_pat) pl
  | Decl.IllegalTypeAlias ts ->
      fprintf fmt
        "Type symbol %a is a type alias and cannot be declared as algebraic"
        print_ts ts
  | Decl.NonFoundedTypeDecl ts ->
      fprintf fmt "Cannot construct a value of type %a" print_ts ts
  | Decl.NonPositiveTypeDecl (_ts, ls, ts1) ->
      fprintf fmt "Constructor %a \
          contains a non strictly positive occurrence of type symbol %a"
        print_ls ls print_ts ts1
  | Decl.InvalidIndDecl (_ls, pr) ->
      fprintf fmt "Ill-formed inductive clause %a"
        print_pr pr
  | Decl.NonPositiveIndDecl (_ls, pr, ls1) ->
      fprintf fmt "Inductive clause %a contains \
          a negative occurrence of symbol %a"
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
  | Decl.NonExhaustiveExpr (pl, e) ->
      fprintf fmt "Pattern @[%a@] is not covered in expression:@\n  @[%a@]"
        (print_list comma print_pat) pl print_expr e
  | _ -> raise exn
  end

