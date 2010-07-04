(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

let iprinter,tprinter,lprinter,pprinter =
  let bl = ["theory"; "type"; "logic"; "inductive";
            "axiom"; "lemma"; "goal"; "use"; "clone";
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

let thash = Hid.create 63
let lhash = Hid.create 63
let phash = Hid.create 63

let forget_all () =
  forget_all iprinter;
  forget_all tprinter;
  forget_all lprinter;
  forget_all pprinter;
  Hid.clear thash;
  Hid.clear lhash;
  Hid.clear phash

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

(* theory names always start with an upper case letter *)
let print_th fmt th =
  let sanitizer = String.capitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer th.th_name)

let print_ts fmt ts =
  Hid.replace thash ts.ts_name ts;
  fprintf fmt "%s" (id_unique tprinter ts.ts_name)

let print_ls fmt ls =
  Hid.replace lhash ls.ls_name ls;
  fprintf fmt "%s" (id_unique lprinter ls.ls_name)

let print_cs fmt ls =
  Hid.replace lhash ls.ls_name ls;
  let sanitizer = String.capitalize in
  fprintf fmt "%s" (id_unique lprinter ~sanitizer ls.ls_name)

let print_pr fmt pr =
  Hid.replace phash pr.pr_name pr;
  fprintf fmt "%s" (id_unique pprinter pr.pr_name)

(** Types *)

let rec ns_comma fmt () = fprintf fmt ",@,"

let rec print_ty fmt ty = match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, []) -> print_ts fmt ts
  | Tyapp (ts, [t]) -> fprintf fmt "%a@ %a" print_ty t print_ts ts
  | Tyapp (ts, l) -> fprintf fmt "(%a)@ %a"
      (print_list ns_comma print_ty) l print_ts ts

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

let lparen_l fmt () = fprintf fmt "@ ("
let lparen_r fmt () = fprintf fmt "(@,"
let print_paren_l fmt x = print_list_delim lparen_l rparen comma fmt x
let print_paren_r fmt x = print_list_delim lparen_r rparen comma fmt x

let rec print_pat fmt p = match p.pat_node with
  | Pwild -> fprintf fmt "_"
  | Pvar v -> print_vs fmt v
  | Pas (p,v) -> fprintf fmt "%a as %a" print_pat p print_vs v
  | Papp (cs,pl) -> fprintf fmt "%a%a"
      print_cs cs (print_paren_r print_pat) pl

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

let print_label fmt l = fprintf fmt "\"%s\"" l

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_term fmt t = print_lrterm false false fmt t
and     print_fmla fmt f = print_lrfmla false false fmt f
and print_opl_term fmt t = print_lrterm true  false fmt t
and print_opl_fmla fmt f = print_lrfmla true  false fmt f
and print_opr_term fmt t = print_lrterm false true  fmt t
and print_opr_fmla fmt f = print_lrfmla false true  fmt f

and print_lrterm opl opr fmt t = match t.t_label with
  | [] -> print_tnode opl opr fmt t
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_tnode false false) t

and print_lrfmla opl opr fmt f = match f.f_label with
  | [] -> print_fnode opl opr fmt f
  | ll -> fprintf fmt "(%a %a)"
      (print_list space print_label) ll (print_fnode false false) f

and print_tnode opl opr fmt t = match t.t_node with
  | Tbvar _ ->
      assert false
  | Tvar v ->
      print_vs fmt v
  | Tconst c ->
      print_const fmt c
  | Tapp (fs, tl) when unambig_fs fs ->
      fprintf fmt "%a%a" print_ls fs (print_paren_r print_term) tl
  | Tapp (fs, tl) ->
      fprintf fmt (protect_on opl "%a%a:%a")
        print_ls fs (print_paren_r print_term) tl print_ty t.t_ty
  | Tif (f,t1,t2) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        print_fmla f print_term t1 print_opl_term t2
  | Tlet (t1,tb) ->
      let v,t2 = t_open_bound tb in
      fprintf fmt (protect_on opr "let %a =@ %a in@ %a")
        print_vs v print_opl_term t1 print_opl_term t2;
      forget_var v
  | Tcase (tl,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_list comma print_term) tl
        (print_list newline print_tbranch) bl
  | Teps fb ->
      let v,f = f_open_bound fb in
      fprintf fmt (protect_on opr "epsilon %a.@ %a")
        print_vsty v print_opl_fmla f;
      forget_var v

and print_fnode opl opr fmt f = match f.f_node with
  | Fapp (ps,[t1;t2]) when ps = ps_equ ->
      fprintf fmt (protect_on (opl || opr) "%a =@ %a")
        print_opr_term t1 print_opl_term t2
  | Fapp (ps,tl) ->
      fprintf fmt "%a%a" print_ls ps
        (print_paren_r print_term) tl
  | Fquant (q,fq) ->
      let vl,tl,f = f_open_quant fq in
      fprintf fmt (protect_on opr "%a %a%a.@ %a") print_quant q
        (print_list comma print_vsty) vl print_tl tl print_fmla f;
      List.iter forget_var vl
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fbinop (b,f1,f2) ->
      fprintf fmt (protect_on (opl || opr) "%a %a@ %a")
        print_opr_fmla f1 print_binop b print_opl_fmla f2
  | Fnot f ->
      fprintf fmt (protect_on opr "not %a") print_opl_fmla f
  | Fif (f1,f2,f3) ->
      fprintf fmt (protect_on opr "if %a@ then %a@ else %a")
        print_fmla f1 print_fmla f2 print_opl_fmla f3
  | Flet (t,f) ->
      let v,f = f_open_bound f in
      fprintf fmt (protect_on opr "let %a =@ %a in@ %a")
        print_vs v print_opl_term t print_opl_fmla f;
      forget_var v
  | Fcase (tl,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        (print_list comma print_term) tl
        (print_list newline print_fbranch) bl

and print_tbranch fmt br =
  let pl,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]"
    (print_list comma print_pat) pl print_term t;
  Svs.iter forget_var (List.fold_left pat_freevars Svs.empty pl)

and print_fbranch fmt br =
  let pl,f = f_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]"
    (print_list comma print_pat) pl print_fmla f;
  Svs.iter forget_var (List.fold_left pat_freevars Svs.empty pl)

and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_expr)) tl

and print_expr fmt = e_apply (print_term fmt) (print_fmla fmt)

(** Declarations *)

let print_constr fmt cs =
  fprintf fmt "@[<hov 4>| %a%a@]" print_cs cs
    (print_paren_l print_ty) cs.ls_args

let print_ty_args fmt = function
  | [] -> ()
  | [tv] -> fprintf fmt " %a" print_tv tv
  | l -> fprintf fmt " (%a)" (print_list ns_comma print_tv) l

let print_type_decl fmt (ts,def) = match def with
  | Tabstract -> begin match ts.ts_def with
      | None ->
          fprintf fmt "@[<hov 2>type%a %a@]"
            print_ty_args ts.ts_args print_ts ts
      | Some ty ->
          fprintf fmt "@[<hov 2>type%a %a =@ %a@]"
            print_ty_args ts.ts_args print_ts ts print_ty ty
      end
  | Talgebraic csl ->
      fprintf fmt "@[<hov 2>type%a %a =@\n@[<hov>%a@]@]"
        print_ty_args ts.ts_args print_ts ts
        (print_list newline print_constr) csl

let print_type_decl fmt d = print_type_decl fmt d; forget_tvs ()

let print_ls_type fmt = fprintf fmt " :@ %a" print_ty

let print_logic_decl fmt (ls,ld) = match ld with
  | Some ld ->
      let vl,e = open_ls_defn ld in
      fprintf fmt "@[<hov 2>logic %a%a%a =@ %a@]"
        print_ls ls (print_paren_l print_vsty) vl
        (print_option print_ls_type) ls.ls_value print_expr e;
      List.iter forget_var vl
  | None ->
      fprintf fmt "@[<hov 2>logic %a%a%a@]"
        print_ls ls (print_paren_l print_ty) ls.ls_args
        (print_option print_ls_type) ls.ls_value

let print_logic_decl fmt d = print_logic_decl fmt d; forget_tvs ()

let print_ind fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a : %a@]" print_pr pr print_fmla f

let print_ind_decl fmt (ps,bl) =
  fprintf fmt "@[<hov 2>inductive %a%a =@ @[<hov>%a@]@]"
    print_ls ps (print_paren_l print_ty) ps.ls_args
    (print_list newline print_ind) bl;
  forget_tvs ()

let print_pkind fmt = function
  | Paxiom -> fprintf fmt "axiom"
  | Plemma -> fprintf fmt "lemma"
  | Pgoal  -> fprintf fmt "goal"
  | Pskip  -> fprintf fmt "skip"

let print_prop_decl fmt (k,pr,f) =
  fprintf fmt "@[<hov 2>%a %a : %a@]" print_pkind k
    print_pr pr print_fmla f;
  forget_tvs ()

let print_decl fmt d = match d.d_node with
  | Dtype tl  -> print_list newline print_type_decl fmt tl
  | Dlogic ll -> print_list newline print_logic_decl fmt ll
  | Dind il   -> print_list newline print_ind_decl fmt il
  | Dprop p   -> print_prop_decl fmt p

let print_inst fmt (id1,id2) =
  if Hid.mem thash id2 then
    let n = id_unique tprinter id1 in
    fprintf fmt "type %s = %a" n print_ts (Hid.find thash id2)
  else if Hid.mem lhash id2 then
    let n = id_unique lprinter id1 in
    fprintf fmt "logic %s = %a" n print_ls (Hid.find lhash id2)
  else if Hid.mem phash id2 then
    let n = id_unique pprinter id1 in
    fprintf fmt "prop %s = %a" n print_pr (Hid.find phash id2)
  else
    fprintf fmt "ident %s = %s" id1.id_string id2.id_string

let print_meta_arg_type fmt = function
  | MTtysymbol -> fprintf fmt "type_symbol"
  | MTlsymbol -> fprintf fmt "logic_symbol"
  | MTprsymbol -> fprintf fmt "proposition"
  | MTstring -> fprintf fmt "string"
  | MTint -> fprintf fmt "int"

let print_meta_arg fmt = function
  | MARid id ->
      if Hid.mem thash id then
        fprintf fmt "type %a" print_ts (Hid.find thash id)
      else if Hid.mem lhash id then
        fprintf fmt "logic %a" print_ls (Hid.find lhash id)
      else if Hid.mem phash id then
        fprintf fmt "prop %a" print_pr (Hid.find phash id)
      else
        fprintf fmt "ident %s" id.id_string
  | MARstr s -> fprintf fmt "\"%s\"" s
  | MARint i -> fprintf fmt "%d" i

let print_tdecl fmt td = match td.td_node with
  | Decl d ->
      print_decl fmt d
  | Use th ->
      fprintf fmt "@[<hov 2>(* use %a *)@]" print_th th
  | Clone (th,inst) ->
      let inst = Mid.fold (fun x y a -> (x,y)::a) inst [] in
      fprintf fmt "@[<hov 2>(* clone %a with %a *)@]"
        print_th th (print_list comma print_inst) inst
  | Meta (t,al) ->
      fprintf fmt "@[<hov 2>(* meta %s %a *)@]"
        t (print_list space print_meta_arg) al

let print_theory fmt th =
  fprintf fmt "@[<hov 2>theory %a@\n%a@]@\nend@."
    print_th th (print_list newline2 print_tdecl) th.th_decls

let print_task fmt task =
  fprintf fmt "@[<hov>%a@]@."
    (print_list newline2 print_decl) (task_decls task)

let print_named_task fmt name task =
  fprintf fmt "@[<hov 2>task %s@\n%a@]@\nend@."
    name (print_list newline2 print_tdecl) (task_tdecls task)

module NsTree = struct
  type t =
    | Namespace of string * namespace
    | Leaf      of string

  let contents ns =
    let add_ns s ns acc = Namespace (s, ns) :: acc in
    let add_pr s _  acc = Leaf ("prop " ^ s) :: acc in
    let add_ls s ls acc =
      if s = "infix ="  && ls_equal ls ps_equ then acc else
      if s = "infix <>" && ls_equal ls ps_neq then acc else
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
    | Namespace (s,ns) -> s, contents ns
    | Leaf s           -> s, []
end

let print_namespace fmt name ns =
  let module P = Print_tree.Make(NsTree) in
  fprintf fmt "@[<hov>%a@]@." P.print (NsTree.Namespace (name, ns))

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
  | Term.DuplicateVar vs ->
      fprintf fmt "Variable %a is used twice" print_vsty vs
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
  | Decl.InvalidIndDecl (_ls, pr) ->
      fprintf fmt "Ill-formed clause %a in inductive predicate declaration"
        print_pr pr
  | Decl.TooSpecificIndDecl (_ls, pr, t) ->
      fprintf fmt "Clause %a in inductive predicate declaration \
          has too type-specific conclusion %a"
        print_pr pr print_term t
  | Decl.NonPositiveIndDecl (_ls, pr, ls1) ->
      fprintf fmt "Clause %a in inductive predicate declaration \
          contains a negative occurrence of dependent symbol %a"
        print_pr pr print_ls ls1
  | Decl.BadLogicDecl (id1,id2) ->
      fprintf fmt "Ill-formed definition: idents %s and %s are different"
        id1.id_string id2.id_string
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
  | Decl.NonExhaustiveExpr (pl, e) ->
      fprintf fmt
        "Non-exhaustive pattern list:@\n@[<hov 2>%a@]@\nin expression %a"
        (print_list newline print_pat) pl print_expr e
  | _ -> raise exn
  end

