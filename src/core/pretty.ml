(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Pp
open Wstdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Task

let why3_keywords = Keywords.keywords

let coercion_attr = create_attribute "coercion"

let prio_binop = function
  | Tand -> 4
  | Tor -> 3
  | Timplies -> 1
  | Tiff -> 1

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

type any_pp =
  | Pp_term of (Term.term * int) (* term and priority *)
  | Pp_ty of (Ty.ty * int * bool) (* ty * prio * q *)
  | Pp_decl of (bool * Ty.tysymbol * (Term.lsymbol * Term.lsymbol option list) list)
    (* [Pp_decl (fst, ts, csl)]: Declaration of type [ts] with constructors
       [csl] as [fst] *)
  | Pp_ts of Ty.tysymbol (* Print tysymbol *)
  | Pp_ls of Term.lsymbol (* Print lsymbol *)
  | Pp_id of Ident.ident (* Print ident *)
  | Pp_cs of Term.lsymbol (* Print constructor *)
  | Pp_vs of Term.vsymbol (* Print vsymbol *)
  | Pp_trigger of Term.trigger (* Print triggers *)
  | Pp_forget of Term.vsymbol list (* Forget all the vsymbols listed *)
  | Pp_forget_tvs (* execute forget_tvs *)


module type Printer = sig

    val tprinter : ident_printer  (* type symbols *)
    val aprinter : ident_printer  (* type variables *)
    val sprinter : ident_printer  (* variables and functions *)
    val pprinter : ident_printer  (* proposition names *)

    val forget_all : unit -> unit     (* flush id_unique *)
    val forget_tvs : unit -> unit     (* flush id_unique for type vars *)
    val forget_var : vsymbol -> unit  (* flush id_unique for a variable *)

    val print_id_attrs : formatter -> ident -> unit   (* attributes and location *)

    val print_tv : formatter -> tvsymbol -> unit      (* type variable *)
    val print_vs : formatter -> vsymbol -> unit       (* variable *)

    val print_ts : formatter -> tysymbol -> unit      (* type symbol *)
    val print_ls : formatter -> lsymbol -> unit       (* logic symbol *)
    val print_cs : formatter -> lsymbol -> unit       (* constructor symbol *)
    val print_pr : formatter -> prsymbol -> unit      (* proposition name *)
    val print_th : formatter -> theory -> unit        (* theory name *)

    val print_ty : formatter -> ty -> unit            (* type *)
    val print_vsty : formatter -> vsymbol -> unit     (* variable : type *)

    val print_ts_qualified : formatter -> tysymbol -> unit
    val print_ls_qualified : formatter -> lsymbol -> unit
    val print_cs_qualified : formatter -> lsymbol -> unit
    val print_pr_qualified : formatter -> prsymbol -> unit
    val print_th_qualified : formatter -> theory -> unit
    val print_ty_qualified : formatter -> ty -> unit
    val print_vs_qualified : formatter -> vsymbol -> unit
    val print_tv_qualified : formatter -> tvsymbol -> unit

    val print_quant : formatter -> quant -> unit      (* quantifier *)
    val print_binop : asym:bool -> formatter -> binop -> unit (* binary operator *)
    val print_pat : formatter -> pattern -> unit      (* pattern *)
    val print_term : formatter -> term -> unit   (* term *)

    val print_attr : formatter -> attribute -> unit
    val print_attrs : formatter -> Sattr.t -> unit
    val print_loc_as_attribute : formatter -> Loc.position -> unit
    val print_pkind : formatter -> prop_kind -> unit
    val print_meta_arg : formatter -> meta_arg -> unit
    val print_meta_arg_type : formatter -> meta_arg_type -> unit

    val print_ty_decl : formatter -> tysymbol -> unit
    val print_data_decl : formatter -> data_decl -> unit
    val print_param_decl : formatter -> lsymbol -> unit
    val print_logic_decl : formatter -> logic_decl -> unit
    val print_ind_decl : ind_sign -> formatter -> ind_decl -> unit
    val print_next_data_decl : formatter -> data_decl -> unit
    val print_next_logic_decl : formatter -> logic_decl -> unit
    val print_next_ind_decl : formatter -> ind_decl -> unit
    val print_prop_decl : formatter -> prop_decl -> unit

    val print_decl : formatter -> decl -> unit
    val print_tdecl : formatter -> tdecl -> unit

    val print_task : formatter -> task -> unit
    val print_sequent : formatter -> task -> unit

    val print_theory : formatter -> theory -> unit

    val print_namespace : string -> formatter -> theory -> unit

  end

let debug_print_attrs = Debug.register_info_flag "print_attributes"
    ~desc:"Print@ attributes@ of@ identifiers@ and@ expressions."

let debug_print_locs = Debug.register_info_flag "print_locs"
  ~desc:"Print@ locations@ of@ identifiers@ and@ expressions."

let debug_print_types = Debug.register_info_flag "print_types"
    ~desc:"Print@ types@ of@ terms"

let debug_print_coercions = Debug.register_info_flag "print_coercions"
  ~desc:"Print@ coercions@ in@ logical@ formulas."

(* always print qualified?
let debug_print_qualifs = Debug.register_info_flag "print_qualifs"
  ~desc:"Print@ qualifiers@ of@ identifiers@ in@ error@ messages."*)

let create
      ?(print_ext_any = (fun (printer: any_pp Pp.pp) -> printer))
      ?(do_forget_all = true) ?(shorten_axioms = false)
      ?(show_uses_clones_metas = true) sprinter aprinter tprinter pprinter =
  (module (struct

(* Using a reference for customized external printer. This avoids changing the
   rest of this module to make it recursive with print_any *)
let print_any_ref = ref None

let set_print_any (f: any_pp Pp.pp) =
  print_any_ref := Some f

let get_print_any () =
  match !print_any_ref with
  | None -> (* As soon as the module is created the only call to set_print_any
               is executed so there is always a value in this reference *)
      assert false
  | Some f -> f

let forget_tvs () =
  (* we always forget type variables between each declaration *)
  (* if do_forget_all then *) forget_all aprinter

let forget_all () =
  if do_forget_all then forget_all sprinter;
  if do_forget_all then forget_all aprinter;
  if do_forget_all then forget_all tprinter;
  if do_forget_all then forget_all pprinter

let print_attr fmt a =
  (* `%@` prints a single `@` *)
  fprintf fmt "[%@%s]" a.attr_string

let print_attrs = print_iter1 Sattr.iter space print_attr

let print_loc_as_attribute fmt l =
  let (f,bl,bc,el,ec) = Loc.get l in
  fprintf fmt "#\"%s\" %d %d %d %d#" f bl bc el ec

let print_id_attrs fmt id =
  if Debug.test_flag debug_print_attrs &&
      not (Sattr.is_empty id.id_attrs) then
    fprintf fmt "@ %a" print_attrs id.id_attrs;
  if Debug.test_flag debug_print_locs then
    Opt.iter (fprintf fmt "@ %a" print_loc_as_attribute) id.id_loc

(* type variables always start with a quote *)
let print_tv fmt tv =
  fprintf fmt "'%s" (id_unique aprinter tv.tv_name)

(* logic variables always start with a lower case letter *)
let print_vs fmt vs =
  let sanitizer = Strings.uncapitalize in
  Ident.print_decoded fmt (id_unique sprinter ~sanitizer vs.vs_name)

let forget_var vs = forget_id sprinter vs.vs_name

(* theory names always start with an upper case letter *)
let print_th fmt th =
  let sanitizer = Strings.capitalize in
  pp_print_string fmt (id_unique sprinter ~sanitizer th.th_name)

let print_ts fmt ts =
  if ts_equal ts ts_func then pp_print_string fmt "(->)" else
  pp_print_string fmt (id_unique tprinter ts.ts_name)

let print_cs fmt ls =
  let sanitizer = Strings.capitalize in
  pp_print_string fmt (id_unique sprinter ~sanitizer ls.ls_name)

let print_ls fmt ls =
  Ident.print_decoded fmt (id_unique sprinter ls.ls_name)

let print_pr fmt pr =
  Ident.print_decoded fmt (id_unique pprinter pr.pr_name)

let print_qualified decode fmt id =
(* if Debug.test_noflag debug_print_qualifs then raise Not_found; *)
  let dot fmt () =
    pp_print_char fmt '.'; pp_print_cut fmt () in
  let str fmt s =
    if String.contains s ' ' || String.contains s '.' then begin
      pp_print_char fmt '"'; pp_print_string fmt s; pp_print_char fmt '"'
    end else pp_print_string fmt s;
    dot fmt () in
  let lp, tn, qn = Theory.restore_path id (* raises Not_found *) in
  let qn = match lp with
    | "why3"::_ -> if qn = [] then [tn] (* theory *) else qn
    | _ -> print_list Pp.nothing str fmt lp; tn::qn in
  if decode then match List.rev qn with
    | [sn] ->
        Ident.print_decoded fmt sn
    | sn::qn ->
        print_list dot pp_print_string fmt (List.rev qn); dot fmt ();
        Ident.print_decoded fmt sn
    | [] -> ()
  else
    print_list dot pp_print_string fmt qn

let print_th_qualified fmt th =
  try print_qualified false fmt th.th_name with Not_found -> print_th fmt th

let print_ts_qualified fmt ts =
  if ts_equal ts ts_func then pp_print_string fmt "(->)" else
  try print_qualified false fmt ts.ts_name with Not_found -> print_ts fmt ts

let print_cs_qualified fmt ls =
  try print_qualified false fmt ls.ls_name with Not_found -> print_cs fmt ls

let print_ls_qualified fmt ls =
  try print_qualified true fmt ls.ls_name with Not_found -> print_ls fmt ls

let print_pr_qualified fmt pr =
  try print_qualified true fmt pr.pr_name with Not_found -> print_pr fmt pr

let print_vs_qualified fmt vs =
  try print_qualified true fmt vs.vs_name with Not_found -> print_vs fmt vs

let print_tv_qualified fmt tv =
  try print_qualified true fmt tv.tv_name with Not_found -> print_tv fmt tv

(** Types *)

let rec print_ty_node ?(ext_printer=true) q pri fmt ty =
  if ext_printer then
    let print_any = get_print_any () in
    print_ext_any print_any fmt (Pp_ty (ty, pri, q))
  else begin match ty.ty_node with
  | Tyvar v -> print_tv fmt v
  | Tyapp (ts, [t1;t2]) when ts_equal ts Ty.ts_func ->
      fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_ty_node q 1) t1 (print_ty_node q 0) t2
  | Tyapp (ts, []) when is_ts_tuple ts ->
      pp_print_string fmt "unit"
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      fprintf fmt "(%a)" (print_list comma (print_ty_node q 0)) tl
  | Tyapp (ts, []) ->
      if q then print_ts_qualified fmt ts else print_ts fmt ts
  | Tyapp (ts, tl) -> fprintf fmt (protect_on (pri > 1) "%a@ %a")
      (if q then print_ts_qualified else print_ts) ts
      (print_list space (print_ty_node q 2)) tl
  end

let print_ty fmt ty = print_ty_node false 0 fmt ty

let print_ty_qualified fmt ty = print_ty_node true 0 fmt ty

let print_vsty fmt v =
  fprintf fmt "%a%a:@,%a" print_vs v
    print_id_attrs v.vs_name print_ty v.vs_ty

let print_tv_arg fmt tv = fprintf fmt "@ %a" print_tv tv
let print_ty_arg fmt ty = fprintf fmt "@ %a" (print_ty_node false 2) ty
let print_vs_arg fmt vs = fprintf fmt "@ (%a)" print_vsty vs

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
      pp_print_string fmt "_"
  | Pvar v ->
      print_vs fmt v; print_id_attrs fmt v.vs_name
  | Pas (p, v) ->
      fprintf fmt (protect_on (pri > 1) "%a as %a%a")
        (print_pat_node 1) p print_vs v print_id_attrs v.vs_name
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

let print_quant fmt = function
  | Tforall -> pp_print_string fmt "forall"
  | Texists -> pp_print_string fmt "exists"

let print_binop ~asym fmt = function
  | Tand when asym -> pp_print_string fmt "&&"
  | Tor when asym -> pp_print_string fmt "||"
  | Tand -> pp_print_string fmt "/\\"
  | Tor -> pp_print_string fmt "\\/"
  | Timplies -> pp_print_string fmt "->"
  | Tiff -> pp_print_string fmt "<->"

let rec print_term fmt t =
  print_lterm 0 fmt t

and print_lterm pri fmt t =
  let print_tattr pri fmt t =
    if Debug.test_flag debug_print_attrs && not (Sattr.is_empty t.t_attrs)
    then fprintf fmt (protect_on (pri > 0) "@[<hov 0>%a@ %a@]")
      print_attrs t.t_attrs (print_tnode 0) t
    else print_tnode pri fmt t in
  let print_tloc pri fmt t =
    if Debug.test_flag debug_print_locs && t.t_loc <> None
    then fprintf fmt (protect_on (pri > 0) "@[<hov 0>%a@ %a@]")
      (print_option print_loc_as_attribute) t.t_loc (print_tattr 0) t
    else print_tattr pri fmt t in
  let print_types pri fmt t =
    if Debug.test_flag debug_print_types && t.t_ty <> None
    then fprintf fmt (protect_on (pri > 0) "(%a: %a)")
        (print_tloc 0) t (print_option print_ty) t.t_ty
    else print_tloc pri fmt t in
  print_types pri fmt t

and print_app pri ls fmt tl =
  if tl = [] then print_ls fmt ls else
  let s = id_unique sprinter ls.ls_name in
  match Ident.sn_decode s, tl with
  | Ident.SNtight s, [t1] ->
      fprintf fmt (protect_on (pri > 8) "@[%s%a@]")
        s (print_lterm 8) t1
  | Ident.SNprefix s, [t1] ->
      let lspace p = if p.[0] = '*' then " " else "" in
      fprintf fmt (protect_on (pri > 5) "@[%s%s %a@]")
        (lspace s) s (print_lterm 6) t1
  | Ident.SNinfix s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 5) "@[%a@ %s %a@]")
        (print_lterm 6) t1 s (print_lterm 6) t2
  | Ident.SNget s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 7) "@[%a@,[%a]%s@]")
        (print_lterm 7) t1 print_term t2 s
  | Ident.SNupdate s, [t1;t2;t3] ->
      fprintf fmt (protect_on (pri > 7) "@[%a@,[%a <-@ %a]%s@]")
        (print_lterm 7) t1 (print_lterm 6) t2 (print_lterm 6) t3 s
  | Ident.SNset s, [t1;t2;t3] ->
      fprintf fmt (protect_on (pri > 5) "@[%a@,[%a]%s <-@ %a@]")
        (print_lterm 6) t1 print_term t2 s (print_lterm 6) t3
  | Ident.SNcut s, [t1;t2;t3] ->
      fprintf fmt (protect_on (pri > 7) "%a[%a..%a]%s")
        (print_lterm 7) t1 (print_lterm 6) t2 (print_lterm 6) t3 s
  | Ident.SNrcut s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 7) "%a[%a..]%s")
        (print_lterm 7) t1 print_term t2 s
  | Ident.SNlcut s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 7) "%a[..%a]%s")
        (print_lterm 7) t1 print_term t2 s
  | Ident.SNword s, [t] when Sattr.mem is_field_id_attr ls.ls_name.id_attrs ->
     fprintf fmt (protect_on (pri > 6) "@[%a.%s@]")
       print_term t s
  | Ident.SNword s, tl ->
      fprintf fmt (protect_on (pri > 6) "@[%s@ %a@]")
        s (print_list space (print_lterm 7)) tl
  | (Ident.SNtight s | SNprefix s | SNinfix s
     | SNget s | SNupdate s | SNset s
     | SNcut s | SNrcut s | SNlcut s), tl ->
     (* do not fail, just print the string *)
     fprintf fmt (protect_on (pri > 6) "@[(*Pretty.print_app: unexpected case*)%s@ %a@]")
       s (print_list space (print_lterm 7)) tl

and print_tnode ?(ext_printer=true) pri fmt t =
  if ext_printer then
    let print_any = get_print_any () in
    print_ext_any print_any fmt (Pp_term (t, pri))
  else begin
    match t.t_node with
    | Tvar v ->
        print_vs fmt v
    | Tconst c ->
        begin
          match t.t_ty with
          | Some {ty_node = Tyapp (ts,[])}
            when ts_equal ts ts_int || ts_equal ts ts_real ->
              Constant.print_def fmt c
          | Some ty -> fprintf fmt "(%a:%a)" Constant.print_def c
                         print_ty ty
          | None -> assert false
        end
    | Tapp (_, [t1]) when Sattr.mem coercion_attr t.t_attrs &&
                          Debug.test_noflag debug_print_coercions ->
        print_lterm pri fmt (t_attr_set t1.t_attrs t1)
    | Tapp (fs, tl) when is_fs_tuple fs ->
        fprintf fmt "(%a)" (print_list comma print_term) tl
    | Tapp (fs, [t1;t2]) when ls_equal fs ps_equ ->
        fprintf fmt (protect_on (pri > 6) "@[%a =@ %a@]")
          (print_lterm 6) t1 (print_lterm 6) t2
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
          print_vs v print_id_attrs v.vs_name (print_lterm 5) t1 print_term t2;
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
          fprintf fmt (protect_on (pri > 0) "@[<hov 1>fun%a%a ->@ %a@]")
            (print_list nothing print_vs_arg) vl print_tl tl print_term e;
          List.iter forget_var vl
        end
    | Tquant (q,fq) ->
        let vl,tl,f = t_open_quant fq in
        fprintf fmt (protect_on (pri > 0) "@[<hov 1>%a %a%a.@ %a@]") print_quant q
          (print_list comma print_vsty) vl print_tl tl print_term f;
        List.iter forget_var vl
    | Ttrue ->
        pp_print_string fmt "true"
    | Tfalse ->
        pp_print_string fmt "false"
    | Tbinop (Tand,f1,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) })
      when Sattr.mem Term.asym_split f2.t_attrs ->
        fprintf fmt (protect_on (pri > 1) "@[<hov 1>%a so@ %a@]")
          (print_lterm 2) f1 (print_lterm 1) f2
    | Tbinop (Timplies,{ t_node = Tbinop (Tor,f2,{ t_node = Ttrue }) },f1)
      when Sattr.mem Term.asym_split f2.t_attrs ->
        fprintf fmt (protect_on (pri > 1) "@[<hov 1>%a by@ %a@]")
          (print_lterm 2) f1 (print_lterm 1) f2
    | Tbinop (b,f1,f2) ->
        let asym = Sattr.mem Term.asym_split f1.t_attrs in
        let p = prio_binop b in
        fprintf fmt (protect_on (pri > p) "@[%a %a@ %a@]")
          (print_lterm (p + 1)) f1 (print_binop ~asym) b (print_lterm p) f2
    | Tnot f ->
        fprintf fmt (protect_on (pri > 5) "not %a") (print_lterm 5) f
  end

and print_tbranch fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_term t;
  Svs.iter forget_var p.pat_vars

and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_term)) tl

(** Declarations *)

let print_constr fmt (cs,pjl) =
  let add_pj pj ty pjl = (pj,ty)::pjl in
  let print_pj fmt (pj,ty) = match pj with
    | Some ls -> fprintf fmt "@ (%a:@,%a)" print_ls ls print_ty ty
    | None -> print_ty_arg fmt ty
  in
  fprintf fmt "@[<hov 4>| %a%a%a@]" print_cs cs
    print_id_attrs cs.ls_name
    (print_list nothing print_pj)
    (List.fold_right2 add_pj pjl cs.ls_args [])

let print_ty_decl fmt ts =
  let print_def fmt = function
    | NoDef     -> ()
    | Alias ty  -> fprintf fmt " =@ %a" print_ty ty
    | Range ir  ->
        fprintf fmt " =@ <range %s %s>"
          (BigInt.to_string ir.Number.ir_lower)
          (BigInt.to_string ir.Number.ir_upper)
    | Float irf ->
        fprintf fmt " =@ <float %d %d>"
          irf.Number.fp_exponent_digits
          irf.Number.fp_significand_digits
  in
  fprintf fmt "@[<hov 2>type %a%a%a%a@]"
    print_ts ts print_id_attrs ts.ts_name
    (print_list nothing print_tv_arg) ts.ts_args
    print_def ts.ts_def;
  forget_tvs ()

let print_data_decl_aux ?(ext_printer=true) fst fmt (ts,csl) =
  if ext_printer then
    let print_any = get_print_any () in
    print_ext_any print_any fmt (Pp_decl (fst, ts, csl))
  else begin
    fprintf fmt "@[<hov 2>%s %a%a%a =@\n@[<hov>%a@]@]"
      (if fst then "type" else "with") print_ts ts
      print_id_attrs ts.ts_name
      (print_list nothing print_tv_arg) ts.ts_args
      (print_list newline print_constr) csl;
  end;
  forget_tvs ()

let print_ls_type fmt = fprintf fmt " :@ %a" print_ty

let ls_kind ls =
  if ls.ls_value = None then "predicate"
  else if ls.ls_args = [] then "constant" else "function"

let print_param_decl fmt ls =
  fprintf fmt "@[<hov 2>%s %a%a%a%a@]"
    (ls_kind ls) print_ls ls
    print_id_attrs ls.ls_name
    (print_list nothing print_ty_arg) ls.ls_args
    (print_option print_ls_type) ls.ls_value;
  forget_tvs ()

let print_logic_decl fst fmt (ls,ld) =
  let vl,e = open_ls_defn ld in
  fprintf fmt "@[<hov 2>%s %a%a%a%a =@ %a@]"
    (if fst then ls_kind ls else "with") print_ls ls
    print_id_attrs ls.ls_name
    (print_list nothing print_vs_arg) vl
    (print_option print_ls_type) ls.ls_value print_term e;
  List.iter forget_var vl;
  forget_tvs ()

let print_ind fmt (pr,f) =
  fprintf fmt "@[<hov 4>| %a%a :@ %a@]"
    print_pr pr print_id_attrs pr.pr_name print_term f

let ind_sign = function
  | Ind   -> "inductive"
  | Coind -> "coinductive"

let print_ind_decl s fst fmt (ps,bl) =
  fprintf fmt "@[<hov 2>%s %a%a%a =@ @[<hov>%a@]@]"
    (if fst then ind_sign s else "with") print_ls ps
    print_id_attrs ps.ls_name
    (print_list nothing print_ty_arg) ps.ls_args
    (print_list newline print_ind) bl;
  forget_tvs ()

let sprint_pkind = function
  | Paxiom -> "axiom"
  | Plemma -> "lemma"
  | Pgoal  -> "goal"

let print_pkind fmt k = pp_print_string fmt (sprint_pkind k)

let print_axiom fmt (pr, f) =
  (fprintf fmt "@[<hov 2>%a%a :@ %a@]"
       print_pr pr print_id_attrs pr.pr_name print_term f;
     forget_tvs ())

let print_prop_decl fmt (k,pr,f) =
  if shorten_axioms && k == Paxiom &&
       not (Sattr.exists (Ident.attr_equal Ident.useraxiom_attr) pr.pr_name.id_attrs) then
    print_axiom fmt (pr, f)
  else
    (fprintf fmt "@[<hov 2>%a %a%a :@ %a@]" print_pkind k
       print_pr pr print_id_attrs pr.pr_name print_term f;
     forget_tvs ())

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r -> print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let print_decl fmt d = match d.d_node with
  | Dtype ts  -> print_ty_decl fmt ts
  | Ddata tl  ->
      print_list_next newline (print_data_decl_aux ~ext_printer:true) fmt tl
  | Dparam ls -> print_param_decl fmt ls
  | Dlogic ll -> print_list_next newline print_logic_decl fmt ll
  | Dind (s, il) -> print_list_next newline (print_ind_decl s) fmt il
  | Dprop p   -> print_prop_decl fmt p

let print_next_data_decl  = print_data_decl_aux false
let print_data_decl       = print_data_decl_aux true
let print_next_logic_decl = print_logic_decl false
let print_logic_decl      = print_logic_decl true
let print_next_ind_decl   = print_ind_decl Ind false
let print_ind_decl s      = print_ind_decl s true

let print_inst_ty fmt (ts1,ty2) =
  fprintf fmt "type %a%a = %a" print_ts ts1
    (print_list_pre space print_tv) ts1.ts_args
    print_ty ty2; forget_tvs ()

let print_inst_ts fmt (ts1,ts2) =
  fprintf fmt "type %a = %a" print_ts ts1 print_ts ts2

let print_inst_ls fmt (ls1,ls2) =
  fprintf fmt "%s %a = %a" (ls_kind ls1) print_ls ls1 print_ls ls2

let print_inst_pr fmt (pr1,pr2) =
  fprintf fmt "prop %a = %a" print_pr pr1 print_pr pr2

let print_meta_arg_type fmt = function
  | MTty       -> pp_print_string fmt "[type]"
  | MTtysymbol -> pp_print_string fmt "[type symbol]"
  | MTlsymbol  -> pp_print_string fmt "[function/predicate symbol]"
  | MTprsymbol -> pp_print_string fmt "[proposition]"
  | MTstring   -> pp_print_string fmt "[string]"
  | MTint      -> pp_print_string fmt "[integer]"
  | MTid       -> pp_print_string fmt "[identifier]"

let print_meta_arg fmt = function
  | MAty ty -> fprintf fmt "type %a" print_ty ty; forget_tvs ()
  | MAts ts -> fprintf fmt "type %a" print_ts ts
  | MAls ls -> fprintf fmt "%s %a" (ls_kind ls) print_ls ls
  | MApr pr -> fprintf fmt "prop %a" print_pr pr
  | MAstr s -> fprintf fmt "\"%s\"" s
  | MAint i -> pp_print_int fmt i
  | MAid i -> Ident.print_decoded fmt (id_unique sprinter i)

let print_qt fmt th =
  if th.th_path = [] then print_th fmt th else
  fprintf fmt "%a.%a"
    (print_list (constant_string ".") string) th.th_path
    print_th th

let print_tdecl fmt td = match td.td_node with
  | Decl d ->
      fprintf fmt "@\n@[<hov 2>%a@]@\n" print_decl d
  | Use th ->
      if show_uses_clones_metas then
        fprintf fmt "@\n@[<hov 2>(* use %a *)@]@\n" print_qt th
  | Clone (th,sm) ->
      if show_uses_clones_metas then
        let tm = Mts.fold (fun x y a -> (x,y)::a) sm.sm_ts [] in
        let ym = Mts.fold (fun x y a -> (x,y)::a) sm.sm_ty [] in
        let lm = Mls.fold (fun x y a -> (x,y)::a) sm.sm_ls [] in
        let pm = Mpr.fold (fun x y a -> (x,y)::a) sm.sm_pr [] in
        fprintf fmt "@\n@[<hov 2>(* clone %a with %a%a%a%a *)@]@\n"
          print_qt th (print_list_suf comma print_inst_ts) tm
          (print_list_suf comma print_inst_ty) ym
          (print_list_suf comma print_inst_ls) lm
          (print_list_suf comma print_inst_pr) pm
  | Meta (m,al) ->
      if show_uses_clones_metas then
        fprintf fmt "@\n@[<hov 2>(* meta %s%a *)@]@\n"
          m.meta_name
          (print_list_delim ~start:space ~stop:nothing ~sep:comma print_meta_arg) al

let print_theory fmt th =
  let th_decls = th.th_decls in
  fprintf fmt "@[<v 0>theory %a%a@\n@[<v 2>  %a@]@\nend@]@." print_th th
    print_id_attrs th.th_name (print_list nothing print_tdecl) th_decls

let print_task fmt task =
  forget_all ();
  let th_decls = task_tdecls task in
  fprintf fmt "@[<v 0>theory Task@\n@[<v 2>  %a@]@\nend@]@."
  (print_list nothing print_tdecl) th_decls


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
      if ls_equal ls ps_equ then acc else
        Leaf (ls_kind ls ^ " " ^ s) :: acc
    in
    let add_ts s ts acc =
      if ts_equal ts ts_int  then acc else
      if ts_equal ts ts_real then acc else
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

let print_namespace name fmt th =
  let module P = Print_tree.Make(NsTree) in
  fprintf fmt "@[<hov>%a@]@." P.print
    (NsTree.Namespace (name, th.th_export, th.th_known))


(* print task under the form of a sequent, with only local context, for the IDE *)

let print_decl_filter_unused fmt d =
  match d.d_node with
  | (Dparam ls | Dlogic [ls,_]) when Sattr.mem Ident.unused_attr ls.ls_name.Ident.id_attrs ->
      ()
  | Ddata _ | Dtype _ | Dparam _ -> fprintf fmt "@[<v 0>%a@\n@\n@]" print_decl d
  | Dlogic _ -> fprintf fmt "@[<v 0>%a@\n@\n@]" print_decl d  (* TODO filter d ? *)
  | Dind _ -> fprintf fmt "@[<v 0>%a@\n@\n@]" print_decl d (* TODO filter d ? *)
  | Dprop(k,pr,f) ->
      let pol = match k with Pgoal -> true | Paxiom -> false | Plemma -> assert false in
      let f = Term.remove_unused_in_term pol f in
      fprintf fmt "@[<v 0>%a@\n@\n@]" print_prop_decl (k,pr,f)

let rec print_decls_filter_unused fmt dl =
  match dl with
  | [] -> ()
  | [g] ->
      fprintf fmt "------------------------------- Goal --------------------------------@\n@\n";
      print_decl_filter_unused fmt g
  | h::rem ->
      print_decl_filter_unused fmt h;
      print_decls_filter_unused fmt rem


let print_sequent fmt task =
  let ut = Task.used_symbols (Task.used_theories task) in
  fprintf fmt "--------------------------- Local Context ---------------------------@\n@\n";
  print_decls_filter_unused fmt (Task.local_decls task ut)

(* TODO this needs to be completed in the other cases *)
let print_any fmt t =
  match t with
  | Pp_term (t, pri) -> print_tnode ~ext_printer:false pri fmt t
  | Pp_ty (ty, pri, q) -> print_ty_node ~ext_printer:false q pri fmt ty
  | Pp_decl (fst, ts, csl) ->
      print_data_decl_aux ~ext_printer:false fst fmt (ts, csl)
  | Pp_ts ts -> print_ts fmt ts
  | Pp_ls ls -> print_ls fmt ls
  | Pp_id id -> print_id_attrs fmt id
  | Pp_cs cs -> print_cs fmt cs
  | Pp_vs vs -> print_vsty fmt vs
  | Pp_trigger tl -> print_tl fmt tl
  | Pp_forget vl -> List.iter forget_var vl
  | Pp_forget_tvs -> forget_tvs ()


(* When this module is loaded, the function is always set in the reference *)
let () = set_print_any print_any

let sprinter = sprinter
let aprinter = aprinter
let tprinter = tprinter
let pprinter = pprinter

            end) : Printer) (* end of the first class module *)


module LegacyPrinter =
  (val (let sprinter,aprinter,tprinter,pprinter =
    let same = fun x -> x in
    create_ident_printer why3_keywords ~sanitizer:same,
    create_ident_printer why3_keywords ~sanitizer:same,
    create_ident_printer why3_keywords ~sanitizer:same,
    create_ident_printer why3_keywords ~sanitizer:same
  in
  create ~do_forget_all:true ~shorten_axioms:false sprinter aprinter tprinter pprinter))

include LegacyPrinter


(* Exception reporting *)

let print_id fmt id =
  Ident.print_decoded fmt id.id_string

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | Ty.TypeMismatch (t1,t2) ->
      fprintf fmt "Type mismatch between %a and %a"
        print_ty_qualified t1 print_ty_qualified t2
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
      pp_print_string fmt "Unexpected propositional type"
  | Ty.EmptyRange ->
      pp_print_string fmt "Empty integer range"
  | Ty.BadFloatSpec ->
      pp_print_string fmt "Invalid floating point format"
  | Ty.IllegalTypeParameters ->
      pp_print_string fmt "This type cannot have type parameters"
  | Term.BadArity ({ls_args = []} as ls, _) ->
      fprintf fmt "%s %a expects no arguments"
        (if ls.ls_value = None then "Predicate" else "Function") print_ls ls
  | Term.BadArity (ls, app_arg) ->
      let i = List.length ls.ls_args in
      fprintf fmt "%s %a expects %i argument%s but is applied to %i"
        (if ls.ls_value = None then "Predicate" else "Function")
        print_ls ls i (if i = 1 then "" else "s") app_arg
  | Term.EmptyCase ->
      pp_print_string fmt "Empty match expression"
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
  | Term.InvalidIntegerLiteralType ty
  | Term.InvalidRealLiteralType ty
  | Term.InvalidStringLiteralType ty when
         (match ty.ty_node with Tyvar _ -> true | _ -> false) ->
      pp_print_string fmt "literal has an ambiguous type"
  | Term.InvalidIntegerLiteralType ty ->
      fprintf fmt "Cannot cast an integer literal to type %a" print_ty ty
  | Term.InvalidRealLiteralType ty ->
      fprintf fmt "Cannot cast a real literal to type %a" print_ty ty
  | Term.InvalidStringLiteralType ty ->
      fprintf fmt "Cannot cast a string literal to type %a" print_ty ty
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
  | Decl.BadRecordCons (ls, ty) ->
      fprintf fmt "Type %a contains several constructors and cannot be \
                   (de)constructed using curly braces.\n\
                   Function %a is presumably a field of type %a."
        print_ts ty print_ls ls print_ts ty
  | Decl.BadRecordType (ls, ty) ->
      fprintf fmt "Type %a is not a record type or contains an invariant, \
                   it cannot be (de)constructed using curly braces.\n\
                   Function %a is presumably a field of type %a."
        print_ts ty print_ls ls print_ts ty
  | Decl.BadRecordUnnamed (ls, ty) ->
      fprintf fmt "Type %a contains unnamed fields and cannot be \
                   (de)constructed using curly braces.\n\
                   Function %a is presumably a field of type %a."
        print_ts ty print_ls ls print_ts ty
  | Decl.RecordFieldMissing ls ->
      fprintf fmt "Field %a is missing" print_ls ls
  | Decl.DuplicateRecordField ls ->
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
      fprintf fmt "Ident %a is defined twice" Ident.print_decoded id.id_string
  | Decl.EmptyDecl ->
      pp_print_string fmt "Empty declaration"
  | Decl.EmptyAlgDecl ts ->
      fprintf fmt "Algebraic type %a has no constructors" print_ts ts
  | Decl.EmptyIndDecl ls ->
      fprintf fmt "Inductive predicate %a has no constructors" print_ls ls
  | Decl.KnownIdent {id_string = s} ->
      fprintf fmt "Ident %a is already declared" Ident.print_decoded s
  | Decl.UnknownIdent {id_string = s} ->
      fprintf fmt "Ident %a is not yet declared" Ident.print_decoded s
  | Decl.RedeclaredIdent {id_string = s} ->
      fprintf fmt "Ident %a is already declared, with a different declaration"
        Ident.print_decoded s
  | Decl.NoTerminationProof ls ->
      fprintf fmt "Cannot prove termination for %a" print_ls ls
  | Decl.UnexpectedProjOrConstr ls ->
      fprintf fmt "Unexpected projection or constructor symbol %a" print_ls ls
  | NonLocal id -> Format.fprintf fmt
      "Non-local symbol: %a" print_id id
  | CannotInstantiate id -> Format.fprintf fmt
      "Cannot instantiate a defined symbol %a" print_id id
  | BadInstance (BadI id) -> Format.fprintf fmt
      "Illegal instantiation for symbol %a" print_id id
  | BadInstance (BadI_ty_vars ts) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
          extra type variables in the type expression"
        print_ts ts
  | BadInstance (BadI_ty_ner ts) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
          record types cannot be instantiated with type expressions"
        print_ts ts
  | BadInstance (BadI_ty_impure ts) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
          both %a and the refining type expression must be pure"
        print_ts ts print_ts ts
  | BadInstance (BadI_ty_arity ts) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\narity mismatch"
        print_ts ts
  | BadInstance (BadI_ty_rec ts) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
        the refining type must be a non-recursive record"
        print_ts ts
  | BadInstance (BadI_ty_mut_lhs ts) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
        the refinining type must be mutable"
        print_ts ts
  | BadInstance (BadI_ty_mut_rhs ts) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
        the refinining type must be immutable"
        print_ts ts
  | BadInstance (BadI_ty_alias ts) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
        the added fields are aliased with the original fields"
        print_ts ts
  | BadInstance (BadI_field (ts,vs)) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
        field %a not found in the refinining type"
        print_ts ts print_vs vs
  | BadInstance (BadI_field_type (ts,vs)) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
        incompatible types for field %a"
        print_ts ts print_vs vs
  | BadInstance (BadI_field_ghost (ts,vs)) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
        incompatible ghost status for field %a"
        print_ts ts print_vs vs
  | BadInstance (BadI_field_mut (ts,vs)) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
        incompatible mutability status for field %a"
        print_ts ts print_vs vs
  | BadInstance (BadI_field_inv (ts,vs)) -> Format.fprintf fmt
      "Illegal instantiation for type %a:@\n\
        field %a must not appear in the refined invariant"
        print_ts ts print_vs vs
  | BadInstance (BadI_ls_type (ls,ty1,ty2)) -> Format.fprintf fmt
      "Illegal instantiation for %s %a:@\ntype mismatch between %a and %a"
        (if ls.ls_value = None then "predicate" else "function")
        print_ls ls print_ty_qualified ty1 print_ty_qualified ty2
  | BadInstance (BadI_ls_kind ls) -> Format.fprintf fmt
      "Illegal instantiation for %s %a:@\n%s expected"
        (if ls.ls_value = None then "predicate" else "function")
        print_ls ls
        (if ls.ls_value = None then "predicate" else "function")
  | BadInstance (BadI_ls_arity ls) -> Format.fprintf fmt
      "Illegal instantiation for %s %a:@\narity mismatch"
        (if ls.ls_value = None then "predicate" else "function")
        print_ls ls
  | BadInstance (BadI_ls_rs ls) -> Format.fprintf fmt
      "Cannot instantiate %s %a:@\nprogram function %a \
        must be refined instead"
        (if ls.ls_value = None then "predicate" else "function")
        print_ls ls print_ls ls
  | BadInstance (BadI_rs_arity id) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        arity mismatch"
        print_id id
  | BadInstance (BadI_rs_type (id,exn)) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        %a"
        print_id id Exn_printer.exn_printer exn
  | BadInstance (BadI_rs_kind id) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        incompatible kind"
        print_id id
  | BadInstance (BadI_rs_ghost id) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        incompatible ghost status"
        print_id id
  | BadInstance (BadI_rs_mask id) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        incompatible mask"
        print_id id
  | BadInstance (BadI_rs_reads (id,svs)) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        unreferenced external dependencies: %a"
        print_id id (Pp.print_list Pp.space print_vs) (Svs.elements svs)
  | BadInstance (BadI_rs_writes (id,svs)) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        unreferenced write effects in variables: %a"
        print_id id (Pp.print_list Pp.space print_vs) (Svs.elements svs)
  | BadInstance (BadI_rs_taints (id,svs)) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        unreferenced ghost write effects in variables: %a"
        print_id id (Pp.print_list Pp.space print_vs) (Svs.elements svs)
  | BadInstance (BadI_rs_covers (id,svs)) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        unreferenced region modifications in variables: %a"
        print_id id (Pp.print_list Pp.space print_vs) (Svs.elements svs)
  | BadInstance (BadI_rs_resets (id,svs)) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        unreferenced region resets in variables: %a"
        print_id id (Pp.print_list Pp.space print_vs) (Svs.elements svs)
  | BadInstance (BadI_rs_raises (id,sid)) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        unreferenced raised exceptions: %a"
        print_id id (Pp.print_list Pp.space print_id) (Sid.elements sid)
  | BadInstance (BadI_rs_spoils (id,stv)) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        restricted type variables: %a"
        print_id id (Pp.print_list Pp.space print_tv) (Stv.elements stv)
  | BadInstance (BadI_rs_oneway id) -> Format.fprintf fmt
      "Illegal instantiation for program function %a:@\n\
        incompatible termination status"
        print_id id
  | BadInstance (BadI_xs_type id) -> Format.fprintf fmt
      "Illegal instantiation for exception %a:@\n\
        type mismatch"
        print_id id
  | BadInstance (BadI_xs_mask id) -> Format.fprintf fmt
      "Illegal instantiation for exception %a:@\n\
        incompatible mask"
        print_id id
  | CloseTheory ->
      pp_print_string fmt "Cannot close theory: some namespaces are still open"
  | NoOpenedNamespace ->
      pp_print_string fmt "No opened namespaces"
  | ClashSymbol s ->
      Format.fprintf fmt "Symbol %s is already defined in the current scope" s
  | UnknownMeta s ->
      Format.fprintf fmt "Unknown meta-property %s" s
  | KnownMeta m ->
      Format.fprintf fmt "Metaproperty %s is already registered with \
        a conflicting signature" m.meta_name
  | BadMetaArity (m,n) ->
      let i = List.length m.meta_type in
      Format.fprintf fmt "Metaproperty %s expects %d argument%s but \
        is applied to %d" m.meta_name i (if i = 1 then "" else "s") n
  | MetaTypeMismatch (m,t1,t2) ->
      Format.fprintf fmt "Metaproperty %s expects a %a argument but \
        is applied to %a"
        m.meta_name print_meta_arg_type t1 print_meta_arg_type t2
  | RangeConflict ts ->
      Format.fprintf fmt "Conflicting definitions for range type %a"
        print_ts ts
  | FloatConflict ts ->
      Format.fprintf fmt "Conflicting definitions for float type %a"
        print_ts ts
  | ProvedWfConflict ls ->
      Format.fprintf fmt "Conflicting definitions for well-foundedness of relation %a"
        print_ls ls
  | IllFormedWf(pr,ls) ->
      Format.fprintf fmt
        "meta \"vc:proved_wf\" requires that proposition %a has the form (well_founded %a)"
        print_pr pr print_ls ls
  | _ -> raise exn
  end


(* New attribute for plugins (parsing of arguments of transformation when
   printing Ada, python or C *)
let is_syntax_attr a =
  Strings.has_prefix "syntax:" a.attr_string

let get_syntax_attr ~attrs =
  try Some (Sattr.choose (Sattr.filter is_syntax_attr attrs))
  with Not_found -> None

type syntax =
| Is_array of string
| Is_getter of string
| Is_none

let get_element_syntax ~attrs =
  match get_syntax_attr ~attrs with
  | None -> Is_none
  | Some syntax_attr ->
    let splitted1 = Strings.bounded_split ':' syntax_attr.attr_string 3 in
    match splitted1 with
    | ["syntax"; "getter"; name] ->
        Is_getter name
    | ["syntax"; "array"; name] ->
        Is_array name
    | _ -> Is_none
