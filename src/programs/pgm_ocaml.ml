
open Format
open Why3
open Pp
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Pgm_types.T
open Pgm_ttree
open Pgm_module

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

let extract_op ls =
  let s = ls.ls_name.id_string in
  let len = String.length s in
  if len < 7 then None else
  let inf = String.sub s 0 6 in
  if inf = "infix "  then Some (String.sub s 6 (len - 6)) else
  let prf = String.sub s 0 7 in
  if prf = "prefix " then Some (String.sub s 7 (len - 7)) else
  None

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

let print_ls fmt ls =
  if ls.ls_name.id_string = "mixfix []" then fprintf fmt "([])" else
  if ls.ls_name.id_string = "mixfix [<-]" then fprintf fmt "([<-])" else
  match extract_op ls with
  | Some s -> fprintf fmt "(%s)" (escape_op s)
  | None   -> fprintf fmt "%s" (id_unique iprinter ls.ls_name)

let print_cs fmt ls =
  let sanitizer = String.capitalize in
  fprintf fmt "%s" (id_unique iprinter ~sanitizer ls.ls_name)

let print_ts fmt ts =
  fprintf fmt "%s" (id_unique tprinter ts.ts_name)

let to_be_implemented fmt s =
  fprintf fmt "failwith \"to be implemented\" (* %s *)" s

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let star fmt () = fprintf fmt " *@ "

let rec print_ty_node inn fmt ty = match ty.ty_node with
  | Tyvar v ->
      print_tv fmt v
  | Tyapp (ts, []) when is_ts_tuple ts ->
      fprintf fmt "unit"
  | Tyapp (ts, tl) when is_ts_tuple ts ->
      fprintf fmt "(%a)" (print_list star (print_ty_node false)) tl
  | Tyapp (ts, []) ->
      print_ts fmt ts
  | Tyapp (ts, tl) ->
      fprintf fmt (protect_on inn "(%a)@ %a")
        (print_list comma (print_ty_node false)) tl print_ts ts

let print_ty = print_ty_node false

let print_vsty fmt v =
  fprintf fmt "%a:@,%a" print_vs v print_ty v.vs_ty

let print_tv_arg = print_tv
let print_tv_args fmt = function
  | [] -> ()
  | [tv] -> fprintf fmt "%a@ " print_tv_arg tv
  | tvl -> fprintf fmt "(%a)@ " (print_list comma print_tv_arg) tvl

let print_ty_arg fmt ty = fprintf fmt "%a" (print_ty_node true) ty
let print_vs_arg fmt vs = fprintf fmt "(%a)" print_vsty vs

(* FIXME: print projections! *)
let print_constr ty fmt (cs,_) =
  let ty_val = of_option cs.ls_value in
  let m = ty_match Mtv.empty ty_val ty in
  let tl = List.map (ty_inst m) cs.ls_args in
  match tl with
    | [] ->
        fprintf fmt "@[<hov 4>| %a@]" print_cs cs
    | _ ->
        fprintf fmt "@[<hov 4>| %a of %a@]" print_cs cs
          (print_list star print_ty_arg) tl

let print_type_decl fst fmt (ts,def) = match def with
  | Tabstract -> begin match ts.ts_def with
      | None ->
          fprintf fmt "@[<hov 2>%s %a%a@]"
            (if fst then "type" else "and")
            print_tv_args ts.ts_args print_ts ts
      | Some ty ->
          fprintf fmt "@[<hov 2>%s %a%a =@ %a@]"
            (if fst then "type" else "and")
            print_tv_args ts.ts_args print_ts ts print_ty ty
      end
  | Talgebraic csl ->
      let ty = ty_app ts (List.map ty_var ts.ts_args) in
      fprintf fmt "@[<hov 2>%s %a%a =@\n@[<hov>%a@]@]"
        (if fst then "type" else "and")
        print_tv_args ts.ts_args print_ts ts
        (print_list newline (print_constr ty)) csl

let print_type_decl first fmt d =
  print_type_decl first fmt d; forget_tvs ()

(** Inductive *)

let name_args l =
  let r = ref 0 in
  let mk ty = incr r; create_vsymbol (id_fresh "x") ty in
  List.map mk l

let print_ind_decl fst fmt (ps,_) =
  let vars = name_args ps.ls_args in
  fprintf fmt "@[<hov 2>%s %a %a : bool =@ @[<hov>%a@]@]"
    (if fst then "let rec" else "and") print_ls ps
    (print_list space print_vs_arg) vars
    to_be_implemented "inductive";
  forget_vars vars

let print_ind_decl first fmt d =
  print_ind_decl first fmt d; forget_tvs ()

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

let print_const = Pretty.print_const

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

let rec print_pat_node pri fmt p = match p.pat_node with
  | Term.Pwild ->
      fprintf fmt "_"
  | Term.Pvar v ->
      print_vs fmt v
  | Term.Pas (p, v) ->
      fprintf fmt (protect_on (pri > 1) "%a as %a")
        (print_pat_node 1) p print_vs v
  | Term.Por (p, q) ->
      fprintf fmt (protect_on (pri > 0) "%a | %a")
        (print_pat_node 0) p (print_pat_node 0) q
  | Term.Papp (cs, pl) when is_fs_tuple cs ->
      fprintf fmt "(%a)"
        (print_list comma (print_pat_node 1)) pl
  | Term.Papp (cs, []) ->
      print_cs fmt cs
  | Term.Papp (cs, pl) ->
      fprintf fmt (protect_on (pri > 1) "%a@ (%a)")
        print_cs cs (print_list comma (print_pat_node 2)) pl

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

let rec print_term fmt t =
  print_lterm 0 fmt t

and print_lterm pri fmt t =
  print_tnode pri fmt t

and print_app pri ls fmt tl = match extract_op ls, tl with
  | _, [] ->
      print_ls fmt ls
  | Some s, [t1] when tight_op s ->
      fprintf fmt (protect_on (pri > 7) "%s%a")
        s (print_lterm 7) t1
  | Some s, [t1] ->
      fprintf fmt (protect_on (pri > 4) "%s %a")
        s (print_lterm 5) t1
  | Some s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 4) "@[<hov 1>%a %s@ %a@]")
        (print_lterm 5) t1 s (print_lterm 5) t2
  | _, [t1;t2] when ls.ls_name.id_string = "mixfix []" ->
      fprintf fmt (protect_on (pri > 6) "%a[%a]")
        (print_lterm 6) t1 print_term t2
  | _, [t1;t2;t3] when ls.ls_name.id_string = "mixfix [<-]" ->
      fprintf fmt (protect_on (pri > 6) "%a[%a <- %a]")
        (print_lterm 6) t1 (print_lterm 5) t2 (print_lterm 5) t3
  | _, tl ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a@ %a@]")
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
  | Teps _
  | Tquant _ ->
      assert false
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tbinop (Timplies,f1,f2) ->
      fprintf fmt "(not (%a) || (%a))" print_term f1 print_term f2
  | Tbinop (b,f1,f2) ->
      let p = prio_binop b in
      fprintf fmt (protect_on (pri > p) "@[<hov 1>%a %a@ %a@]")
        (print_lterm (p + 1)) f1 print_binop b (print_lterm p) f2
  | Tnot f ->
      fprintf fmt (protect_on (pri > 4) "not %a") (print_lterm 4) f

and print_tbranch fmt br =
  let p,t = t_open_branch br in
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_term t;
  Svs.iter forget_var p.pat_vars

and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_term)) tl


let print_ls_type fmt = function
  | None -> fprintf fmt "bool"
  | Some ty -> print_ty fmt ty

let print_defn fmt e =
  if is_exec_term e then print_term fmt e
  else to_be_implemented fmt "not executable"

let print_logic_decl fst fmt (ls,ld) = match ld with
  | Some ld ->
      let vl,e = open_ls_defn ld in
      fprintf fmt "@[<hov 2>%s %a %a : %a =@ %a@]"
        (if fst then "let rec" else "and") print_ls ls
        (print_list space print_vs_arg) vl
        print_ls_type ls.ls_value print_defn e;
      forget_vars vl
  | None ->
      let vars = name_args ls.ls_args in
      fprintf fmt "@[<hov 2>%s %a %a : %a =@ %a@]"
        (if fst then "let rec" else "and") print_ls ls
        (print_list space print_vs_arg) vars
        print_ls_type ls.ls_value
        to_be_implemented "uninterpreted symbol";
      forget_vars vars

let print_logic_decl first fmt d =
  print_logic_decl first fmt d; forget_tvs ()

(** Logic Declarations *)

let print_list_next sep print fmt = function
  | [] ->
      ()
  | [x] ->
      print true fmt x
  | x :: r ->
      print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let logic_decl fmt d = match d.d_node with
  | Dtype tl ->
      print_list_next newline print_type_decl fmt tl
  | Dlogic ll ->
      print_list_next newline print_logic_decl fmt ll
  | Dind il ->
      print_list_next newline print_ind_decl fmt il
  | Dprop (pk, pr, _) ->
      fprintf fmt "(* %a %a *)" Pretty.print_pkind pk Pretty.print_pr pr

let logic_tdecl fmt td = match td.td_node with
  | Decl d ->
      logic_decl fmt d
  | Use th ->
      fprintf fmt "(* use %a *)" print_ident th.th_name
  | Clone (th, _) ->
      fprintf fmt "(* clone %a *)" print_ident th.th_name
  | Meta _ ->
      fprintf fmt "(* meta *)"

(** Theories *)

let extract_theory _path _th =
  assert false (*TODO*)

(** Program Expression *)

let rec print_expr fmt e = match e.expr_desc with
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

(** Program Declarations *)

let decl fmt = function
  | Dlet (ps, e) ->
      fprintf fmt "@[<hov 2>let %a =@ %a@]"
        print_ls ps.ps_pure print_expr e
  | Dletrec _dl ->
      fprintf fmt "(* pgm let rec *)" (* TODO *)
  | Dparam ps ->
      print_logic_decl true fmt (ps.ps_pure, None)

(** Modules *)

let extract_module_to m fmt =
  (* extract all logic decls first *)
  print_list newline2 logic_tdecl fmt m.m_pure.th_decls;
  fprintf fmt "@\n@\n";
  (* then program decls *)
  print_list newline2 decl fmt m.m_decls;
  fprintf fmt "@."

let extract_module path m =
  let id = m.m_name.id_string in
  eprintf "extract_module %s [path = %a]@."
    id (print_list space pp_print_string) path;
  if is_stdlib path id then
    eprintf "  standard library@."
  else begin
    let file = "/tmp/" ^ id ^ ".ml" in
    eprintf "  to file %s@." file;
    print_in_file (extract_module_to m) file
  end

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
