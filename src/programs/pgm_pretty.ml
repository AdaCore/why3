
open Format
open Why
open Pp
open Ident
open Term
open Pretty
open Pgm_types.T
open Pgm_ttree

(* pretty-printing (for debugging) *)

let rec print_expr fmt e = match e.expr_desc with
  | Elogic t ->
      fprintf fmt "@[<hov 2><term: %a>@]" Pretty.print_term t
  | Elocal v ->
      fprintf fmt "%a" print_pv v
  | Eglobal ls ->
      fprintf fmt "<global %a>" print_ls ls.p_ls
  | Efun (bl, t) ->
      fprintf fmt "@[fun %a ->@ %a@]" 
	(print_list space print_pv) bl print_triple t
  | Elet (v, e1, e2) ->
      fprintf fmt "@[<hv 0>@[<hov 2>let %a =@ %a in@]@ %a@]" print_vs v.pv_vs
	print_expr e1 print_expr e2

  | Eif (e1, e2, e3) ->
      fprintf fmt "@[if %a@ then@ %a else@ %a@]"
	print_expr e1 print_expr e2 print_expr e3

  | Eany c ->
      fprintf fmt "@[[any %a]@]" print_type_c c

  | Elabel (_, _)  ->
      fprintf fmt "<todo: Elabel>"
  | Eassert (_, _) ->
      fprintf fmt "<todo: Eassert>"
  | Efor (_, _, _, _, _, _) ->
      fprintf fmt "<todo: Efor>"
  | Etry (_, _) ->
      fprintf fmt "<todo: Etry>"
  | Eraise (_, _)  ->
      fprintf fmt "<todo: Eraise>"
  | Ematch (v, cl) ->
      fprintf fmt "@[<hov 2>match %a with@ %a@]" print_pv v
	(print_list newline print_branch) cl
  | Eloop (_, _) ->
      fprintf fmt "<todo: Eloop>"
  | Eletrec (_, _)  ->
      fprintf fmt "<todo: Eletrec>"
  | Eabsurd ->
      fprintf fmt "absurd"

and print_pv fmt v =
  fprintf fmt "<%s : %a/%a>" 
    v.pv_name.id_string print_ty v.pv_ty print_vs v.pv_vs

and print_triple fmt (p, e, q) =
  fprintf fmt "@[<hv 0>%a@ %a@ %a@]" print_pre p print_expr e print_post q

and print_recfun fmt (v, bl, _, t) =
  fprintf fmt "@[<hov 2>rec %a@ %a =@ %a@]" 
    print_pv v (print_list space print_pv) bl print_triple t

and print_branch fmt (p, e) =
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pattern p print_expr e

and print_pattern fmt p = 
  Pretty.print_pat fmt p.ppat_pat

