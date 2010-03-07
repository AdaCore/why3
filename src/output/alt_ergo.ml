
open Format
open Pp
open Ident
open Ty
open Term
open Theory

let ident_printer = 
  let bls = ["let"; "forall"; "exists"; "and"; "or"] in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let forget_var v = forget_id ident_printer v.vs_name

let rec print_type fmt ty = match ty.ty_node with
  | Tyvar id -> 
      fprintf fmt "'%a" print_ident id
  | Tyapp (ts, []) -> 
      print_ident fmt ts.ts_name
  | Tyapp (ts, [ty]) -> 
      fprintf fmt "%a %a" print_type ty print_ident ts.ts_name
  | Tyapp (ts, tyl) ->
      fprintf fmt "(%a) %a" 
	(print_list comma print_type) tyl print_ident ts.ts_name

let rec print_term fmt t = match t.t_node with
  | Tbvar _ -> 
      assert false
  | Tconst (ConstInt s) ->
      fprintf fmt "%s" s
  | Tconst (ConstReal _) ->
      assert false (*TODO*)
  | Tvar { vs_name = id } | Tapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Tapp (ls, tl) ->
      fprintf fmt "%a(%a)" 
	print_ident ls.ls_name (print_list comma print_term) tl
  | Tlet (t1, tb) ->
      let v, t2 = t_open_bound tb in
      fprintf fmt "@[(let %a = %a@ in %a)@]" print_ident v.vs_name
        print_term t1 print_term t2;
      forget_var v
  | Tcase _ ->
      assert false
  | Teps _ ->
      assert false

let rec print_fmla fmt f = match f.f_node with
  | Fapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Fapp (ls, [t1; t2]) when ls == ps_equ ->
      fprintf fmt "(%a = %a)" print_term t1 print_term t2
  | Fapp (ls, tl) ->
      fprintf fmt "%a(%a)" 
	print_ident ls.ls_name (print_list comma print_term) tl
  | Fquant (Fforall, fq) ->
      let vl, tl, f = f_open_quant fq in
      let forall fmt v = 
	fprintf fmt "forall %a:%a" print_ident v.vs_name print_type v.vs_ty
      in
      fprintf fmt "@[<hov2>(%a%a.@ %a)@]" (print_list dot forall) vl
        (print_list alt print_triggers) tl print_fmla f;
      List.iter forget_var vl
  | Fquant (Fexists, fq) ->
      assert false (*TODO*)
  | Fbinop (Fand, f1, f2) ->
      fprintf fmt "(%a and %a)" print_fmla f1 print_fmla f2
  | Fbinop (For, f1, f2) ->
      fprintf fmt "(%a or %a)" print_fmla f1 print_fmla f2
  | Fbinop (Fimplies, f1, f2) ->
      fprintf fmt "(%a -> %a)" print_fmla f1 print_fmla f2
  | Fbinop (Fiff, f1, f2) ->
      fprintf fmt "(%a <-> %a)" print_fmla f1 print_fmla f2
  | Fnot f ->
      fprintf fmt "(not %a)" print_fmla f
  | Ftrue ->
      fprintf fmt "true"
  | Ffalse ->
      fprintf fmt "false"
  | Fif (f1, f2, f3) ->
      fprintf fmt "((%a and %a) or (not %a and %a))"
	print_fmla f1 print_fmla f2 print_fmla f1 print_fmla f3
  | Flet _ ->
      assert false
  | Fcase _ ->
      assert false

and print_trigger fmt = function
  | TrTerm t -> print_term fmt t
  | TrFmla f -> print_fmla fmt f

and print_triggers fmt tl = print_list comma print_trigger fmt tl


let print_logic_binder fmt v =
  fprintf fmt "%a: %a" print_ident v.vs_name print_type v.vs_ty

let print_type_decl fmt = function
  | ts, Tabstract ->
      fprintf fmt "type %a" print_ident ts.ts_name
  | _, Talgebraic _ ->
      assert false

let print_logic_decl fmt = function
  | Lfunction (ls, None) ->
      let tyl = ls.ls_args in
      let ty = match ls.ls_value with None -> assert false | Some ty -> ty in
      fprintf fmt "@[<hov 2>logic %a : %a -> %a@]@\n" print_ident ls.ls_name
	(print_list comma print_type) tyl print_type ty
  | Lfunction (ls, Some defn) ->
      let id = ls.ls_name in
      let _, vl, t = open_fs_defn defn in
      let ty = match ls.ls_value with None -> assert false | Some ty -> ty in
      fprintf fmt "@[<hov 2>function %a(%a) : %a =@ %a@]@\n" print_ident id
        (print_list comma print_logic_binder) vl print_type ty print_term t;
      List.iter forget_var vl
  | Lpredicate _ ->
      assert false (*TODO*)

let print_decl fmt d = match d.d_node with
  | Dtype dl ->
      print_list newline print_type_decl fmt dl
  | Dlogic dl ->
      print_list newline print_logic_decl fmt dl
  | Dind _ ->
      assert false
  | Dprop (Paxiom, pr) ->
      fprintf fmt "@[<hov 2>axiom %a :@ %a@]@\n" 
        print_ident pr.pr_name print_fmla pr.pr_fmla
  | Dprop (Pgoal, pr) ->
      fprintf fmt "@[<hov 2>goal %a :@ %a@]@\n"
        print_ident pr.pr_name print_fmla pr.pr_fmla
  | Dprop (Plemma, _) ->
      assert false
  | Duse _ | Dclone _ ->
      ()

let print_context fmt ctxt = 
  let decls = Context.get_decls ctxt in
  print_list newline2 print_decl fmt decls


let print_goal fmt (id, f, ctxt) =
  print_context fmt ctxt;
  fprintf fmt "@\n@[<hov 2>goal %a : %a@]" print_ident id print_fmla f
