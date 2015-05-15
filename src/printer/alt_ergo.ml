(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Alt-ergo printer *)

open Format
open Pp
open Ident
open Ty
open Term
open Decl
open Printer

let meta_ac = Theory.register_meta "AC" [Theory.MTlsymbol]
  ~desc:"Specify@ that@ a@ symbol@ is@ associative@ and@ commutative."

let meta_printer_option =
  Theory.register_meta "printer_option" [Theory.MTstring]
    ~desc:"Pass@ additional@ parameters@ to@ the@ pretty-printer."

let meta_invalid_trigger =
  Theory.register_meta "invalid trigger" [Theory.MTlsymbol]
  ~desc:"Specify@ that@ a@ symbol@ is@ not@ allowed@ in@ a@ trigger."

type info = {
  info_syn : syntax_map;
  info_ac  : Sls.t;
  info_show_labels : bool;
  info_type_casts : bool;
  info_csm : lsymbol list Mls.t;
  info_pjs : Sls.t;
  info_axs : Spr.t;
  info_inv_trig : Sls.t;
}

let ident_printer =
  let bls = [
    "ac"; "and"; "array"; "as"; "axiom"; "bitv"; "bool";
    "check"; "cut"; "distinct"; "else"; "exists";
    "false"; "forall"; "function"; "goal";
    "if"; "in"; "include"; "int"; "inversion";
    "let"; "logic"; "not"; "or"; "parameter"; "predicate";
    "prop"; "real"; "rewriting"; "select"; "store";
    "then"; "true"; "type"; "unit"; "void"; "with";
  ]
  in
  let san = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer bls ~sanitizer:san

let print_ident fmt id =
  fprintf fmt "%s" (id_unique ident_printer id)

let print_label fmt l =
  fprintf fmt "\"%s\"" l.lab_string

let print_ident_label info fmt id =
  if info.info_show_labels then
    fprintf fmt "%s %a"
      (id_unique ident_printer id)
      (print_list space print_label) (Slab.elements id.id_label)
  else
    print_ident fmt id

let forget_var v = forget_id ident_printer v.vs_name

(*
let tv_printer =
  let san = sanitizer char_to_lalpha char_to_alnumus in
  create_ident_printer [] ~sanitizer:san

let print_tvsymbol fmt tv =
  fprintf fmt "'%s" (id_unique tv_printer tv.tv_name)

let forget_tvs () = forget_all tv_printer
*)

(* work around a "duplicate type variable" bug of Alt-Ergo 0.94 *)
let print_tvsymbol, forget_tvs =
  let htv = Hid.create 5 in
  (fun fmt tv ->
    Hid.replace htv tv.tv_name ();
    fprintf fmt "'%s" (id_unique ident_printer tv.tv_name)),
  (fun () ->
    Hid.iter (fun id _ -> forget_id ident_printer id) htv;
    Hid.clear htv)

let rec print_type info fmt ty = match ty.ty_node with
  | Tyvar id ->
      print_tvsymbol fmt id
  | Tyapp (ts, tl) -> begin match query_syntax info.info_syn ts.ts_name with
      | Some s -> syntax_arguments s (print_type info) fmt tl
      | None -> fprintf fmt "%a%a" (print_tyapp info) tl print_ident ts.ts_name
    end

and print_tyapp info fmt = function
  | [] -> ()
  | [ty] -> fprintf fmt "%a " (print_type info) ty
  | tl -> fprintf fmt "(%a) " (print_list comma (print_type info)) tl

let rec print_term info fmt t = match t.t_node with
  | Tconst c ->
      let number_format = {
          Number.long_int_support = true;
          Number.extra_leading_zeros_support = true;
          Number.dec_int_support = Number.Number_default;
          Number.hex_int_support = Number.Number_unsupported;
          Number.oct_int_support = Number.Number_unsupported;
          Number.bin_int_support = Number.Number_unsupported;
          Number.def_int_support = Number.Number_unsupported;
          Number.dec_real_support = Number.Number_default;
          Number.hex_real_support = Number.Number_default;
          Number.frac_real_support = Number.Number_unsupported;
          Number.def_real_support = Number.Number_unsupported;
        } in
      Number.print number_format fmt c
  | Tvar { vs_name = id } ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None when Mls.mem ls info.info_csm ->
          let print_field fmt ({ls_name = id},t) =
            fprintf fmt "%a =@ %a" print_ident id (print_term info) t in
          fprintf fmt "{@ %a@ }" (print_list semi print_field)
            (List.combine (Mls.find ls info.info_csm) tl)
      | None when Sls.mem ls info.info_pjs ->
          fprintf fmt "%a.%a" (print_tapp info) tl print_ident ls.ls_name
      | None when unambig_fs ls || not info.info_type_casts ->
          fprintf fmt "%a%a" print_ident ls.ls_name (print_tapp info) tl
      | None ->
          fprintf fmt "(%a%a : %a)" print_ident ls.ls_name (print_tapp info) tl
             (print_type info) (t_type t)
    end
  | Tlet _ -> unsupportedTerm t
      "alt-ergo : you must eliminate let in term"
  | Tif _ -> unsupportedTerm t
      "alt-ergo : you must eliminate if_then_else"
  | Tcase _ -> unsupportedTerm t
      "alt-ergo : you must eliminate match"
  | Teps _ -> unsupportedTerm t
      "alt-ergo : you must eliminate epsilon"
  | Tquant _ | Tbinop _ | Tnot _ | Ttrue | Tfalse -> raise (TermExpected t)

and print_tapp info fmt = function
  | [] -> ()
  | tl -> fprintf fmt "(%a)" (print_list comma (print_term info)) tl

let rec print_fmla info fmt f =
  if info.info_show_labels then
    match Slab.elements f.t_label with
      | [] -> print_fmla_node info fmt f
      | l ->
        fprintf fmt "(%a : %a)"
          (print_list colon print_label) l
          (print_fmla_node info) f
  else
    print_fmla_node info fmt f

and print_fmla_node info fmt f = match f.t_node with
  | Tapp ({ ls_name = id }, []) ->
      print_ident fmt id
  | Tapp (ls, tl) -> begin match query_syntax info.info_syn ls.ls_name with
      | Some s -> syntax_arguments s (print_term info) fmt tl
      | None -> fprintf fmt "%a(%a)" print_ident ls.ls_name
                    (print_list comma (print_term info)) tl
    end
  | Tquant (q, fq) ->
      let vl, tl, f = t_open_quant fq in
      let q, tl = match q with
        | Tforall -> "forall", tl
        | Texists -> "exists", [] (* Alt-ergo has no triggers for exists *)
      in
      let forall fmt v =
        fprintf fmt "%s %a:%a" q (print_ident_label info) v.vs_name
          (print_type info) v.vs_ty
      in
      fprintf fmt "@[(%a%a.@ %a)@]" (print_list dot forall) vl
        (print_triggers info) tl (print_fmla info) f;
      List.iter forget_var vl
  | Tbinop (Tand, f1, f2) ->
      fprintf fmt "(%a and@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tor, f1, f2) ->
      fprintf fmt "(%a or@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Timplies, f1, f2) ->
      fprintf fmt "(%a ->@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Tbinop (Tiff, f1, f2) ->
      fprintf fmt "(%a <->@ %a)" (print_fmla info) f1 (print_fmla info) f2
  | Tnot f ->
      fprintf fmt "(not %a)" (print_fmla info) f
  | Ttrue ->
      fprintf fmt "true"
  | Tfalse ->
      fprintf fmt "false"
  | Tif (f1, f2, f3) ->
      fprintf fmt "((%a and@ %a)@ or@ (not@ %a and@ %a))"
        (print_fmla info) f1 (print_fmla info) f2 (print_fmla info)
        f1 (print_fmla info) f3
  | Tlet _ -> unsupportedTerm f
      "alt-ergo: you must eliminate let in formula"
  | Tcase _ -> unsupportedTerm f
      "alt-ergo: you must eliminate match"
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)

and print_expr info fmt =
  TermTF.t_select (print_term info fmt) (print_fmla info fmt)

and print_triggers info fmt tl =
  let filter = function
    | { t_ty = Some _ } -> true
    | { t_node = Tapp (ps,_) } -> not (Sls.mem ps info.info_inv_trig)
    | _ -> false in
  let tl = List.map (List.filter filter) tl in
  let tl = List.filter (function [] -> false | _::_ -> true) tl in
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma (print_expr info))) tl

let print_logic_binder info fmt v =
  fprintf fmt "%a: %a" print_ident v.vs_name (print_type info) v.vs_ty

let print_type_decl fmt ts = match ts.ts_args with
  | [] -> fprintf fmt "type %a"
      print_ident ts.ts_name
  | [tv] -> fprintf fmt "type %a %a"
      print_tvsymbol tv print_ident ts.ts_name
  | tl -> fprintf fmt "type (%a) %a"
      (print_list comma print_tvsymbol) tl print_ident ts.ts_name

let print_enum_decl fmt ts csl =
  let print_cs fmt (ls,_) = print_ident fmt ls.ls_name in
  fprintf fmt "@[<hov 2>type %a =@ %a@]@\n@\n" print_ident ts.ts_name
    (print_list alt2 print_cs) csl

let print_ty_decl info fmt ts =
  if ts.ts_def <> None then () else
  if Mid.mem ts.ts_name info.info_syn then () else
  (fprintf fmt "%a@\n@\n" print_type_decl ts; forget_tvs ())

let print_data_decl info fmt = function
  | ts, csl (* monomorphic enumeration *)
    when ts.ts_args = [] && List.for_all (fun (_,l) -> l = []) csl ->
      print_enum_decl fmt ts csl
  | ts, [cs,_] (* non-recursive records *)
    when Mls.mem cs info.info_csm ->
      let pjl = Mls.find cs info.info_csm in
      let print_field fmt ls =
        fprintf fmt "%a@ :@ %a" print_ident ls.ls_name
          (print_type info) (Opt.get ls.ls_value) in
      fprintf fmt "%a@ =@ {@ %a@ }@\n@\n" print_type_decl ts
        (print_list semi print_field) pjl
  | _, _ -> unsupported
      "alt-ergo : algebraic datatype are not supported"

let print_data_decl info fmt ((ts, _csl) as p) =
  if Mid.mem ts.ts_name info.info_syn then () else
  print_data_decl info fmt p

let print_param_decl info fmt ls =
  let sac = if Sls.mem ls info.info_ac then "ac " else "" in
  fprintf fmt "@[<hov 2>logic %s%a : %a%s%a@]@\n@\n"
    sac print_ident ls.ls_name
    (print_list comma (print_type info)) ls.ls_args
    (if ls.ls_args = [] then "" else " -> ")
    (print_option_or_default "prop" (print_type info)) ls.ls_value

let print_param_decl info fmt ls =
  if Mid.mem ls.ls_name info.info_syn || Sls.mem ls info.info_pjs
    then () else (print_param_decl info fmt ls; forget_tvs ())

let print_logic_decl info fmt ls ld =
  let vl,e = open_ls_defn ld in
  begin match e.t_ty with
    | Some _ ->
        (* TODO AC? *)
        fprintf fmt "@[<hov 2>function %a(%a) : %a =@ %a@]@\n@\n"
          print_ident ls.ls_name
          (print_list comma (print_logic_binder info)) vl
          (print_type info) (Opt.get ls.ls_value)
          (print_term info) e
    | None ->
        fprintf fmt "@[<hov 2>predicate %a(%a) =@ %a@]@\n@\n"
          print_ident ls.ls_name
          (print_list comma (print_logic_binder info)) vl
          (print_fmla info) e
  end;
  List.iter forget_var vl

let print_logic_decl info fmt (ls,ld) =
  if Mid.mem ls.ls_name info.info_syn || Sls.mem ls info.info_pjs
    then () else (print_logic_decl info fmt ls ld; forget_tvs ())

let print_prop_decl info fmt k pr f = match k with
  | Paxiom ->
      fprintf fmt "@[<hov 2>axiom %a :@ %a@]@\n@\n"
        print_ident pr.pr_name (print_fmla info) f
  | Pgoal ->
      fprintf fmt "@[<hov 2>goal %a :@ %a@]@\n"
        print_ident pr.pr_name (print_fmla info) f
  | Plemma| Pskip -> assert false

let print_prop_decl info fmt k pr f =
  if Mid.mem pr.pr_name info.info_syn || Spr.mem pr info.info_axs
    then () else (print_prop_decl info fmt k pr f; forget_tvs ())

let print_decl info fmt d = match d.d_node with
  | Dtype ts ->
      print_ty_decl info fmt ts
  | Ddata dl ->
      print_list nothing (print_data_decl info) fmt dl
  | Dparam ls ->
      print_param_decl info fmt ls
  | Dlogic dl ->
      print_list nothing (print_logic_decl info) fmt dl
  | Dind _ -> unsupportedDecl d
      "alt-ergo: inductive definitions are not supported"
  | Dprop (k,pr,f) -> print_prop_decl info fmt k pr f

let add_projection (csm,pjs,axs) = function
  | [Theory.MAls ls; Theory.MAls cs; Theory.MAint ind; Theory.MApr pr] ->
      let csm = try Array.set (Mls.find cs csm) ind ls; csm
      with Not_found ->
        Mls.add cs (Array.make (List.length cs.ls_args) ls) csm in
      csm, Sls.add ls pjs, Spr.add pr axs
  | _ -> assert false

let check_showlabels acc = function
  | [Theory.MAstr "show_labels"] -> true
  | [Theory.MAstr _] -> acc
  | _ -> assert false

let check_typecasts acc = function
  | [Theory.MAstr "no_type_cast"] -> false
  | [Theory.MAstr _] -> acc
  | _ -> assert false

let print_decls =
  let print_decl info fmt d =
    try print_decl info fmt d; info, []
    with Unsupported s -> raise (UnsupportedDecl (d,s)) in
  let print_decl = Printer.sprint_decl print_decl in
  let print_decl task acc = print_decl task.Task.task_decl acc in
  Discriminate.on_syntax_map (fun sm ->
  Trans.on_tagged_ls meta_ac (fun ac ->
  Trans.on_meta meta_printer_option (fun args ->
  Trans.on_meta Eliminate_algebraic.meta_proj (fun mal ->
  Trans.on_tagged_ls meta_invalid_trigger (fun inv_trig ->
    let csm,pjs,axs =
      List.fold_left add_projection (Mls.empty,Sls.empty,Spr.empty) mal in
    let info = {
      info_syn = sm;
      info_ac  = ac;
      info_show_labels = List.fold_left check_showlabels false args;
      info_type_casts = List.fold_left check_typecasts true args;
      info_csm = Mls.map Array.to_list csm;
      info_pjs = pjs;
      info_axs = axs;
      info_inv_trig = Sls.add ps_equ inv_trig;
    } in
    Trans.fold print_decl (info,[]))))))

let print_task args ?old:_ fmt task =
  (* In trans-based p-printing [forget_all] is a no-no *)
  (* forget_all ident_printer; *)
  print_prelude fmt args.prelude;
  print_th_prelude task fmt args.th_prelude;
  let rec print = function
    | x :: r -> print r; Pp.string fmt x
    | [] -> () in
  print (snd (Trans.apply print_decls task));
  pp_print_flush fmt ()

let () = register_printer "alt-ergo" print_task
  ~desc:"Printer for the Alt-Ergo theorem prover."
