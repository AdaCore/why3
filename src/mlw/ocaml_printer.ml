(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Printer for extracted OCaml code *)

open Compile
open Format
open Pmodule
open Theory
open Ident
open Pp
open Ity
open Term
open Printer
open Expr
open Ty

type info = {
  info_syn          : syntax_map;
  info_convert      : syntax_map;
  info_current_th   : Theory.theory;
  info_current_mo   : Pmodule.pmodule option;
  info_th_known_map : Decl.known_map;
  info_mo_known_map : Pdecl.known_map;
  info_fname        : string option;
}

module Print = struct

  open ML

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

  let iprinter, aprinter =
    let isanitize = sanitizer char_to_alpha char_to_alnumus in
    let lsanitize = sanitizer char_to_lalpha char_to_alnumus in
    create_ident_printer ocaml_keywords ~sanitizer:isanitize,
    create_ident_printer ocaml_keywords ~sanitizer:lsanitize

  let print_ident fmt id =
    let s = id_unique iprinter id in
    fprintf fmt "%s" s

  (* let print_lident = print_qident ~sanitizer:Strings.uncapitalize *)
  (* let print_uident = print_qident ~sanitizer:Strings.capitalize *)

  let print_tv fmt tv =
    fprintf fmt "'%s" (id_unique aprinter tv.tv_name)

  let protect_on b s =
    if b then "(" ^^ s ^^ ")" else s

  let star fmt () = fprintf fmt " *@ "

  (** Types *)

  let rec print_ty ?(paren=false) fmt = function
    | Tvar tv ->
       print_tv fmt tv
    | Ttuple [] ->
       fprintf fmt "unit"
    | Ttuple tl ->
       fprintf fmt (protect_on paren "@[%a@]")
               (print_list star (print_ty ~paren:false)) tl
    | Tapp (ts, []) ->
       print_ident fmt ts
    | Tapp (ts, [ty]) ->
       fprintf fmt (protect_on paren "%a@ %a")
               (print_ty ~paren:true) ty print_ident ts
    | Tapp (ts, tl) ->
       fprintf fmt (protect_on paren "(%a)@ %a")
               (print_list comma (print_ty ~paren:false)) tl
               print_ident ts

  let print_vsty fmt (v, ty, _) =
    fprintf fmt "%a:@ %a" print_ident v (print_ty ~paren:false) ty

  let print_tv_arg = print_tv
  let print_tv_args fmt = function
    | []   -> ()
    | [tv] -> fprintf fmt "%a@ " print_tv_arg tv
    | tvl  -> fprintf fmt "(%a)@ " (print_list comma print_tv_arg) tvl

  let print_vs_arg fmt vs =
    fprintf fmt "@[(%a)@]" print_vsty vs

  let print_path =
    print_list dot pp_print_string (* point-free *)

  let print_path_id fmt = function
    | [], id -> print_ident fmt id
    | p, id  -> fprintf fmt "%a.%a" print_path p print_ident id

  let print_theory_name fmt th =
    print_path_id fmt (th.th_path, th.th_name)

  let print_module_name fmt m =
    print_theory_name fmt m.mod_theory

  let rec print_pat fmt = function
    | Pwild ->
       fprintf fmt "_"
    | Pident id ->
       print_ident fmt id
    | Pas (p, id) ->
       fprintf fmt "%a as %a" print_pat p print_ident id
    | Por (p1, p2) ->
       fprintf fmt "%a | %a" print_pat p1 print_pat p2
    | Ptuple pl ->
       fprintf fmt "(%a)" (print_list comma print_pat) pl
    | Papp (id, []) ->
       print_ident fmt id
    | Papp (id, [p]) ->
       fprintf fmt "%a %a" print_ident id print_pat p
    | Papp (id, pl) ->
       fprintf fmt "%a (%a)" print_ident id (print_list comma print_pat) pl
    | Precord fl ->
       let print_field fmt (id, p) =
         fprintf fmt "%a = %a" print_ident id print_pat p
       in
       fprintf fmt "{ %a }" (print_list semi print_field) fl

  let print_const fmt c =
    let n = Number.compute_int c in
    let m = BigInt.to_int n in
    fprintf fmt "%d" m

  (** Expressions *)

  let extract_op {id_string = s} =
    try Some (Strings.remove_prefix "infix " s) with Not_found ->
    try Some (Strings.remove_prefix "prefix " s) with Not_found ->
    None

  let pv_name pv = pv.pv_vs.vs_name

  let print_apply info fmt rs pvl =
    let isfield =
      match rs.rs_field with
      | None -> false
      | Some _ -> true
    in
    match extract_op rs.rs_name, pvl with
    | Some o, [t1; t2] ->
       fprintf fmt "@[<hov 1>%a %s %a@]"
         print_pv t1 o print_pv t2
    | _, [] ->
       print_ident fmt rs.rs_name
    | _, [t1] when isfield ->
       fprintf fmt "%a.%a" print_pv t1 print_ident rs.rs_name
    | _, tl ->
       fprintf fmt "@[<hov 2>%a %a@]"
         print_ident rs.rs_name (print_list space print_pv) tl

  let rec print_enode info fmt = function
    | Econst c ->
       fprintf fmt "%a" print_const c
    | Evar pvs ->
       print_ident fmt (pv_name pvs)
    | Elet (pv, e1, e2) ->
       fprintf fmt "@[<hov 2>let @[%a@] =@ @[%a@]@] in@ %a"
         print_ident (pv_name pv) (print_expr info) e1 (print_expr info) e2
    | Eabsurd ->
       fprintf fmt "assert false (* absurd *)"
    | Eapp (s, []) when rs_equal s rs_true ->
       fprintf fmt "true"
    | Eapp (s, []) when rs_equal s rs_false ->
       fprintf fmt "false"
    | Eapp (s, pvl) ->
       print_apply info fmt s pvl
    | Ematch (e, pl) ->
       fprintf fmt "@[begin match @[%a@] with@\n@[<hov>%a@] end@]"
         (print_expr info) e (print_list newline (print_branch info)) pl
    | Eblock [] ->
       fprintf fmt "()"
    | _ -> (* TODO *) assert false

  and print_branch info fmt (p, e) =
    fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p (print_expr info) e

  and print_expr info fmt e =
    print_enode info fmt e.e_node

  let print_type_decl fmt its =
    let print_constr fmt (id, cs_args) =
      match cs_args with
      | [] ->
         fprintf fmt "@[<hov 4>| %a@]"
                 print_ident id (* FIXME: first letter must be uppercase
                                       -> print_uident *)
      | l ->
         fprintf fmt "@[<hov 4>| %a of %a@]"
                 print_ident id (* FIXME: print_uident *)
                 (print_list star (print_ty ~paren:false)) l in
    let print_field fmt (is_mutable, id, ty) =
      fprintf fmt "%s%a: %a;"
              (if is_mutable then "mutable " else "")
              print_ident id
              (print_ty ~paren:false) ty in
    let print_def fmt = function
      | None ->
        ()
      | Some (Ddata csl) ->
        fprintf fmt " =@\n%a" (print_list newline print_constr) csl
      | Some (Drecord fl) ->
        fprintf fmt " = %s{@\n%a@\n}"
          (if its.its_private then "private " else "")
          (print_list newline print_field) fl
      | Some (Dalias ty) ->
        fprintf fmt " =@ %a" (print_ty ~paren:false) ty
    in
    fprintf fmt "@[<hov 2>%s %a%a%a@]"
      (if true then "type" else "and") (* FIXME: mutual recursive types *)
      print_tv_args its.its_args
      print_ident its.its_name  (* FIXME: first letter must be lowercase
                                   -> print_lident *)
      print_def its.its_def

  let print_decl info fmt = function
    | Dlet (isrec, [rs, pvl, e]) ->
       fprintf fmt "@[<hov 2>%s %a@ %a =@ %a@]"
               (if isrec then "let rec" else "let")
               print_ident rs.rs_name
               (print_list space print_vs_arg) pvl
               (print_expr info) e;
       fprintf fmt "@\n@\n"
    | Dtype dl ->
       print_list newline print_type_decl fmt dl;
       fprintf fmt "@\n@\n"
    | Dexn (xs, None) ->
       fprintf fmt "exception %a@\n@\n" print_ident xs.xs_name
    | Dexn (xs, Some t) ->
       fprintf fmt "@[<hov 2>exception %a of %a@]@\n@\n"
               print_ident xs.xs_name (print_ty ~paren:true) t
    | _ -> (* TODO *) assert false

end

let extract_module pargs ?old fmt ({mod_theory = th} as m) =
  ignore (pargs);
  ignore (old);
  ignore (m);
  let info = {
    info_syn          = pargs.Pdriver.syntax;
    info_convert      = pargs.Pdriver.converter;
    info_current_th   = th;
    info_current_mo   = Some m;
    info_th_known_map = th.th_known;
    info_mo_known_map = m.mod_known;
    info_fname        = None; (* TODO *)
  } in
  fprintf fmt "(*@\n%a@\n*)@\n@\n" print_module m;
  fprintf fmt
    "(* This file has been generated from Why3 module %a *)@\n@\n"
    Print.print_module_name m;
  let mdecls = Translate.module_ info m in
  print_list nothing (Print.print_decl info) fmt mdecls;
  fprintf fmt "@."

let fg ?fname m =
  let mod_name = m.Pmodule.mod_theory.Theory.th_name.id_string in
  match fname with
  | None   -> mod_name ^ ".ml"
  | Some f -> (Filename.remove_extension f) ^ "__" ^ mod_name ^ ".ml"

let () = Pdriver.register_printer "ocaml" ~desc:"printer for OCaml code" fg extract_module

(*
 * Local Variables:
 * compile-command: "make -C ../.. -j3 bin/why3extract.opt"
 * End:
 *)
