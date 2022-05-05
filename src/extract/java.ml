(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2022 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* WhyML to Java translation

* Packages

  Use attribute @java_pkg to indicate the Java package where to extract.
  E.g.

      module M [@java_pkg:foo.bar.gee] ... end
  -->
      package foo.bar.gee;
      public class M { ... }

  in file foo/bar/gee/M.java.

* Classes

  Without any type definition, a module is translated to a class with static
  methods:

      module M let f x = ... end
  -->
      class M { static tau f(tau x) {...} ... }

  With a single type definition, it is translated to a class:

      module T type t = { f1: type1; f2: type2; ... } ... end
  -->
      class T { type1 f1; type2 f2; ... }

  Inside, any function is turned into a method

      module T ... let f (self: t) (x: typex) : typef = ...self.f1... end
  --> class T { typef f(typex x) { ... this.f1 ... } }

* Constructors

* Arithmetic

*)

open Format
open Ident
open Pp
open Ity
open Term
open Expr
open Ty
open Theory
open Pmodule
open Mltree
open Printer

exception Unsupported = Printer.Unsupported

let () = Exn_printer.register (fun fmt e -> match e with
  | Unsupported s -> fprintf fmt "unsupported: %s" s
  | _ -> raise e)

let unsupported s = raise (Unsupported s)

let debug_java_extraction =
  Debug.register_info_flag ~desc:"Java extraction" "java_extraction"

type info = {
  syntax : Printer.syntax_map;
  literal: Printer.syntax_map;
  kn     : Pdecl.known_map;
  prec   : (int list) Mid.t;
}

let java_keywords = [
    "abstract"; "continue"; "for"; "new"; "switch";
    "assert"; "default"; "goto"; "package";  "synchronized";
    "boolean"; "do"; "if"; "private"; "this";
    "break"; "double"; "implements"; "protected"; "throw";
    "byte"; "else"; "import"; "public"; "throws";
    "case"; "enum"; "instanceof"; "return"; "transient";
    "catch"; "extends"; "int"; "short"; "try";
    "char"; "final"; "interface"; "static"; "void";
    "class"; "finally"; "long"; "strictfp"; "volatile";
    "const"; "float"; "native"; "super";  "while";
  ]

(* iprinter: local names
   aprinter: type variables
   tprinter: toplevel definitions *)
let iprinter, aprinter, tprinter =
  let isanitize = sanitizer char_to_alnumus char_to_alnumus in
  let lsanitize = sanitizer char_to_lalnumus char_to_alnumus in
  create_ident_printer java_keywords ~sanitizer:isanitize,
  create_ident_printer java_keywords ~sanitizer:lsanitize,
  create_ident_printer java_keywords ~sanitizer:lsanitize

let forget_id id = forget_id iprinter id
let _forget_ids = List.iter forget_id
let forget_var (id, _, _) = forget_id id
let forget_vars = List.iter forget_var

let print_ident ~sanitizer info fmt id =
  let s = id_unique ~sanitizer iprinter id in
  pp_print_string fmt s
let print_lident = print_ident ~sanitizer:Strings.uncapitalize
(* let print_uident = print_ident ~sanitizer:Strings.capitalize *)

 let pv_name pv = pv.pv_vs.vs_name

let print_tv fmt tv =
  fprintf fmt "%s" (id_unique ~sanitizer:Strings.capitalize aprinter tv.tv_name)

let protect_on ?(boxed=false) ?(be=false) b s =
  if b
  then if be
       then "begin@;<1 2>@["^^ s ^^ "@] end"
       else "@[<1>(" ^^ s ^^ ")@]"
  else if not boxed then "@[<hv>" ^^ s ^^ "@]"
  else s

let rec print_ty ?(paren=false) info fmt = function
    | Tvar tv ->
        print_tv fmt tv
    | Ttuple [] ->
        pp_print_string fmt "void"
    | Ttuple [t] ->
        print_ty ~paren info fmt t
    | Ttuple tl ->
        unsupported "tuple type"
    | Tarrow (t1, t2) ->
        unsupported "function type"
    | Tapp (ts, tl) ->
        match query_syntax info.syntax ts with
        | Some s ->
            fprintf fmt (protect_on paren "%s%a") s (print_type_args info) tl
        | None ->
            fprintf fmt "%a%a" (print_lident info) ts (print_type_args info) tl

and print_type_args info fmt = function
  | [] ->
      ()
  | tyl ->
      fprintf fmt "<%a>" (print_list comma (print_ty ~paren:false info)) tyl

let print_var_decl info fmt (id, ty, _) =
  fprintf fmt "%a %a" (print_ty info) ty (print_lident info) id
let print_fun_args info fmt (args, _) =
  fprintf fmt "%a" (print_list comma (print_var_decl info)) args

let check_val_in_drv info loc id =
  match query_syntax info.syntax id with
  | None -> Loc.errorm ?loc "Symbol `%s' cannot be extracted" id.id_string
  | _ -> ()

let rec expr info prec fmt e =
  match e.e_node with
  | Econst (Constant.ConstInt c) ->
      let open Number in
      let print fmt ic =
        let n = c.Number.il_int in
        if BigInt.lt n BigInt.zero then
          (* default to base 10 for negative literals *)
          fprintf fmt "-%a" (print_in_base 10 None) (BigInt.abs n)
        else
          match ic.il_kind with
          | ILitHex | ILitBin -> fprintf fmt "0x%a" (print_in_base 16 None) n
          | ILitOct -> fprintf fmt "0%a" (print_in_base 8 None) n
          | ILitDec | ILitUnk ->
              (* default to base 10 *)
              print_in_base 10 None fmt n in
      let tname = match e.e_mlty with Tapp (id, _) -> id | _ -> assert false in
      begin match query_syntax info.literal tname with
      | Some st ->
          fprintf fmt "%a" (syntax_range_literal ~cb:(Some print) st) c
      | _ ->
          let s = tname.id_string in
          unsupported ("unspecified number format for type " ^ s) end
  | Econst _ ->
      fprintf fmt "TODO Econst"
  | Evar pvs ->
      (print_lident info) fmt (pv_name pvs)
  | Eapp (rs, [], _) when rs_equal rs rs_true ->
      pp_print_string fmt "true"
  | Eapp (rs, [], _) when rs_equal rs rs_false ->
      pp_print_string fmt "false"
  | Eapp (rs, pvl, _) ->
      (match query_syntax info.syntax rs.rs_name with
       | Some s ->
           let p = Mid.find rs.rs_name info.prec in
           syntax_arguments_prec s (expr info) p fmt pvl
       | None ->
           fprintf fmt "%a(%a)" (print_lident info) rs.rs_name
             (print_list comma (expr info 18)) pvl)
  | _ ->
      fprintf fmt "expr TODO"

and stmt ~return info fmt e =
  match e.e_node with
  | _ when return ->
      fprintf fmt "return %a;" (expr info 18) e
  | _ ->
      fprintf fmt "stmt TODO"

and print_let_def info fmt = function
  | Lvar (pv, e) ->
      unsupported "Lvar"
  | Lsym (rs, svar, res, args, e) ->
      fprintf fmt "@\n@[%a %a(%a) {@\n"
        (print_ty info) res
        (print_lident info) rs.rs_name
        (print_fun_args info) (args,svar);
      fprintf fmt "  @[%a@]@\n@]}@\n" (stmt ~return:true info) e;
      forget_vars args
  | Lrec rdef ->
      unsupported "Lrec"
  | Lany ({rs_name}, _, _, _) ->
      check_val_in_drv info rs_name.id_loc rs_name

let print_decl info fmt = function
  | Dtype tdl ->
      fprintf fmt "TODO Dtype@\n"
  | Dlet ldef ->
      print_let_def info fmt ldef
  | Dval (pv, ty) ->
      fprintf fmt" TODO Dval@\n"
  | Dexn (xs, ty) ->
      unsupported "exception declaration"
  | Dmodule (s, dl) ->
      fprintf fmt "nested module@\n"

let print_decl ~flat =
  let memo = Hashtbl.create 16 in
  fun args ?old ?fname ({mod_theory = th} as m) fmt d ->
    if flat then unsupported "no flat extraction for Java";
    if not (Hashtbl.mem memo d) then begin
      Hashtbl.add memo d ();
      let info = { syntax = args.Pdriver.syntax;
                   literal = args.Pdriver.literal;
                   prec = args.Pdriver.prec;
                   kn = m.mod_known } in
      print_decl info fmt d
    end

let file_name ?fname m =
  let n = m.mod_theory.th_name.id_string in
  let r = match fname with
    | None -> n
    | Some f -> f ^ "__" ^ n in
  r ^ ".java"

let get_package id =
  let exception Found of string in
  let get {attr_string=a} =
    if Strings.has_prefix "java_pkg:" a
    then raise (Found (Strings.remove_prefix "java_pkg:" a)) in
  match Sattr.iter get id.id_attrs with
  | () -> None
  | exception (Found p) -> Some p

let print_prelude args ?old ?fname ~deps ~global_prelude ~prelude fmt m =
  let n = m.mod_theory.th_name.id_string in
  Debug.dprintf debug_java_extraction "extract module %s@." n;
  (*
  Printer.print_prelude fmt global_prelude;
  let add_include m =
    let id = m.mod_theory.th_name.id_string in
    fprintf fmt "import %s@\n" id in
  List.iter add_include (List.rev deps);
  *)
  (match get_package m.mod_theory.th_name with
   | None -> ()
   | Some p -> fprintf fmt "package %s;@\n@\n" p);
  fprintf fmt "@[class %s {@\n  @[" n;
  (*
  Printer.print_prelude fmt prelude;
  *)
  ()

let class_footer_printer _args ?old:_ ?fname fmt m =
  fprintf fmt "@]@\n}@]@."

let java_printer = Pdriver.{
  desc = "printer for Java code";
  implem_printer = {
    filename_generator = file_name;
    decl_printer = print_decl ~flat:false;
    prelude_printer = print_prelude;
    header_printer = dummy_border_printer;
    footer_printer = class_footer_printer;
  };
  flat_printer = {
    filename_generator = file_name;
    decl_printer = print_decl ~flat:true;
    prelude_printer = print_prelude;
    header_printer = dummy_border_printer;
    footer_printer = dummy_border_printer;
  };
  interf_printer = None
}

let () = Pdriver.register_printer "java" java_printer
