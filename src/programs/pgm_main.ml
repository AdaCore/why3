(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* main module for whyl *)

open Format
open Why3
open Stdlib
open Typing
open Ptree
open Pgm_module

exception ClashModule of string

let () = Exn_printer.register (fun fmt e -> match e with
  | ClashModule m -> fprintf fmt "clash with previous module %s" m
  | _ -> raise e)

type theory_ast = {
  pth_name : Ptree.ident;
  pth_decl : (Ptree.loc * Pgm_typing.program_decl) list;
}

type module_ast = {
  mod_name : Ptree.ident;
  mod_decl : (Ptree.loc * Pgm_typing.program_decl) list;
}

type theory_module_ast =
| Ptheory of theory_ast
| Pmodule of module_ast

let add_theory env path lenv m =
  let id = m.pth_name in
  let env = Lexer.library_of_env (Env.env_of_library env) in
  let th = Theory.create_theory ~path (Denv.create_user_id id) in
  let rec add_decl th (loc,dcl) = match dcl with
    | Pgm_typing.PDdecl d ->
      Typing.add_decl loc th d
    | Pgm_typing.PDuseclone d ->
      Typing.add_use_clone env lenv th loc d
    | Pgm_typing.PDnamespace (name, import, dl) ->
      let th = Theory.open_namespace th name in
      let th = List.fold_left add_decl th dl in
      Typing.close_namespace loc import th
    | Pgm_typing.PDpdecl _ -> assert false
  in
  let th = List.fold_left add_decl th m.pth_decl in
  close_theory lenv th

let add_module ?(type_only=false) env path (ltm, lmod) m =
  let id = m.mod_name in
  let loc = id.id_loc in
  if Mstr.mem id.id lmod then raise (Loc.Located (loc, ClashModule id.id));
  let wp = not type_only in
  let uc = create_module ~path (Ident.id_user id.id loc) in
  let logic_env = Lexer.library_of_env (Env.env_of_library env) in
  let prelude = Env.read_lib_theory logic_env ["bool"] "Bool" in
  let uc = use_export_theory uc prelude in
  let uc = List.fold_left (Pgm_typing.decl ~wp env ltm lmod) uc m.mod_decl in
  let md = close_module uc in
  Mstr.add ("WP " ^ id.id) md.m_pure ltm, (* avoids a theory/module clash *)
  Mstr.add id.id md lmod

let add_theory_module ?(type_only=false) env path (ltm, lmod) = function
  | Ptheory t -> add_theory env path ltm t, lmod
  | Pmodule m -> add_module ~type_only env path (ltm, lmod) m

open Pgm_typing

let open_file, close_file =
  let ids  = Stack.create () in
  let muc  = Stack.create () in
  let prf  = Stack.create () in
  let lenv = Stack.create () in
  let open_file () =
    Stack.push [] lenv;
    let open_theory id = Stack.push id ids; Stack.push [] muc in
    let open_module id = Stack.push id ids; Stack.push [] muc in
    let close_theory () =
      let tast = { pth_name = Stack.pop ids;
                   pth_decl = List.rev (Stack.pop muc) } in
      Stack.push (Ptheory tast :: Stack.pop lenv) lenv in
    let close_module () =
      let mast = { mod_name = Stack.pop ids;
                   mod_decl = List.rev (Stack.pop muc) } in
      Stack.push (Pmodule mast :: Stack.pop lenv) lenv in
    let open_namespace s =
      Stack.push s prf; Stack.push [] muc in
    let close_namespace loc imp =
      let name = Stack.pop prf in
      let decl = List.rev (Stack.pop muc) in
      Stack.push ((loc, PDnamespace (name,imp,decl)) :: Stack.pop muc) muc in
    let new_decl loc d =
      Stack.push ((loc, PDdecl d) :: Stack.pop muc) muc in
    let new_pdecl loc d =
      Stack.push ((loc, PDpdecl d) :: Stack.pop muc) muc in
    let use_clone loc use =
      Stack.push ((loc, PDuseclone use) :: Stack.pop muc) muc in
    { open_theory = open_theory;
      close_theory = close_theory;
      open_module = open_module;
      close_module = close_module;
      open_namespace = open_namespace;
      close_namespace = close_namespace;
      new_decl = new_decl;
      new_pdecl = new_pdecl;
      use_clone = use_clone; }
  in
  let close_file () = List.rev (Stack.pop lenv) in
  open_file, close_file


let retrieve env path file c =
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let inc = open_file () in
  Lexer.parse_program_file inc lb;
  let ml = close_file () in
  if Debug.test_flag Typing.debug_parse_only then
    Mstr.empty, Mstr.empty
  else
    let type_only = Debug.test_flag Typing.debug_type_only in
    List.fold_left (add_theory_module ~type_only env path)
      (Mstr.empty, Mstr.empty) ml

let read_channel env path file c =
  let tm, mm = retrieve env path file c in
  mm, tm

let read_channel =
  let one_time_hack = ref true in
  fun env path file c ->
    let env =
      if !one_time_hack then begin
        one_time_hack := false;
        let genv = Env.env_of_library env in
        Env.register_format "whyml-old-library" ["mlw"] read_channel genv
          ~desc:"for internal use"
      end
      else env
    in
    read_channel env path file c

let library_of_env = Env.register_format "whyml-old" [] read_channel
  ~desc:"WhyML@ programming@ language@ (obsolete@ implementation)"
(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
