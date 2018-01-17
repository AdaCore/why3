(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident

module C = struct

  type ty =
    | Tvoid
    | Tsyntax of string (* ints, floats, doubles, chars are here *)
    | Tptr of ty
    | Tarray of ty * expr
    | Tstruct of ident * (ident * ty) list
    | Tunion of ident * (ident * ty) list
    | Tproto of proto
    | Tnamed of ident (* alias from typedef *)
    (* enum, const could be added *)

  (* int x=2, *y ... *)
  and names = ty * (ident * expr) list

  (* names with a single declaration *)
  and name = ty * ident * expr

  (* return type, parameter list. Variadic functions not handled. *)
  and proto = ty * (ty * ident) list

  and binop = Band | Bor | Beq | Bne | Bassign (* += and co. maybe to add *)

  and unop = Unot | Ustar | Uaddr (* (pre|post)(incr|decr) maybe to add *)

  and expr =
    | Enothing
    | Eunop of unop * expr
    | Ebinop of binop * expr * expr
    | Eternary of expr * expr * expr (* c ? then : else *)
    | Ecast of ty * expr
    | Ecall of expr * expr list
    | Econst of constant
    | Evar of string
    | Esize_expr of expr
    | Esize_type of ty
    | Eindex of expr * expr (* Array access *)
    | Edot of expr * string (* Field access with dot *)
    | Earrow of expr * string (* Pointer access with arrow *)

  and constant =
    | Cint of string
    | Cfloat of string
    | Cchar of string
    | Cstring of string
    | Ccompound of expr list

  type stmt =
    | Snop
    | Sexpr of expr
    | Sblock of body
    | Sseq of stmt * stmt
    | Sif of expr * stmt * stmt
    | Swhile of expr * stmt
    | Sfor of expr * expr * expr * stmt
    | Sbreak
    | Sreturn of expr

  and definition =
    | Dfun of name * body
    | Ddecl of names
    | Dtypedef of ty * ident
    | Dstructural of names (* struct, union... *)

  and body = definition list * stmt

  type file = definition list

end

let fg ?fname m =
  let n = m.Pmodule.mod_theory.Theory.th_name.Ident.id_string in
  match fname with
  | None -> n ^ ".c"
  | Some f -> f ^ "__" ^ n ^ ".c"

open Format

let pr args ?old ?fname ~flat m fmt d =
  ignore(args);
  ignore(old);
  ignore(m);
  ignore(d);
  ignore(fname);
  ignore(flat);
  fprintf fmt "#include <stdio.h>\n\
\n\
int main() {\n\
  printf \"Extraction from WhyML to C not yet implemented\\n\";\n\
  return 1;\n\
}\n\
"

let () = Pdriver.register_printer "c" ~desc:"printer for C code" fg pr
