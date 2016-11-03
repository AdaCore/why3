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
    | Evar of ident
    | Esize_expr of expr
    | Esize_type of ty
    | Eindex of expr * expr (* Array access *)
    | Edot of expr * ident (* Field access with dot *)
    | Earrow of expr * ident (* Pointer access with arrow *)

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
    | Dfun of ident * proto * body
    | Ddecl of names
    | Dtypedef of ty * ident
    | Dstructural of names (* struct, union... *)

  and body = definition list * stmt

  type file = definition list

  exception NotAValue

  (* [assignify id] transforms a statement that computes a value into
     a statement that assigns that value to id *)
  let rec assignify id = function
    | Snop -> raise NotAValue
    | Sexpr e -> Sexpr (Ebinop (Bassign, Evar id, e))
    | Sblock (ds, s) -> Sblock (ds, assignify id s)
    | Sseq (s1, s2) -> Sseq (s1, assignify id s2)
    | Sif (c,t,e) -> Sif (c, assignify id t, assignify id e)
    | Swhile (c,s) -> Swhile (c, assignify id s) (* can this be a value ?*)
    | Sfor (e0,e1,e2,s) -> Sfor (e0,e1,e2, assignify id s)
    | Sbreak -> raise NotAValue
    | Sreturn _ -> raise NotAValue

end

type info = Pdriver.printer_args = private {
  env         : Env.env;
  prelude     : Printer.prelude;
  thprelude   : Printer.prelude_map;
  blacklist   : Printer.blacklist;
  syntax      : Printer.syntax_map;
  converter   : Printer.syntax_map;
}

module Translate = struct
  open Pdecl
  open Ity
  open Ty
  open Expr
  open Term
  open Printer

  exception Unsupported of string

  let ty_of_ty info ty =
    match ty.ty_node with
    | Tyvar v ->
      begin match query_syntax info.syntax v.tv_name
        with
        | Some s -> C.Tsyntax s
        | None -> C.Tnamed (v.tv_name)
      end
    | Tyapp (ts, _tl) ->
       begin match query_syntax info.syntax ts.ts_name
        with
        | Some s -> C.Tsyntax s (*TODO something with the %[tv][1-9] logic ?*)
        | None -> assert false
       end

  let ty_of_ts info ts =
    match query_syntax info.syntax ts.ts_name
        with
        | Some s -> C.Tsyntax s (*TODO something with the %[tv][1-9] logic ?*)
        | None -> assert false

  let ty_of_ity info ity =
    match ity.ity_node with
    | Ityvar (tv,_) ->
      begin match query_syntax info.syntax tv.tv_name with
      | Some s -> C.Tsyntax s
      | None -> C.Tnamed (tv.tv_name)
      end
    | Ityapp (its,_,_) ->
      ty_of_ts info its.its_ts
    | Ityreg _ -> assert false

  let pv_name pv = pv.pv_vs.vs_name

  let rec expr info (e:expr) : C.body =
    match e.e_node with
    | Evar pv -> C.([], Sexpr(Evar (pv_name pv)))
    | Econst c -> assert false (*TODO*)
    | Eexec (ce, cty) ->
      begin match ce.c_node with
      | Cfun e -> expr info e
      | Capp (rs, pvsl) ->
        let args = List.filter (fun pv -> not pv.pv_ghost) pvsl in
        C.([],
           Sexpr(Ecall(Evar(rs.rs_name),
                       List.map (fun pv -> Evar(pv_name pv)) args)))
      | _ -> assert false
      end
    | Eassign _ -> assert false
    | Elet (ld,e) ->
      begin match ld with
      | LDvar (pv,le) ->
        if pv.pv_ghost then expr info e
        else
          let t = ty_of_ity info pv.pv_ity in
          let initblock = expr info le in
          [ C.Ddecl (t, [pv_name pv, C.Enothing]) ],
          C.Sseq (C.Sblock initblock, C.Sblock (expr info e))
      | _ -> assert false
      end
    | Eif (c, t, e) ->
      let t = expr info t in
      let e = expr info e in
      begin match expr info c with
      | [], C.Sexpr c -> [], C.Sif(c,C.Sblock t, C.Sblock e)
      | cblock ->
        let cid = id_register (id_fresh "cond") in (* ? *)
        [ C.Ddecl (C.Tsyntax "int", [cid, C.Enothing]) ],
        C.Sseq (C.Sblock cblock, C.Sif (C.Evar cid, C.Sblock t, C.Sblock e))
      end
    | Ewhile (c,_,_,e) ->
      let cd, cs = expr info c in
      let b = expr info e in
      begin match cs with
      | C.Sexpr ce -> cd, C.Swhile (ce, C.Sblock b)
      | _ ->
        let cid = id_register (id_fresh "cond") in (* ? *)
        [C.Ddecl (C.Tsyntax "int", [cid, C.Enothing])],
        C.Sseq (C.Sblock (cd, cs), C.Swhile (C.Evar cid, C.Sblock b))
      end
    | Etry _ | Eraise _ -> assert false (*TODO*)
    | Efor _ -> assert false (*TODO*)
    | Eassert _ -> [], C.Snop
    | Eghost _ | Epure _ | Ecase _ | Eabsurd -> assert false

  let pdecl info (pd:Pdecl.pdecl) : C.definition list =
    match pd.pd_node with
    | PDlet (LDsym (rs, ce)) ->
      begin match ce.c_node with
      | Cfun e ->
        let fname = rs.rs_name in
        let rtype = match rs.rs_cty.cty_result.ity_node with
          | Ityapp (its, _,_) ->
            ty_of_ts info its.its_ts
          | _ -> assert false
        in
        let params = List.map
          (fun pv -> ty_of_ty info pv.pv_vs.vs_ty, pv_name pv)
          (List.filter (fun pv -> not pv.pv_ghost) rs.rs_cty.cty_args) in
        [C.Dfun (fname, (rtype,params), expr info e)]
      | _ -> assert false
      end
    | PDtype [{itd_its = ity}] ->
      let id = ity.its_ts.ts_name in
      [C.Dtypedef (ty_of_ts info ity.its_ts, id)]
    | _ -> assert false


  let translate (info:info) (m:Pmodule.pmodule) : C.file =
    assert false

end

let fg ?fname m =
  let n = m.Pmodule.mod_theory.Theory.th_name.Ident.id_string in
  match fname with
  | None -> n ^ ".c"
  | Some f -> f ^ "__" ^ n ^ ".c"

open Format

(*

decl : d:pdecl -> Cdefinition list

  cas sur d.pd_node:

    1: PDlet (LDsym (rs: routine symbol) (expr)


pr_unit : mod_unit -> Cdefinition list

  cas numero 1: Udecl d -> appeler fonction decl

*)

let pr args ?old fmt m =
  ignore(args);
  ignore(old);
  ignore(m);
  (* TODO:
    iterer sur m.mod_units la fonction pr_unit
   *)

  fprintf fmt "#include <stdio.h>\n\
\n\
int main() {\n\
  printf \"Extraction from WhyML to C not yet implemented\\n\";\n\
  return 1;\n\
}\n\
"

let () = Pdriver.register_printer "c" ~desc:"printer for C code" fg pr
