open Ident

exception Unsupported of string
exception NoSyntax of string

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
    | Dinclude of ident
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

  let rec propagate_in_expr id (v:expr) = function
    | Evar i when Ident.id_equal i id -> v
    | Evar i -> Evar i
    | Eunop (u,e) -> Eunop (u, propagate_in_expr id v e)
    | Ebinop (b,e1,e2) -> Ebinop (b,
                                  propagate_in_expr id v e1,
                                  propagate_in_expr id v e2)
    | Eternary (c,t,e) -> Eternary (propagate_in_expr id v c,
                                    propagate_in_expr id v t,
                                    propagate_in_expr id v e)
    | Ecast (ty,e) -> Ecast (ty, propagate_in_expr id v e)
    | Ecall (e, l) -> Ecall (propagate_in_expr id v e,
                             List.map (propagate_in_expr id v) l)
    | Esize_expr e -> Esize_expr (propagate_in_expr id v e)
    | Eindex (e1,e2) -> Eindex (propagate_in_expr id v e1,
                                propagate_in_expr id v e2)
    | Edot (e,i) -> Edot (propagate_in_expr id v e, i)
    | Earrow (e,i) -> Earrow (propagate_in_expr id v e, i)
    | Enothing -> Enothing
    | Econst c -> Econst c
    | Esize_type ty -> Esize_type ty

  let rec propagate_in_stmt id v = function
    | Sexpr e -> Sexpr (propagate_in_expr id v e)
    | Sblock b -> Sblock(propagate_in_block id v b)
    | Sseq (s1,s2) -> Sseq (propagate_in_stmt id v s1,
                            propagate_in_stmt id v s2)
    | Sif (e,s1,s2) -> Sif (propagate_in_expr id v e,
                            propagate_in_stmt id v s1,
                            propagate_in_stmt id v s2)
    | Swhile (e, s) -> Swhile (propagate_in_expr id v e,
                               propagate_in_stmt id v s)
    | Sfor (e1,e2,e3,s) -> Sfor (propagate_in_expr id v e1,
                                 propagate_in_expr id v e2,
                                 propagate_in_expr id v e3,
                                 propagate_in_stmt id v s)
    | Sreturn e -> Sreturn (propagate_in_expr id v e)
    | Snop -> Snop
    | Sbreak -> Sbreak

  and propagate_in_def id v d =
    let rec aux = function
      | [] -> [], true
      | (i,e)::t ->
        if Ident.id_equal i id then (i,e)::t, false
        else let t,b = aux t in ((i,propagate_in_expr id v e)::t), b
    in
    match d with
    | Ddecl (ty,l) ->
      let l,b = aux l in
      Ddecl (ty, l), b
    | Dinclude i -> Dinclude i, true
    | Dfun _ -> raise (Unsupported "nested function")
    | Dtypedef _ -> raise (Unsupported "typedef inside body")
    | Dstructural (ty,l) ->
      let l,b = aux l in
      Dstructural (ty, l), b

  and propagate_in_block id v (dl, s) =
    let dl, b = List.fold_left
      (fun (dl, acc) d ->
        if acc
        then
          let d, b = propagate_in_def id v d in
          (d::dl, b)
        else (d::dl, false))
      ([],true) dl in
    (List.rev dl, if b then propagate_in_stmt id v s else s)


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
  open Pmodule

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
        | None -> raise (NoSyntax ts.ts_name.id_string)
       end

  let ty_of_ts info ts =
    match query_syntax info.syntax ts.ts_name
        with
        | Some s -> C.Tsyntax s (*TODO something with the %[tv][1-9] logic ?*)
        | None -> raise (NoSyntax ts.ts_name.id_string)

  let ty_of_ity info ity =
    match ity.ity_node with
    | Ityvar (tv,_) ->
      begin match query_syntax info.syntax tv.tv_name with
      | Some s -> C.Tsyntax s
      | None -> C.Tnamed (tv.tv_name)
      end
    | Ityapp (its,_,_) | Ityreg {reg_its=its} -> ty_of_ts info its.its_ts

  let pv_name pv = pv.pv_vs.vs_name

  let rec expr info (e:expr) : C.body =
    match e.e_node with
    | Evar pv -> C.([], Sexpr(Evar (pv_name pv)))
    | Econst (Number.ConstInt ic) ->
      let n = Number.compute_int ic in
      C.([], Sexpr(Econst (Cint (BigInt.to_string n))))
    | Econst _ -> assert false (*TODO*)
    | Eexec (ce, _cty) ->
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
        Format.printf "let %s@." pv.pv_vs.vs_name.id_string;
        if pv.pv_ghost then expr info e
        else if ((pv_name pv).id_string = "_" && ity_equal pv.pv_ity ity_unit)
        then ([], C.Sseq (C.Sblock(expr info le), C.Sblock(expr info e)))
        else begin
          match le.e_node with
          | Econst (Number.ConstInt ic) ->
            let n = Number.compute_int ic in
            let cexp = C.(Econst (Cint (BigInt.to_string n))) in
            C.propagate_in_block (pv_name pv) cexp (expr info e)
          | _->
            let t = ty_of_ity info pv.pv_ity in
            let initblock = expr info le in
            [ C.Ddecl (t, [pv_name pv, C.Enothing]) ],
            C.Sseq (C.Sblock initblock, C.Sblock (expr info e))
        end
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
    | Etry _ | Eraise _ -> raise (Unsupported "try/exceptions") (*TODO*)
    | Efor _ -> assert false (*TODO*)
    | Eassert _ -> [], C.Snop
    | Eghost _ | Epure _ | Ecase _ | Eabsurd -> assert false

  let pdecl info (pd:Pdecl.pdecl) : C.definition list =
    match pd.pd_node with
    | PDlet (LDsym (rs, ce)) ->
      let fname = rs.rs_name in
      Format.printf "PDlet rsymbol %s@." fname.id_string;
      begin try
        if Mid.mem fname info.syntax then []
        else
        let params = List.map
          (fun pv -> ty_of_ty info pv.pv_vs.vs_ty, pv_name pv)
          (List.filter
             (fun pv -> not pv.pv_ghost && not (ity_equal pv.pv_ity ity_unit))
             rs.rs_cty.cty_args) in
        match ce.c_node with
        | Cfun e ->
          let rtype = match rs.rs_cty.cty_result.ity_node with
            | Ityapp (its, _,_) ->
              ty_of_ts info its.its_ts
            | _ ->
              raise (Unsupported "variable return type")
          in
          [C.Dfun (fname, (rtype,params), expr info e)]
        | _ -> raise (Unsupported "Non-function with no syntax in toplevel let")
        with
          NoSyntax s ->
            Format.printf "%s has no syntax : not extracted@." s;
            []
      end
    | PDtype [{itd_its = ity}] ->
      let id = ity.its_ts.ts_name in
      Format.printf "PDtype %s@." id.id_string;
      let def =
        match ity.its_ts.ts_def with
        | Some def -> ty_of_ty info def
        | None ->
          begin match query_syntax info.syntax id with
          | Some s -> C.Tsyntax s
          | None ->
            raise (Unsupported "type declaration without syntax or alias")
          end
      in
      [C.Dtypedef (def, id)]
    | _ -> [] (*TODO exn ? *)


  let munit info = function
    | Udecl pd -> pdecl info pd
    | Uuse _ -> []
    | Uclone _ -> raise (Unsupported "clone")
    | Umeta _ -> raise (Unsupported "meta")
    | Uscope _ -> []

  let translate (info:info) (m:pmodule) : C.file =
    Format.printf "Translating module %s@."
      m.mod_theory.Theory.th_name.id_string;
    try List.flatten (List.map (munit info) m.mod_units)
    with
    | Unsupported s ->
      Format.printf "Failed because of unsupported construct: %s@." s; []
    | NoSyntax s ->
      Format.printf "Failed because %s has no syntax@." s; []
end

let fg ?fname m =
  let n = m.Pmodule.mod_theory.Theory.th_name.Ident.id_string in
  match fname with
  | None -> n ^ ".c"
  | Some f -> f ^ "__" ^ n ^ ".c"

open Format

let pr args ?old fmt m =
  ignore(old);
  let _ast = Translate.translate args m in
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
