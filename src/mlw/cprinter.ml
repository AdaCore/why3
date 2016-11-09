open Ident

exception Unsupported of string

module C = struct

  type ty =
    | Tvoid
    | Tsyntax of string * ty list
    | Tptr of ty
    | Tarray of ty * expr
    | Tstruct of ident * (ident * ty) list
    | Tunion of ident * (ident * ty) list
    | Tnamed of ident (* alias from typedef *)
    | Tnosyntax (* types that do not have a syntax, can't be printed *)
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
    | Ecast of ty * expr
    | Ecall of expr * expr list
    | Econst of constant
    | Evar of ident
    | Esize_expr of expr
    | Esize_type of ty
    | Eindex of expr * expr (* Array access *)
    | Edot of expr * ident (* Field access with dot *)
    | Earrow of expr * ident (* Pointer access with arrow *)
    | Esyntax of string * ty * (ty array) * (expr*ty) list * bool
  (* template, type and type arguments of result, typed arguments,
     is/is not converter*)

  and constant =
    | Cint of string
    | Cfloat of string
    | Cchar of string
    | Cstring of string

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
    | Dproto of ident * proto
    | Ddecl of names
    | Dtypedef of ty * ident

  and body = definition list * stmt

  type file = definition list

  exception NotAValue

  (* [assignify id] transforms a statement that computes a value into
     a statement that assigns that value to id *)
  let rec assignify id s =
    match s with
    | Snop -> (*Format.printf "assign snop@."; Snop*) raise NotAValue (* ? *)
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
    | Ecast (ty,e) -> Ecast (ty, propagate_in_expr id v e)
    | Ecall (e, l) -> Ecall (propagate_in_expr id v e,
                             List.map (propagate_in_expr id v) l)
    | Esize_expr e -> Esize_expr (propagate_in_expr id v e)
    | Eindex (e1,e2) -> Eindex (propagate_in_expr id v e1,
                                propagate_in_expr id v e2)
    | Edot (e,i) -> Edot (propagate_in_expr id v e, i)
    | Earrow (e,i) -> Earrow (propagate_in_expr id v e, i)
    | Esyntax (s,t,ta,l,b) ->
      Esyntax (s,t,ta,List.map (fun (e,t) -> (propagate_in_expr id v e),t) l,b)
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
    | Dtypedef _ -> raise (Unsupported "typedef inside function")
    | Dproto _ -> raise (Unsupported "prototype inside function")

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

  let is_empty_block s = s = Sblock([], Snop)
  let block_of_expr e = [], Sexpr e

  let rec is_nop = function
    | Snop -> true
    | Sblock ([], s) -> is_nop s
    | Sseq (s1,s2) -> is_nop s1 && is_nop s2
    | _ -> false

  let one_stmt = function
    | Snop -> true
    | Sexpr _ -> true
    | Sblock _ -> true
    | _ -> false

end

type info = Pdriver.printer_args = private {
  env         : Env.env;
  prelude     : Printer.prelude;
  thprelude   : Printer.prelude_map;
  blacklist   : Printer.blacklist;
  syntax      : Printer.syntax_map;
  converter   : Printer.syntax_map;
}

module Print = struct

  open C
  open Format
  open Printer
  open Pp

  exception Unprinted of string

  let c_keywords = ["auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do"; "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if"; "int"; "long"; "register"; "return"; "short"; "signed"; "sizeof"; "static"; "struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile"; "while" ]

  let () = assert (List.length c_keywords = 32)

  let sanitizer = sanitizer char_to_lalpha char_to_alnumus
  let printer = create_ident_printer c_keywords ~sanitizer

  let print_ident fmt id = fprintf fmt "%s" (id_unique printer id)

  let protect_on x s = if x then "(" ^^ s ^^ ")" else s

  let rec print_ty ?(paren=false) fmt = function
    | Tvoid -> fprintf fmt "void"
    | Tsyntax (s, tl) ->
      syntax_arguments
        (if paren then ("("^s^")") else s)
        (print_ty ~paren:false) fmt tl
    | Tptr ty -> fprintf fmt "(%a)*" (print_ty ~paren:true) ty
    | Tarray (ty, expr) ->
      fprintf fmt (protect_on paren "%a[%a]")
        (print_ty ~paren:true) ty (print_expr ~paren:false) expr
    | Tstruct _ -> raise (Unprinted "structs")
    | Tunion _ -> raise (Unprinted "unions")
    | Tnamed id -> print_ident fmt id
    | Tnosyntax -> raise (Unprinted "type without syntax")

  and print_unop fmt = function
    | Unot -> fprintf fmt "!"
    | Ustar -> fprintf fmt "*"
    | Uaddr -> fprintf fmt "&"

  and print_binop fmt = function
    | Band -> fprintf fmt "&&"
    | Bor -> fprintf fmt "||"
    | Beq -> fprintf fmt "=="
    | Bne -> fprintf fmt "!="
    | Bassign -> fprintf fmt "="

  and print_expr ~paren fmt = function
    | Enothing -> Format.printf "enothing"; ()
    | Eunop(u,e) -> fprintf fmt (protect_on paren "%a %a")
      print_unop u (print_expr ~paren:true) e
    | Ebinop(b,e1,e2) ->
      fprintf fmt (protect_on paren "%a %a %a")
        (print_expr ~paren:true) e1 print_binop b (print_expr ~paren:true) e2
    | Ecast(ty, e) ->
      fprintf fmt (protect_on paren "(%a)%a")
        (print_ty ~paren:false) ty (print_expr ~paren:true) e
    | Ecall (e,l) -> fprintf fmt (protect_on paren "%a(%a)")
      (print_expr ~paren:true) e (print_list comma (print_expr ~paren:false)) l
    | Econst c -> print_const fmt c
    | Evar id -> print_ident fmt id
    | Esize_expr e ->
      fprintf fmt (protect_on paren "sizeof(%a)") (print_expr ~paren:false) e
    | Esize_type ty ->
      fprintf fmt (protect_on paren "sizeof(%a)") (print_ty ~paren:false) ty
    | Eindex _ | Edot _ | Earrow _ -> raise (Unprinted "struct/array access")
    | Esyntax (s, t, args, lte,_) ->
      gen_syntax_arguments_typed snd (fun _ -> args)
        (if paren then ("("^s^")") else s)
        (fun fmt (e,_t) -> print_expr ~paren:false fmt e)
        (print_ty ~paren:false) (C.Enothing,t) fmt lte

  and print_const  fmt = function
    | Cint s | Cfloat s | Cchar s | Cstring s -> fprintf fmt "%s" s

  let print_id_init fmt = function
    | id, Enothing -> print_ident fmt id
    | id,e -> fprintf fmt "%a = %a" print_ident id (print_expr ~paren:false) e

  let rec print_stmt ~braces fmt = function
    | Snop -> Format.printf "snop"; ()
    | Sexpr e -> fprintf fmt "%a;" (print_expr ~paren:false) e;
    | Sblock ([] ,s) when (not braces || one_stmt s) -> (print_stmt ~braces:false) fmt s
    | Sblock b -> fprintf fmt "@[<hov>{@\n  @[<hov>%a@]@\n}@]" print_body b
    | Sseq (s1,s2) -> fprintf fmt "%a@\n%a"
      (print_stmt ~braces:false) s1
      (print_stmt ~braces:false) s2
    | Sif(c,t,e) when is_empty_block e ->
       fprintf fmt "if(%a)@\n%a" (print_expr ~paren:false) c
         (print_stmt ~braces:true) t
    | Sif (c,t,e) -> fprintf fmt "if(%a)@\n%a@\nelse@\n%a"
      (print_expr ~paren:false) c
      (print_stmt ~braces:true) t
      (print_stmt ~braces:true) e
    | Swhile (e,b) -> fprintf fmt "while (%a)@ %a"
      (print_expr ~paren:false) e (print_stmt ~braces:true) b
    | Sfor _ -> raise (Unprinted "for loops")
    | Sbreak -> fprintf fmt "break;"
    | Sreturn e -> fprintf fmt "return %a;" (print_expr ~paren:true) e

  and print_def fmt = function
    | Dfun (id,(rt,args),body) ->
       fprintf fmt "%a %a(@[%a@])@ @[<hov>{@;<1 2>@[<hov>%a@]@\n}@\n@]"
               (print_ty ~paren:false) rt
               print_ident id
               (print_list comma
			   (print_pair_delim nothing space nothing
					     (print_ty ~paren:false) print_ident))
	       args
               print_body body
    | Dproto (id, (rt, args)) ->
      fprintf fmt "%a %a(@[%a@]);@;"
        (print_ty ~paren:false) rt
        print_ident id
        (print_list comma
           (print_pair_delim nothing space nothing
			     (print_ty ~paren:false) print_ident))
	args
    | Ddecl (ty, lie) ->
       fprintf fmt "%a @[<hov>%a@];@;"
	       (print_ty ~paren:false) ty
	       (print_list comma print_id_init) lie
    | Dinclude id ->
       fprintf fmt "#include<%a.h>@;" print_ident id
    | Dtypedef (ty,id) ->
       fprintf fmt "@[<hov>typedef@ %a@;%a;@]@;"
	       (print_ty ~paren:false) ty print_ident id

  and print_body fmt body =
    print_pair_delim nothing newline nothing
		     (print_list newline print_def)
		     (print_stmt ~braces:true)
		     fmt body

  let print_file fmt info ast =
    Mid.iter (fun _ sl -> List.iter (fprintf fmt "%s\n") sl) info.thprelude;
    newline fmt ();
    fprintf fmt "@[<v>%a@]@." (print_list newline print_def) ast

end

module Translate = struct
  open Pdecl
  open Ity
  open Ty
  open Expr
  open Term
  open Printer
  open Pmodule

  let rec ty_of_ty info ty =
    match ty.ty_node with
    | Tyvar v ->
      begin match query_syntax info.syntax v.tv_name
        with
        | Some s -> C.Tsyntax (s, [])
        | None -> C.Tnamed (v.tv_name)
      end
    | Tyapp (ts, tl) ->
       begin match query_syntax info.syntax ts.ts_name
        with
        | Some s -> C.Tsyntax (s, List.map (ty_of_ty info) tl)
        | None -> C.Tnosyntax
       end

  let pv_name pv = pv.pv_vs.vs_name

  let rec expr info ?(is_return=false) (e:expr) : C.body =
    if e_ghost e then (Format.printf "translating ghost expr@."; C.([], Snop))
    else if is_e_void e then C.([], Snop)
    else if is_e_true e then expr info ~is_return (e_nat_const 1)
    else if is_e_false e then expr info ~is_return (e_nat_const 0)
    else match e.e_node with
    | Evar pv ->
       let e = C.Evar(pv_name pv) in
       C.([], if is_return then Sreturn e else Sexpr e)
    | Econst (Number.ConstInt ic) ->
      let n = Number.compute_int ic in
      let e = C.(Econst (Cint (BigInt.to_string n))) in
      C.([], if is_return then Sreturn e else Sexpr e)
    | Econst _ -> raise (Unsupported "real constants")
    | Eexec (ce, _cty) ->
      begin match ce.c_node with
      | Cfun e -> expr info ~is_return e
      | Capp (rs, pvsl) ->
         let e =  match query_syntax info.syntax rs.rs_name with
           | Some s ->
              let params =
		List.map (fun pv -> (C.Evar(pv_name pv), ty_of_ty info (ty_of_ity pv.pv_ity)))
			 pvsl in
              let rty = ty_of_ity e.e_ity in
              let rtyargs = match rty.ty_node with
		| Tyvar _ -> [||]
		| Tyapp (_,args) -> Array.of_list (List.map (ty_of_ty info) args)
              in
              C.Esyntax(s,ty_of_ty info rty, rtyargs, params,
                        Mid.mem rs.rs_name info.converter)
           | None ->
              let args = List.filter (fun pv -> not pv.pv_ghost) pvsl in
              C.(Ecall(Evar(rs.rs_name), List.map (fun pv -> Evar(pv_name pv)) args))
         in
	 C.([],
            if is_return && not (ity_equal rs.rs_cty.cty_result ity_unit)
            then Sreturn e
            else Sexpr e)
      | _ -> raise (Unsupported "Cpur/Cany") (*TODO clarify*)
      end
    | Eassign _ -> raise (Unsupported "mutable field assign")
    | Elet (ld,e) ->
      begin match ld with
      | LDvar (pv,le) ->
        Format.printf "let %s@." pv.pv_vs.vs_name.id_string;
        if pv.pv_ghost then expr info ~is_return e
        else if ity_equal pv.pv_ity ity_unit
        then ([], C.Sseq (C.Sblock(expr info ~is_return:false le),
			  C.Sblock(expr info ~is_return e)))
        else begin
          match le.e_node with
          | Econst (Number.ConstInt ic) ->
            let n = Number.compute_int ic in
            let ce = C.(Econst (Cint (BigInt.to_string n))) in
	    Format.printf "propagate constant %s for var %s@."
			  (BigInt.to_string n) (pv_name pv).id_string;
            C.propagate_in_block (pv_name pv) ce (expr info ~is_return e)
          | Eexec ({c_node = Capp(rs,_); _},_)
              when Mid.mem rs.rs_name info.converter ->
            begin match expr info ~is_return:false le with
            | [], C.Sexpr(se) ->
              C.propagate_in_block (pv_name pv) se (expr info ~is_return e)
            | _ -> assert false
            end
          | _->
            let t = ty_of_ty info (ty_of_ity pv.pv_ity) in
            match expr info ~is_return:false le with
            | [], C.Sexpr((C.Esyntax(_,_,_,_,b) as se))
                when b (* converter *) ->
              Format.printf "propagate converter for var %s@."
                (pv_name pv).id_string;
              C.propagate_in_block (pv_name pv) se (expr info ~is_return e)
            | d,s ->
              let initblock = d, C.assignify (pv_name pv) s in
              [ C.Ddecl (t, [pv_name pv, C.Enothing]) ],
              C.Sseq (C.Sblock initblock, C.Sblock (expr info ~is_return e))
        end
      | _ -> assert false
      end
    | Eif (cond, th, el) ->
       let c = expr info ~is_return:false cond in
       let t = expr info ~is_return th in
       let e = expr info ~is_return el in
       begin match c with
	     | [], C.Sexpr c ->
		if is_e_false th && is_e_true el
		then C.([], Sexpr(Eunop(Unot, c)))
		else [], C.Sif(c,C.Sblock t, C.Sblock e)
	     | cdef, cs ->
		let cid = id_register (id_fresh "cond") in (* ? *)
		C.Ddecl (C.Tsyntax ("int",[]), [cid, C.Enothing])::cdef,
		C.Sseq (C.assignify cid cs, C.Sif (C.Evar cid, C.Sblock t, C.Sblock e))
       (* TODO detect empty branches and replace with Snop, detect and/or*)
       end
    | Ewhile (c,_,_,e) ->
      let cd, cs = expr info ~is_return:false c in
      let b = expr info ~is_return:false e in
      begin match cs with
      | C.Sexpr ce -> cd, C.Swhile (ce, C.Sblock b)
      | _ ->
        let cid = id_register (id_fresh "cond") in (* ? *)
        [C.Ddecl (C.Tsyntax ("int",[]), [cid, C.Enothing])],
        C.Sseq (C.Sblock (cd, cs), C.Swhile (C.Evar cid, C.Sblock b))
      end
    | Etry _ | Eraise _ -> raise (Unsupported "try/exceptions") (*TODO*)
    | Efor _ -> raise (Unsupported "for loops")  (*TODO*)
    | Eassert _ -> [], C.Snop
    | Ecase _ -> raise (Unsupported "pattern matching")
    | Eghost _ | Epure _ | Eabsurd -> assert false

  let pdecl info (pd:Pdecl.pdecl) : C.definition list =
    match pd.pd_node with
    | PDlet (LDsym (rs, ce)) ->
      let fname = rs.rs_name in
      Format.printf "PDlet rsymbol %s@." fname.id_string;
      if Mid.mem fname info.syntax then (Format.printf "has syntax@."; [])
      else
        let params = List.map
		       (fun pv -> ty_of_ty info pv.pv_vs.vs_ty, pv_name pv)
		       (List.filter
			  (fun pv -> not pv.pv_ghost && not (ity_equal pv.pv_ity ity_unit))
			  rs.rs_cty.cty_args) in
        begin match ce.c_node with
        | Cfun e ->
           let rity = rs.rs_cty.cty_result in
           let rtype =
             if ity_equal rity ity_unit then C.Tvoid
             else ty_of_ty info (ty_of_ity rity) in
           [C.Dfun (fname, (rtype,params), expr info ~is_return:true e)]
        | _ -> raise (Unsupported "Non-function with no syntax in toplevel let")
	end
    | PDtype [{itd_its = its}] ->
      let id = its.its_ts.ts_name in
      Format.printf "PDtype %s@." id.id_string;
      begin
        match its.its_ts.ts_def with
        | Some def -> [C.Dtypedef (ty_of_ty info def, id)]
        | None ->
          begin match query_syntax info.syntax id with
          | Some _ -> []
          | None ->
            raise (Unsupported "type declaration without syntax or alias")
          end
      end

    | _ -> [] (*TODO exn ? *)

  let munit info = function
    | Udecl pd -> pdecl info pd
    | Uuse _m -> (*[C.Dinclude m.mod_theory.Theory.th_name]*) []
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
end
(*TODO simplifications : propagate constants, collapse blocks with only a statement and no def*)



let fg ?fname m =
  let n = m.Pmodule.mod_theory.Theory.th_name.Ident.id_string in
  match fname with
  | None -> n ^ ".c"
  | Some f -> f ^ "__" ^ n ^ ".c"

let pr args ?old fmt m =
  ignore(old);
  let ast = Translate.translate args m in
  try Print.print_file fmt args ast
  with Print.Unprinted s -> (Format.printf "Could not print: %s@." s;
		       Format.fprintf fmt "/* Dummy file */@.")

let () = Pdriver.register_printer "c" ~desc:"printer for C code" fg pr
