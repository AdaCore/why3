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
    | Equestion of expr * expr * expr (* c ? t : e *)
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

  let rec is_nop = function
    | Snop -> true
    | Sblock ([], s) -> is_nop s
    | Sseq (s1,s2) -> is_nop s1 && is_nop s2
    | _ -> false

  let rec one_stmt = function
    | Snop -> true
    | Sexpr _ -> true
    | Sblock (d,s) -> d = [] && one_stmt s
    | _ -> false

  (** [assignify id] transforms a statement that computes a value into
     a statement that assigns that value to id *)
  let rec assignify id = function
    | Snop -> raise NotAValue
    | Sexpr e -> Sexpr (Ebinop (Bassign, Evar id, e))
    | Sblock (ds, s) -> Sblock (ds, assignify id s)
    | Sseq (s1, s2) when not (is_nop s2) -> Sseq (s1, assignify id s2)
    | Sseq (s1,_) -> assignify id s1
    | Sif (c,t,e) -> Sif (c, assignify id t, assignify id e)
    | Swhile (c,s) -> Swhile (c, assignify id s) (* can this be a value ?*)
    | Sfor (e0,e1,e2,s) -> Sfor (e0,e1,e2, assignify id s)
    | Sbreak -> raise NotAValue
    | Sreturn _ -> raise NotAValue


  (** [get_last_expr] extracts the expression computed by the given statement.
     This is needed when loop conditions are more complex than a simple expression. *)
  let rec get_last_expr = function
    | Snop -> raise NotAValue
    | Sexpr e -> Snop, e
    | Sblock (ds,s) ->
      let s',e = get_last_expr s in
      Sblock(ds,s'), e
    | Sseq (s1,s2) when not (is_nop s2) ->
      let s', e = get_last_expr s2 in
      Sseq(s1,s'), e
    | Sseq (s1,_) -> get_last_expr s1
    | Sif (c,Sexpr t,Sexpr e) -> Snop, Equestion(c,t,e)
    | Sif _ -> raise (Unsupported "while (complex if)")
    | Swhile (_c,_s) -> raise (Unsupported "while (while) {}")
    | Sfor _ -> raise (Unsupported "while (for)")
    | Sbreak -> raise NotAValue
    | Sreturn _ -> raise NotAValue

  (** [propagate_in_expr id v] and the associated functions replace
      all instances of [id] by [v] in an
      expression/statement/definition/block. It is used for constant
      propagation to reduce the number of variables. *)
  let rec propagate_in_expr id (v:expr) = function
    | Evar i when Ident.id_equal i id -> v
    | Evar i -> Evar i
    | Eunop (u,e) -> Eunop (u, propagate_in_expr id v e)
    | Ebinop (b,e1,e2) -> Ebinop (b,
                                  propagate_in_expr id v e1,
                                  propagate_in_expr id v e2)
    | Equestion (c,t,e) -> Equestion(propagate_in_expr id v c,
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

(** [flatten_defs d s] appends all definitions in the statement [s] to d. *)
  (* TODO check ident unicity ? *)
  let rec flatten_defs d = function
    | Sseq (s1,s2) ->
      let d, s1' = flatten_defs d s1 in
      let d, s2' = flatten_defs d s2 in
      d, Sseq(s1',s2')
    | Sblock (d',s) ->
      let d',s' = flatten_defs d' s in
      d@d', s'
    | Sif (c,t,e) ->
      let d, t' = flatten_defs d t in
      let d, e' = flatten_defs d e in
      d,Sif(c,t',e')
    | Swhile (c,s) ->
      let d, s' = flatten_defs d s in
      d, Swhile (c, s')
    | Sfor (e1,e2,e3,s) ->
      let d, s' = flatten_defs d s in
      d, Sfor(e1,e2,e3,s')
    | s -> d,s

  let rec elim_empty_blocks = function
    | Sblock ([], s) -> elim_empty_blocks s
    | Sblock (d,s) -> Sblock (d, elim_empty_blocks s)
    | Sseq (s1,s2) -> Sseq (elim_empty_blocks s1, elim_empty_blocks s2)
    | Sif (c,t,e) -> Sif(c, elim_empty_blocks t, elim_empty_blocks e)
    | Swhile (c,s) -> Swhile(c, elim_empty_blocks s)
    | Sfor(e1,e2,e3,s) -> Sfor(e1,e2,e3,elim_empty_blocks s)
    | s -> s

  let rec elim_nop = function
    | Sseq (s1,s2) ->
      let s1 = elim_nop s1 in
      let s2 = elim_nop s2 in
      begin match s1,s2 with
      | Snop, Snop -> Snop
      | Snop, s | s, Snop -> s
      | _ -> Sseq(s1,s2)
      end
    | Sblock (d,s) ->
      let s = elim_nop s in
      begin match d, s with
      | [], Snop -> Snop
      | _ -> Sblock(d,s)
      end
    | Sif (c,t,e) -> Sif(c, elim_nop t, elim_nop e)
    | Swhile (c,s) -> Swhile (c, elim_nop s)
    | Sfor(e1,e2,e3,s) -> Sfor(e1,e2,e3,elim_nop s)
    | s -> s

  let rec add_to_last_call params = function
    | Sblock (d,s) -> Sblock (d, add_to_last_call params s)
    | Sseq (s1,s2) when not (is_nop s2) ->
      Sseq (s1, add_to_last_call params s2)
    | Sseq (s1,_) -> add_to_last_call params s1
    | Sexpr (Ecall(fname, args)) ->
      Sexpr (Ecall(fname, params@args)) (*change name to ensure no renaming ?*)
    | Sreturn (Ecall (fname, args)) ->
      Sreturn (Ecall(fname, params@args))
    | _ -> raise (Unsupported "tuple pattern matching with too complex def")

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
	s
        (print_ty ~paren:false) fmt tl
    | Tptr ty -> fprintf fmt "%a *" (print_ty ~paren:true) ty
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
    | Equestion(c,t,e) ->
      fprintf fmt (protect_on paren "%a ? %a : %a")
        (print_expr ~paren:true) c
        (print_expr ~paren:true) t
        (print_expr ~paren:true) e
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
    | Sblock ([] ,s) when (not braces || (one_stmt s && not (is_nop s))) ->
      (print_stmt ~braces:false) fmt s
    | Sblock b -> fprintf fmt "@[<hov>{@\n  @[<hov>%a@]@\n}@]" print_body b
    | Sseq (s1,s2) -> fprintf fmt "%a@\n%a"
      (print_stmt ~braces:false) s1
      (print_stmt ~braces:false) s2
    | Sif(c,t,e) when is_nop e ->
       fprintf fmt "if(%a)@\n%a" (print_expr ~paren:false) c
         (print_stmt ~braces:true) (Sblock([],t))
    | Sif (c,t,e) -> fprintf fmt "if(%a)@\n%a@\nelse@\n%a"
      (print_expr ~paren:false) c
      (print_stmt ~braces:true) (Sblock([],t))
      (print_stmt ~braces:true) (Sblock([],e))
    | Swhile (e,b) -> fprintf fmt "while (%a)@;<1 2>%a"
      (print_expr ~paren:false) e (print_stmt ~braces:true) (Sblock([],b))
    | Sfor _ -> raise (Unprinted "for loops")
    | Sbreak -> fprintf fmt "break;"
    | Sreturn Enothing -> fprintf fmt "return;"
    | Sreturn e -> fprintf fmt "return %a;" (print_expr ~paren:true) e

  and print_def fmt def =
    try match def with
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
       fprintf fmt "%a @[<hov>%a@];"
	       (print_ty ~paren:false) ty
	       (print_list comma print_id_init) lie
    | Dinclude id ->
       fprintf fmt "#include<%a.h>@;" print_ident id
    | Dtypedef (ty,id) ->
       fprintf fmt "@[<hov>typedef@ %a@;%a;@]"
	       (print_ty ~paren:false) ty print_ident id
    with Unprinted s -> Format.printf "Missed a def because : %s@." s

  and print_body fmt body =
    if fst body = []
    then print_stmt ~braces:true fmt (snd body)
    else
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

  type syntax_env = { in_unguarded_loop : bool;
                      computes_return_value : bool;
		      returns_tuple: bool * ident list;
                      breaks : Sid.t;
                      returns : Sid.t; }

  let rec expr info env (e:expr) : C.body =
    if e_ghost e then (Format.printf "translating ghost expr@."; C.([], Snop))
    else if is_e_void e then
      if env.computes_return_value
      then C.([], Sreturn(Enothing))
      else C.([], Snop)
    else if is_e_true e then expr info env (e_nat_const 1)
    else if is_e_false e then expr info env (e_nat_const 0)
    else match e.e_node with
    | Evar pv ->
       let e = C.Evar(pv_name pv) in
       C.([], if env.computes_return_value then Sreturn e else Sexpr e)
    | Econst (Number.ConstInt ic) ->
      let n = Number.compute_int ic in
      let e = C.(Econst (Cint (BigInt.to_string n))) in
      C.([], if env.computes_return_value then Sreturn e else Sexpr e)
    | Econst _ -> raise (Unsupported "real constants")
    | Eexec (ce, _cty) ->
      begin match ce.c_node with
      | Cfun e -> expr info env e
      | Capp (rs, pvsl) ->
	 if is_rs_tuple rs && env.computes_return_value
	 then begin
	     match env.returns_tuple with
	     | true, rl ->
		let args = List.filter (fun pv -> not (pv.pv_ghost
						       || ity_equal pv.pv_ity ity_unit))
				       pvsl in
		assert (List.length rl = List.length args);
		C.([],
		   List.fold_right2 (fun res arg acc ->
				     Sseq(Sexpr(Ebinop(Bassign,
						       Eunop(Ustar,Evar(res)),
						       Evar(pv_name arg))),
					 acc))
				    rl args (Sreturn(Enothing)))
	     | _ -> assert false
	   end
	 else
	   let e =
             match
               (query_syntax info.syntax rs.rs_name,
                query_syntax info.converter rs.rs_name) with

               | _, Some s
               | Some s, _ ->
		 let params =
		   List.map (fun pv -> (C.Evar(pv_name pv),
                                        ty_of_ty info (ty_of_ity pv.pv_ity)))
		     pvsl in
		 let rty = ty_of_ity e.e_ity in
		 let rtyargs = match rty.ty_node with
		   | Tyvar _ -> [||]
		   | Tyapp (_,args) ->
                     Array.of_list (List.map (ty_of_ty info) args)
		 in
		 C.Esyntax(s,ty_of_ty info rty, rtyargs, params,
                           Mid.mem rs.rs_name info.converter)
               | None, None ->
		 let args = List.filter
		   (fun pv -> not (pv.pv_ghost
				   || ity_equal pv.pv_ity ity_unit))
		   pvsl in
		 C.(Ecall(Evar(rs.rs_name),
			  List.map (fun pv -> Evar(pv_name pv)) args))
           in
	   C.([],
              if env.computes_return_value
	      then
                if (ity_equal rs.rs_cty.cty_result ity_unit)
                then Sseq(Sexpr e, Sreturn Enothing)
                else Sreturn e
              else Sexpr e)
      | _ -> raise (Unsupported "Cpur/Cany") (*TODO clarify*)
      end
    | Eassign _ -> raise (Unsupported "mutable field assign")
    | Elet (ld,e) ->
      begin match ld with
      | LDvar (pv,le) ->
        Format.printf "let %s@." pv.pv_vs.vs_name.id_string;
        if pv.pv_ghost then expr info env e
        else if ity_equal pv.pv_ity ity_unit
        then let env' = {env with computes_return_value = false} in
             ([], C.Sseq (C.Sblock(expr info env' le),
		          C.Sblock(expr info env e)))
        else begin
          match le.e_node with
          | Econst (Number.ConstInt ic) ->
            let n = Number.compute_int ic in
            let ce = C.(Econst (Cint (BigInt.to_string n))) in
	    Format.printf "propagate constant %s for var %s@."
			  (BigInt.to_string n) (pv_name pv).id_string;
            C.propagate_in_block (pv_name pv) ce (expr info env e)
          | Eexec ({c_node = Capp(rs,_); _},_)
              when Mid.mem rs.rs_name info.converter ->
            begin match expr info {env with computes_return_value = false} le
              with
            | [], C.Sexpr(se) ->
              C.propagate_in_block (pv_name pv) se (expr info env e)
            | _ -> assert false
            end
          | _->
            let t = ty_of_ty info (ty_of_ity pv.pv_ity) in
            match expr info {env with computes_return_value = false} le with
            | [], C.Sexpr((C.Esyntax(_,_,_,_,b) as se))
                when b (* converter *) ->
              Format.printf "propagate converter for var %s@."
                (pv_name pv).id_string;
              C.propagate_in_block (pv_name pv) se (expr info env e)
            | d,s ->
              let initblock = d, C.assignify (pv_name pv) s in
              [ C.Ddecl (t, [pv_name pv, C.Enothing]) ],
              C.Sseq (C.Sblock initblock, C.Sblock (expr info env e))
        end
      | _ -> raise (Unsupported "LDsym/LDrec") (* TODO for rec at least*)
      end
    | Eif (cond, th, el) ->
       let c = expr info {env with computes_return_value = false} cond in
       let t = expr info env th in
       let e = expr info env el in
       begin match c with
	     | [], C.Sexpr c ->
		if is_e_false th && is_e_true el
		then C.([], Sexpr(Eunop(Unot, c)))
		else [], C.Sif(c,C.Sblock t, C.Sblock e)
	     | cdef, cs ->
		let cid = id_register (id_fresh "cond") in (* ? *)
		C.Ddecl (C.Tsyntax ("int",[]), [cid, C.Enothing])::cdef,
		C.Sseq (C.assignify cid cs,
                        C.Sif (C.Evar cid, C.Sblock t, C.Sblock e))
       (* TODO detect empty branches and replace with Snop, detect and/or*)
       end
    | Ewhile (c,_,_,b) ->
      Format.printf "while@.";
      let cd, cs = expr info {env with computes_return_value = false} c in
      (* this is needed so that the extracted expression has all
         needed variables in its scope *)
      let cd, cs = C.flatten_defs cd cs in
      let env' = { computes_return_value = false;
                   in_unguarded_loop = true;
		   returns_tuple = env.returns_tuple;
                   returns = env.returns;
                   breaks =
                     if env.in_unguarded_loop
                     then Sid.empty else env.breaks } in
      let b = expr info  env' b in
      begin match cs with
      | C.Sexpr ce -> cd, C.Swhile (ce, C.Sblock b)
      | _ ->
        begin match C.get_last_expr cs with
        | C.Snop, e -> cd, C.(Swhile(e, C.Sblock b))
        | s,e -> cd, C.(Swhile(Econst (Cint "1"),
                     Sseq(s,
                          Sseq(Sif(Eunop(Unot, e), Sbreak, Snop),
                               C.Sblock b))))
        end
      end
    | Etry (b, exm) ->
      Format.printf "TRY@.";
      let is_while = match b.e_node with Ewhile _ -> true | _-> false in
      let breaks,returns = Mexn.fold
        (fun xs (pvsl,r) (bs,rs) ->
          let id = xs.xs_name in
          match pvsl, r.e_node with
          | [pv], Evar pv' when pv_equal pv pv' && env.computes_return_value ->
            (bs, Sid.add id rs)
          | [], _ when is_e_void r && is_while ->
            (Sid.add id bs, rs)
          |_ -> raise (Unsupported "non break/return exception in try"))
        exm (Sid.empty, env.returns)
      in
      let env' = { computes_return_value = env.computes_return_value;
                   in_unguarded_loop = false;
		   returns_tuple = env.returns_tuple;
                   breaks = breaks;
                   returns = returns;
                 } in
      expr info env' b
    | Eraise (xs,_) when Sid.mem xs.xs_name env.breaks ->
      Format.printf "BREAK@.";
      ([], C.Sbreak)
    | Eraise (xs,r) when Sid.mem xs.xs_name env.returns ->
      Format.printf "RETURN@.";
      expr info {env with computes_return_value = true} r
    | Eraise _ -> raise (Unsupported "non break/return exception raised")
    | Efor _ -> raise (Unsupported "for loops")  (*TODO*)
    | Eassert _ -> [], C.Snop
      (* let (a,b) = f(...) in *)
    | Ecase (e1,[{pp_pat = {pat_node = Papp(ls,rets)}}, e2])
        when is_fs_tuple ls
          && List.for_all (fun p ->
            match p.pat_node with Pvar _ -> true |_-> false)
            rets
          ->
      let rets, defs = List.fold_right
        (fun p (r, d)-> match p.pat_node with
        | Pvar vs -> (C.(Eunop(Uaddr,Evar(vs.vs_name)))::r,
		     C.Ddecl(ty_of_ty info vs.vs_ty, [vs.vs_name, C.Enothing])::d)
        | _ -> assert false )
        rets ([], []) in
      let d,s = expr info {env with computes_return_value = false} e1 in
      let b = expr info env e2 in
      d@defs, C.(Sseq(add_to_last_call rets s, Sblock b))
    | Ecase _ -> raise (Unsupported "pattern matching")
    | Eghost _ | Epure _ | Eabsurd -> assert false

  let pdecl info (pd:Pdecl.pdecl) : C.definition list =
    match pd.pd_node with
    | PDlet (LDsym (rs, ce)) ->
      let fname = rs.rs_name in
      Format.printf "PDlet rsymbol %s@." fname.id_string;
      if rs_ghost rs
      then begin Format.printf "is ghost@."; [] end
      else
      begin try
              if Mid.mem fname info.syntax
              then (Format.printf "has syntax@."; [])
              else
                let params = List.map
		  (fun pv -> ty_of_ty info pv.pv_vs.vs_ty, pv_name pv)
		  (List.filter
		     (fun pv -> not pv.pv_ghost
                       && not (ity_equal pv.pv_ity ity_unit))
		     rs.rs_cty.cty_args) in
                begin match ce.c_node with
                      | Cfun e ->
			 let env = { computes_return_value = true;
				     in_unguarded_loop = false;
				     returns_tuple = false, [];
				     returns = Sid.empty;
				     breaks = Sid.empty; } in
			 let rity = rs.rs_cty.cty_result in
			 let is_simple_tuple ity =
			   let arity_zero = function
			     | Ityapp(_,a,r) -> a = [] && r = []
			     | Ityreg { reg_args = a; reg_regs = r } ->
                               a = [] && r = []
			     | Ityvar _ -> true
			   in
			   (match ity.ity_node with
			    | Ityapp ({its_ts = s},_,_)
                            | Ityreg { reg_its = {its_ts = s}; }
			      -> is_ts_tuple s
			    | _ -> false)
			   && (ity_fold
                                 (fun acc ity ->
                                   acc && arity_zero ity.ity_node) true ity)
			 in
			 (* FIXME is it necessary to have arity 0 in regions ?*)
			 let rtype =
			   if ity_equal rity ity_unit
			   then C.Tvoid
			   else ty_of_ty info (ty_of_ity rity) in
			 let env, rtype, params = match rtype with
			   | C.Tnosyntax when is_simple_tuple rity ->
			      (* instead of returning a tuple, return
			      void and assign the result to addresses
			      passed as parameters *)
			      let returns =
				let f ity b acc =
				  if b
				  then (C.Tptr(ty_of_ty info (ty_of_ity ity)),
					id_register (id_fresh "result"))::acc
				  else acc
				in
				match rity.ity_node with
				| Ityapp(s, tl,_)
				| Ityreg { reg_its = s; reg_args = tl } ->
				   List.fold_right2 f tl s.its_arg_vis []
				| Ityvar _ -> assert false
			      in
			      {env with returns_tuple = true, List.map snd returns},
			      C.Tvoid,
			      returns@params
			   | _ -> env, rtype, params
			 in
			 let d,s = expr info env e in
			 (* let d,s = C.flatten_defs d s in *)
			 let s = C.elim_nop s in
			 let s = C.elim_empty_blocks s in
			 [C.Dfun (fname, (rtype,params), (d,s))]
                | _ -> raise (Unsupported
                                "Non-function with no syntax in toplevel let")
	        end
        with Unsupported s -> Format.printf "Unsupported : %s@." s; []
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
