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

exception Unsupported of string

module C = struct

  type struct_def = string * (string * ty) list

  and ty =
    | Tvoid
    | Tsyntax of string * ty list
    | Tptr of ty
    | Tarray of ty * expr
    | Tstruct of struct_def
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

  and binop = Band | Bor | Beq | Bne | Bassign | Blt | Ble | Bgt | Bge
  (* += and co. maybe to add *)

  and unop = Unot | Ustar | Uaddr | Upreincr | Upostincr | Upredecr | Upostdecr

  and expr =
    | Enothing
    | Eunop of unop * expr
    | Ebinop of binop * expr * expr
    | Equestion of expr * expr * expr (* c ? t : e *)
    | Ecast of ty * expr
    | Ecall of expr * expr list
    | Econst of constant
    | Evar of ident
    | Elikely of expr (* __builtin_expect(e,1) *)
    | Eunlikely of expr (* __builtin_expect(e,0) *)
    | Esize_expr of expr
    | Esize_type of ty
    | Eindex of expr * expr (* Array access *)
    | Edot of expr * string (* Field access with dot *)
    | Earrow of expr * string (* Pointer access with arrow *)
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
    | Dstruct of struct_def
    | Dtypedef of ty * ident

  and body = definition list * stmt

  type file = definition list

  exception NotAValue

  let rec is_nop = function
    | Snop -> true
    | Sblock ([], s) -> is_nop s
    | Sseq (s1,s2) -> is_nop s1 && is_nop s2
    | _ -> false

  let is_true = function
    | Sexpr(Econst(Cint "1")) -> true
    | _ -> false

  let is_false = function
    | Sexpr(Econst(Cint "0")) -> true
    | _ -> false

  let rec one_stmt = function
    | Snop -> true
    | Sexpr _ -> true
    | Sblock (d,s) -> d = [] && one_stmt s
    | _ -> false

  (** [assignify v] transforms a statement that computes a value into
     a statement that assigns that value to v *)
  let rec assignify v = function
    | Snop -> raise NotAValue
    | Sexpr e -> Sexpr (Ebinop (Bassign, v, e))
    | Sblock (ds, s) -> Sblock (ds, assignify v s)
    | Sseq (s1, s2) when not (is_nop s2) -> Sseq (s1, assignify v s2)
    | Sseq (s1,_) -> assignify v s1
    | Sif (c,t,e) -> Sif (c, assignify v t, assignify v e)
    | Swhile (c,s) -> Swhile (c, assignify v s) (* can this be a value ?*)
    | Sfor (e0,e1,e2,s) -> Sfor (e0,e1,e2, assignify v s)
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
    | Elikely e -> Elikely (propagate_in_expr id v e)
    | Eunlikely e -> Eunlikely (propagate_in_expr id v e)
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
    | Dstruct _ -> raise (Unsupported "struct declaration inside function")
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


  let rec group_defs_by_type l =
    (* heuristic to reduce the number of lines of defs*)
    let rec group_types t1 t2 =
      match t1, t2 with
      | Tsyntax (s1, l1), Tsyntax (s2, l2) ->
        List.length l1 = List.length l2
        && List.for_all2 group_types l1 l2
        && (s1 = s2)
        && (not (String.contains s1 '*'))
      | Tsyntax _, _ | _, Tsyntax _ -> false
      | t1, t2 -> t1 = t2
    in
    match l with
    | [] | [_] -> l
    | Ddecl (ty1, el1) :: Ddecl (ty2, el2) :: l'
        when group_types ty1 ty2
          -> group_defs_by_type (Ddecl(ty1, el1@el2)::l')
    | Ddecl (ty1, el1) :: Ddecl (ty2, el2) :: Ddecl (ty3, el3) :: l'
        when group_types ty1 ty3
          -> group_defs_by_type (Ddecl (ty1, el1@el3) :: Ddecl (ty2, el2) :: l')
    | Ddecl (ty1, el1) :: Ddecl (ty2, el2) :: Ddecl (ty3, el3) :: l'
        when group_types ty2 ty3
          -> group_defs_by_type (Ddecl (ty1, el1) :: Ddecl (ty2, el2@el3) :: l')
    | Ddecl (ty1, el1) :: l' ->
      Ddecl (ty1, el1) :: group_defs_by_type l'
    | _ -> l

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

  let rec stmt_of_list (l: stmt list) : stmt =
    match l with
    | [] -> Snop
    | [s] -> s
    | h::t -> Sseq (h, stmt_of_list t)

  let is_expr = function
    | Sexpr _ -> true
    | _ -> false

  let simplify_expr (d,s) : expr =
    match (d,s) with
    | [], Sexpr e -> e
    | _ -> raise (Invalid_argument "simplify_expr")

  let rec simplify_cond (cd, cs) =
    match cd,elim_empty_blocks(elim_nop cs) with
    | [], Sexpr c -> ([], Sexpr c)
    | ([], Sif (c', t', e') as b) ->
       let _,t' = simplify_cond ([], t') in
       let _,e' = simplify_cond ([], e') in
       if is_false e' && is_expr t'(* c' && t' *)
       then
         let t' = simplify_expr ([],t') in
         [], Sexpr(Ebinop(Band, c', t'))
       else if is_true e' && is_expr t' (* !c' || t' *)
       then
         let t' = simplify_expr ([],t') in
         [], Sexpr(Ebinop(Bor,Eunop(Unot,c'),t'))
       else if is_true t' && is_expr e' (* c' || e' *)
       then
         let e' = simplify_expr ([],e') in
         [], Sexpr(Ebinop(Bor,c',e'))
       else if is_false t' && is_expr e' (* !c' && e' *)
       then
         let e' = simplify_expr ([],e') in
         [], Sexpr(Ebinop(Band,Eunop(Unot,c'),e'))
       else b
    | d,s -> d, s

end

type info = Pdriver.printer_args = private {
  env         : Env.env;
  prelude     : Printer.prelude;
  thprelude   : Printer.prelude_map;
  blacklist   : Printer.blacklist;
  syntax      : Printer.syntax_map;
  converter   : Printer.syntax_map;
  literal     : Printer.syntax_map; (*TODO handle literals*)
}

let debug = false

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

  let extract_stars ty =
    let rec aux acc = function
      | Tptr t -> aux (acc+1) t
      | t -> (acc, t)
    in
  aux 0 ty

  let rec print_ty ?(paren=false) fmt = function
    | Tvoid -> fprintf fmt "void"
    | Tsyntax (s, tl) ->
      syntax_arguments
	s
        (print_ty ~paren:false) fmt tl
    | Tptr ty -> fprintf fmt "%a *" (print_ty ~paren:true) ty
    (* should be handled in extract_stars *)
    | Tarray (ty, expr) ->
      fprintf fmt (protect_on paren "%a[%a]")
        (print_ty ~paren:true) ty (print_expr ~paren:false) expr
    | Tstruct (s,_) -> fprintf fmt "struct %s" s
    | Tunion _ -> raise (Unprinted "unions")
    | Tnamed id -> print_ident fmt id
    | Tnosyntax -> raise (Unprinted "type without syntax")

  and print_unop fmt = function
    | Unot -> fprintf fmt "!"
    | Ustar -> fprintf fmt "*"
    | Uaddr -> fprintf fmt "&"
    | Upreincr | Upostincr -> fprintf fmt "++"
    | Upredecr | Upostdecr -> fprintf fmt "--"

  and unop_postfix = function
    | Upostincr | Upostdecr -> true
    | _ -> false

  and print_binop fmt = function
    | Band -> fprintf fmt "&&"
    | Bor -> fprintf fmt "||"
    | Beq -> fprintf fmt "=="
    | Bne -> fprintf fmt "!="
    | Bassign -> fprintf fmt "="
    | Blt -> fprintf fmt "<"
    | Ble -> fprintf fmt "<="
    | Bgt -> fprintf fmt ">"
    | Bge -> fprintf fmt ">="

  and print_expr ~paren fmt = function
    | Enothing -> if debug then Format.printf "enothing"; ()
    | Eunop(u,e) ->
       if unop_postfix u
       then fprintf fmt (protect_on paren "%a%a")
              (print_expr ~paren:true) e print_unop u
       else fprintf fmt (protect_on paren "%a%a")
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
    | Elikely e -> fprintf fmt (protect_on paren "__builtin_expect(%a,1)")
                           (print_expr ~paren:true) e
    | Eunlikely e -> fprintf fmt (protect_on paren "__builtin_expect(%a,0)")
                           (print_expr ~paren:true) e
    | Esize_expr e ->
      fprintf fmt (protect_on paren "sizeof(%a)") (print_expr ~paren:false) e
    | Esize_type ty ->
       fprintf fmt (protect_on paren "sizeof(%a)") (print_ty ~paren:false) ty
    | Edot (e,s) -> fprintf fmt "%a.%s" (print_expr ~paren:true) e s
    | Eindex _  | Earrow _ -> raise (Unprinted "struct/array access")
    | Esyntax (s, t, args, lte,_) ->
      gen_syntax_arguments_typed snd (fun _ -> args)
        (if paren then ("("^s^")") else s)
        (fun fmt (e,_t) -> print_expr ~paren:false fmt e)
        (print_ty ~paren:false) (C.Enothing,t) fmt lte

  and print_const  fmt = function
    | Cint s | Cfloat s | Cchar s | Cstring s -> fprintf fmt "%s" s

  let print_id_init ~stars fmt ie =
    (if stars > 0
    then fprintf fmt "%s " (String.make stars '*')
    else ());
    match ie with
    | id, Enothing -> print_ident fmt id
    | id,e -> fprintf fmt "%a = %a" print_ident id (print_expr ~paren:false) e

  let rec print_stmt ~braces fmt = function
    | Snop -> if debug then Format.printf "snop"; ()
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
    | Sfor (einit, etest, eincr, s) ->
       fprintf fmt "for (%a; %a; %a)@;<1 2>%a"
         (print_expr ~paren:false) einit
         (print_expr ~paren:false) etest
         (print_expr ~paren:false) eincr
         (print_stmt ~braces:true) (Sblock([],s))
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
      let nb, ty = extract_stars ty in
      assert (nb=0);
      fprintf fmt "%a @[<hov>%a@];"
	(print_ty ~paren:false) ty
	(print_list comma (print_id_init ~stars:nb)) lie
    | Dstruct (s, lf) ->
       fprintf fmt "struct %s@ @[<hov>{@;<1 2>@[<hov>%a@]@\n};@\n@]"
         s
         (print_list newline
            (fun fmt (s,ty) -> fprintf fmt "%a %s;"
                                 (print_ty ~paren:false) ty s))
         lf
    | Dinclude id ->
       fprintf fmt "#include<%a.h>@;" print_ident id
    | Dtypedef (ty,id) ->
       fprintf fmt "@[<hov>typedef@ %a@;%a;@]"
	 (print_ty ~paren:false) ty print_ident id
    with Unprinted s -> Format.printf "Missed a def because : %s@." s

  and print_body fmt (def, s) =
    if def = []
    then print_stmt ~braces:true fmt s
    else
      print_pair_delim nothing newline nothing
        (print_list newline print_def)
        (print_stmt ~braces:true)
        fmt (def,s)

  let print_file fmt info ast =
    Mid.iter (fun _ sl -> List.iter (fprintf fmt "%s\n") sl) info.thprelude;
    newline fmt ();
    fprintf fmt "@[<v>%a@]@." (print_list newline print_def) ast

end

(*TODO simplifications : propagate constants, collapse blocks with only a statement and no def*)

module MLToC = struct

  open Ity
  open Ty
  open Expr
  open Term
  open Printer
  open Mltree
  open C

  let rec ty_of_mlty info = function
    | Tvar tv ->
      begin match query_syntax info.syntax tv.tv_name
        with
        | Some s -> C.Tsyntax (s, [])
        | None -> C.Tnamed (tv.tv_name)
      end
    | Tapp (id, tl) ->
       begin match query_syntax info.syntax id
        with
        | Some s -> C.Tsyntax (s, List.map (ty_of_mlty info) tl)
        | None -> C.Tnosyntax
       end
    | Ttuple [] -> C.Tvoid
    | Ttuple _ -> raise (Unsupported "tuple parameters")

  let rec ty_of_ty info ty = (*FIXME try to use only ML tys*)
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
        | None -> if is_ts_tuple ts && tl = []
                  then C.Tvoid
                  else C.Tnosyntax
       end

  let ity_of_expr e = match e.e_ity with
    | I i -> i
    | _ -> assert false

  let pv_name pv = pv.pv_vs.vs_name

  type syntax_env = { in_unguarded_loop : bool;
                      computes_return_value : bool;
                      current_function : rsymbol;
		      breaks : Sid.t;
                      returns : Sid.t; }


  let is_true e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_true
    | _ -> false

  let is_false e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_false
    | _ -> false

  let is_unit = function
    | I i -> ity_equal i Ity.ity_unit
    | C _ -> false

  let return_or_expr env (e:C.expr) =
    if env.computes_return_value
    then Sreturn e
    else Sexpr e


  let likely = create_label "ex:likely"
  let unlikely = create_label "ex:unlikely"

  let handle_likely lbl (e:C.expr) =
    let lkl = Slab.mem likely lbl in
    let ulk = Slab.mem unlikely lbl in
    if lkl
    then (if ulk then e else Elikely e)
    else (if ulk then Eunlikely e else e)

  let reverse_likely = function
    | Elikely e -> Eunlikely e
    | Eunlikely e -> Elikely e
    | e -> e

  let field i = "__field_"^(string_of_int i)

  let struct_of_rs info rs =
    let rty = ty_of_ity rs.rs_cty.cty_result in
    match rty.ty_node with
    | Tyapp (ts, lt) ->
       assert (is_ts_tuple ts);
       let rec fields fr tys =
         match tys with
         | [] -> []
         | ty::l -> (field fr, ty_of_ty info ty)::(fields (fr+1) l) in
       let fields = fields 0 lt in
       let s = match query_syntax info.syntax rs.rs_name with
         | Some s -> s
         | None -> rs.rs_name.id_string in
       let name = Pp.sprintf "__%s_result" s in
       (name, fields)
    | _ -> assert false

  let struct_of_rs info = Wrs.memoize 17 (fun rs -> struct_of_rs info rs)

  let rec expr info env (e:Mltree.expr) : C.body =
    assert (not e.e_effect.eff_ghost);
    match e.e_node with
    | Eblock [] ->
       if env.computes_return_value
       then C.([], Sreturn(Enothing))
       else C.([], Snop)
    | Eblock [_] -> assert false
    | Eblock l ->
       let env_f = { env with computes_return_value = false } in
       let rec aux = function
         | [] ->
            if env.computes_return_value
            then C.([], Sreturn(Enothing))
            else C.([], Snop)
         | [s] -> ([], C.Sblock (expr info env s))
         | h::t -> ([], C.Sseq (C.Sblock (expr info env_f h),
                                C.Sblock (aux t)))
       in
       aux l
    | Eapp (rs, []) when rs_equal rs rs_true ->
       ([],return_or_expr env (C.Econst (Cint "1")))
    | Eapp (rs, []) when rs_equal rs rs_false ->
       ([],return_or_expr env (C.Econst (Cint "0")))
    | Mltree.Evar pv ->
       let e = C.Evar (pv_name pv) in
       ([], return_or_expr env e)
    | Mltree.Econst ic ->
      let n = Number.compute_int_constant ic in
      let e = C.(Econst (Cint (BigInt.to_string n))) in
      ([], return_or_expr env e)
    | Eapp (rs, el) ->
       if is_rs_tuple rs && env.computes_return_value
       then begin
	 let args =
           List.filter
             (fun e ->
               assert (not e.e_effect.eff_ghost);
               match e.e_ity with
               | I i when ity_equal i Ity.ity_unit -> false
               | _ -> true)
	     el
         in (*FIXME still needed with masks? *)
         let env_f = { env with computes_return_value = false } in
         let id_struct = id_register (id_fresh "result") in
         let e_struct = C.Evar id_struct in
         let d_struct = C.(Ddecl(Tstruct
                                   (struct_of_rs info env.current_function),
                                 [id_struct, Enothing])) in
         let assign i (d,s) =
           C.Sblock (d,assignify C.(Edot (e_struct, field i)) s) in
         let rec assigns args i =
           match args with
           | [] -> Snop
           | e::t ->
              let b = expr info env_f e in
              C.Sseq(assign i b, assigns t (i+1)) in
	 C.([d_struct], Sseq(assigns args 0, Sreturn(e_struct)))
	 end
       else
	 let e' =
           match
             (query_syntax info.syntax rs.rs_name,
              query_syntax info.converter rs.rs_name) with
           | _, Some s
             | Some s, _ ->
              begin
                try
                  let _ =
                    Str.search_forward
                      (Str.regexp "[%]\\([tv]?\\)[0-9]+") s 0 in
                  let env_f =
                    { env with computes_return_value = false } in
                  let params =
		    List.map
                      (fun e ->
                        (simplify_expr (expr info env_f e),
                         ty_of_ty info (ty_of_ity (ity_of_expr e))))
		      el in
		  let rty = ty_of_ity (match e.e_ity with
                                       | C _ -> assert false
                                       | I i -> i) in
		  let rtyargs = match rty.ty_node with
		    | Tyvar _ -> [||]
		    | Tyapp (_,args) ->
                       Array.of_list (List.map (ty_of_ty info) args)
		  in
		  C.Esyntax(s,ty_of_ty info rty, rtyargs, params,
                            Mid.mem rs.rs_name info.converter)
                with Not_found ->
		  let args =
                    List.filter
                      (fun e ->
                        assert (not e.e_effect.eff_ghost);
                        match e.e_ity with
                        | I i when ity_equal i Ity.ity_unit -> false
                        | _ -> true)
		      el
                  in
                  if args=[]
                  then C.(Esyntax(s, Tnosyntax, [||], [], true)) (*constant*)
                  else
                    (*function defined in the prelude *)
                    let env_f =
                      { env with computes_return_value = false } in
		    C.(Ecall(Esyntax(s, Tnosyntax, [||], [], true),
			     List.map
                               (fun e ->
                                 simplify_expr (expr info env_f e))
                               el))
              end
           | _ ->
              let args =
                List.filter
                  (fun e ->
                    assert (not e.e_effect.eff_ghost);
                    match e.e_ity with
                    | I i when ity_equal i Ity.ity_unit -> false
                    | _ -> true)
		  el in
              let env_f =
                { env with computes_return_value = false } in
	      C.(Ecall(Evar(rs.rs_name), List.map
                                           (fun e ->
                                             simplify_expr (expr info env_f e))
                                           args))
         in
	 C.([],
            if env.computes_return_value
	    then
              begin match e.e_ity with
              | I ity when ity_equal ity Ity.ity_unit ->
                 Sseq(Sexpr e', Sreturn Enothing)
              | I _ -> Sreturn e'
              | _ -> assert false
              end
            else Sexpr e')
    | Elet (ld,e) ->
       begin match ld with
       | Lvar (pv,le) -> (* not a block *)
          begin
          match le.e_node with
          | Mltree.Econst ic ->
            let n = Number.compute_int_constant ic in
            let ce = C.(Econst (Cint (BigInt.to_string n))) in
	    if debug then Format.printf "propagate constant %s for var %s@."
			  (BigInt.to_string n) (pv_name pv).id_string;
            C.propagate_in_block (pv_name pv) ce (expr info env e)
          | Eapp (rs,_) when Mid.mem rs.rs_name info.converter ->
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
              if debug then Format.printf "propagate converter for var %s@."
                (pv_name pv).id_string;
              C.propagate_in_block (pv_name pv) se (expr info env e)
            | d,s ->
              let initblock = d, C.assignify (Evar (pv_name pv)) s in
              [ C.Ddecl (t, [pv_name pv, C.Enothing]) ],
              C.Sseq (C.Sblock initblock, C.Sblock (expr info env e))
          end
      | Lsym _ -> raise (Unsupported "LDsym")
      | Lrec _ -> raise (Unsupported "LDrec") (* TODO for rec at least*)
      | Lany _ -> raise (Unsupported "Lany")
       end
    | Eif (cond, th, el) ->
       let cd,cs = expr info {env with computes_return_value = false} cond in
       let t = expr info env th in
       let e = expr info env el in
       begin match simplify_cond (cd, cs) with
       | [], C.Sexpr c ->
          let c = handle_likely cond.e_label c in
          if is_false th && is_true el
	  then C.([], Sexpr(Eunop(Unot, c)))
	  else [], C.Sif(c,C.Sblock t, C.Sblock e)
       | cdef, cs ->
	  let cid = id_register (id_fresh "cond") in (* ? *)
	  C.Ddecl (C.Tsyntax ("int",[]), [cid, C.Enothing])::cdef,
	  C.Sseq (C.assignify (Evar cid) cs,
                  C.Sif ((handle_likely cond.e_label (C.Evar cid)),
                         C.Sblock t, C.Sblock e))
       end
    | Ewhile (c,b) ->
       if debug then Format.printf "while@.";
      let cd, cs = expr info {env with computes_return_value = false} c in
      (* this is needed so that the extracted expression has all
         needed variables in its scope *)
      let cd, cs = C.flatten_defs cd cs in
      let cd = C.group_defs_by_type cd in
      let env' = { computes_return_value = false;
                   in_unguarded_loop = true;
		   returns = env.returns;
                   current_function = env.current_function;
                   breaks =
                     if env.in_unguarded_loop
                     then Sid.empty else env.breaks } in
      let b = expr info  env' b in
      begin match (C.simplify_cond (cd,cs)) with
      | cd, C.Sexpr ce -> cd, C.Swhile (handle_likely c.e_label ce, C.Sblock b)
      | _ ->
        begin match C.get_last_expr cs with
        | C.Snop, e -> cd, C.(Swhile(handle_likely c.e_label e, C.Sblock b))
        | s,e ->
           let brc = reverse_likely (handle_likely c.e_label (Eunop(Unot,e))) in
           cd, C.(Swhile(Econst (Cint "1"),
                         Sseq(s,
                              Sseq(Sif(brc, Sbreak, Snop),
                                   C.Sblock b))))
        end
      end
    | Ematch (b, [], (_::_ as xl)) ->
      if debug then Format.printf "TRY@.";
      let is_while = match b.e_node with Ewhile _ -> true | _-> false in
      let breaks, returns = List.fold_left
        (fun (bs,rs) (xs, pvsl, r) ->
          let id = xs.xs_name in
          match pvsl, r.e_node with
          | [pv], Mltree.Evar pv'
            when pv_equal pv pv' && env.computes_return_value ->
            (bs, Sid.add id rs)
          | [], (Eblock []) when is_unit r.e_ity && is_while ->
            (Sid.add id bs, rs)
          |_ -> raise (Unsupported "non break/return exception in try"))
        (Sid.empty, env.returns) xl
      in
      let env' = { computes_return_value = env.computes_return_value;
                   in_unguarded_loop = false;
                   current_function = env.current_function;
		   breaks = breaks;
                   returns = returns;
                 } in
      expr info env' b
    | Eraise (xs,_) when Sid.mem xs.xs_name env.breaks ->
      if debug then Format.printf "BREAK@.";
      ([], C.Sbreak)
    | Eraise (xs, Some r) when Sid.mem xs.xs_name env.returns ->
      if debug then Format.printf "RETURN@.";
      expr info {env with computes_return_value = true} r
    | Eraise (_, None) -> assert false (* nothing to pass to return *)
    | Eraise _ -> raise (Unsupported "non break/return exception raised")
    | Efor (i, sb, dir, eb, body) ->
       begin match i.pv_vs.vs_ty.ty_node with
       | Tyapp ({ ts_def = Range _ },_) ->
          let ty = ty_of_ty info i.pv_vs.vs_ty in
          let di = C.Ddecl(ty, [i.pv_vs.vs_name, Enothing]) in
          let ei = C.Evar (i.pv_vs.vs_name) in
          let init_e = C.Ebinop (Bassign, ei, C.Evar (sb.pv_vs.vs_name)) in
          let incr_op = match dir with To -> C.Upostincr | DownTo -> C.Upostdecr in
          let incr_e = C.Eunop (incr_op, ei) in
          let init_test_op = match dir with | To -> C.Blt | DownTo -> C.Bgt in
          let init_test = C.Sif (C.Ebinop(init_test_op,
                                          C.Evar (eb.pv_vs.vs_name),
                                          C.Evar (sb.pv_vs.vs_name)),
                                 Sbreak, Snop) in
          let end_test = C.Sif (C.Ebinop (C.Beq, ei, C.Evar eb.pv_vs.vs_name),
                                Sbreak, Snop) in
          let env' = { env with computes_return_value = false;
                                in_unguarded_loop = true;
                                breaks =
                                  if env.in_unguarded_loop
                                  then Sid.empty else env.breaks } in
          let bd, bs = expr info env' body in
          let bs = C.Sseq(init_test, C.Sseq (bs, end_test)) in
          [di], C.Sfor(init_e, Enothing, incr_e, C.Sblock (bd,bs))
       |  _ -> raise (Unsupported "for loops")
       end
    | Ematch (({e_node = Eapp(rs,_)} as e1), [Ptuple rets,e2], [])
         when List.for_all
                (function | Pwild (*ghost*) | Pvar _ -> true |_-> false)
                rets
      ->
       let id_struct = id_register (id_fresh "struct_res") in
       let e_struct = C.Evar id_struct in
       let d_struct = C.Ddecl(C.Tstruct (struct_of_rs info rs),
                              [id_struct, C.Enothing]) in
       let defs =
         List.fold_right
           (fun p acc ->
             match p with
             | Pvar vs -> C.Ddecl(ty_of_ty info vs.vs_ty,
                                  [vs.vs_name, C.Enothing])::acc
             | Pwild -> acc
             | _ -> assert false )
        rets [d_struct] in
       let d,s = expr info {env with computes_return_value = false} e1 in
       let s = assignify e_struct s in
       let assign vs i =
         assignify (C.Evar vs) C.(Sexpr (Edot (e_struct, field i))) in
       let rec assigns rets i =
         match rets with
         | [] -> C.Snop
         | Pvar vs :: t -> C.Sseq ((assign vs.vs_name i), (assigns t (i+1)))
         | Pwild :: t -> assigns t (i+1) (* ghost variable, skip *)
         | _ -> assert false in
       let assigns = assigns rets 0 in
       let b = expr info env e2 in
       d@defs, C.(Sseq(Sseq(s,assigns), Sblock b))
    | Ematch _ -> raise (Unsupported "pattern matching")
    | Eabsurd -> assert false
    | Eassign ([pv, ({rs_field = Some _} as rs), v]) ->
       let t =
         match (query_syntax info.syntax rs.rs_name,
                      query_syntax info.converter rs.rs_name) with
         | _, Some s | Some s, _ ->
            let _ =
              try
                Str.search_forward
                  (Str.regexp "[%]\\([tv]?\\)[0-9]+") s 0
              with Not_found -> raise (Unsupported "assign field format")  in
            let params = [ C.Evar pv.pv_vs.vs_name,
                           ty_of_ty info (ty_of_ity pv.pv_ity) ] in
            let rty = ty_of_ity rs.rs_cty.cty_result in
            let rtyargs = match rty.ty_node with
	      | Tyvar _ -> [||]
	      | Tyapp (_,args) ->
                 Array.of_list (List.map (ty_of_ty info) args)
	    in
            C.Esyntax(s,ty_of_ty info rty, rtyargs, params,
                      Mid.mem rs.rs_name info.converter)
         | None, None -> raise (Unsupported ("assign not in driver")) in
       [], C.(Sexpr(Ebinop(Bassign, t, C.Evar v.pv_vs.vs_name)))
    | Eassign _ -> raise (Unsupported "assign")
    | Ehole -> assert false
    | Eexn _ -> raise (Unsupported "exception")
    | Eignore e ->
       [], C.Sseq(C.Sblock(expr info {env with computes_return_value = false} e),
              if env.computes_return_value
              then C.Sreturn(Enothing)
              else C.Snop)
    | Efun _ -> raise (Unsupported "higher order")

  let translate_decl (info:info) (d:decl) : C.definition list
    =
    match d with
    | Dlet (Lsym(rs, _, vl, e)) ->
       if rs_ghost rs
       then begin if debug then Format.printf "is ghost@."; [] end
       else
         begin try
           let params =
             List.map (fun (id, ty, _gh) -> (ty_of_mlty info ty, id))
               (List.filter (fun (_,_, gh) -> not gh) vl) in
           let params = List.filter (fun (ty, _) -> ty <> C.Tvoid) params in
	   let env = { computes_return_value = true;
		       in_unguarded_loop = false;
                       current_function = rs;
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
	   let rtype = ty_of_ty info (ty_of_ity rity) in
           let rtype,sdecls =
             if rtype=C.Tnosyntax && is_simple_tuple rity
             then
               let st = struct_of_rs info rs in
               C.Tstruct st, [C.Dstruct st]
             else rtype, [] in
	   let d,s = expr info env e in
           (*TODO check if we want this flatten*)
	   let d,s = C.flatten_defs d s in
           let d = C.group_defs_by_type d in
	   let s = C.elim_nop s in
	   let s = C.elim_empty_blocks s in
	   sdecls@[C.Dfun (rs.rs_name, (rtype,params), (d,s))]
           with Unsupported s ->
             Format.printf "Unsupported : %s@." s; []
         end
    | Dtype [{its_name=id; its_def=idef}] ->
      if debug then Format.printf "PDtype %s@." id.id_string;
      begin
        match idef with
        | Some (Dalias ty) -> [C.Dtypedef (ty_of_mlty info ty, id)]
        | Some _ -> raise (Unsupported "Ddata/Drecord@.")
        | None ->
          begin match query_syntax info.syntax id with
          | Some _ -> []
          | None ->
             raise (Unsupported ("type declaration without syntax or alias: "^id.id_string))
          end
      end

    | _ -> [] (*TODO exn ? *)

  let translate_decl (info:info) (d:Mltree.decl) : C.definition list
    =
    let decide_print id = query_syntax info.syntax id = None in
    match Mltree.get_decl_name d with
    | [id] when decide_print id ->
       if debug then Format.printf "print %s@." id.id_string;
       translate_decl info d
    | [_] -> []
    | _ -> raise (Unsupported "no name or recursive defs")


end


let fg ?fname m =
  let n = m.Pmodule.mod_theory.Theory.th_name.Ident.id_string in
  match fname with
  | None -> n ^ ".c"
  | Some f -> f ^ "__" ^ n ^ ".c"
(*
let pr args ?old ?fname ~flat m fmt _d =
  ignore(old);
  let ast = Translate.translate args m in
  try Print.print_file fmt args ast
  with Print.Unprinted s -> (Format.printf "Could not print: %s@." s;
		       Format.fprintf fmt "/* Dummy file */@.")
*)
let print_decl args ?old ?fname ~flat m fmt d =
  ignore old;
  ignore fname;
  ignore flat; (*FIXME*)
  ignore m;
  let cds = MLToC.translate_decl args d in
  List.iter (Format.fprintf fmt "%a@." Print.print_def) cds

let () =
  Pdriver.register_printer "c" ~desc:"printer for C code" fg print_decl

(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
