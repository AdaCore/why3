(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident

exception Unsupported = Printer.Unsupported
let current_decl_name = ref ""

module C = struct

  (* struct name, fields) *)
  type struct_def = string * (string * ty) list

  and ty =
    | Tvoid
    | Tsyntax of string * ty list
    | Tptr of ty
    | Tarray of ty * expr
    | Tstruct of struct_def
    | Tunion of ident * (ident * ty) list
    | Tnamed of ident (* alias from typedef *)
    | Tmutable of ty (* struct with a single mutable field *)
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
    | Esyntaxrename of string * expr list (* syntax val f "g" w/o params *)
    | Esyntax of string * ty * (ty array) * (expr*ty) list * int list
  (* template, type and type arguments of result, typed arguments, precedence level *)

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

  and include_kind = Sys | Proj (* include <...> vs. include "..." *)
  and definition =
    | Dfun of ident * proto * body
    | Dinclude of ident * include_kind
    | Dproto of ident * proto
    | Ddecl of names
    | Dstruct of struct_def
    | Dstruct_decl of string
    | Dtypedef of ty * ident

  and body = definition list * stmt

  type file = definition list

  exception NotAValue

  let rec is_nop = function
    | Snop | Sexpr Enothing -> true
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
     This is needed when loop conditions are more complex than a
     simple expression. *)
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
    | Sif _ -> raise (Unsupported "for/while (complex if)")
    | Swhile (_c,_s) -> raise (Unsupported "for/while (while) {}")
    | Sfor _ -> raise (Unsupported "for/while (for)")
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
    | Esyntax (s,t,ta,l,p) ->
       Esyntax (s,t,ta,List.map (fun (e,t) -> (propagate_in_expr id v e),t) l,p)
    | Esyntaxrename (s, l) ->
       Esyntaxrename (s, List.map (propagate_in_expr id v) l)
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
    | Dinclude (i,k) -> Dinclude (i,k), true
    | Dstruct _ -> raise (Unsupported "struct declaration inside function")
    | Dfun _ -> raise (Unsupported "nested function")
    | Dtypedef _ | Dproto _ | Dstruct_decl _ -> assert false

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
    | Sbreak | Snop | Sexpr _ | Sreturn _ as s -> d, s

  let rec group_defs_by_type l =
    (* heuristic to reduce the number of lines of defs*)
    let rec group_types t1 t2 =
      match t1, t2 with
      | Tvoid, Tvoid -> true
      | Tsyntax (s1, l1), Tsyntax (s2, l2) ->
        List.length l1 = List.length l2
        && List.for_all2 group_types l1 l2
        && s1 = s2
        && (not (String.contains s1 '*'))
      | Tptr t, Tptr t' -> group_types t t'
      | Tarray _, _ -> false
      | Tstruct (n1, _), Tstruct (n2, _) -> n1 = n2
      | Tunion (id1, _), Tunion (id2, _) -> id_equal id1 id2
      | Tnamed id1, Tnamed id2 -> id_equal id1 id2
      | Tmutable t, Tmutable t' -> group_types t t'
      | _,_ -> false
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
    | Snop | Sbreak | Sexpr _ | Sreturn _ as s -> s

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
    | Snop | Sbreak | Sexpr _ | Sreturn _ as s -> s

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

  let rec simplify_expr (d,s) : expr =
    match (d,elim_empty_blocks(elim_nop s)) with
    | [], Sblock([],s) -> simplify_expr ([],s)
    | [], Sexpr e -> e
    | [], Sif(c,t,e) ->
       Equestion (c, simplify_expr([],t), simplify_expr([],e))
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

(* Operator precedence, needed to compute which parentheses can be removed *)

  let prec_unop = function
    | Unot | Ustar | Uaddr | Upreincr | Upredecr -> 2
    | Upostincr  | Upostdecr -> 1

  let prec_binop = function
    | Band -> 11
    | Bor -> 11 (* really 12, but this avoids Wparentheses *)
    | Beq | Bne -> 7
    | Bassign -> 14
    | Blt | Ble | Bgt | Bge -> 6

  let is_const_unop (u:unop) = match u with
    | Unot -> true
    | Ustar | Uaddr | Upreincr | Upostincr | Upredecr | Upostdecr -> false

  let is_const_binop (b:binop) = match b with
    | Band | Bor | Beq | Bne | Blt | Ble | Bgt | Bge -> true
    | Bassign -> false

  let rec is_const_expr = function
    | Enothing -> true
    | Eunop (u,e) -> is_const_unop u && is_const_expr e
    | Ebinop (b,e1,e2) ->
       is_const_binop b && is_const_expr e1 && is_const_expr e2
    | Equestion (c,_,_) -> is_const_expr c
    | Ecast (_,_) -> true
    | Ecall (_,_) -> false
    | Econst _ -> true
    | Evar _ -> false
    | Elikely e | Eunlikely e -> is_const_expr e
    | Esize_expr _ -> false
    | Esize_type _ -> true
    | Eindex (_,_) | Edot (_,_) | Earrow (_,_) -> false
    | Esyntax (_,_,_,_,_) -> false
    | Esyntaxrename _ -> false

  let rec get_const_expr (d,s) =
    let fail () = raise (Unsupported "non-constant array size") in
    if (d = [])
    then match elim_empty_blocks (elim_nop s) with
    | Sexpr e -> if is_const_expr e then e
                 else fail ()
    | Sblock (d, s) -> get_const_expr (d,s)
    | _ -> fail ()
    else fail ()

  let rec has_unboxed_struct = function
    | Tstruct _ -> true
    | Tmutable _ -> true
    | Tunion (_, lidty)  -> List.exists has_unboxed_struct (List.map snd lidty)
    | Tsyntax (_, lty) -> List.exists has_unboxed_struct lty
    | _ -> false

  let rec has_array = function
    | Tarray _ -> true
    | Tmutable t -> has_array t
    | Tsyntax (_,lty) -> List.exists has_array lty
    | Tstruct (_, lsty) -> List.exists has_array (List.map snd lsty)
    | Tunion (_,lidty) -> List.exists has_array (List.map snd lidty)
    | _ -> false

  let rec should_not_escape = function
    | Tstruct _ -> true
    | Tarray _ -> true
    | Tmutable _ -> true
    | Tunion (_, lidty)  -> List.exists should_not_escape (List.map snd lidty)
    | Tsyntax (_, lty) -> List.exists should_not_escape lty
    | _ -> false

  let left_assoc = function
    | Beq | Bne | Blt | Ble | Bgt | Bge -> true
    | Bassign -> false
    | Band | Bor -> false (* avoids Wparentheses *)

  let right_assoc = function
    | Bassign -> true
    | _ -> false

  let e_map fe (e:expr) =
    match e with
    | Enothing -> Enothing
    | Eunop (u,e) -> Eunop (u, fe e)
    | Ebinop (b, e1, e2) -> Ebinop (b, fe e1, fe e2)
    | Equestion (c, t, e) -> Equestion (fe c, fe t, fe e)
    | Ecast (t,e) -> Ecast(t, fe e)
    | Ecall (f,args) -> Ecall (fe f, List.map fe args)
    | Econst c -> Econst c
    | Evar v -> Evar v
    | Elikely e -> Elikely (fe e)
    | Eunlikely e -> Eunlikely (fe e)
    | Esize_expr e -> Esize_expr (fe e)
    | Esize_type t -> Esize_type t
    | Eindex (a,i) -> Eindex (fe a, fe i)
    | Edot (e,f) -> Edot (fe e, f)
    | Earrow (e, f) -> Earrow (fe e, f)
    | Esyntaxrename (s,args) -> Esyntaxrename (s, List.map fe args)
    | Esyntax (s,rt,ta,args,pl) ->
       Esyntax (s, rt, ta, List.map (fun (e, t) -> (fe e, t)) args, pl)

  let s_map fd fs fe (s:stmt) = match s with
    | Snop -> Snop
    | Sexpr e -> Sexpr (fe e)
    | Sblock (d,s) -> Sblock (List.map fd d, fs s)
    | Sseq (s1,s2) -> Sseq (fs s1, fs s2)
    | Sif (ce,ts,es) -> Sif (fe ce, fs ts, fs es)
    | Swhile (c,b) -> Swhile (fe c, fs b)
    | Sfor (e1,e2,e3,b) -> Sfor (fe e1, fe e2, fe e3, fs b)
    | Sbreak -> Sbreak
    | Sreturn e -> Sreturn (fe e)

  (** Integer type bounds *)
  open BigInt
  let min32 = minus (pow_int_pos 2 31)
  let max32 = sub (pow_int_pos 2 31) one
  let maxu32 = sub (pow_int_pos 2 32) one
  let min64 = minus (pow_int_pos 2 63)
  let max64 = sub (pow_int_pos 2 63) one
  let maxu64 = sub (pow_int_pos 2 64) one

end

type info = {
  env         : Env.env;
  prelude     : Printer.prelude;
  thprelude   : Printer.prelude_map;
  thinterface : Printer.interface_map;
  blacklist   : Printer.blacklist;
  syntax      : Printer.syntax_map;
  literal     : Printer.syntax_map; (*TODO handle literals*)
  kn          : Pdecl.known_map;
  prec        : (int list) Mid.t;
}

let debug_c_extraction = Debug.register_info_flag
                           ~desc:"C extraction"
                           "c_extraction"
let debug_c_no_error_msgs =
  Debug.register_flag
    ~desc:"Disable the printing of the error messages in the C extraction"
    "c_no_error_msgs"

module Print = struct

  open C
  open Format
  open Printer
  open Pp

  exception Unprinted of string

  let c_keywords = ["auto"; "break"; "case"; "char"; "const"; "continue"; "default"; "do"; "double"; "else"; "enum"; "extern"; "float"; "for"; "goto"; "if"; "int"; "long"; "register"; "return"; "short"; "signed"; "sizeof"; "static"; "struct"; "switch"; "typedef"; "union"; "unsigned"; "void"; "volatile"; "while" ]

  let () = assert (List.length c_keywords = 32)

  let sanitizer = sanitizer char_to_lalpha char_to_alnumus
  let sanitizer s = Strings.lowercase (sanitizer s)
  let local_printer = create_ident_printer c_keywords ~sanitizer
  let global_printer = create_ident_printer c_keywords ~sanitizer

  let c_static_inline = create_attribute "extraction:c_static_inline"
  (* prints the c inline keyword *)

  let print_local_ident fmt id = fprintf fmt "%s" (id_unique local_printer id)
  let print_global_ident fmt id = fprintf fmt "%s" (id_unique global_printer id)

  let clear_local_printer () = Ident.forget_all local_printer

  let space_nolinebreak fmt () = fprintf fmt " "

  let protect_on ?(boxed=false) x s =
    if x then "@[<1>(" ^^ s ^^ ")@]"
    else if not boxed then "@[" ^^ s ^^ "@]"
    else s

  let extract_stars ty =
    let rec aux acc = function
      | Tptr t -> aux (acc+1) t
      | t -> (acc, t)
    in
  aux 0 ty

  let char_escape c = match c with
    | '\'' -> "\\'"
    | _ -> Constant.default_escape c

  let rec print_ty ?(paren=false) fmt = function
    | Tvoid -> fprintf fmt "void"
    | Tsyntax (s, tl) ->
      syntax_arguments s (print_ty ~paren:false) fmt tl
    | Tptr ty -> fprintf fmt "%a *" (print_ty ~paren:true) ty
    (* should be handled in extract_stars *)
    | Tarray (ty, Enothing) ->
       fprintf fmt (protect_on paren "%a *")
         (print_ty ~paren:true) ty
    (* raise (Unprinted "printing array type with unknown size")*)
    | Tarray (ty, expr) ->
      fprintf fmt (protect_on paren "%a[%a]")
        (print_ty ~paren:true) ty (print_expr ~prec:1) expr
    | Tstruct (s,_) -> fprintf fmt "struct %s" s
    | Tunion _ -> raise (Unprinted "unions")
    | Tnamed id -> print_global_ident fmt id
    | Tmutable ty -> print_ty ~paren fmt ty
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

  and print_expr ~prec fmt = function
    (* invariant: 0 <= prec <= 15 *)
    | Enothing -> ()
    | Eunop(u,e) ->
       let p = prec_unop u in
       if unop_postfix u
       then fprintf fmt (protect_on (prec < p) "%a%a")
              (print_expr ~prec:(p-1)) e print_unop u
       else fprintf fmt (protect_on (prec < p) "%a%a")
              print_unop u (print_expr ~prec:(p-1)) e
    | Ebinop(b,e1,e2) ->
       let p = prec_binop b in
       let pleft = if left_assoc b then p else p-1 in
       let pright = if right_assoc b then p else p-1 in
       fprintf fmt (protect_on (prec < p) "%a %a %a")
         (print_expr ~prec:pleft) e1 print_binop b (print_expr ~prec:pright) e2
    | Equestion(c,t,e) ->
      fprintf fmt (protect_on (prec < 13) "%a ? %a : %a")
        (print_expr ~prec:12) c
        (print_expr ~prec:15) t
        (print_expr ~prec:13) e
    | Ecast(ty, e) ->
      fprintf fmt (protect_on (prec < 2) "(%a)%a")
        (print_ty ~paren:false) ty (print_expr ~prec:2) e
    | Esyntaxrename (s, l) ->
       (* call to function defined in the prelude *)
       fprintf fmt (protect_on (prec < 1) "%s(%a)")
         s (print_list comma (print_expr ~prec:15)) l
    | Ecall (Evar id, l) ->
       fprintf fmt (protect_on (prec < 1) "%a(%a)")
         print_global_ident id (print_list comma (print_expr ~prec:15)) l
    | Ecall ((Esyntax _ as e),l) ->
       fprintf fmt (protect_on (prec < 1) "%a(%a)")
         (print_expr ~prec:1) e (print_list comma (print_expr ~prec:15)) l
    | Ecall _ -> raise (Unsupported "complex function expression")
    | Econst c -> print_const fmt c
    | Evar id -> print_local_ident fmt id
    | Elikely e -> fprintf fmt
                     (protect_on (prec < 1) "__builtin_expect(%a,1)")
                     (print_expr ~prec:15) e
    | Eunlikely e -> fprintf fmt
                       (protect_on (prec < 1) "__builtin_expect(%a,0)")
                       (print_expr ~prec:15) e
    | Esize_expr e ->
       fprintf fmt (protect_on (prec < 2) "sizeof(%a)") (print_expr ~prec:15) e
    | Esize_type ty ->
       fprintf fmt (protect_on (prec < 2) "sizeof(%a)")
         (print_ty ~paren:false) ty
    | Edot (e,s) ->
       fprintf fmt (protect_on (prec < 1) "%a.%s")
         (print_expr ~prec:1) e s
    | Eindex (e1, e2) ->
       fprintf fmt (protect_on (prec <= 1) "%a[%a]")
                      (print_expr ~prec:1) e1
                      (print_expr ~prec:15) e2
    | Earrow (e,s) ->
       fprintf fmt (protect_on (prec <= 1) "%a->%s")
         (print_expr ~prec:1) e s
    | Esyntax ("%1", _, _, [e,_], _) ->
        print_expr ~prec fmt e
    | Esyntax (s, t, args, lte, pl) ->
        let s =
          if pl = [] || prec < List.hd pl
          then Format.sprintf "(%s)" s
          else s in
        let lte = Array.of_list lte in
        let pr fmt p c i =
          match c with
          | None -> print_expr ~prec:p fmt (fst lte.(i - 1))
          | Some 't' ->
              let v = if i = 0 then t else snd lte.(i - 1) in
              print_ty ~paren:false fmt v
          | Some 'v' ->
              print_ty ~paren:false fmt args.(i)
          | Some 'd' -> (* dereference the value *)
              begin match fst lte.(i - 1) with
              | Eunop (Uaddr, e) -> print_expr ~prec:p fmt e
              | e -> print_expr ~prec:p fmt (Eunop (Ustar, e))
              end
          | Some c -> raise (BadSyntaxKind c) in
        gen_syntax_arguments_prec fmt s pr pl

  and print_const  fmt = function
    | Cint s | Cfloat s -> fprintf fmt "%s" s
    | Cchar s -> fprintf fmt "'%s'" Constant.(escape char_escape s)
    | Cstring s -> fprintf fmt "\"%s\"" Constant.(escape default_escape s)

  let print_id_init ?(size=None) ~stars fmt ie =
    (if stars > 0
    then fprintf fmt "%s " (String.make stars '*')
     else ());
    match size, ie with
    | None, (id, Enothing) -> print_local_ident fmt id
    | None, (id,e) ->
       fprintf fmt "%a = %a"
         print_local_ident id (print_expr ~prec:(prec_binop Bassign)) e
    | Some Enothing, (id, Enothing) ->
       (* size unknown, treat as pointer *)
       fprintf fmt "* %a" print_local_ident id
    | Some e, (id, Enothing) ->
       fprintf fmt "%a[%a]" print_local_ident id (print_expr ~prec:15) e
    | Some _es, (_id, _ei) -> raise (Unsupported "array initializer")

  let print_expr_no_paren fmt expr = print_expr ~prec:max_int fmt expr

  let rec print_stmt ~braces fmt = function
    | Snop | Sexpr Enothing -> Debug.dprintf debug_c_extraction "snop"; ()
    | Sexpr e -> fprintf fmt "%a;" print_expr_no_paren e;
    | Sblock ([] ,s) when not braces ->
      (print_stmt ~braces:false) fmt s
    | Sblock b ->
       fprintf fmt "@[<hov>{@\n  @[<hov>%a@]@\n}@]" print_body b
    | Sseq (s1,s2) -> fprintf fmt "%a@\n%a"
      (print_stmt ~braces:false) s1
      (print_stmt ~braces:false) s2
    | Sif(c,t,e) when is_nop e ->
       fprintf fmt "@[<hov 2>if (%a) {@\n@[<hov>%a@]@]@\n}"
         print_expr_no_paren c (print_stmt ~braces:false) t
    | Sif(c,t,e) ->
       fprintf fmt
         "@[<hov 2>if (%a) {@\n@[<hov>%a@]@]@\n@[<hov 2>} else {@\n@[<hov>%a@]@]@\n}"
         print_expr_no_paren c
         (print_stmt ~braces:false) t
         (print_stmt ~braces:false) e
    | Swhile (e,b) -> fprintf fmt "@[<hov 2>while (%a) {@\n@[<hov>%a@]@]@\n}"
      print_expr_no_paren e (print_stmt ~braces:false) b
    | Sfor (einit, etest, eincr, s) ->
       fprintf fmt "@[<hov 2>for (%a; %a; %a) {@\n@[<hov>%a@]@]@\n}"
         print_expr_no_paren einit
         print_expr_no_paren etest
         print_expr_no_paren eincr
         (print_stmt ~braces:false) s
    | Sbreak -> fprintf fmt "break;"
    | Sreturn Enothing -> fprintf fmt "return;"
    | Sreturn e -> fprintf fmt "return %a;" print_expr_no_paren e

  and print_def fmt def =
    let print_inline fmt id =
      if Sattr.mem c_static_inline id.id_attrs
      then fprintf fmt "static inline "
      else fprintf fmt "" in
    try match def with
      | Dfun (id,(rt,args),body) ->
         let s = sprintf "@[@\n@[<hv 2>%a%a %a(@[%a@]) {@\n@[%a@]@]\n}@]"
                   print_inline id
                   (print_ty ~paren:false) rt
                   print_global_ident id
                   (print_list comma
                      (print_pair_delim nothing space_nolinebreak nothing
                         (print_ty ~paren:false) print_local_ident))
                   args
                   print_body body in
         (* print into string first to print nothing in case of exception *)
         fprintf fmt "%s" s
      | Dproto (id, (rt, args)) ->
         let s = sprintf "@\n%a %a(@[%a@]);"
                   (print_ty ~paren:false) rt
                   print_global_ident id
                   (print_list comma
                      (print_pair_delim nothing space_nolinebreak nothing
                         (print_ty ~paren:false) print_local_ident))
                   args in
         fprintf fmt "%s" s
      | Ddecl (Tarray(ty, e), lie) ->
         let s = sprintf "%a @[<hov>%a@];"
                   (print_ty ~paren:false) ty
                   (print_list comma (print_id_init ~stars:0 ~size:(Some e)))
                   lie in
         fprintf fmt "%s" s
      | Ddecl (ty, lie) ->
         let nb, ty = extract_stars ty in
         assert (nb=0);
         let s = sprintf "%a @[<hov>%a@];"
                   (print_ty ~paren:false) ty
                   (print_list comma (print_id_init ~stars:nb ~size:None))
                   lie in
         fprintf fmt "%s" s
      | Dstruct (s, lf) ->
         let s = sprintf "@\nstruct %s@ @[<hov>{@;<1 2>@[<hov>%a@]@\n};@]"
                   s
                   (print_list newline
                      (fun fmt (s,ty) -> fprintf fmt "%a %s;"
                                           (print_ty ~paren:false) ty s))
                   lf in
         fprintf fmt "%s" s
      | Dstruct_decl s ->
         fprintf fmt "struct %s;@;" s
      | Dinclude (id, Sys) ->
         fprintf fmt "#include <%s.h>"  (sanitizer id.id_string)
      | Dinclude (id, Proj) ->
         fprintf fmt "#include \"%s.h\"" (sanitizer id.id_string)
      | Dtypedef (ty,id) ->
         let s = sprintf "@[<hov>typedef@ %a@;%a;@]"
                   (print_ty ~paren:false) ty print_global_ident id in
         fprintf fmt "%s" s
    with
      Unprinted s ->
       if Debug.test_noflag debug_c_no_error_msgs
       then
         Format.eprintf
           "Could not print declaration of %s. Unsupported: %s@."
           !current_decl_name s

  and print_body fmt (def, s) =
    if def = []
    then print_stmt ~braces:true fmt s
    else
      print_pair_delim nothing newline nothing
        (print_list newline print_def)
        (print_stmt ~braces:true)
        fmt (def,s)

  let print_global_def fmt def =
    clear_local_printer ();
    print_def fmt def

  let print_file fmt info ast =
    Mid.iter (fun _ sl -> List.iter (fprintf fmt "%s\n") sl) info.thprelude;
    newline fmt ();
    fprintf fmt "@[<v>%a@]@." (print_list newline print_global_def) ast

end

module MLToC = struct

  open Ity
  open Ty
  open Expr
  open Term
  open Printer
  open Mltree
  open C

  let field i = "__field_"^(string_of_int i)

  let structs : struct_def Hid.t = Hid.create 16
  let aliases : C.ty Hid.t = Hid.create 16
  let globals : unit Hid.t = Hid.create 16

  let array = create_attribute "extraction:array"
  let array_mk = create_attribute "extraction:array_make"
  let likely = create_attribute "extraction:likely"
  let unlikely = create_attribute "extraction:unlikely"

  let decl_attribute = create_attribute "extraction:c_declaration"

  let rec ty_of_ty info ty =
    (*FIXME try to use only ML tys*)
    match ty.ty_node with
    | Tyvar v ->
      begin match query_syntax info.syntax v.tv_name
        with
        | Some s -> C.Tsyntax (s, [])
        | None -> C.Tnamed (v.tv_name)
      end
    | Tyapp (ts, [t]) when Sattr.mem array ts.ts_name.id_attrs ->
       Tarray (ty_of_ty info t, Enothing)
    | Tyapp (id, [t]) when ts_equal id Pmodule.ts_ref ->
        Tmutable (ty_of_ty info t)
    | Tyapp (ts, tl) ->
       begin match query_syntax info.syntax ts.ts_name
        with
        | Some s -> C.Tsyntax (s, List.map (ty_of_ty info) tl)
        | None ->
           if is_ts_tuple ts
           then begin
             match tl with
             | [] -> C.Tvoid
             | [t] -> ty_of_ty info t
             | _ -> Tnosyntax
             end
           else if tl = []
           then if Hid.mem aliases ts.ts_name
                then Hid.find aliases ts.ts_name
                else
                  try Tstruct (Hid.find structs ts.ts_name)
                  with Not_found -> Tnosyntax
           else Tnosyntax
       end

  let rec ty_of_mlty info = function
    | Tvar { tv_name = id } ->
      begin match query_syntax info.syntax id
        with
        | Some s -> C.Tsyntax (s, [])
        | None -> C.Tnamed id
      end
    | Tapp (id, [t]) when Sattr.mem array id.id_attrs ->
       Tarray (ty_of_mlty info t, Enothing)
    | Tapp (id, [t]) when id_equal id Pmodule.ts_ref.ts_name ->
        Tmutable (ty_of_mlty info t)
    | Tapp (id, tl) ->
       begin match query_syntax info.syntax id
        with
        | Some s -> C.Tsyntax (s, List.map (ty_of_mlty info) tl)
        | None ->
           if tl = []
           then if Hid.mem aliases id
                then Hid.find aliases id
                else try Tstruct (Hid.find structs id)
                     with Not_found -> Tnosyntax
           else Tnosyntax
       end
    | Ttuple [] -> C.Tvoid
    | Ttuple [t] -> ty_of_mlty info t
    | Ttuple _ -> raise (Unsupported "tuple parameters")

  let struct_of_rs info rs : struct_def =
    let rity = rs.rs_cty.cty_result in
    let rty = ty_of_ity rity in
    let s = match query_syntax info.syntax rs.rs_name with
      | Some s -> s
      | None -> rs.rs_name.id_string in
    let name = Pp.sprintf "__%s_result" s in
    match rty.ty_node, rs.rs_cty.cty_mask with
    | Tyapp (ts, lt), MaskVisible ->
       assert (is_ts_tuple ts);
       let rec fields fr tys = match tys with
         | [] -> []
         | ty::l -> (field fr, ty_of_ty info ty)::(fields (fr+1) l) in
       let fields = fields 0 lt in
       (name, fields)
    | Tyapp (ts, lt), MaskTuple ml ->
       assert (is_ts_tuple ts);
       assert (List.length lt = List.length ml);
       let rec fields fr tys masks =
         match tys, masks with
         | [], [] -> []
         | [], _ | _, [] -> assert false
         | _, MaskTuple _::_ ->
            raise (Unsupported "nested tuple function result")
         | _::l, MaskGhost::ml ->
            fields fr l ml
         | ty::l, MaskVisible::ml ->
            (field fr, ty_of_ty info ty)::(fields (fr+1) l ml) in
       let fields = fields 0 lt ml in
       (name, fields)
    | _ -> assert false

  let struct_of_rs info = Wrs.memoize 17 (fun rs -> struct_of_rs info rs)

  let ity_of_expr e = match e.e_ity with
    | I i -> i
    | _ -> assert false

  let pv_name pv = pv.pv_vs.vs_name

  let is_constructor rs its =
    List.exists (rs_equal rs) its.Pdecl.itd_constructors

  let is_struct_constructor info rs =
    let open Pdecl in
    if is_rs_tuple rs then false
    else match Mid.find_opt rs.rs_name info.kn with
      | Some { pd_node = PDtype its } ->
         List.exists (is_constructor rs) its
      | _ -> false

  let struct_of_constructor info rs =
    let open Pdecl in
    match Mid.find rs.rs_name info.kn with
    | { pd_node = PDtype its } ->
         let its = List.find (is_constructor rs) its in
         let id = its.itd_its.its_ts.ts_name in
         (try Hid.find structs id
         with Not_found -> raise (Unsupported "bad struct"))
    | _ -> assert false

  type syntax_env = { in_unguarded_loop : bool;
                      computes_return_value : bool;
                      current_function : rsymbol;
                      ret_regs : Sreg.t;
                      breaks : Sid.t;
                      returns : Sid.t;
                      array_sizes : C.expr Mid.t;
                      boxed : unit Hreg.t;
                      (* is this struct boxed or passed by value? *)
                    }

  let is_true e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_true
    | _ -> false

  let is_false e = match e.e_node with
    | Eapp (s, []) -> rs_equal s rs_false
    | _ -> false

  let is_unit = function
    | I i -> ity_equal i Ity.ity_unit
    | C _ -> false

  let handle_likely attrs (e:C.expr) =
    let lkl = Sattr.mem likely attrs in
    let ulk = Sattr.mem unlikely attrs in
    if lkl
    then (if ulk then e else Elikely e)
    else (if ulk then Eunlikely e else e)

  let reverse_likely = function
    | Elikely e -> Eunlikely e
    | Eunlikely e -> Elikely e
    | e -> e

  (* /!\ Do not use if e may have type unit and not be Enothing *)
  let expr_or_return env e =
    if env.computes_return_value
    then Sreturn e
    else Sexpr e

  let ity_escapes_from_expr env ity e =
    let aregs = ity_exp_fold Sreg.add_left Sreg.empty ity in
    let reset_regs = e.e_effect.eff_resets in
    let locked_regs = Sreg.union env.ret_regs reset_regs in
    not (Sreg.is_empty (Sreg.inter aregs locked_regs))

  let var_escapes_from_expr env v e =
    ity_escapes_from_expr env v.pv_ity e

  let rec expr info env (e:Mltree.expr) : C.body =
    let do_let id ity cty le e =
      if should_not_escape cty && ity_escapes_from_expr env ity e
      then raise (Unsupported "array or struct escaping function");
      let (d,s) =  expr info {env with computes_return_value = false} le in
      let initblock = d, C.assignify (Evar id) s in
      [ C.Ddecl (cty, [id, C.Enothing]) ],
      C.Sseq (C.Sblock initblock, C.Sblock (expr info env e)) in
    let do_for (eb: pvsymbol) (ee: Mltree.expr option)
          (sb: pvsymbol) (se: Mltree.expr option)  i dir body =
      let open Number in
      match i.pv_vs.vs_ty.ty_node with
      | Tyapp ({ ts_def = Range { ir_lower = lb; ir_upper = ub }},_) ->
         let init_test_ok, end_test_ok =
           match se, ee with
           | _, Some { e_node = Mltree.Econst (Constant.ConstInt ec) } ->
              true,
              if dir = To
              then BigInt.lt ec.il_int ub
              else BigInt.lt lb ec.il_int
           | Some { e_node = Mltree.Econst (Constant.ConstInt sc) }, _ ->
              (if dir = To
               then BigInt.eq sc.il_int lb
               else BigInt.eq sc.il_int ub),
              false
           | _, _ -> false, false
         in
         let ty = ty_of_ty info i.pv_vs.vs_ty in
         let di = C.Ddecl(ty, [i.pv_vs.vs_name, Enothing]) in
         let ei = C.Evar (i.pv_vs.vs_name) in
         let env_f = { env with computes_return_value = false } in
         let ds, is, ie = match se with
           | Some se ->
              let ds, is = expr info env_f se in
               begin match is with
                | Sexpr (Econst _ | Evar _ as e) ->
                   ds, Snop, e
                | _ ->
                   let iv = Evar (pv_name sb) in
                   let is = assignify iv is in
                   C.Ddecl (ty, [pv_name sb, Enothing]) :: ds, is, iv
                               end
           | None -> [], Snop, Evar(pv_name sb)
         in
         let init_e = C.Ebinop (Bassign, ei, ie) in
         let de, es, ee =
           match ee with
           | Some ee ->
              let de, es = expr info env_f ee in
              begin match es with
              | Sexpr (Econst _ | Evar _ as e) ->
                 de, Snop, e
              | _ ->
                 let ev = Evar (pv_name eb) in
                 let es = assignify ev es in
                 C.Ddecl (ty, [pv_name eb, Enothing]) :: de, es, ev
              end
           | None -> [], Snop, Evar (pv_name eb)
         in
         let d = di :: ds @ de in
         let incr_op = match dir with To -> Upreincr | DownTo -> Upredecr in
         let incr_e = C.Eunop (incr_op, ei) in
         let env' = { env with computes_return_value = false;
                               in_unguarded_loop = true;
                               breaks =
                                 if env.in_unguarded_loop
                                 then Sid.empty else env.breaks } in
         let bd, bs = expr info env' body in
         let test_op = match dir with | To -> C.Ble | DownTo -> C.Bge in
         let sloop =
           if end_test_ok
           then C.Sfor(init_e, C.Ebinop (test_op, ei, ee),
                       incr_e, C.Sblock(bd, bs))
           else
             let end_test = C.Sif (C.Ebinop (C.Beq, ei, ee),
                                   Sbreak, Snop) in
             let bs = C.Sseq (bs, end_test) in
             C.Sfor(init_e, Enothing, incr_e, C.Sblock(bd,bs)) in
         let ise = C.Sseq (is, es) in
         let s = if init_test_ok
                 then sloop
                 else C.(Sif (Ebinop (test_op, ie, ee), sloop, Snop)) in
         d, C.Sseq (ise, s)
      |  _ ->
          raise (Unsupported "for loops where loop index is not a range type")
      in
    match e.e_node with
    | Eblock [] -> ([], expr_or_return env Enothing)
    | Eblock [e] -> [], C.Sblock (expr info env e)
    | Eblock l ->
       let env_f = { env with computes_return_value = false } in
       let rec aux = function
         | [] -> ([], expr_or_return env Enothing)
         | [s] -> ([], C.Sblock (expr info env s))
         | h::t -> ([], C.Sseq (C.Sblock (expr info env_f h),
                                C.Sblock (aux t)))
       in
       aux l
    | Eapp (rs, []) when rs_equal rs rs_true ->
       Debug.dprintf debug_c_extraction "true@.";
       ([],expr_or_return env (C.Econst (Cint "1")))
    | Eapp (rs, []) when rs_equal rs rs_false ->
       Debug.dprintf debug_c_extraction "false@.";
       ([],expr_or_return env (C.Econst (Cint "0")))
    | Mltree.Evar pv ->
       let id = pv_name pv in
       let e = C.Evar id in
       ([], expr_or_return env e)
    | Mltree.Econst (Constant.ConstStr s) ->
       C.([], expr_or_return env (Econst (Cstring s)))
    | Mltree.Econst (Constant.ConstReal _) ->
       raise (Unsupported "real constant")
    | Mltree.Econst (Constant.ConstInt ic) ->
       let open Number in
       let print fmt ic =
        let n = ic.il_int in
        if BigInt.lt n BigInt.zero
        then
          (* default to base 10 for negative literals *)
          Format.fprintf fmt "-%a" (print_in_base 10 None) (BigInt.abs n)
        else
          match ic.il_kind with
          | ILitHex | ILitBin
            -> Format.fprintf fmt "0x%a" (print_in_base 16 None) n
          | ILitOct -> Format.fprintf fmt "0%a" (print_in_base 8 None) n
          | ILitDec | ILitUnk ->
             (* default to base 10 *)
             Format.fprintf fmt "%a" (print_in_base 10 None) n in
       let s =
         let i = ity_of_expr e in
         let ts = match (ty_of_ity i) with
           | { ty_node = Tyapp (ts, []) } -> ts
             | _ -> assert false in
         begin match query_syntax info.literal ts.ts_name with
         | Some st ->
            Format.asprintf "%a" (syntax_range_literal ~cb:(Some print) st) ic
         | _ ->
            let s = ts.ts_name.id_string in
            raise (Unsupported ("unspecified number format for type "^s)) end
       in
       let e = C.(Econst (Cint s)) in
       ([], expr_or_return env e)
    | Eapp (rs, []) when Hid.mem globals rs.rs_name ->
       Debug.dprintf debug_c_extraction "global variable %s@."
         rs.rs_name.id_string;
       [], expr_or_return env (Evar rs.rs_name)
    | Eapp (rs, _) when Sattr.mem decl_attribute rs.rs_name.id_attrs ->
       raise (Unsupported "local variable declaration call outside let-in")
    | Eapp (rs, [e]) when rs_equal rs Pmodule.rs_ref ->
       Debug.dprintf debug_c_extraction "ref constructor@.";
       let env_f = { env with computes_return_value = false } in
       let arg = simplify_expr (expr info env_f e) in
       ([], expr_or_return env arg)
    | Eapp (rs, el)
         when is_struct_constructor info rs
              && query_syntax info.syntax rs.rs_name = None ->
       Debug.dprintf debug_c_extraction "constructor %s@." rs.rs_name.id_string;
       let args =
         List.filter
           (fun e ->
             assert (not e.e_effect.eff_ghost);
             (not (Sattr.mem dummy_expr_attr e.e_attrs)) &&
             match e.e_ity with
             | I i when ity_equal i Ity.ity_unit -> false
             | _ -> true)
           el in
       let env_f = { env with computes_return_value = false } in
       let args = List.map (fun e -> simplify_expr (expr info env_f e)) args in
       let ((sname, sfields) as sd) = struct_of_constructor info rs in
       let id = id_register (id_fresh sname) in
       let defs = [ Ddecl (Tstruct sd, [id, Enothing]) ] in
       let st = Evar id in
       let assign_expr f arg = Sexpr (Ebinop (Bassign, Edot (st, f), arg)) in
       let inits =
         List.fold_left2
           (fun acc (f, _ty) arg -> Sseq (acc,assign_expr f arg))
           Snop sfields args in
       (defs, Sseq (inits, expr_or_return env st))
    | Eapp (rs, el) ->
       Debug.dprintf debug_c_extraction "call to %s@." rs.rs_name.id_string;
       let args = List.filter (fun e -> not (is_unit e.e_ity)) el
       in (*FIXME still needed with masks? *)
       let env_f = { env with computes_return_value = false } in
       if is_rs_tuple rs
       then begin
         match args with
         | [] -> C.([], expr_or_return env Enothing);
         | [e] -> expr info env e
         | _ ->
            let id_struct = id_register (id_fresh "result") in
            let e_struct = C.Evar id_struct in
            let d_struct =
              C.(Ddecl(Tstruct
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
            C.([d_struct], Sseq(assigns args 0, expr_or_return env e_struct))
         end
       else
         let (prdefs, prstmt), e' =
           let prelude, unboxed_params =
             Lists.map_fold_left
               (fun ((accd, accs) as acc) e ->
                 let pty = ty_of_ty info (ty_of_ity (ity_of_expr e)) in
                 let d, s = expr info env_f e in
                 try
                   acc,
                   (simplify_expr (d,s), pty)
                 with Invalid_argument _ ->
                   let s', e' = get_last_expr s in
                   (accd@d, Sseq(accs, s')), (e', pty))
               ([], Snop)
               args in
           let params =
             List.map2
               (fun p mle ->
                 match (p, mle) with
                 | (ce, Tstruct s), { e_ity = I { ity_node = Ityreg r }}
                      when not (Hreg.mem env.boxed r) ->
                    C.(Eunop(Uaddr, ce), Tptr (Tstruct s))
                 | (ce, Tmutable t), { e_ity = I { ity_node = Ityreg r }}
                       when not (Hreg.mem env.boxed r) ->
                     (Eunop(Uaddr, ce), Tptr t)
                 | p, _ -> p)
               unboxed_params args in
           prelude,
           match query_syntax info.syntax rs.rs_name with
           | Some s ->
              let complex s =
                String.contains s '%'
                || String.contains s ' '
                || String.contains s '(' in
              let p = Mid.find rs.rs_name info.prec in
              if complex s
              then
                let rty = ty_of_ity (ity_of_expr e) in
                let rtyargs = match rty.ty_node with
                  | Tyvar _ -> [||]
                  | Tyapp (_,args) ->
                     Array.of_list
                       (List.map (ty_of_ty info)
                          args)
                in
                C.Esyntax(s,ty_of_ty info rty, rtyargs, params, p)
              else
                if args=[]
                then C.(Esyntax(s, Tnosyntax, [||], [], p)) (*constant*)
                else
                  (*function defined in the prelude *)
                  let cargs = List.map fst params in
                  C.(Esyntaxrename (s, cargs))
           | None ->
              match rs.rs_field with
              | None ->
                 C.(Ecall(Evar(rs.rs_name), List.map fst params))
              | Some pv ->
                 assert (List.length el = 1);
                 begin match unboxed_params, args with
                 | [(ce, Tstruct _)], [{ e_ity = I { ity_node = Ityreg r }}] ->
                    if Hreg.mem env.boxed r
                    then C.Earrow (ce, (pv_name pv).id_string)
                    else C.Edot (ce, (pv_name pv).id_string)
                 | [(ce, Tmutable _)], [{ e_ity = I { ity_node = Ityreg r }}] ->
                     if Hreg.mem env.boxed r then C.Eunop (C.Ustar, ce) else ce
                 | _ -> C.Edot (fst (List.hd params), (pv_name pv).id_string)
                 end
         in
         let s =
           if env.computes_return_value
           then
             begin match e.e_ity with
             | I ity when ity_equal ity Ity.ity_unit ->
                Sseq(Sexpr e', Sreturn Enothing)
             | I _ -> Sreturn e'
             | _ -> assert false
             end
           else Sexpr e' in
         if is_nop prstmt
         then prdefs, s
         else C.(prdefs, Sseq(prstmt, s))
    | Eif (cond, th, el) ->
       let cd,cs = expr info {env with computes_return_value = false} cond in
       let t = expr info env th in
       let e = expr info env el in
       begin match simplify_cond (cd, cs) with
       | [], C.Sexpr c ->
          let c = handle_likely cond.e_attrs c in
          if is_false th && is_true el
          then C.([], expr_or_return env (Eunop(Unot, c)))
          else [], C.Sif(c,C.Sblock t, C.Sblock e)
       | cdef, cs ->
          let cid = id_register (id_fresh "cond") in (* ? *)
          C.Ddecl (C.Tsyntax ("int",[]), [cid, C.Enothing])::cdef,
          C.Sseq (C.assignify (Evar cid) cs,
                  C.Sif ((handle_likely cond.e_attrs (C.Evar cid)),
                         C.Sblock t, C.Sblock e))
       end
    | Ewhile (c,b) ->
       Debug.dprintf debug_c_extraction "while@.";
      let cd, cs = expr info {env with computes_return_value = false} c in
      (* this is needed so that the extracted expression has all
         needed variables in its scope *)
      let cd, cs = C.flatten_defs cd cs in
      let cd = C.group_defs_by_type cd in
      let env' = { env with
                   computes_return_value = false;
                   in_unguarded_loop = true;
                   breaks =
                     if env.in_unguarded_loop
                     then Sid.empty else env.breaks } in
      let b = expr info env' b in
      begin match (C.simplify_cond (cd,cs)) with
      | cd, C.Sexpr ce -> cd, C.Swhile (handle_likely c.e_attrs ce, C.Sblock b)
      | _ ->
        begin match C.get_last_expr cs with
        | C.Snop, e -> cd, C.(Swhile(handle_likely c.e_attrs e, C.Sblock b))
        | s,e ->
           let brc = reverse_likely (handle_likely c.e_attrs (Eunop(Unot,e))) in
           cd, C.(Swhile(Econst (Cint "1"),
                         Sseq(s,
                              Sseq(Sif(brc, Sbreak, Snop),
                                   C.Sblock b))))
        end
      end
    | Ematch (b, [], (_::_ as xl)) ->
      Debug.dprintf debug_c_extraction "TRY@.";
      let is_while = match b.e_node with Ewhile _ -> true | _-> false in
      let breaks, returns = List.fold_left
        (fun (bs,rs) (xs, pvsl, r) ->
          let id = xs.xs_name in
          match pvsl, r.e_node with
          | [], (Eblock []) when is_while ->
             assert (is_unit r.e_ity);
             (Sid.add id bs, rs)
          | [pv], Mltree.Evar pv'
             when pv_equal pv pv' && env.computes_return_value ->
             (bs, Sid.add id rs)
          | [], Mltree.Eblock [] when env.computes_return_value ->
             assert (is_unit r.e_ity);
             (bs, Sid.add id rs)
          | _ -> raise (Unsupported "non break/return exception in try"))
        (Sid.empty, env.returns) xl
      in
      let env' = { env with
                   in_unguarded_loop = false;
                   breaks = breaks;
                   returns = returns;
                   boxed = env.boxed;
                 } in
      expr info env' b
    | Eraise (xs,_) when Sid.mem xs.xs_name env.breaks ->
      Debug.dprintf debug_c_extraction "BREAK@.";
      ([], C.Sbreak)
    | Eraise (xs, Some r) when Sid.mem xs.xs_name env.returns ->
      Debug.dprintf debug_c_extraction "RETURN@.";
      expr info {env with computes_return_value = true} r
    | Eraise (xs, None)
         when Sid.mem xs.xs_name env.returns &&
                ity_equal Ity.ity_unit env.current_function.rs_cty.cty_result
      -> ([], C.Sreturn Enothing)
    | Eraise (xs, None) when Sid.mem xs.xs_name env.returns ->
       assert false (* nothing to pass to return *)
    | Eraise _ -> raise (Unsupported "non break/return exception raised")
    | Elet (Lvar(eb, ee),
            { e_node = Elet(Lvar (sb, se),
                 { e_node = Efor (i, sb', dir, eb', body) })})
         when pv_equal sb sb' && pv_equal eb eb' ->
       Debug.dprintf debug_c_extraction "LETLETFOR@.";
       do_for eb (Some ee) sb (Some se) i dir body
    | Elet (Lvar (eb, ee), { e_node = Efor (i, sb, dir, eb', body) })
         when pv_equal eb eb' ->
       Debug.dprintf debug_c_extraction "ENDLETFOR@.";
       do_for eb (Some ee) sb None i dir body
    | Elet (Lvar (sb, se), { e_node = Efor (i, sb', dir, eb, body) })
         when pv_equal sb sb' ->
       Debug.dprintf debug_c_extraction "STARTLETFOR@.";
       do_for eb None sb (Some se) i dir body
    | Efor (i, sb, dir, eb, body) ->
       Debug.dprintf debug_c_extraction "FOR@.";
       do_for eb None sb None i dir body
    | Ematch (({e_node = Eapp(_rs,_)} as e1), [Pwild, e2], []) ->
       let ne = { e with e_node = Eblock [e1; e2] } in
       expr info env ne
    | Ematch (e1, [Pvar v, e2], []) ->
       let ity = ity_of_expr e1 in
       let cty = ty_of_ty info (ty_of_ity ity) in
       do_let v.vs_name ity cty e1 e2
    | Ematch (({e_node = Eapp(rs,_)} as e1), [Ptuple rets,e2], [])
         when List.for_all
                (function | Pwild (*ghost*) | Pvar _ -> true |_-> false)
                rets
      ->
       begin match rets with
       | _ ->
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
        d@defs, C.(Sseq(Sseq(s,assigns), Sblock b)) end
    | Ematch _ -> raise (Unsupported "pattern matching")
    | Eabsurd -> assert false
    | Eassign ([pv, ({rs_field = Some _} as rs), e2]) ->
       let id = pv_name pv in
       let boxed =
         match pv.pv_ity.ity_node with
         | Ityreg r ->  Hreg.mem env.boxed r
         | _ -> false in
       let t =
         match query_syntax info.syntax rs.rs_name with
         | Some s ->
            let _ =
              try
                Re.Str.search_forward
                  (Re.Str.regexp "[%]\\([tv]?\\)[0-9]+") s 0
              with Not_found -> raise (Unsupported "assign field format")  in
            let st = if boxed
                     then C.(Eunop(Ustar, Evar id))
                     else C.Evar id in
            let params = [ st, ty_of_ty info (ty_of_ity pv.pv_ity) ] in
            let rty = ty_of_ity rs.rs_cty.cty_result in
            let rtyargs = match rty.ty_node with
              | Tyvar _ -> [||]
              | Tyapp (_,args) ->
                 Array.of_list (List.map (ty_of_ty info) args)
            in
            let p = Mid.find rs.rs_name info.prec in
            C.Esyntax(s,ty_of_ty info rty, rtyargs, params,p)
         | None ->
             let ty = ty_of_ty info (ty_of_ity pv.pv_ity) in
             match ty with
             | Tmutable _ ->
                 if boxed then Eunop (Ustar, Evar id) else Evar id
             | _ ->
                 if boxed
                 then Earrow (Evar id, rs.rs_name.id_string)
                 else Edot (Evar id, rs.rs_name.id_string) in
       let d,v = expr info { env with computes_return_value = false } e2 in
       d, C.(Sexpr(Ebinop(Bassign, t, simplify_expr ([],v))))
    | Eassign _ -> raise (Unsupported "assign")
    | Eexn (_,_,e) -> expr info env e
    | Eignore e ->
       [],
       C.Sseq(C.Sblock(expr info {env with computes_return_value = false} e),
              if env.computes_return_value
              then C.Sreturn(Enothing)
              else C.Snop)
    | Efun _ -> raise (Unsupported "higher order")
    | Elet (Lvar (v, { e_node = Eapp (rs, al) }), e)
         when Sattr.mem decl_attribute rs.rs_name.id_attrs
              && query_syntax info.syntax rs.rs_name <> None
              && List.for_all (fun e -> is_unit e.e_ity) al
      ->
       Debug.dprintf debug_c_extraction "variable declaration call@.";
       if var_escapes_from_expr env v e
       then raise (Unsupported "local variable escaping function");
       let t = ty_of_ty info (ty_of_ity v.pv_ity) in
       let scall = Opt.get (query_syntax info.syntax rs.rs_name) in
       let p = Mid.find rs.rs_name info.prec in
       let ecall = C.(Esyntax(scall, Tnosyntax, [||], [], p)) in
       let d = C.Ddecl (t, [pv_name v, ecall]) in
       let d', s = expr info env e in
       d::d', s
    | Elet (Lvar (a, { e_node = Eapp (rs, [n; v]) }), e)
         when Sattr.mem array_mk rs.rs_name.id_attrs ->
       (* let a = Array.make n v in e*)
       Debug.dprintf debug_c_extraction "call to an array constructor@.";
       if var_escapes_from_expr env a e
       then raise (Unsupported "array escaping function");
       let env_f = { env with computes_return_value = false } in
       let n = expr info env_f n in
       let n = get_const_expr n in
       let avar = pv_name a in
       let sizes = Mid.add avar n env.array_sizes in
       let v_ty = ty_of_ty info (ty_of_ity (ity_of_expr v)) in
       let loop_i = id_register (id_fresh "i") in
       let d = C.([Ddecl (Tarray (v_ty, n), [avar, Enothing]);
                   Ddecl (Tsyntax ("int", []), [loop_i, Enothing])]) in
       let i = C.Evar loop_i in
       let dv, sv = expr info env_f v in
       let eai = C.Eindex(Evar avar, i) in
       let assign_e = assignify eai sv in
       let init_loop = C.(Sfor(Ebinop(Bassign, i, Econst (Cint "0")),
                               Ebinop(Blt, i, n),
                               Eunop(Upreincr, i),
                               assign_e)) in
       let env = { env with array_sizes = sizes } in
       let d', s' = expr info env e in
       d@dv@d', Sseq (init_loop, s')
    | Elet (ld,e) ->
       begin match ld with
       | Lvar (pv,le) -> (* not a block *)
          let ity = pv.pv_ity in
          let cty = ty_of_ty info (ty_of_ity ity) in
          do_let pv.pv_vs.vs_name ity cty le e
       | Lsym _ -> raise (Unsupported "LDsym")
       | Lrec _ -> raise (Unsupported "LDrec") (* TODO for rec at least*)
       | Lany _ -> raise (Unsupported "Lany")
       end

  let translate_decl (info:info) (d:decl) ~header : C.definition list =
    current_decl_name := "";
    let translate_fun rs mlty vl e =
      current_decl_name := rs.rs_name.id_string;
      Debug.dprintf debug_c_extraction "print %s@." rs.rs_name.id_string;
      if rs_ghost rs
      then begin Debug.dprintf debug_c_extraction "is ghost@."; [] end
      else
        let is_dummy id = Sattr.mem Dexpr.dummy_var_attr id.id_attrs in
        let boxed = Hreg.create 16 in
        let keep_var (id, mlty, gh) =
          not gh &&
            match mlty with
            | Ttuple [] ->
               if is_dummy id
               then false
               else raise (Unsupported "non-dummy unit parameter")
            | _ -> true in
        let keep_pv pv =
          not pv.pv_ghost &&
            not (ity_equal pv.pv_ity Ity.ity_unit
                 && is_dummy pv.pv_vs.vs_name) in
        let ngvl = List.filter keep_var vl in
        let ngargs = List.filter keep_pv rs.rs_cty.cty_args in
        let params =
          List.map2 (fun (id, mlty, _gh) pv ->
              let cty = ty_of_mlty info mlty in
              match has_unboxed_struct cty, pv.pv_ity.ity_node with
              | true, Ityreg r ->
                 Debug.dprintf debug_c_extraction "boxing parameter %s@."
                   id.id_string;
                 Hreg.add boxed r ();
                 C.Tptr cty, id
              | _ -> (cty, id)) ngvl ngargs in
        let rity = rs.rs_cty.cty_result in
        let ret_regs = ity_exp_fold Sreg.add_left Sreg.empty rity in
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
        let rtype = try ty_of_mlty info mlty
                    with Unsupported _ -> (*FIXME*)
                      ty_of_ty info (ty_of_ity rity) in
        let rtype,sdecls =
          if rtype=C.Tnosyntax && is_simple_tuple rity
          then
            let st = struct_of_rs info rs in
            C.Tstruct st, [C.Dstruct st]
          else rtype, [] in
        if has_array rtype then raise (Unsupported "array return");
        if header
        then sdecls@[C.Dproto (rs.rs_name, (rtype, params))]
        else
          let env = { computes_return_value = true;
                      in_unguarded_loop = false;
                      current_function = rs;
                      ret_regs = ret_regs;
                      returns = Sid.empty;
                      breaks = Sid.empty;
                      array_sizes = Mid.empty;
                      boxed = boxed;
                    } in
          let d,s = expr info env e in
          let d,s = C.flatten_defs d s in
          let d = C.group_defs_by_type d in
          let s = C.elim_nop s in
          let s = C.elim_empty_blocks s in
          match s with
          | Sreturn r when params = [] ->
             Format.printf "declaring global %s@." rs.rs_name.id_string;
             Hid.add globals rs.rs_name ();
             sdecls@[C.Ddecl (rtype, [rs.rs_name, r])]
          | _ -> sdecls@[C.Dfun (rs.rs_name, (rtype,params), (d,s))] in
    try
      begin match d with
      | Dlet (Lsym(rs, _, mlty, vl, e)) ->
         if Sattr.mem Compile.InlineFunctionCalls.inline_attr
              rs.rs_name.id_attrs (* call is inlined, do not extract *)
         then []
         else translate_fun rs mlty vl e
      | Dtype [{its_name=id; its_def=idef}] ->
         current_decl_name := id.id_string;
         Debug.dprintf debug_c_extraction "PDtype %s@." id.id_string;
         begin match query_syntax info.syntax id with
         | Some _ -> []
         | None -> begin
             match idef with
             | Some (Dalias mlty) ->
                let ty = ty_of_mlty info mlty in
                Hid.replace aliases id ty;
                []
             (*TODO print actual typedef? *)
             (*[C.Dtypedef (ty_of_mlty info ty, id)]*)
             | Some (Drecord pjl) ->
                let pjl =
                  List.filter
                    (fun (_,_,ty) ->
                      match ty with
                      | Ttuple [] -> false
                      | _ -> true)
                    pjl in
                let fields =
                  List.map
                    (fun (_, id, ty) -> (id.id_string, ty_of_mlty info ty))
                    pjl in
                (*if List.exists
                     (fun (_,t) -> match t with Tarray _ -> true | _ -> false)
                     fields
                then raise (Unsupported "array in struct");*)
                let sd = id.id_string, fields in
                Hid.replace structs id sd;
                [C.Dstruct sd]
             | Some Ddata _ -> raise (Unsupported "Ddata@.")
             | Some (Drange _) | Some (Dfloat _) ->
                raise (Unsupported "Drange/Dfloat@.")
             | None -> raise (Unsupported
                                ("type declaration without syntax or alias: "
                                 ^id.id_string))
           end
         end
      | Dlet (Lrec rl) ->
         let translate_rdef rd =
           translate_fun rd.rec_sym rd.rec_res rd.rec_args rd.rec_exp in
         let defs = List.flatten (List.map translate_rdef rl) in
         if header then defs
         else
           let proto_of_fun = function
             | C.Dfun (id, pr, _) -> [C.Dproto (id, pr)]
             | _ -> [] in
           let protos = List.flatten (List.map proto_of_fun defs) in
           protos@defs
      | _ -> [] (*TODO exn ? *) end
    with
      Unsupported s ->
       if Debug.test_noflag debug_c_no_error_msgs
       then
         Format.eprintf
           "Could not translate declaration of %s. Unsupported : %s@."
           !current_decl_name s;
       []

  let translate_decl (info:info) (d:Mltree.decl) ~header : C.definition list =
    let decide_print id =
      (not (header && (Sattr.mem Print.c_static_inline id.id_attrs)))
      && query_syntax info.syntax id = None in
    let names = Mltree.get_decl_name d in
    match List.filter decide_print names with
    | [] -> []
    | _ -> translate_decl info d ~header

end

module Transform = struct

open C

let rec expr e =
  let e = e_map expr e in
  match e with
  | Equestion (c, Econst (Cint "1"), Econst (Cint "0")) -> c
  | _ -> e

and stmt s =
  let s = s_map def stmt expr s in
  s

and def (d:definition) = match d with
  | C.Dfun (id,p,(dl, s)) ->  Dfun (id, p, (List.map def dl, stmt s))
  | C.Ddecl (ty, dl) -> C.Ddecl (ty, List.map (fun (id, e) -> id, expr e) dl)
  | C.Dproto (_,_) | C.Dstruct _
  | C.Dstruct_decl _ | C.Dtypedef (_,_)
  | C.Dinclude (_,_) -> d

let defs dl = List.map def dl

end


let name_gen suffix ?fname m =
  let n = m.Pmodule.mod_theory.Theory.th_name.Ident.id_string in
  let n = Print.sanitizer n in
  let r = match fname with
    | None -> n ^ suffix
    | Some f -> f ^ "__" ^ n ^ suffix in
  Strings.lowercase r

let header_border_printer header _args ?old:_ ?fname ~flat:_ fmt m =
  let n = Strings.uppercase (name_gen "_H_INCLUDED" ?fname m) in
  if header then
    Format.fprintf fmt "#ifndef %s@\n@." n
  else
    Format.fprintf fmt "#define %s@\n#endif // %s@." n n

let print_header_decl args fmt d =
  let cds = MLToC.translate_decl args d ~header:true in
  List.iter (Format.fprintf fmt "%a@." Print.print_global_def) cds

let mk_info (args:Pdriver.printer_args) m = {
    env = args.Pdriver.env;
    prelude = args.Pdriver.prelude;
    thprelude = args.Pdriver.thprelude;
    thinterface = args.Pdriver.thinterface;
    blacklist = args.Pdriver.blacklist;
    syntax = args.Pdriver.syntax;
    literal = args.Pdriver.literal;
    prec = args.Pdriver.prec;
    kn = m.Pmodule.mod_known }

let print_header_decl =
  let memo = Hashtbl.create 16 in
  fun args ?old ?fname ~flat m fmt d ->
  ignore old;
  ignore fname;
  ignore flat;
  if not (Hashtbl.mem memo d)
  then begin
    Hashtbl.add memo d ();
    let info = mk_info args m in
    print_header_decl info fmt d end

let print_prelude args ?old ?fname ~flat deps fmt pm =
  ignore old;
  ignore fname;
  ignore flat;
  ignore pm;
  ignore args;
  let add_include id =
    Format.fprintf fmt "%a@." Print.print_global_def C.(Dinclude (id,Proj)) in
  List.iter
    (fun m ->
      let id = m.Pmodule.mod_theory.Theory.th_name in
      add_include id)
    (List.rev deps)

let print_decl args fmt d =
  let cds = MLToC.translate_decl args d ~header:false in
  let cds = Transform.defs cds in
  let print_def d =
    Format.fprintf fmt "%a@." Print.print_global_def d in
  List.iter print_def cds

let print_decl =
  let memo = Hashtbl.create 16 in
  fun args ?old ?fname ~flat m fmt d ->
  ignore old;
  ignore fname;
  ignore flat;
  ignore m;
  if not (Hashtbl.mem memo d)
  then begin
      Hashtbl.add memo d ();
      let info = mk_info args m in
    print_decl info fmt d end

let c_printer = Pdriver.{
    desc = "printer for C code";
    implem_printer = {
        filename_generator = name_gen ".c";
        decl_printer = print_decl;
        prelude_printer = print_prelude;
        header_printer = dummy_border_printer;
        footer_printer = dummy_border_printer;
      };
    interf_printer = Some {
        filename_generator = name_gen ".h";
        decl_printer = print_header_decl;
        prelude_printer = print_prelude;
        header_printer = header_border_printer true;
        footer_printer = header_border_printer false;
      };
  }

let () =
  Pdriver.register_printer "c" c_printer

(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
