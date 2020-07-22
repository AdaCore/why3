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

open Format
open Wstdlib
open Term
open Ident
open Ty
open Ity
open Expr
open Big_real
open Mlmpfr_wrapper

let pp_indent fmt =
  match Printexc.(backtrace_slots (get_callstack 100)) with
  | None -> ()
  | Some a ->
      let s = String.make (2 * (Array.length a - 10)) ' ' in
      pp_print_string fmt s

let debug =
  Debug.register_info_flag "trace_exec"
    ~desc:"trace execution of code given by --exec or --eval"

let debug_rac = Debug.register_info_flag "rac" ~desc:"trace evaluation for RAC"

let pp_bindings ?(sep = Pp.semi) ?(pair_sep = Pp.arrow) ?(delims = Pp.(lbrace, rbrace))
    pp_key pp_value fmt l =
  let pp_binding fmt (k, v) =
    fprintf fmt "@[<h>%a%a%a@]" pp_key k pair_sep () pp_value v in
  fprintf fmt "%a%a%a" (fst delims) ()
    (Pp.print_list sep pp_binding)
    l (snd delims) ()

let pp_typed pp ty fmt x =
  fprintf fmt "(%a: %a)" pp x Pretty.print_ty (ty x)
[@@warning "-32"]

(* EXCEPTIONS *)

exception NoMatch
exception Undetermined
exception CannotCompute
exception NotNum
exception CannotFind of (Env.pathname * string * string)

(* VALUES *)

type float_mode = mpfr_rnd_t

type big_float = mpfr_float

let mode_to_string m =
  match m with
  | To_Nearest -> "RNE"
  | Away_From_Zero -> "RNA"
  | Toward_Plus_Infinity -> "RTP"
  | Toward_Minus_Infinity -> "RTN"
  | Toward_Zero -> "RTZ"
  | Faithful -> assert false

module rec Value : sig
  type value = {v_desc: value_desc; v_ty: ty}
  and value_desc =
    | Vconstr of rsymbol * field list
    | Vnum of BigInt.t
    | Vreal of real
    | Vfloat_mode of float_mode
    | Vfloat of big_float
    | Vstring of string
    | Vbool of bool
    | Vvoid
    | Varray of value array
    | Vfun of value Mvs.t (* closure *) * vsymbol * expr
    | Vpurefun of ty (* keys *) * value Mv.t * value
    | Vterm of term (* ghost values *)
  and field = Field of value ref
  val compare_values : value -> value -> int
end = struct
  type value = {v_desc: value_desc; v_ty: ty}
  and value_desc =
    | Vconstr of rsymbol * field list
    | Vnum of BigInt.t
    | Vreal of real
    | Vfloat_mode of float_mode
    | Vfloat of big_float
    | Vstring of string
    | Vbool of bool
    | Vvoid
    | Varray of value array
    | Vfun of value Mvs.t (* closure *) * vsymbol * expr
    | Vpurefun of ty (* keys *) * value Mv.t * value
    | Vterm of term
  and field = Field of value ref
  let (<?>) c (cmp,x,y) = if c = 0 then cmp x y else c
  let rec compare_lists c l1 l2 : int = match l1, l2 with
    | h1::t1, h2::t2 -> c h1 h2 <?> (compare_lists c, t1, t2)
    | _ -> List.compare_lengths l1 l2
  let rec compare_values v1 v2 : int =
    ty_compare v1.v_ty v2.v_ty <?> (compare_desc, v1.v_desc, v2.v_desc)
  and compare_desc d1 d2 =
    match d1, d2 with
    | Vconstr (rs1, fs1), Vconstr (rs2, fs2) ->
        rs_compare rs1 rs2 <?> (compare_lists compare_fields, fs1, fs2)
    | Vconstr _, _ -> -1 | _, Vconstr _ -> 1
    | Vnum i1, Vnum i2 ->
        BigInt.compare i1 i2
    | Vnum _, _ -> -1 | _, Vnum _ -> 1
    | Vreal r1, Vreal r2 ->
        Big_real.(if eq r1 r2 then 0 else if lt r1 r2 then -1 else 1)
    | Vreal _, _ -> -1 | _, Vreal _ -> 1
    | Vfloat_mode m1, Vfloat_mode m2 ->
        compare m1 m2
    | Vfloat_mode _, _ -> -1 | _, Vfloat_mode _ -> 1
    | Vfloat f1, Vfloat f2 ->
        Mlmpfr_wrapper.(if equal_p f1 f2 then 0 else if less_p f1 f2 then -1 else 1)
    | Vfloat _, _ -> -1 | _, Vfloat _ -> 1
    | Vstring s1, Vstring s2 ->
        String.compare s1 s2
    | Vstring _, _ -> -1 | _, Vstring _ -> 1
    | Vbool b1, Vbool b2 ->
        compare b1 b2
    | Vbool _, _ -> -1 | _, Vbool _ -> 1
    | Vvoid, Vvoid ->
        0
    | Vvoid, _ -> -1 | _, Vvoid -> 1
    | Vfun _, Vfun _ ->
        failwith "Value.compare: Vfun"
    | Vfun _, _ -> -1 | _, Vfun _ -> 1
    | Vpurefun (ty1, mv1, v1), Vpurefun (ty2, mv2, v2) ->
        ty_compare ty1 ty2 <?> (compare, v1, v2)
        <?> (Mv.compare compare, mv1, mv2)
    | Vpurefun _, _ -> -1 | _, Vpurefun _ -> 1
    | Vterm t1, Vterm t2 ->
        t_compare t1 t2
    | Vterm _, _ -> -1 | _, Vterm _ -> 1
    | Varray a1, Varray a2 ->
        let rec loop n a1 a2 =
          if n = 0 then 0
          else compare a1.(n-1) a2.(n-1) <?> (loop (pred n), a1, a2) in
        Array.length a2 - Array.length a1 <?> (loop (Array.length a1), a1, a2)
  and compare_fields (Field r1) (Field r2) =
    compare !r1 !r2
end
and Mv : Map.S with type key = Value.value =
  Map.Make (struct
    type t = Value.value
    let compare = Value.compare_values
  end)

include Value

let value ty desc = {v_desc= desc; v_ty= ty}
let field v = Field (ref v)
let constr rs vl = Vconstr (rs, List.map field vl)
let v_desc v = v.v_desc
let v_ty v = v.v_ty
let field_get (Field r) = r.contents

let rec snapshot v = match v.v_desc with
  | Vconstr (rs, fs) ->
      let fs = List.map snapshot_field fs in
      {v with v_desc= Vconstr (rs, fs)}
  | Vfun (cl, vs, e) ->
      let cl = Mvs.map snapshot cl in
      {v with v_desc= Vfun (cl, vs, e)}
  | Vpurefun (ty, mv, v) ->
      let mv = Mv.fold (fun k v -> Mv.add (snapshot k) (snapshot v)) mv Mv.empty in
      {v with v_desc= Vpurefun (ty, mv, snapshot v)}
  | Varray a ->
      let a = Array.map snapshot a in
      {v with v_desc= Varray a}
  | Vfloat _ | Vstring _ | Vterm _ | Vbool _
  | Vreal _ | Vfloat_mode _ | Vvoid | Vnum _ ->
      v

and snapshot_field f =
  field (snapshot (field_get f))

let rec print_value fmt v =
  match v.v_desc with
  | Vnum n ->
      if BigInt.ge n BigInt.zero then
        fprintf fmt "%s" (BigInt.to_string n)
      else
        fprintf fmt "(%s)" (BigInt.to_string n)
  | Vbool b -> fprintf fmt "%b" b
  | Vreal r -> print_real fmt r
  | Vfloat f ->
      (* Getting "@" is intentional in mlmpfr library for bases higher than 10.
         So, we keep this notation. *)
      let hexadecimal = get_formatted_str ~base:16 f in
      let decimal = get_formatted_str ~base:10 f in
      fprintf fmt "%s (%s)" decimal hexadecimal
  | Vfloat_mode m -> fprintf fmt "%s" (mode_to_string m)
  | Vstring s -> Constant.print_string_def fmt s
  | Vvoid -> fprintf fmt "()"
  | Vfun (mvs, vs, e) ->
      fprintf fmt "@[<v2>(%tfun %a -> %a)@]"
        (fun fmt ->
           if not (Mvs.is_empty mvs) then
             fprintf fmt "%a " (pp_bindings Pretty.print_vs print_value) (Mvs.bindings mvs))
        Pretty.print_vs vs
        print_expr e
  | Vconstr (rs, vl) when is_rs_tuple rs ->
      fprintf fmt "@[(%a)@]" (Pp.print_list Pp.comma print_field) vl
  | Vconstr (rs, []) -> fprintf fmt "@[%a@]" print_rs rs
  | Vconstr (rs, vl) ->
      fprintf fmt "@[(%a %a)@]" print_rs rs
        (Pp.print_list Pp.space print_field)
        vl
  | Varray a ->
      fprintf fmt "@[[%a]@]"
        (Pp.print_list Pp.comma print_value)
        (Array.to_list a)
  | Vpurefun (_, mv, v) ->
      fprintf fmt "@[[|%a; _ -> %a|]@]" (pp_bindings ~delims:Pp.(nothing,nothing) print_value print_value)
        (Mv.bindings mv) print_value v
  | Vterm t ->
      fprintf fmt "(term:@ %a)" Pretty.print_term t

and print_field fmt f = print_value fmt (field_get f)

let term_of_value env v =
  let rec term_of_value' mt v : ty Mtv.t * term =
    match v.v_desc with
    | Vnum i -> mt, t_const (Constant.int_const i) v.v_ty
    | Vstring s -> mt, t_const (Constant.ConstStr s) ty_str
    | Vbool b -> mt, if b then t_bool_true else t_bool_false
    | Vvoid -> mt, t_tuple []
    | Vterm t -> mt, t
    | Vreal _ | Vfloat _ | Vfloat_mode _ -> (* TODO *)
        Format.kasprintf failwith "term_of_value: %a" print_value v
    | Vconstr (rs, fs) ->
        let mt, fs = Lists.map_fold_left term_of_field mt fs in
        if rs_kind rs = RKfunc then
          mt, t_app_infer (ls_of_rs rs) fs
        else (* TODO Not sure if needed *)
          kasprintf failwith "Cannot construct term for constructor \
                              %a that is not a function" print_rs rs
    | Vfun (cl, arg, e) ->
        (* TERM: fun arg -> t *)
        let t = Opt.get (term_of_expr ~prop:false e) in
        let bind_cl vs v (mt, mv) =
          let mt = ty_match mt vs.vs_ty v.v_ty in
          let mt, t = term_of_value' mt v in
          mt, Mvs.add vs t mv in
        let t = (* Substitute values from the closure *)
          let mt, mv = Mvs.fold bind_cl cl (mt, Mvs.empty) in
          t_ty_subst mt mv t in
        mt, t_lambda [arg] [] t
    | Varray a ->
        (* TERM: epsilon v. v[0] = a[0] /\ ... /\ v[n-1] = a[n-1] *)
        let pm = Pmodule.read_module env ["array"] "Array" in
        let vs = create_vsymbol (id_fresh "a") v.v_ty in
        let ls_get = Mstr.find (Ident.op_get "") pm.Pmodule.mod_theory.Theory.th_export.Theory.ns_ls in
        let rec loop mt i =
          if i = Array.length a then
            mt, t_true
          else
            let t_i = t_const (Constant.int_const_of_int i) ty_int in
            let t1 = t_app_infer ls_get [t_var vs; t_i] in (* v[i] *)
            let mt, t2 = term_of_value' mt a.(i) in        (* a[i] *)
            let mt, t3 = loop mt (succ i) in
            mt, t_and (t_equ t1 t2) t3 in    (* v[i] = a[i] /\ ... *)
        let mt, t = loop mt 0 in
        mt, t_eps (t_close_bound vs t)
    | Vpurefun (ty, mv, v) ->
        (* TERM: fun arg -> if arg = k0 then v0 else ... else v *)
        (* TODO Use function literal [|mv...; _ -> v|] when available in Why3 *)
        let arg = create_vsymbol (id_fresh "arg") ty in
        let mk_case key value (mt, t) =
          let mt, key = term_of_value' mt key in      (* k_i *)
          let mt, value = term_of_value' mt value in  (* v_i *)
          mt, t_if (t_equ (t_var arg) key) value t in (* if arg = k_i then v_i else ... *)
        let mt, t = Mv.fold mk_case mv (term_of_value' mt v) in
        mt, t_lambda [arg] [] t
  and term_of_field mt f = term_of_value' mt (field_get f) in
  snd (term_of_value' Mtv.empty v)

(* RESULT *)

type result =
  | Normal of value
  | Excep of xsymbol * value
  | Irred of expr
  | Fun of rsymbol * pvsymbol list * int

let print_logic_result fmt r =
  match r with
  | Normal v -> fprintf fmt "@[%a@]" print_value v
  | Excep (x, v) ->
      fprintf fmt "@[exception %s(@[%a@])@]" x.xs_name.id_string print_value v
  | Irred e -> fprintf fmt "@[Cannot execute expression@ @[%a@]@]" print_expr e
  | Fun _ -> fprintf fmt "@[Result is a function@]"

(* ENV *)

type env =
  { mod_known : Pdecl.known_map;
    th_known  : Decl.known_map;
    funenv    : Expr.cexp Mrs.t;
    vsenv     : value Mvs.t;
    ce_model  : Model_parser.model;
    env       : Env.env
  }

let default_env env =
  { mod_known = Mid.empty; th_known = Mid.empty; funenv = Mrs.empty;
    vsenv = Mvs.empty; ce_model = Model_parser.default_model; env }

let add_local_funs locals env =
  let add acc (rs, ce) = Mrs.add rs ce acc in
  let funenv = List.fold_left add env.funenv locals in
  {env with funenv}

let bind_vs vs v env = {env with vsenv= Mvs.add vs v env.vsenv}
let bind_pvs pv v_t env = bind_vs pv.pv_vs v_t env
let multibind_pvs l tl env = List.fold_right2 bind_pvs l tl env

(* BUILTINS *)

let big_int_of_const i = i.Number.il_int
let big_int_of_value v = match v.v_desc with Vnum i -> i | _ -> raise NotNum
let eval_true _ls _l = value ty_bool (Vbool true)
let eval_false _ls _l = value ty_bool (Vbool false)

let eval_int_op op ls l =
  value (ty_of_ity ls.rs_cty.cty_result)
    ( match List.map v_desc l with
    | [Vnum i1; Vnum i2] -> (
      try Vnum (op i1 i2) with NotNum | Division_by_zero -> constr ls l )
    | _ -> constr ls l )

let eval_int_uop op ls l =
  let v_desc =
    match List.map v_desc l with
    | [Vnum i1] -> ( try Vnum (op i1) with NotNum -> constr ls l )
    | _ -> constr ls l in
  {v_desc; v_ty=ty_of_ity ls.rs_cty.cty_result}

let eval_int_rel op ls l =
  let v_desc =
    match List.map v_desc l with
    | [Vnum i1; Vnum i2] -> (
      try Vbool (op i1 i2) with NotNum -> constr ls l )
    | _ -> constr ls l in
  {v_desc; v_ty= ty_int}

(* This initialize Mpfr for float32 behavior *)
let initialize_float32 () = set_default_prec 24 ; set_emin (-148) ; set_emax 128

(* This initialize Mpfr for float64 behavior *)
let initialize_float64 () =
  set_default_prec 53 ; set_emin (-1073) ; set_emax 1024

type 'a float_arity =
  | Mode1 : (float_mode -> big_float -> big_float) float_arity (* Unary op *)
  | Mode2 : (float_mode -> big_float -> big_float -> big_float) float_arity (* binary op *)
  | Mode3
      : (float_mode -> big_float -> big_float -> big_float -> big_float)
        float_arity (* ternary op *)
  | Mode_rel : (big_float -> big_float -> bool) float_arity (* binary predicates *)
  | Mode_rel1 : (big_float -> bool) float_arity

let use_float_format (float_format : int) =
  match float_format with
  | 32 -> initialize_float32 ()
  | 64 -> initialize_float64 ()
  | _ -> raise CannotCompute

let eval_float :
    type a.
    ty -> int -> a float_arity -> a -> Expr.rsymbol -> value list -> value =
 fun ty_result float_format ty op ls l ->
  (* Set the exponent depending on Float type that are used: 32 or 64 *)
  use_float_format float_format ;
  try
    let v_desc =
      match ty, List.map v_desc l with
      | Mode1, [Vfloat_mode mode; Vfloat f] ->
          (* Subnormalize used to simulate IEEE behavior *)
          Vfloat (subnormalize ~rnd:mode (op mode f))
      | Mode2, [Vfloat_mode mode; Vfloat f1; Vfloat f2] ->
          Vfloat (subnormalize ~rnd:mode (op mode f1 f2))
      | Mode3, [Vfloat_mode mode; Vfloat f1; Vfloat f2; Vfloat f3] ->
          Vfloat (subnormalize ~rnd:mode (op mode f1 f2 f3))
      | Mode_rel, [Vfloat f1; Vfloat f2] -> Vbool (op f1 f2)
      | Mode_rel1, [Vfloat f] -> Vbool (op f)
      | _ -> constr ls l in
    {v_desc; v_ty= ty_result}
  with
  | Mlmpfr_wrapper.Not_Implemented -> raise CannotCompute
  | _ -> assert false

type 'a real_arity =
  | Modeconst : real real_arity
  | Mode1r : (real -> real) real_arity
  | Mode2r : (real -> real -> real) real_arity
  | Mode_relr : (real -> real -> bool) real_arity

let eval_real : type a. a real_arity -> a -> Expr.rsymbol -> value list -> value
    =
 fun ty op ls l ->
  let v_desc =
    try
      match ty, List.map v_desc l with
      | Mode1r, [Vreal r] -> Vreal (op r)
      | Mode2r, [Vreal r1; Vreal r2] -> Vreal (op r1 r2)
      | Mode_relr, [Vreal r1; Vreal r2] -> Vbool (op r1 r2)
      | Modeconst, [] -> Vreal op
      | _ -> constr ls l
    with
    | Big_real.Undetermined ->
        (* Cannot decide interval comparison *)
        constr ls l
    | Mlmpfr_wrapper.Not_Implemented -> raise CannotCompute
    | _ -> assert false in
  {v_desc; v_ty= ty_real}

let builtin_progs = Hrs.create 17

let builtin_mode _kn _its = ()
let builtin_float_type _kn _its = ()
let builtin_array_type _kn _its = ()

let exec_array_make ts_array _ args =
  match args with
  | [{v_desc= Vnum n};def] -> (
      try
        let n = BigInt.to_int n in
        let ty = ty_app ts_array [def.v_ty] in
        value ty (Varray (Array.make n def))
      with _ -> raise CannotCompute )
  | _ ->
      raise CannotCompute

let exec_array_empty ts_array _ args =
  match args with
  | [{v_desc= Vconstr(_, [])}] ->
      (* we know by typing that the constructor
         will be the Tuple0 constructor *)
      let ty = ty_app ts_array [ty_var (tv_of_string "a")] in
      value ty (Varray [||])
  | _ ->
      raise CannotCompute

let exec_array_get _ args =
  match args with
  | [{v_desc= Varray a}; {v_desc= Vnum i}] -> (
      try a.(BigInt.to_int i)
      with _ -> raise CannotCompute )
  | _ -> raise CannotCompute

let exec_array_length _ args =
  match args with
  | [{v_desc= Varray a}] ->
      value ty_int (Vnum (BigInt.of_int (Array.length a)))
  | _ -> raise CannotCompute

let exec_array_set _ args =
  match args with
  | [{v_desc= Varray a}; {v_desc= Vnum i}; v] -> (
      try
        a.(BigInt.to_int i) <- v;
        value ty_unit Vvoid
      with _ -> raise CannotCompute )
| _ -> assert false

(* Described as a function so that this code is not executed outside of
   why3execute. *)

(** Description of modules *)
let built_in_modules env =
  let bool_module =
    ["bool"], "Bool", [], ["True", eval_true; "False", eval_false] in
  let int_ops =
    [ op_infix "+", eval_int_op BigInt.add;
      (* defined as x+(-y)
         op_infix "-", eval_int_op BigInt.sub; *)
      op_infix "*", eval_int_op BigInt.mul;
      op_prefix "-", eval_int_uop BigInt.minus;
      op_infix "=", eval_int_rel BigInt.eq;
      op_infix "<", eval_int_rel BigInt.lt;
      op_infix "<=", eval_int_rel BigInt.le;
      op_infix ">", eval_int_rel BigInt.gt;
      op_infix ">=", eval_int_rel BigInt.ge ] in
  let bounded_int_ops =
    ("of_int", eval_int_uop (fun x -> x)) ::
    ("to_int", eval_int_uop (fun x -> x)) ::
    (op_infix "-", eval_int_op BigInt.sub) ::
    (op_infix "/", eval_int_op BigInt.computer_div) ::
    (op_infix "%", eval_int_op BigInt.computer_mod) ::
    int_ops in
  let int_modules =
    [ ( ["int"],
        "Int",
        [],
        int_ops );
      ( ["int"],
        "MinMax",
        [],
        ["min", eval_int_op BigInt.min; "max", eval_int_op BigInt.max] );
      ( ["int"],
        "ComputerDivision",
        [],
        [ "div", eval_int_op BigInt.computer_div;
          "mod", eval_int_op BigInt.computer_mod ] );
      ( ["int"],
        "EuclideanDivision",
        [],
        [ "div", eval_int_op BigInt.euclidean_div;
          "mod", eval_int_op BigInt.euclidean_mod ] ) ] in
  let int63_module = (["mach";"int"],"Int63",[],bounded_int_ops) in
  let int31_module = (["mach";"int"],"Int31",[],bounded_int_ops) in
  let byte_module  = (["mach";"int"],"Byte",[],bounded_int_ops) in
  let array_module =
    let pm = Pmodule.read_module env ["array"] "Array" in
    let {its_ts= ts_array} = Pmodule.ns_find_its pm.Pmodule.mod_export ["array"] in
    ["array"],"Array",
    ["array", builtin_array_type],
    ["make", exec_array_make ts_array;
     "empty", exec_array_empty ts_array;
     Ident.op_get "", exec_array_get ;
     "length", exec_array_length ;
     Ident.op_set "", exec_array_set ;
    ] in
  let mode_module =
    let pm = Pmodule.read_module env ["ieee_float"] "RoundingMode" in
    let its = Pmodule.ns_find_its pm.Pmodule.mod_export ["mode"] in
    let v_ty = ty_app its.its_ts [] in
    let aux m _ _ = value v_ty (Vfloat_mode m) in
    ( ["ieee_float"],
      "RoundingMode",
      ["mode", builtin_mode],
      [ "RNE", aux To_Nearest; "RNA", aux Away_From_Zero;
        "RTP", aux Toward_Plus_Infinity; "RTN", aux Toward_Minus_Infinity;
        "RTZ", aux Toward_Zero ] ) in
  let float_modules tyb ~prec m =
    let pm = Pmodule.read_module env ["ieee_float"] m in
    let its = Pmodule.ns_find_its pm.Pmodule.mod_export ["t"] in
    let ty = ty_app its.its_ts [] in
    ( ["ieee_float"],
      m,
      ["t", builtin_float_type],
      [ ("zeroF", fun _rs _l -> value ty (Vfloat (make_zero ~prec Positive)));
        "add", eval_float ty tyb Mode2 (fun rnd -> add ~rnd ~prec);
        "sub", eval_float ty tyb Mode2 (fun rnd -> sub ~rnd ~prec);
        "mul", eval_float ty tyb Mode2 (fun rnd -> mul ~rnd ~prec);
        "div", eval_float ty tyb Mode2 (fun rnd -> div ~rnd ~prec);
        "abs", eval_float ty tyb Mode1 (fun rnd -> abs ~rnd ~prec);
        "neg", eval_float ty tyb Mode1 (fun rnd -> neg ~rnd ~prec);
        "fma", eval_float ty tyb Mode3 (fun rnd -> fma ~rnd ~prec);
        "sqrt", eval_float ty tyb Mode1 (fun rnd -> sqrt ~rnd ~prec);
        "roundToIntegral", eval_float ty tyb Mode1 (fun rnd -> rint ~rnd ~prec);
        (* Intentionnally removed from programs
           "min", eval_float_minmax min;
           "max", eval_float_minmax max; *)
        "le", eval_float ty_bool tyb Mode_rel lessequal_p;
        "lt", eval_float ty_bool tyb Mode_rel less_p;
        "eq", eval_float ty_bool tyb Mode_rel equal_p;
        "is_zero", eval_float ty_bool tyb Mode_rel1 zero_p;
        "is_infinite", eval_float ty_bool tyb Mode_rel1 inf_p;
        "is_nan", eval_float ty_bool tyb Mode_rel1 nan_p;
        ( "is_positive",
          eval_float ty_bool tyb Mode_rel1 (fun s -> signbit s = Positive) );
        ( "is_negative",
          eval_float ty_bool tyb Mode_rel1 (fun s -> signbit s = Negative) ) ] )
  in
  let real_module =
    ( ["real"],
      "Real",
      [],
      [ op_infix "=", eval_real Mode_relr Big_real.eq;
        op_infix "<", eval_real Mode_relr Big_real.lt;
        op_infix "<=", eval_real Mode_relr Big_real.le;
        op_prefix "-", eval_real Mode1r Big_real.neg;
        op_infix "+", eval_real Mode2r Big_real.add;
        op_infix "*", eval_real Mode2r Big_real.mul;
        op_infix "/", eval_real Mode2r Big_real.div ] ) in
  let real_square_module =
    ["real"], "Square", [], ["sqrt", eval_real Mode1r Big_real.sqrt] in
  let real_trigo_module =
    ["real"], "Trigonometry", [], ["pi", eval_real Modeconst (Big_real.pi ())]
  in
  let real_exp_log =
    ( ["real"],
      "ExpLog",
      [],
      [ "exp", eval_real Mode1r Big_real.exp;
        "log", eval_real Mode1r Big_real.log ] ) in
  (bool_module :: int_modules)
  @ [ real_module; real_square_module; real_trigo_module; real_exp_log;
      mode_module; float_modules 32 ~prec:24 "Float32";
      float_modules 64 ~prec:53 "Float64"; int63_module;
      int31_module; byte_module; array_module ]

let add_builtin_mo env (l, n, t, d) =
  let mo = Pmodule.read_module env l n in
  let exp = mo.Pmodule.mod_export in
  let kn = mo.Pmodule.mod_known in
  List.iter
    (fun (id, r) ->
      let its =
        try Pmodule.ns_find_its exp [id]
        with Not_found -> raise (CannotFind (l, n, id)) in
      r kn its)
    t ;
  List.iter
    (fun (id, f) ->
      let ps =
        try Pmodule.ns_find_rs exp [id]
        with Not_found -> raise (CannotFind (l, n, id)) in
      Hrs.add builtin_progs ps f)
    d

let get_builtin_progs env =
  List.iter (add_builtin_mo env) (built_in_modules env)

let get_pvs env pvs =
  let t =
    try Mvs.find pvs.pv_vs env.vsenv
    with Not_found ->
      eprintf "program variable %s not found in env@."
        pvs.pv_vs.vs_name.id_string ;
      assert false in
  t

(* DEFAULTS *)

let rec default_value_of_type known ity : value =
  let ty = ty_of_ity ity in
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg r -> default_value_of_types known r.reg_its r.reg_args r.reg_regs ty
  | Ityapp (ts, _, _) when its_equal ts its_int -> value ty (Vnum BigInt.zero)
  | Ityapp (ts, _, _) when its_equal ts its_real -> assert false (* TODO *)
  | Ityapp (ts, _, _) when its_equal ts its_bool -> value ty (Vbool false)
  (* | Ityapp(ts,_,_) when is_its_tuple ts -> assert false (* TODO *) *)
  | Ityapp (ts, l1, l2) -> default_value_of_types known ts l1 l2 ty

and default_value_of_types known ts l1 l2 ty : value =
  let cs =
    match Pdecl.((find_its_defn known ts).itd_constructors) with
    | cs :: _ -> cs
    | [] ->
        assert ts.its_nonfree;
        kasprintf failwith "Cannot create default value for non-free type %a@." Ity.print_its ts in
  let subst = its_match_regs ts l1 l2 in
  let ityl = List.map (fun pv -> pv.pv_ity) cs.rs_cty.cty_args in
  let tyl = List.map (ity_full_inst subst) ityl in
  let fl = List.map (fun ity -> field (default_value_of_type known ity)) tyl in
  value ty (Vconstr (cs, fl))

(* ROUTINE DEFINITIONS *)

type routine_defn =
  | Builtin of (rsymbol -> value list -> value)
  | LocalFunction of (rsymbol * cexp) list * cexp
  | Constructor of Pdecl.its_defn
  | Projection of Pdecl.its_defn

let rec find_def rs = function
  | d :: _ when rs_equal rs d.rec_sym ->
      d.rec_fun (* TODO : put rec_rsym in local env *)
  | _ :: l -> find_def rs l
  | [] -> raise Not_found

let rec find_constr_or_proj dl rs =
  match dl with
  | [] -> raise Not_found
  | d :: rem ->
      if List.mem rs d.Pdecl.itd_constructors then (
        Debug.dprintf debug "@[<hov 2>[interp] found constructor:@ %s@]@."
          rs.rs_name.id_string ;
        Constructor d )
      else if List.mem rs d.Pdecl.itd_fields then (
        Debug.dprintf debug "@[<hov 2>[interp] found projection:@ %s@]@."
          rs.rs_name.id_string ;
        Projection d )
      else
        find_constr_or_proj rem rs

let find_global_definition kn rs =
  match (Mid.find rs.rs_name kn).Pdecl.pd_node with
  | Pdecl.PDtype dl -> find_constr_or_proj dl rs
  | Pdecl.PDlet (LDvar _) -> raise Not_found
  | Pdecl.PDlet (LDsym (_, ce)) -> LocalFunction ([], ce)
  | Pdecl.PDlet (LDrec dl) ->
      let locs = List.map (fun d -> d.rec_rsym, d.rec_fun) dl in
      LocalFunction (locs, find_def rs dl)
  | Pdecl.PDexn _ -> raise Not_found
  | Pdecl.PDpure -> raise Not_found

let find_definition env (rs: rsymbol) =
  (* then try if it is a built-in symbol *)
  match Hrs.find builtin_progs rs with
  | f -> Builtin f
  | exception Not_found ->
      (* then try if it is a local function *)
      match Mrs.find rs env.funenv with
      | f -> LocalFunction ([], f)
      | exception Not_found ->
          (* else look for a global function *)
          find_global_definition env.mod_known rs

(* CONTRADICTION CONTEXT *)

type cntr_ctx =
  { c_desc: string;
    c_trigger_loc: Loc.position option;
    c_env: Env.env; (* to get builtins in Reduction_engine.create *)
    c_known: Decl.known_map; (* becomes Reduction_engine.engine.known_map *)
    c_rule_terms: term Mid.t;
    c_vsenv: term Mvs.t }

exception Contr of cntr_ctx * term

let cntr_desc str id =
  asprintf "%s of %a" str print_decoded id.id_string

let report_cntr_head fmt (ctx, msg, term) =
  let pp_pos fmt loc =
    let f, l, b, e = Loc.get loc in
    fprintf fmt "%s, line %d, characters %d-%d" f l b e in
  fprintf fmt "@[<v>%s %s" ctx.c_desc msg;
  ( match ctx.c_trigger_loc, term.t_loc with
    | Some t1, Some t2 ->
        fprintf fmt " at %a@,- Defined at %a" pp_pos t1 pp_pos t2
    | Some t, None | None, Some t ->
        fprintf fmt " at %a" pp_pos t
    | None, None -> () );
  fprintf fmt "@]"

let pp_vsenv pp_value fmt =
  let delims = Pp.(nothing, nothing) and sep = Pp.comma in
  fprintf fmt "%a" (pp_bindings ~delims ~sep Pretty.print_vs pp_value)

let report_cntr fmt (ctx, msg, term) =
  let cmp_vs (vs1, _) (vs2, _) =
    String.compare vs1.vs_name.id_string vs2.vs_name.id_string in
  let mvs = t_freevars Mvs.empty term in
  fprintf fmt "@[<v>%a@," report_cntr_head (ctx, msg, term);
  fprintf fmt "@[<hov2>- Term: %a@]@," Pretty.print_term term ;
  fprintf fmt "@[<hov2>- Variables: %a@]"
    (pp_vsenv Pretty.print_term)
    (List.sort cmp_vs (Mvs.bindings (Mvs.filter (fun vs _ -> Mvs.contains mvs vs) ctx.c_vsenv)));
  fprintf fmt "@]"

let rule_term decl =
  let open Decl in
  match decl.d_node with
  | Dprop (Paxiom, _, t) -> Some t
  | _ -> None

let add_fun_to_known rs cexp known =
  try
    let t =
      match cexp.c_node with
      | Cfun e -> Opt.get_exn Exit (term_of_expr ~prop:false e)
      | _ -> raise Exit in
    let ty_args = List.map (fun pv -> Ity.ty_of_ity pv.pv_ity) rs.rs_cty.cty_args in
    let ty_res = Ity.ty_of_ity rs.rs_cty.cty_result in
    let ls = Term.create_lsymbol (id_clone rs.rs_name) ty_args (Some ty_res) in
    let vs_args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
    let ldecl = Decl.make_ls_defn ls vs_args t in
    let decl = Decl.create_logic_decl [ldecl] in
    Mid.add rs.rs_name decl known
  with Exit -> known

let cntr_ctx desc ?trigger_loc ?(vsenv = Mvs.empty) env =
  let rule_terms = Mid.map_filter rule_term env.th_known in
  let known = Mrs.fold add_fun_to_known env.funenv env.th_known in
  let vsenv = Mvs.union (fun _ _ t -> Some t)
      vsenv (Mvs.map (term_of_value env.env) env.vsenv) in
  { c_env= env.env;
    c_desc= desc;
    c_trigger_loc= trigger_loc;
    c_known= known;
    c_rule_terms= rule_terms;
    c_vsenv= vsenv }

(* TERM EVALUATION *)

let try_add_rule _id t eng =
  let open Reduction_engine in
  try add_rule t eng
  with NotARewriteRule _s ->
    (* TODO Try to evaluate terms of the form `<t> -> if <t> then <t> else <t>` during
       normalization. *)
    (* Format.eprintf "@[<v2>Could not add rule for the axiomatization of %s:@ %a@ because %s.@]@."
     *   id.id_string Pretty.print_term t s; *)
    eng

let fix_vsenv_value vs t (vsenv, mt, mv) =
  match t.t_ty with
  | None -> (* Don't fix prop-typed terms *)
      vsenv, mt, mv
  | Some ty ->
    let vs' = create_vsymbol (id_clone vs.vs_name) ty in
    let vsenv = Mvs.add vs' t vsenv in
    let mt = ty_match mt vs.vs_ty ty in
    let mv = Mvs.add vs (t_var vs') mv in
    vsenv, mt, mv

(** Reduce a term using the reduction engine.

    @param env Why3 environment
    @param known Global definitions from the interpreted module
    @param rule_terms Rules to be added to the reduction engine
    @param vsenv Local variable environment
    @param t Term to be evaluated
    @return A reduction of term [t]
  *)
let reduce_term ?(mt = Mtv.empty) ?(mv = Mvs.empty) env known rule_terms vsenv t =
  let open Reduction_engine in
  let params =
    { compute_builtin= true;
      compute_defs= true;
      compute_def_set= Sls.empty } in
  let eng = create params env known in
  let eng = Mid.fold try_add_rule rule_terms eng in
  let vsenv, mt, mv = Mvs.fold fix_vsenv_value vsenv (Mvs.empty, mt, mv) in
  let t = t_ty_subst mt mv t in
  normalize ~limit:1000 eng vsenv t

(** Evaluate a term and raise an exception [Contr] if the result is false. *)
let check_term ctx t =
  (* TODO raise NoContrdiction / CannotEvaluate if [t] corresponds to the goal of the CE
     and reduces to true / cannot be reduced. *)
  match reduce_term ctx.c_env ctx.c_known ctx.c_rule_terms ctx.c_vsenv t with
  | {t_node= Ttrue} ->
      if Debug.test_flag debug_rac then
        eprintf "%a@." report_cntr_head (ctx, "is ok", t)
  | {t_node= Tfalse} ->
      raise (Contr (ctx, t))
  | t' ->
      eprintf "%a@." report_cntr (ctx, "cannot be evaluated", t) ;
      if Debug.test_flag debug_rac then
        eprintf "@[<hv2>- Result: %a@]@." Pretty.print_term t'
  | exception e when Debug.test_flag debug_rac ->
      eprintf "%a@." report_cntr (ctx, "WHEN TRYING", t) ;
      raise e

let check_terms ctx = List.iter (check_term ctx)

(* Check a post-condition [t] by binding the result variable to
   the term [vt] representing the result value. *)
let check_post ctx vt post =
  let vs, t = open_post post in
  let ctx = {ctx with c_vsenv= Mvs.add vs vt ctx.c_vsenv} in
  check_term ctx t

let check_posts desc loc env oldies v posts =
  let env = {env with vsenv= Mvs.union (fun _ _ v -> Some v) env.vsenv oldies} in
  let ctx = cntr_ctx desc ?trigger_loc:loc env in
  let vt = term_of_value env.env v in
  List.iter (fun t -> check_post ctx vt t) posts

(* EXPRESSION EVALUATION *)

(* Assuming the real is given in pow2 and pow5 *)
let compute_fraction {Number.rv_sig= i; Number.rv_pow2= p2; Number.rv_pow5= p5}
  =
  let p2_val = BigInt.pow_int_pos_bigint 2 (BigInt.abs p2) in
  let p5_val = BigInt.pow_int_pos_bigint 5 (BigInt.abs p5) in
  let num = ref BigInt.one in
  let den = ref BigInt.one in
  num := BigInt.mul i !num ;
  if BigInt.ge p2 BigInt.zero then
    num := BigInt.mul p2_val !num
  else
    den := BigInt.mul p2_val !den ;
  if BigInt.ge p5 BigInt.zero then
    num := BigInt.mul p5_val !num
  else
    den := BigInt.mul p5_val !den ;
  !num, !den

let rec matching env (v : value) p =
  match p.pat_node with
  | Pwild -> env
  | Pvar vs -> bind_vs vs v env
  | Por (p1, p2) -> (
      try matching env v p1 with NoMatch -> matching env v p2 )
  | Pas (p, vs) -> matching (bind_vs vs v env) v p
  | Papp (ls, pl) -> (
      match v.v_desc with
      | Vconstr ({rs_logic= RLls ls2}, tl) ->
          if ls_equal ls ls2 then
            List.fold_left2 matching env (List.map field_get tl) pl
          else if ls2.ls_constr > 0 then
            raise NoMatch
          else
            raise Undetermined
      | Vbool b ->
          let ls2 = if b then fs_bool_true else fs_bool_false in
          if ls_equal ls ls2 then env else raise NoMatch
      | _ -> raise Undetermined )

let is_true v = match v.v_desc with
  | Vbool true | Vterm {t_node= Ttrue} -> true
  | Vterm t when t_equal t t_bool_true -> true
  | _ -> false

let is_false v = match v.v_desc with
  | Vbool false | Vterm {t_node= Tfalse} -> true
  | Vterm t when t_equal t t_bool_false -> true
  | _ -> false

let fix_boolean_term t =
  if t_equal t t_true then t_bool_true else
  if t_equal t t_false then t_bool_false else t

let get_model_value model name loc =
  let open Model_parser in
  let aux me =
    me.me_name.men_name = name &&
    Opt.equal Loc.equal me.me_location (Some loc) in
  Opt.map (fun me -> me.me_value)
    (List.find_opt aux (Model_parser.get_model_elements model))

let model_value pv model =
  Opt.bind pv.pv_vs.vs_name.id_loc
    (get_model_value model pv.pv_vs.vs_name.id_string)

exception CannotImportModelValue of string

let rec import_model_value known ity =
  let open Model_parser in
  let get_def_subst ity =
    match ity.ity_node with
    | Ityapp (ts, l1, l2) | Ityreg {reg_its= ts; reg_args= l1; reg_regs= l2} ->
        Pdecl.find_its_defn known ts,
        its_match_regs ts l1 l2
    | _ -> assert false in
  let check_construction def =
    if def.Pdecl.itd_its.its_nonfree then (
      let msg = asprintf "Value of non-free type %a" print_ity ity in
      raise (CannotImportModelValue msg) );
    if is_range_type_def def.Pdecl.itd_its.its_def then (
      let msg = asprintf "Value of range type %a (TODO)" print_ity ity in
      raise (CannotImportModelValue msg) );
    if is_float_type_def def.Pdecl.itd_its.its_def then (
      let msg = asprintf "Value of float type %a (TODO)" print_ity ity in
      raise (CannotImportModelValue msg) ) in
  function
    | Integer s ->
        assert (ity_equal ity ity_int);
        value ty_int (Vnum (BigInt.of_string s))
    | String s ->
        assert (ity_equal ity ity_str);
        value ty_str (Vstring s)
    | Boolean b ->
        assert (ity_equal ity ity_bool);
        value ty_bool (Vbool b)
    | Record r ->
        let def, subst = get_def_subst ity in
        check_construction def;
        let rs = match def.Pdecl.itd_constructors with [c] -> c | _ -> assert false in
        let assoc_ity rs =
          let name =
            try Ident.get_model_element_name ~attrs:rs.rs_name.id_attrs
            with Not_found -> rs.rs_name.id_string in
          let ity = ity_full_inst subst (fd_of_rs rs).pv_ity in
          name, ity in
        let arg_itys = Mstr.of_list (List.map assoc_ity def.Pdecl.itd_fields) in
        let fs = List.map (fun (f, mv) -> import_model_value known (Mstr.find f arg_itys) mv) r in
        value (ty_of_ity ity) (Vconstr (rs, List.map field fs))
    | Apply (s, mvs) ->
        let def, subst = get_def_subst ity in
        check_construction def;
        let matching_name rs = String.equal rs.rs_name.id_string s in
        let rs = List.find matching_name def.Pdecl.itd_constructors in
        let import field_pv = import_model_value known (ity_full_inst subst field_pv.pv_ity) in
        let fs = List.map2 import rs.rs_cty.cty_args mvs in
        value (ty_of_ity ity) (Vconstr (rs, List.map field fs))
    | Proj (s, mv) ->
        let def, subst = get_def_subst ity in
        check_construction def;
        let matching_name rs = String.equal rs.rs_name.id_string s in
        let rs = List.find matching_name def.Pdecl.itd_constructors in
        let import_or_default field_pv =
          let ity = ity_full_inst subst field_pv.pv_ity in
          if String.equal field_pv.pv_vs.vs_name.id_string s
          then import_model_value known ity mv
          else default_value_of_type known ity in
        let fs = List.map import_or_default rs.rs_cty.cty_args in
        value (ty_of_ity ity) (Vconstr (rs, List.map field fs))
    | Array a ->
        let def, subst = get_def_subst ity in
        assert (its_equal def.Pdecl.itd_its its_func);
        let key_ity, value_ity = match def.Pdecl.itd_its.its_ts.ts_args with
          | [ts1; ts2] -> Mtv.find ts1 subst.isb_var, Mtv.find ts2 subst.isb_var
          | _ -> assert false in
        let add_index mv ix =
          let key = import_model_value known key_ity ix.arr_index_key in
          let value = import_model_value known value_ity ix.arr_index_value in
          Mv.add key value mv in
        let mv = List.fold_left add_index Mv.empty a.arr_indices in
        let v = import_model_value known value_ity a.arr_others in
        value (ty_of_ity ity) (Vpurefun (ty_of_ity key_ity, mv, v))
        (* let def, subst = get_def_subst ity in
         * if its_equal def.Pdecl.itd_its its_func then
         *   let key_ity, value_ity = match def.Pdecl.itd_its.its_ts.ts_args with
         *     | [ts1; ts2] -> Mtv.find ts1 subst.isb_var, Mtv.find ts2 subst.isb_var
         *     | _ -> assert false in
         *   let mvs, e0 =
         *     let pv = create_pvsymbol (id_fresh "default") value_ity in
         *     let v = import_model_value known value_ity a.arr_others in
         *     Mvs.singleton pv.pv_vs v, e_var pv in
         *   let arg_pv = create_pvsymbol (id_fresh "arg") key_ity in
         *   let aux ix (mvs, e) =
         *     let key_pv = create_pvsymbol (id_fresh "key") value_ity in
         *     let value_pv = create_pvsymbol (id_fresh "value") key_ity in
         *     let key_v = import_model_value known key_ity ix.arr_index_key in
         *     let value_v = import_model_value known value_ity ix.arr_index_value in
         *     let mvs = Mvs.add key_pv.pv_vs key_v (Mvs.add (value_pv.pv_vs) value_v mvs) in
         *     let test = e_exec (c_app rs_dyn_poly_equ [arg_pv; key_pv] [] ity_bool) in
         *     mvs, e_if test (e_var value_pv) e in
         *   let mvs, e = List.fold_right aux a.arr_indices (mvs, e0) in
         *   value (ty_of_ity ity) (Vfun (mvs, arg_pv.pv_vs, e))
         * else
         *   failwith "import_model_value array" *)
    | Decimal _ | Fraction _ | Float _ | Bitvector _ | Unparsed _ as v ->
        kasprintf failwith "import_model_value (not implemented): %a" print_model_value v


let exec_pure env ls pvs =
  if ls_equal ls ps_equ then
    (* TODO (?) Add more builtin logical symbols *)
    let pv1, pv2 = match pvs with [pv1; pv2] -> pv1, pv2 | _ -> assert false in
    let v1 = Mvs.find pv1.pv_vs env.vsenv and v2 = Mvs.find pv2.pv_vs env.vsenv in
    Normal (value ty_bool (Vbool (compare_values v1 v2 = 0)))
  else if ls_equal ls fs_func_app then
    failwith "Pure function application not yet implemented"
  else
    match Decl.find_logic_definition env.th_known ls with
    | Some defn ->
        let vs, t = Decl.open_ls_defn defn in
        let rule_terms = Mid.map_filter rule_term env.th_known in
        let known = Mrs.fold add_fun_to_known env.funenv env.th_known in
        let args = List.map (get_pvs env) pvs in
        let vsenv = List.fold_right2 Mvs.add vs args env.vsenv in
        let vsenv = Mvs.map (term_of_value env.env) vsenv in
        let t = reduce_term env.env known rule_terms vsenv t in
        (* TODO A variable x binding the result of exec pure are used as (x = True) in
           subsequent terms, so we map true/false to True/False here. Is this reasonable? *)
        let t = fix_boolean_term t in
        Normal (value (Opt.get_def ty_bool t.t_ty) (Vterm t))
    | None ->
        kasprintf failwith "No logic definition for %a"
          Pretty.print_ls ls

let pp_limited ?(n=100) pp fmt x =
  let s = asprintf "%a@." pp x in
  let s = String.map (function '\n' -> ' ' | c -> c) s in
  let s = String.sub s 0 (Pervasives.min n (String.length s)) in
  pp_print_string fmt s

let print_result fmt = function
  | Normal v -> print_value fmt v
  | Excep (xs, v) -> fprintf fmt "EXC %a: %a" print_xs xs print_value v
  | Fun (rs, _, _) -> fprintf fmt "FUN %a" print_rs rs
  | Irred e -> fprintf fmt "IRRED: %a" (pp_limited print_expr) e

exception InvCeInfraction of Loc.position option
exception AbstractExEnded of Loc.position option

let rec eval_expr ~rac ~abs env e =
  Debug.dprintf debug "@[<h>%t%sEVAL EXPR: %a@]@." pp_indent
    (if abs then "Abs. " else "Con. ")
    (pp_limited print_expr) e;
  let res = eval_expr' ~rac ~abs env e in
  Debug.dprintf debug "@[<h>%t -> %a@]@." pp_indent (print_result) res;
  res

(* abs = abstractly - do not execute loops and function calls - use
   instead invariants and function contracts to guide execution. *)
and eval_expr' ~rac ~abs env ({e_loc} as e) =
  let e_loc = Opt.get_def Loc.dummy_position e_loc in
  let get_value name ity loc =
    match get_model_value env.ce_model name loc with
    | Some v ->
       let v = import_model_value env.mod_known ity v in
       Debug.dprintf debug "@[<h>%tVALUE from ce-model: %a@]@."
         pp_indent print_value v;
       v
    | None -> Debug.dprintf debug "@[<h>%tVALUE not in ce-model@]@." pp_indent;
       default_value_of_type env.mod_known ity in
  let assign_written_vars env vs _ =
    let pv = restore_pv vs in
    if pv_affected e.e_effect.eff_writes pv then begin
        Debug.dprintf debug "@[<h>%tVAR %a is written in loop %a@]@."
          pp_indent print_pv pv
          (Pp.print_option Pretty.print_loc) pv.pv_vs.vs_name.id_loc;
        let value = get_value vs.vs_name.id_string pv.pv_ity e_loc in
        bind_vs vs value env end
    else env in
  match e.e_node with
  | Evar pvs -> (
    try
      let v = get_pvs env pvs in
      Debug.dprintf debug "[interp] reading var %s from env -> %a@\n"
        pvs.pv_vs.vs_name.id_string print_value v ;
      Normal v
    with Not_found -> assert false (* Irred e ? *) )
  | Econst (Constant.ConstInt c) ->
      Normal (value (ty_of_ity e.e_ity) (Vnum (big_int_of_const c)))
  | Econst (Constant.ConstReal r) ->
      (* ConstReal can be float or real *)
      if ity_equal e.e_ity ity_real then
        let p, q = compute_fraction r.Number.rl_real in
        let sp, sq = BigInt.to_string p, BigInt.to_string q in
        try Normal (value ty_real (Vreal (real_from_fraction sp sq)))
        with Mlmpfr_wrapper.Not_Implemented -> raise CannotCompute
      else
        let c = Constant.ConstReal r in
        let s = Format.asprintf "%a" Constant.print_def c in
        Normal (value ty_real (Vfloat (make_from_str s)))
  | Econst (Constant.ConstStr s) -> Normal (value ty_str (Vstring s))
  | Eexec (ce, cty) -> (
    match ce.c_node with
      | Cpur (ls, pvs) ->
          Debug.dprintf debug "@[<h>%tEVAL EXPR: EXEC PURE %a %a@]@." pp_indent Pretty.print_ls ls
            (Pp.print_list Pp.comma print_value) (List.map (get_pvs env) pvs);
          exec_pure env ls pvs
      | Cfun e' ->
        Debug.dprintf debug "@[<h>%tEVAL EXPR EXEC FUN: %a@]@." pp_indent print_expr e';
        let add_free pv = Mvs.add pv.pv_vs (Mvs.find pv.pv_vs env.vsenv) in
        let cl = Spv.fold add_free ce.c_cty.cty_effect.eff_reads Mvs.empty in
        let arg =
          match ce.c_cty.cty_args with [arg] -> arg | _ -> assert false in
        let match_free pv mt =
          let v = Mvs.find pv.pv_vs env.vsenv in
          ty_match mt pv.pv_vs.vs_ty v.v_ty in
        let mt = Spv.fold match_free cty.cty_effect.eff_reads Mtv.empty in
        let ty = ty_inst mt (ty_of_ity e.e_ity) in
        Normal (value ty (Vfun (cl, arg.pv_vs, e')))
    | Cany -> raise CannotCompute
    | Capp _ when cty.cty_args <> [] ->
        eprintf "Cannot compute partial function application";
        raise CannotCompute
    | Capp (rs, pvsl) ->
        assert (ce.c_cty.cty_args = []) ;
        exec_call ~rac ~abs ?loc:e.e_loc env rs pvsl e.e_ity )
  | Eassign l ->
      List.iter
        (fun (pvs, rs, value) ->
          let cstr, args =
            match (get_pvs env pvs).v_desc with
            | Vconstr (cstr, args) -> cstr, args
            | _ -> assert false in
          let rec search_and_assign constr_args args =
            match constr_args, args with
            | pv :: pvl, Field r :: vl ->
                if pv_equal pv (fd_of_rs rs) then
                  r := get_pvs env value
                else
                  search_and_assign pvl vl
            | _ -> raise CannotCompute in
          search_and_assign cstr.rs_cty.cty_args args)
        l ;
      Normal (value ty_unit Vvoid)
  | Elet (ld, e2) -> (
    match ld with
    | LDvar (pvs, e1) -> (
      match eval_expr ~rac ~abs env e1 with
      | Normal v ->
        let env = bind_pvs pvs v env in
        eval_expr ~rac ~abs env e2
      | r -> r )
    | LDsym (rs, ce) ->
        let env = {env with funenv= Mrs.add rs ce env.funenv} in
        eval_expr ~rac ~abs env e2
    | LDrec l ->
        let env' =
          { env with
            funenv=
              List.fold_left
                (fun acc d ->
                  Mrs.add d.rec_sym d.rec_fun (Mrs.add d.rec_rsym d.rec_fun acc))
                env.funenv l } in
        eval_expr ~rac ~abs env' e2 )
  | Eif (e1, e2, e3) -> (
    match eval_expr ~rac ~abs env e1 with
    | Normal v ->
      if is_true v then
        eval_expr ~rac ~abs env e2
      else if is_false v then
        eval_expr ~rac ~abs env e3
      else (
        eprintf "@[[Exec] Cannot decide condition of if: @[%a@]@]@." print_value v ;
        Irred e )
    | r -> r )
  | Ewhile (cond, inv, _var, e1) when abs -> begin
      (* arbitrary execution of an iteartion taken from the counterexample

        while e1 do invariant {I} e2 done
        ~>
        assert1 {I};
        assign_written_vars_with_ce;
        assert2 {I};
        if e1 then (e2;assert3 {I}; absurd* ) else ()

        1 - if assert1 fails, then we have a real couterexample
            (invariant init doesn't hold)
        2 - if assert2 fails, then we have a false counterexample
            (invariant does not hold at beginning of execution)
        3 - if assert3 fails, then we have a real counterexample
            (invariant does not hold after iteration)
        * stop the interpretation here - raise AbstractExEnded *)
      (* assert1 *)
      if rac then
        check_terms (cntr_ctx "Loop invariant initialization" env) inv;
      let env = Mvs.fold_left assign_written_vars env env.vsenv in
      (* assert2 *)
      (try check_terms (cntr_ctx "ce satisfies invariant" env) inv with
       | Contr (_,t) ->
          printf "ce model does not satisfy loop invariant %a@."
            (Pp.print_option Pretty.print_loc) t.t_loc;
          raise (InvCeInfraction t.t_loc));
      match eval_expr ~rac ~abs env cond with
      | Normal v ->
         if is_true v then begin
             match eval_expr ~rac ~abs env e1 with
             | Normal _ ->
                if rac then
                  check_terms (cntr_ctx "Loop invariant preservation" env) inv;
                raise (AbstractExEnded e.e_loc)
             | r -> r
           end
         else if is_false v then
           Normal (value ty_unit Vvoid)
         else (
           eprintf "@[[Exec] Cannot decide condition of while: @[%a@]@]@."
             print_value v ;
           Irred e )
      | r -> r
    end
  | Ewhile (cond, inv, _var, e1) -> begin
      (* TODO variants *)
      if rac then
        check_terms (cntr_ctx "Loop invariant initialization" env) inv ;
      match eval_expr ~rac ~abs env cond with
      | Normal v ->
          if is_true v then (
            match eval_expr ~rac ~abs env e1 with
            | Normal _ ->
                if rac then
                  check_terms (cntr_ctx "Loop invariant preservation" env) inv ;
                eval_expr ~rac ~abs env e
            | r -> r )
          else if is_false v then
            Normal (value ty_unit Vvoid)
          else (
            eprintf "@[[Exec] Cannot decide condition of while: @[%a@]@]@."
              print_value v ;
            Irred e )
      | r -> r end
  | Efor (pvs, (pvs1, dir, pvs2), _i, inv, e1) when abs -> begin
      (* arbitrary execution of an iteartion taken from the counterexample

        for i = e1 to e2 do invariant {I} e done
        ~>
        let a = eval_expr e1 in
        let b = eval_expr e2 in
        let i = a in assert1 {I};
        if a <= b then begin
          assign_written_vars_with_ce;
          let i = get_model_value i in
          assert2 { a <= i }; (*?? i <= b + 1 ??*)
          assert3 { I };
          if a <= b then begin
            eval_expr e;
            let i = i + 1 in assert4 {I};
            absurd
          end else ()
        end else ()

        1 - if assert1 fails, then we have a real counterexample
            (invariant init doesn't hold)
        2 - if assert2 fails, then we have a false counterexample
            (the value assigned to i is not compatible with for loop)
        3 - if assert3 fails, then we have a false counterexample
            (invariant does not hold at beginning of execution)
        4 - if assert4 fails, then we have a real counterexample
            (invariant does not hold after iteration) *)
      try
        let a = big_int_of_value (get_pvs env pvs1) in
        let b = big_int_of_value (get_pvs env pvs2) in
        let le, suc = match dir with
          | To -> BigInt.le, BigInt.succ
          | DownTo -> BigInt.ge, BigInt.pred in
        (* assert1 *)
        if rac then begin
          let env = bind_vs pvs.pv_vs (value ty_int (Vnum a)) env in
          check_terms (cntr_ctx "Loop invariant initialization" env) inv end;
        if le a b then begin
            let env = Mvs.fold_left assign_written_vars env env.vsenv in
            let pvs_v = get_value pvs.pv_vs.vs_name.id_string pvs.pv_ity
                              (Opt.get pvs.pv_vs.vs_name.id_loc) in
            let env = bind_vs pvs.pv_vs pvs_v env in
            let pvs_int = match pvs_v.v_desc with
                Vnum n -> n | _ -> assert false in
            (* assert2 *)
            if not (le a pvs_int) then begin
                printf "ce model does not satisfy loop bounds %a@."
                  (Pp.print_option Pretty.print_loc) e.e_loc;
                raise (InvCeInfraction e.e_loc) end;
            (* assert3 *)
            (try check_terms (cntr_ctx "ce satisfies invariant" env) inv with
             | Contr (_,t) ->
                printf "ce model does not satisfy loop invariant %a@."
                  (Pp.print_option Pretty.print_loc) t.t_loc;
                raise (InvCeInfraction t.t_loc));
            if le pvs_int b then begin
                match eval_expr ~rac ~abs env e1 with
                | Normal _ ->
                   let env = bind_vs pvs.pv_vs
                               (value ty_int (Vnum (suc pvs_int))) env in
                   (* assert4 *)
                   if rac then
                     check_terms
                       (cntr_ctx "Loop invariant preservation" env) inv;
                   raise (AbstractExEnded e.e_loc)
                | r -> r
              end
            else Normal (value ty_unit Vvoid)
          end
        else Normal (value ty_unit Vvoid)
      with NotNum -> Irred e
    end
  | Efor (pvs, (pvs1, dir, pvs2), _i, inv, e1) -> (
    try
      let a = big_int_of_value (get_pvs env pvs1) in
      let b = big_int_of_value (get_pvs env pvs2) in
      let le, suc =
        match dir with
        | To -> BigInt.le, BigInt.succ
        | DownTo -> BigInt.ge, BigInt.pred in
      let rec iter i =
        Debug.dprintf debug "[interp] for loop with index = %s@."
          (BigInt.to_string i) ;
        if le i b then
          let env' = bind_vs pvs.pv_vs (value ty_int (Vnum i)) env in
          match eval_expr ~rac ~abs env' e1 with
          | Normal _ ->
              if rac then
                check_terms (cntr_ctx "Loop invariant preservation" env') inv ;
              iter (suc i)
          | r -> r
        else
          Normal (value ty_unit Vvoid) in
      ( if rac then
          let env' = bind_vs pvs.pv_vs (value ty_int (Vnum a)) env in
          check_terms (cntr_ctx "Loop invariant initialization" env') inv ) ;
      iter a
    with NotNum -> Irred e )
  | Ematch (e0, ebl, el) -> (
      let r = eval_expr ~rac ~abs env e0 in
      match r with
      | Normal t -> (
          if ebl = [] then
            r
          else
            try exec_match ~rac ~abs env t ebl with Undetermined -> Irred e )
      | Excep (ex, t) -> (
        match Mxs.find ex el with
        | [], e2 ->
            (* assert (t = Vvoid); *)
            eval_expr ~rac ~abs env e2
        | [v], e2 ->
            let env' = bind_vs v.pv_vs t env in
            eval_expr ~rac ~abs env' e2
        | _ -> assert false (* TODO ? *)
        | exception Not_found -> r )
      | _ -> r )
  | Eraise (xs, e1) -> (
      let r = eval_expr ~rac ~abs env e1 in
      match r with Normal t -> Excep (xs, t) | _ -> r )
  | Eexn (_, e1) -> eval_expr ~rac ~abs env e1
  | Eassert (kind, t) ->
      let descr =
        match kind with
        | Expr.Assert -> "Assertion"
        | Expr.Assume -> "Assumption"
        | Expr.Check -> "Check" in
      if rac then check_term (cntr_ctx descr env) t ;
      Normal (value ty_unit Vvoid)
  | Eghost e1 ->
      Debug.dprintf debug "@[<h>%tEVAL EXPR: GHOST %a@]@." pp_indent print_expr e1;
      (* TODO: do not eval ghost if no assertion check *)
      eval_expr ~rac ~abs env e1
  | Epure t ->
      Debug.dprintf debug "@[<h>%tEVAL EXPR: PURE %a@]@." pp_indent Pretty.print_term t;
      let t =
        let rule_terms = Mid.map_filter rule_term env.th_known in
        let known = Mrs.fold add_fun_to_known env.funenv env.th_known in
        let vsenv = Mvs.map (term_of_value env.env) env.vsenv in
        reduce_term env.env known rule_terms vsenv t in
      Normal (value (Opt.get t.t_ty) (Vterm t))
  | Eabsurd ->
      eprintf "@[[Exec] unsupported expression: @[%a@]@]@."
        print_expr e ;
      Irred e

and exec_match ~rac ~abs env t ebl =
  let rec iter ebl =
    match ebl with
    | [] ->
        eprintf "[Exec] Pattern matching not exhaustive in evaluation@." ;
        assert false
    | (p, e) :: rem -> (
      try
        let env' = matching env t p.pp_pat in
        eval_expr ~rac ~abs env' e
      with NoMatch -> iter rem ) in
  iter ebl

and exec_call ~rac ~abs ?loc env rs arg_pvs ity_result =
  let arg_vs = List.map (get_pvs env) arg_pvs in
  (* Debug.dprintf debug_rac "@[<h>Exec call %a %a@]@."
   *   print_rs rs Pp.(print_list space print_value) arg_vs; *)
  let env = multibind_pvs rs.rs_cty.cty_args arg_vs env in
  let oldies =
    let snapshot_oldie old_pv pv =
      Mvs.add old_pv.pv_vs (snapshot (Mvs.find pv.pv_vs env.vsenv)) in
    Mpv.fold snapshot_oldie rs.rs_cty.cty_oldies Mvs.empty in
  if rac then (
    (* TODO variant *)
    let ctx = cntr_ctx (cntr_desc "Precondition" rs.rs_name) ?trigger_loc:loc env in
    check_terms ctx rs.rs_cty.cty_pre );
  let res =
    if rs_equal rs rs_func_app then
      match arg_vs with
      | [{v_desc= Vfun (cl, arg, e)}; value] ->
          let env =
            {env with vsenv= Mvs.union (fun _ _ v -> Some v) env.vsenv cl} in
          let env = bind_vs arg value env in
          eval_expr ~rac ~abs env e
      | [{v_desc= Vpurefun (_, bindings, default)}; value] ->
          let v = try Mv.find value bindings with Not_found -> default in
          Normal v
      | _ -> assert false
    else
      match find_definition env rs with
      | LocalFunction (locals, ce) -> (
          let env = add_local_funs locals env in
          match ce.c_node with
            | Capp (rs', pvl) ->
                Debug.dprintf debug "@[<h>%tEXEC CALL %a: Capp %a]@." pp_indent print_rs rs print_rs rs';
                exec_call ~rac ~abs env rs' (pvl @ arg_pvs) ity_result
            | Cfun body ->
                Debug.dprintf debug"@[<hv2>%tEXEC CALL %a: FUN %a@]@." pp_indent print_rs rs (pp_limited print_expr) body;
                let env' = multibind_pvs ce.c_cty.cty_args arg_vs env in
                eval_expr ~rac ~abs env' body
            | Cany ->
                eprintf "@[<hv2>EXEC CALL %a: ANY@]@." print_rs rs;
                eprintf "Cannot compute any function %a" print_rs rs;
                raise CannotCompute
            | Cpur _ -> assert false (* TODO ? *) )
      | Builtin f ->
          Debug.dprintf debug "@[<hv2>EXEC CALL %a: BUILTIN@]@." print_rs rs;
          Normal (f rs arg_vs)
      | Constructor _ ->
          Debug.dprintf debug "@[<hv2>EXEC CALL %a: CONSTRUCTOR@]@." print_rs rs;
          let mt = List.fold_left2 ty_match Mtv.empty
              (List.map (fun pv -> pv.pv_vs.vs_ty) rs.rs_cty.cty_args) (List.map v_ty arg_vs) in
          let ty = ty_inst mt (ty_of_ity ity_result) in
          let fs = List.map field arg_vs in
          Normal (value ty (Vconstr (rs, fs)))
      | Projection _d -> (
        Debug.dprintf debug "@[<hv2>EXEC CALL %a: PROJECTION@]@." print_rs rs;
        match rs.rs_field, arg_vs with
        | Some pv, [{v_desc= Vconstr (cstr, args)}] ->
            let rec search constr_args args =
              match constr_args, args with
              | pv2 :: pvl, v :: vl ->
                  if pv_equal pv pv2 then
                    Normal (field_get v)
                  else search pvl vl
              | _ -> raise CannotCompute in
            search cstr.rs_cty.cty_args args
        | _ -> assert false )
      | exception Not_found ->
          eprintf "[interp] cannot find definition of routine %s@."
            rs.rs_name.id_string ;
          raise CannotCompute in
  ( if rac then
      match res with
      | Normal v ->
          let desc = cntr_desc "Postcondition" rs.rs_name in
          check_posts desc loc env oldies v rs.rs_cty.cty_post
      | Excep (xs, v) ->
          let desc = cntr_desc "Exceptional postcondition" rs.rs_name in
          let posts = Mxs.find xs rs.rs_cty.cty_xpost in
          check_posts desc loc env oldies v posts
      | _ -> () );
  res

(* GLOBAL EVALUATION *)

let init_real (emin, emax, prec) = Big_real.init emin emax prec

let make_global_env ?model known =
  let add_glob _id d acc =
    match d.Pdecl.pd_node with
    | Pdecl.PDlet (LDvar (pv, _e)) ->
        (* TODO evaluate _e! *)
        let v = match Opt.bind model (model_value pv) with
          | Some v -> import_model_value known pv.pv_ity  v
          | None -> default_value_of_type known pv.pv_ity in
        Mvs.add pv.pv_vs v acc
    | _ -> acc in
  Mid.fold add_glob known Mvs.empty

let eval_global_expr ~rac env mod_known th_known locals e =
  get_builtin_progs env ;
  let global_env = make_global_env mod_known in
  let env = add_local_funs locals
      { (default_env env) with mod_known; th_known; vsenv = global_env } in
  let res = eval_expr ~rac ~abs:false env e in
  res, global_env

let eval_global_fundef ~rac env mod_known mod_theory locals body =
  try eval_global_expr ~rac env mod_known mod_theory locals body
  with CannotFind (l, s, n) ->
    eprintf "Cannot find %a.%s.%s" (Pp.print_list Pp.dot pp_print_string) l s n ;
    assert false

let eval_rs ~abs env mod_known th_known _loc model (rs: rsymbol) =
  let get_value pv =
    match model_value pv model with
    | Some mv ->
        import_model_value mod_known pv.pv_ity mv
    | None ->
        Debug.dprintf debug_rac "Missing value for parameter %a; taking default@."
          print_pv pv;
        default_value_of_type mod_known pv.pv_ity in
  let arg_vs = List.map get_value rs.rs_cty.cty_args in
  get_builtin_progs env ;
  let global_env = make_global_env ~model mod_known in
  let env =
    { (default_env env) with mod_known; th_known; vsenv = global_env;
                             ce_model = model} in
  let env = multibind_pvs rs.rs_cty.cty_args arg_vs env in
  exec_call ~rac:true ~abs env rs rs.rs_cty.cty_args rs.rs_cty.cty_result

let maybe_ce_model_rs env pm loc model rs =
  let open Pmodule in
  let open Theory in
  begin try
      ignore (eval_rs ~abs:false env pm.mod_known
                pm.mod_theory.th_known loc model rs);
      printf "RAC does not confirm the counter-example (no \
              contradiction during execution)@."
    with
    | Contr (_, t) when Opt.equal Loc.equal
                          (Model_parser.get_model_term_loc model) t.Term.t_loc ->
       printf "RAC confirms the counter-example@."
    | Contr (_, t) ->
       printf "RAC found a contradiction at different location %a@."
         (Pp.print_option_or_default "NO LOC" Pretty.print_loc) t.Term.t_loc
    | CannotImportModelValue msg ->
       printf "RAC impossible: Cannot import model value: %s@." msg
    | Failure msg ->
       (* E.g., cannot create default value for non-free type, cannot construct
         term for constructor that is not a function *)
       printf "RAC failure: %s@." msg
  end;
  try
    ignore (eval_rs ~abs:true env pm.mod_known pm.mod_theory.th_known loc model rs);
    printf "Abstractly RAC does not confirm the counter-example \
            (execution did not fail at all)@.";
    None
  with
  | Contr (_, t) when Opt.equal Loc.equal
                        (Model_parser.get_model_term_loc model) t.Term.t_loc ->
     printf "Abstractly RAC confirms the counter-example@.";
     Some true
  | Contr (_, t) ->
     printf "Abstractly RAC found a contradiction at different location %a@."
       (Pp.print_option_or_default "NO LOC" Pretty.print_loc) t.Term.t_loc;
     None
  | CannotImportModelValue msg ->
     printf "Abstractly RAC impossible: Cannot import model value: %s@." msg;
     None
  | Failure msg ->
     (* E.g., cannot create default value for non-free type, cannot construct
         term for constructor that is not a function *)
     printf "Abstractly RAC failure: %s@." msg;
     None
  | AbstractExEnded l ->
     printf "Abstractly RAC cannot continue after %a@."
       (Pp.print_option Pretty.print_loc) l;
     None
  | InvCeInfraction l ->
     printf "Abstraclty RAC: counter-example model is not consistent \
             with the invariant %a@."
       (Pp.print_option Pretty.print_loc) l;
     None

(** [loc_contains loc1 loc2] if loc1 contains loc2, i.e., loc1:[   loc2:[   ]  ].
    Relies on [get_multiline] and fails under the same conditions. *)
let loc_contains loc1 loc2 =
  let f1, (bl1, bc1), (el1, ec1) = Loc.get_multiline loc1 in
  let f2, (bl2, bc2), (el2, ec2) = Loc.get_multiline loc2 in
  String.equal f1 f2 &&
  (bl1 < bl2 || (bl1 = bl2 && bc1 <= bc2)) &&
  (el1 > el2 || (el1 = el2 && ec1 >= ec2))

(** Identifies the rsymbol of the definition that contains the given position. Raises
    [Not_found] if no such definition is found. **)
let find_rs pm loc =
  let open Pmodule in
  let open Pdecl in
  let loc_of_exp e = Opt.get_def Loc.dummy_position e.e_loc in
  let loc_of_cexp ce = match ce.c_node with
    | Cfun e -> loc_of_exp e | _ -> Loc.dummy_position in
  let cty_loc_contains cty loc =
    let rec p = function
      | {t_loc= Some loc'} -> loc_contains loc' loc
      | {t_loc= None; t_node= Teps tb} ->
          (* The Teps introduced for post conditions does not carry its location *)
          p (snd (t_open_bound tb))
      | _ -> false in
    List.exists p (cty.cty_pre @ cty.cty_post @ List.concat (Mxs.values cty.cty_xpost)) in
  let exception Found of Expr.rsymbol in
  let find_pd_rec_defn rd =
    if loc_contains (loc_of_cexp rd.rec_fun) loc || cty_loc_contains rd.rec_sym.rs_cty loc then
      raise (Found rd.rec_sym) in
  let find_pd_pdecl pd =
    match pd.pd_node with
    | PDlet (LDsym (rs, ce))
      when loc_contains (loc_of_cexp ce) loc || cty_loc_contains rs.rs_cty loc ->
        raise (Found rs)
    | PDlet (LDrec rds) ->
        List.iter find_pd_rec_defn rds
    | _ -> () in
  let rec find_pd_mod_unit = function
    | Uuse _ | Uclone _ | Umeta _ -> ()
    | Uscope (_, us) -> List.iter find_pd_mod_unit us
    | Udecl pd -> find_pd_pdecl pd in
  match List.iter find_pd_mod_unit pm.mod_units with
  | () -> raise Not_found
  | exception Found rs -> rs

let maybe_ce_model env pm m =
  try
    let loc = Opt.get_exn Not_found (Model_parser.get_model_term_loc m) in
    if let f, _, _, _ = Loc.get loc in Sys.file_exists f then
      (* TODO deal with VC from variable declarations and type declarations *)
      let rs = find_rs pm loc in
      Opt.get_def true (maybe_ce_model_rs env pm loc m rs)
    else
      true
  with Not_found -> true

let report_eval_result body fmt (res, final_env) =
  match res with
  | Normal _ ->
      fprintf fmt "@[<hov2>result:@ %a@ =@ %a@]@,"
        print_ity body.e_ity print_logic_result res;
      fprintf fmt "@[<hov2>globals:@ %a@]"
        (pp_vsenv print_value) (Mvs.bindings final_env)
  | Excep _ ->
      fprintf fmt "@[<hov2>exceptional result:@ %a@]@,"
        print_logic_result res;
      fprintf fmt "@[<hov2>globals:@ %a@]"
        (pp_vsenv print_value) (Mvs.bindings final_env)
  | Irred _ | Fun _ ->
      fprintf fmt "@[<hov2>Execution error: %a@]@," print_logic_result res ;
      fprintf fmt "@[globals:@ %a@]" (pp_vsenv print_value) (Mvs.bindings final_env)

let report_cntr _body fmt (ctx, term) =
  report_cntr fmt (ctx, "failed", term)
