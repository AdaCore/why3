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
open Pretty
open Ity
open Expr
open Big_real
open Mlmpfr_wrapper
open Model_parser

let debug =
  Debug.register_info_flag "trace_exec"
    ~desc:"trace execution of code given by --exec or --eval"

let debug_rac = Debug.register_info_flag "rac" ~desc:"trace evaluation for RAC"
let debug_rac_check = Debug.register_info_flag "rac-check" ~desc:"trace checking assertions in RAC"

let print_loc fmt loc =
  let f, l, b, e = Loc.get loc in
  fprintf fmt "%S, line %d, characters %d-%d" f l b e

(** [loc_contains loc1 loc2] if loc1 contains loc2, i.e., loc1:[   loc2:[   ]  ].
    Relies on [get_multiline] and fails under the same conditions. *)
let loc_contains loc1 loc2 =
  if Loc.equal loc1 Loc.dummy_position || Loc.equal loc2 Loc.dummy_position then
    false (* loc_contains doesn't make sense, and calling get_multiline is invalid *)
  else
    let f1, b1, e1 = Loc.get_multiline loc1 in
    let f2, b2, e2 = Loc.get_multiline loc2 in
    let le (l1, c1) (l2, c2) = l1 < l2 || (l1 = l2 && c1 <= c2) in
    String.equal f1 f2 && le b1 b2 && le e2 e1

let pp_bindings ?(sep = Pp.semi) ?(pair_sep = Pp.arrow) ?(delims = Pp.(lbrace, rbrace))
    pp_key pp_value fmt l =
  let pp_binding fmt (k, v) =
    fprintf fmt "@[<h>%a%a%a@]" pp_key k pair_sep () pp_value v in
  fprintf fmt "%a%a%a" (fst delims) ()
    (Pp.print_list sep pp_binding)
    l (snd delims) ()


let pp_indent fmt =
  match Printexc.(backtrace_slots (get_callstack 100)) with
  | None -> ()
  | Some a ->
      let n = Pervasives.max 0 (Array.length a - 25) in
      let s = String.make (2 * n) ' ' in
      pp_print_string fmt s

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

  open Util

  let rec compare_values v1 v2 =
    let v_ty v = v.v_ty and v_desc v = v.v_desc in
    cmp [cmptr v_ty ty_compare; cmptr v_desc compare_desc] v1 v2
  and compare_desc d1 d2 =
    match d1, d2 with
    | Vconstr (rs1, fs1), Vconstr (rs2, fs2) ->
        let field_get (Field f) = !f in
        let cmp_fields = cmp_lists [cmptr field_get compare_values] in
        cmp [cmptr fst rs_compare; cmptr snd cmp_fields] (rs1, fs1) (rs2, fs2)
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
    | Vvoid, Vvoid -> 0
    | Vvoid, _ -> -1 | _, Vvoid -> 1
    | Vfun _, Vfun _ ->
        failwith "Value.compare: Vfun"
    | Vfun _, _ -> -1 | _, Vfun _ -> 1
    | Vpurefun (ty1, mv1, v1), Vpurefun (ty2, mv2, v2) ->
        cmp [
          cmptr (fun (x,_,_) -> x) ty_compare;
          cmptr (fun (_,x,_) -> x) (Mv.compare compare_values);
          cmptr (fun (_,_,x) -> x) compare_values;
        ] (ty1, mv1, v1) (ty2, mv2, v2)
    | Vpurefun _, _ -> -1 | _, Vpurefun _ -> 1
    | Vterm t1, Vterm t2 ->
        t_compare t1 t2
    | Vterm _, _ -> -1 | _, Vterm _ -> 1
    | Varray a1, Varray a2 ->
        cmp [
          cmptr Array.length (-);
          cmptr Array.to_list (cmp_lists [cmptr (fun x -> x) compare_values]);
        ] a1 a2
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
      fprintf fmt "(@[<v2>%tfun %a -> %a)@]"
        (fun fmt ->
           if not (Mvs.is_empty mvs) then
             fprintf fmt "%a " (pp_bindings print_vs print_value) (Mvs.bindings mvs))
        print_vs vs print_expr e
  | Vconstr (rs, vl) when is_rs_tuple rs ->
      fprintf fmt "(@[%a)@]" (Pp.print_list Pp.comma print_field) vl
  | Vconstr (rs, []) -> fprintf fmt "@[%a@]" print_rs rs
  | Vconstr (rs, vl) ->
      fprintf fmt "(@[%a %a)@]" print_rs rs
        (Pp.print_list Pp.space print_field)
        vl
  | Varray a ->
      fprintf fmt "@[[%a]@]"
        (Pp.print_list Pp.semi print_value)
        (Array.to_list a)
  | Vpurefun (_, mv, v) ->
      fprintf fmt "@[[|%a; _ -> %a|]@]" (pp_bindings ~delims:Pp.(nothing,nothing) print_value print_value)
        (Mv.bindings mv) print_value v
  | Vterm t ->
      fprintf fmt "(term:@ %a)" print_term t

and print_field fmt f = print_value fmt (field_get f)

let rec snapshot v =
  let v_desc = match v.v_desc with
    | Vconstr (rs, fs) -> Vconstr (rs, List.map snapshot_field fs)
    | Vfun (cl, vs, e) -> Vfun (Mvs.map snapshot cl, vs, e)
    | Vpurefun (ty, mv, v) ->
        let mv = Mv.(fold (fun k v -> add (snapshot k) (snapshot v)) mv empty) in
        Vpurefun (ty, mv, snapshot v)
    | Varray a -> Varray (Array.map snapshot a)
    | Vfloat _ | Vstring _ | Vterm _ | Vbool _ | Vreal _
    | Vfloat_mode _ | Vvoid | Vnum _ as vd -> vd in
  {v with v_desc}

and snapshot_field f =
  field (snapshot (field_get f))

(** Convert a value into a term. The first component of the result are additional bindings
    from closures, (roughly) sorted by strongly connected components. *)
let rec term_of_value env vsenv v : (vsymbol * term) list * term =
  match v.v_desc with
  | Vnum i -> vsenv, t_const (Constant.int_const i) v.v_ty
  | Vstring s -> vsenv, t_const (Constant.ConstStr s) ty_str
  | Vbool b -> vsenv, if b then t_bool_true else t_bool_false
  | Vvoid -> vsenv, t_tuple []
  | Vterm t -> vsenv, t
  | Vreal _ | Vfloat _ | Vfloat_mode _ -> (* TODO *)
      Format.kasprintf failwith "term_of_value: %a" print_value v
  | Vconstr (rs, fs) ->
      if rs_kind rs = RKfunc then
        let term_of_field vsenv f = term_of_value env vsenv (field_get f) in
        let vsenv, fs = Lists.map_fold_left term_of_field vsenv fs in
        vsenv, t_app_infer (ls_of_rs rs) fs
      else (* TODO bench/ce/{record_one_field,record_inv}.mlw/CVC4/WP *)
        kasprintf failwith "Cannot construct term for constructor \
                            %a that is not a function" print_rs rs
  | Vfun (cl, arg, e) ->
      (* TERM: fun arg -> t *)
      let t = Opt.get_exn (Failure "Cannot convert function body to term")
          (term_of_expr ~prop:false e) in

      (* Rebind values from closure *)
      let bind_cl vs v (mt, mv, vsenv) =
        let vs' = create_vsymbol (id_clone vs.vs_name) v.v_ty in
        let mt = ty_match mt vs.vs_ty v.v_ty in
        let mv = Mvs.add vs (t_var vs') mv in
        let vsenv, t = term_of_value env vsenv v in
        let vsenv = (vs', t) :: vsenv in
        mt, mv, vsenv in
      let mt, mv, vsenv = Mvs.fold bind_cl cl (Mtv.empty, Mvs.empty, vsenv) in

      (* Substitute argument type *)
      let ty_arg = match v.v_ty.ty_node with
        | Tyapp (ts, [ty_arg; _]) when ts_equal ts ts_func -> ty_arg
        | _ -> assert false in
      let mt = ty_match mt arg.vs_ty ty_arg in
      let arg' = create_vsymbol (id_clone arg.vs_name) ty_arg in
      let mv = Mvs.add arg (t_var arg') mv in
      let t = t_ty_subst mt mv t in
      vsenv, t_lambda [arg'] [] t
  | Varray a ->
      (* TERM: [make a.length (eps v. true)][0 <- a[0]]...[n-1 <- a[n-1]] *)
      let pm = Pmodule.read_module env ["array"] "Array" in
      let ls_make = Mstr.find "make" pm.Pmodule.mod_theory.Theory.th_export.Theory.ns_ls in
      let ls_update = Mstr.find (Ident.op_update "") pm.Pmodule.mod_theory.Theory.th_export.Theory.ns_ls in
      let rec loop (vsenv, t) ix =
        if ix = Array.length a then vsenv, t
        else
          let t_ix = t_const (Constant.int_const_of_int ix) ty_int in
          let vsenv, t_a_ix = term_of_value env vsenv a.(ix) in
          let t = t_app_infer ls_update [t; t_ix; t_a_ix] in
          loop (vsenv, t) (succ ix) in
      let t_n = t_const (Constant.int_const_of_int (Array.length a)) ty_int in
      let t_v =
        let val_ty = match v.v_ty.ty_node with
          | Tyapp (_, [ty]) -> ty
          | _ -> assert false in
        let vs = create_vsymbol (Ident.id_fresh "v") val_ty in
        t_eps (t_close_bound vs t_true) in
      let t_make = t_app_infer ls_make [t_n; t_v] in
      loop (vsenv, t_make) 0
  | Vpurefun (ty, m, v) ->
      (* TERM: fun arg -> if arg = k0 then v0 else ... else v *)
      (* TODO Use function literal [|mv...; _ -> v|] when available in Why3 *)
      let arg = create_vsymbol (id_fresh "arg") ty in
      let mk_case key value (vsenv, t) =
        let vsenv, key = term_of_value env vsenv key in      (* k_i *)
        let vsenv, value = term_of_value env vsenv value in  (* v_i *)
        let t = t_if (t_equ (t_var arg) key) value t in (* if arg = k_i then v_i else ... *)
        vsenv, t in
      let vsenv, t = Mv.fold mk_case m (term_of_value env vsenv v) in
      vsenv, t_lambda [arg] [] t

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

type rac_prover = Rac_prover of {command: string; driver: Driver.driver; limit_time: int}

let rac_prover config env ~limit_time s =
  let open Whyconf in
  let prover = filter_one_prover config (parse_filter_prover s) in
  let command = String.concat " " (prover.command :: prover.extra_options) in
  let driver = load_driver (get_main config) env prover.driver prover.extra_drivers in
  Rac_prover {command; driver; limit_time}

type model_value = Loc.position * vsymbol * value

type env =
  { mod_known   : Pdecl.known_map;
    th_known    : Decl.known_map;
    funenv      : Expr.cexp Mrs.t;
    vsenv       : value Mvs.t;
    ce_model    : model;
    env         : Env.env;
    rac_trans   : Task.task Trans.tlist option;
    rac_prover  : rac_prover option;
    used_values : model_value list ref (* values taken from the ce model *)
  }

let default_env env =
  { mod_known= Mid.empty; th_known= Mid.empty; funenv= Mrs.empty;
    vsenv= Mvs.empty; ce_model= default_model; rac_trans= None;
    rac_prover= None; env; used_values= ref [] }

let register_used_value env loc vs value =
  env.used_values := (loc, vs, snapshot value) :: !(env.used_values)

let snapshot_env env = {env with vsenv= Mvs.map snapshot env.vsenv}

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
  {v_desc; v_ty= ty_bool}

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

(* TODO Remove argument [env] after replacing Varray by model substitution *)
let rec default_value_of_type env known ity : value =
  let ty = ty_of_ity ity in
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityapp (ts, _, _) when its_equal ts its_int -> value ty (Vnum BigInt.zero)
  | Ityapp (ts, _, _) when its_equal ts its_real -> assert false (* TODO *)
  | Ityapp (ts, _, _) when its_equal ts its_bool -> value ty (Vbool false)
  (* | Ityapp(ts,_,_) when is_its_tuple ts -> assert false (* TODO *) *)
  | Ityreg {reg_its= its; reg_args= l1; reg_regs= l2}
  | Ityapp (its, l1, l2) ->
      let is_array_its env its =
        let pm = Pmodule.read_module env ["array"] "Array" in
        let array_its = Pmodule.ns_find_its pm.Pmodule.mod_export ["array"] in
        its_equal its array_its in
      if is_array_its env its then
        value ty (Varray (Array.init 0 (fun _ -> assert false)))
      else
      let itd = Pdecl.find_its_defn known its in
      match itd.Pdecl.itd_its.its_def with
      | Range r -> value ty (Vnum r.Number.ir_lower)
      | _ ->
      let cs =
        match itd.Pdecl.itd_constructors with
        | cs :: _ -> cs
        | [] ->
            if not its.its_nonfree then
              kasprintf failwith "not non-free type without constructors: %a" print_its its;
            (* TODO Axiomatize values of record fields by rules in the reduction engine?
               Cf. bench/ce/records_inv.mlw *)
            kasprintf failwith "Cannot create default value for non-free type %a" Ity.print_its its in
      let subst = its_match_regs its l1 l2 in
      let ityl = List.map (fun pv -> pv.pv_ity) cs.rs_cty.cty_args in
      let tyl = List.map (ity_full_inst subst) ityl in
      let fl = List.map (fun ity -> field (default_value_of_type env known ity)) tyl in
      value ty (Vconstr (cs, fl))

(* VALUE IMPORT *)

let get_model_value model name loc =
  let aux me =
    me.me_name.men_name = name &&
    Opt.equal Loc.equal me.me_location (Some loc) in
  Opt.map (fun me -> me.me_value)
    (List.find_opt aux (get_model_elements model))

let model_value model pv =
  Opt.bind pv.pv_vs.vs_name.id_loc
    (get_model_value model pv.pv_vs.vs_name.id_string)

exception CannotImportModelValue of string

(* TODO Remove argument [env] after replacing Varray by model substitution *)
let rec import_model_value env known ity v =
  (* TODO If the type has a model projection `p` and the model value is a
     projection `p _ = v`, we could add this equality as a rule to the
     reduction engine. (Cf. bench/ce/oracles/double_projection.mlw) *)
  (* TODO If the type is a non-free record, we could similarily axiomatize
     the values of the fields by rules in the reduction engine. (Cf.
     bench/ce/record_one_field.mlw)  *)
  let def, subst =
    match ity.ity_node with
    | Ityapp (ts, l1, l2) | Ityreg {reg_its= ts; reg_args= l1; reg_regs= l2} ->
        Pdecl.find_its_defn known ts,
        its_match_regs ts l1 l2
    | Ityvar _ -> assert false in
  (* let is_ity_array env ity =
   *   let pm = Pmodule.read_module env ["array"] "Array" in
   *   let its_array = Pmodule.ns_find_its pm.Pmodule.mod_export ["array"] in
   *   match ity.ity_node with
   *   | Ityreg r -> its_equal r.reg_its its_array
   *   | _ -> false in *)
  (* if is_ity_array env ity then (\* TODO *\)
   *   kasprintf failwith "ARRAY: %a@." print_model_value v
   * else *)
  if is_range_type_def def.Pdecl.itd_its.its_def then
    match v with
    | Proj (_, Integer s)
    | Integer s -> value (ty_of_ity ity) (Vnum (BigInt.of_string s))
    | _ -> assert false
  else
    let check_construction def =
      if def.Pdecl.itd_its.its_nonfree then
        let msg = asprintf "Value of non-free type %a" print_ity ity in
        raise (CannotImportModelValue msg) in
    match v with
    | Integer s ->
        assert (ity_equal ity ity_int);
        value (ty_of_ity ity) (Vnum (BigInt.of_string s))
    | String s ->
        assert (ity_equal ity ity_str);
        value ty_str (Vstring s)
    | Boolean b ->
        assert (ity_equal ity ity_bool);
        value ty_bool (Vbool b)
    | Record r ->
        check_construction def;
        let rs = match def.Pdecl.itd_constructors with [c] -> c | _ -> assert false in
        let assoc_ity rs =
          let name =
            try Ident.get_model_element_name ~attrs:rs.rs_name.id_attrs
            with Not_found -> rs.rs_name.id_string in
          let ity = ity_full_inst subst (fd_of_rs rs).pv_ity in
          name, ity in
        let arg_itys = Mstr.of_list (List.map assoc_ity def.Pdecl.itd_fields) in
        let fs = List.map (fun (f, mv) -> import_model_value env known (Mstr.find f arg_itys) mv) r in
        value (ty_of_ity ity) (Vconstr (rs, List.map field fs))
    | Apply (s, mvs) ->
        check_construction def;
        let matching_name rs = String.equal rs.rs_name.id_string s in
        let rs = List.find matching_name def.Pdecl.itd_constructors in
        let import field_pv = import_model_value env known (ity_full_inst subst field_pv.pv_ity) in
        let fs = List.map2 import rs.rs_cty.cty_args mvs in
        value (ty_of_ity ity) (Vconstr (rs, List.map field fs))
    | Proj (s, mv) ->
        check_construction def;
        let rs = match def.Pdecl.itd_constructors with
          | [rs] -> rs
          | [] ->
              eprintf "Cannot import projection to type without constructor";
              raise CannotCompute
          | _ -> failwith "(Singleton) record constructor expected" in
        let import_or_default field_pv =
          let ity = ity_full_inst subst field_pv.pv_ity in
          let name = field_pv.pv_vs.vs_name.id_string and attrs = field_pv.pv_vs.vs_name.id_attrs in
          if String.equal (Ident.get_model_trace_string ~name ~attrs) s then
            import_model_value env known ity mv
          else default_value_of_type env known ity in
        let fs = List.map import_or_default rs.rs_cty.cty_args in
        value (ty_of_ity ity) (Vconstr (rs, List.map field fs))
    | Array a ->
        assert (its_equal def.Pdecl.itd_its its_func);
        let key_ity, value_ity = match def.Pdecl.itd_its.its_ts.ts_args with
          | [ts1; ts2] -> Mtv.find ts1 subst.isb_var, Mtv.find ts2 subst.isb_var
          | _ -> assert false in
        let add_index mv ix =
          let key = import_model_value env known key_ity ix.arr_index_key in
          let value = import_model_value env known value_ity ix.arr_index_value in
          Mv.add key value mv in
        let mv = List.fold_left add_index Mv.empty a.arr_indices in
        let v0 = import_model_value env known value_ity a.arr_others in
        value (ty_of_ity ity) (Vpurefun (ty_of_ity key_ity, mv, v0))
    | Decimal _ | Fraction _ | Float _ | Bitvector _ | Unparsed _ as v ->
        kasprintf failwith "import_model_value (not implemented): %a" print_model_value v

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
    c_env: env;
  }

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
  fprintf fmt "%a" (pp_bindings ~delims ~sep print_vs pp_value)

let report_cntr fmt (ctx, msg, term) =
  let cmp_vs (vs1, _) (vs2, _) =
    String.compare vs1.vs_name.id_string vs2.vs_name.id_string in
  let mvs = t_freevars Mvs.empty term in
  fprintf fmt "@[<v>%a@," report_cntr_head (ctx, msg, term);
  fprintf fmt "@[<hv2>- Term: %a@]@," print_term term ;
  fprintf fmt "@[<hv2>- Variables: %a@]" (pp_vsenv print_value)
    (List.sort cmp_vs (Mvs.bindings (Mvs.filter (fun vs _ -> Mvs.contains mvs vs) ctx.c_env.vsenv)));
  fprintf fmt "@]"

let cntr_ctx desc ?trigger_loc env =
  { c_desc= desc;
    c_trigger_loc= trigger_loc;
    c_env= snapshot_env env}

(* VISITED LOCATIONS *)

(* A spurious model element has a location that has not been encountered during RAC.

   TODO Models with spurious elements are considered invalid.

   To identify spurious model elements, we collect initially the location of all variable
   declarations, and during RAC the locations of all encountered expressions and function
   parameters. Finally, we check for model elements with locations that have not been
   recorded. *)

let reset_visited_locs, visit_loc, visited_all_model_locs =
  let visited = Hstr.create 7 in
  let reset () =
    Hstr.reset visited in
  let visit loc =
    let f, l, _, _ = Loc.get loc in
    let lines =
      try Hstr.find visited f
      with Not_found -> Sint.empty in
    Hstr.replace visited f (Sint.add l lines) in
  let check model =
    let pp_visited fmt =
      let pp_f_ls f ls = fprintf fmt "%s:%a" f (Pp.print_list Pp.comma Pp.int) (Sint.elements ls) in
      Hstr.iter pp_f_ls visited in
    Debug.dprintf debug_rac "@[<hov2>Visited: %t@]@." pp_visited;
    let not_visited =
      List.filter (fun (f, l) -> let lines = Hstr.find_def visited Sint.empty f in not (Sint.mem l lines))
        (List.map (fun loc -> let f, l, _, _ = Loc.get loc in f, l)
           (Lists.map_filter (fun me -> me.me_location)
              (get_model_elements model))) in
    if not_visited <> [] then (
      let pp_f_l fmt (f, l) = fprintf fmt "%s:%d" f l in
      Debug.dprintf debug_rac "@[<hov2>Not visited %a@]@." (Pp.print_list Pp.space pp_f_l) not_visited );
    not_visited = [] in
  reset, visit, check

(** Iterate the locations of variable declarations in [known] with function [f]. **)
let iter_decl_locs f known =
  let visit_decl d = let open Pdecl in match d.pd_node with
    | PDlet (LDvar (pv, _)) -> Opt.iter f pv.pv_vs.vs_name.id_loc
    | _ -> () in
  Mid.iter (fun _ -> visit_decl) known

(* TERM EVALUATION *)

(* Add declarations for additional term bindings in [vsenv] *)
let bind_term (vs, t) (task, ls_mt, ls_mv) =
  let ty = Opt.get t.t_ty in
  let ls = create_fsymbol (id_clone vs.vs_name) [] ty in
  let ls_mt = ty_match ls_mt vs.vs_ty ty in
  let ls_mv = Mvs.add vs (fs_app ls [] ty) ls_mv in
  let t = t_ty_subst ls_mt ls_mv t in
  let defn = Decl.make_ls_defn ls [] t in
  let task = Task.add_logic_decl task [defn] in
  task, ls_mt, ls_mv

let task_of_term ?(vsenv=[]) env t =
  let open Task in let open Decl in
  let task, ls_mt, ls_mv = None, Mtv.empty, Mvs.empty in
  let task = List.fold_left use_export task Theory.[builtin_theory; bool_theory; highord_theory] in
  let task = use_export task (Env.read_theory env.env ["map"] "MapExt") in (* TODO remove, use map.MapExt where necessary in program *)
  (* Add known declarations *)
  let add_known _ decl task =
    match decl.d_node with
    | Dprop (Pgoal, _, _) -> task
    | Dprop (Plemma, prs, t) ->
        add_decl task (create_prop_decl Paxiom prs t)
    | _ -> add_decl task decl in
  let task = Mid.fold add_known env.th_known task in
  (* Add declarations from local functions in [env.funenv] *)
  let bind_fun rs cexp (task, ls_mv) =
    try
      let t = match cexp.c_node with
        | Cfun e -> Opt.get_exn Exit (term_of_expr ~prop:false e)
        | _ -> raise Exit in
      let ty_args = List.map (fun pv -> Ity.ty_of_ity pv.pv_ity) rs.rs_cty.cty_args in
      let ty_res = Ity.ty_of_ity rs.rs_cty.cty_result in
      let ls, ls_mv = match rs.rs_logic with
        | RLlemma | RLnone -> raise Exit
        | RLls ls -> ls, ls_mv
        | RLpv {pv_vs= vs} ->
            let ls = create_fsymbol (id_clone rs.rs_name) ty_args ty_res in
            let vss = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
            let ts = List.map t_var vss in
            let t0 = fs_app ls ts ty_res in
            let t = t_lambda vss [] t0 in
            let ls_mv = Mvs.add vs t ls_mv in
            ls, ls_mv in
      let vs_args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
      let decl = make_ls_defn ls vs_args t in
      let task = add_logic_decl task [decl] in
      task, ls_mv
    with Exit -> task, ls_mv in
  let task, ls_mv = Mrs.fold bind_fun env.funenv (task, ls_mv) in
  let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
  (* Add declarations for value bindings in [env.vsenv] *)
  let bind_value vs v (task, ls_mt, ls_mv) =
    let ls = create_fsymbol (id_clone vs.vs_name) [] v.v_ty in
    let ls_mt = ty_match ls_mt vs.vs_ty v.v_ty in
    let ls_mv = Mvs.add vs (fs_app ls [] v.v_ty) ls_mv in
    let vsenv, t = term_of_value env.env [] v in
    let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
    let t = t_ty_subst ls_mt ls_mv t in
    let defn = make_ls_defn ls [] t in
    let task = add_logic_decl task [defn] in
    task, ls_mt, ls_mv in
  let task, ls_mt, ls_mv = Mvs.fold bind_value env.vsenv (task, ls_mt, ls_mv) in
  let t = t_ty_subst ls_mt ls_mv t in
  let task =
    if t.t_ty = None then (* Add goal ... *)
      let prs = create_prsymbol (id_fresh "goal") in
      add_prop_decl task Pgoal prs t
    else (* ... or declaration *)
      let ls = create_lsymbol (id_fresh "value") [] t.t_ty in
      let decl = make_ls_defn ls [] t in
      add_logic_decl task [decl] in
  task, ls_mv

let bind_univ_quant_vars = true
let bind_univ_quant_vars_fallback_default = true

let bind_quants env task =
  let t = Task.task_goal_fmla task in
  try match t with
    | {t_node= Tquant (Tforall, tq)} when bind_univ_quant_vars ->
        let vs, _, t = t_open_quant tq in
        let get_value vs =
          match vs.vs_name with
          | {id_string= name; id_loc= Some loc} -> (
              match get_model_value env.ce_model name loc with
              | Some mv ->
                  let v = import_model_value env.env env.mod_known (ity_of_ty vs.vs_ty) mv in
                  Debug.dprintf debug_rac "Bind value for all-quantified %a to %a@." print_vs vs print_value v;
                  v
              | None ->
                  if bind_univ_quant_vars_fallback_default then (
                    let v = default_value_of_type env.env env.mod_known (ity_of_ty vs.vs_ty) in
                    Debug.dprintf debug_rac "Use default value for all-quantified %a: %a@." print_vs vs print_value v;
                    v
                  ) else (
                    Debug.dprintf debug_rac "No value for all-quantified %a@." print_vs vs;
                    raise Exit ) )
          | _ -> raise Exit (* Missing location, cannot identify CE value *) in
        let values = List.map get_value vs in
        let _, task = Task.task_separate_goal task in
        let bind_vs vs v (ls_mv, ls_mt, task) =
          let ls_mt = ty_match ls_mt vs.vs_ty v.v_ty in
          let ls = create_lsymbol (id_clone vs.vs_name) [] (Some v.v_ty) in
          let ls_mv = Mvs.add vs (fs_app ls [] v.v_ty) ls_mv in
          let vsenv, t = term_of_value env.env [] v in
          let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
          let defn = Decl.make_ls_defn ls [] t in
          let task = Task.add_logic_decl task [defn] in
          ls_mv, ls_mt, task in
        let ls_mv, ls_mt, task = List.fold_right2 bind_vs vs values (Mvs.empty, Mtv.empty, task) in
        let t = t_ty_subst ls_mt ls_mv t in
        let prs = Decl.create_prsymbol (id_fresh "goal") in
        Task.add_prop_decl task Decl.Pgoal prs t
    | _ -> raise Exit
  with Exit -> task

let task_hd_equal t1 t2 = let open Task in let open Theory in let open Decl in
  match t1.task_decl.td_node, t2.task_decl.td_node with
  | Decl {d_node = Dprop (Pgoal,p1,g1)}, Decl {d_node = Dprop (Pgoal,p2,g2)} ->
      (* Opt.equal (==) t1.task_prev t2.task_prev && *)
      pr_equal p1 p2 && t_equal_strict g1 g2
  | _ -> t1 == t2

(** Apply the (reduction) transformation and fill universally quantified variables
    in the head of the task by values from the CE model, recursively. *)
let rec trans_and_bind_quants env trans task =
  let task = bind_quants env task in
  let tasks = Trans.apply trans task in
  let task_unchanged = match tasks with
    | [task'] -> Opt.equal task_hd_equal task' task
    | _ -> false in
  if task_unchanged then tasks
  else List.flatten (List.map (trans_and_bind_quants env trans) tasks)

(** Compute the value of a term by using the (reduction) transformation *)
let compute_term env t =
  match env.rac_trans with
  | None -> t
  | Some trans ->
      let task, ls_mv = task_of_term env t in
      if t.t_ty = None then
        match List.map Task.task_goal_fmla (trans_and_bind_quants env trans task) with
        | [] -> t_true
        | t :: ts -> List.fold_left t_and t ts
      else
        let t = match Trans.apply trans task with
          | [Some Task.{task_decl= Theory.{td_node= Decl Decl.{d_node= Dlogic [_, ldef]}}}] ->
              ( match Decl.open_ls_defn ldef with
                | [], t -> t
                | _ ->  failwith "compute_term" )
          | _ -> failwith "compute_term" in
        (* Free vsymbols in [t] have been substituted in [task] by fresh
           lsymbols (actually: ls @ []) to bind them to the task declarations.
           Now we have to reverse these substitution to ensures that the reduced
           term is valid in the original environment of [t]. *)
        let reverse vs t' t = t_replace t' (t_var vs) t in
        Mvs.fold reverse ls_mv t

(** Check the validiy of a term that has been encoded in a task by the (reduction) transformation *)
let check_term_compute env trans task =
  let is_false = function
    | Some {Task.task_decl= Theory.{
        td_node= Decl Decl.{
            d_node= Dprop (Pgoal, _, {t_node= Tfalse})}}} ->
        true
    | _ -> false in
  match trans_and_bind_quants env trans task with
  | [] -> Some true
  | tasks ->
      Debug.dprintf debug_rac_check "Transformation produced %d tasks@." (List.length tasks);
      if List.exists is_false tasks then
        Some false
      else (
        List.iter (Debug.dprintf debug_rac_check "- %a@." print_tdecl)
          (Lists.map_filter (Opt.map (fun t -> t.Task.task_decl)) tasks);
        None )

(** Check the validiy of a term that has been encoded in a task by dispatching it to a prover *)
let check_term_dispatch (Rac_prover {command; driver; limit_time}) task =
  let open Call_provers in
  let limit = {empty_limit with limit_time} in
  let call = Driver.prove_task ~command ~limit driver task in
  let res = wait_on_call call in
  Debug.dprintf debug_rac_check "Check term dispatch answer: %a@."
    print_prover_answer res.pr_answer;
  match res.pr_answer with
  | Valid -> Some true
  | Invalid -> Some false
  | _ -> None

(* TODO replace by a strategy? e.g., t compute_in_goal; c Z3,4.8.7 2 2000 *)
let check_term ?vsenv ctx t =
  Opt.iter visit_loc t.t_loc;
  Debug.dprintf debug_rac_check "@[<hv2>Check term: %a@]@." print_term t;
  let task, _ = task_of_term ?vsenv ctx.c_env t in
  let res = (* Try checking the term using computation first ... *)
    Opt.map (fun b -> Debug.dprintf debug_rac_check "Computed.@."; b)
      (Opt.bind ctx.c_env.rac_trans
         (fun trans -> check_term_compute ctx.c_env trans task)) in
  let res =
    if res = None then (* ... then try solving using a prover *)
      Opt.map (fun b -> Debug.dprintf debug_rac_check "Dispatched.@."; b)
        (Opt.bind ctx.c_env.rac_prover
           (fun rp -> check_term_dispatch rp task))
    else res in
  match res with
  | Some true ->
      if Debug.test_flag debug_rac then
        eprintf "%a@." report_cntr_head (ctx, "is ok", t)
  | Some false ->
      raise (Contr (ctx, t))
  | None ->
      eprintf "%a@." report_cntr (ctx, "cannot be evaluated", t)

let check_terms ctx = List.iter (check_term ctx)

(* Check a post-condition [t] by binding the result variable to
   the term [vt] representing the result value. *)
let check_post ctx v post =
  let vs, t = open_post post in
  let vsenv = Mvs.add vs v ctx.c_env.vsenv in
  let ctx = {ctx with c_env= {ctx.c_env with vsenv}} in
  check_term ctx t

let check_posts desc loc env v posts =
  let ctx = cntr_ctx desc ?trigger_loc:loc env in
  List.iter (check_post ctx v) posts

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
        let args = List.map (get_pvs env) pvs in
        let vsenv = List.fold_right2 Mvs.add vs args env.vsenv in
        let t = compute_term {env with vsenv} t in
        (* TODO A variable x binding the result of exec pure are used as (x = True) in
           subsequent terms, so we map true/false to True/False here. Is this reasonable? *)
        let t = fix_boolean_term t in
        Normal (value (Opt.get_def ty_bool t.t_ty) (Vterm t))
    | None ->
        kasprintf failwith "No logic definition for %a" print_ls ls

let pp_limited ?(n=100) pp fmt x =
  let s = asprintf "%a" pp x in
  let s = String.map (function '\n' -> ' ' | c -> c) s in
  let s = String.(if length s > n then sub s 0 (Pervasives.min n (length s)) ^ "..." else s) in
  pp_print_string fmt s

let print_result fmt = function
  | Normal v -> print_value fmt v
  | Excep (xs, v) -> fprintf fmt "EXC %a: %a" print_xs xs print_value v
  | Fun (rs, _, _) -> fprintf fmt "FUN %a" print_rs rs
  | Irred e -> fprintf fmt "IRRED: %a" (pp_limited print_expr) e

exception AbstractRACStuck of env * Loc.position option

let rec eval_expr ~rac ~abs env e =
  Debug.dprintf debug "@[<h>%t%sEVAL EXPR: %a@]@." pp_indent
    (if abs then "Abs. " else "Con. ")
    (pp_limited print_expr) e;
  Opt.iter visit_loc e.e_loc;
  let res = eval_expr' ~rac ~abs env e in
  Debug.dprintf debug "@[<h>%t -> %a@]@." pp_indent (print_result) res;
  res

(* abs = abstractly - do not execute loops and function calls - use
   instead invariants and function contracts to guide execution. *)
and eval_expr' ~rac ~abs env e =
  let e_loc = Opt.get_def Loc.dummy_position e.e_loc in
  let get_value vs ity loc =
    let name = vs.vs_name.id_string in
    let value = match get_model_value env.ce_model name loc with
      | Some v ->
         let v = import_model_value env.env env.mod_known ity v in
         Debug.dprintf debug "@[<h>%tVALUE from ce-model: %a@]@."
           pp_indent print_value v;
         v
      | None -> eprintf "@[<h>VALUE for %s %a not in ce-model, taking \
                         default@]@."
                  name print_loc loc;
                default_value_of_type env.env env.mod_known ity in
    register_used_value env e_loc vs value;
    value in
  let assign_written_vars env vs _ =
    let pv = restore_pv vs in
    if pv_affected e.e_effect.eff_writes pv then begin
        Debug.dprintf debug "@[<h>%tVAR %a is written in loop %a@]@."
          pp_indent print_pv pv
          (Pp.print_option print_loc) pv.pv_vs.vs_name.id_loc;
        let value = get_value vs pv.pv_ity e_loc in
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
          Debug.dprintf debug "@[<h>%tEVAL EXPR: EXEC PURE %a %a@]@." pp_indent print_ls ls
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
        assert2* {I};
        if e1 then (e2;assert3 {I}; absurd* ) else ()

        1 - if assert1 fails, then we have a real couterexample
            (invariant init doesn't hold)
        2 - if assert2 fails, then we have a false counterexample
            (invariant does not hold at beginning of execution)
        3 - if assert3 fails, then we have a real counterexample
            (invariant does not hold after iteration)
        * stop the interpretation here - raise AbstractRACStuck *)
      (* assert1 *)
      if rac then
        check_terms (cntr_ctx "Loop invariant initialization" env) inv;
      let env = Mvs.fold_left assign_written_vars env env.vsenv in
      (* assert2 *)
      (try check_terms (cntr_ctx "ce satisfies invariant" env) inv with
       | Contr (_,t) ->
          printf "ce model does not satisfy loop invariant %a@."
            (Pp.print_option Pretty.print_loc) t.t_loc;
          raise (AbstractRACStuck (env, t.t_loc)));
      match eval_expr ~rac ~abs env cond with
      | Normal v ->
         if is_true v then begin
             match eval_expr ~rac ~abs env e1 with
             | Normal _ ->
                if rac then
                  check_terms (cntr_ctx "Loop invariant preservation" env) inv;
                raise (AbstractRACStuck (env,e.e_loc))
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
        if a <= b + 1 then begin
          (let i = a in assert1 {I});
          assign_written_vars_with_ce;
          let i = get_model_value i in  (* i is not registered as asgn *)
          if a <= i <= b then begin
            assert2* { I };
            eval_expr e;
            let i = i + 1 in
            assert3 {I};
            absurd
          end else begin
            (* ??? assert4* { i = b + 1 } ???*)
            let i = b + 1 in assert5* {I}
          end
        end else ()

        1 - if assert1 fails, then we have a real counterexample
            (invariant init doesn't hold)
        2 - if assert3 fails, then we have a false counterexample
            (invariant does not hold at beginning of execution)
        3 - if assert4 fails, then we have a real counterexample
            (invariant does not hold after iteration)
        (* ??? 4 - if assert2 fails, then we have a false counterexample
            (the value assigned to i is not compatible with for loop) *)
        5 - if assert5 fails, then we have a false counterexample
            (invariant does not hold for the execution to continue) *)
      try
  let a = big_int_of_value (get_pvs env pvs1) in
  let b = big_int_of_value (get_pvs env pvs2) in
  let le, suc = match dir with
    | To -> BigInt.le, BigInt.succ
    | DownTo -> BigInt.ge, BigInt.pred in
  (* assert1 *)
  if le a (suc b) then begin
    if rac then begin
      let env = bind_vs pvs.pv_vs (value ty_int (Vnum a)) env in
      check_terms (cntr_ctx "Loop invariant initialization" env) inv end;
    let env = Mvs.fold_left assign_written_vars env env.vsenv in
    let pvs_v = get_value pvs.pv_vs pvs.pv_ity
                  (Opt.get pvs.pv_vs.vs_name.id_loc) in
    let env = bind_vs pvs.pv_vs pvs_v env in
    let pvs_int = big_int_of_value pvs_v in
    if le a pvs_int && le pvs_int b then begin
      (* assert2 *)
      (try check_terms (cntr_ctx "ce satisfies invariant" env) inv with
       | Contr (_,t) ->
          printf "ce model does not satisfy loop invariant %a@."
            (Pp.print_option Pretty.print_loc) t.t_loc;
          raise (AbstractRACStuck (env,t.t_loc)));
      match eval_expr ~rac ~abs env e1 with
      | Normal _ ->
         let env =
           bind_vs pvs.pv_vs (value ty_int (Vnum (suc pvs_int))) env in
         (* assert3 *)
         if rac then
           check_terms (cntr_ctx "Loop invariant preservation" env) inv;
         raise (AbstractRACStuck (env,e.e_loc))
      | r -> r
      end
    else begin
      (* (\* assert4 *\)
       * if not (pvs_int = suc b) then begin
       *     printf "index is not in bounds %a@."
       *       (Pp.print_option Pretty.print_loc) e.e_loc;
       *     raise (AbstractRACStuck (env,e.e_loc)) end; *)
      (* assert5 *)
      let env = bind_vs pvs.pv_vs (value ty_int (Vnum (suc b))) env in
      (try check_terms (cntr_ctx "invariant holds after loop" env) inv with
       | Contr (_,t) ->
          printf "ce model does not satisfy loop invariant after \
                  loop %a@." (Pp.print_option Pretty.print_loc) t.t_loc;
          raise (AbstractRACStuck (env,t.t_loc)));
      Normal (value ty_unit Vvoid)
      end
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
      let descr = match kind with
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
      Debug.dprintf debug "@[<h>%tEVAL EXPR: PURE %a@]@." pp_indent print_term t;
      let t = compute_term env t in
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
  List.iter (Opt.iter visit_loc) (List.map (fun pv -> pv.pv_vs.vs_name.id_loc) arg_pvs);
  let arg_vs = List.map (get_pvs env) arg_pvs in
  Debug.dprintf debug "@[<h>%tExec call %a %a@]@."
    pp_indent print_rs rs Pp.(print_list space print_value) arg_vs;
  let env = multibind_pvs rs.rs_cty.cty_args arg_vs env in
  let oldies =
    let snapshot_oldie old_pv pv =
      Mvs.add old_pv.pv_vs (snapshot (Mvs.find pv.pv_vs env.vsenv)) in
    Mpv.fold snapshot_oldie rs.rs_cty.cty_oldies Mvs.empty in
  let env = {env with vsenv= Mvs.union (fun _ _ v -> Some v) env.vsenv oldies} in
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
                Debug.dprintf debug "@[<hv2>%tEXEC CALL %a: FUN %a@]@." pp_indent print_rs rs (pp_limited print_expr) body;
                let env' = multibind_pvs ce.c_cty.cty_args arg_vs env in
                eval_expr ~rac ~abs env' body
            | Cany ->
                Debug.dprintf debug  "@[<hv2>%tEXEC CALL %a: ANY@]@." pp_indent print_rs rs;
                eprintf "Cannot compute any function %a@." print_rs rs;
                raise CannotCompute
            | Cpur _ -> assert false (* TODO ? *) )
      | Builtin f ->
          Debug.dprintf debug "@[<hv2>%tEXEC CALL %a: BUILTIN@]@." pp_indent print_rs rs;
          Normal (f rs arg_vs)
      | Constructor _ ->
          Debug.dprintf debug "@[<hv2>%tEXEC CALL %a: CONSTRUCTOR@]@." pp_indent print_rs rs;
          let mt = List.fold_left2 ty_match Mtv.empty
              (List.map (fun pv -> pv.pv_vs.vs_ty) rs.rs_cty.cty_args) (List.map v_ty arg_vs) in
          let ty = ty_inst mt (ty_of_ity ity_result) in
          let fs = List.map field arg_vs in
          Normal (value ty (Vconstr (rs, fs)))
      | Projection _d -> (
        Debug.dprintf debug "@[<hv2>%tEXEC CALL %a: PROJECTION@]@." pp_indent print_rs rs;
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
          check_posts desc loc env v rs.rs_cty.cty_post
      | Excep (xs, v) ->
          let desc = cntr_desc "Exceptional postcondition" rs.rs_name in
          let posts = Mxs.find xs rs.rs_cty.cty_xpost in
          check_posts desc loc env v posts
      | _ -> () );
  res

(* GLOBAL EVALUATION *)

let init_real (emin, emax, prec) = Big_real.init emin emax prec

let make_global_env ?(model=default_model) env known =
  let add_glob _id d acc =
    match d.Pdecl.pd_node with
    | Pdecl.PDlet (LDvar (pv, _e)) ->
        (* TODO evaluate _e! *)
        let v = match model_value model pv with
          | Some v -> import_model_value env known pv.pv_ity  v
          | None -> default_value_of_type env known pv.pv_ity in
        Mvs.add pv.pv_vs v acc
    | _ -> acc in
  Mid.fold add_glob known Mvs.empty

let eval_global_expr ~rac ?rac_trans ?rac_prover env mod_known th_known locals e =
  get_builtin_progs env ;
  let vsenv = make_global_env env mod_known in
  let env = add_local_funs locals
      { (default_env env) with mod_known; th_known; vsenv; rac_trans; rac_prover } in
  let e_loc = Opt.get_def Loc.dummy_position e.e_loc in
  Mvs.iter (fun vs v -> register_used_value env e_loc vs v) vsenv;
  let res = eval_expr ~rac ~abs:false env e in
  res, vsenv

let eval_global_fundef ~rac ?rac_trans ?rac_prover env mod_known mod_theory locals body =
  try eval_global_expr ~rac ?rac_trans ?rac_prover env mod_known mod_theory locals body
  with CannotFind (l, s, n) ->
    eprintf "Cannot find %a.%s.%s" (Pp.print_list Pp.dot pp_print_string) l s n ;
    assert false

let eval_rs ~abs ?rac_trans ?rac_prover env mod_known th_known model (rs: rsymbol) =
  let get_value pv =
    match model_value model pv with
    | Some mv ->
        import_model_value env mod_known pv.pv_ity mv
    | None ->
        let v = default_value_of_type env mod_known pv.pv_ity in
        Debug.dprintf debug_rac "Missing value for parameter %a, continue with default value %a@."
          print_pv pv print_value v;
        v in
  let arg_vs = List.map get_value rs.rs_cty.cty_args in
  get_builtin_progs env ;
  let vsenv = make_global_env env ~model mod_known in
  let env = { (default_env env) with mod_known; th_known; vsenv; rac_trans; rac_prover; ce_model= model} in
  let env = multibind_pvs rs.rs_cty.cty_args arg_vs env in
  let e_loc = Opt.get_def Loc.dummy_position rs.rs_name.id_loc in
  Mvs.iter (fun vs v -> register_used_value env e_loc vs v) env.vsenv;
  let res = exec_call ~rac:true ~abs env rs rs.rs_cty.cty_args rs.rs_cty.cty_result in
  res, env

let check_equals loc env exec_value model_value =
  let ctx = cntr_ctx "Model value equality" ?trigger_loc:loc env in
  let vsenv, t1 = term_of_value env.env [] exec_value in
  let vsenv, t2 = term_of_value env.env vsenv model_value in
  try check_term ~vsenv ctx (t_equ t1 t2); true
  with Contr _ -> false

(* TODO do we need it? *)
let values_match env m =
  let aux vs v1 =
    match restore_pv vs with
    | exception Not_found -> true
    | pv -> match model_value m pv with
      | None -> true
      | Some mv2 ->
          let v2 = import_model_value env.env env.mod_known pv.pv_ity mv2 in
          check_equals pv.pv_vs.vs_name.id_loc env v1 v2 in
  Mvs.for_all aux env.vsenv

let warnings env model =
  if visited_all_model_locs model then [] else
    ["Warning: Model contains spurious values for \
      locations that were not encountered during RAC"] @
  if values_match env model then [] else
    ["Warning: RAC detected value divergence"]

let loc_contains_opt oloc1 oloc2 =
  match oloc1, oloc2 with
  | Some loc1, Some loc2 -> loc_contains loc1 loc2
  | _ -> false

let check_model_rs ?(abs=false) ?rac_trans ?rac_prover env pm model rs =
  let open Pmodule in
  let abs_msg = if abs then "abstract" else "concrete" in
  let abs_Msg = String.capitalize_ascii abs_msg in
  let kind = if abs then Abstract else Concrete in
  let vals_from_model env =
    let print_vals (loc,vs,v) = (loc,vs,asprintf "%a" print_value v) in
    List.rev_map print_vals !(env.used_values) in
  Debug.dprintf debug_rac "Validating model %s:@\n%a@." (abs_msg ^ "ly")
    (print_model ?me_name_trans:None ~print_attrs:false) model;
  reset_visited_locs (); iter_decl_locs visit_loc pm.mod_known;
  try
    let _, env = eval_rs ~abs ?rac_trans ?rac_prover env pm.mod_known pm.mod_theory.Theory.th_known model rs in
    let reason= abs_Msg ^ " RAC does not confirm the counter-example, no \
                           contradiction during execution" in
    { verdict= Dont_know; kind; reason; warnings= warnings env model;
      values= vals_from_model env}
  with
  | Contr (ctx, t) when loc_contains_opt (get_model_term_loc model) t.t_loc ->
     let reason= abs_Msg ^ " RAC confirms the counter-example" in
     { verdict= Good_model; kind; reason; warnings= warnings ctx.c_env model;
       values= vals_from_model ctx.c_env }
  | Contr (ctx, t) ->
     let reason = asprintf
                    "%s RAC found a contradiction at different location %a"
                    abs_Msg
                    (Pp.print_option_or_default "NO LOC" print_loc)
                    t.Term.t_loc in
     {verdict= Good_model; kind; reason; warnings= warnings ctx.c_env model;
       values= vals_from_model ctx.c_env}
  | CannotImportModelValue msg ->
     let reason = sprintf "%s RAC: Cannot import value from model: %s"
                    abs_Msg msg in
     {verdict= Dont_know; kind; reason; warnings= []; values= []}
  | CannotCompute ->
     (* TODO E.g., bad default value for parameter and cannot evaluate
        pre-condition *)
     let reason = abs_Msg ^ "RAC execution got stuck" in
     {verdict= Dont_know; kind; reason; warnings= []; values= []}
  | Failure msg ->
     (* E.g., cannot create default value for non-free type, cannot construct
         term for constructor that is not a function *)
     let reason = sprintf "%s RAC failure: %s" abs_Msg msg in
     {verdict= Dont_know; kind; reason; warnings= []; values= []}
  | AbstractRACStuck (env,l) ->
     let reason = asprintf "%s RAC, with the counterexample model cannot \
                            continue after %a@."
                    abs_Msg (Pp.print_option Pretty.print_loc) l in
     {verdict= Dont_know; kind; reason; warnings= [];
      values= vals_from_model env}

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

let check_model ?rac_trans ?rac_prover env pm m =
  match get_model_term_loc m with
  | None ->
      let reason = "No model term location" in
      [{verdict = Dont_know; kind = NotApplied; reason; warnings = [];
        values= []}]
  | Some loc ->
    if let f, _, _, _ = Loc.get loc in Sys.file_exists f then
      (* TODO deal with VCs from variable declarations and type declarations *)
      (* TODO deal with VCs from goal definitions *)
      match find_rs pm loc with
      | rs ->
         let c_res =
           check_model_rs ~abs:false ?rac_trans ?rac_prover env pm m rs in
         let a_res =
           check_model_rs ~abs:true ?rac_trans ?rac_prover env pm m rs in
         [c_res;a_res]
      | exception Not_found ->
          let reason = "No corresponding routine symbol found" in
          [{verdict = Dont_know; kind = NotApplied; reason; warnings = [];
            values= []}]
    else
      let reason = "Source file does not exist, cannot apply Loc.get_multiline" in
      [{verdict = Dont_know; kind = NotApplied; reason; warnings = [];
        values= []}]

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
