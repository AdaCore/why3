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

(* Test for declarations program constants with logical counterparts. These values are
   kept in the [rsenv] environment *)
let is_prog_constant d =
  let open Pdecl in
  match d.pd_node with
  | PDlet (LDsym (_, {c_cty= {Ity.cty_args= []}})) -> true
  | _ -> false

(* EXCEPTIONS *)

exception NoMatch
exception Undetermined
exception CannotCompute of {reason: string}
exception NotNum
exception CannotFind of (Env.pathname * string * string)

let cannot_compute f =
  kasprintf (fun reason -> raise (CannotCompute {reason})) f

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
    | Vundefined
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
    | Vundefined
  and field = Field of value ref

  open Util

  let rec compare_values v1 v2 =
    if v1.v_desc = Vundefined then
      cannot_compute "compare with undefined value of type %a" print_ty v1.v_ty;
    if v2.v_desc = Vundefined then
      cannot_compute "compare with undefined value of type %a" print_ty v2.v_ty;
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
    | Vundefined, _ | _, Vundefined -> assert false
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
let field_set (Field r) v = r := v

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
      print_term fmt t
  | Vundefined -> fprintf fmt "UNDEFINED"

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
    | Vfloat_mode _ | Vvoid | Vnum _ | Vundefined as vd -> vd in
  {v with v_desc}

and snapshot_field f =
  field (snapshot (field_get f))

let ls_undefined =
  let ty_a = ty_var (create_tvsymbol (id_fresh "a")) in
  create_fsymbol (id_fresh "undefined") [] ty_a

     (** Convert a value into a term. The first component of the result are additional bindings
    from closures, (roughly) sorted by strongly connected components. *)
let rec term_of_value env vsenv v : (vsymbol * term) list * term =
  match v.v_desc with
  | Vundefined ->
      (* TODO Replace ls_undefined by fs_any_function when branch
       * fun-lits-noptree is merged:
       * env, t_app fs_any_function [t_tuple []] v.v_ty *)
      vsenv, t_app ls_undefined [] (Some v.v_ty)
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

type rac_reduce_config = {
  rac_trans: Task.task Trans.tlist option;
  rac_prover: rac_prover option;
}

let rac_reduce_config ?trans:rac_trans ?prover:rac_prover () = {rac_trans; rac_prover}

type rac_config = {
  do_rac       : bool;
  rac_abstract : bool;
  rac_reduce   : rac_reduce_config;
  ce_model     : model;
  exec_log     : exec_log ref (* execution log, it includes values
                                 taken from the ce model *)
}

let rac_config ~do_rac ~abstract:rac_abstract ?reduce:rac_reduce
    ?model:(ce_model=Model_parser.default_model) () =
  let rac_reduce = match rac_reduce with Some r -> r | None -> rac_reduce_config () in
  {do_rac; rac_abstract; rac_reduce; ce_model; exec_log= ref empty_log}

type env =
  { mod_known   : Pdecl.known_map;
    th_known    : Decl.known_map;
    funenv      : Expr.cexp Mrs.t;
    vsenv       : value Mvs.t;
    rsenv       : value Mrs.t; (* global constants *)
    env         : Env.env;
    rac         : rac_config;
  }

let default_env env rac mod_known th_known =
  { mod_known; th_known; rac; env; funenv= Mrs.empty; vsenv= Mvs.empty; rsenv= Mrs.empty }

let register_used_value env loc id value =
  env.rac.exec_log := add_val_to_log id (asprintf "%a" print_value value) loc !(env.rac.exec_log)

let register_call env loc rs mvs kind =
  env.rac.exec_log := add_call_to_log rs mvs kind loc !(env.rac.exec_log)

let register_pure_call env loc ls kind =
  env.rac.exec_log := add_pure_call_to_log ls kind loc !(env.rac.exec_log)
let register_any_call env loc value =
    let v = (asprintf "%a" print_value value) in
    env.rac.exec_log := add_any_call_to_log v loc !(env.rac.exec_log)

let register_failure env loc reason mvs =
  env.rac.exec_log := add_failed_to_log reason mvs loc !(env.rac.exec_log)

let register_stucked env loc reason mvs =
  env.rac.exec_log := add_stucked_to_log reason mvs loc !(env.rac.exec_log)

let register_ended env loc =
  env.rac.exec_log := add_exec_ended_to_log loc !(env.rac.exec_log)

let register_loop env loc kind =
  env.rac.exec_log := add_exec_loop_to_log kind loc !(env.rac.exec_log)

let snapshot_env env = {env with vsenv= Mvs.map snapshot env.vsenv}

let add_local_funs locals env =
  let add acc (rs, ce) = Mrs.add rs ce acc in
  let funenv = List.fold_left add env.funenv locals in
  {env with funenv}

let bind_vs vs v env = {env with vsenv= Mvs.add vs v env.vsenv}
let bind_rs rs v env = {env with rsenv= Mrs.add rs v env.rsenv}
let bind_pvs ?register pv v_t env =
  let env = bind_vs pv.pv_vs v_t env in
  Opt.iter (fun r -> r pv.pv_vs.vs_name v_t) register;
  env
let multibind_pvs ?register l tl env =
  List.fold_left2 (fun env pv v -> bind_pvs ?register pv v env) env l tl

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
  | _ -> cannot_compute "Unknown float format: %d" float_format

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
  | Mlmpfr_wrapper.Not_Implemented ->
      cannot_compute "Mlmpfr wrapper: not implemented"
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
    | Mlmpfr_wrapper.Not_Implemented ->
        cannot_compute "Mlmpfr wrapper: not implemented"
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
      with e ->
        cannot_compute "Error making array: %a" Exn_printer.exn_printer e )
  | _ -> assert false

let exec_array_empty ts_array _ args =
  match args with
  | [{v_desc= Vconstr(_, [])}] ->
      (* we know by typing that the constructor
         will be the Tuple0 constructor *)
      let ty = ty_app ts_array [ty_var (tv_of_string "a")] in
      value ty (Varray [||])
  | _ -> assert false

let exec_array_get _ args =
  match args with
  | [{v_desc= Varray a}; {v_desc= Vnum i}] -> (
      try a.(BigInt.to_int i)
      with e ->
        cannot_compute "Error getting array: %a" Exn_printer.exn_printer e )
  | _ -> assert false

let exec_array_length _ args =
  match args with
  | [{v_desc= Varray a}] ->
      value ty_int (Vnum (BigInt.of_int (Array.length a)))
  | _ -> assert false

let exec_array_set _ args =
  match args with
  | [{v_desc= Varray a}; {v_desc= Vnum i}; v] -> (
      try
        a.(BigInt.to_int i) <- v;
        value ty_unit Vvoid
      with e ->
        cannot_compute "Error setting array: %a" Exn_printer.exn_printer e )
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

let get_vs env vs =
  try Mvs.find vs env.vsenv
  with Not_found ->
    ksprintf failwith "program variable %s not found in env"
      vs.vs_name.id_string

let get_pvs env pvs =
  get_vs env pvs.pv_vs

(* DEFAULTS *)

let is_array_its env its =
  let pm = Pmodule.read_module env ["array"] "Array" in
  let array_its = Pmodule.ns_find_its pm.Pmodule.mod_export ["array"] in
  its_equal its array_its

(* TODO Remove argument [env] after replacing Varray by model substitution *)
let rec default_value_of_type env known ity : value =
  let ty = ty_of_ity ity in
  match ity.ity_node with
  | Ityvar _ -> failwith "default_value_of_type: type variable"
  | Ityapp (ts, _, _) when its_equal ts its_int -> value ty (Vnum BigInt.zero)
  | Ityapp (ts, _, _) when its_equal ts its_real -> assert false (* TODO *)
  | Ityapp (ts, _, _) when its_equal ts its_bool -> value ty (Vbool false)
  | Ityapp (ts, _, _) when its_equal ts its_str -> value ty (Vstring "")
  (* | Ityapp(ts,_,_) when is_its_tuple ts -> assert false (* TODO *) *)
  | Ityreg {reg_its= its; reg_args= l1; reg_regs= l2}
  | Ityapp (its, l1, l2) ->
      if is_array_its env its then
        value ty (Varray (Array.init 0 (fun _ -> assert false)))
      else
        let itd = Pdecl.find_its_defn known its in
        match itd.Pdecl.itd_its.its_def with
        | Range r -> value ty (Vnum r.Number.ir_lower)
        | _ -> match itd.Pdecl.itd_constructors with
          | rs :: _ ->
              let subst = its_match_regs its l1 l2 in
              let ityl = List.map (fun pv -> pv.pv_ity) rs.rs_cty.cty_args in
              let tyl = List.map (ity_full_inst subst) ityl in
              let fl = List.map (fun ity -> field (default_value_of_type env known ity)) tyl in
              value ty (Vconstr (rs, fl))
          | [] ->
              (* if its.its_private then
               *   (\* There is no constructor so we can just invent a Vconstr,
               *      but we will have to axiomatize the corresponding term *\)
               *   let itys = List.map (fun rs -> (Opt.get rs.rs_field).pv_ity) itd.Pdecl.itd_fields in
               *   let fl = List.map (fun ity -> field (default_value_of_type env known ity)) itys in
               *   value ty (Vconstr (None, fl))
               * else *)
              value ty Vundefined

(* VALUE IMPORT *)

let get_model_value_by_loc model loc =
  let aux me = Opt.equal Loc.equal me.me_location (Some loc) in
  List.find_opt aux (get_model_elements model)

let get_model_value model name loc =
  let aux me =
    me.me_name.men_name = name &&
    Opt.equal Loc.equal me.me_location (Some loc) in
  Opt.map (fun me -> me.me_value)
    (List.find_opt aux (get_model_elements model))

let model_value model id =
  match id.id_loc with
  | None -> None
  | Some loc ->
      let name = Ident.get_model_trace_string ~name:id.id_string ~attrs:id.id_attrs in
      get_model_value model name loc

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
        let msg = asprintf "value of non-free type %a" print_ity ity in
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
              cannot_compute "Cannot import projection to type without constructor"
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

type cntr_ctx = {
  c_desc: string;
  c_trigger_loc: Loc.position option;
  c_env: env;
}

exception Contr of cntr_ctx * term

let cntr_desc_str str1 str2 = str1 ^ " of " ^ str2

let cntr_desc str id =
  asprintf "%s of %a" str print_decoded id.id_string

let cntr_title fmt (ctx, msg) =
  fprintf fmt "%s %s" ctx.c_desc msg

let report_cntr_head fmt (ctx, msg, term) =
  fprintf fmt "@[<v>%a%t@]" cntr_title (ctx, msg)
    (fun fmt ->
       match ctx.c_trigger_loc, term.t_loc with
       | Some t1, Some t2 ->
           fprintf fmt " at %a@,- Defined at %a" Pretty.print_loc' t1 Pretty.print_loc' t2
       | Some t, None | None, Some t ->
           fprintf fmt " at %a" Pretty.print_loc' t
       | None, None -> () )

let env_sep = Pp.comma

let pp_env pp_key pp_value fmt =
  let delims = Pp.nothing, Pp.nothing in
  fprintf fmt "%a" (pp_bindings ~delims ~sep:env_sep pp_key pp_value)

let report_cntr_body fmt (ctx, term) =
  let cmp_vs (vs1, _) (vs2, _) =
    String.compare vs1.vs_name.id_string vs2.vs_name.id_string in
  let mvs = t_freevars Mvs.empty term in
  fprintf fmt "@[<hv2>- Term: %a@]@," print_term term ;
  fprintf fmt "@[<hv2>- Variables: %a@]" (pp_env print_vs print_value)
    (List.sort cmp_vs
       (Mvs.bindings
          (Mvs.filter (fun vs _ -> Mvs.contains mvs vs) ctx.c_env.vsenv)))

let report_cntr fmt (ctx, msg, term) =
  fprintf fmt "@[<v>%a@," report_cntr_head (ctx, msg, term);
  report_cntr_body fmt (ctx, term);
  fprintf fmt "@]"

let cntr_ctx desc ?trigger_loc env =
  { c_desc= desc;
    c_trigger_loc= trigger_loc;
    c_env= snapshot_env env}

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

(* Add declarations for value bindings in [env.vsenv] *)
let bind_value env vs v (task, ls_mt, ls_mv) =
  let ls = create_fsymbol (id_clone vs.vs_name) [] v.v_ty in
  let ls_mt = ty_match ls_mt vs.vs_ty v.v_ty in
  let ls_mv = Mvs.add vs (fs_app ls [] v.v_ty) ls_mv in
  let vsenv, t = term_of_value env [] v in
  let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
  let t = t_ty_subst ls_mt ls_mv t in
  let defn = Decl.make_ls_defn ls [] t in
  let task = Task.add_logic_decl task [defn] in
  task, ls_mt, ls_mv

(* Create and open a formula `p t` for a non-formula term `t`, to use the reduction engine
   to evaluate `t` *)
let p = object
  val ls_p =
    let tv = create_tvsymbol (id_fresh "a") in
    create_psymbol (id_fresh "p") [ty_var tv]
  method decl =
    Decl.create_param_decl ls_p
  method create_app t =
    t_app ls_p [t] None
  method open_app t = match t with
    | {t_node= Tapp (ls, [t])} when ls_equal ls ls_p -> t
    | _ -> failwith "p#open_app"
end

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
    let decl = Decl.make_ls_defn ls vs_args t in
    let task = Task.add_logic_decl task [decl] in
    task, ls_mv
  with Exit -> task, ls_mv

let task_of_term ?(vsenv=[]) env t =
  let open Task in let open Decl in
  let task, ls_mt, ls_mv = None, Mtv.empty, Mvs.empty in
  let task = List.fold_left use_export task Theory.[builtin_theory; bool_theory; highord_theory] in
  let task = add_param_decl task ls_undefined in
  let lsenv =
    let aux1 rs v mls =
      match rs.rs_logic with
      | RLls ls -> Mls.add ls v mls
      | _ -> mls in
    Mrs.fold aux1 env.rsenv Mls.empty in
  (* Add known declarations *)
  let add_known _id decl task =
    match decl.d_node with
    | Dprop (Pgoal, _, _) -> task
    | Dprop (Plemma, prs, t) ->
        add_decl task (create_prop_decl Paxiom prs t)
    | Dparam ls when Mls.contains lsenv ls ->
        (* Take value from lsenv (i.e. env.rsenv) for declaration *)
        let vsenv, t = term_of_value env.env [] (Mls.find ls lsenv) in
        let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
        let t = t_ty_subst ls_mt ls_mv t in
        let decl = Decl.make_ls_defn ls [] t in
        add_decl task (create_logic_decl [decl])
    | _ -> add_decl task decl in
  let task = Mid.fold add_known env.th_known task in
  let task, ls_mv = Mrs.fold bind_fun env.funenv (task, ls_mv) in
  let task, ls_mt, ls_mv = List.fold_right bind_term vsenv (task, ls_mt, ls_mv) in
  let task, ls_mt, ls_mv = Mvs.fold (bind_value env.env) env.vsenv (task, ls_mt, ls_mv) in
  let t = t_ty_subst ls_mt ls_mv t in
  let task =
    if t.t_ty = None then (* Add a formula as goal directly ... *)
      let prs = create_prsymbol (id_fresh "goal") in
      add_prop_decl task Pgoal prs t
    else (* ... and wrap a non-formula in a call to a predicate with no definition *)
      let task = add_decl task p#decl in
      let prs = create_prsymbol (id_fresh "goal") in
      add_prop_decl task Pgoal prs (p#create_app t) in
  task, ls_mv

(* Parameters for binding universally quantified variables to a value from the CE model or the default value *)
let bind_univ_quant_vars_ce_model = false
let bind_univ_quant_vars_default = false

(* Get the value of a vsymbol from the CE-model, a default value *)
let get_value_for_quant_var env vs =
  match vs.vs_name.id_loc with
  | None -> None
  | Some loc ->
      let value =
        if bind_univ_quant_vars_ce_model then
          match get_model_value env.rac.ce_model vs.vs_name.id_string loc with
          | Some mv ->
              let v = import_model_value env.env env.mod_known (ity_of_ty vs.vs_ty) mv in
              Debug.dprintf debug_rac "Bind model value for all-quantified variable %a to %a@." print_vs vs print_value v;
              Some v
          | _ -> None
        else None in
      if value <> None then value else
      if bind_univ_quant_vars_default then (
        let v = default_value_of_type env.env env.mod_known (ity_of_ty vs.vs_ty) in
        Debug.dprintf debug_rac "Use default value for all-quantified variable %a: %a@." print_vs vs print_value v;
        Some v
      ) else None

(** When the task goal is [forall vs* . t], add declarations to the task that bind the
   variables [vs*] to concrete values (from the CE-model or default values), and make [t]
   the new goal. *)
let bind_univ_quant_vars env task =
  try match (Task.task_goal_fmla task).t_node with
    | Tquant (Tforall, tq) ->
        let vs, _, t = t_open_quant tq in
        let values = List.map (fun vs -> Opt.get_exn Exit (get_value_for_quant_var env vs)) vs in
        let _, task = Task.task_separate_goal task in
        let task, ls_mt, ls_mv = List.fold_right2 (bind_value env.env) vs values (task, Mtv.empty, Mvs.empty) in
        let prs = Decl.create_prsymbol (id_fresh "goal") in
        let t = t_ty_subst ls_mt ls_mv t in
        Task.add_prop_decl task Decl.Pgoal prs t
    | _ -> raise Exit
  with Exit -> task

let task_hd_equal t1 t2 = let open Task in let open Theory in let open Decl in
  (* Task.task_hd_equal is too strict: it requires physical equality between
     {t1,t2}.task_prev *)
  match t1.task_decl.td_node, t2.task_decl.td_node with
  | Decl {d_node = Dprop (Pgoal,p1,g1)}, Decl {d_node = Dprop (Pgoal,p2,g2)} ->
      pr_equal p1 p2 && t_equal_strict g1 g2
  | _ -> t1 == t2

(** Apply the (reduction) transformation and fill universally quantified variables
    in the head of the task by values from the CE model, recursively. *)
let rec trans_and_bind_quants env trans task =
  let task = bind_univ_quant_vars env task in
  let tasks = Trans.apply trans task in
  let task_unchanged = match tasks with
    | [task'] -> Opt.equal task_hd_equal task' task
    | _ -> false in
  if task_unchanged then
    tasks
  else
    List.flatten (List.map (trans_and_bind_quants env trans) tasks)

(** Compute the value of a term by using the (reduction) transformation *)
let compute_term env t =
  match env.rac.rac_reduce.rac_trans with
  | None -> t
  | Some trans ->
      let task, ls_mv = task_of_term env t in
      if t.t_ty = None then (* [t] is a formula *)
        match List.map Task.task_goal_fmla (trans_and_bind_quants env trans task) with
        | [] -> t_true
        | t :: ts -> List.fold_left t_and t ts
      else (* [t] is not a formula *)
        let t = match Trans.apply trans task with
          | [task] -> p#open_app (Task.task_goal_fmla task)
          | _ -> failwith "compute_term" in
        (* Free vsymbols in the original [t] have been substituted in by fresh lsymbols
           (actually: ls @ []) to bind them to declarations in the task. Now we have to
           reverse these substitution to ensures that the reduced term is valid in the
           original environment of [t]. *)
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

let check_term ?vsenv ctx t =
  Debug.dprintf debug_rac_check "@[<hv2>Check term: %a@]@." print_term t;
  let task, _ = task_of_term ?vsenv ctx.c_env t in
  let res = (* Try checking the term using computation first ... *)
    Opt.map (fun b -> Debug.dprintf debug_rac_check "Computed.@."; b)
      (Opt.bind ctx.c_env.rac.rac_reduce.rac_trans
         (fun trans -> check_term_compute ctx.c_env trans task)) in
  let res =
    if res = None then (* ... then try solving using a prover *)
      Opt.map (fun b -> Debug.dprintf debug_rac_check "Dispatched.@."; b)
        (Opt.bind ctx.c_env.rac.rac_reduce.rac_prover
           (fun rp -> check_term_dispatch rp task))
    else res in
  match res with
  | Some true ->
      Debug.dprintf debug_rac "%a@." report_cntr_head (ctx, "is ok", t)
  | Some false ->
      Debug.dprintf debug_rac "%a@." report_cntr_head (ctx, "has failed", t);
      raise (Contr (ctx, t))
  | None ->
      let msg = "cannot be evaluated" in
      if (Model_parser.is_model_empty ctx.c_env.rac.ce_model) then
        Debug.dprintf debug_rac "%a@." report_cntr (ctx, msg, t)
      else
        cannot_compute "%a" cntr_title (ctx, msg)

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

exception RACStuck of env * Loc.position option
(* The execution goes into RACStuck when a property that should be
   assumed is not satisfied. E.g. when executing a function, if the
   environment does not satisfy the precondition, the execution ends
   with RACStuck. *)

let value_of_free_vars env t =
  let get env vs = asprintf "%a" (Pp.print_option_or_default "(??)" print_value) (Mvs.find_opt vs env.vsenv) in
  t_v_fold (fun mvs vs -> Mvs.add vs (get env vs) mvs) Mvs.empty t

let check_assume_term ctx t =
  try check_term ctx t with Contr (ctx,t) ->
    let mvs = value_of_free_vars ctx.c_env t in
    register_stucked ctx.c_env t.t_loc ctx.c_desc mvs;
    raise (RACStuck (ctx.c_env, t.t_loc))

let check_assume_terms ctx tl =
  try check_terms ctx tl with Contr (ctx,t) ->
    let mvs = value_of_free_vars ctx.c_env t in
    register_stucked ctx.c_env t.t_loc ctx.c_desc mvs;
    raise (RACStuck (ctx.c_env, t.t_loc))

let check_assume_posts ctx v posts =
  try check_posts ctx.c_desc ctx.c_trigger_loc ctx.c_env v posts with Contr (ctx,t) ->
    let mvs = value_of_free_vars ctx.c_env t in
    register_stucked ctx.c_env t.t_loc ctx.c_desc mvs;
    raise (RACStuck (ctx.c_env,t.t_loc))

let check_term ?vsenv ctx t =
  try check_term ?vsenv ctx t with (Contr (ctx,t)) as e ->
    let mvs = value_of_free_vars ctx.c_env t in
    register_failure ctx.c_env t.t_loc ctx.c_desc mvs;
    raise e

let check_terms ctx tl =
  try check_terms ctx tl with (Contr (ctx,t)) as e ->
    let mvs = value_of_free_vars ctx.c_env t in
    register_failure ctx.c_env t.t_loc ctx.c_desc mvs;
    raise e

let check_posts desc loc env v posts =
  try check_posts desc loc env v posts with (Contr (ctx,t)) as e ->
    let mvs = value_of_free_vars ctx.c_env t in
    register_failure ctx.c_env t.t_loc ctx.c_desc mvs;
    raise e

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

let exec_pure ~loc env ls pvs =
  register_pure_call env loc ls ExecConcrete;
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

let get_and_register_value env ?def ?ity vs loc =
  let ity = match ity with None -> ity_of_ty vs.vs_ty | Some ity -> ity in
  let name = vs.vs_name.id_string in
  let value = match get_model_value env.rac.ce_model name loc with
    | Some v ->
       let v = import_model_value env.env env.mod_known ity v in
       Debug.dprintf debug_check_ce "@[<h>VALUE from ce-model for %a at %a: %a@]@."
         Ident.print_decoded name
         Pretty.print_loc' loc
         print_value v;
       v
    | None ->
       let v = match def with
         | None ->
            default_value_of_type env.env env.mod_known ity
         | Some v -> v in
       Debug.dprintf debug_check_ce "@[<h>VALUE for %s %a not in ce-model, taking \
                default %a@]@." name print_loc' loc print_value v;
       v
  in
  register_used_value env (Some loc) vs.vs_name value;
  value

let rec set_fields fs1 fs2 =
  let set_field f1 f2 =
    match (field_get f1).v_desc, (field_get f2).v_desc with
    | Vconstr (rs1, fs1), Vconstr (rs2, fs2) ->
        assert (rs_equal rs1 rs2);
        set_fields fs1 fs2
    | _ -> field_set f1 (field_get f2) in
  List.iter2 set_field fs1 fs2

let set_constr v1 v2 =
  (match v1.v_desc, v2.v_desc with
   | Vconstr (rs1, fs1), Vconstr (rs2, fs2) ->
       assert (rs_equal rs1 rs2);
       set_fields fs1 fs2;
   | _ -> failwith "set_constr")

let assign_written_vars ?(vars_map=Mpv.empty) wrt loc env vs =
  let pv = restore_pv vs in
  if pv_affected wrt pv then (
    Debug.dprintf debug "@[<h>%tVAR %a is written in loop %a@]@."
      pp_indent print_pv pv
      (Pp.print_option print_loc') pv.pv_vs.vs_name.id_loc;
    let pv = Mpv.find_def pv pv vars_map in
    let value = get_and_register_value ~ity:pv.pv_ity env pv.pv_vs loc in
    set_constr (get_vs env vs) value )

let rec eval_expr env e =
  Debug.dprintf debug "@[<h>%t%sEVAL EXPR: %a@]@." pp_indent
    (if env.rac.rac_abstract then "Abs. " else "")
    (pp_limited print_expr) e;
  let res = eval_expr' env e in
  Debug.dprintf debug "@[<h>%t -> %a@]@." pp_indent (print_result) res;
  res

(* abs = abstractly - do not execute loops and function calls - use
   instead invariants and function contracts to guide execution. *)
and eval_expr' env e =
  let loc_or_dummy = Opt.get_def Loc.dummy_position e.e_loc in
  match e.e_node with
  | Evar pvs ->
      let v = get_pvs env pvs in
      Debug.dprintf debug "[interp] reading var %s from env -> %a@\n"
        pvs.pv_vs.vs_name.id_string print_value v ;
      Normal v
  | Econst (Constant.ConstInt c) ->
      Normal (value (ty_of_ity e.e_ity) (Vnum (big_int_of_const c)))
  | Econst (Constant.ConstReal r) ->
      (* ConstReal can be float or real *)
      if ity_equal e.e_ity ity_real then
        let p, q = compute_fraction r.Number.rl_real in
        let sp, sq = BigInt.to_string p, BigInt.to_string q in
        try Normal (value ty_real (Vreal (real_from_fraction sp sq)))
        with Mlmpfr_wrapper.Not_Implemented ->
          cannot_compute "Mlmpfr wrapper: not implemented"
      else
        let c = Constant.ConstReal r in
        let s = Format.asprintf "%a" Constant.print_def c in
        Normal (value ty_real (Vfloat (make_from_str s)))
  | Econst (Constant.ConstStr s) -> Normal (value ty_str (Vstring s))
  | Eexec (ce, cty) -> begin
      (* TODO (When) do we have to check the contracts in cty? When ce <> Capp? *)
      (* check_terms (cntr_ctx "Exec precondition" env) cty.cty_pre; *)
      match ce.c_node with
      | Cpur (ls, pvs) ->
          Debug.dprintf debug "@[<h>%tEVAL EXPR: EXEC PURE %a %a@]@." pp_indent print_ls ls
            (Pp.print_list Pp.comma print_value) (List.map (get_pvs env) pvs);
          exec_pure ~loc:e.e_loc env ls pvs
      | Cfun e' ->
        Debug.dprintf debug "@[<h>%tEVAL EXPR EXEC FUN: %a@]@." pp_indent print_expr e';
        let add_free pv = Mvs.add pv.pv_vs (Mvs.find pv.pv_vs env.vsenv) in
        let cl = Spv.fold add_free ce.c_cty.cty_effect.eff_reads Mvs.empty in
        let mvs = Mvs.map (asprintf "%a" print_value) cl in
        ( match ce.c_cty.cty_args with
          | [] ->
             if env.rac.rac_abstract then begin
                 register_call env e.e_loc None mvs ExecAbstract;
                 exec_call_abstract ?loc:e.e_loc env ce.c_cty [] e.e_ity
               end
             else begin
                 register_call env e.e_loc None mvs ExecConcrete;
                 eval_expr env e'
               end
          | [arg] ->
              let match_free pv mt =
                let v = Mvs.find pv.pv_vs env.vsenv in
                ty_match mt pv.pv_vs.vs_ty v.v_ty in
              let mt = Spv.fold match_free cty.cty_effect.eff_reads Mtv.empty in
              let ty = ty_inst mt (ty_of_ity e.e_ity) in
              Normal (value ty (Vfun (cl, arg.pv_vs, e')))
          | _ -> failwith "many args for exec fun" (* TODO *) )
      | Cany ->
          let v =
            try match get_model_value_by_loc env.rac.ce_model (Opt.get_exn Exit e.e_loc) with
              | Some me -> import_model_value env.env env.mod_known e.e_ity me.me_value
              | None -> raise Exit
            with Exit ->
              let v = default_value_of_type env.env env.mod_known e.e_ity in
              let pp_loc fmt = function
                | Some loc -> fprintf fmt " at %a" Pretty.print_loc' loc
                | None -> () in
              Debug.dprintf debug "Take default value %a for any expression%a"
                print_value v pp_loc e.e_loc;
              v in
          register_any_call env e.e_loc v;
          (* register_used_value env e.e_loc Ident.(id_register (id_fresh ?loc:e.e_loc "ANY")) v; *)
          (* check_posts "Exec postcondition" e.e_loc env v cty.cty_post; *)
          Normal v
      | Capp (rs, pvsl) when Opt.map is_prog_constant (Mid.find_opt rs.rs_name env.mod_known) = Some true ->
          assert (cty.cty_args = [] && pvsl = []);
          let v = Mrs.find rs env.rsenv in
          (* check_posts "Exec postcondition" e.e_loc env v cty.cty_post; *)
          Normal v
      | Capp (rs, pvsl) ->
        if cty.cty_args <> [] then cannot_compute "Cannot compute partial function application";
        exec_call ?loc:e.e_loc env rs pvsl e.e_ity
    end
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
            | _ -> assert false in
          search_and_assign cstr.rs_cty.cty_args args)
        l ;
      Normal (value ty_unit Vvoid)
  | Elet (ld, e2) -> (
    match ld with
    | LDvar (pvs, e1) -> (
      match eval_expr env e1 with
      | Normal v ->
        let env = bind_pvs pvs v env in
        eval_expr env e2
      | r -> r )
    | LDsym (rs, ce) ->
        let env = {env with funenv= Mrs.add rs ce env.funenv} in
        eval_expr env e2
    | LDrec l ->
        let env' =
          { env with
            funenv=
              List.fold_left
                (fun acc d ->
                  Mrs.add d.rec_sym d.rec_fun (Mrs.add d.rec_rsym d.rec_fun acc))
                env.funenv l } in
        eval_expr env' e2 )
  | Eif (e1, e2, e3) -> (
    match eval_expr env e1 with
    | Normal v ->
      if is_true v then
        eval_expr env e2
      else if is_false v then
        eval_expr env e3
      else (
        eprintf "@[[Exec] Cannot decide condition of if: @[%a@]@]@." print_value v ;
        Irred e )
    | r -> r )
  | Ewhile (cond, inv, _var, e1) when env.rac.rac_abstract -> begin
      (* arbitrary execution of an iteartion taken from the counterexample

        while e1 do invariant {I} e2 done
        ~>
        assert1 {I};
        assign_written_vars_with_ce;
        assert2* {I};
        if e1 then (e2;assert3 {I}; abort* ) else ()

        1 - if assert1 fails, then we have a real couterexample
            (invariant init doesn't hold)
        2 - if assert2 fails, then we have a false counterexample
            (invariant does not hold at beginning of execution)
        3 - if assert3 fails, then we have a real counterexample
            (invariant does not hold after iteration)
        * stop the interpretation here - raise RACStuck *)
      (* assert1 *)
      register_loop env e.e_loc ExecAbstract;
      if env.rac.do_rac then
        check_terms (cntr_ctx "Loop invariant initialization" env) inv;
      List.iter (assign_written_vars e.e_effect.eff_writes loc_or_dummy env)
        (Mvs.keys env.vsenv);
      (* assert2 *)
      check_assume_terms (cntr_ctx "Assume loop invariant" env) inv;
      match eval_expr env cond with
      | Normal v ->
         if is_true v then begin
             match eval_expr env e1 with
             | Normal _ ->
                if env.rac.do_rac then
                  check_terms (cntr_ctx "Loop invariant preservation" env) inv;
                (* the execution cannot continue from here *)
                register_stucked env e.e_loc "Cannot continue after arbitrary iteration" Mvs.empty;
                raise (RACStuck (env,e.e_loc))
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
      register_loop env e.e_loc ExecConcrete;
      (* TODO variants *)
      if env.rac.do_rac then
        check_terms (cntr_ctx "Loop invariant initialization" env) inv ;
      match eval_expr env cond with
      | Normal v ->
          if is_true v then (
            match eval_expr env e1 with
            | Normal _ ->
                if env.rac.do_rac then
                  check_terms (cntr_ctx "Loop invariant preservation" env) inv ;
                eval_expr env e
            | r -> r )
          else if is_false v then
            Normal (value ty_unit Vvoid)
          else (
            eprintf "@[[Exec] Cannot decide condition of while: @[%a@]@]@."
              print_value v ;
            Irred e )
      | r -> r end
  | Efor (i, (pvs1, dir, pvs2), _ii, inv, e1) when env.rac.rac_abstract -> begin
      (* TODO what to do with _ii? *)
      (* arbitrary execution of an iteartion taken from the counterexample
        for i = e1 to e2 do invariant {I} e done
        ~>
        let a = eval_expr e1 in
        let b = eval_expr e2 in
        if a <= b + 1 then begin
          (let i = a in assert1 {I});
          assign_written_vars_with_ce;
          let i = get_and_register_value ~def:(b+1) i in
          if not (a <= i <= b + 1) then abort1;
          if a <= i <= b then begin
            assert2* { I };
            eval_expr e;
            let i = i + 1 in
            assert3 {I};
            abort2
          end else begin
            assert4* {I} (* i is already equal to 'b + 1' *)
          end
        end else ()

        1 - if assert1 fails, then we have a real counterexample
            (invariant init doesn't hold)
        2 - if assert2 fails, then we have a false counterexample
            (invariant does not hold at beginning of execution)
        3 - if assert3 fails, then we have a real counterexample
            (invariant does not hold after iteration)
        4 - if assert4 fails, then we have a false counterexample
            (invariant does not hold for the execution to continue)
        5 - abort1: we have a false counterexample
            (value assigned to i is not compatible with loop range)
        6 - abort2: we have a false counterexample
            (the abstract rac cannot continue from this state) *)
      register_loop env e.e_loc ExecAbstract;
      try
  let a = big_int_of_value (get_pvs env pvs1) in
  let b = big_int_of_value (get_pvs env pvs2) in
  let le, suc = match dir with
    | To -> BigInt.le, BigInt.succ
    | DownTo -> BigInt.ge, BigInt.pred in
  (* assert1 *)
  if le a (suc b) then begin
    if env.rac.do_rac then begin
      let env = bind_vs i.pv_vs (value ty_int (Vnum a)) env in
      check_terms (cntr_ctx "Loop invariant initialization" env) inv end;
    List.iter (assign_written_vars e.e_effect.eff_writes loc_or_dummy env)
      (Mvs.keys env.vsenv);
    let def = value ty_int (Vnum (suc b)) in
    let i_val = get_and_register_value ~def ~ity:i.pv_ity env i.pv_vs
                  (Opt.get i.pv_vs.vs_name.id_loc) in
    let env = bind_vs i.pv_vs i_val env in
    let i_val = big_int_of_value i_val in
    if not (le a i_val && le i_val (suc b)) then begin
        let msg = asprintf "Iterating variable not in bounds" in
        let mvs = Mvs.singleton i.pv_vs (BigInt.to_string i_val) in
        register_stucked env e.e_loc msg mvs;
        raise (RACStuck (env,e.e_loc)) end;
    if le a i_val && le i_val b then begin
      (* assert2 *)
      let ctx = cntr_ctx "Assume loop invariant" env in
      check_assume_terms ctx inv;
      match eval_expr env e1 with
      | Normal _ ->
         let env = bind_vs i.pv_vs (value ty_int (Vnum (suc i_val))) env in
         (* assert3 *)
         if env.rac.do_rac then
           check_terms (cntr_ctx "Loop invariant preservation" env) inv;
         register_stucked env e.e_loc
           "Cannot continue after arbitrary iteration" Mvs.empty;
         raise (RACStuck (env,e.e_loc))
      | r -> r
      end
    else begin
      (* assert4 *)
      (* i is already equal to b + 1 *)
      let ctx = cntr_ctx "Invariant after last iteration" env in
      check_assume_terms ctx inv;
      Normal (value ty_unit Vvoid)
      end
    end
  else Normal (value ty_unit Vvoid)
      with NotNum -> Irred e
    end
  | Efor (pvs, (pvs1, dir, pvs2), _i, inv, e1) -> (
    register_loop env e.e_loc ExecConcrete;
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
          match eval_expr env' e1 with
          | Normal _ ->
              if env.rac.do_rac then
                check_terms (cntr_ctx "Loop invariant preservation" env') inv ;
              iter (suc i)
          | r -> r
        else
          Normal (value ty_unit Vvoid) in
      ( if env.rac.do_rac then
          let env' = bind_vs pvs.pv_vs (value ty_int (Vnum a)) env in
          check_terms (cntr_ctx "Loop invariant initialization" env') inv ) ;
      iter a
    with NotNum -> Irred e )
  | Ematch (e0, ebl, el) -> (
      let r = eval_expr env e0 in
      match r with
      | Normal t -> (
          if ebl = [] then
            r
          else
            try exec_match env t ebl with Undetermined -> Irred e )
      | Excep (ex, t) -> (
        match Mxs.find ex el with
        | [], e2 ->
            (* assert (t = Vvoid); *)
            eval_expr env e2
        | [v], e2 ->
            let env' = bind_vs v.pv_vs t env in
            eval_expr env' e2
        | _ -> assert false (* TODO ? *)
        | exception Not_found -> r )
      | _ -> r )
  | Eraise (xs, e1) -> (
      let r = eval_expr env e1 in
      match r with Normal t -> Excep (xs, t) | _ -> r )
  | Eexn (_, e1) -> eval_expr env e1
  | Eassert (kind, t) ->
      if env.rac.do_rac then begin
          match kind with
          | Assert -> check_term (cntr_ctx "Assertion" env) t
          | Assume -> check_assume_term (cntr_ctx "Assumption" env) t
          | Check -> check_term (cntr_ctx "Check" env) t
        end;
      Normal (value ty_unit Vvoid)
  | Eghost e1 ->
      Debug.dprintf debug "@[<h>%tEVAL EXPR: GHOST %a@]@." pp_indent print_expr e1;
      (* TODO: do not eval ghost if no assertion check *)
      eval_expr env e1
  | Epure t ->
      Debug.dprintf debug "@[<h>%tEVAL EXPR: PURE %a@]@." pp_indent print_term t;
      let t = compute_term env t in
      Normal (value (Opt.get t.t_ty) (Vterm t))
  | Eabsurd ->
      eprintf "@[[Exec] unsupported expression: @[%a@]@]@."
        print_expr e ;
      Irred e

and exec_match env t ebl =
  let rec iter ebl =
    match ebl with
    | [] ->
        eprintf "[Exec] Pattern matching not exhaustive in evaluation@." ;
        assert false
    | (p, e) :: rem -> (
      try
        let env' = matching env t p.pp_pat in
        eval_expr env' e
      with NoMatch -> iter rem ) in
  iter ebl

and exec_call ?(main_function=false) ?loc env rs arg_pvs ity_result =
  let arg_vs = List.map (get_pvs env) arg_pvs in
  Debug.dprintf debug "@[<h>%tExec call %a %a@]@."
    pp_indent print_rs rs Pp.(print_list space print_value) arg_vs;
  let env = multibind_pvs rs.rs_cty.cty_args arg_vs env in
  let oldies =
    let snapshot_oldie old_pv pv =
      Mvs.add old_pv.pv_vs (snapshot (Mvs.find pv.pv_vs env.vsenv)) in
    Mpv.fold snapshot_oldie rs.rs_cty.cty_oldies Mvs.empty in
  let env = {env with vsenv= Mvs.union (fun _ _ v -> Some v)
                               env.vsenv oldies} in
  if env.rac.do_rac then begin
      let ctx = cntr_ctx (cntr_desc "Precondition" rs.rs_name) ?trigger_loc:loc env in
      if main_function then check_assume_terms ctx rs.rs_cty.cty_pre
      else check_terms ctx rs.rs_cty.cty_pre end;
  let can_interpret_abstractly =
    if rs_equal rs rs_func_app then false else
      match find_definition env rs with
      | LocalFunction _ -> true | _ -> false in
  let mvs = Mvs.of_list (List.combine
     (List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args)
     (List.map (asprintf "%a" print_value) arg_vs)) in
  if env.rac.rac_abstract && can_interpret_abstractly &&
       not main_function then begin
      register_call env loc (Some rs) mvs ExecAbstract;
      let rs_name,cty = rs.rs_name, rs.rs_cty in
      exec_call_abstract ?loc ~rs_name env cty arg_pvs ity_result
    end
  else begin
      register_call env loc (Some rs) mvs ExecConcrete;
      let res =
        if rs_equal rs rs_func_app then
          match arg_vs with
          | [{v_desc= Vfun (cl, arg, e)}; value] ->
             let env =
               {env with vsenv= Mvs.union (fun _ _ v -> Some v)
                                  env.vsenv cl} in
             let env = bind_vs arg value env in
             eval_expr env e
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
                  Debug.dprintf debug "@[<h>%tEXEC CALL %a: Capp %a]@."
                    pp_indent print_rs rs print_rs rs';
                  exec_call ?loc env rs' (pvl @ arg_pvs) ity_result
               | Cfun body ->
                  Debug.dprintf debug "@[<hv2>%tEXEC CALL %a: FUN/%d %a@]@."
                    pp_indent print_rs rs (List.length ce.c_cty.cty_args) (pp_limited print_expr) body;
                  let env' = multibind_pvs ce.c_cty.cty_args arg_vs env in
                  eval_expr env' body
               | Cany ->
                  Debug.dprintf debug  "@[<hv2>%tEXEC CALL %a: ANY@]@."
                    pp_indent print_rs rs;
                  cannot_compute "Cannot compute application of local any-function %a"
                    print_rs rs
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
                 | _ -> assert false in
               search cstr.rs_cty.cty_args args
            | _ -> assert false )
          | exception Not_found ->
             cannot_compute "[interp] cannot find definition of routine %s"
               rs.rs_name.id_string in
      ( match res with
        | Normal v ->
           let desc = cntr_desc "Postcondition" rs.rs_name in
           check_posts desc loc env v rs.rs_cty.cty_post
        | Excep (xs, v) ->
           let desc = cntr_desc "Exceptional postcondition" rs.rs_name in
           let posts = Mxs.find xs rs.rs_cty.cty_xpost in
           check_posts desc loc env v posts
        | _ -> () );
      res
    end

and exec_call_abstract ?loc ?rs_name env cty arg_pvs ity_result =
  (* let f (x1: ...) ... (xn: ...) = e
     ~>
     assert1 {f_pre};
     assign_written_vars_with_ce;
     assert2* {f_post};

     1 - if assert1 fails, then we have a real counterexample
     (precondition doesn't hold)
     2 - if assert2 fails, then we have a false counterexample
     (postcondition does not hold with the values obtained
     from the counterexample)
   *)
  let loc_or_dummy = Opt.get_def Loc.dummy_position loc in
  (* assert1 is already done above *)
  let res = match cty.cty_post with
    | p :: _ -> let (vs,_) = open_post p in
                id_clone vs.vs_name
    | _ -> id_fresh "result" in
  let res = create_vsymbol res (ty_of_ity ity_result) in
  let vars_map = Mpv.of_list (List.combine cty.cty_args arg_pvs) in
  let asgn_wrt = assign_written_vars ~vars_map
                   cty.cty_effect.eff_writes loc_or_dummy env in
  List.iter asgn_wrt (Mvs.keys env.vsenv);
  let res_v = get_and_register_value ~ity:ity_result env res
                loc_or_dummy in
  (* assert2 *)
  let msg = "Assume postcondition" in
  let msg = match rs_name with
    | None -> cntr_desc_str msg "anonymous function"
    | Some name -> cntr_desc msg name in
  let ctx = cntr_ctx msg ?trigger_loc:loc env in
  check_assume_posts ctx res_v cty.cty_post;
  Normal res_v

(* GLOBAL EVALUATION *)

let init_real (emin, emax, prec) = Big_real.init emin emax prec

let bind_globals ?(model=default_model) ?rs_main mod_known env =
  let get_value register id opt_e ity =
    match model_value model id with
    | Some mv ->
        let v = import_model_value env.env mod_known ity mv in
        register v; v
    | None -> match opt_e with
      | None ->
          let v = default_value_of_type env.env mod_known ity in
          register v; v
      | Some e ->
          let env = {env with rac= {env.rac with rac_abstract= false}} in
          match eval_expr env e with
          | Normal v -> v
          | Fun _ -> failwith "bind_globals: should be program constant, is function"
          | Excep _ -> cannot_compute "exception in initialization of global variable %a"
                         Ident.print_decoded id.id_string
          | Irred _ -> cannot_compute "initialization of global variable %a irreducible"
                         Ident.print_decoded id.id_string in
  let open Pdecl in
  let eval_global _ d env =
    match d.pd_node with
    | PDlet (LDvar (pv, e)) ->
        let register = register_used_value env pv.pv_vs.vs_name.id_loc pv.pv_vs.vs_name in
        let v = get_value register pv.pv_vs.vs_name (Some e) e.e_ity in
        bind_vs pv.pv_vs v env
    | PDlet (LDsym (rs, ce)) when is_prog_constant d -> (
        assert (ce.c_cty.cty_args = []);
        let register = register_used_value env rs.rs_name.id_loc rs.rs_name in
        let v = match ce.c_node with
          | Cany -> get_value register rs.rs_name None ce.c_cty.cty_result
          | Cfun e -> get_value register rs.rs_name (Some e) ce.c_cty.cty_result
          | _ -> failwith "eval_globals: program constant cexp" in
        check_assume_posts (cntr_ctx "Any postcondition" env) v ce.c_cty.cty_post;
        bind_rs rs v env )
    | _ -> env in
  let is_before id d (env, found_rs) =
    let found_rs_here = match d.pd_node with
      | PDlet (LDsym (rs, _)) -> Opt.equal rs_equal (Some rs) rs_main
      | PDlet (LDrec ds) -> List.exists (fun d -> Opt.equal rs_equal (Some d.rec_sym) rs_main) ds
      | _ -> false in
    let found_rs = found_rs || found_rs_here in
    let env = if found_rs then env else Mid.add id d env in
    env, found_rs in
  let mod_known, _ = Mid.fold is_before mod_known (Mid.empty, false) in
  Mid.fold eval_global mod_known env

let eval_global_fundef rac env mod_known th_known locals e =
  get_builtin_progs env ;
  let env = default_env env rac mod_known th_known in
  let env = bind_globals mod_known env in
  let env = add_local_funs locals env in
  let res = eval_expr env e in
  res, env.vsenv, env.rsenv

let eval_rs rac env mod_known th_known model (rs: rsymbol) =
  let get_value (pv: pvsymbol) =
    match model_value model pv.pv_vs.vs_name with
    | Some mv -> import_model_value env mod_known pv.pv_ity mv
    | None ->
        let v = default_value_of_type env mod_known pv.pv_ity in
        Debug.dprintf debug_rac "Missing value for parameter %a, continue with default value %a@."
          print_pv pv print_value v;
        v in
  get_builtin_progs env ;
  let env = default_env env rac mod_known th_known in
  let env = bind_globals ~model ~rs_main:rs mod_known env in
  let env = multibind_pvs ~register:(register_used_value env rs.rs_name.id_loc)
      rs.rs_cty.cty_args (List.map get_value rs.rs_cty.cty_args) env in
  let e_loc = Opt.get_def Loc.dummy_position rs.rs_name.id_loc in
  let res = exec_call ~main_function:true ~loc:e_loc env rs rs.rs_cty.cty_args rs.rs_cty.cty_result in
  register_ended env rs.rs_name.id_loc;
  res, env


let check_model_rs rac env pm model rs =
  let open Pmodule in
  let abs_msg = if rac.rac_abstract then "abstract" else "concrete" in
  let abs_Msg = String.capitalize_ascii abs_msg in
  Debug.dprintf debug_rac "Validating model %s:@\n%a@." (abs_msg ^ "ly")
    (print_model ?me_name_trans:None ~print_attrs:false) model;
  try
    let _, env = eval_rs rac env pm.mod_known pm.mod_theory.Theory.th_known model rs in
    let reason = sprintf "%s RAC does not confirm the counter-example, no \
                          contradiction during execution" abs_Msg in
    {Model_parser.verdict= Bad_model; reason; exec_log= !(env.rac.exec_log)}
  with
  | Contr (ctx, t) when t.t_loc <> None && Opt.equal Loc.equal t.t_loc (get_model_term_loc model) ->
      let reason = sprintf "%s RAC confirms the counter-example" abs_Msg in
      {Model_parser.verdict= Good_model; reason; exec_log= !(ctx.c_env.rac.exec_log)}
  | Contr (ctx, t) ->
      let reason = asprintf "%s RAC found a contradiction at different location %a"
          abs_Msg (Pp.print_option_or_default "NO LOC" print_loc') t.Term.t_loc in
      {Model_parser.verdict= Good_model; reason; exec_log= !(ctx.c_env.rac.exec_log)}
  | CannotImportModelValue msg ->
      let reason = sprintf "cannot import value from model: %s" msg in
      {Model_parser.verdict= Dont_know; reason; exec_log= empty_log}
  | CannotCompute r ->
      (* TODO E.g., bad default value for parameter and cannot evaluate
         pre-condition *)
      let reason = sprintf "RAC execution got stuck: %s" r.reason in
      {Model_parser.verdict= Dont_know; reason; exec_log= empty_log}
  | Failure msg ->
      (* E.g., cannot create default value for non-free type, cannot construct
          term for constructor that is not a function *)
      let reason = sprintf "failure: %s" msg in
      {Model_parser.verdict= Dont_know; reason; exec_log= empty_log}
  | RACStuck (env,l) ->
      let reason =
        asprintf "%s RAC, with the counterexample model cannot continue after %a"
          abs_Msg (Pp.print_option print_loc') l in
      {Model_parser.verdict= Bad_model; reason; exec_log= !(env.rac.exec_log)}

(** Identifies the rsymbol of the definition that contains the given position. **)
let find_rs pm loc =
  let open Pmodule in
  let open Pdecl in
  let rec find_in_list f = function
    | [] -> None
    | x :: xs -> match f x with
      | None -> find_in_list f xs
      | res -> res in
  let in_t t =
    Opt.equal Loc.equal (Some loc) t.t_loc ||
    t_any (fun t ->  Opt.equal Loc.equal (Some loc) t.t_loc) t in
  let in_cty cty =
    List.exists in_t cty.cty_pre ||
    List.exists in_t cty.cty_post ||
    Mxs.exists (fun _ -> List.exists in_t) cty.cty_xpost in
  let rec in_e e =
    Opt.equal Loc.equal (Some loc) e.e_loc ||
    match e.e_node with
    | Evar _ | Econst _ | Eassign _ -> false
    | Eexec (ce, cty) -> in_ce ce || in_cty cty
    | Elet (d, e) ->
        (match d with
         | LDvar (_, e') -> in_e e'
         | LDsym (rs, ce) -> in_cty rs.rs_cty || in_ce ce
         | LDrec defs -> List.exists (fun d -> in_ce d.rec_fun) defs) ||
        in_e e
    | Eif (e1, e2, e3) ->
        in_e e1 || in_e e2 || in_e e3
    | Ematch (e, regs, exns) ->
        in_e e || List.exists in_e (List.map snd regs) ||
        List.exists in_e (List.map snd (Mxs.values exns))
    | Ewhile (e1, invs, vars, e2) ->
        in_e e1 || List.exists in_t invs ||
        List.exists in_t (List.map fst vars) || in_e e2
    | Efor (_, _, _, invs, e) ->
        List.exists in_t invs || in_e e
    | Eraise (_, e)
    | Eexn (_, e) -> in_e e
    | Eassert (_, t) -> in_t t
    | Eghost e -> in_e e
    | Epure t -> in_t t
    | Eabsurd -> false
  and in_ce ce = match ce.c_node with
    | Cfun e -> in_e e
    | Capp (rs, _) -> in_cty rs.rs_cty
    | Cpur _ | Cany -> false in
  let rec find_pdecl pd =
    let maybe b r = if b then Some r else None in
    match pd.pd_node with
    | PDtype ds ->
        let in_tdef td =
          List.exists in_t td.itd_invariant ||
          List.exists in_e td.itd_witness in
        let find_td td = (* TODO *)
          if in_tdef td then Warning.emit "Can't check CE for VC from type definitions :(";
          None in
        find_in_list find_td ds
    | PDlet ld ->
        (match ld with
         | LDvar (_, e) -> (* TODO *)
             if in_e e then Warning.emit "Can't check CE for VC from variable definitions :(";
             None
         | LDsym (rs, ce) ->
             maybe (in_cty rs.rs_cty || in_ce ce) rs
         | LDrec defs ->
             let in_def d = in_cty d.rec_sym.rs_cty || in_ce d.rec_fun in
             find_in_list (fun d -> maybe (in_def d) d.rec_sym) defs)
    | PDexn _
    | PDpure -> None
  and find_mod_unit = function
    | Uuse _ | Uclone _ | Umeta _ -> None
    | Uscope (_, us) -> find_in_list find_mod_unit us
    | Udecl pd -> find_pdecl pd in
  find_in_list find_mod_unit pm.mod_units

let check_model reduce env pm model =
  match get_model_term_loc model with
  | None ->
      let reason = "model term has no location" in
      Cannot_check_model {reason}
  | Some loc ->
      (* TODO deal with VCs from goal definitions? *)
      if Loc.equal loc Loc.dummy_position then
        failwith ("Pinterp.check_model: the term of the CE model has a dummy "^
                  "location, it cannot be used to find the toplevel definition");
      match find_rs pm loc with
      | Some rs ->
          let check_model_rs ~abstract =
            let rac = rac_config ~do_rac:true ~abstract ~reduce ~model () in
            check_model_rs rac env pm model rs in
          let concrete = check_model_rs ~abstract:false in
          let abstract = check_model_rs ~abstract:true in
          Check_model_result {concrete; abstract}
      | None ->
          let reason = asprintf "no corresponding routine symbol found for %a" print_loc' loc in
          Cannot_check_model {reason}

let report_eval_result body fmt (res, vsenv, rsenv) =
  let print_envs fmt =
    pp_env print_vs print_value fmt (Mvs.bindings vsenv);
    (* if not (Mvs.is_empty vsenv) && not (Mrs.is_empty rsenv) then
     *   fprintf fmt "%a" env_sep ();
     * pp_env print_rs print_value fmt (Mrs.bindings rsenv) *)
    ignore rsenv
  in
  match res with
  | Normal _ ->
      fprintf fmt "@[<hov2>result:@ %a@ =@ %a@]@,"
        print_ity body.e_ity print_logic_result res;
      fprintf fmt "@[<hov2>globals:@ %t@]" print_envs
  | Excep _ ->
      fprintf fmt "@[<hov2>exceptional result:@ %a@]@,"
        print_logic_result res;
      fprintf fmt "@[<hov2>globals:@ %t@]" print_envs
  | Irred _ | Fun _ ->
      fprintf fmt "@[<hov2>Execution error: %a@]@," print_logic_result res ;
      fprintf fmt "@[globals:@ %t@]" print_envs

let report_cntr fmt (ctx, term) =
  report_cntr fmt (ctx, "has failed", term)
