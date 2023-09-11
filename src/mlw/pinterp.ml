(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Term
open Ident
open Ty
open Pretty
open Ity
open Expr
open Pinterp_core
open Value

let debug_rac_values =
  Debug.register_info_flag "rac:values"
    ~desc:"print values that are taken into account during interpretation"

let debug_disable_builtin_mach =
  Debug.register_flag "rac:execute_no_builtin_mach"
    ~desc:"don't register builtins for modules under stdlib/mach"

let pp_typed pp ty fmt x =
  fprintf fmt "%a: %a" pp x print_ty (ty x)
[@@warning "-32"]

let pp_mt fmt mt =
  pp_bindings print_tv print_ty fmt (Mtv.bindings mt)
[@@warning "-32"]

let pp_mv fmt mv =
  pp_bindings (pp_typed print_vs (fun vs -> vs.vs_ty))
    (pp_typed print_term t_type) fmt (Mvs.bindings mv)
[@@warning "-32"]

let pp_indent fmt =
  match Printexc.(backtrace_slots (get_callstack 100)) with
  | None -> ()
  | Some a ->
      let n = max 0 (Array.length a - 25) in
      let s = String.make (2 * n) ' ' in
      pp_print_string fmt s

(* Test for declarations program constants with logical counterparts. These values are
   kept in the [rsenv] environment *)
let is_prog_constant d =
  let open Pdecl in
  match d.pd_node with
  | PDlet (LDsym ({rs_logic = RLls _}, {c_cty={cty_args=[]}})) -> true
  | _ -> false

(******************************************************************************)
(*                              EXCEPTIONS                                    *)
(******************************************************************************)

exception NoMatch
exception Undetermined
exception NotNum
exception CannotFind of (Env.pathname * string * string)

(******************************************************************************)
(*                                 RESULT                                     *)
(******************************************************************************)

type ctx = {
  env          : Pinterp_core.env;
  giant_steps  : bool;
  do_rac       : bool;
  rac          : rac;
  oracle    : oracle;
  compute_term : compute_term;
  limits       : float option * int option;
  old_varl     : ((term * lsymbol option) list * value Mvs.t) option;
}
(** The evaluation context of Pinterp *)

let get_env ctx = ctx.env

let get_do_rac ctx = ctx.do_rac

let get_rac ctx = ctx.rac

let get_giant_steps ctx = ctx.giant_steps

let mk_empty_env = Pinterp_core.mk_empty_env

let mk_cntr_ctx ctx =
  Pinterp_core.mk_cntr_ctx ctx.env ~giant_steps:(Some ctx.giant_steps)

let mk_rac = Pinterp_core.mk_rac

let mk_ctx env ?timelimit ?steplimit ?(giant_steps=false)
    ?(do_rac=false) ?(rac=rac_dummy) ?(oracle=oracle_dummy)
    ?(compute_term=compute_term_dummy) () =
  {env; do_rac; compute_term; giant_steps; rac; oracle;
   limits=(timelimit, steplimit); old_varl= None }

let add_local_funs locals rdl ctx =
  let add acc (rs, ce) = Mrs.add rs (ce, rdl) acc in
  let funenv = List.fold_left add ctx.funenv locals in
  {ctx with funenv}

(******************************************************************************)
(*                                BUILTINS                                    *)
(******************************************************************************)

type _ vtype =
  | VTnum : BigInt.t vtype
  | VTfloat : big_float vtype
  | VTrnd : Mlmpfr_wrapper.mpfr_rnd_t vtype
  | VTreal : Big_real.real vtype
  | VTbool : bool vtype
  | VTstring : string vtype
  | VTunit : unit vtype
  | VTany : value vtype
  | VTarray : value array vtype
  | VTint : int vtype
  | VTfun : ('a vtype * 'b vtype) -> ('a -> 'b) vtype
  | VTlazy : 'a vtype -> (unit -> 'a) vtype

let get_arg : type t. t vtype -> _ -> _ -> t = fun t rs v ->
  match t, v.v_desc with
  | VTnum, Vnum x -> x
  | VTfloat, Vfloat x -> x
  | VTrnd, Vfloat_mode m -> m
  | VTreal, Vreal x -> x
  | VTbool, Vbool x -> x
  | VTstring, Vstring x -> x
  | VTunit, _ -> ()
  | VTany, _ -> v
  | VTarray, Varray v -> v
  | VTint, Vnum x -> BigInt.to_int x
  | _, Vundefined ->
      incomplete "an undefined argument was passed to builtin %a"
        Ident.print_decoded rs.rs_name.id_string
  | VTint, Vterm vt when (Opt.equal Ty.ty_equal vt.t_ty (Some Ty.ty_int)) ->
      begin match vt.t_node with
      | Tconst (Constant.ConstInt c) -> BigInt.to_int c.Number.il_int
      | _ -> assert false
      end
  | VTnum, Vterm vt when (Opt.equal Ty.ty_equal vt.t_ty (Some Ty.ty_int)) ->
      begin match vt.t_node with
      | Tconst (Constant.ConstInt c) -> c.Number.il_int
      | _ -> assert false
      end
  | VTbool, Vterm vt when (Opt.equal Ty.ty_equal vt.t_ty (Some Ty.ty_bool)) ->
      begin match vt.t_node with
      | Ttrue -> true
      | Tfalse -> false
      | _ -> assert false
      end
  | VTstring, Vterm vt when (Opt.equal Ty.ty_equal vt.t_ty (Some Ty.ty_str)) ->
      begin match vt.t_node with
      | Tconst (Constant.ConstStr s) -> s
      | _ -> assert false
      end
  | _ -> assert false

let rec eval : type t. t vtype -> t -> _ -> _ list -> _ = fun t f rs l ->
  match t with
  | VTnum -> range_value rs.rs_cty.cty_result f
  | VTfloat -> value ty_unit (Vfloat f) (* dummy type *)
  | VTreal -> real_value f
  | VTbool -> bool_value f
  | VTstring -> string_value f
  | VTunit -> unit_value
  | VTany -> f
  | VTint -> range_value rs.rs_cty.cty_result (BigInt.of_int f)
  | VTfun (i,o) ->
      begin match l with
      | x::l -> eval o (f (get_arg i rs x)) rs l
      | _ -> assert false
      end
  | VTlazy o -> eval o (f ()) rs l
  | _ -> assert false

let eval t f rs l =
  try
    eval t f rs l
  with
  | Division_by_zero -> incomplete "division by zero"
  | Failure "int_of_big_int" -> incomplete "index is out of bounds"
  | Invalid_argument "index out of bounds" -> incomplete "index is out of bounds"
  | Big_real.Undetermined -> incomplete "computation on real numbers is undetermined"
  | Mlmpfr_wrapper.Not_Implemented -> incomplete "mlmpfr not available"

let (^->) a b = VTfun (a, b)

let big_int_of_const i = i.Number.il_int
let big_int_of_value v =
  match v_desc v with
  | Vnum i -> i
  | Vterm {t_node = Tconst (Constant.ConstInt i)} -> big_int_of_const i
  | _ -> raise NotNum

let eval_int_op op ls l =
  eval (VTnum ^-> VTnum ^-> VTnum) op ls l

let eval_int_uop op ls l =
  eval (VTnum ^-> VTnum) op ls l

let eval_int_rel op ls l =
  eval (VTnum ^-> VTnum ^-> VTbool) op ls l

(* This initialize Mpfr for float32 behavior *)
let initialize_float32 () =
  let open Mlmpfr_wrapper in
  set_default_prec 24 ; set_emin (-148) ; set_emax 128

(* This initialize Mpfr for float64 behavior *)
let initialize_float64 () =
  let open Mlmpfr_wrapper in
  set_default_prec 53 ; set_emin (-1073) ; set_emax 1024

let use_float_format (float_format : int) =
  match float_format with
  | 32 -> initialize_float32 ()
  | 64 -> initialize_float64 ()
  | _ -> incomplete "float format is unknown: %d" float_format

let eval_float tys_result float_format arity op rs l =
  let ity_result = ity_of_ty (ty_app tys_result []) in
  use_float_format float_format ;
  let mode = ref Mlmpfr_wrapper.To_Nearest in
  let f = eval (VTrnd ^-> arity) (fun m -> mode := m; op m) rs l in
  match v_desc f with
  | Vfloat f -> float_value ity_result (Mlmpfr_wrapper.subnormalize ~rnd:!mode f)
  | _ -> assert false

let io_print_newline =
  eval (VTunit ^-> VTunit) print_newline

let io_print_int =
  eval (VTnum ^-> VTunit) (fun n -> print_string (BigInt.to_string n))

let io_print_string =
  eval (VTstring ^-> VTunit) print_string

let debug_print =
  eval (VTany ^-> VTunit) (fun v -> Format.eprintf "%a\n@?" print_value v)

let builtin_progs = Hrs.create 17

type builtin = Builtin_module of {
  path: string list;
  name: string;
  types: (string * (Pdecl.known_map -> itysymbol -> unit)) list;
  values: Pmodule.pmodule -> (string * (rsymbol -> value list -> value)) list;
}

let dummy_type (_:Pdecl.known_map) (_:itysymbol) = ()

let builtin path name values =
  Builtin_module {path; name; types=[]; values= fun _ -> values}

let builtin1t path name (type_name, type_def) values =
  let values = fun pm ->
    let its = Pmodule.(ns_find_its pm.mod_export [type_name]) in
    values its.its_ts in
  Builtin_module {path; name; types= [type_name, type_def]; values}

(* Described as a function so that this code is not executed outside of
   why3execute. *)

(** Description of modules *)
let built_in_modules () =
  let int_ops = [
    op_infix "+",      eval_int_op BigInt.add;
    (* defined as x+(-y)
       op_infix "-",   eval_int_op BigInt.sub; *)
    op_infix "*",      eval_int_op BigInt.mul;
    op_prefix "-",     eval_int_uop BigInt.minus;
    op_infix "=",      eval_int_rel BigInt.eq;
    op_infix "<",      eval_int_rel BigInt.lt;
    op_infix "<=",     eval_int_rel BigInt.le;
    op_infix ">",      eval_int_rel BigInt.gt;
    op_infix ">=",     eval_int_rel BigInt.ge;
  ] in
  let bounded_int_ops = int_ops @ [
    "of_int",          eval_int_uop (fun x -> x);
    "to_int",          eval_int_uop (fun x -> x);
    op_infix "-",      eval_int_op BigInt.sub;
    op_infix "/",      eval_int_op BigInt.computer_div;
    op_infix "%",      eval_int_op BigInt.computer_mod;
  ] in
  let open Mlmpfr_wrapper in
  let float_module tyb ~prec m = builtin1t ["ieee_float"] m ("t", dummy_type) (fun ts -> [
    "zeroF",           (fun _ _ -> value (ty_app ts []) (Vfloat (make_zero ~prec Positive)));
    "add",             eval_float ts tyb (VTfloat ^-> VTfloat ^-> VTfloat) (fun rnd -> add ~rnd ~prec);
    "sub",             eval_float ts tyb (VTfloat ^-> VTfloat ^-> VTfloat) (fun rnd -> sub ~rnd ~prec);
    "mul",             eval_float ts tyb (VTfloat ^-> VTfloat ^-> VTfloat) (fun rnd -> mul ~rnd ~prec);
    "div",             eval_float ts tyb (VTfloat ^-> VTfloat ^-> VTfloat) (fun rnd -> div ~rnd ~prec);
    "abs",             eval_float ts tyb (VTfloat ^-> VTfloat) (fun rnd -> abs ~rnd ~prec);
    "neg",             eval_float ts tyb (VTfloat ^-> VTfloat) (fun rnd -> neg ~rnd ~prec);
    "fma",             eval_float ts tyb (VTfloat ^-> VTfloat ^-> VTfloat ^-> VTfloat) (fun rnd -> fma ~rnd ~prec);
    "sqrt",            eval_float ts tyb (VTfloat ^-> VTfloat) (fun rnd -> sqrt ~rnd ~prec);
    "roundToIntegral", eval_float ts tyb (VTfloat ^-> VTfloat) (fun rnd -> rint ~rnd ~prec);
    (* Intentionnally removed from programs
       "min",          eval_float_minmax min;
       "max",          eval_float_minmax max; *)
    "le",              eval (VTfloat ^-> VTfloat ^-> VTbool) lessequal_p;
    "lt",              eval (VTfloat ^-> VTfloat ^-> VTbool) less_p;
    "eq",              eval (VTfloat ^-> VTfloat ^-> VTbool) equal_p;
    "is_zero",         eval (VTfloat ^-> VTbool) zero_p;
    "is_infinite",     eval (VTfloat ^-> VTbool) inf_p;
    "is_nan",          eval (VTfloat ^-> VTbool) nan_p;
    "is_positive",     eval (VTfloat ^-> VTbool) (fun s -> signbit s = Positive);
    "is_negative",     eval (VTfloat ^-> VTbool) (fun s -> signbit s = Negative);
  ]) in
  [
    builtin ["bool"] "Bool" [
      "True",          (fun _ _ -> bool_value true);
      "False",         (fun _ _ -> bool_value false);
    ];
    builtin ["debug"] "Debug" [
        "print", debug_print
      ];
    builtin ["int"] "Int" int_ops;
    builtin ["int"] "MinMax" [
      "min",           eval_int_op BigInt.min;
      "max",           eval_int_op BigInt.max
    ];
    builtin ["int"] "ComputerDivision" [
      "div",           eval_int_op BigInt.computer_div;
      "mod",           eval_int_op BigInt.computer_mod
    ];
    builtin ["int"] "EuclideanDivision" [
      "div",           eval_int_op BigInt.euclidean_div;
      "mod",           eval_int_op BigInt.euclidean_mod
    ];
    builtin1t ["ieee_float"] "RoundingMode" ("mode", dummy_type) (fun ts -> [
      "RNE",           (fun _ _ -> value (ty_app ts []) (Vfloat_mode To_Nearest));
      "RNA",           (fun _ _ -> value (ty_app ts []) (Vfloat_mode Away_From_Zero));
      "RTP",           (fun _ _ -> value (ty_app ts []) (Vfloat_mode Toward_Plus_Infinity));
      "RTN",           (fun _ _ -> value (ty_app ts []) (Vfloat_mode Toward_Minus_Infinity));
      "RTZ",           (fun _ _ -> value (ty_app ts []) (Vfloat_mode Toward_Zero));
    ]);
    builtin ["io"] "StdIO" [
        "print_int", io_print_int;
        "print_newline", io_print_newline;
        "print_string", io_print_string;
      ];
    builtin ["real"] "Real" [
      op_infix "=",  eval (VTreal ^-> VTreal ^-> VTbool) Big_real.eq;
      op_infix "<",  eval (VTreal ^-> VTreal ^-> VTbool) Big_real.lt;
      op_infix "<=", eval (VTreal ^-> VTreal ^-> VTbool) Big_real.le;
      op_prefix "-", eval (VTreal ^-> VTreal) Big_real.neg;
      op_infix "+",  eval (VTreal ^-> VTreal ^-> VTreal) Big_real.add;
      op_infix "*",  eval (VTreal ^-> VTreal ^-> VTreal) Big_real.mul;
      op_infix "/",  eval (VTreal ^-> VTreal ^-> VTreal) Big_real.div
    ];
    builtin ["real"] "Square" [
      "sqrt",        eval (VTreal ^-> VTreal) Big_real.sqrt
    ];
    builtin ["real"] "Trigonometry" [
      "pi",          eval (VTlazy VTreal) Big_real.pi
    ];
    builtin ["real"] "ExpLog" [
      "exp",         eval (VTreal ^-> VTreal) Big_real.exp;
      "log",         eval (VTreal ^-> VTreal) Big_real.log;
    ];
    builtin1t ["array"] "Array" ("array", dummy_type) (fun ts -> [
      "make", eval (VTint ^-> VTany ^-> VTany) (fun n def ->
              try
                let ty = ty_app ts [def.v_ty] in
                value ty (Varray (Array.make n def))
              with e -> incomplete "array could not be made: %a" Exn_printer.exn_printer e);
      "empty", eval (VTunit ^-> VTany) (fun () ->
              let ty = ty_app ts [ty_var (tv_of_string "a")] in
              value ty (Varray [||]));
      "length", eval (VTarray ^-> VTint) (fun a -> Array.length a);
      op_get "", eval (VTarray ^-> VTint ^-> VTany) (fun a i -> a.(i));
      op_set "", eval (VTarray ^-> VTint ^-> VTany ^-> VTunit) (fun a i v -> a.(i) <- v);
        ]);
    float_module 32 ~prec:24 "Float32";
    float_module 64 ~prec:53 "Float64";
  ] @ if Debug.test_flag debug_disable_builtin_mach then [] else [
    builtin ["mach"; "int"] "Byte" bounded_int_ops;
    builtin ["mach"; "int"] "Int31" bounded_int_ops;
    builtin ["mach"; "int"] "Int63" bounded_int_ops;
  ]

let add_builtin_mo env (Builtin_module {path; name; types; values}) =
  let open Pmodule in
  let pm = read_module env path name in
  List.iter
    (fun (id, r) ->
      let its =
        try Pmodule.ns_find_its pm.mod_export [id]
        with Not_found -> raise (CannotFind (path, name, id)) in
      r pm.mod_known its)
    types ;
  List.iter
    (fun (id, f) ->
      let ps =
        try Pmodule.ns_find_rs pm.mod_export [id]
        with Not_found -> raise (CannotFind (path, name, id)) in
      Hrs.add builtin_progs ps f)
    (values pm)

let get_builtin_progs env =
  List.iter (add_builtin_mo env) (built_in_modules ())

(******************************************************************************)
(*                           ROUTINE DEFINITIONS                              *)
(******************************************************************************)

type routine_defn =
  | Builtin of (rsymbol -> value list -> value)
  | LocalFunction of (rsymbol * cexp) list * (cexp * rec_defn list option)
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
      if List.mem rs d.Pdecl.itd_constructors then
        Constructor d
      else if List.mem rs d.Pdecl.itd_fields then
        Projection d
      else
        find_constr_or_proj rem rs

let find_global_definition kn rs =
  match (Mid.find rs.rs_name kn).Pdecl.pd_node with
  | Pdecl.PDtype dl -> find_constr_or_proj dl rs
  | Pdecl.PDlet (LDvar _) -> raise Not_found
  | Pdecl.PDlet (LDsym (_, ce)) -> LocalFunction ([], (ce, None))
  | Pdecl.PDlet (LDrec dl) ->
      let locs = List.map (fun d -> d.rec_rsym, d.rec_fun) dl in
      LocalFunction (locs, (find_def rs dl, Some dl))
  | Pdecl.PDexn _ -> raise Not_found
  | Pdecl.PDpure -> raise Not_found

let find_definition env (rs: rsymbol) =
  (* then try if it is a built-in symbol *)
  try Builtin (Hrs.find builtin_progs rs) with Not_found ->
  (* then try if it is a local function *)
  try LocalFunction ([], Mrs.find rs env.funenv) with Not_found ->
  (* else look for a global function *)
  find_global_definition env.pmodule.Pmodule.mod_known rs

(******************************************************************************)
(*                           EXPRESSION EVALUATION                            *)
(******************************************************************************)

(* Assuming the real is given in pow2 and pow5 *)
let compute_fraction {Number.rv_sig= i; rv_pow2= p2; rv_pow5= p5} =
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
      | Vconstr (Some {rs_logic= RLls ls2}, _, tl) ->
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

(* Many ways to say yes... *)
let is_true v = match v.v_desc with
  | Vbool true | Vterm {t_node= Ttrue} -> true
  | Vterm t when t_equal t t_bool_true -> true
  | Vconstr (Some rs, [], []) when rs_equal rs rs_true -> true
  | _ -> false

(* ...and no *)
let is_false v = match v.v_desc with
  | Vbool false | Vterm {t_node= Tfalse} -> true
  | Vterm t when t_equal t t_bool_false -> true
  | Vconstr (Some rs, [], []) when rs_equal rs rs_false -> true
  | _ -> false

let fix_boolean_term t =
  if t_equal t t_true then t_bool_true else
  if t_equal t t_false then t_bool_false else t

type result =
  | Normal of Value.value
  | Excep of xsymbol * value
  | Irred of expr

let print_logic_result fmt r =
  match r with
  | Normal v -> fprintf fmt "@[%a@]" print_value v
  | Excep (x, v) ->
      fprintf fmt "@[exception %s(@[%a@])@]" x.xs_name.id_string print_value v
  | Irred e -> fprintf fmt "@[Cannot execute expression@ @[%a@]@]" print_expr e

let
  exec_pure ~loc ctx ls pvs =
  register_pure_call ctx.env loc ls Log.Exec_normal;
  if ls_equal ls ps_equ then
    (* TODO (?) Add more builtin logical symbols *)
    let pv1, pv2 = match pvs with [pv1; pv2] -> pv1, pv2 | _ -> assert false in
    let v1 = Mvs.find pv1.pv_vs ctx.env.vsenv and v2 = Mvs.find pv2.pv_vs ctx.env.vsenv in
    Normal (value ty_bool (Vbool (compare_values v1 v2 = 0)))
  else if ls_equal ls fs_func_app then
    failwith "Pure function application not yet implemented"
  else
    match Decl.find_logic_definition ctx.env.pmodule.Pmodule.mod_theory.Theory.th_known ls with
    | Some defn ->
        let vs, t = Decl.open_ls_defn defn in
        let args = List.map (get_pvs ctx.env) pvs in
        let vsenv = List.fold_right2 Mvs.add vs args ctx.env.vsenv in
        let t = ctx.compute_term {ctx.env with vsenv} t in
        (* TODO A variable x binding the result of exec pure are used as (x = True) in
           subsequent terms, so we map true/false to True/False here. Is this reasonable? *)
        let t = fix_boolean_term t in
        Normal (value (Opt.get_def ty_bool t.t_ty) (Vterm t))
    | None ->
        kasprintf failwith "No logic definition for %a" print_ls ls

let pp_limited ?(n=100) pp fmt x =
  let s = asprintf "%a" pp x in
  let s = String.map (function '\n' -> ' ' | c -> c) s in
  let s = String.(if length s > n then sub s 0 (min n (length s)) ^ "..." else s) in
  pp_print_string fmt s

let print_result fmt = function
  | Normal v -> print_value fmt v
  | Excep (xs, v) -> fprintf fmt "EXC %a: %a" print_xs xs print_value v
  | Irred e -> fprintf fmt "IRRED: %a" (pp_limited print_expr) e

(******************************************************************************)
(*                                VALUE OF TERM                               *)
(******************************************************************************)

let value_of_constant ty c =
  let open Constant in
  match c with
  | ConstInt i -> value ty (Vnum i.Number.il_int)
  | ConstStr s -> string_value s
  | ConstReal _ -> failwith "not implemented: value_of_term real"

let value_of_term ctx t =
  let rec aux t =
    let ty = Opt.get_exn Exit t.t_ty in
    match t.t_node with
    | Ttrue -> bool_value true
    | Tfalse -> bool_value false
    | Tconst c -> value_of_constant ty c
    | Tapp (ls, ts) when ls.ls_constr > 0 ->
        let rs = try restore_rs ls with Not_found -> raise Exit in
        let fs = match (ity_of_ty ty).ity_node with
          | Ityapp (its, _, _) | Ityreg {reg_its= its} ->
              let defn = Pdecl.find_its_defn ctx.env.pmodule.Pmodule.mod_known its in
              defn.Pdecl.itd_fields
          | _ -> raise Exit in
        let vs = List.map aux ts in
        let res = value ty (Vconstr (Some rs, fs, List.map field vs)) in
        if ctx.do_rac then
          check_type_invs ctx.rac ~giant_steps:ctx.giant_steps ctx.env
            (ity_of_ty ty) res;
        res
    | _ -> raise Exit in
  try Some (aux t) with Exit -> None

(* Find a postcondition of the form [ensures { result = t (/\ ...) }],
   compute_fraction [t], and return it as a value. *)
let try_eval_ensures ctx posts =
  let rec loop vs = function
    | {t_node= Tapp (ls, [{t_node= Tvar vs'}; t])}
      when ls_equal ls ps_equ && vs_equal vs vs' ->
        let t = ctx.compute_term ctx.env t in
        value_of_term ctx t
    | {t_node= Tbinop (Tand, t1, t2)} ->
        let res = loop vs t1 in
        if res <> None then res else loop vs t2
    | _ -> None in
  let is_ensures_result = function
    | {t_node= Teps tb} -> let vs, t = t_open_bound tb in loop vs t
    | _ -> None in
  try Some (Lists.first is_ensures_result posts)
  with Not_found | Incomplete _ -> None

(******************************************************************************)
(*            GET AND REGISTER VALUES FOR VARIABLES AND CALL RESULTS          *)
(******************************************************************************)

let is_ignore_id id = Strings.has_prefix "_" id.id_string

(** A partial value generator with a string as a description. *)
type value_gen = string * (unit -> value option)

(** [get_value gens] takes a list of generators [gen] and returns the
    description and value for the first generator whose result is not [None]. *)
let get_value : value_gen list -> string * value =
  let aux (s, gen) = match gen () with Some v -> Some (s, v) | None -> None in
  Lists.first aux

(** Generate a value by querying the model for a variable. *)
let gen_model_variable ?check ({giant_steps} as ctx) ?loc id ity : value_gen =
  "value from model", fun () ->
    Opt.apply () check id;
    try
      let check = check_assume_type_invs ctx.rac ?loc ~giant_steps ctx.env in
      ctx.oracle.for_variable ~loc ~check ctx.env id ity
    with Stuck _ when is_ignore_id id -> None

(** Generate a value by querying the model for a result *)
let gen_model_result ({giant_steps} as ctx) (oid:expr_id option) loc ity : value_gen =
  "value from model", fun () ->
    if ity_equal ity ity_unit
    then Some unit_value
    else
      let res = ctx.oracle.for_result ctx.env ~call_id:oid ~loc ity in
      Opt.iter (check_assume_type_invs ctx.rac ~loc ~giant_steps ctx.env ity) res;
      res

(** Generator for a default value *)
let gen_default ity def : value_gen =
  "default value", fun () ->
    if ity_equal ity ity_unit
    then Some unit_value
    else def

(** Generate a value by computing the postcondition *)
let gen_from_post env posts : value_gen =
  "value computed from postcondition", fun () ->
    try_eval_ensures env posts

(** Generator for the type default value, when [posts] are not none or [really]
    is true. *)
let gen_type_default ~really ?posts ctx ity : value_gen =
  "type default value", fun () ->
    if posts = None && not really then None else
    let v = default_value_of_type ctx.env ity in
    try
      let cntr_ctx = mk_cntr_ctx ctx ~desc:"type default value" Vc.expl_post in
      Opt.iter (check_posts ctx.rac cntr_ctx v) posts;
      Some v
    with Fail _ | Incomplete _ -> None

(** Generate a value by evaluating an optional expression, if that is not [None]
   *)
let gen_eval_expr cnf exec_expr id oexp =
  "RHS evaluated", fun () ->
    match oexp with
    | None -> None
    | Some e ->
        let cnf' = {cnf with giant_steps= false} in
        register_const_init cnf.env id.id_loc id;
        match exec_expr cnf' e with
        | Normal v -> Some v
        | Excep _ ->
            incomplete "initialization of global variable `%a` raised an \
                            exception" print_decoded id.id_string
        | Irred _ -> None

(** Get a value from a list of generators and print debugging messages or fail,
    if no value is generated. *)
let get_value' ctx_desc oloc gens =
  let desc, value = try get_value gens with Not_found ->
    Debug.dprintf debug_rac_values "@[<h>No value for %s at %a@]@." ctx_desc
      (Pp.print_option_or_default "NO LOC" Loc.pp_position) oloc;
    incomplete "missing value for %s" ctx_desc
      (Pp.print_option_or_default "NO LOC" Loc.pp_position) oloc in
  Debug.dprintf debug_rac_values "@[<h>%s for %s at %a: %a@]@."
    (String.capitalize_ascii desc) ctx_desc
    (Pp.print_option_or_default "NO LOC" Loc.pp_position) oloc print_value value;
  value

let get_and_register_variable ctx ?def ?loc id ity =
  let ctx_desc = asprintf "variable `%a`%t" print_decoded id.id_string
      (fun fmt -> match loc with
         | Some loc -> fprintf fmt " at %a" Loc.pp_position loc
         | None -> ()) in
  let oloc = if loc <> None then loc else id.id_loc in
  let gens = [
    gen_model_variable ctx ?loc id ity;
    gen_default ity def;
    gen_type_default ~really:true (* (is_ignore_id id) *) ctx ity;
  ] in
  let value = get_value' ctx_desc oloc gens in
  register_used_value ctx.env oloc id value;
  value

let get_and_register_result ?def ?rs ctx posts (oid:expr_id option) loc ity =
  let ctx_desc = asprintf "return value of call%t at %a"
      (fun fmt -> Opt.iter (fprintf fmt " to %a" print_rs) rs)
      Loc.pp_position loc
  in
  let gens = [
    gen_model_result ctx oid loc ity;
    gen_default ity def;
    gen_from_post ctx posts;
    gen_type_default ~really:true ~posts ctx ity;
  ] in
  let value = get_value' ctx_desc (Some loc) gens in
  register_res_value ctx.env loc rs value;
  value

let get_and_register_param ctx id ity =
  let ctx_desc = asprintf "parameter `%a`" print_decoded id.id_string in
  let gens = [
    gen_model_variable ctx id ity;
    gen_type_default ~really:true (* (is_ignore_id id) *) ctx ity;
  ] in
  let value = get_value' ctx_desc id.id_loc gens in
  register_used_value ctx.env id.id_loc id value;
  value

(* For globals, RAC_Stuck exceptions that indicate invalid model values are
   referred lazily until their value is required in RAC or in the task. *)
let get_and_register_global check_model_variable ctx exec_expr id oexp post ity =
  let ctx_desc = asprintf "global `%a`" print_decoded id.id_string in
  let gens = [
    gen_model_variable ~check:check_model_variable ctx id ity;
    gen_eval_expr ctx exec_expr id oexp;
  ] in
  try
    let value = get_value' ctx_desc id.id_loc gens in
    register_used_value ctx.env id.id_loc id value;
    if ctx.do_rac then (
      let desc = asprintf "of global variable `%a`" print_decoded id.id_string in
      let cntr_ctx = mk_cntr_ctx ctx ~desc Vc.expl_post in
      check_assume_posts ctx.rac cntr_ctx value post );
    lazy value
  with Incomplete _ | Stuck _ as e ->
    (* We should not need to capture these exceptions if this function was not
       executed on logic constants and logic functions. *)
    lazy Printexc.(raise_with_backtrace e (get_raw_backtrace ()))

(******************************************************************************)
(*                              SIDE EFFECTS                                  *)
(******************************************************************************)

let rec set_fields fs1 fs2 =
  let set_field f1 f2 =
    match (field_get f1).v_desc, (field_get f2).v_desc with
    | Vconstr (Some rs1, _, fs1), Vconstr (Some rs2, _, fs2) ->
        assert (rs_equal rs1 rs2);
        set_fields fs1 fs2
    | _ -> field_set f1 (field_get f2) in
  List.iter2 set_field fs1 fs2

let set_constr v1 v2 =
  match v1.v_desc, v2.v_desc with
  | Vconstr (Some rs1, _, fs1), Vconstr (Some rs2, _, fs2) ->
      assert (rs_equal rs1 rs2);
      set_fields fs1 fs2;
  | Vconstr (_, _, fs1), Vconstr (_, _, fs2) ->
      set_fields fs1 fs2;
  | _ -> failwith "set_constr"

let assign_written_vars ?(vars_map=Mpv.empty) wrt loc ctx vs =
  let pv = restore_pv vs in
  if pv_affected wrt pv then (
    Debug.dprintf debug_trace_exec "@[<h>%tVAR %a is written in loop/function call %a@]@."
      pp_indent print_pv pv
      (Pp.print_option Loc.pp_position) pv.pv_vs.vs_name.id_loc;
    let pv = Mpv.find_def pv pv vars_map in
    let value = get_and_register_variable ctx ~loc pv.pv_vs.vs_name pv.pv_ity in
    set_constr (get_vs ctx.env vs) value )

(******************************************************************************)
(*                           TIME AND STEP LIMITS                             *)
(******************************************************************************)

let check_timelimit time0 = function
  | None -> ()
  | Some timelimit ->
      if Sys.time () -. time0 >= timelimit then
        incomplete "RAC timelimit reached"

let check_steplimit (steps: int) = function
  | None -> ()
  | Some steplimit ->
      if steps >= steplimit then
        incomplete "RAC steplimit reached"

(* State for checking limits (start time and current step count) *)
let limits_state = ref None

let check_limits (timelimit, steplimit) =
  match !limits_state with
  | None -> failwith "check_limits: called outside with_limits"
  | Some (time0, steps) ->
      incr steps;
      check_timelimit time0 timelimit;
      check_steplimit !steps steplimit

let set_limits () =
  if !limits_state <> None then failwith "set_limits: limits already set";
  limits_state := Some (Sys.time (), ref 0)

let reset_limits () =
  if !limits_state = None then failwith "reset_limits: limits not set";
  Debug.dprintf debug_trace_exec "Finished after %d steps@."
    !(snd (Opt.get !limits_state));
  limits_state := None

let with_limits f =
  set_limits ();
  match f () with
  | res ->
      reset_limits (); res
  | exception e ->
      reset_limits (); Printexc.(raise_with_backtrace e (get_raw_backtrace ()))

(******************************************************************************)
(*                          EXPRESSION EVALUATION                             *)
(******************************************************************************)

let find_rec_defn rs env =
  let open Pdecl in
  match Mrs.find rs env.funenv with
  | (_, rds) -> rds
  | exception Not_found ->
      match (Mid.find rs.rs_name env.pmodule.Pmodule.mod_known).pd_node with
      | PDlet (LDrec rds) -> Some rds
      | _ -> None


let add_premises ?post_res ?(vsenv=[]) ts env =
  let match_free_var env vs _ (vsenv, mt, mv) =
    let v = get_vs env vs in
    let vsenv, t = term_of_value env vsenv v in
    let ty = ty_inst mt (v_ty v) in
    let vs' = create_vsymbol (id_clone vs.vs_name) ty in
    let mt = ty_match mt (ty_inst mt vs.vs_ty) ty in
    let mv = Mvs.add vs (vs', t) mv in
    vsenv, mt, mv in
  let bind_vs mt mv (vs, t1) t2 =
    t_let_close vs (t_ty_subst mt mv t1) t2 in
  let bind_fun env mt mv vs _ sofar =
    let matching_vs rs _ = id_equal rs.rs_name vs.vs_name in
    match Mrs.choose (Mrs.filter matching_vs env.funenv) with
    | rs, ({ c_node= Cfun e }, _) ->
        let t = Opt.get (term_of_expr ~prop:false e) in
        let t = t_ty_subst mt mv t in
        let vs_args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
        t_let_close vs (t_lambda vs_args [] t) sofar
    | _ -> incomplete "anonymous function not cfun"
    | exception Not_found ->
        kasprintf failwith "add_premises: function %a not found" print_vs vs in
  let close_term t =
    let mt, mv = Mtv.empty, Mvs.empty in
    let free = t_freevars Mvs.empty t in
    let free_vars, free_funs =
      Mvs.partition (fun vs _ -> Mvs.mem vs env.vsenv) free in
    let t, mt, mv =
      match post_res with
      | Some t_res ->
          let vs, t = open_post t in
          let mt = ty_match mt vs.vs_ty (t_type t_res) in
          let vs' = create_vsymbol (id_clone vs.vs_name) (t_type t_res) in
          let mv = Mvs.add vs (vs', t_res) mv in
          t, mt, mv
      | None -> t, mt, mv in
    let vsenv, mt, mv =
      Mvs.fold (match_free_var env) free_vars (vsenv, mt, mv) in
    (* mv : old (polymorphic) vsymbol -> new (monomorphic) vsymbol * value term *)
    let mv_vs = Mvs.map fst mv in
    let mv_t = Mvs.map (fun (vs', _) -> t_var vs') mv in
    let vsenv = List.map (fun (vs, t) -> Mvs.find_def vs vs mv_vs, t_ty_subst mt mv_t t) vsenv in
    let t = t_ty_subst mt mv_t t in
    let t = Mvs.fold (fun _ -> bind_vs mt mv_t) mv t in
    let t = List.fold_left (fun t vs_t -> bind_vs mt mv_t vs_t t) t vsenv in
    let t = Mvs.fold (bind_fun env mt mv_t) free_funs t in
    t in
  add_premises (List.map close_term ts) env.premises

let add_post_premises cty res env =
  let post_res = match res with
    | Normal v -> Some (cty.cty_post, v)
    | Excep (xs, v) -> Some (Mxs.find xs cty.cty_xpost, v)
    | Irred _ -> None in
  Opt.iter (fun (post, res) ->
      let vsenv, t = term_of_value env [] res in
      add_premises ~post_res:t ~vsenv post env) post_res

let rec exec_expr ctx e =
  check_limits ctx.limits;
  let _,bl,bc,el,ec = Loc.get (Opt.get_def Loc.dummy_position e.e_loc) in
  Debug.dprintf debug_trace_exec "@[<h>%t%sEVAL EXPR %d,%d-%d,%d: %a@]@." pp_indent
    (if ctx.giant_steps then "G-s. " else "") bl bc el ec
    (pp_limited print_expr) e;
  let res = exec_expr' ctx e in
  Debug.dprintf debug_trace_exec "@[<h>%t -> %a@]@." pp_indent (print_result) res;
  res

(* abs = abstractly - do not execute loops and function calls - use
   instead invariants and function contracts to guide execution. *)
and exec_expr' ctx e =
  let loc_or_dummy = Opt.get_def Loc.dummy_position e.e_loc in
  match e.e_node with
  | Evar pvs ->
      let v = get_pvs ctx.env pvs in
      Debug.dprintf debug_trace_exec "[interp] reading var %s from env -> %a@\n"
        pvs.pv_vs.vs_name.id_string print_value v ;
      Normal v
  | Econst (Constant.ConstInt c) ->
      Normal (value (ty_of_ity e.e_ity) (Vnum (big_int_of_const c)))
  | Econst (Constant.ConstReal r) ->
      (* ConstReal can be float or real *)
      if ity_equal e.e_ity ity_real then
        let p, q = compute_fraction r.Number.rl_real in
        let sp, sq = BigInt.to_string p, BigInt.to_string q in
        try Normal (value ty_real (Vreal (Big_real.real_from_fraction sp sq)))
        with Mlmpfr_wrapper.Not_Implemented ->
          incomplete "mlmpfr wrapper is not implemented"
      else
        let c = Constant.ConstReal r in
        let s = Format.asprintf "%a" Constant.print_def c in
        Normal (value (ty_of_ity e.e_ity) (Vfloat (Mlmpfr_wrapper.make_from_str s)))
  | Econst (Constant.ConstStr s) -> Normal (value ty_str (Vstring s))
  | Eexec (ce, cty) -> begin
      (* TODO (When) do we have to check the contracts in cty? When ce <> Capp? *)
      match ce.c_node with
      | Cpur (ls, pvs) ->
          Debug.dprintf debug_trace_exec "@[<h>%tEVAL EXPR: EXEC PURE %a %a@]@." pp_indent print_ls ls
            (Pp.print_list Pp.comma print_value) (List.map (get_pvs ctx.env) pvs);
          let desc = asprintf "of `%a`" print_ls ls in
          if ctx.do_rac then (
            let cntr_ctx = mk_cntr_ctx ctx ?loc:e.e_loc ~desc Vc.expl_pre in
            check_terms ctx.rac cntr_ctx cty.cty_pre );
          with_push_premises ctx.env.premises @@ fun () -> (
          add_premises cty.cty_pre ctx.env;
          exec_pure ~loc:e.e_loc ctx ls pvs )
      | Cfun e' ->
        Debug.dprintf debug_trace_exec "@[<h>%tEVAL EXPR EXEC FUN: %a@]@." pp_indent print_expr e';
        let add_free pv = Mvs.add pv.pv_vs (Mvs.find pv.pv_vs ctx.env.vsenv) in
        let cl = Spv.fold add_free ce.c_cty.cty_effect.eff_reads Mvs.empty in
        let mvs = snapshot_vsenv cl in
        ( match ce.c_cty.cty_args with
          | [] ->
             if ctx.giant_steps then begin
                 register_call ctx.env e.e_loc None mvs Log.Exec_giant_steps;
                 exec_call_abstract ?loc:e.e_loc ~attrs:e'.e_attrs
                   ~snapshot:cty.cty_oldies (Some e.e_id) ctx ce.c_cty [] e.e_ity
               end
             else begin
                 register_call ctx.env e.e_loc None mvs Log.Exec_normal;
                 if ctx.do_rac then (
                   let cntr_ctx = mk_cntr_ctx ctx ?loc:e.e_loc Vc.expl_pre in
                   check_terms ctx.rac cntr_ctx cty.cty_pre );
                 with_push_premises ctx.env.premises @@ fun () -> (
                 add_premises cty.cty_pre ctx.env;
                 exec_expr ctx e' )
               end
          | [arg] ->
              let match_free pv mt =
                let v = Mvs.find pv.pv_vs ctx.env.vsenv in
                ty_match mt pv.pv_vs.vs_ty v.v_ty in
              let mt = Spv.fold match_free cty.cty_effect.eff_reads Mtv.empty in
              let ty = ty_inst mt (ty_of_ity e.e_ity) in
              if cty.cty_pre <> [] then
                incomplete "anonymous function with precondition not supported (%a)"
                  Pp.(print_option_or_default "unknown location" Loc.pp_position) e.e_loc;
              Normal (value ty (Vfun (cl, arg.pv_vs, e')))
          | _ -> incomplete "many args for exec fun" (* TODO *) )
      | Cany ->
         register_any_call ctx.env e.e_loc None Mvs.empty;
         if ctx.do_rac then
           exec_call_abstract ?loc:e.e_loc ~attrs:e.e_attrs
             ~snapshot:cty.cty_oldies (Some e.e_id) ctx cty [] e.e_ity
         else
           Normal (undefined_value ctx.env e.e_ity)
      | Capp (rs, pvsl) when
          Opt.map is_prog_constant (Mid.find_opt rs.rs_name ctx.env.pmodule.Pmodule.mod_known)
          = Some true ->
          Debug.dprintf debug_trace_exec "@[<h>%tEVAL EXPR: EXEC CAPP %a@]@." pp_indent print_rs rs;
          if ctx.do_rac then (
            let desc = asprintf "of `%a`" print_rs rs in
            let cntr_ctx = mk_cntr_ctx ctx ?loc:e.e_loc ~desc Vc.expl_pre in
            check_terms ctx.rac cntr_ctx cty.cty_pre );
          assert (cty.cty_args = [] && pvsl = []);
          let v =
            match find_definition ctx.env rs with
            | Builtin f ->
                Debug.dprintf debug_trace_exec "@[<hv2>%tEXEC CALL %a: BUILTIN@]@." pp_indent print_rs rs;
                f rs []
            | _ -> Lazy.force (Mrs.find rs ctx.env.rsenv) in
          if ctx.do_rac then (
            let desc = asprintf "of `%a`" print_rs rs in
            let cntr_ctx = mk_cntr_ctx ctx ~desc Vc.expl_post in
            check_posts ctx.rac cntr_ctx v rs.rs_cty.cty_post );
          Normal v
      | Capp (rs, pvsl) ->
          if ce.c_cty.cty_args <> [] then
            incomplete "no support for partial function applications (%a)"
              (Pp.print_option_or_default "unknown location" Loc.pp_position)
              e.e_loc;
          exec_call ?loc:e.e_loc ~attrs:e.e_attrs (Some e.e_id) ctx rs pvsl e.e_ity
    end
  | Eassign l ->
      let search_and_assign (pvs, rs, v) =
        let rss, fs =
          match (get_pvs ctx.env pvs).v_desc with
          | Vconstr (_, rs, args) -> rs, args
          | _ -> assert false in
        let maybe_assign rs' f =
          if rs_equal rs' rs then (
            field_set f (get_pvs ctx.env v);
            raise Exit) in
        try List.iter2 maybe_assign rss fs
        with Exit -> () in
      List.iter search_and_assign l;
      Normal unit_value
  | Elet (ld, e2) -> (
    match ld with
    | LDvar (pvs, e1) -> (
      match exec_expr ctx e1 with
      | Normal v ->
        let ctx = {ctx with env= bind_pvs pvs v ctx.env} in
        exec_expr ctx e2
      | r -> r )
    | LDsym (rs, ce) ->
        let funenv = Mrs.add rs (ce, None) ctx.env.funenv in
        exec_expr {ctx with env= {ctx.env with funenv}} e2
    | LDrec l ->
        let funenv =
          List.fold_left
            (fun acc d ->
               Mrs.add d.rec_sym (d.rec_fun, Some l)
                 (Mrs.add d.rec_rsym (d.rec_fun, Some l) acc))
            ctx.env.funenv l in
        exec_expr {ctx with env= {ctx.env with funenv}} e2 )
  | Eif (e1, e2, e3) -> (
    match exec_expr ctx e1 with
    | Normal v ->
      if is_true v then
        exec_expr ctx e2
      else if is_false v then
        exec_expr ctx e3
      else (
        Debug.dprintf debug_trace_exec "Cannot eval if condition@.";
        Irred e )
    | r -> r )
  | Ewhile (cond, inv, varl, e1) when ctx.giant_steps -> begin
      (* arbitrary execution of an iteration taken from the counterexample

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
        * stop the interpretation here - raise RAC_Stuck *)
      (* assert1 *)
      let res = with_push_premises ctx.env.premises @@ fun () -> (
      if ctx.do_rac then
        check_terms ctx.rac (mk_cntr_ctx ctx Vc.expl_loop_init) inv;
      add_premises inv ctx.env;
      register_iter_loop ctx.env e.e_loc Log.Exec_giant_steps;
      List.iter (assign_written_vars e.e_effect.eff_writes loc_or_dummy ctx)
        (Mvs.keys ctx.env.vsenv);
      (* assert2 *)
      let opt_old_varl =
        if ctx.do_rac && e.e_effect.eff_oneway = Total then
          Some (oldify_varl ctx.env varl) else None in
      let cntr_ctx = mk_cntr_ctx ctx Vc.expl_loop_keep in
      check_assume_terms ctx.rac cntr_ctx inv;
      add_premises inv ctx.env;
      match exec_expr ctx cond with
      | Normal v ->
         if is_true v then begin
             register_iter_loop ctx.env e.e_loc Log.Exec_normal;
             match exec_expr ctx e1 with
             | Normal _ ->
                 if ctx.do_rac then (
                   let cntr_ctx = mk_cntr_ctx ctx Vc.expl_loop_keep in
                   check_terms ctx.rac cntr_ctx inv );
                 add_premises inv ctx.env;
                 if ctx.do_rac && e.e_effect.eff_oneway = Total then (
                   let oldified_varl = Opt.get opt_old_varl in
                   check_variant ctx.rac Vc.expl_loop_vari e.e_loc
                     ~giant_steps:ctx.giant_steps ctx.env oldified_varl varl );
                 (* the execution cannot continue from here *)
                 register_stucked ctx.env e.e_loc
                   "Cannot continue after arbitrary iteration" Mid.empty;
                 let desc = "when reaching the end of a loop iteration" in
                 let cntr_ctx = mk_cntr_ctx ctx ~desc Vc.expl_absurd in
                 stuck ?loc:e.e_loc cntr_ctx "%s" desc
             | r -> r
           end
         else if is_false v then
           Normal unit_value
         else (
           Debug.dprintf debug_trace_exec "Cannot debug while condition@.";
           Irred e )
      | r -> r
      ) in
      add_premises inv ctx.env;
      res
    end
  | Ewhile (e1, inv, varl, e2) ->
      let res = with_push_premises ctx.env.premises @@ fun () -> (
      if ctx.do_rac then
        check_terms ctx.rac (mk_cntr_ctx ctx Vc.expl_loop_init) inv;
      add_premises inv ctx.env;
      let rec iter () =
        let opt_old_varl =
          if ctx.do_rac && e.e_effect.eff_oneway = Total then
            Some (oldify_varl ctx.env varl) else None in
        match exec_expr ctx e1 with
        | Normal v ->
            if is_true v then ( (* condition true *)
              register_iter_loop ctx.env e.e_loc Log.Exec_normal;
              match exec_expr ctx e2 with
              | Normal _ -> (* body executed normally *)
                  if ctx.do_rac then (
                    let cntr_ctx = mk_cntr_ctx ctx Vc.expl_loop_keep in
                    check_terms ctx.rac cntr_ctx inv );
                  add_premises inv ctx.env;
                  if ctx.do_rac && e.e_effect.eff_oneway = Total then (
                    let old_varl = Opt.get opt_old_varl in
                    check_variant ctx.rac Vc.expl_loop_vari e.e_loc
                      ~giant_steps:ctx.giant_steps ctx.env old_varl varl );
                  iter ()
              | r -> r
            ) else if is_false v then (* condition false *)
              Normal unit_value
            else (
              Debug.dprintf debug_trace_exec "Cannot eval while condition@.";
              Irred e )
        | r -> r in
      iter ()
      ) in
      add_premises inv ctx.env;
      res
  | Efor (i, (pvs1, dir, pvs2), _ii, inv, e1) when ctx.giant_steps -> begin
      (* TODO what to do with _ii? *)
      (* arbitrary execution of an iteartion taken from the counterexample
        for i = e1 to e2 do invariant {I} e done
        ~>
        let a = exec_expr e1 in
        let b = exec_expr e2 in
        if a <= b + 1 then begin
          bind_vs i a;
          assert1 {I};
          assign_written_vars_with_ce;
          let i = get_and_register_variable ~def:(b+1) i in
          if not (a <= i <= b + 1) then abort1;
          if a <= i <= b then begin
            assert2* { I };
            exec_expr e;
            bind_vs i (i + 1) in
            assert3 {I};
            bind_vs i (b + 1);
          end;
          assert4* {I}
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
            (value assigned to i is not compatible with loop range) *)
      let res, v = with_push_premises ctx.env.premises @@ fun () -> (
      try
        let a = big_int_of_value (get_pvs ctx.env pvs1) in
        let b = big_int_of_value (get_pvs ctx.env pvs2) in
        let le, suc = match dir with
          | To -> BigInt.le, BigInt.succ
          | DownTo -> BigInt.ge, BigInt.pred in
        register_iter_loop ctx.env e.e_loc Log.Exec_giant_steps;
        (* assert1 *)
        if le a (suc b) then begin
          let ctx = {ctx with env= bind_vs i.pv_vs (int_value a) ctx.env} in
          if ctx.do_rac then (
            let cntr_ctx = mk_cntr_ctx ctx Vc.expl_loop_init in
            check_terms ctx.rac cntr_ctx inv );
          add_premises inv ctx.env;
          List.iter (assign_written_vars e.e_effect.eff_writes loc_or_dummy ctx)
            (Mvs.keys ctx.env.vsenv);
          let def = int_value (suc b) in
          let i_val = get_and_register_variable ctx ~def i.pv_vs.vs_name i.pv_ity in
          let ctx = {ctx with env= bind_vs i.pv_vs i_val ctx.env} in
          let i_bi = big_int_of_value i_val in
          if not (le a i_bi && le i_bi (suc b)) then begin
            let desc = asprintf "Iterating variable not in bounds" in
            let mid = Mid.singleton i.pv_vs.vs_name i_val in
            register_stucked ctx.env e.e_loc desc mid;
            let cntr_ctx = mk_cntr_ctx ctx ~desc Vc.expl_pre in
            stuck ?loc:e.e_loc cntr_ctx "because %s" desc end;
          if le a i_bi && le i_bi b then begin
            register_iter_loop ctx.env e.e_loc Log.Exec_giant_steps;
            (* assert2 *)
            let cntr_ctx = mk_cntr_ctx ctx Vc.expl_loop_keep in
            check_assume_terms ctx.rac cntr_ctx inv;
            add_premises inv ctx.env;
            match exec_expr ctx e1 with
            | Normal _ ->
                let ctx = {ctx with env= bind_vs i.pv_vs (int_value (suc i_bi)) ctx.env} in
                (* assert3 *)
                if ctx.do_rac then
                  check_terms ctx.rac (mk_cntr_ctx ctx Vc.expl_loop_keep) inv;
                add_premises inv ctx.env;
                let ctx =
                  {ctx with env= bind_vs i.pv_vs (int_value (suc b)) ctx.env} in
                (* assert4 *)
                check_assume_terms ctx.rac
                  (mk_cntr_ctx ctx ~desc:"with (b+1)" Vc.expl_loop_keep) inv;
                Normal unit_value, Some (suc b)
            | r -> r, None
          end
          else begin
            (* assert4 *)
            (* i is already equal to b + 1 *)
            let desc = "after last iteration" in
            check_assume_terms ctx.rac
              (mk_cntr_ctx ctx ~desc Vc.expl_loop_keep) inv;
            Normal unit_value, match i_val.v_desc with Vnum n -> Some n | _ -> None
          end
        end
        else
          Normal unit_value, None
      with NotNum -> failwith "Something's not a number@."
      ) in
      Opt.iter (fun v -> add_premises inv (bind_vs i.pv_vs (int_value v) ctx.env)) v;
      res
    end
  | Efor (pvs, (pvs1, dir, pvs2), _i, inv, e1) ->
    let res, i = with_push_premises ctx.env.premises @@ fun () -> (
    let le, suc =
      match dir with
      | To -> BigInt.le, BigInt.succ
      | DownTo -> BigInt.ge, BigInt.pred in
    try
      let a = big_int_of_value (get_pvs ctx.env pvs1) in
      let b = big_int_of_value (get_pvs ctx.env pvs2) in
      let ctx =
        {ctx with env= bind_vs pvs.pv_vs (value ty_int (Vnum a)) ctx.env} in
      ( if ctx.do_rac then
          check_terms ctx.rac (mk_cntr_ctx ctx Vc.expl_loop_init) inv ) ;
      add_premises inv ctx.env;
      let rec iter i =
        Debug.dprintf debug_trace_exec "[interp] for loop with index = %s@."
          (BigInt.to_string i) ;
        if le i b then (
          register_iter_loop ctx.env e.e_loc Log.Exec_normal;
          let ctx = {ctx with env= bind_vs pvs.pv_vs (int_value i) ctx.env} in
          match exec_expr ctx e1 with
          | Normal _ ->
              if ctx.do_rac then
                check_terms ctx.rac (mk_cntr_ctx ctx Vc.expl_loop_keep) inv;
              iter (suc i)
          | r -> r, None
        ) else
          Normal unit_value, Some i
        in
      iter a
    with NotNum -> failwith "Something's not a number@."
    ) in
    Opt.iter (fun i -> add_premises inv (bind_vs pvs.pv_vs (int_value i) ctx.env)) i;
    res
  | Ematch (e0, ebl, el) -> (
      let r = exec_expr ctx e0 in
      match r with
      | Normal t -> (
          if ebl = [] then
            r
          else
            try exec_match ctx t ebl with Undetermined -> (
                Debug.dprintf debug_trace_exec "Match is undetermined@.";
                Irred e ) )
      | Excep (ex, t) -> (
        match Mxs.find ex el with
        | [], e2 ->
            (* assert (t = Vvoid); *)
            exec_expr ctx e2
        | [v], e2 ->
            let ctx = {ctx with env= bind_vs v.pv_vs t ctx.env} in
            exec_expr ctx e2
        | _ -> assert false (* TODO ? *)
        | exception Not_found -> r )
      | _ -> r )
  | Eraise (xs, e1) -> (
      let r = exec_expr ctx e1 in
      match r with Normal t -> Excep (xs, t) | _ -> r )
  | Eexn (_, e1) -> exec_expr ctx e1
  | Eassert (kind, t) ->
      if ctx.do_rac then begin
          match kind with
            | Assert ->
                check_term ctx.rac (mk_cntr_ctx ctx Vc.expl_assert) t;
                add_premises [t] ctx.env
            | Assume ->
                check_assume_term ctx.rac (mk_cntr_ctx ctx Vc.expl_assume) t;
                add_premises [t] ctx.env
            | Check ->
                check_term ctx.rac (mk_cntr_ctx ctx Vc.expl_check) t
        end;
      Normal unit_value
  | Eghost e1 ->
      Debug.dprintf debug_trace_exec "@[<h>%tEVAL EXPR: GHOST %a@]@." pp_indent print_expr e1;
      (* TODO: do not eval ghost if no assertion check *)
      exec_expr ctx e1
  | Epure t ->
      Debug.dprintf debug_trace_exec "@[<h>%tEVAL EXPR: PURE %a@]@." pp_indent print_term t;
      let t = ctx.compute_term ctx.env t in
      Normal (value (Opt.get t.t_ty) (Vterm t))
  | Eabsurd ->
      let cntr_ctx = mk_cntr_ctx ctx ?loc:e.e_loc Vc.expl_absurd in
      raise (Fail (cntr_ctx, t_false))

and exec_match ctx t ebl =
  let rec iter ebl =
    match ebl with
    | [] ->
        Loc.warning
          (Loc.register_warning "non_exhaustive_eval" "Warn for non=exhaustive pattern matching in evaluation.@.")
          "[Exec] Pattern matching not exhaustive in evaluation@." ;
        assert false
    | (p, e) :: rem -> (
      try
        let ctx = {ctx with env= matching ctx.env t p.pp_pat} in
        exec_expr ctx e
      with NoMatch -> iter rem ) in
  iter ebl

and exec_call ?(main_function=false) ?loc ?attrs (eid:expr_id option) ctx rs arg_pvs ity_result =
  let arg_vs = List.map (get_pvs ctx.env) arg_pvs in
  Debug.dprintf debug_trace_exec "@[<h>%tExec call %a %a@]@."
    pp_indent print_rs rs Pp.(print_list space print_value) arg_vs;
  let ctx = {ctx with env= multibind_pvs rs.rs_cty.cty_args arg_vs ctx.env} in
  let ctx =
    let vsenv = snapshot_oldies rs.rs_cty.cty_oldies ctx.env.vsenv in
    {ctx with env= {ctx.env with vsenv}} in
  let res = with_push_premises ctx.env.premises @@ fun () -> (
  let mode =
    let giant_steps_possible () =
      if rs_equal rs rs_func_app then false else
        match find_definition ctx.env rs with
        | LocalFunction _ -> true | _ -> false in
    if ctx.giant_steps && not main_function && giant_steps_possible ()
    then Log.Exec_giant_steps
    else Log.Exec_normal in
  let mvs = let aux pv v = pv.pv_vs, snapshot v in
    Mvs.of_list (List.map2 aux rs.rs_cty.cty_args arg_vs) in
  let ctx =
    if ctx.do_rac then ( (* Check variant decrease, maybe *)
      match find_rec_defn rs ctx.env with
      | None -> (* Call to non-recursive function *)
          {ctx with old_varl= None}
      | Some rds ->
          match List.find (fun rd -> rs_equal rs rd.rec_sym) rds with
          | rd -> (* Non-recursive (initial) call to recursive function *)
              {ctx with old_varl= Some (oldify_varl ctx.env rd.rec_varl)}
          | exception Not_found ->
              match List.find (fun rd -> rs_equal rs rd.rec_rsym) rds with
              | rd -> (* Recursive call to recursive function *)
                  let old_varl = Opt.get ctx.old_varl in
                  check_variant ctx.rac Vc.expl_variant loc
                    ~giant_steps:ctx.giant_steps ctx.env old_varl rd.rec_varl;
                  {ctx with old_varl= Some (oldify_varl ctx.env rd.rec_varl)} )
    else ctx in
  let check_pre_and_register_call ?(any_function=false) mode =
    if not main_function then
      if any_function then
        register_any_call ctx.env loc (Some rs) mvs
      else
        register_call ctx.env loc (Some rs) mvs mode;
    (* Module [Expr] adds a precondition "DECR f" to each recursive function
       "f", which is not defined in the context of Pinterp. TODO? *)
    let not_DECR = function
      | {t_node= Tapp (f, _)} -> not (Strings.has_prefix "DECR " f.ls_name.id_string)
      | _ -> true in
    if ctx.do_rac then (
      let desc = asprintf "of `%a`" print_rs rs in
      (if main_function then check_assume_terms else check_terms)
        ctx.rac (mk_cntr_ctx ctx ?loc:loc ?attrs ~desc Vc.expl_pre)
        (List.filter not_DECR rs.rs_cty.cty_pre));
    add_premises (List.filter not_DECR rs.rs_cty.cty_pre) ctx.env in
  match mode with
  | Log.Exec_giant_steps ->
      check_pre_and_register_call Log.Exec_giant_steps;
      exec_call_abstract ?loc ?attrs ~rs eid ctx rs.rs_cty arg_pvs ity_result
  | Log.Exec_normal ->
      let res =
        if rs_equal rs rs_func_app then begin
          let exception UnexpectedArgs in
          try
            check_pre_and_register_call Log.Exec_normal;
            begin match arg_vs with
            | [{v_desc= Vfun (cl, arg, e)}; value] ->
                let vsenv = Mvs.union (fun _ _ v -> Some v) ctx.env.vsenv cl in
                let ctx = {ctx with env= bind_vs arg value {ctx.env with vsenv}} in
                exec_expr ctx e
            | [{v_desc= Vpurefun (_, bindings, default)}; value] ->
                let v = try Mv.find value bindings with Not_found -> default in
                Normal v
            | [{v_desc= Vterm t}; value ] ->
                begin match t_open_lambda t with
                | ([vs],_,t') ->
                  begin match t'.t_node with
                  (* special case when [t] is a function defining the mapping of elements
                  for an array or a map, for example:
                  t = fun (x:bool) -> if x = True then -1 else 0 *)
                  | Tif (t1,t2,t3) ->
                    let ctx = {ctx with env= bind_vs vs value ctx.env} in
                    begin match (ctx.compute_term ctx.env t1).t_node with
                    | Ttrue -> exec_expr ctx (e_pure (ctx.compute_term ctx.env t2))
                    | Tfalse ->  exec_expr ctx (e_pure (ctx.compute_term ctx.env t3))
                    | _ -> incomplete "could not reduce %a" print_term t'
                    end
                  (* special case when [t] is a constant function *)
                  | Tconst _ ->
                    let ctx = {ctx with env= bind_vs vs value ctx.env} in
                    exec_expr ctx (e_pure (ctx.compute_term ctx.env t'))
                  | _ -> raise UnexpectedArgs
                  end
                | _ -> raise UnexpectedArgs
                end
            | [{v_desc= Vundefined }; _] ->
                incomplete "an undefined argument was passed to %a"
                  Ident.print_decoded rs.rs_name.id_string
            | _ -> raise UnexpectedArgs
            end
          with
          | UnexpectedArgs ->
            incomplete "unexpected arguments passed to %a"
              Ident.print_decoded rs.rs_name.id_string
          end
        else
          match rs, arg_vs with
          | {rs_logic= RLls ls}, [{v_desc= Vproj (ls', v)}]
            when ls_equal ls ls' -> (* Projection of a projection value *)
              check_pre_and_register_call Log.Exec_normal;
              Normal v
          | _ -> match find_definition ctx.env rs with
            | LocalFunction (locals, (ce, rdl)) -> (
                let ctx = {ctx with env= add_local_funs locals rdl ctx.env} in
                match ce.c_node with
                | Capp (rs', pvl) ->
                    Debug.dprintf debug_trace_exec "@[<h>%tEXEC CALL %a: Capp %a]@."
                      pp_indent print_rs rs print_rs rs';
                    check_pre_and_register_call Log.Exec_normal;
                    exec_call ?loc ?attrs eid ctx rs' (pvl @ arg_pvs) ity_result
                | Cfun body ->
                    Debug.dprintf debug_trace_exec "@[<hv2>%tEXEC CALL %a: FUN/%d %a@]@."
                      pp_indent print_rs rs (List.length ce.c_cty.cty_args) (pp_limited print_expr) body;
                    let ctx = {ctx with env= multibind_pvs ce.c_cty.cty_args arg_vs ctx.env} in
                    check_pre_and_register_call Log.Exec_normal;
                    exec_expr ctx body
                | Cany ->
                    if ctx.do_rac then (
                      check_pre_and_register_call ~any_function:true Log.Exec_giant_steps;
                      exec_call_abstract ?loc ?attrs ~rs eid ctx rs.rs_cty arg_pvs ity_result )
                    else (* We can't check the postcondition *)
                      incomplete "cannot apply an any-function %a with RAC disabled"
                        print_rs rs
                | Cpur _ -> assert false (* TODO ? *) )
            | Builtin f ->
                Debug.dprintf debug_trace_exec "@[<hv2>%tEXEC CALL %a: BUILTIN@]@." pp_indent print_rs rs;
                check_pre_and_register_call Log.Exec_normal;
                Normal (f rs arg_vs)
            | Constructor its_def ->
                Debug.dprintf debug_trace_exec "@[<hv2>%tEXEC CALL %a: CONSTRUCTOR@]@." pp_indent print_rs rs;
                check_pre_and_register_call Log.Exec_normal;
                let aux mt pv v =
                  ty_match mt pv.pv_vs.vs_ty (ty_inst mt (v_ty v)) in
                let mt =
                  List.fold_left2 aux Mtv.empty rs.rs_cty.cty_args arg_vs in
                let ty = ty_inst mt (ty_of_ity ity_result) in
                let vs = List.map field arg_vs in
                let v = value ty (Vconstr (Some rs, its_def.Pdecl.itd_fields, vs)) in
                if ctx.do_rac then
                  check_type_invs ctx.rac ?loc ~giant_steps:ctx.giant_steps
                    ctx.env ity_result v;
                Normal v
            | Projection proj_def -> (
              let exception CannotProject in
              try
                Debug.dprintf debug_trace_exec "@[<hv2>%tEXEC CALL %a: PROJECTION@]@." pp_indent print_rs rs;
                check_pre_and_register_call Log.Exec_normal;
                let rec search pv opt_constr_args args v' =
                  match opt_constr_args, args with
                  | Some pv2 :: pvl, v :: vl ->
                      if pv_equal pv pv2 then
                        Normal (field_get v)
                      else search pv pvl vl v'
                  | _ -> raise CannotProject
                in
                begin match rs.rs_field, arg_vs with
                | Some pv, [{v_desc= Vconstr (Some cstr, _, args)} as v] ->
                    let opt_constr_args = List.map (fun f -> Some f) cstr.rs_cty.cty_args in
                    search pv opt_constr_args args v
                | Some pv, [{v_desc= Vconstr (None, field_rss, args)} as v] ->
                    begin try
                      let opt_constr_args = List.map (fun rs -> rs.rs_field) field_rss in
                      search pv opt_constr_args args v
                    with _ -> raise CannotProject
                    end
                | Some pv, [{v_desc= Vterm {t_node = Tapp (ls,args)}} as v] ->
                  let matching_name rs =
                    String.equal rs.rs_name.id_string ls.ls_name.id_string in
                  begin
                    match List.find matching_name proj_def.Pdecl.itd_constructors with
                    | rs ->
                      let opt_constr_args = List.map (fun f -> Some f) rs.rs_cty.cty_args in
                      let fields = List.map (fun f -> field (term_value (ity_of_ty (Opt.get f.t_ty)) f)) args in
                      search pv opt_constr_args fields v
                    | exception Not_found -> raise CannotProject
                  end
                | _, [{v_desc= Vundefined}] ->
                    incomplete "cannot project undefined by %a" print_rs rs
                | _ -> raise CannotProject
                end
              with CannotProject ->
                kasprintf failwith "Cannot project values %a by %a"
                  Pp.(print_list comma print_value) arg_vs
                  print_rs rs )
            | exception Not_found ->
                incomplete "definition of routine %s could not be found"
                  rs.rs_name.id_string in
      if ctx.do_rac then (
        let desc = asprintf "of `%a`" print_rs rs in
        let loc = if main_function then None else loc in
        match res with
        | Normal v ->
            let cntr_ctx = mk_cntr_ctx ctx ?attrs ?loc ~desc Vc.expl_post in
            check_posts ctx.rac cntr_ctx v rs.rs_cty.cty_post
        | Excep (xs, v) ->
            let cntr_ctx = mk_cntr_ctx ctx ?loc ~desc ?attrs Vc.expl_xpost in
            check_posts ctx.rac cntr_ctx v (Mxs.find xs rs.rs_cty.cty_xpost)
        | Irred _ -> () );
      res
  ) in
  add_post_premises rs.rs_cty res ctx.env;
  res

and exec_call_abstract ?snapshot ?loc ?attrs ?rs (eid:expr_id option) ctx cty arg_pvs ity_result =
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
  let exn = Incomplete "Giant-step call without location" in
  let loc = Opt.get_exn exn loc in
  let ctx = match snapshot with
    | Some oldies ->
        let vsenv = snapshot_oldies oldies ctx.env.vsenv in
        {ctx with env= {ctx.env with vsenv}}
    | None -> ctx in
  let res = with_push_premises ctx.env.premises @@ fun () -> (
  (* assert1 is already done above *)
  let vars_map = Mpv.of_list (List.combine cty.cty_args arg_pvs) in
  let asgn_wrt =
    assign_written_vars ~vars_map cty.cty_effect.eff_writes loc ctx in
  List.iter asgn_wrt (Mvs.keys ctx.env.vsenv);
  let res_v = get_and_register_result ?rs ctx cty.cty_post eid loc ity_result in
  (* assert2 *)
  let desc = match rs with
    | None -> "of anonymous function"
    | Some rs -> asprintf "of `%a`" print_rs rs in
  check_assume_posts ctx.rac
    (mk_cntr_ctx ctx ~desc ?attrs Vc.expl_post) res_v cty.cty_post;
  Normal res_v
  ) in
  add_post_premises cty res ctx.env;
  res

(******************************************************************************)
(*                             GLOBAL EVALUATION                              *)
(******************************************************************************)

let init_real (emin, emax, prec) = Big_real.init emin emax prec

module Sidpos = struct
  include Set.Make (struct
    type t = Ident.ident * Loc.position
    let compare = Util.cmp [
        Util.cmptr fst Ident.id_compare;
        Util.cmptr snd Loc.compare;
      ]
  end)

  let add_id id locs =
    match id.id_loc with Some loc -> add (id, loc) locs | None -> locs

  (** Currently the model can contain only one value for a variable defined in a
     module that has been cloned several times (limitations in
     [Printer.queried_terms]). When getting the model value for a global
     variable, we cannot decide here if the values is intended for that
     variable, because they the different variables share the same location.
     Because the wrong value can make the RAC stuck and the model to be
     considered (wrongly) BAD_CE, we have to abort.

     As of 84f534324, identifiers from cloned modules have the location of
     the clone, but we leave the check here to identify possible other sources
     of ambigous model elements. *)
  let check locs id =
    match id.id_loc with
    | Some loc -> assert (not (mem (id, loc) locs))
    | _ -> ()
end

let bind_globals ?rs_main ctx =
  let open Pdecl in
  let is_before id d (known, found_rs) =
    let found_rs = found_rs || match d.pd_node with
      | PDlet (LDsym (rs, _)) ->
          Opt.equal rs_equal (Some rs) rs_main
      | PDlet (LDrec ds) ->
          List.exists (fun d -> Opt.equal rs_equal (Some d.rec_sym) rs_main) ds
      | _ -> false in
    let known = if found_rs then known else Mid.add id d known in
    known, found_rs in
  let eval_global id d (ctx, locs) =
    match d.pd_node with
    | PDlet (LDvar (pv, e)) ->
        Debug.dprintf debug_trace_exec "EVAL GLOBAL VAR %a at %a@."
          print_decoded id.id_string
          Pp.(print_option_or_default "NO LOC" Loc.pp_position) id.id_loc;
        let v = get_and_register_global (Sidpos.check locs) ctx exec_expr id
            (Some e) [] e.e_ity in
        {ctx with env= bind_vs pv.pv_vs (Lazy.force v) ctx.env}, (* TODO Don't force [v] until used *)
        Sidpos.add_id id locs
    | PDlet (LDsym (rs, ce)) when is_prog_constant d -> (
        Debug.dprintf debug_trace_exec "EVAL GLOBAL SYM CONST %a at %a@."
          print_decoded id.id_string
          Pp.(print_option_or_default "NO LOC" Loc.pp_position) id.id_loc;
        assert (ce.c_cty.cty_args = []);
        let oexp = match ce.c_node with
          | Cany -> None | Cfun e -> Some e
          | _ -> failwith "eval_globals: program constant cexp" in
        let v = get_and_register_global (Sidpos.check locs) ctx exec_expr id
            oexp ce.c_cty.cty_post ce.c_cty.cty_result in
        {ctx with env= bind_rs rs v ctx.env}, Sidpos.add_id id locs )
    | PDpure ->
      begin match d.pd_pure with
      | [Decl.{d_node = Dparam ls}] when ls.ls_args = [] ->
        begin match ls.ls_value with
        | None -> ctx, locs
        | Some ty ->
          Debug.dprintf debug_trace_exec "EVAL GLOBAL LOGICAL CONST %a at %a@."
            print_decoded id.id_string
            Pp.(print_option_or_default "NO LOC" Loc.pp_position) id.id_loc;
          let v = get_and_register_global (Sidpos.check locs) ctx exec_expr id None [] (Ity.ity_of_ty ty) in
          {ctx with env= bind_ls ls v ctx.env}, Sidpos.add_id id locs
        end
      | [Decl.{d_node = Dparam ls}] ->
        let ty = match ls.ls_value with
          | None -> ty_bool
          | Some ty -> ty
        in
        let ls_ty = List.fold_right ty_func ls.ls_args ty in
        Debug.dprintf debug_trace_exec "EVAL GLOBAL LOGICAL FUN %a of type @[%a@] at %a@."
          print_decoded id.id_string
          Pretty.print_ty ls_ty
          Pp.(print_option_or_default "NO LOC" Loc.pp_position) id.id_loc;
        let v = get_and_register_global (Sidpos.check locs) ctx exec_expr id None [] (Ity.ity_of_ty ls_ty) in
        {ctx with env= bind_ls ls v ctx.env}, Sidpos.add_id id locs
      | _ -> ctx, locs
      end
    | _ -> ctx, locs in
  let mod_known, _ =
    Mid.fold is_before ctx.env.pmodule.Pmodule.mod_known (Mid.empty, false) in
  fst (Mid.fold eval_global mod_known (ctx, Sidpos.empty))

let exec_global_fundef ctx locals rdl e =
  get_builtin_progs ctx.env.why_env ;
  with_limits @@ fun () ->
  let ctx = bind_globals ctx in
  let ctx = {ctx with env= add_local_funs locals rdl ctx.env} in
  let res = exec_expr ctx e in
  res, ctx.env.vsenv, ctx.env.rsenv

let exec_rs ctx rs =
  get_builtin_progs ctx.env.why_env ;
  with_limits @@ fun () ->
  let get_value env pv = get_and_register_param env pv.pv_vs.vs_name pv.pv_ity in
  let ctx = bind_globals ~rs_main:rs ctx in
  let ctx =
    let register = register_used_value ctx.env rs.rs_name.id_loc in
    let env = multibind_pvs ~register rs.rs_cty.cty_args
        (List.map (get_value ctx) rs.rs_cty.cty_args) ctx.env in
    {ctx with env} in
  register_exec_main ctx.env rs;
  let loc = Opt.get_def Loc.dummy_position rs.rs_name.id_loc in
  let res = exec_call ~main_function:true ~loc None ctx rs rs.rs_cty.cty_args
      rs.rs_cty.cty_result in
  register_ended ctx.env rs.rs_name.id_loc;
  res, ctx

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
  | Irred _ ->
      fprintf fmt "@[<hov2>Execution error: %a@]@," print_logic_result res ;
      fprintf fmt "@[globals:@ %t@]" print_envs

let report_cntr fmt (ctx, term) =
  report_cntr fmt (ctx, "failed", term)
