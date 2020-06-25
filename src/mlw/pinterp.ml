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

let debug =
  Debug.register_info_flag "trace_exec"
    ~desc:"trace execution of code given by --exec or --eval"

let debug_rac = Debug.register_info_flag "rac" ~desc:"trace evaluation for RAC"

let pp_bindings ?(sep = Pp.semi) ?(pair_sep = Pp.arrow) ?(delims = Pp.(lbrace, rbrace)) pp_key pp_value
    fmt l =
  let pp_binding fmt (k, v) =
    fprintf fmt "@[<h>%a%a%a@]" pp_key k pair_sep () pp_value v in
  fprintf fmt "%a%a%a" (fst delims) ()
    (Pp.print_list sep pp_binding)
    l (snd delims) ()

let pp_typed pp ty fmt x =
  fprintf fmt "(%a: %a)" pp x Pretty.print_ty (ty x)


(* EXCEPTIONS *)

exception NoMatch
exception Undetermined
exception CannotCompute
exception NotNum
exception CannotFind of (Env.pathname * string * string)
exception Missing_dispatch of string

(* DISPATCH *)

type dispatch_ctx = {
  disp_rs: (Pdecl.known_map * rsymbol) option Mrs.t; (* Map source symbols to target symbols *)
  disp_ty: tysymbol option Mts.t; (* Map source type symbols to target type symbols *)
}

let empty_dispatch = {disp_rs= Mrs.empty; disp_ty= Mts.empty}

let add_dispatch env ~source:pm1 ~target:pm2 disp_ctx =
  let open Pmodule in
  let add_rs_rev_ls disp_ctx =
    let for_rs _ rs1 disp_ctx =
      if List.mem rs1.rs_name.id_string ["Tuple0"; "True"; "False"] then
        (* TODO Why are they in every module? *)
        disp_ctx
      else
        let exception Found of rsymbol in
        let find str2 ps =
          if str2 = rs1.rs_name.id_string then
            match ps with
            | RS rs2 -> raise (Found rs2)
            | _ -> () in
        let def = match Mstr.iter find pm2.mod_export.ns_ps with
          | exception Found rs2 -> Some (pm2.mod_known, rs2)
          | () -> None in
        let disp_rs = Mrs.add rs1 def disp_ctx.disp_rs in
        {disp_ctx with disp_rs} in
    let print_ps fmt = function
      | PV pv -> fprintf fmt "PV %a" print_pv pv
      | RS rs -> fprintf fmt "PV %a" print_rs rs
      | OO _ -> fprintf fmt "OO" in
    let get_rs = function RS rs -> Some rs | ps -> eprintf "IGNORE %a@." print_ps ps; None in
    let mrs1 = Mstr.map_filter get_rs pm1.mod_export.ns_ps in
    Mstr.fold for_rs mrs1 disp_ctx in
  let add_ty disp_ctx =
    let for_ity _ {its_ts= ts1} disp_ctx =
      let exception Found of tysymbol in
      let find str2 {its_ts= ts2} =
        if str2 = ts1.ts_name.id_string then
          raise (Found ts2) in
      let def = match Mstr.iter find pm2.mod_export.ns_ts with
        | exception Found ts2 ->
            Some ts2
        | () -> None in
      let disp_ty = Mts.add ts1 def disp_ctx.disp_ty in
      {disp_ctx with disp_ty} in
    Mstr.fold for_ity pm1.mod_export.ns_ts disp_ctx in
  add_ty (add_rs_rev_ls disp_ctx)

let () = Exn_printer.register (fun fmt exn ->
    match exn with
    | Missing_dispatch str -> fprintf fmt "Missing dispatch for %s" str
    | _ -> raise exn)

let rs_dispatch disp_rs rs =
  match Mrs.find rs disp_rs with
  | Some (known, rs') ->
      let pp_rs fmt rs =
        fprintf fmt "%a:%a -> %a" print_rs rs
          Pp.(print_list arrow (pp_typed print_pv (fun pv -> pv.pv_vs.vs_ty))) rs.rs_cty.cty_args
          Pretty.print_ty (ty_of_ity rs.rs_cty.cty_result) in
      Debug.dprintf debug_rac "@[<hv2>Dispatched @[<h>%a@] to @[<h>%a@]@]@."
        pp_rs rs pp_rs rs';
      rs', known
  | None -> raise (Missing_dispatch (asprintf "rsymbol %a" print_rs rs))

let rec ty_dispatch disp_ty ty =
  match ty.ty_node with
  | Tyvar _ -> ty
  | Tyapp (ts, tys) ->
      try
        match Mts.find ts disp_ty with
        | Some ts' ->
            Debug.dprintf debug_rac "@[<hv2>Dispatched type @[<h>%a@] to @[<h>%a@]@]@."
              Pretty.print_ts ts Pretty.print_ts ts';
            ty_app ts' (List.map (ty_dispatch disp_ty) tys)
        | None -> raise (Missing_dispatch (asprintf "tvsymbol %a" Pretty.print_ts ts))
      with Not_found -> ty

(* VALUES *)

type float_mode = mpfr_rnd_t
type big_float = mpfr_float

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
  | Vfun of value Mvs.t (* closure *) * vsymbol * expr

and field = value ref

let rec freeze v = match v.v_desc with
  | Vconstr (rs, fs) ->
      let fs = List.map freeze_field fs in
      {v with v_desc= Vconstr (rs, fs)}
  | _ -> v

and freeze_field r = ref (freeze !r)

let value ty desc = {v_desc= desc; v_ty= ty}
let v_desc v = v.v_desc
let v_ty v = v.v_ty
let field_get (f : field) = f.contents
let constr rs vl = Vconstr (rs, List.map ref vl)

let mode_to_string m =
  match m with
  | To_Nearest -> "RNE"
  | Away_From_Zero -> "RNA"
  | Toward_Plus_Infinity -> "RTP"
  | Toward_Minus_Infinity -> "RTN"
  | Toward_Zero -> "RTZ"
  | Faithful -> assert false

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
  | Vfun _ -> fprintf fmt "@[<v2><fun>@]"
  | Vconstr (rs, vl) when is_rs_tuple rs ->
      fprintf fmt "@[(%a)@]" (Pp.print_list Pp.comma print_field) vl
  | Vconstr (rs, []) -> fprintf fmt "@[%a@]" print_rs rs
  | Vconstr (rs, vl) ->
      fprintf fmt "@[(%a %a)@]" print_rs rs
        (Pp.print_list Pp.space print_field)
        vl

and print_field fmt f = print_value fmt (field_get f)


let rec term_of_value' mt v : ty Mtv.t * term =
  match v.v_desc with
  | Vnum i -> mt, t_const (Constant.int_const i) v.v_ty
  | Vstring s -> mt, t_const (Constant.ConstStr s) ty_str
  | Vbool b -> mt, if b then t_bool_true else t_bool_false
  | Vvoid -> mt, t_tuple []
  | Vconstr (rs, fs) ->
      let mt, fs = Lists.map_fold_left term_of_field mt fs in
      mt, t_app_infer (ls_of_rs rs) fs
  | Vfun (cl, arg, e) ->
      let aux vs v (mt, mv) =
        let mt = ty_match mt vs.vs_ty v.v_ty in
        let mt, t = term_of_value' mt v in
        mt, Mvs.add vs t mv in
      let mt, mv = Mvs.fold aux cl (mt, Mvs.empty) in
      let t = Opt.get (term_of_expr ~prop:false e) in
      let t = t_ty_subst mt mv t in
      mt, t_lambda [arg] [] t
      (* let mv = Mvs.map term_of_value cl in
       * let t = t_ty_subst Mtv.empty mv t in
       * t_lambda [arg] [] t *)
  | _ -> Format.kasprintf failwith "term_of_value: %a" print_value v

and term_of_field mt r = term_of_value' mt r.contents

let term_of_value t = snd (term_of_value' Mtv.empty t)

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
  { known: Pdecl.known_map;
    funenv: Expr.cexp Mrs.t;
    vsenv: value Mvs.t;
    env: Env.env;
    disp_ctx: dispatch_ctx }

let add_local_funs locals env =
  let add acc (rs, ce) = Mrs.add rs ce acc in
  let funenv = List.fold_left add env.funenv locals in
  {env with funenv}

let bind_vs vs v env = {env with vsenv= Mvs.add vs v env.vsenv}
let bind_pvs pv v_t env = bind_vs pv.pv_vs v_t env

let multibind_pvs l tl env =
  List.fold_right2 bind_pvs l tl env

(** [multibind_pvs' ty_disp pvs vs (env, mt, mv)] binds values [vs] to variables [pvs],
    updating the type mapping [mt] by the bindings. Values are possibly
    dispatching values by [ty_disp], adding entries from original variables to
    new variables with dispatched types in [mv]. *)
let multibind_pvs' ty_disp pvs vs (env, mt, mv) =
  let aux pv v (env, mt, mv) =
    let vs = create_vsymbol (id_clone pv.pv_vs.vs_name) v.v_ty in
    let ty = ty_dispatch ty_disp pv.pv_vs.vs_ty in
    let env = bind_vs vs v env in
    let mt = ty_match mt ty v.v_ty in
    let mv = Mvs.add pv.pv_vs (t_var vs) mv in
    env, mt, mv in
  List.fold_right2 aux pvs vs (env, mt, mv)

let print_vsenv_ty fmt m =
  let pp_vs = pp_typed Pretty.print_vs (fun vs -> vs.vs_ty) in
  let pp_value = pp_typed print_value (fun v -> v.v_ty) in
  fprintf fmt "@[<v 0>%a@]" (pp_bindings pp_vs pp_value) (Mvs.bindings m)

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
      int31_module; byte_module ]

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
       eprintf "Cannot compute instances of private type %a (add \
                dispatch?)@." print_its ts;
       raise CannotCompute in
  let subst = its_match_regs ts l1 l2 in
  let ityl = List.map (fun pv -> pv.pv_ity) cs.rs_cty.cty_args in
  let tyl = List.map (ity_full_inst subst) ityl in
  let fl = List.map (fun ity -> ref (default_value_of_type known ity)) tyl in
  value ty (Vconstr (cs, fl))

(* ROUTINE DEFINITIONS *)

type routine_defn =
  | Builtin of (rsymbol -> value list -> value)
  | Function of (rsymbol * cexp) list * cexp
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
  | Pdecl.PDlet (LDsym (_, ce)) -> Function ([], ce)
  | Pdecl.PDlet (LDrec dl) ->
      let locs = List.map (fun d -> d.rec_rsym, d.rec_fun) dl in
      Function (locs, find_def rs dl)
  | Pdecl.PDexn _ -> raise Not_found
  | Pdecl.PDpure -> raise Not_found

let find_definition env (rs: rsymbol) =
  (* then try if it is a built-in symbol *)
  match Hrs.find builtin_progs rs with
  | f -> Builtin f
  | exception Not_found ->
      (* then try if it is a local function *)
      match Mrs.find rs env.funenv with
      | f -> Function ([], f)
      | exception Not_found ->
          (* else look for a global function *)
          find_global_definition env.known rs

(* CONTRADICTION CONTEXT *)

type cntr_ctx =
  { c_desc: string;
    c_trigger_loc: Loc.position option;
    c_env: Env.env;
    c_known: Decl.known_map;
    c_rule_terms: term Mid.t;
    c_vsenv: term Mvs.t }

exception Contr of cntr_ctx * term

let report_cntr_head fmt (ctx, msg, term) =
  let pp_pos fmt loc =
    let f, l, b, e = Loc.get loc in
    fprintf fmt "%s, line %d, characters %d-%d" f l b e in
  fprintf fmt "@[<v2>%s %s" ctx.c_desc msg;
  ( match ctx.c_trigger_loc, term.t_loc with
    | Some t1, Some t2 ->
        fprintf fmt " at %a@,Defined at %a" pp_pos t1 pp_pos t2
    | Some t, None | None, Some t ->
        fprintf fmt " at %a" pp_pos t
    | None, None -> () );
  fprintf fmt "@]"

let cmp_vs (vs1, _) (vs2, _) =
  String.compare vs1.vs_name.id_string vs2.vs_name.id_string

let pp_vsenv pp_value fmt =
  let delims = Pp.(nothing, nothing) and sep = Pp.comma in
  fprintf fmt "%a" (pp_bindings ~delims ~sep Pretty.print_vs pp_value)

let report_cntr fmt (ctx, msg, term) =
  fprintf fmt "@[<v2>%a@," report_cntr_head (ctx, msg, term);
  fprintf fmt "@[<hov2>Term: %a@]@," Pretty.print_term term ;
  fprintf fmt "@[<hov2>Variables: %a@]"
    (pp_vsenv Pretty.print_term)
    (List.sort cmp_vs (Mvs.bindings ctx.c_vsenv)) ;
  fprintf fmt "@]"

let add_known_rule_term id pd (known, rule_terms) =
  match pd.Pdecl.pd_pure with
  | [] -> known, rule_terms
  | [decl] ->
      Mid.add id decl known, rule_terms
  | Decl.[({d_node= Dparam _} as decl); {d_node= Dprop (Paxiom, _, t)}] ->
      (* let function: function + axiom *)
      Mid.add id decl known, Mid.add id t rule_terms
  | Decl.[({d_node= Dlogic [(ls, _def)]} as decl); {d_node= Dprop (Paxiom, pr, t)}]
    ->
      (* let (rec) predicate:
         predicate + axiom *)
      Mid.add ls.ls_name decl known, Mid.add pr.Decl.pr_name t rule_terms
  | Decl.
      [ {d_node= Dparam _}; {d_node= Dprop (Paxiom, pr, t)};
        {d_node= Dprop (Paxiom, _, _)} ] ->
      (* let (rec) function:
         function f args : ty + axiom f'def : t + axiom f'spec : t *)
      known, Mid.add pr.Decl.pr_name t rule_terms
  | Decl.{d_node= Dtype _} :: _ ->
      (* - type declaration
         - field function declarations (Dparam)
         - type invariants (Dprop (Paxiom, _, _)) *)
      known, rule_terms
  | _ ->
      Format.eprintf "@[<hv2>Cannot process pure declarations for %s:@ %a@]@."
        id.id_string
        (Pp.print_list Pp.space Pretty.print_decl)
        pd.Pdecl.pd_pure ;
      failwith "Cannot process pure declarations"

let add_fun rs cexp known =
  try
    let t =
      match cexp.c_node with
      | Cfun e -> Opt.get_exn Exit (term_of_expr ~prop:false e)
      | _ -> raise Exit in
    let ls =
      let preid = id_clone rs.rs_name in
      let ty_args =
        List.map (fun pv -> Ity.ty_of_ity pv.pv_ity) rs.rs_cty.cty_args in
      let ty_res = Ity.ty_of_ity rs.rs_cty.cty_result in
      Term.create_lsymbol preid ty_args (Some ty_res) in
    let vs_args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
    let ldecl = Decl.make_ls_defn ls vs_args t in
    let decl = Decl.create_logic_decl [ldecl] in
    Mid.add rs.rs_name decl known
  with Exit -> known

let cntr_ctx desc ?trigger_loc ?(vsenv = Mvs.empty) env =
  let c_known, c_rule_terms =
    Mid.fold add_known_rule_term env.known (Mid.empty, Mid.empty) in
  let c_known = Mrs.fold add_fun env.funenv c_known in
  let vsenv' = Mvs.map term_of_value env.vsenv in
  let c_vsenv = Mvs.union (fun _ _ t -> Some t) vsenv vsenv' in
  { c_env= env.env;
    c_desc= desc;
    c_trigger_loc= trigger_loc;
    c_known;
    c_rule_terms;
    c_vsenv }

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

(** Reduce a term using the reduction engine.

    @param env Why3 environment
    @param known Global definitions from the interpreted module
    @param rule_terms Rules to be added to the reduction engine
    @param vsenv Local variable environment
    @param t Term to be evaluated
    @return A reduction of term [t]
  *)
let reduce_term env known rule_terms vsenv t =
  let open Reduction_engine in
  let params =
    { compute_builtin= true;
      compute_defs= true;
      compute_def_set= Sls.empty } in
  let eng = create params env known in
  let eng = Mid.fold try_add_rule rule_terms eng in
  let vsenv = (* TODO better fix typing of the variables in vsenv *)
    let vars = t_freevars Mvs.empty t in
    Mvs.filter (fun vs _ -> Mvs.contains vars vs) vsenv in
  (* (\* Cannot substite abstract with concrete types (only type variables) *\)
   * let mt, mv, vsenv =
   *   let aux vs t (mt, mv, vsenv) =
   *     let ty = Opt.get t.t_ty in
   *     let vs' = create_vsymbol (id_clone vs.vs_name) ty in
   *     (\* eprintf "TY MATCH @[<h>%a@] @[%a@]@." Pretty.print_ty vs.vs_ty Pretty.print_ty ty; *\)
   *     let (\* mt, *\) ty0 = (\* ty_dispatch dispatch mt *\) vs.vs_ty in
   *     let mt = ty_match mt ty0 ty in
   *     let mv = Mvs.add vs (t_var vs') mv in
   *     let vsenv = Mvs.add vs' t vsenv in
   *     mt, mv, vsenv in
   *   Mvs.fold aux vsenv (Mtv.empty, Mvs.empty, Mvs.empty) in
   * let t = t_ty_subst mt mv t in *)
  normalize ~limit:1000 eng vsenv t

(** Evaluate a term and raise an exception [Contr] if the result is false. *)
let check_term ctx t =
  match reduce_term ctx.c_env ctx.c_known ctx.c_rule_terms ctx.c_vsenv t with
  | {t_node= Ttrue} ->
      if Debug.test_flag debug_rac then
        eprintf "%a@." report_cntr_head (ctx, "is ok", t)
  | {t_node= Tfalse} -> raise (Contr (ctx, t))
  | t' ->
      eprintf "%a@." report_cntr (ctx, "cannot be evaluated", t) ;
      if Debug.test_flag debug_rac then
        eprintf "  @[<hv2>Result: %a@]@." Pretty.print_term t'
  | exception e when Debug.test_flag debug_rac ->
      eprintf "%a@." report_cntr (ctx, "WHEN TRYING", t) ;
      raise e

let check_terms ctx = List.iter (check_term ctx)

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

let rec eval_expr ~rac env (e : expr) : result =
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
      let is_real ity = ity_equal ity ity_real in
      if is_real e.e_ity then
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
    | Cpur _ -> assert false (* TODO ? *)
    | Cfun e' ->
        let aux pv = Mvs.add pv.pv_vs (Mvs.find pv.pv_vs env.vsenv) in
        let cl = Spv.fold aux ce.c_cty.cty_effect.eff_reads Mvs.empty in
        let arg =
          match ce.c_cty.cty_args with [arg] -> arg | _ -> assert false in
        let aux pv mt =
          let v = Mvs.find pv.pv_vs env.vsenv in
          ty_match mt pv.pv_vs.vs_ty v.v_ty in
        let mt = Spv.fold aux cty.cty_effect.eff_reads Mtv.empty in
        let ty = ty_inst mt (ty_of_ity e.e_ity) in
        Normal (value ty (Vfun (cl, arg.pv_vs, e')))
    | Cany -> raise CannotCompute
    | Capp (rs, pvsl) ->
        assert (cty.cty_args = []) ;
        assert (ce.c_cty.cty_args = []) ;
        exec_call ~rac ?loc:e.e_loc env rs pvsl e.e_ity )
  | Eassign l ->
      List.iter
        (fun (pvs, rs, value) ->
          let cstr, args =
            match (get_pvs env pvs).v_desc with
            | Vconstr (cstr, args) -> cstr, args
            | _ -> assert false in
          let rec aux constr_args args =
            match constr_args, args with
            | pv :: pvl, v :: vl ->
                if pv_equal pv (fd_of_rs rs) then
                  v := get_pvs env value
                else
                  aux pvl vl
            | _ -> raise CannotCompute in
          aux cstr.rs_cty.cty_args args)
        l ;
      Normal (value ty_unit Vvoid)
  | Elet (ld, e2) -> (
    match ld with
    | LDvar (pvs, e1) -> (
      match eval_expr ~rac env e1 with
      | Normal v ->
        let env = bind_pvs pvs v env in
        eval_expr ~rac env e2
      | r -> r )
    | LDsym (rs, ce) ->
        let env = {env with funenv= Mrs.add rs ce env.funenv} in
        eval_expr ~rac env e2
    | LDrec l ->
        let env' =
          { env with
            funenv=
              List.fold_left
                (fun acc d ->
                  Mrs.add d.rec_sym d.rec_fun (Mrs.add d.rec_rsym d.rec_fun acc))
                env.funenv l } in
        eval_expr ~rac env' e2 )
  | Eif (e1, e2, e3) -> (
    match eval_expr ~rac env e1 with
    | Normal t -> (
      match t.v_desc with
      | Vbool true -> eval_expr ~rac env e2
      | Vbool false -> eval_expr ~rac env e3
      | _ ->
          eprintf "@[[Exec] Cannot decide condition of if: @[%a@]@]@."
            print_value t ;
          Irred e )
    | r -> r )
  | Ewhile (cond, inv, _var, e1) -> (
      (* TODO variants *)
      if rac then
        check_terms (cntr_ctx "Loop invariant initialization" env) inv ;
      match eval_expr ~rac env cond with
      | Normal {v_desc= Vbool false} -> Normal (value ty_unit Vvoid)
      | Normal {v_desc= Vbool true} -> (
        match eval_expr ~rac env e1 with
        | Normal _ ->
            if rac then
              check_terms (cntr_ctx "Loop invariant preservation" env) inv ;
            eval_expr ~rac env e
        | r -> r )
      | Normal t ->
          eprintf "@[[Exec] Cannot decide condition of while: @[%a@]@]@."
            print_value t ;
          Irred e
      | r -> r )
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
          match eval_expr ~rac env' e1 with
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
      let r = eval_expr ~rac env e0 in
      match r with
      | Normal t -> (
          if ebl = [] then
            r
          else
            try exec_match ~rac env t ebl with Undetermined -> Irred e )
      | Excep (ex, t) -> (
        match Mxs.find ex el with
        | [], e2 ->
            (* assert (t = Vvoid); *)
            eval_expr ~rac env e2
        | [v], e2 ->
            let env' = bind_vs v.pv_vs t env in
            eval_expr ~rac env' e2
        | _ -> assert false (* TODO ? *)
        | exception Not_found -> r )
      | _ -> r )
  | Eraise (xs, e1) -> (
      let r = eval_expr ~rac env e1 in
      match r with Normal t -> Excep (xs, t) | _ -> r )
  | Eexn (_, e1) -> eval_expr ~rac env e1
  | Eassert (kind, t) ->
      let descr =
        match kind with
        | Expr.Assert -> "Assertion"
        | Expr.Assume -> "Assumption"
        | Expr.Check -> "Check" in
      if rac then check_term (cntr_ctx descr env) t ;
      Normal (value ty_unit Vvoid)
  | Eghost e1 ->
      (* TODO: do not eval ghost if no assertion check *)
      eval_expr ~rac env e1
  | Epure _ -> Normal (value ty_unit Vvoid) (* TODO *)
  | Eabsurd ->
      eprintf "@[[Exec] unsupported expression: @[%a@]@]@."
        print_expr e ;
      Irred e

and exec_match ~rac env t ebl =
  let rec iter ebl =
    match ebl with
    | [] ->
        eprintf "[Exec] Pattern matching not exhaustive in evaluation@." ;
        assert false
    | (p, e) :: rem -> (
      try
        let env' = matching env t p.pp_pat in
        eval_expr ~rac env' e
      with NoMatch -> iter rem ) in
  iter ebl

and exec_call ~rac ?loc env rs arg_pvs ity_result =
  let rs, env =
    match rs_dispatch env.disp_ctx.disp_rs rs with
    | rs, known -> rs, {env with known}
    | exception Not_found -> rs, env in
  let arg_vs = List.map (get_pvs env) arg_pvs in
  let env', mt, mv = multibind_pvs' env.disp_ctx.disp_ty rs.rs_cty.cty_args arg_vs (env, Mtv.empty, Mvs.empty) in
  let res_ty = ty_inst mt (ty_of_ity ity_result) in
  let oldies = (* cty_oldies: {old_v -> v} *)
    let aux old_pv pv oldies =
      try Mvs.add old_pv.pv_vs (freeze (Mvs.find pv.pv_vs env.vsenv)) oldies
      with Not_found ->
        oldies in
    Mpv.fold aux rs.rs_cty.cty_oldies Mvs.empty in
  let desc str = asprintf "%s of %a" str print_decoded rs.rs_name.id_string in
  if rac then (
    (* TODO variant *)
    let ctx = cntr_ctx (desc "Precondition") ?trigger_loc:loc env' in
    let pre = (* Substitute paramaters in preconditions *)
      List.map (t_ty_subst mt mv) rs.rs_cty.cty_pre in
    check_terms ctx pre );
  let res =
    if rs_equal rs rs_func_app then
      match arg_vs with
      | [{v_desc= Vfun (cl, arg, e)}; value] ->
          let env =
            {env with vsenv= Mvs.union (fun _ _ v -> Some v) env.vsenv cl} in
          let env = bind_vs arg value env in
          eval_expr ~rac env e
      | _ -> assert false
    else
      let call env d =
        match d.c_node with
        | Capp (rs', pvl) ->
            exec_call ~rac env rs' (pvl @ arg_pvs) ity_result
        | Cpur _ -> assert false (* TODO ? *)
        | Cany ->
            eprintf "Cannot compute any function %a (add dispatch?)@." print_decoded rs.rs_name.id_string;
            raise CannotCompute
        | Cfun body ->
            let pvsl = d.c_cty.cty_args in
            let env' = multibind_pvs pvsl arg_vs env in
            Debug.dprintf debug "@[Evaluating function body of %s@]@."
              rs.rs_name.id_string ;
            let r = eval_expr ~rac env' body in
            Debug.dprintf debug "@[Return from function %s@ result@ %a@]@."
              rs.rs_name.id_string print_logic_result r ;
            r in
      match find_definition env rs with
      | Function (locals, d) ->
          let env = add_local_funs locals env in
          call env d
      | Builtin f ->
          Debug.dprintf debug "@[Evaluating builtin function %s@]@."
            rs.rs_name.id_string ;
          let r = Normal (f rs arg_vs) in
          Debug.dprintf debug "@[Return from builtin function %s result %a@]@."
            rs.rs_name.id_string print_logic_result r ;
          r
      | Constructor _ ->
          Debug.dprintf debug "[interp] create record with type %a@." print_ity
            ity_result ;
          (* FIXME : put a ref only on mutable fields *)
          let args' = List.map ref arg_vs in
          Normal (value res_ty (Vconstr (rs, args')))
      | Projection _d -> (
        match rs.rs_field, arg_vs with
        | Some pv, [{v_desc= Vconstr (cstr, args)}] ->
            let rec aux constr_args args =
              match constr_args, args with
              | pv2 :: pvl, v :: vl ->
                  if pv_equal pv pv2 then Normal (field_get v) else aux pvl vl
              | _ -> raise CannotCompute in
            aux cstr.rs_cty.cty_args args
        | _ -> assert false )
      | exception Not_found ->
          eprintf "[interp] cannot find definition of routine %s@."
            rs.rs_name.id_string ;
          raise CannotCompute in
  ( if rac then
      (* Check a post-condition [t] by binding the result variable to
         the term [vt] representing the result value. *)
      let check_post ctx (vt : term) (mt : ty Mtv.t) (t : term) =
        let vs, t = open_post t in
        let mt = ty_match mt vs.vs_ty (oty_type vt.t_ty) in
        let vsenv = Mvs.singleton vs vt in
        let t = t_ty_subst mt vsenv t in
        check_term ctx t in
      (* Checking shared between normal and exceptional post-conditions *)
      let check_posts desc v posts =
        let env' = {env' with vsenv= Mvs.union (fun _ _ v -> Some v) env'.vsenv oldies} in
        let ctx = cntr_ctx desc ?trigger_loc:loc env' in
        let vt = term_of_value v in
        let post = (* Substitute parameters in postconditions *)
          List.map (t_ty_subst mt mv) posts in
        List.iter (check_post ctx vt mt) post in
      match res with
      | Normal v ->
          check_posts (desc "Postcondition") v rs.rs_cty.cty_post
      | Excep (xs, v) ->
          check_posts (desc "Exceptional postcondition") v (Mxs.find xs rs.rs_cty.cty_xpost)
      | _ -> () );
  res

(* GLOBAL EVALUATION *)

let init_real (emin, emax, prec) = Big_real.init emin emax prec

let eval_global_expr ~rac env disp_ctx km locals e =
  get_builtin_progs env ;
  let add_glob _id d acc =
    match d.Pdecl.pd_node with
    | Pdecl.PDlet (LDvar (pvs, _e)) ->
        (* TODO evaluate _e! *)
        let v = default_value_of_type km pvs.pv_ity in
        Mvs.add pvs.pv_vs v acc
    | _ -> acc in
  let global_env = Mid.fold add_glob km Mvs.empty in
  let env' = {known= km; funenv= Mrs.empty; vsenv= global_env; env; disp_ctx} in
  let env' = add_local_funs locals env' in
  let res = eval_expr ~rac env' e in
  res, global_env

let eval_global_fundef ~rac env disp_ctx mod_known locals body =
  try eval_global_expr ~rac env disp_ctx mod_known locals body
  with CannotFind (l, s, n) ->
    eprintf "Cannot find %a.%s.%s" (Pp.print_list Pp.dot pp_print_string) l s n ;
    assert false

let report_eval_result body fmt (res, final_env) =
  ( match res with
  | Normal _ ->
      fprintf fmt "@[<hov2>result:@ %a@ =@ %a@]@,@[<hov2>globals:@ %a@]"
        print_ity body.e_ity print_logic_result res (pp_vsenv print_value) (Mvs.bindings final_env)
  | Excep _ ->
      fprintf fmt "@[<hov2>exceptional result:@ %a@]@,@[<hov2>globals:@ %a@]"
        print_logic_result res (pp_vsenv print_value) (Mvs.bindings final_env)
  | Irred _ | Fun _ ->
      fprintf fmt "@[<hov2>Execution error: %a@]@," print_logic_result res ;
      fprintf fmt "@[globals:@ %a@]" (pp_vsenv print_value) (Mvs.bindings final_env) ) ;
  fprintf fmt "@]"

let report_cntr _body fmt (ctx, term) =
  fprintf fmt "@[%a@]" report_cntr (ctx, "failed", term)
