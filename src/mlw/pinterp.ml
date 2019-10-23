(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Term


let debug = Debug.register_info_flag "trace_exec"
  ~desc:"trace execution of code given by --exec or --eval"

(* environment *)

open Ity
open Expr
open Big_real
open Mlmpfr_wrapper

(* module Nummap = Map.Make(BigInt) *)

type float_mode = mpfr_rnd_t
type big_float = mpfr_float

type value =
  | Vconstr of rsymbol * field list
  | Vnum of BigInt.t
  | Vreal of real
  | Vfloat_mode of float_mode
  | Vfloat of big_float
  | Vstring of string
  | Vbool of bool
  | Vvoid
  | Varray of value array

and field = Fimmutable of value | Fmutable of value ref

let field_get f =
  match f with
  | Fimmutable v | Fmutable { contents = v } -> v

let constr rs vl =
  Vconstr(rs,List.map (fun v -> Fimmutable v) vl)

let mode_to_string m =
  match m with
  | To_Nearest            -> "RNE"
  | Away_From_Zero        -> "RNA"
  | Toward_Plus_Infinity  -> "RTP"
  | Toward_Minus_Infinity -> "RTN"
  | Toward_Zero           -> "RTZ"
  | Faithful              -> assert false

let rec print_value fmt v =
  match v with
  | Vnum n ->
    if BigInt.ge n BigInt.zero then
      fprintf fmt "%s" (BigInt.to_string n)
    else
      fprintf fmt "(%s)" (BigInt.to_string n)
  | Vbool b ->
    fprintf fmt "%b" b
  | Vreal r ->
    print_real fmt r
  | Vfloat f ->
      (* Getting "@" is intentional in mlmpfr library for bases higher than 10.
         So, we keep this notation. *)
      let hexadecimal = get_formatted_str ~base:16 f in
      let decimal = get_formatted_str ~base:10 f in
      fprintf fmt "%s (%s)" decimal hexadecimal
  | Vfloat_mode m ->
      fprintf fmt "%s" (mode_to_string m)
  | Vstring s ->
      Constant.print_string_default fmt s
  | Vvoid ->
    fprintf fmt "()"
  | Varray a ->
    fprintf fmt "@[[%a]@]"
      (Pp.print_list Pp.comma print_value)
      (Array.to_list a)
  | Vconstr(rs,vl) when is_rs_tuple rs ->
    fprintf fmt "@[(%a)@]"
      (Pp.print_list Pp.comma print_field) vl
  | Vconstr(rs,[]) ->
    fprintf fmt "@[%a@]" print_rs rs
  | Vconstr(rs,vl) ->
    fprintf fmt "@[(%a %a)@]"
      print_rs rs (Pp.print_list Pp.space print_field) vl

and print_field fmt f = print_value fmt (field_get f)

type env = {
  known : Pdecl.known_map;
  funenv : Expr.cexp Mrs.t;
  vsenv : value Mvs.t;
}

let add_local_funs locals env =
  { env with funenv =
      List.fold_left
        (fun acc (rs,ce) -> Mrs.add rs ce acc) env.funenv locals}


let bind_vs vs (v:value) env =
(*
  eprintf "[interp] binding var %s to %a@."
    vs.vs_name.Ident.id_string
    print_value v;
*)
  { env with vsenv = Mvs.add vs v env.vsenv }

let bind_pvs pv v env = bind_vs pv.pv_vs v env

let multibind_pvs l tl env =
  try
    List.fold_right2 bind_pvs l tl env
  with Invalid_argument _ -> assert false


let p_vsvar fmt (vs,t) =
  fprintf fmt "@[<hov 2>%a -> %a@]"
    Pretty.print_vs vs print_value t

let print_vsenv fmt s =
  let l = Mvs.bindings s in
  fprintf fmt "@[<v 0>%a@]" (Pp.print_list Pp.semi p_vsvar) l

(* evaluation of terms *)

exception NoMatch
exception Undetermined
exception CannotCompute

let rec matching env (v:value) p =
  match p.pat_node with
  | Pwild -> env
  | Pvar vs -> bind_vs vs v env
  | Por(p1,p2) ->
    begin
      try matching env v p1
      with NoMatch -> matching env v p2
    end
  | Pas(p,vs) -> matching (bind_vs vs v env) v p
  | Papp(ls,pl) ->
    match v with
      | Vconstr({rs_logic = RLls ls2},tl) ->
        if ls_equal ls ls2 then
          List.fold_left2 matching env (List.map field_get tl) pl
        else
          if ls2.ls_constr > 0 then raise NoMatch
          else raise Undetermined
      | Vbool b ->
        let ls2 = if b then fs_bool_true else fs_bool_false in
        if ls_equal ls ls2 then env else raise NoMatch
      | _ -> raise Undetermined


exception NotNum

let big_int_of_const i =
  i.Number.il_int

let big_int_of_value v =
  match v with
    | Vnum i -> i
    | _ -> raise NotNum

let eval_true _ls _l = Vbool true

let eval_false _ls _l = Vbool false

let eval_int_op op ls l =
  match l with
  | [Vnum i1;Vnum i2] ->
    begin
      try Vnum (op i1 i2)
      with NotNum | Division_by_zero ->
        constr ls l
    end
  | _ -> constr ls l

let eval_int_uop op ls l =
  match l with
  | [Vnum i1] ->
    begin
      try Vnum (op i1)
      with NotNum ->
        constr ls l
    end
  | _ -> constr ls l

let eval_int_rel op ls l =
  match l with
  | [Vnum i1;Vnum i2] ->
    begin
      try Vbool (op i1 i2)
      with NotNum ->
        constr ls l
    end
  | _ -> constr ls l

(* This initialize Mpfr for float32 behavior *)
let initialize_float32 () =
  set_default_prec 24;
  set_emin (-148);
  set_emax 128

(* This initialize Mpfr for float64 behavior *)
let initialize_float64 () =
  set_default_prec 53;
  set_emin (-1073);
  set_emax 1024

type 'a float_arity =
  | Mode1: (float_mode -> big_float -> big_float) float_arity (* Unary op *)
  | Mode2: (float_mode -> big_float -> big_float -> big_float) float_arity (* binary op *)
  | Mode3: (float_mode -> big_float -> big_float -> big_float -> big_float) float_arity (* ternary op *)
  | Mode_rel: (big_float -> big_float -> bool) float_arity (* binary predicates *)
  | Mode_rel1: (big_float -> bool) float_arity (* Unary predicate *)

let use_float_format (float_format: int) =
  match float_format with
  | 32 -> initialize_float32 ()
  | 64 -> initialize_float64 ()
  | _ -> raise CannotCompute

let eval_float:
  type a. int -> a float_arity -> a -> Expr.rsymbol -> value list -> value =
  (fun float_format ty op ls l ->
     (* Set the exponent depending on Float type that are used: 32 or 64 *)
     use_float_format float_format;
     try
       begin match ty, l with
         | Mode1, [Vfloat_mode mode; Vfloat f] ->
             (* Subnormalize used to simulate IEEE behavior *)
             Vfloat (subnormalize ~rnd:mode (op mode f))
         | Mode2, [Vfloat_mode mode; Vfloat f1; Vfloat f2] ->
             Vfloat (subnormalize ~rnd:mode (op mode f1 f2))
         | Mode3, [Vfloat_mode mode; Vfloat f1; Vfloat f2; Vfloat f3] ->
             Vfloat (subnormalize ~rnd:mode (op mode f1 f2 f3))
         | Mode_rel, [Vfloat f1; Vfloat f2] ->
             Vbool (op f1 f2)
         | Mode_rel1, [Vfloat f] ->
             Vbool (op f)
         | _ -> constr ls l
       end
     with
     | Mlmpfr_wrapper.Not_Implemented -> raise CannotCompute
     | _ -> assert false
  )

type 'a real_arity =
  | Modeconst: real real_arity
  | Mode1r: (real -> real) real_arity
  | Mode2r: (real -> real -> real) real_arity
  | Mode_relr: (real -> real -> bool) real_arity

let eval_real : type a. a real_arity -> a -> Expr.rsymbol -> value list -> value =
  (fun ty op ls l ->
     try
       begin match ty, l with
         | Mode1r, [Vreal r] ->
             Vreal (op r)
         | Mode2r, [Vreal r1; Vreal r2] ->
             Vreal (op r1 r2)
         | Mode_relr, [Vreal r1; Vreal r2] ->
             Vbool (op r1 r2)
         | Modeconst, [] ->
             Vreal op
         | _ -> constr ls l
       end
     with
     | Big_real.Undetermined -> (* Cannot decide interval comparison *)
         constr ls l
     | Mlmpfr_wrapper.Not_Implemented ->
         raise CannotCompute
     | _ -> assert false
  )

let rec default_value_of_type env ity =
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg r ->
    default_value_of_types env r.reg_its r.reg_args r.reg_regs
  | Ityapp(ts,_,_) when its_equal ts its_int ->
    Vnum BigInt.zero
  | Ityapp(ts,_,_) when its_equal ts its_real ->
    assert false (* TODO *)
  | Ityapp(ts,_,_) when its_equal ts its_bool ->
    Vbool false
(*
  | Ityapp(ts,_,_) when is_its_tuple ts ->
    assert false (* TODO *)
*)
  | Ityapp(ts,l1,l2) ->
    default_value_of_types env ts l1 l2

and default_value_of_types env ts l1 l2 =
  try
    let d = Pdecl.find_its_defn env.known ts in
    match d.Pdecl.itd_constructors with
    | [] -> assert false
    | cs :: _ ->
      let subst = its_match_regs ts l1 l2 in
      let tyl = List.map (ity_full_inst subst)
        (List.map (fun pv -> pv.pv_ity) cs.rs_cty.cty_args)
      in
      let vl = List.map (default_value_of_type env) tyl in
      Vconstr(cs, List.map (fun v -> Fmutable (ref v)) vl)
  with Not_found -> assert false

type result =
  | Normal of value
  | Excep of xsymbol * value
  | Irred of expr
  | Fun of rsymbol * pvsymbol list * int

let builtin_progs = Hrs.create 17

let builtin_array_type _kn _its = ()
(*
  match (Pdecl.find_its_defn kn its).Pdecl.itd_constructors with
  | [rs] -> array_cons_rs := rs
  | _ ->  assert false
*)

let exec_array_make _ args =
  match args with
    | [Vnum n;def] ->
      begin
        try
          let n = BigInt.to_int n in
          let v = Varray(Array.make n def) in
          v
        with _ -> raise CannotCompute
      end
    | _ ->
      raise CannotCompute

let exec_array_empty _ args =
  match args with
    | [Vconstr(_, [])] ->
        (* we know by typing that the constructor
           will be the Tuple0 constructor *)
        Varray([||])
    | _ ->
      raise CannotCompute

let exec_array_get _ args =
  match args with
    | [Varray a;Vnum i] ->
      begin
        try
          a.(BigInt.to_int i)
        with _ -> raise CannotCompute
      end
    | _ -> raise CannotCompute

let exec_array_length _ args =
  match args with
    | [Varray a] -> Vnum (BigInt.of_int (Array.length a))
    | _ -> raise CannotCompute

let exec_array_set _ args =
  match args with
    | [Varray a;Vnum i;v] ->
      begin
        try
          a.(BigInt.to_int i) <- v;
          Vvoid
        with _ -> raise CannotCompute
      end
    | _ -> assert false

let builtin_mode _kn _its = ()

let builtin_float_type _kn _its = ()

(** Description of modules *)
let built_in_modules =
  let bool_module =
    ["bool"],"Bool", [],
    [ "True", eval_true ;
      "False", eval_false ;
    ]
  in
  let int_modules =
    [
      ["int"],"Int", [],
      [ Ident.op_infix "+", eval_int_op BigInt.add;
        (* defined as x+(-y)
           Ident.op_infix "-", eval_int_op BigInt.sub; *)
        Ident.op_infix "*", eval_int_op BigInt.mul;
        Ident.op_prefix "-", eval_int_uop BigInt.minus;
        Ident.op_infix "=", eval_int_rel BigInt.eq;
        Ident.op_infix "<", eval_int_rel BigInt.lt;
        Ident.op_infix "<=", eval_int_rel BigInt.le;
        Ident.op_infix ">", eval_int_rel BigInt.gt;
        Ident.op_infix ">=", eval_int_rel BigInt.ge;
      ] ;
      ["int"],"MinMax", [],
      [ "min", eval_int_op BigInt.min;
        "max", eval_int_op BigInt.max;
      ] ;
      ["int"],"ComputerDivision", [],
      [ "div", eval_int_op BigInt.computer_div;
        "mod", eval_int_op BigInt.computer_mod;
      ] ;
      ["int"],"EuclideanDivision", [],
      [ "div", eval_int_op BigInt.euclidean_div;
        "mod", eval_int_op BigInt.euclidean_mod;
      ]
    ]
  in
  let array_module =
    ["array"],"Array",
    ["array", builtin_array_type],
    ["make", exec_array_make ;
     "empty", exec_array_empty ;
     Ident.op_get "", exec_array_get ;
     "length", exec_array_length ;
     Ident.op_set "", exec_array_set ;
    ]
  in

  let mode_module =
    ["ieee_float"], "RoundingMode",
    ["mode", builtin_mode],
    ["RNE", (fun _ _ -> Vfloat_mode To_Nearest);
     "RNA", (fun _ _ -> Vfloat_mode Away_From_Zero);
     "RTP", (fun _ _ -> Vfloat_mode Toward_Plus_Infinity);
     "RTN", (fun _ _ -> Vfloat_mode Toward_Minus_Infinity);
     "RTZ", (fun _ _ -> Vfloat_mode Toward_Zero);
    ]
  in
  let float_modules tyb ~prec m =
    ["ieee_float"], m,
    ["t", builtin_float_type],
    ["zeroF", (fun _rs _l ->
         Vfloat (make_zero ~prec Positive));
     "add", eval_float tyb Mode2 (fun rnd -> add ~rnd ~prec);
     "sub", eval_float tyb Mode2 (fun rnd -> sub ~rnd ~prec);
     "mul", eval_float tyb Mode2 (fun rnd -> mul ~rnd ~prec);
     "div", eval_float tyb Mode2 (fun rnd -> div ~rnd ~prec);
     "abs", eval_float tyb Mode1 (fun rnd -> abs ~rnd ~prec);
     "neg", eval_float tyb Mode1 (fun rnd -> neg ~rnd ~prec);
     "fma", eval_float tyb Mode3 (fun rnd -> fma ~rnd ~prec);
     "sqrt", eval_float tyb Mode1 (fun rnd -> sqrt ~rnd ~prec);
     "roundToIntegral", eval_float tyb Mode1 (fun rnd -> rint ~rnd ~prec);
(* Intentionnally removed from programs
     "min", eval_float_minmax min;
     "max", eval_float_minmax max;
*)
     "le", eval_float tyb Mode_rel lessequal_p;
     "lt", eval_float tyb Mode_rel less_p;
     "eq", eval_float tyb Mode_rel equal_p;
     "is_zero", eval_float tyb Mode_rel1 zero_p;
     "is_infinite", eval_float tyb Mode_rel1 inf_p;
     "is_nan", eval_float tyb Mode_rel1 nan_p;
     "is_positive", eval_float tyb Mode_rel1 (fun s -> signbit s = Positive);
     "is_negative", eval_float tyb Mode_rel1 (fun s -> signbit s = Negative);
    ]
  in

  let real_module =
    ["real"], "Real", [],
    [Ident.op_infix "=", eval_real Mode_relr Big_real.eq;
     Ident.op_infix "<", eval_real Mode_relr Big_real.lt;
     Ident.op_infix "<=", eval_real Mode_relr Big_real.le;
     Ident.op_prefix "-", eval_real Mode1r Big_real.neg;
     Ident.op_infix "+", eval_real Mode2r Big_real.add;
     Ident.op_infix "*", eval_real Mode2r Big_real.mul;
     Ident.op_infix "/", eval_real Mode2r Big_real.div;
    ]
  in
  let real_square_module =
    ["real"], "Square", [],
    ["sqrt", eval_real Mode1r Big_real.sqrt;
    ]
  in
  let real_trigo_module =
    ["real"], "Trigonometry", [],
    ["pi", eval_real Modeconst (Big_real.pi());
    ]
  in
  let real_exp_log =
    ["real"], "ExpLog", [],
    ["exp", eval_real Mode1r Big_real.exp;
     "log", eval_real Mode1r Big_real.log]
  in
  bool_module :: (int_modules @ [array_module;
                                 real_module;
                                 real_square_module;
                                 real_trigo_module;
                                 real_exp_log;
                                 mode_module;
                                 float_modules 32 ~prec:24 "Float32";
                                 float_modules 64 ~prec:53 "Float64";])

exception CannotFind of (Env.pathname * string * string)

let add_builtin_mo env (l,n,t,d) =
  let mo = Pmodule.read_module env l n in
  let exp = mo.Pmodule.mod_export in
  let kn = mo.Pmodule.mod_known in
  List.iter
    (fun (id,r) ->
       let its =
         try Pmodule.ns_find_its exp [id] with
         | Not_found -> raise (CannotFind (l, n, id))
       in
       r kn its)
    t;
  List.iter
    (fun (id,f) ->
       let ps =
         try Pmodule.ns_find_rs exp [id] with
         | Not_found -> raise (CannotFind (l, n, id))
       in
       Hrs.add builtin_progs ps f)
    d

let get_builtin_progs lib =
  List.iter (add_builtin_mo lib) built_in_modules

let get_pvs env pvs =
  let t =
    try
      Mvs.find pvs.pv_vs env.vsenv
  with Not_found ->
    eprintf "program variable %s not found in env@."
      pvs.pv_vs.vs_name.Ident.id_string;
    assert false
  in
  t


(* explicit printing of expr *)

(*

let p_pvs fmt pvs =
  fprintf fmt "@[{ pv_vs =@ %a;@ pv_ity =@ %a;@ pv_ghost =@ %B }@]"
    Pretty.print_vs pvs.pv_vs Ppretty.print_ity pvs.pv_ity
    pvs.pv_ghost

let p_ps fmt ps =
  fprintf fmt "@[{ ps_name =@ %s;@ ... }@]"
    ps.ps_name.Ident.id_string

let p_pls fmt pls =
  fprintf fmt "@[{ pl_ls =@ %s;@ ... }@]"
    pls.pl_ls.ls_name.Ident.id_string

let p_letsym fmt lsym =
  match lsym with
    | LetV pvs -> fprintf fmt "@[LetV(%a)@]" p_pvs pvs
    | LetA _ -> fprintf fmt "@[LetA(_)@]"

let rec p_let fmt ld =
  fprintf fmt "@[{ let_sym =@ %a;@ let_expr =@ %a }@]"
    p_letsym ld.let_sym p_expr ld.let_expr

and p_expr fmt e =
  match e.e_node with
    | Elogic t ->
      fprintf fmt "@[Elogic{type=%a}(%a)@]"
        Ppretty.print_vty e.e_vty
        Pretty.print_term t
    | Evalue pvs -> fprintf fmt "@[Evalue(%a)@]" p_pvs pvs
    | Earrow ps -> fprintf fmt "@[Earrow(%a)@]" p_ps ps
    | Eapp (e1, pvs, _) ->
      fprintf fmt "@[Eapp(%a,@ %a,@ <spec>)@]" p_expr e1 p_pvs pvs
    | Elet(ldefn,e1) ->
      fprintf fmt "@[Elet(%a,@ %a)@]" p_let ldefn p_expr e1
    | Erec (_, _) -> fprintf fmt "@[Erec(_,@ _,@ _)@]"
    | Eif (_, _, _) -> fprintf fmt "@[Eif(_,@ _,@ _)@]"
    | Ematch (_, _) -> fprintf fmt "@[Ematch(_,@ _)@]"
    | Eassign (pls, e1, reg, pvs) ->
      fprintf fmt "@[Eassign(%a,@ %a,@ %a,@ %a)@]"
        p_pls pls p_expr e1 Ppretty.print_reg reg p_pvs pvs
    | Eghost _ -> fprintf fmt "@[Eghost(_)@]"
    | Eany _ -> fprintf fmt "@[Eany(_)@]"
    | Eloop (_, _, _) -> fprintf fmt "@[Eloop(_,@ _,@ _)@]"
    | Efor (_, _, _, _) -> fprintf fmt "@[Efor(_,@ _,@ _,@ _)@]"
    | Eraise (_, _) -> fprintf fmt "@[Eraise(_,@ _)@]"
    | Eabstr (_, _) -> fprintf fmt "@[Eabstr(_,@ _)@]"
    | Eassert (_, _) -> fprintf fmt "@[Eassert(_,@ _)@]"
    | Eabsurd -> fprintf fmt "@[Eabsurd@]"

*)

let print_logic_result fmt r =
  match r with
    | Normal v ->
      fprintf fmt "@[%a@]" print_value v
    | Excep(x,v) ->
      fprintf fmt "@[exception %s(@[%a@])@]"
        x.xs_name.Ident.id_string print_value v
    | Irred e ->
      fprintf fmt "@[Cannot execute expression@ @[%a@]@]"
        print_expr e
    | Fun _ ->
      fprintf fmt "@[Result is a function@]"


(* evaluation of WhyML expressions *)


(* find routine definitions *)

type routine_defn =
  | Builtin of (rsymbol -> value list -> value)
  | Function of (rsymbol * cexp) list * cexp
  | Constructor of Pdecl.its_defn
  | Projection of Pdecl.its_defn

let rec find_def rs = function
  | d :: _ when rs_equal rs d.rec_sym -> d.rec_fun (* TODO : put rec_rsym in local env *)
  | _ :: l -> find_def rs l
  | [] -> raise Not_found

let rec find_constr_or_proj dl rs =
  match dl with
  | [] -> raise Not_found
  | d :: rem ->
    if List.mem rs d.Pdecl.itd_constructors then
      begin
        Debug.dprintf debug
          "@[<hov 2>[interp] found constructor:@ %s@]@."
          rs.rs_name.Ident.id_string;
        Constructor d
      end
    else
      if List.mem rs d.Pdecl.itd_fields then
        begin
          Debug.dprintf debug
            "@[<hov 2>[interp] found projection:@ %s@]@."
            rs.rs_name.Ident.id_string;
          Projection d
        end
      else
        find_constr_or_proj rem rs

let find_global_definition kn rs =
  match (Ident.Mid.find rs.rs_name kn).Pdecl.pd_node with
  | Pdecl.PDtype dl -> find_constr_or_proj dl rs
  | Pdecl.PDlet (LDvar _) -> raise Not_found
  | Pdecl.PDlet (LDsym(_,ce)) -> Function([],ce)
  | Pdecl.PDlet (LDrec dl) ->
    let locs = List.map (fun d -> (d.rec_rsym,d.rec_fun)) dl in
    Function(locs, find_def rs dl)
  | Pdecl.PDexn _ -> raise Not_found
  | Pdecl.PDpure -> raise Not_found

let find_definition env rs =
  try
    (* first try if it is a built-in symbol *)
    Builtin (Hrs.find builtin_progs rs)
  with Not_found ->
    try
      (* then try if it is a local function *)
      let f = Mrs.find rs env.funenv in
      Function([],f)
    with Not_found ->
      (* else look for a global function *)
      find_global_definition env.known rs

(* Assuming the real is given in pow2 and pow5 *)
let compute_fraction { Number.rv_sig = i; Number.rv_pow2 = p2; Number.rv_pow5 = p5 } =
  let p2_val = BigInt.pow_int_pos_bigint 2 (BigInt.abs p2) in
  let p5_val = BigInt.pow_int_pos_bigint 5 (BigInt.abs p5) in
  let num = ref BigInt.one in
  let den = ref BigInt.one in
  num := BigInt.mul i !num;
  if BigInt.ge p2 BigInt.zero then
    num := BigInt.mul p2_val !num
  else
    den := BigInt.mul p2_val !den;
  if BigInt.ge p5 BigInt.zero then
    num := BigInt.mul p5_val !num
  else
    den := BigInt.mul p5_val !den;
  (!num, !den)

(* evaluate expressions *)
let rec eval_expr env (e : expr) : result =
  match e.e_node with
  | Evar pvs ->
    begin
      try
        let v = get_pvs env pvs in
        Debug.dprintf debug
          "[interp] reading var %s from env -> %a@."
          pvs.pv_vs.vs_name.Ident.id_string
          print_value v;
        Normal v
      with Not_found -> assert false (* Irred e ? *)
    end
  | Econst (Constant.ConstInt c) ->
      Normal (Vnum (big_int_of_const c))
  | Econst (Constant.ConstReal r) ->
      (* ConstReal can be float or real *)
      let is_real ity = ity_equal ity ity_real in
      if is_real e.e_ity then
        let (p, q) = compute_fraction r.Number.rl_real in
        let (sp, sq) = BigInt.to_string p, BigInt.to_string q in
        try Normal (Vreal (real_from_fraction sp sq)) with
        | Mlmpfr_wrapper.Not_Implemented -> raise CannotCompute
      else
        let c = Constant.ConstReal r in
        let s = Format.asprintf "%a" Constant.print_def c in
        Normal (Vfloat (make_from_str s))
  | Econst (Constant.ConstStr s) -> Normal (Vstring s)
  | Eexec (ce,cty) ->
    assert (cty.cty_args = []);
    assert (ce.c_cty.cty_args = []);
    begin match ce.c_node with
    | Cpur _ -> assert false (* TODO ? *)
    | Cfun _ -> assert false (* TODO ? *)
    | Cany -> raise CannotCompute
    | Capp(rs,pvsl) -> exec_call env rs pvsl e.e_ity
    end
  | Eassign l ->
    List.iter
      (fun (pvs,rs,value) ->
        let fld = fd_of_rs rs in
        let value = get_pvs env value in
        match get_pvs env pvs with
        | Vconstr(cstr,args) ->
          let rec aux constr_args args =
            match constr_args,args with
            | pv :: pvl, v :: vl ->
              if pv_equal pv fld then
                match v with
                | Fmutable r -> r := value
                | Fimmutable _ -> assert false
              else
                aux pvl vl
            | _ -> raise CannotCompute
          in
          aux cstr.rs_cty.cty_args args
        | _ -> assert false)
      l;
    Normal Vvoid
  | Elet(ld,e2) ->
    begin match ld with
      | LDvar(pvs,e1) ->
        begin match eval_expr env e1 with
          | Normal v ->
            eval_expr (bind_pvs pvs v env) e2
          | r -> r
        end
      | LDsym(rs,ce) ->
        let env' = { env with funenv = Mrs.add rs ce env.funenv }
        in eval_expr env' e2
      | LDrec l ->
        let env' =
          { env with funenv =
              List.fold_left
                (fun acc d ->
                  Mrs.add d.rec_sym d.rec_fun
                    (Mrs.add d.rec_rsym d.rec_fun acc))
                env.funenv l }
        in eval_expr env' e2
    end
  | Eif(e1,e2,e3) ->
    begin
      match eval_expr env e1 with
        | Normal t ->
          begin
            match t with
              | Vbool true -> eval_expr env e2
              | Vbool false -> eval_expr env e3
              | _ ->
              begin
                eprintf
                  "@[[Exec] Cannot decide condition of if: @[%a@]@]@."
                  print_value t;
                Irred e
              end
          end
        | r -> r
    end
  | Ewhile(cond,_inv,_var,e1) ->
    begin
      match eval_expr env cond with
      | Normal t ->
        begin
          match t with
          | Vbool true ->
            let r = eval_expr env e1 in
            begin
              match r with
              | Normal _ -> eval_expr env e
              | _ -> r
            end
          | Vbool false -> Normal Vvoid
          | _ ->
            begin
              eprintf
                "@[[Exec] Cannot decide condition of while: @[%a@]@]@."
                print_value t;
              Irred e
            end
        end
      | r -> r
    end
  | Efor(pvs,(pvs1,dir,pvs2),_i,_inv,e1) ->
    begin
      try
        let a = big_int_of_value (get_pvs env pvs1) in
        let b = big_int_of_value (get_pvs env pvs2) in
        let le,suc = match dir with
          | To -> BigInt.le, BigInt.succ
          | DownTo -> BigInt.ge, BigInt.pred
        in
        let rec iter i =
          Debug.dprintf debug "[interp] for loop with index = %s@."
            (BigInt.to_string i);
          if le i b then
            let env' = bind_vs pvs.pv_vs (Vnum i) env in
            match eval_expr env' e1 with
              | Normal _ -> iter (suc i)
              | r -> r
          else Normal Vvoid
        in
        iter a
      with
          NotNum -> Irred e
    end
  | Ematch(e0,ebl,el) ->
    begin
      let r = eval_expr env e0 in
      match r with
        | Normal t ->
          if ebl = [] then r else
          begin try exec_match env t ebl
            with Undetermined -> Irred e
          end
        | Excep(ex,t) ->
          begin
            match Mxs.find ex el with
            | ([], e2) ->
              (* assert (t = Vvoid); *)
              eval_expr env e2
            | ([v], e2) ->
              let env' = bind_vs v.pv_vs t env in
              eval_expr env' e2
            | _ -> assert false (* TODO ? *)
            | exception Not_found -> r
          end
        | _ -> r
    end
  | Eraise(xs,e1) ->
    begin
      let r = eval_expr env e1 in
      match r with
        | Normal t -> Excep(xs,t)
        | _ -> r
    end
  | Eexn(_,e1) -> eval_expr env e1
  | Eassert(_,_t) -> Normal Vvoid (* TODO *)
    (* TODO: do not eval t if no assertion check *)
(*
    if true then (* noassert *) Normal Vvoid
    else
      begin match (eval_term env t) with
      | Vbool true -> Normal Vvoid
      | Vbool false ->
        eprintf "@[Assertion failed at %a@]@."
          (Pp.print_option Pretty.print_loc) e.e_loc;
        Irred e
      | _ ->
        Warning.emit "@[Warning: assertion cannot be evaluated at %a@]@."
          (Pp.print_option Pretty.print_loc) e.e_loc;
        Normal Vvoid
      end
*)
  | Eghost e1 ->
    (* TODO: do not eval ghost if no assertion check *)
    eval_expr env e1
  | Epure _ -> Normal Vvoid (* TODO *)
  | Eabsurd ->
    eprintf "@[[Exec] unsupported expression: @[%a@]@]@."
      (if Debug.test_flag debug then print_expr (* p_expr *) else print_expr) e;
    Irred e

and exec_match env t ebl =
  let rec iter ebl =
    match ebl with
    | [] ->
      eprintf "[Exec] Pattern matching not exhaustive in evaluation@.";
      assert false
    | (p,e)::rem ->
      try
        let env' = matching env t p.pp_pat in
        eval_expr env' e
      with NoMatch -> iter rem
  in
  iter ebl

and exec_call env rs args ity_result =
  let args' = List.map (fun pvs -> get_pvs env pvs) args in
  try
    match find_definition env rs with
    | Function(locals,d) ->
      let env = add_local_funs locals env in
      begin
        match d.c_node with
        | Capp (rs',pvl) ->
          exec_call env rs' (pvl @ args) ity_result
        | Cpur _ -> assert false (* TODO ? *)
        | Cany -> raise CannotCompute
        | Cfun body ->
          let pvsl = d.c_cty.cty_args in
          let env' = multibind_pvs pvsl args' env in
          Debug.dprintf debug
            "@[Evaluating function body of %s@]@."
            rs.rs_name.Ident.id_string;
          let r = eval_expr env' body
          in
          Debug.dprintf debug
            "@[Return from function %s@ result@ %a@]@."
            rs.rs_name.Ident.id_string print_logic_result r;
          r
      end
    | Builtin f ->
      Debug.dprintf debug
        "@[Evaluating builtin function %s@]@."
        rs.rs_name.Ident.id_string;
      let r = Normal (f rs (* env ity_result *) args') in
      Debug.dprintf debug
        "@[Return from builtin function %s result %a@]@."
        rs.rs_name.Ident.id_string
        print_logic_result r;
      r
    | Constructor _d ->
      Debug.dprintf debug
        "[interp] create record with type %a@."
        print_ity ity_result;
      (* FIXME : put a ref only on mutable fields *)
      let args' = List.map (fun v -> Fmutable (ref v)) args' in
      let v = Vconstr(rs,args') in
      Normal v
    | Projection _d ->
      match rs.rs_field, args' with
      | Some pv,[Vconstr(cstr,args)] ->
        let rec aux constr_args args =
          match constr_args,args with
          | pv2 :: pvl, v :: vl ->
            if pv_equal pv pv2 then Normal (field_get v) else
              aux pvl vl
          | _ -> raise CannotCompute
        in
        aux cstr.rs_cty.cty_args args
      | _ -> assert false
  with Not_found ->
    eprintf "[interp] cannot find definition of routine %s@."
      rs.rs_name.Ident.id_string;
    raise CannotCompute

let eval_global_expr env km locals e =
  get_builtin_progs env;
  let env = {
    known = km;
    funenv = Mrs.empty;
    vsenv = Mvs.empty;
  }
  in
  let add_glob _ d acc =
    match d.Pdecl.pd_node with
      | Pdecl.PDlet (LDvar (pvs,_)) ->
        (*
        eprintf "@[<hov 2>[interp] global:@ %s@]@."
          pvs.pv_vs.vs_name.Ident.id_string;
        *)
        let ity = pvs.pv_ity in
        let v = default_value_of_type env ity in
        Mvs.add pvs.pv_vs v acc
      | _ -> acc
  in
  let global_env =
    Ident.Mid.fold add_glob km Mvs.empty
  in
  let env = {
    known = km;
    funenv = Mrs.empty;
    vsenv = global_env;
  }
  in
  let env = add_local_funs locals env in
  let res = eval_expr env e in
  res, global_env

let init_real real_param =
  match real_param with
  | None -> ()
  | Some (emin, emax, prec) ->
      Big_real.init emin emax prec

(* real_param is used in case of real computation for the user to give the
   precision she wants to use *)
let eval_global_symbol ?real_param env m fmt rs =
  init_real real_param;
  try
    match find_global_definition m.Pmodule.mod_known rs with
    | Function(locals,d) ->
      begin
        match d.c_node with
        | Capp _ -> assert false (* TODO ? *)
        | Cpur _ -> assert false (* TODO ? *)
        | Cany -> assert false (* TODO ? *)
        | Cfun body ->
          begin
            fprintf fmt "@[<hov 2>   type:@ %a@]@."
              print_ity body.e_ity;
            let res, final_env =
              eval_global_expr env
                m.Pmodule.mod_known
                locals
                body
            in
            match res with
            | Normal _ ->
              fprintf fmt "@[<hov 2>   result:@ %a@\nglobals:@ %a@]@."
                print_logic_result res print_vsenv final_env
            | Excep _ ->
              fprintf fmt "@[<hov 2>exceptional result:@ %a@\nglobals:@ %a@]@."
                print_logic_result res print_vsenv final_env;
              exit 1
            | Irred _ | Fun _ ->
              fprintf fmt "@\n@]@.";
              eprintf "Execution error: %a@." print_logic_result res;
              exit 2
          end
      end
    | _ -> assert false
  with
  | Not_found ->
    eprintf "Symbol '%s' has no definition.@." rs.rs_name.Ident.id_string;
    exit 1
  | CannotFind (l, n, s) ->
    eprintf "Cannot find builtin symbol %s %s %s@." (List.fold_left (fun x y -> x^y) "" l) n s
