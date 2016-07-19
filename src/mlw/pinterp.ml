(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
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


module Nummap = Map.Make(BigInt)

type value =
  | Vconstr of rsymbol * field list
  | Vnum of BigInt.t
  | Vbool of bool
  | Vvoid
  | Varray of value array
(*
  | Vmap of value * value Nummap.t  (* default, elements *)
  | Vbin of binop * value * value
  | Veq of value * value
  | Vnot of value
  | Vif of value * term * term
  | Vquant of quant * term_quant
  | Veps of term_bound
  | Vcase of value * term_branch list
*)

and field = Fimmutable of value | Fmutable of value ref

let field_get f =
  match f with
  | Fimmutable v | Fmutable { contents = v } -> v

let constr rs vl =
  Vconstr(rs,List.map (fun v -> Fimmutable v) vl)

(*
let array_cons_rs = ref rs_void (* temporary *)
*)

let rec print_value fmt v =
  match v with
  | Vnum n ->
    if BigInt.ge n BigInt.zero then
      fprintf fmt "%s" (BigInt.to_string n)
    else
      fprintf fmt "(%s)" (BigInt.to_string n)
  | Vbool b ->
    fprintf fmt "%b" b
  | Vvoid ->
    fprintf fmt "()"
  | Varray a ->
    fprintf fmt "@[[%a]@]"
      (Pp.print_list Pp.comma print_value)
      (Array.to_list a)
(*
  | Vmap(def,m) ->
    fprintf fmt "@[[def=%a" print_value def;
    Nummap.iter
      (fun i v ->
        fprintf fmt ",@ %s -> %a" (BigInt.to_string i) print_value v)
      m;
    fprintf fmt "]@]"
*)
(*
  | Vconstr(ls,[Vnum len;Vmap(def,m)]) when rs_equal ls !array_cons_rs ->
    fprintf fmt "@[[";
    let i = ref BigInt.zero in
    while BigInt.lt !i len do
      let v =
        try Nummap.find !i m
        with Not_found -> def
      in
      if BigInt.gt !i BigInt.zero
      then fprintf fmt ",@ ";
      fprintf fmt "%a" print_value v;
      i := BigInt.succ !i
    done;
    fprintf fmt "]@]"
*)
  | Vconstr(rs,vl) when is_rs_tuple rs ->
    fprintf fmt "@[(%a)@]"
      (Pp.print_list Pp.comma print_field) vl
  | Vconstr(rs,[]) ->
    fprintf fmt "@[%a@]" print_rs rs
  | Vconstr(rs,vl) ->
    fprintf fmt "@[(%a %a)@]"
      print_rs rs (Pp.print_list Pp.space print_field) vl
(*
  | Vbin(op,v1,v2) ->
    fprintf fmt "@[(%a %a@ %a)@]"
      print_value v1 (Pretty.print_binop ~asym:false) op print_value v2
  | Veq(v1,v2) ->
    fprintf fmt "@[(%a =@ %a)@]" print_value v1 print_value v2
  | Vnot v ->
    fprintf fmt "@[(not@ %a)@]" print_value v
  | Vif(v,t1,t2) ->
    fprintf fmt "@[(if %a@ then %a@ else %a)@]"
      print_value v Pretty.print_term t1 Pretty.print_term t2
  | Vquant(q,tq) ->
    Pretty.print_term fmt (t_quant q tq)
  | Veps(tb) ->
    Pretty.print_term fmt (t_eps tb)
  | Vcase(v,_) ->
    fprintf fmt "@[match %a@ with ... end@]"
      print_value v
*)

and print_field fmt f = print_value fmt (field_get f)

(*
let v_eq v1 v2 = Veq(v1,v2)

let v_and v1 v2 =
  match (v1,v2) with
    | Vbool b1, Vbool b2 -> Vbool (b1 && b2)
    | _ -> Vbin(Tand,v1,v2)

let v_or v1 v2 =
  match (v1,v2) with
    | Vbool b1, Vbool b2 -> Vbool (b1 || b2)
    | _ -> Vbin(Tor,v1,v2)

let v_implies v1 v2 =
  match (v1,v2) with
    | Vbool b1, Vbool b2 -> Vbool (not b1 || b2)
    | _ -> Vbin(Timplies,v1,v2)

let v_iff v1 v2 =
  match (v1,v2) with
    | Vbool b1, Vbool b2 -> Vbool (b1 == b2)
    | _ -> Vbin(Tiff,v1,v2)

let v_not v =
  match v with
    | Vbool b -> Vbool (not b)
    | _ -> Vnot(v)

let v_if v t1 t2 = Vif(v,t1,t2)
*)

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

(*
let multibind_vs l tl env =
  try
    List.fold_right2 bind_vs l tl env
  with Invalid_argument _ -> assert false
*)

let bind_pvs pv v env = bind_vs pv.pv_vs v env

let multibind_pvs l tl env =
  try
    List.fold_right2 bind_pvs l tl env
  with Invalid_argument _ -> assert false


(* store *)

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
      | _ -> raise Undetermined


(* builtin symbols *)

(*
let builtins = Hls.create 17
*)

let ls_minus = ref rs_void (* temporary *)

exception NotNum

let big_int_of_const c =
  match c with
    | Number.ConstInt i -> Number.compute_int i
    | _ -> raise NotNum

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


(*
let must_be_true b =
  if b then true else raise Undetermined

let rec value_equality v1 v2 =
  match (v1,v2) with
    | Vnum i1, Vnum i2 -> BigInt.eq i1 i2
    | Vbool b1, Vbool b2 -> b1 == b2
    | Vconstr(ls1,vl1), Vconstr(ls2,vl2) ->
      must_be_true (ls_equal ls1 ls2 && List.for_all2 value_equality vl1 vl2)
    | Vbin(o1,v11,v12),Vbin(o2,v21,v22) ->
       must_be_true (o1 == o2 &&
                       value_equality v11 v21 && value_equality v12 v22)
    | Veq(v11,v12),Veq(v21,v22) ->
      must_be_true (value_equality v11 v21 && value_equality v12 v22)
    | Vnot v1, Vnot v2 ->
      must_be_true (value_equality v1 v2)
    | Vif(v1,t11,t12),Vif(v2,t21,t22) ->
      must_be_true (value_equality v1 v2 &&
                      t_equal t11 t21 && t_equal t12 t22)
    | Vquant(q1,t1),Vquant(q2,t2) ->
      must_be_true (q1 = q2 && t1 == t2)
    | Veps t1, Veps t2 ->
      must_be_true (t1 == t2)
    | Vcase(v1,b1),Vcase(v2,b2) ->
      must_be_true(value_equality v1 v2 && b1 == b2)
    | _ -> raise Undetermined

*)

(*
let eval_equ _ls l =
(*
  eprintf "[interp] eval_equ ? @.";
*)
  let res =
  match l with
  | [t1;t2] ->
    begin
      try Vbool(value_equality t1 t2)
      with Undetermined -> v_eq t1 t2
    end
  | _ -> assert false
  in
(*
  Format.eprintf "[interp] eval_equ: OK@.";
*)
  res

let eval_now ls l = constr ls l
*)

(* functions on map.Map *)

(*
let ts_map = ref Ty.ts_int

let builtin_map_type ts = ts_map := ts

let ls_map_const = ref ps_equ
let ls_map_get = ref ps_equ
let ls_map_set = ref ps_equ

let eval_map_const ls l =
  match l with
    | [d] -> Vmap(d,Nummap.empty)
    | _ -> constr ls l
*)

(*
let eval_map_get ls_get l =
  match l with
  | [m;x] ->
      (* eprintf "Looking for get:"; *)
    let rec find m =
      match m with
      | Vmap(def,m) ->
        begin
          match x with
          | Vnum i ->
            begin try Nummap.find i m
              with Not_found -> def
            end
          | _ -> assert false
        end
      | Vconstr(rs,[m';y;v]) when rs_equal rs !ls_map_set ->
        begin try
                if value_equality x y then
                  ((* Format.eprintf "ok!@.";*) v)
                else
                  ((* Format.eprintf "recur...@.";*) find m' )
          with Undetermined ->
              (* Format.eprintf "failed.@."; *)
            Vconstr(ls_get,[m;x])
        end
      | Vconstr(ls,[def]) when ls_equal ls !ls_map_const -> def
      | _ -> Vconstr(ls_get,[m;x])
    in find m
  | _ -> assert false
*)

(*
let eval_map_set ls_set l =
  match l with
  | [m;x;v] ->
    let rec compress m =
      match m with
      | Vmap(def,m) ->
        begin
          match x with
          | Vnum i -> Vmap(def,Nummap.add i v m)
          | _ -> assert false
        end
      | Vconstr(ls,[m';y;v']) when ls_equal ls !ls_map_set ->
        begin try
                if value_equality x y then
                  Vconstr(ls_set,[m';x;v])
                else
                  let c = compress m' in
                  Vconstr(ls_set,[c;y;v'])
          with Undetermined ->
            Vconstr(ls_set,[m;x;v])
        end
      | _ ->
        Vconstr(ls_set,[m;x;v])
    in compress m
  | _ -> assert false
*)

(* all builtin functions *)

(*
let built_in_theories =
  [ ["bool"],"Bool", [],
    [ "True", None, eval_true ;
      "False", None, eval_false ;
    ] ;
    ["int"],"Int", [],
    [ "infix +", None, eval_int_op BigInt.add;
      "infix -", None, eval_int_op BigInt.sub;
      "infix *", None, eval_int_op BigInt.mul;
      "prefix -", Some ls_minus, eval_int_uop BigInt.minus;
      "infix <", None, eval_int_rel BigInt.lt;
      "infix <=", None, eval_int_rel BigInt.le;
      "infix >", None, eval_int_rel BigInt.gt;
      "infix >=", None, eval_int_rel BigInt.ge;
    ] ;
    ["int"],"MinMax", [],
    [ "min", None, eval_int_op BigInt.min;
      "max", None, eval_int_op BigInt.max;
    ] ;
    ["int"],"ComputerDivision", [],
    [ "div", None, eval_int_op BigInt.computer_div;
      "mod", None, eval_int_op BigInt.computer_mod;
    ] ;
    ["int"],"EuclideanDivision", [],
    [ "div", None, eval_int_op BigInt.euclidean_div;
      "mod", None, eval_int_op BigInt.euclidean_mod;
    ] ;
(*
    ["map"],"Map", ["map", builtin_map_type],
    [ "get", Some ls_map_get, eval_map_get;
      "set", Some ls_map_set, eval_map_set;
    ] ;
    ["map"],"Const", [],
    [ "const", Some ls_map_const, eval_map_const ] ;
*)
  ]
*)

(*
let add_builtin_th env (l,n,t,d) =
  let th = Env.read_theory env l n in
  List.iter
    (fun (id,r) ->
      let ts = Theory.ns_find_ts th.Theory.th_export [id] in
      r ts)
    t;
  List.iter
    (fun (id,r,f) ->
      let ls = Theory.ns_find_ls th.Theory.th_export [id] in
      Hls.add builtins ls f;
      match r with
        | None -> ()
        | Some r -> r := ls)
    d

*)

(*
let get_builtins env =
(* no more generic equality
  Hls.add builtins ps_equ eval_equ;
*)
(*  Hls.add builtins Pwp.fs_now eval_now; *)
  List.iter (add_builtin_th env) built_in_theories
*)


(* promotes logic value v of program type ty into a program value,
   e.g if

     type t = { mutable a : int; c: int ; mutable b : int }

   then

     to_value (mk_t 1 43 2 : t <r1,r2>) =
        Vconstr(mk_t,[Vreg r1,Vnum 43, Vreg r2])

   with new regions in s

     <r1> -> Vnum 1
     <r2> -> Vnum 2

*)

(*
let rec to_program_value_rec env regions s ity ls vl =
  try
    let csl = Pdecl.inst_constructors env.tknown env.mknown ity in
    let rec find_cs csl =
      match csl with
      | [] -> assert false (* FIXME ? *)
      | (cs,fdl)::rem ->
        if ls_equal cs ls then
              (* we found the fields of that constructor *)
          begin
            let (s,regions,vl) =
              List.fold_left2
                (fun (s,regions,vl) fd v ->
                  match fd.fd_mut,regions with
                  | None,_ -> (* non mutable field, but
                                 some subfield may be mutable *)
                    begin
                      match v with
                      | Vconstr(ls1,vl1) ->
                        let s, regions, v =
                          to_program_value_rec env regions s fd.fd_ity ls1 vl1
                        in
                        (s,regions,v::vl)
                      | _ -> (s,regions,v::vl)
                    end
                  | Some _r, reg::regions ->
                        (* found a mutable field *)
                    let s' = Mreg.add reg v s in
                    (s',regions,Vreg reg :: vl)
                  | Some _, [] -> assert false)
                (s,regions,[]) fdl vl
            in
            s,regions,Vconstr(ls,List.rev vl)
          end
        else find_cs rem
    in find_cs csl
  with Not_found ->
        (* absurd, it would be a pure type *)
    assert false

let rec get_regions acc ity =
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityapp(its,tl,rl) ->
     List.map (get_reg env) rl
  | Itypur(ts,tl) ->
    *)

(*

let find_fields env ity ls =
  try
    let csl = [] (* Pdecl.inst_constructors env.tknown env.mknown ity *) in
    let rec find_cs csl =
      match csl with
      | [] -> assert false (* FIXME ? *)
      | (cs,fdl)::rem ->
        if ls_equal cs ls then fdl else find_cs rem
    in find_cs csl
  with Not_found ->
    (* absurd, [ity] would be a pure type *)
    assert false

let rec remove_prefix l r =
  match l,r with
  | _,[] -> l
  | [],_ -> assert false
  | r1::l,r2::r -> assert (r1 == r2); remove_prefix l r

let rec to_program_value env s ity v =
  match v with
  | Vconstr(ls,vl) ->
    if ity_immutable ity then [],s,v else
      begin
        let fdl = find_fields env ity ls in
        let targs,regions =
          match ity.ity_node with
          | Ityapp(_,tl,rl) -> tl, List.map (get_reg env) rl
          | Ityvar _ -> assert false
          | Ityreg reg -> [],[reg]
        in
        let s,v = to_program_value_list env s targs fdl regions ls vl in
        regions, s, v
      end
  | _ -> assert (ity_immutable ity); [], s,v

and to_program_value_list env s _tl fdl regions ls vl =
  let (s,regions,vl) =
    List.fold_left2
      (fun (s,regions,vl) fd v ->
        match fd.fd_mut,regions with
        | None,_ -> (* non mutable field, but
                       some subfield may be mutable *)
           let regs, s, v = to_program_value env s fd.fd_ity v in
           let rem_regs =
             match regions with
             | [] -> []
             | _ -> remove_prefix regions regs
           in
           (s,rem_regs,v::vl)
        | Some _r, reg::regions ->
          (* found a mutable field *)
          let s' = Mreg.add reg v s in
          (s',regions,Vreg reg :: vl)
        | Some _, [] -> assert false)
      (s,regions,[]) fdl vl
  in
  match regions with
  | [] -> s, Vconstr(ls,List.rev vl)
  | _ ->
    eprintf "@[<hov 2>error while converting logic value (%a) \
              to a program value:@ regions should be empty, not@ [%a]@]@."
      print_value (Vconstr(ls,vl))
      (Pp.print_list Pp.comma Ppretty.print_reg) regions;
    assert false


let to_program_value env s ty v =
  match ty with
  | VTarrow _ -> s,v
  | VTvalue ity ->
    if ity_immutable ity then s,v else
      let _regs,s,v = to_program_value env s ity v in
      s,v

*)

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

let exec_array_copy _ args =
  match args with
    | [Varray a] -> Varray(Array.copy a)
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


let built_in_modules =
  [
    ["bool"],"Bool", [],
    [ "True", None, eval_true ;
      "False", None, eval_false ;
    ] ;
    ["int"],"Int", [],
    [ "infix +", None, eval_int_op BigInt.add;
      (* defined as x+(-y)
         "infix -", None, eval_int_op BigInt.sub; *)
      "infix *", None, eval_int_op BigInt.mul;
      "prefix -", Some ls_minus, eval_int_uop BigInt.minus;
      "infix =", None, eval_int_rel BigInt.eq;
      "infix <", None, eval_int_rel BigInt.lt;
      "infix <=", None, eval_int_rel BigInt.le;
      "infix >", None, eval_int_rel BigInt.gt;
      "infix >=", None, eval_int_rel BigInt.ge;
    ] ;
    ["int"],"ComputerDivision", [],
    [ "div", None, eval_int_op BigInt.computer_div;
      "mod", None, eval_int_op BigInt.computer_mod;
    ] ;
   ["array"],"Array",
    ["array", builtin_array_type],
    ["make", None, exec_array_make ;
     "mixfix []", None, exec_array_get ;
     "length", None, exec_array_length ;
     "mixfix []<-", None, exec_array_set ;
     "copy", None, exec_array_copy ;
    ] ;
  ]

let add_builtin_mo env (l,n,t,d) =
  let mo = Pmodule.read_module env l n in
  let exp = mo.Pmodule.mod_export in
  let kn = mo.Pmodule.mod_known in
  List.iter
    (fun (id,r) ->
      let its = Pmodule.ns_find_its exp [id] in
      r kn its)
    t;
  List.iter
    (fun (id,r,f) ->
      let ps = Pmodule.ns_find_rs exp [id] in
      Hrs.add builtin_progs ps f;
      match r with
        | None -> ()
        | Some r -> r := ps)
    d

let get_builtin_progs lib =
  List.iter (add_builtin_mo lib) built_in_modules

(*
let get_vs env vs =
  try
    let t = Mvs.find vs env.vsenv in t
  with Not_found ->
    eprintf "logic variable %s not found in env@." vs.vs_name.Ident.id_string;
    assert false
*)

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

(*

let rec to_logic_value env s v =
  let eval_rec t = to_logic_value env s t in
  match v with
  | Vreg r -> Mreg.find (get_reg env r) s
  | Vnum _ | Vbool _ | Vvoid | Vmap _ -> v
  | Vbin(Tand,t1,t2) ->
    v_and (eval_rec t1) (eval_rec t2)
  | Vbin(Tor,t1,t2) ->
    v_or (eval_rec t1) (eval_rec t2)
  | Vbin(Timplies,t1,t2) ->
    v_implies (eval_rec t1) (eval_rec t2)
  | Vbin(Tiff,t1,t2) ->
    v_iff (eval_rec t1) (eval_rec t2)
  | Vnot t1 -> v_not (eval_rec t1)
  | Vconstr(ls,tl) ->
    eval_app env s ls (List.map eval_rec tl)
  | Veq (v1, v2) -> eval_equ ps_equ [v1;v2]
  | Vif(t1,t2,t3) ->
    let u = eval_rec t1 in
    begin match u with
    | Vbool true -> eval_term env s t2
    | Vbool false -> eval_term env s t3
    | _ -> v_if u t2 t3
    end
  | Vcase(t1,tbl) ->
(*
    eprintf "found a match ... with ...@.";
*)
    let u = eval_rec t1 in
    eval_match env s u tbl
  | Vquant(q,t) -> Vquant(q,t)
  | Veps t -> Veps t

and eval_term env s t =
  let eval_rec t = eval_term env s t in
  match t.t_node with
  | Tvar x ->
    begin
      try
        to_logic_value env s (get_vs env x)
      with Not_found -> assert false
    end
  | Tbinop(Tand,t1,t2) ->
    v_and (eval_rec t1) (eval_rec t2)
  | Tbinop(Tor,t1,t2) ->
    v_or (eval_rec t1) (eval_rec t2)
  | Tbinop(Timplies,t1,t2) ->
    v_implies (eval_rec t1) (eval_rec t2)
  | Tbinop(Tiff,t1,t2) ->
    v_iff (eval_rec t1) (eval_rec t2)
  | Tnot t1 -> v_not (eval_rec t1)
  | Tapp(ls,tl) ->
    eval_app env s ls (List.map eval_rec tl)
  | Tif(t1,t2,t3) ->
    let u = eval_rec t1 in
    begin match u with
    | Vbool true -> eval_term env s t2
    | Vbool false -> eval_term env s t3
    | _ -> v_if u t2 t3
    end
  | Tlet(t1,tb) ->
    let u = eval_rec t1 in
    let v,t2 = t_open_bound tb in
    eval_term (bind_vs v u env) s t2
  | Tcase(t1,tbl) ->
(*
    eprintf "found a match ... with ...@.";
*)
    let u = eval_rec t1 in
    eval_match env s u tbl
  | Tquant(q,t) -> Vquant(q,t)
  | Teps t -> Veps t
  | Tconst n -> Vnum (big_int_of_const n)
  | Ttrue -> Vbool true
  | Tfalse -> Vbool false





and eval_match env s u tbl =
  let rec iter tbl =
    match tbl with
    | [] ->
      eprintf "[Exec] fatal error: pattern matching not exhaustive in evaluation.@.";
      assert false
    | b::rem ->
      let p,t = t_open_branch b in
      try
        let env' = matching env u p in
        eval_term env' s t
      with NoMatch -> iter rem
  in
  try iter tbl with Undetermined ->
    Vcase(u,tbl)

and eval_app env s ls tl =
  try
    let f = Hls.find builtins ls in
    f ls tl
  with Not_found ->
    try
      let d = Ident.Mid.find ls.ls_name env.tknown in
      match d.Decl.d_node with
      | Decl.Dtype _ | Decl.Dprop _ -> assert false
      | Decl.Dlogic dl ->
        (* regular definition *)
        let d = List.assq ls dl in
        let l,t = Decl.open_ls_defn d in
        let env' = multibind_vs l tl env in
        eval_term env' s t
      | Decl.Dparam _ | Decl.Dind _ ->
        Vconstr(ls,tl)
      | Decl.Ddata dl ->
        (* constructor or projection *)
        match tl with
        | [ Vconstr(ls1,tl1) ] ->
          (* if ls is a projection and ls1 is a constructor,
             we should compute that projection *)
          let rec iter dl =
            match dl with
            | [] -> Vconstr(ls,tl)
            | (_,csl) :: rem ->
              let rec iter2 csl =
                match csl with
                | [] -> iter rem
                | (cs,prs) :: rem2 ->
                  if ls_equal cs ls1
                  then
                    (* we found the right constructor *)
                    let rec iter3 prs tl1 =
                      match prs,tl1 with
                      | (Some pr)::prs, t::tl1 ->
                        if ls_equal ls pr
                        then (* projection found! *) t
                        else
                          iter3 prs tl1
                      | None::prs, _::tl1 ->
                        iter3 prs tl1
                      | _ -> Vconstr(ls,tl)
                    in iter3 prs tl1
                  else iter2 rem2
              in iter2 csl
          in iter dl
        | _ -> Vconstr(ls,tl)
    with Not_found ->
      Format.eprintf "[Exec] definition of logic symbol %s not found@."
        ls.ls_name.Ident.id_string;
      Vconstr(ls,tl)

let to_logic_result env st res =
  match res with
    | Normal v -> Normal(to_logic_value env st v)
    | Excep(e,v) -> Excep(e,to_logic_value env st v)
    | Irred _ | Fun _ -> res

let eval_global_term env km t =
  get_builtins env;
  let env =
    { mknown = Ident.Mid.empty;
      tknown = km;
      funenv = Mps.empty;
      regenv = Mreg.empty;
      vsenv = Mvs.empty;
    }
  in
  eval_term env Mreg.empty t

*)

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
    | Ecase (_, _) -> fprintf fmt "@[Ecase(_,@ _)@]"
    | Eassign (pls, e1, reg, pvs) ->
      fprintf fmt "@[Eassign(%a,@ %a,@ %a,@ %a)@]"
        p_pls pls p_expr e1 Ppretty.print_reg reg p_pvs pvs
    | Eghost _ -> fprintf fmt "@[Eghost(_)@]"
    | Eany _ -> fprintf fmt "@[Eany(_)@]"
    | Eloop (_, _, _) -> fprintf fmt "@[Eloop(_,@ _,@ _)@]"
    | Efor (_, _, _, _) -> fprintf fmt "@[Efor(_,@ _,@ _,@ _)@]"
    | Eraise (_, _) -> fprintf fmt "@[Eraise(_,@ _)@]"
    | Etry (_, _) -> fprintf fmt "@[Etry(_,@ _)@]"
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

(*
let print_result env s fmt r =
  print_logic_result fmt (to_logic_result env s r)
*)

(*
let print_result env s fmt r =
  let env = {
    mknown = mkm;
    tknown = tkm;
    regenv = Mreg.empty;
    vsenv = Mvs.empty;
  }
  in
  print_result_aux env s fmt r
*)



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


(* evaluate expressions *)
let rec eval_expr env (e : expr) : result =
  match e.e_node with
(*
  | Elogic t ->
(*
    eprintf "@[<hov 2>[interp]before@ @[%a@]:@ vsenv =@ %a@ regenv=@ %a@ state=@ %a@]@."
      p_expr e print_vsenv env.vsenv print_regenv env.regenv print_state s;
*)
    let v = eval_term env s t in
    let s',v' = to_program_value env s e.e_vty v in
(*
    eprintf "@[<hov 2>[interp]after@ @[%a@]: state=@ %a@]@."
      p_expr e print_state s';
*)
    Normal v', s'
*)
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
  | Econst c -> Normal (Vnum (big_int_of_const c))
  | Eexec (ce,cty) ->
    assert (cty.cty_args = []);
    assert (ce.c_cty.cty_args = []);
    begin match ce.c_node with
    | Cpur _ -> assert false (* TODO ? *)
    | Cfun _ -> assert false (* TODO ? *)
    | Cany -> assert false (* TODO ? *)
    | Capp(rs,pvsl) -> exec_call env rs pvsl e.e_ity
    end
(*
      | Fun(ps,args,n), s' ->
        if n > 1 then
          Fun(ps,pvs::args,n-1), s'
        else
          let ity_result =
            match e.e_vty with
              | VTvalue ity -> ity
              | VTarrow _ -> assert false
          in
          begin
            try
              exec_app env s' ps (pvs::args) (*spec*) ity_result
            with CannotCompute -> Irred e, s
          end
      | _ -> Irred e, s
    end
  | Earrow ps ->
    let len = List.length ps.ps_aty.aty_args in
    Fun(ps,[],len),s
*)
  | Eassign l ->
    List.iter
      (fun (pvs,rs,value) ->
        let fld = Opt.get rs.rs_field in
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
  | Ecase(e1,ebl) ->
    begin
      match eval_expr env e1 with
        | Normal t ->
          begin try exec_match env t ebl
            with Undetermined -> Irred e
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
  | Efor(pvs,(pvs1,dir,pvs2),_inv,e1) ->
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
  | Etry(e1,el) ->
    begin
      let r = eval_expr env e1 in
      match r with
        | Excep(ex,t) ->
          begin
            let (vl,e2) = Mexn.find ex el in
            match vl with
            | [] ->
              (* assert (t = Vvoid); *)
              eval_expr env e2
            | [v] ->
              let env' = bind_vs v.pv_vs t env in
              eval_expr env' e2
            | _ -> assert false (* TODO ? *)
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
(*
  let args_ty = List.rev_map (fun pvs -> pvs.pv_ity) args in
*)
(*
  let subst =
    Ity.aty_vars_match ps.ps_subst ps.ps_aty args_ty ity_result
  in
  let subst = subst.ity_subst_reg in
  let subst = (* remove superfluous substitutions *)
    Mreg.filter (fun r1 r2 -> not (reg_equal r1 r2)) subst
  in
  let env1 = { env with regenv =
(*
      Mreg.union (fun _ x _ -> Some x) subst env.regenv }
*)
    Mreg.set_union subst env.regenv }
  in
*)
  try
    match find_definition env rs with
    | Function(locals,d) ->
      let env = add_local_funs locals env in
      begin
        match d.c_node with
        | Capp _ -> assert false (* TODO ? *)
        | Cpur _ -> assert false (* TODO ? *)
        | Cany -> raise Not_found (* try a built-in *)
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



let eval_global_symbol env m fmt rs =
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
  with Not_found ->
    eprintf "Symbol '%s' has no definition.@." rs.rs_name.Ident.id_string;
    exit 1


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3.byte"
End:
*)
