(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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

open Mlw_ty
open Mlw_ty.T
open Mlw_expr

module Nummap = Map.Make(BigInt)

type value =
  | Vapp of lsymbol * value list
  | Vnum of BigInt.t
  | Vbool of bool
  | Vvoid
  | Vreg of region
(*
  | Varray of Big_int.big_int * value * value Nummap.t
              (* length, default, elements *)
*)
  | Vmap of value * value Nummap.t
              (* default, elements *)
  | Vbin of binop * value * value
  | Veq of value * value
  | Vnot of value
  | Vif of value * term * term
  | Vquant of quant * term_quant
  | Veps of term_bound
  | Vcase of value * term_branch list

let array_cons_ls = ref ps_equ
let ls_true = ref ps_equ
let ls_false = ref ps_equ

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
  | Vreg reg -> Mlw_pretty.print_reg fmt reg
  | Vmap(def,m) ->
    fprintf fmt "@[[def=%a" print_value def;
    Nummap.iter
      (fun i v ->
        fprintf fmt ",@ %s -> %a" (BigInt.to_string i) print_value v)
      m;
    fprintf fmt "]@]"
  | Vapp(ls,[Vnum len;Vmap(def,m)]) when ls_equal ls !array_cons_ls ->
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
  | Vapp(ls,vl) when is_fs_tuple ls ->
    fprintf fmt "@[(%a)@]"
      (Pp.print_list Pp.comma print_value) vl
  | Vapp(ls,[]) ->
    fprintf fmt "@[%a@]" Pretty.print_ls ls
  | Vapp(ls,vl) ->
    fprintf fmt "@[(%a %a)@]"
      Pretty.print_ls ls (Pp.print_list Pp.space print_value) vl
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

type env = {
  mknown : Mlw_decl.known_map;
  tknown : Decl.known_map;
  funenv : Mlw_expr.fun_defn Mps.t;
  regenv : region Mreg.t;
  vsenv : value Mvs.t;
}

type state = value Mreg.t

let bind_vs v (t:value) env =
  { env with vsenv = Mvs.add v t env.vsenv }

let multibind_vs l tl env =
  try
    List.fold_right2 bind_vs l tl env
  with Invalid_argument _ -> assert false

let bind_pvs pv t env =
  { env with vsenv = Mvs.add pv.pv_vs t env.vsenv }

let multibind_pvs l tl env =
  try
    List.fold_right2 bind_pvs l tl env
  with Invalid_argument _ -> assert false


let p_regvar fmt (reg,t) =
  fprintf fmt "@[<hov 2><%a> -> %a@]"
    Mlw_pretty.print_reg reg Mlw_pretty.print_reg t

let print_regenv fmt s =
  let l = Mreg.bindings s in
  fprintf fmt "@[<v 0>%a@]" (Pp.print_list Pp.semi p_regvar) l


let get_reg env r =
  let rec aux n r =
    if n > 1000 then
      begin
        eprintf "@[<hov 2>looping region association ??? regenv =@ %a@]@."
          print_regenv env.regenv;
        assert false
      end;
    match Mreg.find_opt r env.regenv with
    | None -> r
    | Some r' -> aux (succ n) r'
  in aux 0 r



(* store *)


let p_reg fmt (reg,t) =
  fprintf fmt "@[<hov 2><%a> -> %a@]"
    Mlw_pretty.print_reg reg print_value t

let print_state fmt s =
  let l = Mreg.bindings s in
  fprintf fmt "@[<v 0>%a@]" (Pp.print_list Pp.semi p_reg) l

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

let rec matching env (t:value) p =
  match p.pat_node with
  | Pwild -> env
  | Pvar v -> bind_vs v t env
  | Por(p1,p2) ->
    begin
      try matching env t p1
      with NoMatch -> matching env t p2
    end
  | Pas(p,v) -> matching (bind_vs v t env) t p
  | Papp(ls1,pl) ->
    match t with
      | Vapp(ls2,tl) ->
        if ls_equal ls1 ls2 then
          List.fold_left2 matching env tl pl
        else
          if ls2.ls_constr > 0 then raise NoMatch
          else raise Undetermined
      | Vbool b ->
         let l = if b then !ls_true else !ls_false in
         if ls_equal ls1 l then env else raise NoMatch
      | _ -> raise Undetermined



(* builtin symbols *)

let builtins = Hls.create 17

let ls_minus = ref ps_equ (* temporary *)

exception NotNum

let big_int_of_const c =
  match c with
    | Number.ConstInt i -> Number.compute_int_constant i
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
        Vapp(ls,l)
    end
  | _ -> Vapp(ls,l)

let eval_int_uop op ls l =
  match l with
  | [Vnum i1] ->
    begin
      try Vnum (op i1)
      with NotNum ->
        Vapp(ls,l)
    end
  | _ -> Vapp(ls,l)

let eval_int_rel op ls l =
  match l with
  | [Vnum i1;Vnum i2] ->
    begin
      try Vbool (op i1 i2)
      with NotNum ->
        Vapp(ls,l)
    end
  | _ -> Vapp(ls,l)


let must_be_true b =
  if b then true else raise Undetermined

let rec value_equality v1 v2 =
  match (v1,v2) with
    | Vnum i1, Vnum i2 -> BigInt.eq i1 i2
    | Vbool b1, Vbool b2 -> b1 == b2
    | Vapp(ls1,vl1), Vapp(ls2,vl2) ->
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

let eval_equ _ls l =
(*
  eprintf "eval_equ ? @.";
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
  Format.eprintf "eval_equ: OK@.";
*)
  res

let eval_now ls l = Vapp(ls,l)

(* functions on map.Map *)

let ts_map = ref Ty.ts_int

let builtin_map_type ts = ts_map := ts

let ls_map_const = ref ps_equ
let ls_map_get = ref ps_equ
let ls_map_set = ref ps_equ

let eval_map_const ls l =
  match l with
    | [d] -> Vmap(d,Nummap.empty)
    | _ -> Vapp(ls,l)

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
      | Vapp(ls,[m';y;v]) when ls_equal ls !ls_map_set ->
        begin try
                if value_equality x y then
                  ((* Format.eprintf "ok!@.";*) v)
                else
                  ((* Format.eprintf "recur...@.";*) find m' )
          with Undetermined ->
              (* Format.eprintf "failed.@."; *)
            Vapp(ls_get,[m;x])
        end
      | Vapp(ls,[def]) when ls_equal ls !ls_map_const -> def
      | _ -> Vapp(ls_get,[m;x])
    in find m
  | _ -> assert false

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
      | Vapp(ls,[m';y;v']) when ls_equal ls !ls_map_set ->
        begin try
                if value_equality x y then
                  Vapp(ls_set,[m';x;v])
                else
                  let c = compress m' in
                  Vapp(ls_set,[c;y;v'])
          with Undetermined ->
            Vapp(ls_set,[m;x;v])
        end
      | _ ->
        Vapp(ls_set,[m;x;v])
    in compress m
  | _ -> assert false

(* all builtin functions *)

let built_in_theories =
  [ ["bool"],"Bool", [],
    [ "True", Some ls_true, eval_true ;
      "False", Some ls_false, eval_false ;
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
    ["map"],"Map", ["map", builtin_map_type],
    [ "get", Some ls_map_get, eval_map_get;
      "set", Some ls_map_set, eval_map_set;
    ] ;
    ["map"],"Const", [],
    [ "const", Some ls_map_const, eval_map_const ] ;
  ]

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

let get_builtins env =
  Hls.add builtins ps_equ eval_equ;
  Hls.add builtins Mlw_wp.fs_now eval_now;
  List.iter (add_builtin_th env) built_in_theories

(* promotes logic value v of program type ty into a program value,
   e.g if

     type t = { mutable a : int; c: int ; mutable b : int }

   then

     to_value (mk_t 1 43 2 : t <r1,r2>) =
        Vapp(mk_t,[Vreg r1,Vnum 43, Vreg r2])

   with new regions in s

     <r1> -> Vnum 1
     <r2> -> Vnum 2

*)

(*
let rec to_program_value_rec env regions s ity ls vl =
  try
    let csl = Mlw_decl.inst_constructors env.tknown env.mknown ity in
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
                      | Vapp(ls1,vl1) ->
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
            s,regions,Vapp(ls,List.rev vl)
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

let find_fields env ity ls =
  try
    let csl = Mlw_decl.inst_constructors env.tknown env.mknown ity in
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
  | Vapp(ls,vl) ->
    if ity_immutable ity then [],s,v else
      begin
        let fdl = find_fields env ity ls in
        let targs,regions =
          match ity.ity_node with
          | Ityapp(_,tl,rl) -> tl, List.map (get_reg env) rl
          | Ityvar _ -> assert false
          | Itypur(_,tl) -> tl, []
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
  | [] -> s, Vapp(ls,List.rev vl)
  | _ ->
    eprintf "@[<hov 2>error while converting logic value (%a) \
              to a program value:@ regions should be empty, not@ [%a]@]@."
      print_value (Vapp(ls,vl))
      (Pp.print_list Pp.comma Mlw_pretty.print_reg) regions;
    assert false


let to_program_value env s ty v =
  match ty with
  | VTarrow _ -> s,v
  | VTvalue ity ->
    if ity_immutable ity then s,v else
      let _regs,s,v = to_program_value env s ity v in
      s,v

let rec any_value_of_type env ty =
  match ty.Ty.ty_node with
  | Ty.Tyvar _ -> assert false
  | Ty.Tyapp(ts,_) when Ty.ts_equal ts Ty.ts_int ->
    let n = Random.int 199 - 99 in
    Vnum (BigInt.of_int n)
  | Ty.Tyapp(ts,_) when Ty.ts_equal ts Ty.ts_real ->
    Vvoid (* FIXME *)
  | Ty.Tyapp(ts,_) when Ty.ts_equal ts Ty.ts_bool ->
    Vbool(Random.bool ())
  | Ty.Tyapp(ts,_tyl) when Ty.is_ts_tuple ts ->
    Vvoid (* FIXME *)
  | Ty.Tyapp(ts,tyargs) ->
    try
      let csl = Decl.find_constructors env.tknown ts in
      match csl with
      | [] -> Vvoid (* FIXME *)
      | [cs,_] ->
        let ts_args = ts.Ty.ts_args in
        let subst = List.fold_left2
          (fun acc v t -> Ty.Mtv.add v t acc) Ty.Mtv.empty ts_args tyargs
        in
        let tyl = List.map (Ty.ty_inst subst) cs.ls_args in
        let vl = List.map (any_value_of_type env) tyl in
        Vapp(cs,vl)
      | (cs,_)::_rem -> (* FIXME *)
        let tyl = cs.ls_args in
        let vl = List.map (any_value_of_type env) tyl in
        Vapp(cs,vl)
    with Not_found -> Vvoid (* FIXME *)

type result =
  | Normal of value
  | Excep of xsymbol * value
  | Irred of expr
  | Fun of psymbol * pvsymbol list * int

let builtin_progs = Hps.create 17

let builtin_array_type kn its =
  let csl = Mlw_decl.find_constructors kn its in
  match csl with
    | [(pls,_)] -> array_cons_ls := pls.pl_ls
    | _ ->  assert false

let exec_array_make env s vty args =
  match args with
    | [Vnum n;def] ->
      let m = Vmap(def,Nummap.empty) in
      let v = Vapp(!array_cons_ls,[Vnum n;m]) in
      let s',v' = to_program_value env s vty v in
      Normal v',s'
    | _ ->
      raise CannotCompute

let exec_array_copy env s vty args =
  match args with
    | [Vapp(ls,[len;m])] when ls_equal ls !array_cons_ls ->
      begin
        match m with
          | Vreg r ->
            let m = Mreg.find r s in
            let v = Vapp(!array_cons_ls,[len;m]) in
            let s',v' = to_program_value env s vty v in
            Normal v',s'
          | _ -> raise CannotCompute
      end
    | _ ->
      raise CannotCompute

let exec_array_get _env s _vty args =
  match args with
    | [t;Vnum i] ->
      begin
        match t with
          | Vapp(ls,[_len;m]) when ls_equal ls !array_cons_ls ->
            begin
              match m with
              | Vreg r ->
                let m = Mreg.find r s in
                let t = eval_map_get !ls_map_get [m;Vnum i] in
(*
                eprintf
                  "exec_array_get (on reg %a)@ state =@ %a@ t[%a] -> %a@."
                  Mlw_pretty.print_reg r print_state s print_value (Vnum i) print_value t;
*)
                Normal t,s
              | _ -> raise CannotCompute
(*
                let t = eval_map_get !ls_map_get [m;Vnum i] in
                eprintf
                  "exec_array_get (on map %a)@ state =@ %a@ t[%a] -> %a@."
                  print_value m print_state s print_value (Vnum i) print_value t;
                Normal t,s
*)
            end
          | _ -> raise CannotCompute
      end
    | _ -> raise CannotCompute

let exec_array_length _env s _vty args =
  match args with
    | [t] ->
      begin
        match t with
          | Vapp(ls,[len;_m]) when ls_equal ls !array_cons_ls ->
            Normal len,s
          | _ -> raise CannotCompute
      end
    | _ -> raise CannotCompute

let exec_array_set _env s _vty args =
  match args with
    | [t;i;v] ->
      begin
        match t with
          | Vapp(ls,[_len;m]) when ls_equal ls !array_cons_ls ->
            begin
              match m with
              | Vreg r ->
                let m = Mreg.find r s in
(*
                eprintf
                  "exec_array_set (on reg %a)@ state =@ %a@ t[%a] -> %a@."
                  Mlw_pretty.print_reg r print_state s print_value i print_value t;
*)
                let t = eval_map_set !ls_map_set [m;i;v] in
                let s' =  Mreg.add r t s in
                Normal Vvoid,s'
(*
            let effs = spec.c_effect.eff_writes in
            let reg =
              if Sreg.cardinal effs = 1 then Sreg.choose effs
              else assert false
            in
            let reg =
              try Mreg.find reg env.regenv
              with Not_found -> reg
            in
            let s' = Mreg.add reg t s in
            eprintf "t[%a] <- %a (state = %a)@."
              print_value i print_value v print_state s';
            Normal Vvoid,s'
*)
              | _ -> raise CannotCompute
            end
          | _ -> raise CannotCompute
      end
    | _ -> assert false

let built_in_modules =
  [
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
  let mo = Mlw_module.read_module env l n in
  let exp = mo.Mlw_module.mod_export in
  let kn = mo.Mlw_module.mod_known in
  List.iter
    (fun (id,r) ->
      let its = Mlw_module.ns_find_its exp [id] in
      r kn its)
    t;
  List.iter
    (fun (id,r,f) ->
      let ps = Mlw_module.ns_find_ps exp [id] in
      Hps.add builtin_progs ps f;
      match r with
        | None -> ()
        | Some r -> r := ps)
    d

let get_builtin_progs lib =
  List.iter (add_builtin_mo lib) built_in_modules

let get_vs env vs =
  try
    let t = Mvs.find vs env.vsenv in t
  with Not_found ->
    eprintf "logic variable %s not found in env@." vs.vs_name.Ident.id_string;
    assert false

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
  | Vapp(ls,tl) ->
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
      eprintf "fatal error: pattern matching not exhaustive in evaluation.@.";
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
        Vapp(ls,tl)
      | Decl.Ddata dl ->
        (* constructor or projection *)
        match tl with
        | [ Vapp(ls1,tl1) ] ->
          (* if ls is a projection and ls1 is a constructor,
             we should compute that projection *)
          let rec iter dl =
            match dl with
            | [] -> Vapp(ls,tl)
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
                      | _ -> Vapp(ls,tl)
                    in iter3 prs tl1
                  else iter2 rem2
              in iter2 csl
          in iter dl
        | _ -> Vapp(ls,tl)
    with Not_found ->
      Format.eprintf "definition of logic symbol %s not found@."
        ls.ls_name.Ident.id_string;
      Vapp(ls,tl)

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


(* explicit printing of expr *)

let p_pvs fmt pvs =
  fprintf fmt "@[{ pv_vs =@ %a;@ pv_ity =@ %a;@ pv_ghost =@ %B }@]"
    Pretty.print_vs pvs.pv_vs Mlw_pretty.print_ity pvs.pv_ity
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
        Mlw_pretty.print_vty e.e_vty
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
        p_pls pls p_expr e1 Mlw_pretty.print_reg reg p_pvs pvs
    | Eghost _ -> fprintf fmt "@[Eghost(_)@]"
    | Eany _ -> fprintf fmt "@[Eany(_)@]"
    | Eloop (_, _, _) -> fprintf fmt "@[Eloop(_,@ _,@ _)@]"
    | Efor (_, _, _, _) -> fprintf fmt "@[Efor(_,@ _,@ _,@ _)@]"
    | Eraise (_, _) -> fprintf fmt "@[Eraise(_,@ _)@]"
    | Etry (_, _) -> fprintf fmt "@[Etry(_,@ _)@]"
    | Eabstr (_, _) -> fprintf fmt "@[Eabstr(_,@ _)@]"
    | Eassert (_, _) -> fprintf fmt "@[Eassert(_,@ _)@]"
    | Eabsurd -> fprintf fmt "@[Eabsurd@]"


let print_logic_result fmt r =
  match r with
    | Normal v ->
      fprintf fmt "@[%a@]" print_value v
    | Excep(x,v) ->
      fprintf fmt "@[exception %s(@[%a@])@]"
        x.xs_name.Ident.id_string print_value v
    | Irred e ->
      fprintf fmt "@[Cannot execute expression@ @[%a@]@]"
        Mlw_pretty.print_expr (* p_expr *) e
    | Fun _ ->
      fprintf fmt "@[Result is a function@]"

let print_result env s fmt r =
  print_logic_result fmt (to_logic_result env s r)

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

let find_definition env ps =
  try
    Some (Mps.find ps env.funenv)
  with
      Not_found ->
        Mlw_decl.find_definition env.mknown ps


(* evaluate expressions *)
let rec eval_expr env (s:state) (e : expr) : result * state =
  match e.e_node with
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
  | Evalue pvs ->
    begin
      try
        let t = get_pvs env pvs in (Normal t),s
      with Not_found -> assert false (* Irred e, s *)
    end
  | Elet(ld,e1) ->
    begin match ld.let_sym with
      | LetV pvs ->
        begin match eval_expr env s ld.let_expr with
          | Normal t,s' ->
            eval_expr (bind_pvs pvs t env) s' e1
          | r -> r
        end
      | LetA _ -> Irred e, s
    end
  | Eapp(e1,pvs,_spec) ->
    begin match eval_expr env s e1 with
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
  | Eif(e1,e2,e3) ->
    begin
(*
      eprintf "condition of the if : @?";
*)
      match eval_expr env s e1 with
        | Normal t, s' ->
          begin
            match t with
              | Vbool true -> eval_expr env s' e2
              | Vbool false -> eval_expr env s' e3
              | _ ->
              begin
                eprintf
                  "@[Cannot decide condition of if: @[%a@]@]@."
                  print_value t;
                Irred e, s
              end
          end
        | r -> r
    end
  | Eraise(xs,e1) ->
    begin
      let r,s' = eval_expr env s e1 in
      match r with
        | Normal t -> Excep(xs,t),s'
        | _ -> r,s'
    end
  | Etry(e1,el) ->
    begin
      let r = eval_expr env s e1 in
      match r with
        | Excep(ex,t), s' ->
          let rec find_exc l =
            match l with
              | [] -> r
              | (xs,pvs,e2)::rem ->
                if xs_equal ex xs then
                  let env' = bind_vs pvs.pv_vs t env in
                  eval_expr env' s' e2
                else find_exc rem
          in
          find_exc el
        | _ -> r
    end
  | Eloop(_inv,_var,e1) ->
    begin
      let r = eval_expr env s e1 in
      match r with
        | Normal _, s' -> eval_expr env s' e
        | _ -> r
    end
  | Efor(pvs,(pvs1,dir,pvs2),_inv,e1) ->
    begin
      try
        let a = big_int_of_value (get_pvs env (*s*) pvs1) in
        let b = big_int_of_value (get_pvs env (*s*) pvs2) in
        let le,suc = match dir with
          | To -> BigInt.le, BigInt.succ
          | DownTo -> BigInt.ge, BigInt.pred
        in
        let rec iter i s =
          Debug.dprintf debug "for loop with index = %s@."
            (BigInt.to_string i);
          if le i b then
            let env' = bind_vs pvs.pv_vs (Vnum i) env in
            match eval_expr env' s e1 with
              | Normal _,s' -> iter (suc i) s'
              | r -> r
          else Normal Vvoid, s
        in
        iter a s
      with
          NotNum -> Irred e,s
    end
  | Ecase(e1,ebl) ->
    begin
      match eval_expr env s e1 with
        | Normal t, s' ->
          begin try exec_match env t s' ebl
            with Undetermined -> Irred e, s
          end
        | r -> r
    end
  | Eassign(_pl,_e1,reg,pvs) ->
(*
    eprintf "@[<hov 2>[interp]before@ @[%a@]:@ regenv =@ %a@ state=@ %a@]@."
      p_expr e print_regenv env.regenv print_state s;
*)
    let t = get_pvs env pvs in
    let r = get_reg env reg in
(*
    eprintf "updating region <%a> with value %a@."
      Mlw_pretty.print_reg r print_value t;
*)
    let _ =
      try Mreg.find r s
      with Not_found ->
        Format.eprintf "region %a not found@." Mlw_pretty.print_reg r;
        assert false
    in
    let s' = Mreg.add r t s in
(*
    eprintf "@[<hov 2>[interp]after@ @[%a@]: state=@ %a@]@."
      p_expr e print_state s;
*)
    Normal Vvoid, s'
  | Eassert(_,t) ->
    (* TODO: do not eval t if no assertion check *)
    if true then (* noassert *) Normal Vvoid, s
    else
      begin match (eval_term env s t) with
      | Vbool true -> Normal Vvoid, s
      | Vbool false ->
        eprintf "@[Assertion failed at %a@]@."
          (Pp.print_option Pretty.print_loc) e.e_loc;
        Irred e, s
      | _ ->
        Warning.emit "@[Warning: assertion cannot be evaluated at %a@]@."
          (Pp.print_option Pretty.print_loc) e.e_loc;
        Normal Vvoid, s
      end
  | Eghost e1 ->
    (* TODO: do not eval ghost if no assertion check *)
    eval_expr env s e1
  | Erec (defs,e1) ->
    let env' =
      { env with funenv =
          List.fold_left
            (fun acc d -> Mps.add d.fun_ps d acc) env.funenv defs
      }
    in
    eval_expr env' s e1
  | Eany _
  | Eabstr _
  | Eabsurd ->
    eprintf "@[unsupported expression: @[%a@]@]@."
      (if Debug.test_flag debug then p_expr else Mlw_pretty.print_expr) e;
    Irred e, s

and exec_match env t s ebl =
  let rec iter ebl =
    match ebl with
    | [] ->
      eprintf "Pattern matching not exhaustive in evaluation@.";
      assert false
    | (p,e)::rem ->
      try
        let env' = matching env t p.ppat_pattern in
        eval_expr env' s e
      with NoMatch -> iter rem
  in
  iter ebl

and exec_app env s ps args (*spec*) ity_result =
  let args' = List.rev_map (fun pvs -> get_pvs env (*s*) pvs) args in
  let args_ty = List.rev_map (fun pvs -> pvs.pv_ity) args in
  let subst =
    Mlw_ty.aty_vars_match ps.ps_subst ps.ps_aty args_ty ity_result
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
  match find_definition env ps with
    | Some d ->
      let lam = d.fun_lambda in
      let env' = multibind_pvs lam.l_args args' env1 in
      Debug.dprintf debug
        "@[Evaluating function body of %s in regenv:@\n%a@\nand state:@\n%a@]@."
        ps.ps_name.Ident.id_string print_regenv env'.regenv
        print_state s;
      let r,s' = eval_expr env' s lam.l_expr
      in
      Debug.dprintf debug
        "@[Return from function %s@ result@ %a in state:@\n%a@]@."
        ps.ps_name.Ident.id_string
        (print_result env s') r
        print_state s';
      r,s'

    | None ->
        let f =
          try
            Hps.find builtin_progs ps
          with Not_found ->
            eprintf "definition of psymbol %s not found@."
              ps.ps_name.Ident.id_string;
            raise CannotCompute
        in
        Debug.dprintf debug
          "@[Evaluating builtin function %s in regenv:@\n%a@\nand state:@\n%a@]@."
          ps.ps_name.Ident.id_string print_regenv env1.regenv
          print_state s;
        let r,s' = f env1 (*spec*) s (VTvalue ity_result) args' in
        Debug.dprintf debug
            "@[Return from builtin function %s result %a in state:@\n%a@]@."
            ps.ps_name.Ident.id_string
            (print_result env s') r
            print_state s';
          r, s'




let eval_global_expr env mkm tkm _writes e =
(*
  eprintf "@[<hov 2>eval_global_expr:@ %a@]@."
    p_expr e;
*)
  get_builtins env;
  get_builtin_progs env;
  let env = {
    mknown = mkm;
    tknown = tkm;
    funenv = Mps.empty;
    regenv = Mreg.empty;
    vsenv = Mvs.empty;
  }
  in
  let add_glob _ d ((venv,renv) as acc) =
    match d.Mlw_decl.pd_node with
      | Mlw_decl.PDval (Mlw_expr.LetV pvs)
        when not (pv_equal pvs Mlw_decl.pv_old) ->
        let ity = pvs.pv_ity in
        let v = any_value_of_type env (ty_of_ity ity) in
        let renv,v = to_program_value env renv (VTvalue ity) v in
        (Mvs.add pvs.pv_vs v venv,renv)
      | _ -> acc
  in
  let init_env,init_state =
    Ident.Mid.fold add_glob mkm (Mvs.empty,Mreg.empty)
  in
  let env = {
    mknown = mkm;
    tknown = tkm;
    funenv = Mps.empty;
    regenv = Mreg.empty;
    vsenv = init_env;
  }
  in
  let res,st = eval_expr env init_state e in
  let final_env =
    Mvs.map (fun v -> to_logic_value env st v) init_env
  in
  let res = to_logic_result env st res in
  res, final_env



let eval_global_symbol env m fmt d =
  let lam = d.Mlw_expr.fun_lambda in
  match lam.Mlw_expr.l_args with
  | [pvs] when Mlw_ty.ity_equal pvs.Mlw_ty.pv_ity Mlw_ty.ity_unit ->
    begin
      let spec = lam.Mlw_expr.l_spec in
      let eff = spec.Mlw_ty.c_effect in
      let writes = eff.Mlw_ty.eff_writes in
      let body = lam.Mlw_expr.l_expr in
      fprintf fmt "@[<hov 2>   type:@ %a@]@."
        Mlw_pretty.print_vty body.Mlw_expr.e_vty;
            (* printf "effect: %a@\n" *)
            (*   Mlw_pretty.print_effect body.Mlw_expr.e_effect; *)
      let res, final_env =
        eval_global_expr env
          m.Mlw_module.mod_known m.Mlw_module.mod_theory.Theory.th_known
          writes lam.Mlw_expr.l_expr
      in
      match res with
        | Normal _ ->
          fprintf fmt "@[<hov 2>   result:@ %a@\nglobals:@ %a@]@."
            print_logic_result res print_vsenv final_env
(*
          fprintf fmt "@[<hov 2>  result:@ %a@\nstate :@ %a@]@."
            (print_result m.Mlw_module.mod_known
               m.Mlw_module.mod_theory.Theory.th_known st) res
            print_state st
*)
        | Excep _ ->
          fprintf fmt "@[<hov 2>exceptional result:@ %a@\nglobals:@ %a@]@."
            print_logic_result res print_vsenv final_env;
(*
          fprintf fmt "@[<hov 2>exceptional result:@ %a@\nstate:@ %a@]@."
            (print_result m.Mlw_module.mod_known
               m.Mlw_module.mod_theory.Theory.th_known st) res
            print_state st;
          *)
          exit 1
        | Irred _ | Fun _ ->
          fprintf fmt "@\n@]@.";
          eprintf "Execution error: %a@." print_logic_result res;
          exit 2
    end
  | _ ->
    eprintf "Only functions with one unit argument can be executed.@.";
    exit 1


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3.byte"
End:
*)
