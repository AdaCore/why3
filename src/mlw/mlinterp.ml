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

open Term
open Ty
open Decl
open Ident
open Mltree
open Expr
open Ity
open Wstdlib

let debug_interp = Debug.register_info_flag
                     ~desc:"Program interpretation"
                     "interp"
let debug_flamegraph = Debug.register_info_flag
                         ~desc:"Print callstacks from the interpreter in Flamegraph input format."
                         "interp_flamegraph"
type value =
  | Vconstr of rsymbol * field list
  | Vtuple of value list
  | Vbigint of BigInt.t
  | Vint of int
  | Vbool of bool
  | Vvoid
  | Varray of value array
  | Vmatrix of value array array
  | Vref of value ref

and field = Fimmutable of value | Fmutable of value ref

type info = {
    env : Env.env;
    mm  : Pmodule.pmodule Mstr.t;
    vars: value Mid.t;
    funs: decl Mrs.t;
    get_decl: rsymbol -> Mltree.decl;
    cur_rs: rsymbol; (* current function *)
    cs: rsymbol list; (* callstack for debugging/profiling *)
  }

exception CannotReduce (* internal failure *)
exception Raised of xsymbol * value option * rsymbol list (* Uncaught WhyML exception *)

open Number

let big_min_int = BigInt.of_int min_int
let big_max_int = BigInt.of_int max_int

let is_range_small_int ir =
  BigInt.le big_min_int ir.ir_lower && BigInt.le ir.ir_upper big_max_int

(* a value with a range type included in [min_int, max_int]
   can be interpreted as an int *)
let value_of_const ic ty =
  let bc = Number.compute_int_constant ic in
  match ty with
  | Some { ty_node = Tyapp ({ ts_def = Range ir }, [])}
       when is_range_small_int ir
    -> Vint (BigInt.to_int bc)
  | _ -> Vbigint bc

open Format

let rec print_value fmt = function
  | Vvoid -> fprintf fmt "()"
  | Vbool b -> fprintf fmt "%b" b
  | Vbigint i -> fprintf fmt "%a" Number.print_constant (Number.const_of_big_int i)
  | Vint i -> fprintf fmt "%d" i
  | Vtuple l -> fprintf fmt "@[<hov 2>(%a)@]"
                        (Pp.print_list Pp.comma print_value) l
  | Vconstr (rs, lf) -> fprintf fmt "@[<hov 2>(%a@ %a)@]"
                                Expr.print_rs rs
                                (Pp.print_list Pp.space print_field) lf
  | Varray a -> fprintf fmt "[|%a|]"
                        (Pp.print_list Pp.space print_value) (Array.to_list a)
  | Vmatrix m -> fprintf fmt "Vmatrix %a" print_matrix m
  | Vref r -> fprintf fmt "Vref %a" print_value !r

and print_field fmt = function
  | Fimmutable v -> fprintf fmt "%a" print_value v
  | Fmutable vr -> fprintf fmt "Fmutable %a" print_value !vr
and print_matrix fmt m =
  Array.iter (fun a -> fprintf fmt "[|%a|]\n"
                               (Pp.print_list Pp.space print_value)
                               (Array.to_list a)) m

let field_get f = match f with
  | Fimmutable v -> v
  | Fmutable v -> !v

let find_module_path env mm path m =
  Debug.dprintf debug_interp "find_module_path path %a m %s@."
                     (Pp.print_list Pp.space Pp.string) path m;
  match path with
  | [] -> Mstr.find m mm
  | path -> let mm = Env.read_library Pmodule.mlw_language env path in
            Mstr.find m mm

let find_module_id env mm id =
  let (path, m, _) = Pmodule.restore_path id in find_module_path env mm path m

let translate_module =
  let memo = Ident.Hid.create 16 in
  fun m ->
    let name = m.Pmodule.mod_theory.Theory.th_name in
    try Ident.Hid.find memo name with Not_found ->
      let pm = Compile.Translate.module_ m in
      let pm = Compile.Transform.module_ pm in
      Ident.Hid.add memo name pm;
      pm

exception Tuple
exception Constructor
exception Field

let get_decl env mm rs =
  let open Pdecl in
  Debug.dprintf debug_interp "get_decl@.";
  let id = rs.rs_name in
  Debug.dprintf debug_interp "looking for rs %s@." id.id_string;
  if is_rs_tuple rs then raise Tuple;
  let pm = find_module_id env mm id in
  Debug.dprintf debug_interp "pmodule %s@."
                              (pm.Pmodule.mod_theory.Theory.th_name.id_string);
  let tm = translate_module pm in
  let pd = Mid.find id tm.mod_from.from_km in
  match pd.pd_node with
  | PDtype l ->
     let rec aux = function
       | [] -> raise Not_found
       | d::t -> if List.mem rs d.itd_constructors then raise Constructor
                 else if List.mem rs d.itd_fields then raise Field
                 else aux t
     in
     aux l
  | _ -> Mid.find id tm.mod_known

let get_decl env mm = Wrs.memoize 17 (fun rs -> get_decl env mm rs)

let builtin_progs = Hrs.create 17

let eval_true _ _ = Vbool true
let eval_false _ _ = Vbool false

let eval_big_int_op op _ l =
  match l with
  | [Vbigint i1; Vbigint i2] ->
     (try Vbigint (op i1 i2) with Division_by_zero -> raise CannotReduce)
  | _ -> assert false

let eval_big_int_uop uop _ l =
  match l with
  | [Vbigint i] -> Vbigint (uop i)
  | _ -> assert false

let eval_big_int_rel r _ l =
  match l with
  | [Vbigint i1; Vbigint i2] ->
     Vbool (r i1 i2)
  | _ -> assert false

let eval_int_op op _ l =
  match l with
  | [Vint i1; Vint i2] ->
     (try Vint (op i1 i2) with Division_by_zero -> raise CannotReduce)
  | _ -> assert false

let eval_int_uop uop _ l =
  match l with
  | [Vint i] -> Vint (uop i)
  | _ -> assert false

let eval_int_rel r _ l =
  match l with
  | [Vint i1; Vint i2] ->
     Vbool (r i1 i2)
  | _ -> assert false

let eval_of_big_int _ l =
  match l with
  | [Vbigint i] ->
     begin try Vint (BigInt.to_int i)
     with Failure _ -> raise CannotReduce end
  | _ -> assert false

let exec_bigarray_make _ args =
  match args with
  | [Vbigint n;def] ->
     begin
       try
         let n = BigInt.to_int n in
         let v = Varray(Array.make n def) in
         v
       with _ -> raise CannotReduce
     end
  | _ ->
     assert false

let exec_bigarray_copy _ args =
  match args with
  | [Varray a] -> Varray(Array.copy a)
  | _ ->
     assert false

let exec_bigarray_get _ args =
  match args with
  | [Varray a;Vbigint i] ->
     begin
       try
         a.(BigInt.to_int i)
       with _ -> raise CannotReduce
     end
  | _ -> assert false

let exec_bigarray_length _ args =
  match args with
  | [Varray a] -> Vbigint (BigInt.of_int (Array.length a))
  | _ -> assert false

let exec_bigarray_set _ args =
  match args with
  | [Varray a;Vbigint i;v] ->
     begin
       try
         a.(BigInt.to_int i) <- v;
         Vvoid
       with _ -> raise CannotReduce
     end
  | _ -> assert false

let exec_array_make _ args =
  match args with
  | [Vint n;def] -> Varray(Array.make n def)
  | _ -> assert false

let exec_array_copy _ args =
  match args with
  | [Varray a] -> Varray(Array.copy a)
  | _ -> assert false

let exec_array_get _ args =
  match args with
  | [Varray a;Vint i] -> a.(i)
  | _ -> assert false

let exec_array_length _ args =
  match args with
  | [Varray a] -> Vint (Array.length a)
  | _ -> assert false

let exec_array_set _ args =
  match args with
  | [Varray a;Vint i;v] ->
     a.(i) <- v;
     Vvoid
  | _ -> assert false

let exec_bigmatrix_make _ args =
  match args with
  | [Vbigint r; Vbigint c; def] ->
     begin
       try
         let r = BigInt.to_int r in
         let c = BigInt.to_int c in
         Vmatrix(Array.make_matrix r c def)
       with _ -> raise CannotReduce
     end
  | _ -> assert false

let exec_bigmatrix_get _ args =
  match args with
  | [Vmatrix m; Vbigint i; Vbigint j] ->
     begin
       try
         m.(BigInt.to_int i).(BigInt.to_int j)
       with _ -> raise CannotReduce
     end
  | _ -> assert false

let exec_bigmatrix_set _ args =
  match args with
  | [Vmatrix m; Vbigint i; Vbigint j; v] ->
     begin
       try
         m.(BigInt.to_int i).(BigInt.to_int j) <- v;
         Vvoid
       with _ -> raise CannotReduce
     end
  | _ -> assert false

let exec_bigmatrix_rows _ args =
  match args with
  | [Vmatrix m] -> Vbigint (BigInt.of_int (Array.length m))
  | _ -> raise CannotReduce

(* FIXME fails if rows=0 *)
let exec_bigmatrix_cols _ args =
  match args with
  | [Vmatrix m] ->
     begin
       try Vbigint (BigInt.of_int (Array.length m.(0)))
       with _ -> raise CannotReduce
     end
  | _ -> assert false

let exec_bigmatrix_copy _ args =
  match args with
  | [Vmatrix m] ->
     let a = Array.copy m in
     for i = 0 to (Array.length m - 1) do
       a.(i) <- Array.copy m.(i)
     done;
     Vmatrix a
  | _ -> assert false

let exec_matrix_make _ args =
  match args with
  | [Vint r; Vint c; def] ->
     begin
       try
         Vmatrix(Array.make_matrix r c def)
       with _ -> raise CannotReduce
     end
  | _ -> assert false

let exec_matrix_get _ args =
  match args with
  | [Vmatrix m; Vint i; Vint j] -> m.(i).(j)
  | _ -> assert false

let exec_matrix_set _ args =
  match args with
  | [Vmatrix m; Vint i; Vint j; v] ->
     m.(i).(j) <- v;
     Vvoid
  | _ -> assert false

let exec_matrix_rows _ args =
  match args with
  | [Vmatrix m] -> Vint (Array.length m)
  | _ -> assert false

(* FIXME fails if rows=0 *)
let exec_matrix_cols _ args =
  match args with
  | [Vmatrix m] ->
     Vint (Array.length m.(0))
  | _ -> assert false

let exec_matrix_copy _ args =
  match args with
  | [Vmatrix m] ->
     let a = Array.copy m in
     for i = 0 to (Array.length m - 1) do
       a.(i) <- Array.copy m.(i)
     done;
     Vmatrix a
  | _ -> assert false

let exec_ref_make _ args =
  match args with
  | [v] ->
     Vref (ref v)
  | _ -> assert false

let exec_ref_get _ args =
  match args with
  | [Vref r] -> !r
  | _ -> assert false

let exec_ref_set _ args =
  match args with
  | [Vref r; v] ->
     r := v;
     Vvoid
  | _ -> assert false

let exec_print _ args =
  List.iter (eprintf "%a@." print_value) args;
  Vvoid


let built_in_modules =
  [
    ["why3"; "Bool"],"Bool", [],
    [ "True", eval_true ;
      "False", eval_false ;
    ] ;
    ["int"],"Int", [],
    [ Ident.op_infix "+", eval_big_int_op BigInt.add;
      (* defined as x+(-y)
         Ident.op_infix "-", eval_big_int_op BigInt.sub; *)
      Ident.op_infix "*", eval_big_int_op BigInt.mul;
      Ident.op_prefix "-", eval_big_int_uop BigInt.minus;
      Ident.op_infix "=", eval_big_int_rel BigInt.eq;
      Ident.op_infix "<", eval_big_int_rel BigInt.lt;
      Ident.op_infix "<=", eval_big_int_rel BigInt.le;
      Ident.op_infix ">", eval_big_int_rel BigInt.gt;
      Ident.op_infix ">=", eval_big_int_rel BigInt.ge;
    ] ;
    ["int"],"MinMax", [],
    [ "min", eval_big_int_op BigInt.min;
      "max", eval_big_int_op BigInt.max;
    ] ;
    ["int"],"ComputerDivision", [],
    [ "div", eval_big_int_op BigInt.computer_div;
      "mod", eval_big_int_op BigInt.computer_mod;
    ] ;
    ["int"],"EuclideanDivision", [],
    [ "div", eval_big_int_op BigInt.euclidean_div;
      "mod", eval_big_int_op BigInt.euclidean_mod;
    ] ;
    ["mach";"int"],"Int31",[],
    [ Ident.op_infix "+", eval_int_op (+);
      Ident.op_infix "-", eval_int_op (-);
      Ident.op_infix "*", eval_int_op ( * );
      Ident.op_infix "/", eval_int_op (/);
      Ident.op_infix "%", eval_int_op (mod);
      Ident.op_prefix "-", eval_int_uop (~-);
      Ident.op_infix "=", eval_int_rel (=);
      Ident.op_infix "<", eval_int_rel (<);
      Ident.op_infix "<=", eval_int_rel (<=);
      Ident.op_infix ">", eval_int_rel (>);
      Ident.op_infix ">=", eval_int_rel (>=);
      "of_int", eval_of_big_int;
    ] ;
    ["mach";"int"],"Int32",[],
    [ Ident.op_infix "+", eval_int_op (+);
      Ident.op_infix "-", eval_int_op (-);
      Ident.op_infix "*", eval_int_op ( * );
      Ident.op_infix "/", eval_int_op (/);
      Ident.op_infix "%", eval_int_op (mod);
      Ident.op_prefix "-", eval_int_uop (~-);
      Ident.op_infix "=", eval_int_rel (=);
      Ident.op_infix "<", eval_int_rel (<);
      Ident.op_infix "<=", eval_int_rel (<=);
      Ident.op_infix ">", eval_int_rel (>);
      Ident.op_infix ">=", eval_int_rel (>=);
      "of_int", eval_of_big_int;
    ] ;
    ["mach";"int"],"Int63",[],
    [ Ident.op_infix "+", eval_int_op (+);
      Ident.op_infix "-", eval_int_op (-);
      Ident.op_infix "*", eval_int_op ( * );
      Ident.op_infix "/", eval_int_op (/);
      Ident.op_infix "%", eval_int_op (mod);
      Ident.op_prefix "-", eval_int_uop (~-);
      Ident.op_infix "=", eval_int_rel (=);
      Ident.op_infix "<", eval_int_rel (<);
      Ident.op_infix "<=", eval_int_rel (<=);
      Ident.op_infix ">", eval_int_rel (>);
      Ident.op_infix ">=", eval_int_rel (>=);
      "of_int", eval_of_big_int;
    ] ;
    ["array"],"Array", [],
    ["make", exec_bigarray_make ;
     "length", exec_bigarray_length ;
     Ident.op_get "", exec_bigarray_get ;
     Ident.op_set "", exec_bigarray_set ;
     "copy", exec_bigarray_copy ;
    ] ;
    ["mach"; "array"],"Array31", [],
    ["make", exec_array_make ;
     "length", exec_array_length ;
     Ident.op_get "", exec_array_get ;
     Ident.op_set "", exec_array_set ;
     "copy", exec_array_copy ;
    ] ;
    ["mach"; "array"],"Array32", [],
    ["make", exec_array_make ;
     "length", exec_array_length ;
     Ident.op_get "", exec_array_get ;
     Ident.op_set "", exec_array_set ;
     "copy", exec_array_copy ;
    ] ;
    ["mach"; "array"],"Array63", [],
    ["make", exec_array_make ;
     "length", exec_array_length ;
     Ident.op_get "", exec_array_get ;
     Ident.op_set "", exec_array_set ;
     "copy", exec_array_copy ;
    ] ;
    ["matrix"],"Matrix", [],
    ["make", exec_bigmatrix_make ;
     "get", exec_bigmatrix_get ;
     "rows", exec_bigmatrix_rows ;
     "columns", exec_bigmatrix_cols ;
     "set", exec_bigmatrix_set ;
     "copy", exec_bigmatrix_copy ;
    ] ;
    ["mach"; "matrix"],"Matrix63", [],
    ["make", exec_matrix_make ;
     "get", exec_matrix_get ;
     "rows", exec_matrix_rows ;
     "columns", exec_matrix_cols ;
     "set", exec_matrix_set ;
     "copy", exec_matrix_copy ;
    ] ;
    ["why3"; "Ref"],"Ref", [],
    ["ref", exec_ref_make ;
     "mk ref", exec_ref_make ;
     "contents", exec_ref_get ;
    ] ;
    ["ref"],"Ref", [],
    [Ident.op_prefix "!", exec_ref_get;
     Ident.op_infix ":=", exec_ref_set;
    ] ;
    ["debug"],"Debug", [],
    ["print", exec_print ] ;
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
    (fun (id,f) ->
      let ps = Pmodule.ns_find_rs exp [id] in
      Hrs.add builtin_progs ps f)
    d

let get_builtin_progs lib =
  List.iter (add_builtin_mo lib) built_in_modules

let ts = ref 0. (* timestamp for current callstack *)

let print_callstack cs time =
  Format.eprintf "%a %d@."
    (Pp.print_list (fun fmt () -> Format.fprintf fmt ";") Expr.print_rs)
    (List.rev cs)
    (int_of_float (time *. 100000000.))

let cs_push info rs =
  let new_cs = rs :: info.cs in
  if Debug.test_flag debug_flamegraph
  then begin
    let ts_end = Unix.gettimeofday () in
    print_callstack info.cs (ts_end -. !ts);
    ts := Unix.gettimeofday ();
    { info with cur_rs = rs; cs = new_cs }
    end
  else { info with cur_rs = rs; cs = new_cs }

let cs_pop info =
  if Debug.test_flag debug_flamegraph
  then begin
    let ts_end = Unix.gettimeofday () in
    print_callstack info.cs (ts_end -. !ts);
    ts := Unix.gettimeofday () end

let get pv info : value =  Mid.find pv.pv_vs.vs_name info.vars

let add_id id v info = {info with vars = Mid.add id v info.vars}
let add_vs vs = add_id vs.vs_name
let add_pv pv = add_vs pv.pv_vs

let add_fundecl rs decl info =
  Debug.dprintf debug_interp "adding decl for %s@." rs.rs_name.id_string;
  { info with funs = Mrs.add rs decl info.funs }

exception NoMatch

let rec matching info v pat =
  match pat with
  | Pwild -> info
  | Pvar vs -> add_vs vs v info
  | Ptuple pl ->
     begin match v with
     | Vtuple l ->
        List.fold_left2 matching info l pl
     | _ -> assert false
     end
  | Por (p1, p2) ->
     begin try matching info v p1 with NoMatch -> matching info v p2 end
  | Pas (p, vs) -> add_vs vs v (matching info v p)
  | Papp (ls, pl) ->
     match v with
     | Vconstr ({rs_logic = RLls ls2}, l) ->
        if ls_equal ls ls2 then
          List.fold_left2 matching info (List.map field_get l) pl
        else if ls2.ls_constr > 0 then raise NoMatch
        else assert false
     | Vbool b ->
        let ls2 = if b then fs_bool_true else fs_bool_false in
        if ls_equal ls ls2 then info else raise NoMatch
     | _ -> raise CannotReduce (* FIXME more cases ? *)

let rec interp_expr info (e:Mltree.expr) : value =
  Mltree.(match e.e_node with
  | Econst nc ->
     begin match e.e_ity with
     | I i -> value_of_const nc (Some (ty_of_ity i))
     | _ -> assert false
     end
  | Evar pv ->
     (try get pv info
      with Not_found ->
        Debug.dprintf debug_interp "var %a not found@." print_pv pv;
           raise CannotReduce)
  | Eapp (rs, le) -> begin
      Debug.dprintf debug_interp "Eapp %a@." Expr.print_rs rs;
      let eval_call info vl e rs =
        Debug.dprintf debug_interp "eval params@.";
        let info' =
          List.fold_left2
            (fun info e (id, _ty, ig) ->
              assert (not ig);
              let v = interp_expr info e in
              Debug.dprintf debug_interp "arg %s : %a@."
                id.id_string print_value v;
              add_id id v info)
            info le vl in
        if rs_equal rs info.cur_rs
        then interp_expr info' e
        else begin
          let info' = cs_push info' rs in
          let v = interp_expr info' e in
          cs_pop info';
          v end in
      Debug.dprintf debug_interp "eval call@.";
      let res = try begin
        if Hrs.mem builtin_progs rs
        then
          (Debug.dprintf debug_interp "%a is builtin@." Expr.print_rs rs;
          let f = Hrs.find builtin_progs rs in
          f rs (List.map (interp_expr info) le))
        else begin
          let decl = try Mrs.find rs info.funs
                     with Not_found -> info.get_decl rs in
          Debug.dprintf debug_interp "decl found@.";
          match decl with
          | Dlet (Lsym (rs, _ty, vl, e)) ->
             eval_call info vl e rs
          | Dlet(Lrec([{rec_args = vl; rec_exp = e;
                        rec_sym = rs; rec_res=_ty}])) ->
             eval_call info vl e rs
          | Dlet (Lrec _) ->
             Debug.dprintf
               debug_interp "unhandled mutually recursive functions@.";
             raise CannotReduce
          | Dlet (Lvar _) ->
             Debug.dprintf debug_interp "Lvar@."; raise CannotReduce
          | Dlet (Lany _) ->
             Debug.dprintf debug_interp "Lany@."; raise CannotReduce
          | _ -> Debug.dprintf debug_interp "not a let decl@.";
                 raise CannotReduce
          end
                  end
      with
      | Constructor ->
         Debug.dprintf debug_interp "constructor@.";
         let field_of_expr pv e =
           let is_mutable = match pv.pv_ity.ity_node with
             | Ityreg _ -> true
             | _ -> false
           in
           let v = interp_expr info e in
           if is_mutable then Fmutable (ref v) else Fimmutable v
         in
         Vconstr(rs, List.map2 field_of_expr rs.rs_cty.cty_args le)
      | Tuple ->
         Debug.dprintf debug_interp "tuple@.";
         Vtuple (List.map (interp_expr info) le)
      | Field ->
         Debug.dprintf debug_interp "field@.";
         (* TODO keep field info when applying constructors, use here ?*)
         raise CannotReduce
      | Not_found ->
         Debug.dprintf debug_interp "decl not found@.";
         raise CannotReduce
      in
      Debug.dprintf debug_interp "result: %a@." print_value res;
      res
    end
  | Efun _ -> Debug.dprintf debug_interp "Efun@."; raise CannotReduce
  | Elet (Lvar(pv, e), ein) ->
     let v = interp_expr info e in
     interp_expr (add_pv pv v info) ein
  | Eif (c, th, el) ->
     begin match interp_expr info c with
     | Vbool true -> interp_expr info th
     | Vbool false -> interp_expr info el
     | _ -> raise CannotReduce
     end
  | Eassign l ->
     List.iter
       (fun (pvs, rs, e) ->
         let fld = fd_of_rs rs in
         let value = interp_expr info e in
         match get pvs info with
         | Vconstr(c, args) ->
            let rec aux cargs args =
              match cargs, args with
              | pv :: pvl, v :: vl ->
                 if pv_equal pv fld then
                   match v with
                   | Fmutable r -> r := value
                   | Fimmutable _ -> assert false
                 else
                   aux pvl vl
              | _ -> assert false
            in
            aux c.rs_cty.cty_args args
         | _ -> assert false)
       l;
     Vvoid
  | Eblock l ->
     List.fold_left
       (fun _ e -> interp_expr info e) (*ignore all but last result*)
       Vvoid l
  | Eignore e -> ignore (interp_expr info e); Vvoid
  | Ewhile (c, b) ->
     Debug.dprintf debug_interp "while@.";
     begin match interp_expr info c with
     | Vbool true ->
        ignore (interp_expr info b);
        interp_expr info e
     | Vbool false -> Vvoid
     | _ -> assert false end
  | Efor (x, pv1, dir, pv2, e) ->
     Debug.dprintf debug_interp "for@.";
     begin match (get pv1 info, get pv2 info) with
     | (Vbigint i1, Vbigint i2) ->
        if dir = To
        then
          for i = BigInt.to_int i1 to BigInt.to_int i2 do
            ignore (interp_expr (add_pv x (Vbigint (BigInt.of_int i)) info) e)
          done
        else
          for i = BigInt.to_int i1 downto BigInt.to_int i2 do
            ignore (interp_expr (add_pv x (Vbigint (BigInt.of_int i)) info) e)
          done;
        Vvoid
     | (Vint i1, Vint i2) ->
        if dir = To
        then
          for i = i1 to i2 do
            ignore (interp_expr (add_pv x (Vint i) info) e)
          done
        else
          for i = i1 downto i2 do
            ignore (interp_expr (add_pv x (Vint i) info) e)
          done;
        Vvoid
     | _ -> Debug.dprintf debug_interp "Non-integer for bounds@.";
            raise CannotReduce
     end
  | Elet (Lany _,_) -> Debug.dprintf debug_interp "unhandled Lany@.";
                       raise CannotReduce
  | Elet ((Lsym(rs,_,_,_) as ld), e) ->
     interp_expr (add_fundecl rs (Dlet ld) info) e
  | Elet ((Lrec rdl as ld), e) ->
     let info = List.fold_left
                  (fun info rd -> add_fundecl rd.rec_sym (Dlet ld) info)
                  info rdl in
     interp_expr info e
  | Eraise (xs, oe)  ->
     Debug.dprintf debug_interp "Eraise %s@." xs.xs_name.id_string;
     let ov = match oe with
       | None -> None
       | Some e -> Some (interp_expr info e) in
     raise (Raised (xs, ov, info.cs))
  | Eexn  _ -> Debug.dprintf debug_interp "Eexn@.";
                         raise CannotReduce
  | Eabsurd -> Debug.dprintf debug_interp "Eabsurd@.";
               raise CannotReduce
  | Ematch (e, l, bl) ->
     Debug.dprintf debug_interp "Ematch@.";
     begin match interp_expr info e with
     | v ->
          Debug.dprintf debug_interp "value %a@." print_value v;
          if l = [] then v else
          let rec aux = function
            | [] -> assert false
            | (p,e)::tl ->
                try
                  let info' = matching info v p in
                  interp_expr info' e
                with NoMatch -> aux tl
          in
          aux l
     | exception (Raised (xs, ov, _) as e) ->
          if bl = [] then raise e else
          let rec aux = function
            | [] -> Debug.dprintf debug_interp "Etry: uncaught exception@.";
                    raise e
            | (xs', pvl, e) :: bl ->
               if xs_equal xs xs'
               then begin
                 match pvl, ov with
                 | [], None -> interp_expr info e
                 | l, Some (Vtuple l') when (List.length l = List.length l') ->
                    let info = List.fold_left2 (fun info pv v -> add_pv pv v info)
                                               info l l' in
                    interp_expr info e
                 | [pv], Some v ->
                    interp_expr (add_pv pv v info) e
                 | _ -> Debug.dprintf debug_interp "Etry: bad arity@.";
                        aux bl end
               else aux bl
          in
          aux bl
      end)

let rec value_of_term kn t =
  Debug.dprintf debug_interp "value of term %a@." Pretty.print_term t;
  match t.t_node with
  | Ttrue -> Vbool true
  | Tfalse -> Vbool false
  | Term.Tapp (ls, lp) when ls.ls_constr > 0 ->
     let rs = restore_rs ls in
     if is_rs_tuple rs
     then Vtuple (List.map (value_of_term kn) lp)
     else Vconstr ((restore_rs ls),
                   (List.map (fun t -> Fimmutable (value_of_term kn t)) lp))
  | Tnot t -> begin match value_of_term kn t with
              | Vbool b -> Vbool (not b)
              | _ -> assert false end
  (* TODO Tbinop maybe *)
  | Tconst (Number.ConstInt ic) -> value_of_const ic t.t_ty
  | Term.Tapp (ls,[]) ->
     begin match find_logic_definition kn ls with
     | None -> raise CannotReduce
     | Some ld ->
        let _,t = open_ls_defn ld in
        value_of_term kn t
     end
  | _ -> raise CannotReduce

let rec term_of_value = function
  | Vbool true -> t_bool_true
  | Vbool false -> t_bool_false
  | Vbigint i -> t_bigint_const i
  | Vint _ -> raise CannotReduce
  | Vtuple l -> t_tuple (List.map term_of_value l)
  | Vconstr (rs, lf) ->
     t_app (ls_of_rs rs) (List.map (fun f -> term_of_value (field_get f)) lf)
           (ls_of_rs rs).ls_value
  | Vvoid -> t_void
  | Vref _ -> raise CannotReduce (* TODO ? *)
  | Varray _ -> raise CannotReduce
  | Vmatrix _ -> raise CannotReduce

let init_info env mm rs vars =
  { env = env;
    mm = mm;
    funs = Mrs.empty;
    vars = vars;
    get_decl = get_decl env mm;
    cur_rs = rs;
    cs = []; }

let interp env mm rs vars =
  get_builtin_progs env;
  let info = init_info env mm rs vars in
  if Debug.test_flag debug_flamegraph then ts := Unix.gettimeofday ();
  let decl = info.get_decl rs in
  match decl with
  | Dlet (Lsym (_rs, _, _vl, expr)) ->
     interp_expr info expr
  | _ -> raise CannotReduce
