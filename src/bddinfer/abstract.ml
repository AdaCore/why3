(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(**

{1 Abstract States}

*)

(* open Why3 *)
(* to comment out when inside Why3 *)

let do_not_check_invariant = true
(* set to true when inside Why3 *)

open Apron

let man = Polka.manager_alloc_strict ()
(* let man = Box.manager_alloc () *)
(* let man = Oct.manager_alloc () *)

type apron_state = Polka.strict Polka.t Abstract1.t
(* type apron_state = Box.t Abstract1.t *)
(* type apron_state = Oct.t Abstract1.t *)

type why_var = {
    var_name : string;
    unique_tag : int;
  }

let create_var =
  let c = ref 0 in
  fun name -> incr c; {
      var_name = name;
      unique_tag = !c;
    }

let compare_var v1 v2 =
  Stdlib.compare v1.unique_tag v2.unique_tag

module VarMap = Map.Make(struct
                  type t = why_var
                  let compare = compare_var
                end)

module Bdd = Bddparam

type var_value =
  | UnitValue
  | IntValue of Apron.Var.t
  | RefValue of why_var
  | BoolValue of Bdd.variable

let var_value_equal v1 v2 =
  match v1,v2 with
  | IntValue v1, IntValue v2 -> Apron.Var.compare v1 v2 = 0
  | RefValue v1, RefValue v2 -> v1 == v2
  | BoolValue v1, BoolValue v2 -> v1 = v2
  | _ -> false

type why_env = var_value VarMap.t

let same_map m1 m2 =
  VarMap.equal var_value_equal m1 m2

(** BDD *)

let print_bdd_var fmt x = Format.fprintf fmt "B%d" x

  module H = Exthtbl.Make(struct
      type t = apron_state
      let equal = Abstract1.is_eq man
      let hash = Abstract1.hash man
    end)


module Dom (* : Bddparam.ParamDomain *) = struct

  type param_index = int

  type param_state = apron_state

  let new_ctx_id = let c = ref 0 in fun () -> let x = !c in incr c; x

  type param_context = {
    ctx_unique_id : int;
    apron_env : Apron.Environment.t;
    mutable counter : int;
    state_to_int : int H.t;
    int_to_state : apron_state Wstdlib.Hint.t;
  }

  let ctx_equal c1 c2 =
    Apron.Environment.equal c1.apron_env c2.apron_env &&
    c1.counter == c2.counter &&
    try
      for i=0 to c1.counter - 1 do
        let s1 = Wstdlib.Hint.find c1.int_to_state i in
        let s2 = Wstdlib.Hint.find c2.int_to_state i in
        if Abstract1.is_eq man s1 s2 then () else raise Exit
      done;
      true
    with Exit | Not_found -> false


  let get ctx i =
    try
      Wstdlib.Hint.find ctx.int_to_state i
    with Not_found ->
      Format.eprintf "Abstract.get: index %d not found in ctx@." i;
      assert false

  let record ctx s =
    try
      H.find ctx.state_to_int s
    with Not_found ->
      let i = ctx.counter in
      ctx.counter <- ctx.counter + 1;
      Wstdlib.Hint.add ctx.int_to_state i s;
      H.add ctx.state_to_int s i;
      i

  let meet ctx i j =
    let si = get ctx i in
    let sj = get ctx j in
    let s = Abstract1.meet man si sj in
    if Abstract1.is_bottom man s then None else Some (record ctx s)

  let join ctx i j =
    let si = get ctx i in
    let sj = get ctx j in
    let s = Abstract1.join man si sj in
    if Abstract1.is_top man s then None else Some (record ctx s)

  let widening ctx i j =
    let si = get ctx i in
    let sj = get ctx j in
    let s = Abstract1.widening man si sj in
    if Abstract1.is_top man s then None else Some (record ctx s)

  let exist_elim ctxi i ctx =
    let si = get ctxi i in
    let s = Abstract1.change_environment man si ctx.apron_env false in
    if Abstract1.is_top man s then None else Some (record ctx s)

  let entails ctx i j =
    let si = get ctx i in
    let sj = get ctx j in
    Abstract1.is_leq man si sj

  let change f ctxi i ctx =
    let si = get ctxi i in
    let s = f si in
    record ctx s

  let meet_with_constraint f ctxi i =
    let s =
      match i with
      | Some i ->
        let si = get ctxi i in f si
      | None -> f (Abstract1.top man ctxi.apron_env)
    in
    if Abstract1.is_bottom man s then None else Some (record ctxi s)

end

module B = Bdd.Make(Dom)(struct
               let print_var = print_bdd_var
               let size = 7001
               let max_var = 700
             end)

let empty_context env = Dom.{
    ctx_unique_id = new_ctx_id ();
    apron_env = env;
    counter = 0;
    state_to_int = H.create 17;
    int_to_state = Wstdlib.Hint.create 17;
  }



let fresh_bdd_var_counter = ref 1 (* starts with 1 in [Bdd] module *)

let fresh_bdd_var () =
  let n = !fresh_bdd_var_counter in
  incr fresh_bdd_var_counter;
  n

let  bdd_stats () =
  !fresh_bdd_var_counter-1, [||] (* B.stats () *)

(** state *)

type t = {
  map_state : why_env;
  ctx_state : Dom.param_context;
  bdd_state : B.t;
}

(** Printing *)

let print_var fmt v =
  Format.fprintf fmt "%s" v.var_name

let print_var_value fmt v =
  match v with
  | UnitValue -> Format.fprintf fmt "()"
  | IntValue y -> Var.print fmt y
  | RefValue y -> Format.fprintf fmt "ref {%a}" print_var y
  | BoolValue v -> print_bdd_var fmt v

let print_env fmt ms =
  VarMap.iter (fun x y -> Format.fprintf fmt "%a -> %a;@ " print_var x print_var_value y) ms


module ApronVarMap = Map.Make(struct type t = Var.t let compare = Var.compare end)

let invert_varmap_int s =
  let vmap = s.map_state in
  VarMap.fold
  ( fun x y m ->
    match y with
    | IntValue (apron_var) ->
        ApronVarMap.add apron_var x m
    | _ -> m
  ) vmap ApronVarMap.empty

let invert_varmap_bool s =
  let vmap = s.map_state in
  VarMap.fold
  ( fun x y m ->
    match y with
    | BoolValue v ->
        Bdd.BddVarMap.add v x m
    | _ -> m
  ) vmap Bdd.BddVarMap.empty


let apron_array_vars_of_why_env (map : why_env) : Apron.Var.t array =
  let env = VarMap.fold (fun _ v acc ->
      match v with
      |IntValue(x) -> x::acc
      |_ -> acc) map [] in
  Array.of_list env

let apron_env_of_why_env (map : why_env) =
  let env_array = apron_array_vars_of_why_env map in
  Apron.Environment.make env_array [||]

(*
let ctx_extend_env new_env ctx =
  let i_to_s = Wstdlib.Hint.create 17 in
  let s_to_i = H.create 17 in
  Wstdlib.Hint.iter
    (fun i s ->
       let s = Abstract1.change_environment man s new_env false in
       Wstdlib.Hint.add i_to_s i s; H.add s_to_i s i)
    ctx.Dom.int_to_state;
  Dom.{
    ctx_unique_id = new_ctx_id ();
    apron_env = new_env;
    counter = ctx.counter;
    int_to_state = i_to_s;
    state_to_int = s_to_i;
  }
*)

(*
let ctx_extend_env ctx_src new_env ctx =
  let open Wstdlib in
  Hint.iter
    (fun i s ->
       try
         let _ = Hint.find ctx.Dom.int_to_state i in
         ()
       with Not_found ->
         let s = Abstract1.change_environment man s new_env false in
         Hint.add ctx.Dom.int_to_state i s; H.add ctx.Dom.state_to_int s i)
    ctx_src.Dom.int_to_state
*)

type memo_add_env = B.param_context * Apron.Environment.t * var_value VarMap.t

let utime () = Unix.((times ()).tms_utime)

let time_in_add_in_environment = ref 0.0

let add_in_environment memo state (map : why_env) =
  let t = utime () in
  let (ctx,env,map) =
    match !memo with
    | Some x -> x
    | None ->
      let array_env = apron_array_vars_of_why_env map in
      let union_env = Environment.add state.ctx_state.Dom.apron_env array_env [||] in
      (* let ctx = ctx_extend_env union_env state.ctx_state in *)
      let ctx = empty_context union_env in
      let map =
        VarMap.union
          (fun _ _ _ ->
             Format.eprintf
               "@[<v 2>[Abstract.add_in_environment] \
                Attempt to add a variable already present in the environment:@ \
                abstract env = @[%a@] ;@ map = @[%a@]@]@."
               print_env state.map_state print_env map;
             assert false)
          state.map_state map
      in
      let x = (ctx,union_env,map) in
      memo := Some x;
      x
  in
  let change_state s =
    let s = Abstract1.change_environment man s env false in
    s
  in
  let b = B.change_ctx change_state state.ctx_state state.bdd_state ctx in
  time_in_add_in_environment := !time_in_add_in_environment +. (utime() -. t);
  { map_state = map;
    ctx_state = ctx;
    bdd_state = b;
  }

let top s =
  { s with bdd_state = B.top }

let top_new_ctx (map : why_env) =
  let env = apron_env_of_why_env map in
  let ctx = empty_context env in
  { map_state = map;
    ctx_state = ctx;
    bdd_state = B.top;
  }


let bottom s =
  { s with bdd_state = B.bottom }


let singleton_boolean_var_true state v =
  { state with bdd_state = B.mk_var v }

let time_in_meet_with_apron_constraint = ref 0.0
let time_in_meet_with_param_constraint = ref 0.0

let meet_with_apron_constraint s (c : Tcons1.t) =
  let t = utime () in
  let env = s.ctx_state.Dom.apron_env in
  let array_cond = Tcons1.array_make env 1 in
  Tcons1.array_set array_cond 0 c;
  let f s = Abstract1.meet_tcons_array man s array_cond in
  let u = utime () in
  let b = B.meet_with_param_constraint f s.ctx_state s.bdd_state in
  let v = utime () in
  time_in_meet_with_param_constraint := !time_in_meet_with_param_constraint +. (v -. u);
  time_in_meet_with_apron_constraint := !time_in_meet_with_apron_constraint +. (v -. t);
  { s with bdd_state = b }


let of_apron_expr s e =
  let env = s.ctx_state.Dom.apron_env in
  Texpr1.of_expr env e

let why_env st = st.map_state

let is_eq s1 s2 =
  B.equivalent s1.bdd_state s2.bdd_state

let time_in_is_leq = ref 0.0

let is_leq s1 s2 =
  assert (do_not_check_invariant || s1.ctx_state == s2.ctx_state);
  let t = utime () in
  let b = B.entails s1.ctx_state s1.bdd_state s2.bdd_state in
  time_in_is_leq := !time_in_is_leq +. (utime () -. t);
  b


let fresh_apron_var_counter = ref 0

let reset_fresh_var_generators () =
  fresh_bdd_var_counter := 1;
  fresh_apron_var_counter :=0

let fresh_apron_var () =
  let s = "V" ^ string_of_int !fresh_apron_var_counter in
  incr fresh_apron_var_counter;
  Apron.Var.of_string s

let is_bottom s = B.is_bottom s.bdd_state

let time_in_join = ref 0.0

let join s1 s2 =
  let t = utime () in
  assert (do_not_check_invariant || same_map s1.map_state s2.map_state);
  assert (do_not_check_invariant || Dom.ctx_equal s1.ctx_state s2.ctx_state);
  let s = B.join s1.ctx_state s1.bdd_state s2.bdd_state in
  time_in_join := !time_in_join +. (utime () -. t);
  { map_state = s1.map_state;
    ctx_state = s1.ctx_state;
    bdd_state = s;
  }

let time_in_meet = ref 0.0

let meet s1 s2 =
  let t = utime () in
  assert (do_not_check_invariant || same_map s1.map_state s2.map_state);
  assert (do_not_check_invariant || Dom.ctx_equal s1.ctx_state s2.ctx_state);
  let s = B.meet s1.ctx_state s1.bdd_state s2.bdd_state in
  time_in_meet := !time_in_meet +. (utime () -. t);
  { map_state = s1.map_state;
    ctx_state = s1.ctx_state;
    bdd_state = s;
  }

let time_in_widening = ref 0.0

let widening s1 s2 =
  (* Format.eprintf "@[widening, s1:@ @[%a@]@]@." print s1; *)
  (* Format.eprintf "@[widening, s2:@ @[%a@]@]@." print s2; *)
  assert (do_not_check_invariant || same_map s1.map_state s2.map_state);
  assert (do_not_check_invariant || Dom.ctx_equal s1.ctx_state s2.ctx_state);
  let t = utime () in
  if do_not_check_invariant || is_leq s1 s2 then
    begin
      let b = B.widening s1.ctx_state s1.bdd_state s2.bdd_state in
      time_in_widening := !time_in_widening +. (utime () -. t);
      { map_state = s1.map_state;
        ctx_state = s1.ctx_state;
        bdd_state = b;
      }
    end
  else
    failwith "Abstract.widening: s1 should be included in s2"

let complement s =
  { s with bdd_state = B.mk_not s.ctx_state s.bdd_state }


let rec get_value env x =
  match VarMap.find x env with
  | RefValue y -> get_value env y
  | v -> (x, v)

let time_in_restrict_environment = ref 0.0

let restrict_environment state target_state =
  let t = utime () in
  let new_bdd_vars =
    VarMap.fold
      (fun x _ l2 ->
         try
           let (_,v) = get_value state.map_state x in
           match v with
           | UnitValue -> l2
           | IntValue _ -> l2
           | BoolValue w -> w::l2
           | RefValue _ -> assert false
         with Not_found -> l2 (* may happen because of drop *)
        )
      target_state.map_state []
  in
  let b = B.mk_exist (fun x -> not (List.mem x new_bdd_vars))
        state.ctx_state state.bdd_state target_state.ctx_state;
  in
  time_in_restrict_environment := !time_in_restrict_environment +. (utime() -. t);
  { target_state with bdd_state = b }


type memo_havoc = (B.param_context * var_value VarMap.t *
   (apron_state -> apron_state) * (int * int) list)

let time_in_prepare_havoc = ref 0.0

let prepare_havoc memo writes state =
  let t = utime () in
  let map = state.map_state in
  let ctx,oldenv,rename_apron,rename_var =
    match !memo with
    | Some(ctx,ov,ra,rv) -> ctx,ov,ra,rv
    | None ->
      let ctx = state.ctx_state in
      let oldenv, map_bvar, av1, av2 =
        VarMap.fold
          (fun x var (old,mb,av1,av2) ->
             (* we want: y mapsto w, oldx mapsto v *)
             match get_value map x with
             | (y, UnitValue) ->
               let old = VarMap.add x (RefValue y) old in
               (VarMap.add y UnitValue old, mb, av1, av2)
             | (y, IntValue v) ->
               let w = match var with
                 | IntValue w -> w
                 | _ -> assert false
               in
               let old = VarMap.add x (RefValue y) old in
               (VarMap.add y (IntValue w) old, mb, v::av1, w::av2)
             | (y, BoolValue v) ->
               let w = match var with
                 | BoolValue w -> w
                 | _ -> assert false
               in
               let old = VarMap.add x (RefValue y) old in
               (VarMap.add y (BoolValue w) old,
                (v,w)::mb, av1, av2)
             | (_, RefValue _) -> assert false
          )
          writes (VarMap.empty,[],[],[])
      in
      let av1 = Array.of_list av1 in
      let av2 = Array.of_list av2 in
      let renamed_apron_env = Environment.rename ctx.Dom.apron_env av1 av2 in
      let full_apron_env = Environment.add renamed_apron_env av1 [||] in
      let rename_apron s =
        let s = Abstract1.rename_array man s av1 av2 in
        Abstract1.change_environment man s full_apron_env false
      in
      let ctx = empty_context full_apron_env in
      memo := Some(ctx,oldenv,rename_apron,map_bvar);
      ctx,oldenv,rename_apron,map_bvar
  in
  let b = B.rename_few rename_var rename_apron state.ctx_state state.bdd_state ctx in
  time_in_prepare_havoc := !time_in_prepare_havoc +. (utime() -. t);
  {
    map_state = map;
    ctx_state = ctx;
    bdd_state = b;
  }, oldenv




(** State to formula *)




let mpqf_to_int s : Z.t =
  match s with
  | Scalar.Mpqf q ->
    let cst, denom = Mpqf.to_mpzf2 q in
    (* check if denom is one. *)
    assert (Mpz.to_string denom = "1");
    Z.of_string (Mpz.to_string cst)
  | Scalar.Float f ->
     begin
       try
         Z.of_float f
       with _ ->
         Format.eprintf "[Abstract.mpqf_to_int] couldn't convert Scalar.Float `%f` to integer" f;
         assert false
     end
  | Scalar.Mpfrf _ ->
     Format.eprintf "[Abstract.mpqf_to_int] couldn't convert a Scalar.Mpfrf to integer";
     assert false


let move_coef a =
  Array.fold_left
  ( fun (l_coefs, r_coefs) (v, c) ->
    match c with
    | Coeff.Scalar s ->
      let cst = mpqf_to_int s in
      if Z.(cst = zero) then
        l_coefs, r_coefs
      else if Z.(cst > zero) then
        (v, cst)::l_coefs, r_coefs
      else
        l_coefs, (v, Z.(neg cst))::r_coefs
    | Coeff.Interval _ ->
      assert false
  )
  ([], []) a


type linear_constraint =
  Lincons0.typ * (ApronVarMap.key option * Z.t) list *
   (ApronVarMap.key option * Z.t) list

let get_lincons s : linear_constraint list
  =
  let cons_array = Abstract1.to_lincons_array man s in
  let vars, _ = Environment.vars (Lincons1.array_get_env cons_array) in
  let res = ref [] in
  for i = 0 to Lincons1.array_length cons_array - 1 do
    let cons = Lincons1.array_get cons_array i in
    let coefs = Array.map (fun x -> (Some(x), Lincons1.get_coeff cons x)) vars in
    let cst = Lincons1.get_cst cons in
    let coefs = Array.append coefs [|None, cst|] in
    let l_coefs, r_coefs = move_coef coefs in
    let ty = Lincons1.get_typ cons in
    res := (ty, l_coefs, r_coefs) :: !res
  done;
  !res


let as_formula s =
  let f = B.as_compact_formula s.ctx_state s.bdd_state in
  let h = s.ctx_state.Dom.int_to_state in
  let m =
    Wstdlib.Hint.fold
      (fun i s acc ->
         let c = get_lincons s in
         Wstdlib.Mint.add i c acc)
      h Wstdlib.Mint.empty
  in
  f, m


(** {2 domains} *)

type bool_domain = BDtrue | BDfalse | BDtop

type int_domain = { id_min : Z.t option ; id_max : Z.t option }

let join_int_domains i1 i2 =
  let id_min =
    match i1.id_min, i2.id_min with
    | None, _ | _, None -> None
    | Some z1, Some z2 -> Some (Z.min z1 z2)
  in
  let id_max =
    match i1.id_max, i2.id_max with
    | None, _ | _, None -> None
    | Some z1, Some z2 -> Some (Z.max z1 z2)
  in
  { id_min ; id_max }

type domain = Bool_domain of bool_domain | Int_domain of int_domain

let print_bool_domain fmt d =
  match d with
  | BDtrue -> Format.fprintf fmt "true"
  | BDfalse -> Format.fprintf fmt "false"
  | BDtop -> Format.fprintf fmt "top"

let print_int_opt inf bracket fmt i =
  match i with
  | None -> Format.fprintf fmt inf
  | Some n -> Format.fprintf fmt bracket (Z.to_string n)

let print_int_domain fmt d =
  Format.fprintf fmt "%a;%a"
    (print_int_opt "]-oo" "[%s") d.id_min
    (print_int_opt "+oo[" "%s]") d.id_max

let print_domain fmt d =
  match d with
  | Bool_domain bd -> print_bool_domain fmt bd
  | Int_domain id -> print_int_domain fmt id


exception Top
exception Bottom

let get_int x =
  match x with
  | Scalar.Mpqf q ->
    let num, den = Mpqf.to_mpzf2 q in
    (Z.of_string (Mpz.to_string num),
     Z.of_string (Mpz.to_string den))
  | _ -> assert false

let get_apron_interval i  =
  let open Interval in
  if is_bottom i then raise Bottom;
  if is_top i then
    { id_min = None; id_max = None }
  else
    let id_min =
      if Scalar.is_infty i.inf = -1 then None else
        let (n,d) = get_int i.inf in
        let (q,r) = Z.div_rem n d in
        let c = (* n = q * d + r *)
          if Z.lt r Z.zero then Z.pred q else q in
        Some c
    in
    let id_max =
      if Scalar.is_infty i.sup = 1 then None else
        let (n,d) = get_int i.sup in
        let (q,r) = Z.div_rem n d in
        let c =
          if Z.gt r Z.zero then Z.succ q else q in
        Some c
    in
    { id_min ; id_max }

let compute_domains s =
  if is_bottom s then
    Bdd.BddVarMap.empty,VarMap.empty
  else
    try
      let bool_values = B.extract_known_values s.bdd_state in
      let all_apron_states =
        try
          Some
            (B.fold_param_states
               (fun b acc -> if b then raise Top else acc)
               (fun i acc -> Dom.get s.ctx_state i :: acc)
               s.bdd_state [])
        with Top -> None
      in
      bool_values,
      VarMap.fold
        ( fun x v acc ->
            match v with
            | UnitValue -> acc
            | IntValue var ->
              begin
                let i =
                  match all_apron_states with
                  | None -> { id_min = None ; id_max = None }
                  | Some [] ->
                    (* impossible case: no apron state as leaves
                       implies the other leaves top and bottom must
                       occur, hence all_apron_states is None *)
                    assert false
                  | Some (s::sl) ->
                    let interval = Abstract1.bound_variable man s var in
                    let d = get_apron_interval interval in
                    List.fold_left
                      (fun i s ->
                         let interval = Abstract1.bound_variable man s var in
                         let d = get_apron_interval interval in
                         join_int_domains i d)
                      d
                      sl
                in
                VarMap.add x (Int_domain i) acc
              end
            | BoolValue v ->
              let d =
                try
                  let b = Bdd.BddVarMap.find v bool_values in
                  if b then BDtrue else BDfalse
                with Not_found -> BDtop
              in
              VarMap.add x (Bool_domain d) acc
            | RefValue _ -> acc)
        s.map_state VarMap.empty
    with Bottom -> assert false

let print_var_dom fmt (v,d) =
  Format.fprintf fmt "@[%a = %a@]"
    print_var v print_domain d

let print_domains fmt m =
  Format.fprintf fmt "@[<hov 2>%a@]"
    Pp.(print_list semi print_var_dom) (VarMap.bindings m)

let get_domains s =
  let _,x = compute_domains s in x

let print_int_to_state fmt h =
    Wstdlib.Hint.iter (fun x y -> Format.fprintf fmt "%d -> %a;@ " x Abstract1.print y) h

let print_ctx fmt ctx =
  Format.fprintf fmt
    "@[<hv 2>{ @[<hv 2>unique_id:@ %d;@]@ \
     @[<hv 2>apron_env:@ @[%a@];@]@ \
     @[<hv 2>counter:@ %d;@]@ \
     @[<hv 2>int_to_state:@ @[%a@];@] }@]"
    ctx.Dom.ctx_unique_id
    (fun fmt -> Environment.print fmt) ctx.Dom.apron_env
    ctx.Dom.counter
    print_int_to_state ctx.Dom.int_to_state


let print fmt s =
  let _m,doms = compute_domains s in
(*
  let reduced_bdd =
    B.mk_exist (fun v ->
        try let _ = Bdd.BddVarMap.find v m in true
        with Not_found -> false) s.bdd_state
  in
*)
  Format.fprintf fmt "@[<hv 2>{ @[<hv 2>map_state:@ @[%a@];@]@ \
                      @[<hv 2>context:@ @[%a@];@]@ \
                      @[<hv 2>bdd:@ @[%a@];@]@ \
                      @[<hv 2>domains:@ @[%a@];@]@ \
                      @[<hv 2>reduced_bdd:@ @[%%a@];@] }@]"
    print_env s.map_state
    print_ctx s.ctx_state
    B.print_compact s.bdd_state
    print_domains doms
    (* B.print_compact reduced_bdd *)
