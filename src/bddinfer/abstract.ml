
(**

{1 Abstract States}

*)

(* open Why3 *)
(* to comment out when inside Why3 *)

let do_not_check_invariant = false

open Apron

let man = Polka.manager_alloc_strict ()
(* let man = Box.manager_alloc () *)
(* let man = Oct.manager_alloc () *)

type apron_state = Polka.strict Polka.t Abstract1.t

(* type apron_constraint = Tcons1.t *)

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

  type param_context = {
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

  let rename f ctxi i ctx =
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

let ctx_change_gen fenv fstates ctx =
  let i_to_s = Wstdlib.Hint.create 17 in
  let s_to_i = H.create 17 in
  Wstdlib.Hint.iter
    (fun i s ->
       let s = fstates s in
       Wstdlib.Hint.add i_to_s i s; H.add s_to_i s i)
    ctx.Dom.int_to_state;
  Dom.{
    apron_env = fenv ctx.apron_env;
    counter = ctx.counter;
    int_to_state = i_to_s;
    state_to_int = s_to_i;
  }

let ctx_extend_env new_env ctx =
  ctx_change_gen
    (fun _ -> new_env)
    (fun s -> Abstract1.change_environment man s new_env false)
    ctx

let add_in_environment state (map : why_env) =
  let array_env = apron_array_vars_of_why_env map in
  let union_env = Environment.add state.ctx_state.Dom.apron_env array_env [||] in
  let ctx = ctx_extend_env union_env state.ctx_state
  in
  { map_state =
      VarMap.union
        (fun _ _ _ ->
          Format.eprintf
            "@[<v 2>[Abstract.add_in_environment] \
             Attempt to add a variable already present in the environment:@ \
             abstract env = @[%a@] ;@ map = @[%a@]@]@."
            print_env state.map_state print_env map;
          assert false)
        state.map_state map;
    ctx_state = ctx;
    bdd_state = state.bdd_state;
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

(*
let state_of_linear_constraint state (c : Tcons1.t) : t =
  let ctx = state.ctx_state in
  let env = ctx.Dom.apron_env in
  let array_cond = Tcons1.array_make env 1 in
  Tcons1.array_set array_cond 0 c;
  let s = Abstract1.of_tcons_array man env array_cond in
  let param = Dom.record ctx s in
  { state with bdd_state = B.mk_param param }
  *)

let meet_with_apron_constraint s (c : Tcons1.t) =
  let env = s.ctx_state.Dom.apron_env in
  let array_cond = Tcons1.array_make env 1 in
  Tcons1.array_set array_cond 0 c;
  let f s = Abstract1.meet_tcons_array man s array_cond in
  { s with bdd_state = B.meet_with_param_constraint f s.ctx_state s.bdd_state }


let _apron_env st = st.ctx_state.Dom.apron_env

let of_apron_expr s e =
  let env = s.ctx_state.Dom.apron_env in
  Texpr1.of_expr env e

let why_env st = st.map_state

let is_eq s1 s2 =
  B.equivalent s1.bdd_state s2.bdd_state

let is_leq s1 s2 =
  assert (s1.ctx_state == s2.ctx_state);
  B.entails s1.ctx_state s1.bdd_state s2.bdd_state

(*
let assign_texpr state x te =
  { apron_state =
      Abstract1.assign_texpr man state.apron_state x te None;
    map_state = state.map_state;
    bdd_state = state.bdd_state;
  }
*)


let fresh_apron_var_counter = ref 0

let reset_fresh_var_generators () =
  fresh_bdd_var_counter := 1;
  fresh_apron_var_counter :=0

let fresh_apron_var () =
  let s = "V" ^ string_of_int !fresh_apron_var_counter in
  incr fresh_apron_var_counter;
  Apron.Var.of_string s

let is_bottom s = B.is_bottom s.bdd_state

let join s1 s2 =
  assert (do_not_check_invariant || same_map s1.map_state s2.map_state);
  assert (do_not_check_invariant || Dom.ctx_equal s1.ctx_state s2.ctx_state);
  { map_state = s1.map_state;
    ctx_state = s1.ctx_state;
    bdd_state = B.join s1.ctx_state s1.bdd_state s2.bdd_state;
  }

let meet s1 s2 =
  assert (do_not_check_invariant || same_map s1.map_state s2.map_state);
  assert (do_not_check_invariant || Dom.ctx_equal s1.ctx_state s2.ctx_state);
  { map_state = s1.map_state;
    ctx_state = s1.ctx_state;
    bdd_state = B.meet s1.ctx_state s1.bdd_state s2.bdd_state;
  }

let widening s1 s2 =
  (* Format.eprintf "@[widening, s1:@ @[%a@]@]@." print s1; *)
  (* Format.eprintf "@[widening, s2:@ @[%a@]@]@." print s2; *)
  assert (do_not_check_invariant || same_map s1.map_state s2.map_state);
  assert (do_not_check_invariant || Dom.ctx_equal s1.ctx_state s2.ctx_state);
  if do_not_check_invariant || is_leq s1 s2 then
    begin
      { map_state = s1.map_state;
        ctx_state = s1.ctx_state;
        bdd_state = B.widening s1.ctx_state s1.bdd_state s2.bdd_state;
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

let restrict_environment state target_state =
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
  { target_state with
    bdd_state = B.mk_exist (fun x -> not (List.mem x new_bdd_vars))
        state.ctx_state state.bdd_state target_state.ctx_state;
  }

let drop_var state v =
  let s = { state with map_state = VarMap.remove v state.map_state } in
  restrict_environment state s


type havoc_data =
  (why_var * Apron.Var.t * Apron.Var.t) list * (why_var * Bdd.variable * Bdd.variable) list

(*
let prepare_havoc vars state =
  let new_map, new_apron_vars, intd, boold, oldenv =
    VarMap.fold
      (fun x var (acc, l, intd, boold, oldenv) ->
          match get_value acc x with
          | (y, IntValue v) ->
             (* v: apron var associated to x *)
             (* fresh apron var *)
             (* let w = fresh_apron_var () in *)
             (* y mapsto w, oldx mapsto v *)
             let w = match var with
             | IntValue w -> w
             | _ -> assert false in
             (VarMap.add y var acc, w::l, (y,w,v)::intd, boold,
              VarMap.add x (IntValue v) oldenv)
          | (y, BoolValue v) ->
             (* let w = fresh_bdd_var () in *)
             (* y mapsto w, oldx mapsto v *)
             let w = match var with
             | BoolValue w -> w
             | _ -> assert false in
             (VarMap.add y var acc, l, intd, (y,w,v)::boold,
              VarMap.add x (BoolValue v) oldenv)
          | (_, RefValue _) -> assert false
      )
      vars (state.map_state, [], [], [], VarMap.empty)
  in
  let array_env = Array.of_list new_apron_vars in
  let union_env = Environment.add state.ctx_state.Dom.apron_env array_env [||] in
  let ctx = ctx_extend_env union_env state.ctx_state in
  {
    map_state = new_map;
    ctx_state = ctx;
    bdd_state = state.bdd_state;
  }, oldenv, (intd, boold)
*)

let prepare_havoc writes state =
  let map = state.map_state in
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
            Bddparam.BddVarMap.add v w mb, av1, av2)
         | (_, RefValue _) -> assert false
      )
      writes (VarMap.empty,Bddparam.BddVarMap.empty,[],[])
  in
  let av1 = Array.of_list av1 in
  let av2 = Array.of_list av2 in
  let renamed_apron_env = Environment.rename ctx.Dom.apron_env av1 av2 in
  let full_apron_env = Environment.add renamed_apron_env av1 [||] in
  let rename_apron s =
    let s = Abstract1.rename_array man s av1 av2 in
    Abstract1.change_environment man s full_apron_env false
  in
  let rename_var v =
    try
      Bddparam.BddVarMap.find v map_bvar
    with Not_found -> v
  in
  let ctx = empty_context full_apron_env in
  let b = B.rename rename_var rename_apron state.ctx_state state.bdd_state ctx in
  (* now ctx is a new context from state where all abstract variables are renamed to fresh ones
     we now insert the former association of variables
  *)
  {
    map_state = map;
    ctx_state = ctx;
    bdd_state = b;
  }, oldenv (*, ([],[]) *)

(*
let finalize_havoc state (intd,boold) =
  ignore state;
  ignore intd;
  ignore boold;
  assert false
*)
(*
  let b,l =
    List.fold_left
      (fun (b,l) (x,w,v) -> B.(meet ctx (mk_eq_var v w) b), w::l)
      (state.bdd_state,[]) boold
  in
  let b = B.mk_exist (fun v -> List.mem v l) ctx b ctx in
  let m,av1,av2 =
    List.fold_left
      (fun (m,av1,av2) (x,w,v) ->
        VarMap.add x (IntValue v) m, w::av1, v::av2)
      (state.map_state,[],[]) intd
  in
  (* and finally we rename the apron vars (we can't rename before
     existential elimination of old vars, it would be unsound *)

  let av1 = Array.of_list av1 in
  let av2 = Array.of_list av2 in
  let new_apron_env = Environment.rename ctx.Dom.apron_env av1 av2 in
  let ctx = ctx_rename_env av1 av2 state.ctx_state in
(*
let ctx_rename_env av1 av2 ctx =
  ctx_change_gen
    (fun env -> Environment.rename env av1 av2)
    (fun s -> Abstract1.rename_array man s av1 av2)
    ctx
*)
  { map_state = m;
    ctx_state = ctx;
    bdd_state = b;
  }
*)


(** BDD *)

(*
let meet_with_bdd state b =
   { state with bdd_state = B.mk_and state.bdd_state b }
*)

(** interprets variable introduction [let x (as boolean var v) = e in ...] *)
(*
let interp_bool_var_intro state x v e : t =
  (* Format.printf "@[interp_bool_var_intro: state=@ @[%a@]@]@." print state; *)
  (* Format.printf "@[v =@ %d@]@." v; *)
  let b = B.(mk_and (mk_iff (mk_var v) e) state.bdd_state) in
  (* Format.printf "@[BDD =@ %a@]@." B.print_compact b; *)
  let s =
    { state with
      map_state = VarMap.add x (BoolValue v) state.map_state;
      bdd_state = b }
    in
  (* Format.printf "@[interp_bool_var_intro: s=@ @[%a@]@]@." print s; *)
  s
*)

(*
let interp_bool_assign state v w bexpr =
  (* we have a state with a (boolean) Why variable `x` associated to
     bdd variable `v`, and a BDD B(v). I write B(v) to make explicit that v occurs in B.
     We want `x` to be now equal to expression `bexpr`
     which may use `v` itself. We want to keep `x` associated to `v`
     at the end. *)
  let b = state.bdd_state in
  (* Format.printf "@[v =@ %d, extrav = %d@]@." v w;
   * Format.printf "@[BDD state =@ %a@]@." B.print_compact b;
   * Format.printf "@[BDD expr =@ %a@]@." B.print_compact bexpr; *)
  (* we first build the BDD  [B(v) /\ w=bexpr] *)
  let b1 = B.(mk_and (mk_iff (mk_var w) bexpr) b) in
  (* we abstract away v *)
  let b2 = B.(mk_exist ((==) v) b1) in
  (* we "rename" w into v by first asserting that v=w and then
     abstracting away w *)
  let b3 = B.(mk_and (mk_iff (mk_var v) (mk_var w)) b2) in
  let b4 = B.(mk_exist ((==) w) b3) in
  (* Format.printf "@[b4 =@ %a@]@." B.print_compact b4; *)
  { state with bdd_state = b4 }
*)



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
     let cst, denom = Mpqf.to_mpzf2 q in
     assert (Mpz.to_string denom = "1");
     Z.of_string (Mpz.to_string cst)
  | _ -> assert false

let get_apron_interval i  =
  let open Interval in
  if is_bottom i then raise Bottom;
  if is_top i then
    { id_min = None; id_max = None }
  else
    let id_min =
      if Scalar.is_infty i.inf = -1 then None else Some (get_int i.inf)
    in
    let id_max =
      if Scalar.is_infty i.sup = 1 then None else Some (get_int i.sup)
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
    "@[<hv 2>{ @[<hv 2>apron_env:@ @[%a@];@]@ \
     @[<hv 2>counter:@ %d;@]@ \
     @[<hv 2>int_to_state:@ @[%a@];@] }@]"
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
