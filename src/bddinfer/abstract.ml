
(**

{1 Abstract States}

*)

(* open Why3 *)
(* to comment out when inside Why3 *)

open Apron

let man = Polka.manager_alloc_strict ()
(* let man = Box.manager_alloc () *)
(* let man = Oct.manager_alloc () *)

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

type var_value = IntValue of Apron.Var.t | RefValue of why_var | BoolValue of Bdd.variable

type why_env = var_value VarMap.t

(** BDD *)

let print_bdd_var fmt x = Format.fprintf fmt "B%d" x

module B = Bdd.Make(struct
               let print_var = print_bdd_var
               let size = 7001
               let max_var = 700
             end)


let fresh_bdd_var_counter = ref 1 (* starts with 1 in [Bdd] module *)

let fresh_bdd_var () =
  let n = !fresh_bdd_var_counter in
  incr fresh_bdd_var_counter;
  n

let  bdd_stats () =
  !fresh_bdd_var_counter-1, [||] (* B.stats () *)

(** state *)

type t = {
    map_state : var_value VarMap.t;
    apron_state : Polka.strict Polka.t Abstract1.t;
    (* apron_state : Box.t Abstract1.t; *)
    (* apron_state : Oct.t Abstract1.t; *)
    bdd_state : B.t;
  }

(** Printing *)

let print_var fmt v =
  Format.fprintf fmt "%s" v.var_name

let print_var_value fmt v =
  match v with
  | IntValue y -> Var.print fmt y
  | RefValue y -> Format.fprintf fmt "ref {%a}" print_var y
  | BoolValue v -> print_bdd_var fmt v

let print_env fmt ms =
  VarMap.iter (fun x y -> Format.fprintf fmt "%a -> %a;@ " print_var x print_var_value y) ms


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


let get_lincons s :
      (Tcons1.typ * (Var.t option * Z.t) list * (Var.t option * Z.t) list) array
       =
  let cons_array = Abstract1.to_lincons_array man s.apron_state in
  let length = Lincons1.array_length cons_array in
  let vars, _ = Environment.vars (Lincons1.array_get_env cons_array) in
  let arr = Array.make length (Lincons1.EQ, [], []) in
  for i = 0 to length - 1 do
    let cons = Lincons1.array_get cons_array i in
    let coefs = Array.map (fun x -> (Some(x), Lincons1.get_coeff cons x)) vars in
    let cst = Lincons1.get_cst cons in
    let coefs = Array.append coefs [|None, cst|] in
    let l_coefs, r_coefs = move_coef coefs in
    let ty = Lincons1.get_typ cons in
    Array.set arr i (ty, l_coefs, r_coefs)
  done;
  arr



let apron_array_vars_of_why_env (map : var_value VarMap.t) : Apron.Var.t array =
  let env = VarMap.fold (fun _ v acc ->
      match v with
      |IntValue(x) -> x::acc
      |_ -> acc) map [] in
  Array.of_list env

let apron_env_of_why_env (map : var_value VarMap.t) =
  let env_array = apron_array_vars_of_why_env map in
  Apron.Environment.make env_array [||]

let add_in_environment state (map : var_value VarMap.t) =
  let array_env = apron_array_vars_of_why_env map in
  let union_env = Environment.add (Abstract1.env state.apron_state) array_env [||] in
  { apron_state =
      Abstract1.change_environment
        man state.apron_state union_env false;
    map_state =
      VarMap.union
        (fun _ _ _ ->
          Format.eprintf
            "@[<v 2>[Abstract.add_in_environment] \
             Attempt to add a variable already present in the environment:@ \
             abstract env = @[%a@] ;@ map = @[%a@]@]@."
            print_env state.map_state print_env map;
          assert false)
        state.map_state map;
    bdd_state = state.bdd_state;
  }

let restrict_environment state (map : var_value VarMap.t) =
  let new_map, new_vars, new_bdd_vars =
    VarMap.fold
      (fun x _ (acc, l1, l2) ->
        (* apron var associated to x *)
         try
           let v = VarMap.find x state.map_state in
           match v with
           | IntValue w -> (VarMap.add x v acc, w::l1, l2)
           | BoolValue w -> (VarMap.add x v acc, l1, w::l2)
           | RefValue _ -> (VarMap.add x v acc, l1, l2)
         with Not_found -> (acc,l1,l2) (* may happen because of drop *)
        )
      map (VarMap.empty, [], [])
  in
  let array_env = Array.of_list new_vars in
  { apron_state = Abstract1.change_environment
      man state.apron_state (Environment.make array_env [||]) false;
    map_state = new_map;
    bdd_state = B.mk_exist (fun x -> not (List.mem x new_bdd_vars)) state.bdd_state;
}


let top (map : var_value VarMap.t) =
  let env = apron_env_of_why_env map in
  { apron_state = Abstract1.top man env;
    map_state = map;
    bdd_state = B.one;
}

let bottom (map : var_value VarMap.t) =
  let env = apron_env_of_why_env map in
  { apron_state = Abstract1.bottom man env;
    map_state = map;
    bdd_state = B.zero;
  }

let apron_env st = Abstract1.env st.apron_state

let why_env st = st.map_state

let is_eq s1 s2 =
  Abstract1.is_eq man s1.apron_state s2.apron_state
  && B.equivalent s1.bdd_state s2.bdd_state

let is_leq s1 s2 =
  Abstract1.is_leq man s1.apron_state s2.apron_state
  && B.entails s1.bdd_state s2.bdd_state

let assign_texpr state x te =
  { apron_state =
      Abstract1.assign_texpr man state.apron_state x te None;
    map_state = state.map_state;
    bdd_state = state.bdd_state;
  }


let fresh_apron_var_counter = ref 0

let reset_fresh_var_generators () =
  fresh_bdd_var_counter := 1;
  fresh_apron_var_counter :=0

let fresh_apron_var () =
  let s = "V" ^ string_of_int !fresh_apron_var_counter in
  incr fresh_apron_var_counter;
  Apron.Var.of_string s

let rec get_value env x =
  match VarMap.find x env with
  | RefValue y -> get_value env y
  | v -> (x, v)




let unify_environments s1 s2 : t =
  let apron1,apron2,bdd_rename =
    VarMap.fold (fun x v1 ((apron1,apron2,bdd) as acc) ->
        match v1, VarMap.find x s2.map_state with
        | RefValue a, RefValue b ->
           assert (a == b);
           acc
        | IntValue a, IntValue b ->
           if a == b then
             acc
           else
             (b::apron1,a::apron2,bdd)
        | BoolValue a, BoolValue b ->
           if a == b then
             acc
           else
             (apron1,apron2,(a,b)::bdd)
        | _ -> assert false
      ) s1.map_state ([],[],[])
  in
  let aprons = Abstract1.rename_array man s2.apron_state
             (Array.of_list apron1) (Array.of_list apron2)
  in
  let b =
    List.fold_left
      (fun acc (v1,v2) ->
        B.mk_exist ((==) v2) (B.mk_and acc (B.mk_iff (B.mk_var v1) (B.mk_var v2)))
      )
      s2.bdd_state bdd_rename
  in
  (* Format.eprintf "@[s2 before unify:@ @[%a@]@]@." print s2; *)
  let s =
    { map_state = s1.map_state;
      apron_state = aprons;
      bdd_state = b }
  in
  (* Format.eprintf "@[s2 after unify:@ @[%a@]@]@." print s; *)
  s

let is_bottom s =
  s.bdd_state == B.zero || Abstract1.is_bottom man s.apron_state

let join s1 s2 =
  if is_bottom s1 then s2 else
  if is_bottom s2 then s1 else
  let s2 =
    if s1.map_state != s2.map_state then
      unify_environments s1 s2
    else s2
  in
  { apron_state = Abstract1.join man s1.apron_state s2.apron_state;
    map_state = s1.map_state;
    bdd_state = B.mk_or s1.bdd_state s2.bdd_state;
  }

let meet s1 s2 =
  let s2 =
    if s1.map_state != s2.map_state then
      unify_environments s1 s2
    else s2
  in
  { apron_state = Abstract1.meet man s1.apron_state s2.apron_state;
    map_state = s1.map_state;
    bdd_state = B.mk_and s1.bdd_state s2.bdd_state;
  }

let widening s1 s2 =
  (* Format.eprintf "@[widening, s1:@ @[%a@]@]@." print s1; *)
  (* Format.eprintf "@[widening, s2:@ @[%a@]@]@." print s2; *)
  let s2 =
    if s1.map_state != s2.map_state then
      unify_environments s1 s2
    else s2
  in
  if is_leq s1 s2 then
    (* Format.eprintf "@[widening, s2 unified:@ @[%a@]@]@." print s2; *)
    { apron_state = Abstract1.widening man s1.apron_state s2.apron_state;
      map_state = s1.map_state;
      bdd_state = B.mk_or s1.bdd_state s2.bdd_state;
    }
  else
    failwith "Abstract.widening: s1 should be included in s2"


type havoc_data =
  (why_var * Apron.Var.t * Apron.Var.t) list * (why_var * Bdd.variable * Bdd.variable) list

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
  let union_env = Environment.add (Abstract1.env state.apron_state) array_env [||] in
  { apron_state = Abstract1.change_environment
      man state.apron_state union_env false;
    map_state = new_map;
    bdd_state = state.bdd_state;
  }, oldenv, (intd, boold)


let finalize_havoc state (intd,boold) =
  let m,av1,av2 =
    List.fold_left
      (fun (m,av1,av2) (x,w,v) ->
        VarMap.add x (IntValue v) m, w::av1, v::av2)
      (state.map_state,[],[]) intd
  in
  let m,b,l =
    List.fold_left
      (fun (m,b,l) (x,w,v) ->
        VarMap.add x (BoolValue v) m,
        B.(mk_and (mk_iff (mk_var v) (mk_var w)) b), w::l)
      (m,state.bdd_state,[]) boold
  in
  let a = Abstract1.rename_array man state.apron_state (Array.of_list av1) (Array.of_list av2) in
  let b = B.mk_exist (fun v -> List.mem v l) b in
  { map_state = m;
    apron_state = a;
    bdd_state = b;
  }


let of_tcons_array map array_cond =
  let env = apron_env_of_why_env map in
  { apron_state =
      Abstract1.of_tcons_array man env array_cond;
    map_state = map;
    bdd_state = B.one;
  }



let meet_with_tcons_array state aenv array_cond =
  let s = Abstract1.of_tcons_array man aenv array_cond in
  { state with apron_state = Abstract1.meet man state.apron_state s }


(** BDD *)

let boolean_substate s = s.bdd_state

let meet_with_bdd state b =
   { state with bdd_state = B.mk_and state.bdd_state b }

(** interprets variable introduction [let x (as boolean var v) = e in ...] *)
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


(** {2 domains} *)

type bool_domain = BDtrue | BDfalse | BDtop

type int_domain = { id_min : Z.t option ; id_max : Z.t option }

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
    bool_values,
    VarMap.fold
      ( fun x v acc ->
        match v with
        | IntValue var ->
           let interval = Abstract1.bound_variable man s.apron_state var in
           let d = get_apron_interval interval in
           VarMap.add x (Int_domain d) acc
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

let print fmt s =
  let m,doms = compute_domains s in
  let reduced_bdd =
    B.mk_exist (fun v ->
        try let _ = Bdd.BddVarMap.find v m in true
        with Not_found -> false) s.bdd_state
  in
  Format.fprintf fmt "@[<hv 2>{ @[<hv 2>map_state:@ @[%a@];@]@ \
                      @[<hv 2>apron_env:@ @[%a@];@]@ \
                      @[<hv 2>apron:@ @[%a@];@]@ \
                      @[<hv 2>bdd:@ @[%a@];@]@ \
                      @[<hv 2>domains:@ @[%a@];@]@ \
                      @[<hv 2>reduced_bdd:@ @[%a@];@] }@]"
    print_env s.map_state
    (fun fmt -> Environment.print fmt) s.apron_state.Abstract1.env
    Abstract1.print s.apron_state
    B.print_compact s.bdd_state
    print_domains doms
    B.print_compact reduced_bdd
